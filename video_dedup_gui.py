#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
视频去重工具（图形界面版）v2.0
==============================

自动检测文件夹内内容相同的视频文件，相同则只保留一个。

判重策略（两级叠加，由廉价到昂贵）：
  【第一级 · 字节级精确查重】
      1. 按文件大小分组     —— 大小不同必然不同，直接排除
      2. 快速指纹预筛       —— 首/中/尾采样
      3. SHA-256 全量哈希   —— 100% 确认逐字节一致
  【第二级 · 帧级相似查重】
      4. 抽取多帧计算感知哈希(pHash) —— 识别「画面相同但清晰度/码率不同」的版本
         用汉明距离判定画面是否相同

保留规则（同一组内）：
      · 分辨率优先（宽×高 更大者胜）
      · 分辨率相同则比锐度（拉普拉斯方差）

交互：
      · 扫描结果中，路径列显示为蓝色，**单击路径即可用系统默认播放器播放**

运行：
    python video_dedup_gui.py
打包（在 Windows 上执行）：
    见 README_打包说明.md
"""

from __future__ import annotations

import hashlib
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from tkinter import (BOTH, END, LEFT, RIGHT, X, Y, BooleanVar, IntVar,
                     StringVar, Tk, filedialog, messagebox)
from tkinter import ttk
from tkinter.scrolledtext import ScrolledText

# --------------------------------------------------------------------------- #
# 可选依赖：OpenCV（帧级查重用，缺失时自动降级为仅字节查重）
# --------------------------------------------------------------------------- #
try:
    import cv2
    import numpy as np
    HAS_CV2 = True
except Exception:                                   # noqa: BLE001
    HAS_CV2 = False

# --------------------------------------------------------------------------- #
# 常量
# --------------------------------------------------------------------------- #

APP_NAME = "视频去重工具"
APP_VERSION = "2.0"

VIDEO_EXTS = {
    ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm", ".m4v",
    ".mpg", ".mpeg", ".ts", ".m2ts", ".3gp", ".rmvb", ".rm", ".vob", ".ogv",
}

SAMPLE_SIZE = 1024 * 1024        # 快速指纹采样字节数
CHUNK_SIZE = 1024 * 1024         # 全量哈希读取块
DEFAULT_WORKERS = min(8, (os.cpu_count() or 4) * 2)

# 帧级查重参数
FRAMES_PER_VIDEO = 8             # 每个视频抽多少帧比对
PHASH_SIZE = 32                  # pHash 输入尺寸
PHASH_LOW = 8                    # 取 DCT 低频 8x8
DEFAULT_PHASH_THRESHOLD = 8      # 汉明距离阈值（64 位中允许不同的位数）

C_BG = "#f5f6f8"
C_CARD = "#ffffff"
C_PRIMARY = "#2563eb"
C_TEXT = "#1f2937"
C_MUTED = "#6b7280"
C_DANGER = "#dc2626"
C_KEEP = "#059669"
C_LINK = "#1d4ed8"


# --------------------------------------------------------------------------- #
# 通用工具
# --------------------------------------------------------------------------- #

def human_size(num_bytes: float) -> str:
    size = float(num_bytes)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024 or unit == "TB":
            return f"{int(size)} B" if unit == "B" else f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} TB"


def open_with_default_player(path: Path) -> tuple[bool, str]:
    """调用系统默认程序打开文件（即用默认播放器播放视频）。"""
    try:
        if not path.exists():
            return False, f"文件不存在：{path}"
        if sys.platform.startswith("win"):
            os.startfile(str(path))                      # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True, ""
    except Exception as e:                               # noqa: BLE001
        return False, str(e)


def iter_video_files(root: Path, recursive: bool) -> list[Path]:
    files: list[Path] = []
    walker = root.rglob("*") if recursive else root.glob("*")
    for p in walker:
        try:
            if not p.is_file() or p.name.startswith("."):
                continue
            if p.suffix.lower() not in VIDEO_EXTS:
                continue
            if any(part in ("_duplicates", "_dupes_deleted") for part in p.parts):
                continue
            files.append(p)
        except OSError:
            continue
    return files


def quick_fingerprint(path: Path) -> str | None:
    try:
        size = path.stat().st_size
        if size == 0:
            return None
        h = hashlib.blake2b(digest_size=16)
        h.update(size.to_bytes(8, "little", signed=False))
        with path.open("rb") as f:
            offsets = {0}
            if size > SAMPLE_SIZE:
                offsets.add(max(0, size // 2 - SAMPLE_SIZE // 2))
            if size > 2 * SAMPLE_SIZE:
                offsets.add(size - SAMPLE_SIZE)
            for off in sorted(offsets):
                f.seek(off)
                h.update(f.read(SAMPLE_SIZE))
        return h.hexdigest()
    except (OSError, ValueError):
        return None


def full_hash(path: Path) -> str | None:
    h = hashlib.sha256()
    try:
        with path.open("rb") as f:
            for block in iter(lambda: f.read(CHUNK_SIZE), b""):
                h.update(block)
        return h.hexdigest()
    except OSError:
        return None


# --------------------------------------------------------------------------- #
# 帧级分析：感知哈希 + 清晰度打分
# --------------------------------------------------------------------------- #

def _sample_frames(path: Path, n: int = FRAMES_PER_VIDEO):
    """均匀抽取 n 帧（避开首尾）。返回 (frames, width, height)。"""
    if not HAS_CV2:
        return [], 0, 0
    cap = cv2.VideoCapture(str(path))
    if not cap.isOpened():
        return [], 0, 0
    total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
    w = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
    h = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
    frames = []
    if total <= 0:
        # 某些容器拿不到帧数，顺序读
        idx = 0
        while len(frames) < n:
            ok, fr = cap.read()
            if not ok:
                break
            if idx % 10 == 0:
                frames.append(fr)
            idx += 1
    else:
        for i in range(n):
            pos = min(total - 1, int(total * (i + 1) / (n + 1)))
            cap.set(cv2.CAP_PROP_POS_FRAMES, pos)
            ok, fr = cap.read()
            if ok:
                frames.append(fr)
    cap.release()
    return frames, w, h


def _phash(frame, size: int = PHASH_SIZE, low: int = PHASH_LOW) -> int:
    """感知哈希：灰度 → 缩放 → DCT → 低频区域与中位数比较，得到 64 位指纹。"""
    gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
    gray = cv2.resize(gray, (size, size), interpolation=cv2.INTER_AREA)
    dct = cv2.dct(np.float32(gray))
    block = dct[:low, :low].flatten()
    med = np.median(block[1:])           # 去掉直流分量后取中位数
    bits = 0
    for i, v in enumerate(block):
        if v > med:
            bits |= (1 << i)
    return bits


def _sharpness(frame) -> float:
    """拉普拉斯方差：衡量画面锐度/细节量，越大越清晰。"""
    gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
    return float(cv2.Laplacian(gray, cv2.CV_64F).var())


def analyze_video(path: Path) -> dict | None:
    """
    对单个视频做帧级分析，返回：
      { 'hashes': [int], 'width': W, 'height': H, 'sharpness': float }
    失败返回 None。
    """
    if not HAS_CV2:
        return None
    try:
        frames, w, h = _sample_frames(path)
        if not frames:
            return None
        hashes = [_phash(fr) for fr in frames]
        sharp = float(np.mean([_sharpness(fr) for fr in frames]))
        return {"hashes": hashes, "width": w, "height": h, "sharpness": sharp}
    except Exception:                                    # noqa: BLE001
        return None


def hamming(a: int, b: int) -> int:
    return bin(a ^ b).count("1")


def frames_similar(ha: list[int], hb: list[int], threshold: int) -> bool:
    """
    多帧投票判定两个视频画面是否相同。
    取两段哈希按序比较，平均汉明距离 <= threshold 即认为相同。
    """
    n = min(len(ha), len(hb))
    if n == 0:
        return False
    dists = [hamming(ha[i], hb[i]) for i in range(n)]
    return (sum(dists) / n) <= threshold


# --------------------------------------------------------------------------- #
# 保留规则
# --------------------------------------------------------------------------- #

def quality_score(info: dict | None, path: Path) -> tuple:
    """
    返回排序用的清晰度键：(分辨率像素数, 锐度, 文件大小)。
    分辨率优先，其次锐度，再次大小 —— 越大越清晰，应保留。
    """
    if info:
        w, h = info.get("width", 0), info.get("height", 0)
        sharp = info.get("sharpness", 0.0)
    else:
        w = h = 0
        sharp = 0.0
    try:
        size = path.stat().st_size
    except OSError:
        size = 0
    return (w * h, sharp, size)


def choose_keeper(group: list[Path], info_map: dict,
                  strategy: str = "quality") -> Path:
    """
    从一组重复文件中挑出要保留的。
    strategy:
      quality  —— 清晰度优先（分辨率→锐度→大小），默认
      first / oldest / newest / shortest-path —— 按路径/时间
    """
    if strategy == "oldest":
        return min(group, key=lambda p: (p.stat().st_mtime, str(p)))
    if strategy == "newest":
        return max(group, key=lambda p: (p.stat().st_mtime, str(p)))
    if strategy == "shortest-path":
        return min(group, key=lambda p: (len(str(p)), str(p)))
    if strategy == "first":
        return min(group, key=lambda p: str(p).lower())
    # quality：清晰度最高者胜；并列时取路径靠前的，保证结果稳定
    return max(group, key=lambda p: (quality_score(info_map.get(str(p)), p),
                                     [-ord(c) for c in str(p).lower()]))


# --------------------------------------------------------------------------- #
# 查重引擎
# --------------------------------------------------------------------------- #

class DedupEngine:
    def __init__(self, log, progress, should_cancel):
        self.log = log
        self.progress = progress
        self.should_cancel = should_cancel

    # ---------- 第一级：字节级 ---------- #
    def find_exact_duplicates(self, files: list[Path]) -> list[list[Path]]:
        self.log("【第1层·字节】按文件大小分组…")
        by_size: dict[int, list[Path]] = defaultdict(list)
        for f in files:
            try:
                by_size[f.stat().st_size].append(f)
            except OSError:
                continue
        candidates = [g for g in by_size.values() if len(g) > 1]
        uniq = sum(len(g) for g in by_size.values() if len(g) == 1)
        self.log(f"         {len(files)} 个文件 → {len(candidates)} 组候选，"
                 f"{uniq} 个大小唯一，排除")
        if not candidates:
            return []

        flat = [f for g in candidates for f in g]

        self.log("【第2层·字节】计算快速指纹（首/中/尾采样）…")
        fp_map: dict[str, list[Path]] = defaultdict(list)
        total, done = len(flat), 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(quick_fingerprint, f): f for f in flat}
            for fut in as_completed(futures):
                if self.should_cancel():
                    return []
                fp = fut.result()
                if fp:
                    fp_map[fp].append(futures[fut])
                done += 1
                if done % 5 == 0 or done == total:
                    self.progress(done, total, "快速指纹")
        fp_candidates = [g for g in fp_map.values() if len(g) > 1]
        saved = total - sum(len(g) for g in fp_candidates)
        self.log(f"         → {len(fp_candidates)} 组候选，{saved} 个指纹唯一，排除")
        if not fp_candidates:
            return []

        flat2 = [f for g in fp_candidates for f in g]
        self.log(f"【第3层·字节】对 {len(flat2)} 个候选做全量 SHA-256 校验…")
        hash_map: dict[str, list[Path]] = defaultdict(list)
        total2, done2 = len(flat2), 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(full_hash, f): f for f in flat2}
            for fut in as_completed(futures):
                if self.should_cancel():
                    return []
                digest = fut.result()
                if digest:
                    hash_map[digest].append(futures[fut])
                done2 += 1
                self.progress(done2, total2, "全量校验")
        groups = [g for g in hash_map.values() if len(g) > 1]
        self.log(f"         字节级确认 {len(groups)} 组完全相同的文件")
        return groups

    # ---------- 第二级：帧级 ---------- #
    def find_similar_by_frames(self, files: list[Path], threshold: int,
                               info_map: dict) -> list[list[Path]]:
        if not HAS_CV2:
            self.log("【第4层·画面】未安装 OpenCV，跳过帧级查重")
            return []

        # 只分析视频文件（避免对非视频做无谓解码）
        targets = [f for f in files if f.suffix.lower() in VIDEO_EXTS]
        self.log(f"【第4层·画面】对 {len(targets)} 个视频抽取 {FRAMES_PER_VIDEO} 帧做画面比对…")
        total, done = len(targets), 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(analyze_video, f): f for f in targets}
            for fut in as_completed(futures):
                if self.should_cancel():
                    return []
                f = futures[fut]
                info = fut.result()
                if info:
                    info_map[str(f)] = info
                done += 1
                if done % 3 == 0 or done == total:
                    self.progress(done, total, "画面分析")

        usable = [f for f in targets if str(f) in info_map]
        self.log(f"         成功分析 {len(usable)}/{len(targets)} 个视频")

        # 两两比较（用并查集合并相似组）
        parent = {str(f): str(f) for f in usable}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra

        n = len(usable)
        pairs_checked = 0
        for i in range(n):
            if self.should_cancel():
                return []
            fi = usable[i]
            hi = info_map[str(fi)]["hashes"]
            for j in range(i + 1, n):
                fj = usable[j]
                # 已经是同一组就不用比了
                if find(str(fi)) == find(str(fj)):
                    continue
                hj = info_map[str(fj)]["hashes"]
                pairs_checked += 1
                if frames_similar(hi, hj, threshold):
                    union(str(fi), str(fj))
                    self.log(f"         画面相同 ⟶ 合并：{fi.name}  ⇄  {fj.name}")
            self.progress(i + 1, n, "画面比对")

        self.log(f"         共比对 {pairs_checked} 对，完成画面查重")
        merged: dict[str, list[Path]] = defaultdict(list)
        for f in usable:
            merged[find(str(f))].append(f)
        groups = [g for g in merged.values() if len(g) > 1]
        self.log(f"         画面级确认 {len(groups)} 组画面相同的文件")
        return groups


def merge_groups(*group_lists) -> list[list[Path]]:
    """把多轮查重的结果按文件合并去重（同一文件只出现在一个组）。"""
    parent: dict[str, str] = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    all_paths = set()
    for groups in group_lists:
        for g in groups:
            keys = [str(p) for p in g]
            all_paths.update(keys)
            for k in keys[1:]:
                union(keys[0], k)

    merged: dict[str, list[Path]] = defaultdict(list)
    for k in all_paths:
        merged[find(k)].append(Path(k))
    return [g for g in merged.values() if len(g) > 1]


# --------------------------------------------------------------------------- #
# GUI
# --------------------------------------------------------------------------- #

class VideoDedupApp:
    def __init__(self, root: Tk):
        self.root = root
        self.root.title(f"{APP_NAME} v{APP_VERSION}")
        self.root.geometry("1080x760")
        self.root.minsize(920, 640)
        self.root.configure(bg=C_BG)

        self.folder = StringVar()
        self.recursive = BooleanVar(value=True)
        self.dry_run = BooleanVar(value=True)
        self.permanent = BooleanVar(value=False)
        self.keep = StringVar(value="quality")
        self.use_frame = BooleanVar(value=bool(HAS_CV2))
        self.threshold = IntVar(value=DEFAULT_PHASH_THRESHOLD)

        self.msg_queue: queue.Queue = queue.Queue()
        self.worker: threading.Thread | None = None
        self.cancel_flag = threading.Event()
        self.found_groups: list[list[Path]] = []
        self.info_map: dict = {}
        self.scan_root: Path | None = None

        self._setup_style()
        self._build_ui()
        self._poll_queue()

    # ---------------- 样式 ---------------- #
    def _setup_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:                                # noqa: BLE001
            pass
        style.configure("TFrame", background=C_BG)
        style.configure("Card.TFrame", background=C_CARD)
        style.configure("TLabel", background=C_BG, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("Card.TLabel", background=C_CARD, foreground=C_TEXT)
        style.configure("Title.TLabel", font=("Microsoft YaHei UI", 16, "bold"),
                        background=C_BG, foreground=C_TEXT)
        style.configure("Muted.TLabel", foreground=C_MUTED, background=C_BG,
                        font=("Microsoft YaHei UI", 9))
        style.configure("TButton", font=("Microsoft YaHei UI", 10))
        style.configure("Primary.TButton", font=("Microsoft YaHei UI", 11, "bold"))
        style.configure("TCheckbutton", background=C_BG, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("Card.TCheckbutton", background=C_CARD, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("TRadiobutton", background=C_BG, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("Card.TRadiobutton", background=C_CARD, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("TProgressbar", thickness=18)
        style.configure("Treeview", font=("Microsoft YaHei UI", 9), rowheight=26)
        style.configure("Treeview.Heading", font=("Microsoft YaHei UI", 9, "bold"))

    # ---------------- 布局 ---------------- #
    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=14)
        outer.pack(fill=BOTH, expand=True)

        head = ttk.Frame(outer)
        head.pack(fill=X)
        ttk.Label(head, text="🎬  " + APP_NAME, style="Title.TLabel").pack(side=LEFT)
        ttk.Label(head, text="找出内容相同的视频（含清晰度不同的版本），只保留最清晰的一个",
                  style="Muted.TLabel").pack(side=LEFT, padx=(12, 0), pady=(6, 0))

        # ---- 步骤1 ----
        c1 = ttk.Frame(outer, style="Card.TFrame", padding=12)
        c1.pack(fill=X, pady=(12, 0))
        ttk.Label(c1, text="第 1 步 · 选择要扫描的文件夹", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")
        row = ttk.Frame(c1, style="Card.TFrame")
        row.pack(fill=X, pady=(8, 0))
        ttk.Entry(row, textvariable=self.folder,
                  font=("Microsoft YaHei UI", 10)).pack(side=LEFT, fill=X,
                                                        expand=True, ipady=4)
        ttk.Button(row, text="浏览…", command=self.on_browse).pack(side=LEFT, padx=(8, 0))
        ttk.Checkbutton(c1, text="递归扫描子文件夹", variable=self.recursive,
                        style="Card.TCheckbutton").pack(anchor="w", pady=(8, 0))

        # ---- 步骤2 ----
        c2 = ttk.Frame(outer, style="Card.TFrame", padding=12)
        c2.pack(fill=X, pady=(10, 0))
        ttk.Label(c2, text="第 2 步 · 处理方式", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")
        mrow = ttk.Frame(c2, style="Card.TFrame")
        mrow.pack(fill=X, pady=(8, 0))
        ttk.Radiobutton(mrow, text="仅扫描，不修改（预演）", variable=self.dry_run,
                        value=True, style="Card.TRadiobutton",
                        command=self._on_mode_change).pack(side=LEFT)
        ttk.Radiobutton(mrow, text="重复文件移到 _duplicates/（可恢复）",
                        variable=self.dry_run, value=False, style="Card.TRadiobutton",
                        command=self._on_mode_change).pack(side=LEFT, padx=(20, 0))
        ttk.Checkbutton(c2, text="永久删除重复文件（不可恢复！）", variable=self.permanent,
                        style="Card.TCheckbutton",
                        command=self._on_mode_change).pack(anchor="w", pady=(6, 0))

        # ---- 步骤2b：保留规则 ----
        c3 = ttk.Frame(outer, style="Card.TFrame", padding=12)
        c3.pack(fill=X, pady=(10, 0))
        ttk.Label(c3, text="第 3 步 · 保留规则", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")
        krow = ttk.Frame(c3, style="Card.TFrame")
        krow.pack(fill=X, pady=(8, 0))
        ttk.Radiobutton(krow, text="保留最清晰的（分辨率→锐度）", variable=self.keep,
                        value="quality", style="Card.TRadiobutton").pack(side=LEFT)
        ttk.Radiobutton(krow, text="路径靠前", variable=self.keep, value="first",
                        style="Card.TRadiobutton").pack(side=LEFT, padx=(16, 0))
        ttk.Radiobutton(krow, text="最旧", variable=self.keep, value="oldest",
                        style="Card.TRadiobutton").pack(side=LEFT, padx=(16, 0))
        ttk.Radiobutton(krow, text="最新", variable=self.keep, value="newest",
                        style="Card.TRadiobutton").pack(side=LEFT, padx=(16, 0))

        # ---- 步骤2c：画面查重 ----
        c4 = ttk.Frame(outer, style="Card.TFrame", padding=12)
        c4.pack(fill=X, pady=(10, 0))
        ttk.Label(c4, text="第 4 步 · 画面查重（识别清晰度/码率不同的同一视频）",
                  style="Card.TLabel", font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")
        frow = ttk.Frame(c4, style="Card.TFrame")
        frow.pack(fill=X, pady=(8, 0))
        self.cb_frame = ttk.Checkbutton(
            frow, text="启用画面级查重（较慢，但对清晰度不同的版本也有效）",
            variable=self.use_frame, style="Card.TCheckbutton",
            state=("normal" if HAS_CV2 else "disabled"))
        self.cb_frame.pack(side=LEFT)
        if not HAS_CV2:
            ttk.Label(frow, text="（未安装 OpenCV，不可用）", style="Card.TLabel",
                      foreground=C_DANGER).pack(side=LEFT, padx=(6, 0))
        else:
            ttk.Label(frow, text="  相似阈值：", style="Card.TLabel").pack(side=LEFT, padx=(16, 0))
            ttk.Spinbox(frow, from_=0, to=32, width=4,
                        textvariable=self.threshold).pack(side=LEFT)
            ttk.Label(frow, text="  （越小越严格，推荐 6~12）", style="Card.TLabel",
                      foreground=C_MUTED).pack(side=LEFT)

        # ---- 操作 ----
        brow = ttk.Frame(outer)
        brow.pack(fill=X, pady=(12, 0))
        self.btn_scan = ttk.Button(brow, text="开始扫描", style="Primary.TButton",
                                   command=self.on_scan)
        self.btn_scan.pack(side=LEFT, ipadx=20, ipady=6)
        self.btn_cancel = ttk.Button(brow, text="停止", command=self.on_cancel,
                                     state="disabled")
        self.btn_cancel.pack(side=LEFT, padx=(10, 0), ipady=6)
        ttk.Label(brow, text="  提示：结果中单击蓝色路径即可播放视频",
                  style="Muted.TLabel").pack(side=LEFT, padx=(12, 0))

        pframe = ttk.Frame(outer)
        pframe.pack(fill=X, pady=(10, 0))
        self.pbar = ttk.Progressbar(pframe, mode="determinate", maximum=100)
        self.pbar.pack(fill=X)
        self.status = ttk.Label(pframe, text="就绪", style="Muted.TLabel")
        self.status.pack(anchor="w", pady=(4, 0))

        nb = ttk.Notebook(outer)
        nb.pack(fill=BOTH, expand=True, pady=(10, 0))

        tab1 = ttk.Frame(nb, padding=8)
        nb.add(tab1, text="  扫描结果  ")
        cols = ("group", "action", "name", "quality", "size", "path")
        self.tree = ttk.Treeview(tab1, columns=cols, show="headings", height=14)
        for c, (txt, w, anchor) in {
            "group": ("组", 45, "center"),
            "action": ("处理", 70, "center"),
            "name": ("文件名", 220, "w"),
            "quality": ("清晰度", 120, "w"),
            "size": ("大小", 80, "e"),
            "path": ("路径（单击播放）", 380, "w"),
        }.items():
            self.tree.heading(c, text=txt)
            self.tree.column(c, width=w, anchor=anchor, stretch=(c == "path"))
        vsb = ttk.Scrollbar(tab1, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side=LEFT, fill=BOTH, expand=True)
        vsb.pack(side=RIGHT, fill=Y)
        self.tree.tag_configure("keep", foreground=C_KEEP)
        self.tree.tag_configure("dup", foreground=C_DANGER)
        # 单击路径列 → 播放
        self.tree.bind("<Button-1>", self._on_tree_click)
        self.tree.bind("<Double-1>", self._on_tree_dblclick)

        tab2 = ttk.Frame(nb, padding=8)
        nb.add(tab2, text="  运行日志  ")
        self.log_box = ScrolledText(tab2, height=12, font=("Consolas", 9),
                                    bg="#1e1e1e", fg="#d4d4d4",
                                    insertbackground="#d4d4d4", wrap="word")
        self.log_box.pack(fill=BOTH, expand=True)

        self.summary = ttk.Label(outer, text="", style="Muted.TLabel")
        self.summary.pack(anchor="w", pady=(8, 0))

    # ---------------- 交互 ---------------- #
    def _on_mode_change(self):
        if self.permanent.get() and self.dry_run.get():
            self.dry_run.set(False)

    def on_browse(self):
        d = filedialog.askdirectory(title="选择包含视频的文件夹",
                                    initialdir=self.folder.get() or str(Path.home()))
        if d:
            self.folder.set(d)

    def log(self, text: str):
        self.msg_queue.put(("log", text))

    def progress(self, done, total, phase):
        self.msg_queue.put(("progress", (done, total, phase)))

    def _on_tree_click(self, event):
        """单击路径列 → 播放该视频。"""
        region = self.tree.identify("region", event.x, event.y)
        if region != "cell":
            return
        col = self.tree.identify_column(event.x)
        # 路径是第 6 列（#6）
        if col != "#6":
            return
        row = self.tree.identify_row(event.y)
        if not row:
            return
        vals = self.tree.item(row, "values")
        if len(vals) < 6:
            return
        rel = vals[5]
        if not self.scan_root:
            return
        target = (self.scan_root / rel)
        ok, err = open_with_default_player(target)
        if not ok:
            messagebox.showwarning("无法播放", f"打不开文件：\n{target}\n\n{err}")

    def _on_tree_dblclick(self, event):
        """双击整行也可播放（更符合直觉）。"""
        row = self.tree.identify_row(event.y)
        if not row or not self.scan_root:
            return
        vals = self.tree.item(row, "values")
        if len(vals) < 6:
            return
        target = self.scan_root / vals[5]
        ok, err = open_with_default_player(target)
        if not ok:
            messagebox.showwarning("无法播放", f"打不开文件：\n{target}\n\n{err}")

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.msg_queue.get_nowait()
                if kind == "log":
                    self.log_box.insert(END, payload + "\n")
                    self.log_box.see(END)
                elif kind == "progress":
                    done, total, phase = payload
                    if total:
                        self.pbar["value"] = int(done * 100 / total)
                    self.status.config(text=f"{phase}… {done}/{total}")
                elif kind == "groups":
                    self._render_groups(payload)
                elif kind == "summary":
                    self.summary.config(text=payload)
                elif kind == "done":
                    self._reset_buttons()
                    if payload:
                        messagebox.showinfo("完成", payload)
                elif kind == "error":
                    self._reset_buttons()
                    messagebox.showerror("出错了", payload)
        except queue.Empty:
            pass
        self.root.after(120, self._poll_queue)

    def _reset_buttons(self):
        self.btn_scan.config(state="normal")
        self.btn_cancel.config(state="disabled")
        self.pbar["value"] = 0

    def _quality_text(self, path: Path) -> str:
        info = self.info_map.get(str(path))
        if not info:
            return "—"
        w, h = info.get("width", 0), info.get("height", 0)
        sharp = info.get("sharpness", 0.0)
        return f"{w}×{h}  锐度{sharp:.0f}"

    def _render_groups(self, groups: list):
        self.tree.delete(*self.tree.get_children())
        root = self.scan_root
        for i, group in enumerate(groups, 1):
            keeper = choose_keeper(group, self.info_map, self.keep.get())
            for p in sorted(group, key=lambda x: str(x).lower()):
                try:
                    size = human_size(p.stat().st_size)
                    rel = str(p.relative_to(root)) if root else str(p)
                except (OSError, ValueError):
                    size, rel = "?", str(p)
                is_keep = (p == keeper)
                self.tree.insert(
                    "", END,
                    values=(i, "保留" if is_keep else "重复", p.name,
                            self._quality_text(p), size, rel),
                    tags=("keep",) if is_keep else ("dup",),
                )

    # ---------------- 扫描 ---------------- #
    def on_scan(self):
        folder = self.folder.get().strip()
        if not folder:
            messagebox.showwarning("请选择文件夹", "请先选择一个要扫描的文件夹。")
            return
        root = Path(folder).expanduser().resolve()
        if not root.is_dir():
            messagebox.showerror("路径无效", f"不是有效的文件夹：\n{root}")
            return
        if self.permanent.get() and self.dry_run.get():
            messagebox.showwarning("选项冲突", "不能同时选择「预演」和「永久删除」。")
            return
        if self.permanent.get():
            if not messagebox.askyesno(
                    "确认永久删除",
                    "你将永久删除重复文件，此操作不可恢复！\n\n确定要继续吗？\n\n"
                    "（建议先做一次「预演」确认结果）", icon="warning"):
                return

        self.scan_root = root
        self.info_map.clear()
        self.cancel_flag.clear()
        self.btn_scan.config(state="disabled")
        self.btn_cancel.config(state="normal")
        self.log_box.delete("1.0", END)
        self.tree.delete(*self.tree.get_children())
        self.summary.config(text="")

        self.worker = threading.Thread(target=self._run_scan, args=(root,), daemon=True)
        self.worker.start()

    def on_cancel(self):
        self.cancel_flag.set()
        self.log("⚠ 用户请求停止…")

    def _run_scan(self, root: Path):
        try:
            t0 = time.time()
            self.log("=" * 64)
            self.log(f"扫描目录：{root}")
            mode = "预演" if self.dry_run.get() else (
                "永久删除" if self.permanent.get() else "移动到 _duplicates/")
            self.log(f"递归：{'是' if self.recursive.get() else '否'}   "
                     f"模式：{mode}   保留规则：{self.keep.get()}")
            self.log(f"画面查重：{'开启' if self.use_frame.get() else '关闭'}"
                     + (f"（阈值 {self.threshold.get()}）" if self.use_frame.get() else ""))
            self.log("=" * 64)

            self.progress(0, 1, "枚举文件")
            files = iter_video_files(root, self.recursive.get())
            total_size = sum(f.stat().st_size for f in files)
            self.log(f"发现 {len(files)} 个视频文件，合计 {human_size(total_size)}")
            if len(files) < 2:
                self.log("文件数量不足 2 个，无需查重。")
                self.msg_queue.put(("done", "文件数量不足，无需查重。"))
                return

            engine = DedupEngine(self.log, self.progress, self.cancel_flag.is_set)

            # 第一级：字节级
            exact_groups = engine.find_exact_duplicates(files)
            if self.cancel_flag.is_set():
                self.msg_queue.put(("done", "已停止，未做任何改动。"))
                return

            # 第二级：画面级
            frame_groups = []
            if self.use_frame.get():
                frame_groups = engine.find_similar_by_frames(
                    files, self.threshold.get(), self.info_map)
                if self.cancel_flag.is_set():
                    self.msg_queue.put(("done", "已停止，未做任何改动。"))
                    return
            else:
                self.log("【第4层·画面】已跳过（未启用）")

            # 合并两级结果
            groups = merge_groups(exact_groups, frame_groups)
            self.log(f"合并后共 {len(groups)} 组重复")

            self.found_groups = groups
            self.msg_queue.put(("groups", groups))

            if not groups:
                self.log("未发现内容相同的视频文件。")
                self.msg_queue.put(("summary", "未发现重复，目录很干净 ✓"))
                self.msg_queue.put(("done", "扫描完成：未发现内容相同的视频。"))
                return

            # ---- 执行处理 ---- #
            dup_dir = root / "_duplicates"
            dup_count = 0
            saved = 0
            failed = 0
            for group in groups:
                if self.cancel_flag.is_set():
                    break
                keeper = choose_keeper(group, self.info_map, self.keep.get())
                others = [p for p in group if p != keeper]
                try:
                    saved += sum(p.stat().st_size for p in others)
                except OSError:
                    pass
                for p in others:
                    dup_count += 1
                    if self.dry_run.get():
                        continue
                    try:
                        if self.permanent.get():
                            p.unlink()
                        else:
                            dup_dir.mkdir(exist_ok=True)
                            target = dup_dir / p.name
                            stem, suffix, k = p.stem, p.suffix, 1
                            while target.exists():
                                target = dup_dir / f"{stem}__{k}{suffix}"
                                k += 1
                            shutil.move(str(p), str(target))
                    except OSError as e:
                        failed += 1
                        self.log(f"  [失败] {p.name}: {e}")

            elapsed = time.time() - t0
            self.log("=" * 64)
            self.log(f"重复文件组数：{len(groups)}")
            self.log(f"可清理文件数：{dup_count}")
            self.log(f"可释放空间：{human_size(saved)}")
            self.log(f"耗时：{elapsed:.1f} 秒")

            if self.dry_run.get():
                s = (f"预演完成：{len(groups)} 组重复，可清理 {dup_count} 个文件，"
                     f"释放 {human_size(saved)}（未修改任何文件）")
            elif self.permanent.get():
                s = (f"完成：已永久删除 {dup_count} 个重复文件，释放 {human_size(saved)}"
                     + (f"（{failed} 个失败）" if failed else ""))
            else:
                s = (f"完成：{dup_count} 个重复文件已移到 {dup_dir}，释放 {human_size(saved)}"
                     + (f"（{failed} 个失败）" if failed else ""))
            self.msg_queue.put(("summary", s))
            self.msg_queue.put(("done", s))

        except Exception as e:                            # noqa: BLE001
            import traceback
            self.log(traceback.format_exc())
            self.msg_queue.put(("error", f"{type(e).__name__}: {e}"))


def main():
    root = Tk()
    app = VideoDedupApp(root)
    if len(sys.argv) > 1:
        p = Path(sys.argv[1])
        if p.is_dir():
            app.folder.set(str(p))
    root.mainloop()


if __name__ == "__main__":
    main()
