#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
视频去重工具（图形界面版）
==========================

自动检测文件夹内内容相同的视频文件，相同则只保留一个。

判重策略（由廉价到昂贵，逐级过滤）：
  1. 按文件大小分组     —— 大小不同必然内容不同，直接排除
  2. 快速指纹预筛       —— 读取首/中/尾采样 + 文件大小，秒级排除绝大多数
  3. SHA-256 全量哈希   —— 仅对候选做完整校验，100% 确认内容一致

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
from tkinter import (BOTH, END, LEFT, RIGHT, X, Y, BooleanVar, StringVar,
                     Tk, filedialog, messagebox)
from tkinter import ttk
from tkinter.scrolledtext import ScrolledText

# --------------------------------------------------------------------------- #
# 常量
# --------------------------------------------------------------------------- #

APP_NAME = "视频去重工具"
APP_VERSION = "1.0"

VIDEO_EXTS = {
    ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm", ".m4v",
    ".mpg", ".mpeg", ".ts", ".m2ts", ".3gp", ".rmvb", ".rm", ".vob", ".ogv",
}

SAMPLE_SIZE = 1024 * 1024        # 快速指纹采样字节数
CHUNK_SIZE = 1024 * 1024         # 全量哈希读取块
DEFAULT_WORKERS = min(8, (os.cpu_count() or 4) * 2)

# 颜色（浅色主题）
C_BG = "#f5f6f8"
C_CARD = "#ffffff"
C_PRIMARY = "#2563eb"
C_PRIMARY_DARK = "#1d4ed8"
C_TEXT = "#1f2937"
C_MUTED = "#6b7280"
C_DANGER = "#dc2626"
C_KEEP = "#059669"


# --------------------------------------------------------------------------- #
# 通用工具
# --------------------------------------------------------------------------- #

def human_size(num_bytes: float) -> str:
    """把字节数格式化成人读的形式。"""
    size = float(num_bytes)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024 or unit == "TB":
            return f"{int(size)} B" if unit == "B" else f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} TB"


def resource_path(rel: str) -> str:
    """兼容 PyInstaller 打包后的资源路径。"""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, rel)


def iter_video_files(root: Path, recursive: bool) -> list[Path]:
    """收集目录下所有视频文件（跳过隐藏文件与输出目录）。"""
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
    """读取文件首/中/尾各 SAMPLE_SIZE 字节 + 文件大小，做快速指纹。"""
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
    """SHA-256 全量哈希。"""
    h = hashlib.sha256()
    try:
        with path.open("rb") as f:
            for block in iter(lambda: f.read(CHUNK_SIZE), b""):
                h.update(block)
        return h.hexdigest()
    except OSError:
        return None


def choose_keeper(group: list[Path], strategy: str) -> Path:
    """从一组重复文件中挑出要保留的那个。"""
    if strategy == "oldest":
        return min(group, key=lambda p: (p.stat().st_mtime, str(p)))
    if strategy == "newest":
        return max(group, key=lambda p: (p.stat().st_mtime, str(p)))
    if strategy == "shortest-path":
        return min(group, key=lambda p: (len(str(p)), str(p)))
    return min(group, key=lambda p: str(p).lower())


# --------------------------------------------------------------------------- #
# 查重核心（与命令行版一致，带进度回调）
# --------------------------------------------------------------------------- #

class DedupEngine:
    """执行查重流程，通过回调汇报进度。"""

    def __init__(self, log, progress, should_cancel):
        self.log = log                 # log(str)
        self.progress = progress       # progress(done, total, text)
        self.should_cancel = should_cancel  # should_cancel() -> bool

    def find_duplicate_groups(self, files: list[Path]) -> list[list[Path]]:
        # --- 第 1 层：按大小分组 ---
        self.log("【第1层】按文件大小分组…")
        by_size: dict[int, list[Path]] = defaultdict(list)
        for f in files:
            try:
                by_size[f.stat().st_size].append(f)
            except OSError:
                continue
        candidates = [g for g in by_size.values() if len(g) > 1]
        uniq = sum(len(g) for g in by_size.values() if len(g) == 1)
        self.log(f"         {len(files)} 个文件 → {len(candidates)} 组候选，"
                 f"{uniq} 个文件大小唯一，直接排除")
        if not candidates:
            return []

        flat = [f for g in candidates for f in g]

        # --- 第 2 层：快速指纹 ---
        self.log(f"【第2层】计算快速指纹（首/中/尾采样）…")
        fp_map: dict[str, list[Path]] = defaultdict(list)
        total = len(flat)
        done = 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(quick_fingerprint, f): f for f in flat}
            for fut in as_completed(futures):
                if self.should_cancel():
                    return []
                f = futures[fut]
                fp = fut.result()
                if fp:
                    fp_map[fp].append(f)
                done += 1
                if done % 5 == 0 or done == total:
                    self.progress(done, total, "快速指纹")
        fp_candidates = [g for g in fp_map.values() if len(g) > 1]
        saved = total - sum(len(g) for g in fp_candidates)
        self.log(f"         → {len(fp_candidates)} 组候选，{saved} 个文件指纹唯一，排除")
        if not fp_candidates:
            return []

        # --- 第 3 层：全量哈希 ---
        flat2 = [f for g in fp_candidates for f in g]
        self.log(f"【第3层】对 {len(flat2)} 个候选做全量 SHA-256 校验…")
        hash_map: dict[str, list[Path]] = defaultdict(list)
        total2 = len(flat2)
        done2 = 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(full_hash, f): f for f in flat2}
            for fut in as_completed(futures):
                if self.should_cancel():
                    return []
                f = futures[fut]
                digest = fut.result()
                if digest:
                    hash_map[digest].append(f)
                done2 += 1
                self.progress(done2, total2, "全量校验")
        groups = [g for g in hash_map.values() if len(g) > 1]
        self.log(f"         确认 {len(groups)} 组内容相同的文件")
        return groups


# --------------------------------------------------------------------------- #
# GUI
# --------------------------------------------------------------------------- #

class VideoDedupApp:
    def __init__(self, root: Tk):
        self.root = root
        self.root.title(f"{APP_NAME} v{APP_VERSION}")
        self.root.geometry("980x720")
        self.root.minsize(860, 620)
        self.root.configure(bg=C_BG)

        self.folder = StringVar()
        self.recursive = BooleanVar(value=True)
        self.dry_run = BooleanVar(value=True)     # 默认预演，安全
        self.permanent = BooleanVar(value=False)
        self.keep = StringVar(value="first")

        self.msg_queue: queue.Queue = queue.Queue()
        self.worker: threading.Thread | None = None
        self.cancel_flag = threading.Event()
        self.found_groups: list[list[Path]] = []
        self.scan_root: Path | None = None

        self._setup_style()
        self._build_ui()
        self._poll_queue()

    # ---------------- 样式 ---------------- #
    def _setup_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("TFrame", background=C_BG)
        style.configure("Card.TFrame", background=C_CARD)
        style.configure("TLabel", background=C_BG, foreground=C_TEXT, font=("Microsoft YaHei UI", 10))
        style.configure("Card.TLabel", background=C_CARD, foreground=C_TEXT)
        style.configure("Title.TLabel", font=("Microsoft YaHei UI", 16, "bold"),
                        background=C_BG, foreground=C_TEXT)
        style.configure("Muted.TLabel", foreground=C_MUTED, background=C_BG,
                        font=("Microsoft YaHei UI", 9))
        style.configure("TButton", font=("Microsoft YaHei UI", 10))
        style.configure("Primary.TButton", font=("Microsoft YaHei UI", 11, "bold"))
        style.configure("TCheckbutton", background=C_BG, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("TRadiobutton", background=C_BG, foreground=C_TEXT,
                        font=("Microsoft YaHei UI", 10))
        style.configure("TProgressbar", thickness=18)
        style.configure("Treeview", font=("Microsoft YaHei UI", 9), rowheight=24)
        style.configure("Treeview.Heading", font=("Microsoft YaHei UI", 9, "bold"))

    # ---------------- 布局 ---------------- #
    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=16)
        outer.pack(fill=BOTH, expand=True)

        # 标题
        head = ttk.Frame(outer)
        head.pack(fill=X)
        ttk.Label(head, text="🎬  " + APP_NAME, style="Title.TLabel").pack(side=LEFT)
        ttk.Label(head, text="自动找出内容相同的视频，只保留一个",
                  style="Muted.TLabel").pack(side=LEFT, padx=(12, 0), pady=(6, 0))

        # ===== 步骤1：选择文件夹 =====
        card1 = ttk.Frame(outer, style="Card.TFrame", padding=14)
        card1.pack(fill=X, pady=(14, 0))
        ttk.Label(card1, text="第 1 步 · 选择要扫描的文件夹", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")

        row = ttk.Frame(card1, style="Card.TFrame")
        row.pack(fill=X, pady=(10, 0))
        self.entry = ttk.Entry(row, textvariable=self.folder, font=("Microsoft YaHei UI", 10))
        self.entry.pack(side=LEFT, fill=X, expand=True, ipady=4)
        ttk.Button(row, text="浏览…", command=self.on_browse).pack(side=LEFT, padx=(8, 0))

        opts = ttk.Frame(card1, style="Card.TFrame")
        opts.pack(fill=X, pady=(10, 0))
        ttk.Checkbutton(opts, text="递归扫描子文件夹", variable=self.recursive).pack(side=LEFT)

        # ===== 步骤2：选项 =====
        card2 = ttk.Frame(outer, style="Card.TFrame", padding=14)
        card2.pack(fill=X, pady=(10, 0))
        ttk.Label(card2, text="第 2 步 · 处理方式", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")

        mrow = ttk.Frame(card2, style="Card.TFrame")
        mrow.pack(fill=X, pady=(10, 0))
        ttk.Radiobutton(mrow, text="仅扫描，不修改（预演）",
                        variable=self.dry_run, value=True,
                        command=self._on_mode_change).pack(side=LEFT)
        ttk.Radiobutton(mrow, text="重复文件移到 _duplicates/（可恢复）",
                        variable=self.dry_run, value=False,
                        command=self._on_mode_change).pack(side=LEFT, padx=(24, 0))

        prow = ttk.Frame(card2, style="Card.TFrame")
        prow.pack(fill=X, pady=(8, 0))
        ttk.Checkbutton(prow, text="永久删除重复文件（不可恢复！）",
                        variable=self.permanent,
                        command=self._on_mode_change).pack(side=LEFT)

        krow = ttk.Frame(card2, style="Card.TFrame")
        krow.pack(fill=X, pady=(8, 0))
        ttk.Label(krow, text="保留规则：", style="Card.TLabel").pack(side=LEFT)
        for val, label in (("first", "路径靠前"), ("oldest", "最旧"),
                           ("newest", "最新"), ("shortest-path", "路径最短")):
            ttk.Radiobutton(krow, text=label, variable=self.keep,
                            value=val).pack(side=LEFT, padx=(10, 0))

        # ===== 操作按钮 =====
        brow = ttk.Frame(outer)
        brow.pack(fill=X, pady=(12, 0))
        self.btn_scan = ttk.Button(brow, text="开始扫描", style="Primary.TButton",
                                   command=self.on_scan)
        self.btn_scan.pack(side=LEFT, ipadx=20, ipady=6)
        self.btn_cancel = ttk.Button(brow, text="停止", command=self.on_cancel,
                                     state="disabled")
        self.btn_cancel.pack(side=LEFT, padx=(10, 0), ipady=6)

        # ===== 进度条 =====
        pframe = ttk.Frame(outer)
        pframe.pack(fill=X, pady=(10, 0))
        self.pbar = ttk.Progressbar(pframe, mode="determinate", maximum=100)
        self.pbar.pack(fill=X)
        self.status = ttk.Label(pframe, text="就绪", style="Muted.TLabel")
        self.status.pack(anchor="w", pady=(4, 0))

        # ===== 结果区 (Notebook) =====
        nb = ttk.Notebook(outer)
        nb.pack(fill=BOTH, expand=True, pady=(10, 0))

        # 结果标签页
        tab1 = ttk.Frame(nb, padding=8)
        nb.add(tab1, text="  扫描结果  ")
        cols = ("group", "action", "name", "size", "path")
        self.tree = ttk.Treeview(tab1, columns=cols, show="headings", height=14)
        for c, (txt, w, anchor) in {
            "group": ("组", 50, "center"),
            "action": ("处理", 80, "center"),
            "name": ("文件名", 240, "w"),
            "size": ("大小", 90, "e"),
            "path": ("路径", 420, "w"),
        }.items():
            self.tree.heading(c, text=txt)
            self.tree.column(c, width=w, anchor=anchor,
                             stretch=(c == "path"))
        vsb = ttk.Scrollbar(tab1, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side=LEFT, fill=BOTH, expand=True)
        vsb.pack(side=RIGHT, fill=Y)
        self.tree.tag_configure("keep", foreground=C_KEEP)
        self.tree.tag_configure("dup", foreground=C_DANGER)

        # 日志标签页
        tab2 = ttk.Frame(nb, padding=8)
        nb.add(tab2, text="  运行日志  ")
        self.log_box = ScrolledText(tab2, height=14, font=("Consolas", 9),
                                    bg="#1e1e1e", fg="#d4d4d4",
                                    insertbackground="#d4d4d4", wrap="word")
        self.log_box.pack(fill=BOTH, expand=True)

        # 底部汇总
        self.summary = ttk.Label(outer, text="", style="Muted.TLabel")
        self.summary.pack(anchor="w", pady=(8, 0))

    # ---------------- 交互 ---------------- #
    def _on_mode_change(self):
        # 永久删除和预演互斥
        if self.permanent.get() and self.dry_run.get():
            self.dry_run.set(False)
        elif not self.permanent.get() and not self.dry_run.get():
            pass

    def on_browse(self):
        # 优先在打包/运行目录的上一级打开，方便用户
        initial = self.folder.get() or str(Path.home())
        d = filedialog.askdirectory(title="选择包含视频的文件夹", initialdir=initial)
        if d:
            self.folder.set(d)

    def log(self, text: str):
        self.msg_queue.put(("log", text))

    def progress(self, done, total, phase):
        self.msg_queue.put(("progress", (done, total, phase)))

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
                        pct = int(done * 100 / total)
                        self.pbar["value"] = pct
                    self.status.config(text=f"{phase}… {done}/{total}")
                elif kind == "status":
                    self.status.config(text=payload)
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

    def _render_groups(self, groups: list):
        self.tree.delete(*self.tree.get_children())
        root = self.scan_root
        for i, group in enumerate(groups, 1):
            keeper = choose_keeper(group, self.keep.get())
            for p in sorted(group, key=lambda x: str(x).lower()):
                try:
                    size = human_size(p.stat().st_size)
                    rel = str(p.relative_to(root)) if root else str(p)
                except (OSError, ValueError):
                    size, rel = "?", str(p)
                is_keep = (p == keeper)
                self.tree.insert(
                    "", END,
                    values=(i, "保留" if is_keep else "重复", p.name, size, rel),
                    tags=("keep",) if is_keep else ("dup",),
                )

    # ---------------- 扫描主流程 ---------------- #
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
                "（建议先做一次「预演」确认结果）",
                icon="warning"):
                return

        self.scan_root = root
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
            self.log("=" * 60)
            self.log(f"扫描目录：{root}")
            self.log(f"递归：{'是' if self.recursive.get() else '否'}   "
                     f"模式：{'预演' if self.dry_run.get() else ('永久删除' if self.permanent.get() else '移动到 _duplicates/')}   "
                     f"保留规则：{self.keep.get()}")
            self.log("=" * 60)

            self.progress(0, 1, "枚举文件")
            files = iter_video_files(root, self.recursive.get())
            total_size = sum(f.stat().st_size for f in files)
            self.log(f"发现 {len(files)} 个视频文件，合计 {human_size(total_size)}")

            if len(files) < 2:
                self.log("文件数量不足 2 个，无需查重。")
                self.msg_queue.put(("done", "文件数量不足，无需查重。"))
                return

            engine = DedupEngine(self.log, self.progress, self.cancel_flag.is_set)
            groups = engine.find_duplicate_groups(files)
            if self.cancel_flag.is_set():
                self.msg_queue.put(("done", "已停止，未做任何改动。"))
                return

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
            for i, group in enumerate(groups, 1):
                if self.cancel_flag.is_set():
                    break
                keeper = choose_keeper(group, self.keep.get())
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

            # ---- 汇总 ---- #
            elapsed = time.time() - t0
            self.log("=" * 60)
            self.log(f"重复文件组数：{len(groups)}")
            self.log(f"可清理文件数：{dup_count}")
            self.log(f"可释放空间：{human_size(saved)}")
            self.log(f"耗时：{elapsed:.1f} 秒")

            if self.dry_run.get():
                s = f"预演完成：{len(groups)} 组重复，可清理 {dup_count} 个文件，释放 {human_size(saved)}（未修改任何文件）"
            elif self.permanent.get():
                s = f"完成：已永久删除 {dup_count} 个重复文件，释放 {human_size(saved)}" + \
                    (f"（{failed} 个失败）" if failed else "")
            else:
                s = f"完成：{dup_count} 个重复文件已移到 {dup_dir}，释放 {human_size(saved)}" + \
                    (f"（{failed} 个失败）" if failed else "")
            self.msg_queue.put(("summary", s))
            self.msg_queue.put(("done", s))

        except Exception as e:  # noqa: BLE001
            import traceback
            self.log(traceback.format_exc())
            self.msg_queue.put(("error", f"{type(e).__name__}: {e}"))


def main():
    root = Tk()
    app = VideoDedupApp(root)
    # 允许命令行带参数直接指定文件夹
    if len(sys.argv) > 1:
        p = Path(sys.argv[1])
        if p.is_dir():
            app.folder.set(str(p))
    root.mainloop()


if __name__ == "__main__":
    main()
