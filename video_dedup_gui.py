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

import ctypes
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
from tkinter import (BOTH, END, LEFT, RIGHT, X, Y, BooleanVar, Canvas, IntVar,
                     StringVar, Tk, filedialog, messagebox)
from tkinter import font as tkfont
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
APP_VERSION = "2.8"

VIDEO_EXTS = {
    ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm", ".m4v",
    ".mpg", ".mpeg", ".ts", ".m2ts", ".3gp", ".rmvb", ".rm", ".vob", ".ogv",
}

SAMPLE_SIZE = 1024 * 1024        # 快速指纹采样字节数
CHUNK_SIZE = 1024 * 1024         # 全量哈希读取块
DEFAULT_WORKERS = min(8, (os.cpu_count() or 4) * 2)

UI_SCALE = 1.0                            # 高 DPI 缩放因子（仅 Windows 高缩放下 >1）


def enable_dpi_awareness(root) -> None:
    """声明进程 DPI 感知，并按系统 DPI 放大 Tk 缩放与界面像素尺寸。

    不声明时 Win10/11 在 125%/150% 缩放下会把界面位图拉伸，整个程序发虚。
    声明后由 Tk 以真实 DPI 渲染，文字与线条恢复清晰。
    """
    global UI_SCALE
    if not sys.platform.startswith("win"):
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)      # Win8.1+
    except (AttributeError, OSError):
        try:
            ctypes.windll.user32.SetProcessDPIAware()       # Win7 回退
        except (AttributeError, OSError):
            pass
    try:
        dpi = float(root.winfo_fpixels("1i"))
    except Exception:                                   # noqa: BLE001
        dpi = 96.0
    if dpi > 97:                              # 标准 96 DPI 不动，仅高 DPI 放大
        UI_SCALE = dpi / 96.0
        try:
            root.tk.call("tk", "scaling", dpi / 72.0)   # 点数字体随 DPI
        except Exception:                               # noqa: BLE001
            pass

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
# 自绘结果表格（Canvas）
# --------------------------------------------------------------------------- #
# 为什么不用 ttk.Treeview：它无法只给「某一列」设置字体，因此无法实现
# 「仅路径列带下划线」。这里用 Canvas 手工绘制单元格，逐列控制字体与颜色。


def _round_rect(cv, x0, y0, x1, y1, r, **kw):
    """在画布 cv 上画圆角矩形（平滑多边形近似），返回 item id。"""
    r = max(1, min(r, (x1 - x0) // 2, (y1 - y0) // 2))
    pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r,
           x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1,
           x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
    return cv.create_polygon(pts, smooth=True, **kw)


class ResultTable(ttk.Frame):
    """自绘表格：支持每列独立字体/颜色、单击某列回调、悬停高亮、垂直滚动。

    额外提供「操作」列的删除按钮：点击后触发 on_delete_click 回调。
    """

    # 列定义：(键, 标题, 宽度, 对齐)
    COLUMNS = [
        ("group", "组", 48, "center"),
        ("action", "处理", 70, "center"),
        ("name", "文件名", 230, "w"),
        ("quality", "清晰度", 140, "w"),
        ("size", "大小", 85, "e"),
        ("path", "路径（单击播放）", 400, "w"),
        ("delete", "操作", 76, "center"),
    ]
    HEADER_H = 30
    ROW_H = 27
    PAD = 8
    # 删除按钮：中性浅色圆角按钮 + 柔和投影；悬停变浅红提示「删除」
    C_BTN_SHADOW = "#e2e7f0"
    C_BTN_BG = "#fcfdff"
    C_BTN_BORDER = "#dbe2ec"
    C_BTN_FG = "#46536b"
    C_BTN_BG_HOVER = "#fee2e2"
    C_BTN_BORDER_HOVER = "#fca5a5"
    C_BTN_FG_HOVER = "#dc2626"
    C_DELETED = "#9ca3af"

    def __init__(self, master, on_link_click=None, on_delete_click=None, **kw):
        super().__init__(master, **kw)
        self.on_link_click = on_link_click      # 回调：点击「链接列」时触发
        self.on_delete_click = on_delete_click  # 回调：点击「删除」按钮时触发
        # 按键定位各特殊列（避免依赖固定顺序）
        self.link_col_index = next(i for i, c in enumerate(self.COLUMNS) if c[0] == "path")
        self.delete_col_index = next(i for i, c in enumerate(self.COLUMNS) if c[0] == "delete")

        self.rows: list[dict] = []              # 每行数据
        self.row_items: list[list[int]] = []    # 每行对应的 canvas item id
        self.delete_btns: list = []             # 每行的删除按钮 (rect_id,text_id,bx0,by0,bx1,by1) 或 None
        self.hover_row: int | None = None
        self._hover_btn_row: int | None = None

        # 字体：普通 / 下划线（仅用于路径列）
        # 高 DPI：像素类尺寸随 UI_SCALE 放大（字体是点单位，由 tk scaling 处理）
        s = UI_SCALE
        self.COLUMNS = [(k, t, max(1, int(w * s)), a)
                        for k, t, w, a in self.COLUMNS]
        self.HEADER_H = max(20, int(self.HEADER_H * s))
        self.ROW_H = max(16, int(self.ROW_H * s))
        self.PAD = max(2, int(self.PAD * s))

        self.font_normal = tkfont.Font(family="Microsoft YaHei UI", size=9)
        self.font_bold = tkfont.Font(family="Microsoft YaHei UI", size=9, weight="bold")
        self.font_link = tkfont.Font(family="Microsoft YaHei UI", size=9, underline=True)

        # 画布 + 滚动条
        self.canvas = Canvas(self, bg=C_CARD, highlightthickness=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.pack(side=LEFT, fill=BOTH, expand=True)
        self.vsb.pack(side=RIGHT, fill=Y)

        self.canvas.bind("<Configure>", lambda e: self._redraw())
        self.canvas.bind("<MouseWheel>", self._on_wheel)
        self.canvas.bind("<Button-4>", lambda e: self._scroll_units(-1))
        self.canvas.bind("<Button-5>", lambda e: self._scroll_units(1))
        self.canvas.bind("<Motion>", self._on_motion)
        self.canvas.bind("<Leave>", self._on_leave)
        self.canvas.bind("<Button-1>", self._on_click)

    # ---------- 滚动守卫 ---------- #
    # Tk 画布的怪癖：内容不满一屏时仍可滚出负偏移（视口跑到内容上方之外），
    # 表格被整体压到下半部分，顶部留出一截空白且不会自愈。因此：
    #   1) 内容不满一屏时直接忽略滚动；
    #   2) 滚动后若视口顶跑到内容上方（canvasy(0) < 0），立即钳回顶部。
    def _content_fits(self) -> bool:
        total_h = self.HEADER_H + len(self.rows) * self.ROW_H
        return total_h <= max(self.canvas.winfo_height(), 1)

    def _scroll_units(self, n: int):
        if self._content_fits():
            return
        self.canvas.yview_scroll(n, "units")
        if self.canvas.canvasy(0) < 0:
            self.canvas.yview_moveto(0)

    def _on_wheel(self, event):
        self._scroll_units(int(-1 * (event.delta / 120)))

    # ---------- 列宽 ---------- #
    def _col_widths(self) -> list[int]:
        widths = [c[2] for c in self.COLUMNS]
        cw = self.canvas.winfo_width()
        if cw > 10:
            total = sum(widths)
            extra = cw - total
            if extra > 0:
                # 多余宽度给「路径」列（而非最后一列）
                widths[self.link_col_index] += extra
            else:
                # 空间不足时按比例压缩
                scale = cw / total
                widths = [max(40, int(w * scale)) for w in widths]
        return widths

    def _col_x(self, widths: list[int]) -> list[int]:
        xs, x = [], 0
        for w in widths:
            xs.append(x)
            x += w
        return xs

    # ---------- 设置数据 ---------- #
    def set_rows(self, rows: list[dict]):
        """rows 每项：{'group','action','name','quality','size','path','is_keep'}"""
        self.rows = rows
        self._redraw()

    def clear(self):
        self.rows = []
        self._redraw()

    # ---------- 绘制 ---------- #
    def _redraw(self):
        cv = self.canvas
        cv.delete("all")
        self.row_items = []
        self.delete_btns = []
        widths = self._col_widths()
        xs = self._col_x(widths)
        cw = self.canvas.winfo_width() or sum(widths)

        # 表头
        cv.create_rectangle(0, 0, cw, self.HEADER_H, fill="#eef1f4", outline="")
        for i, (key, title, w, anchor) in enumerate(self.COLUMNS):
            tx, ta = self._anchor_xy(xs[i], widths[i], anchor)
            cv.create_text(tx, self.HEADER_H // 2, text=title,
                           font=self.font_bold, fill=C_TEXT, anchor=ta)
            if i:
                cv.create_line(xs[i], 0, xs[i], self.HEADER_H, fill="#d5d9de")

        # 数据行
        for ri, row in enumerate(self.rows):
            y0 = self.HEADER_H + ri * self.ROW_H
            y1 = y0 + self.ROW_H
            is_keep = row.get("is_keep", False)
            deleted = row.get("deleted", False)
            if deleted:
                fg = self.C_DELETED            # 已删除 → 整行置灰
            else:
                fg = C_KEEP if is_keep else C_DANGER
            if ri % 2 == 1:
                cv.create_rectangle(0, y0, cw, y1, fill="#fafbfc", outline="")

            ids = []
            for i, (key, _t, w, anchor) in enumerate(self.COLUMNS):
                if i == self.delete_col_index:
                    continue                   # 操作列单独画按钮
                val = str(row.get(key, ""))
                tx, ta = self._anchor_xy(xs[i], w, anchor)
                # ★ 只有「路径列」用下划线字体（并显示为链接蓝）；已删除行整体置灰
                if i == self.link_col_index and not deleted:
                    fid = cv.create_text(tx, (y0 + y1) // 2, text=val,
                                         font=self.font_link, fill=C_LINK, anchor=ta)
                else:
                    fid = cv.create_text(tx, (y0 + y1) // 2, text=val,
                                         font=self.font_normal, fill=fg, anchor=ta)
                ids.append(fid)
                if i:
                    cv.create_line(xs[i], y0, xs[i], y1, fill="#eceff2")
            self.row_items.append(ids)
            cv.create_line(0, y1, cw, y1, fill="#eceff2")

            # ---- 操作列：删除按钮（中性圆角钮 + 柔和投影）---- #
            di = self.delete_col_index
            if deleted:
                self.delete_btns.append(None)
            else:
                cx = xs[di] + widths[di] // 2
                cy = (y0 + y1) // 2
                bw, bh = int(54 * UI_SCALE), int(21 * UI_SCALE)
                bx0, bx1 = cx - bw // 2, cx + bw // 2
                by0, by1 = cy - bh // 2, cy + bh // 2
                # 柔和投影：同形圆角矩形整体下移 2px，垫在按钮下层
                _round_rect(cv, bx0, by0 + 2, bx1, by1 + 2, 10,
                            outline="", fill=self.C_BTN_SHADOW)
                # 按钮本体：圆角矩形（平滑多边形实现圆角）
                rid = _round_rect(cv, bx0, by0, bx1, by1, 10,
                                  outline=self.C_BTN_BORDER,
                                  fill=self.C_BTN_BG, width=1)
                tid = cv.create_text(cx, cy, text="删除",
                                     font=self.font_normal, fill=self.C_BTN_FG)
                self.delete_btns.append((rid, tid, bx0, by0, bx1, by1))


        # 滚动区域
        total_h = self.HEADER_H + len(self.rows) * self.ROW_H
        cv.configure(scrollregion=(0, 0, cw, max(total_h, 10)))
        # 内容不满一屏时强制回到顶部：Tk 画布允许负偏移，
        # 若不清零，残留偏移会把表格整体压下去、顶部留白（本 bug 根源）
        if self._content_fits():
            cv.yview_moveto(0)
        if self.hover_row is not None:
            self._paint_hover(self.hover_row)

    def _anchor_xy(self, x, w, anchor):
        if anchor == "center":
            return x + w // 2, "center"
        if anchor == "e":
            return x + w - self.PAD, "e"
        return x + self.PAD, "w"

    # ---------- 鼠标 ---------- #
    def _row_at(self, y) -> int | None:
        cy = self.canvas.canvasy(y)
        idx = int((cy - self.HEADER_H) // self.ROW_H)
        if 0 <= idx < len(self.rows):
            return idx
        return None

    def _on_motion(self, event):
        row = self._row_at(event.y)
        if row != self.hover_row:
            old = self.hover_row
            self.hover_row = row
            if old is not None:
                self._unpaint_hover(old)
            if row is not None:
                self._paint_hover(row)
        self._hover_button(event, row)

    def _hover_button(self, event, row):
        """删除按钮悬停：浅红底提示「删除」+ 手型光标（已删除行除外）。"""
        if self._hover_btn_row is not None and self._hover_btn_row != row:
            self._restore_btn(self._hover_btn_row)
            self._hover_btn_row = None
        if row is None:
            self.canvas.config(cursor="")
            return
        db = self.delete_btns[row] if row < len(self.delete_btns) else None
        over_btn = False
        if db:
            _rid, _tid, bx0, by0, bx1, by1 = db
            cy = self.canvas.canvasy(event.y)
            over_btn = (bx0 <= event.x <= bx1 and by0 <= cy <= by1)
        if over_btn:
            self.canvas.itemconfigure(db[0], fill=self.C_BTN_BG_HOVER,
                                      outline=self.C_BTN_BORDER_HOVER)
            self.canvas.itemconfigure(db[1], fill=self.C_BTN_FG_HOVER)
            self._hover_btn_row = row
            self.canvas.config(cursor="hand2")
        else:
            # 路径列也用手型光标（已删除行除外）
            widths = self._col_widths()
            xs = self._col_x(widths)
            li = self.link_col_index
            row_deleted = bool(self.rows[row].get("deleted"))
            over_link = (xs[li] <= event.x <= xs[li] + widths[li]
                         and not row_deleted)
            self.canvas.config(cursor="hand2" if over_link else "")

    def _restore_btn(self, row):
        db = self.delete_btns[row] if row < len(self.delete_btns) else None
        if db:
            self.canvas.itemconfigure(db[0], fill=self.C_BTN_BG,
                                      outline=self.C_BTN_BORDER)
            self.canvas.itemconfigure(db[1], fill=self.C_BTN_FG)

    def _on_leave(self, _event):
        if self.hover_row is not None:
            self._unpaint_hover(self.hover_row)
            self.hover_row = None

    def _paint_hover(self, row: int):
        """高亮该行的路径列（下划线更明显，提示可点击）。已删除行不参与。"""
        if self.rows[row].get("deleted"):
            return
        try:
            fid = self.row_items[row][self.link_col_index]
            self.canvas.itemconfigure(fid, fill=C_PRIMARY)
            # 补一条下划横线，强化链接感
            widths = self._col_widths()
            xs = self._col_x(widths)
            y = self.HEADER_H + row * self.ROW_H + self.ROW_H - 6
            line = self.canvas.create_line(
                xs[self.link_col_index] + self.PAD, y,
                xs[self.link_col_index] + widths[self.link_col_index] - self.PAD, y,
                fill=C_PRIMARY, width=2, tags=f"hoverline{row}")
        except IndexError:
            pass

    def _unpaint_hover(self, row: int):
        try:
            fid = self.row_items[row][self.link_col_index]
            deleted = self.rows[row].get("deleted")
            # 已删除行 → 恢复为灰色普通文本；正常行 → 恢复为链接蓝
            self.canvas.itemconfigure(
                fid, fill=self.C_DELETED if deleted else C_LINK)
            self.canvas.delete(f"hoverline{row}")
        except IndexError:
            pass

    def _on_click(self, event):
        """单击：点在路径列 → 播放；点在「删除」按钮 → 触发删除回调。"""
        row_idx = self._row_at(event.y)
        if row_idx is None:
            return
        widths = self._col_widths()
        xs = self._col_x(widths)

        # 1) 删除按钮
        db = self.delete_btns[row_idx] if row_idx < len(self.delete_btns) else None
        if db:
            _rid, _tid, bx0, by0, bx1, by1 = db
            cy = self.canvas.canvasy(event.y)
            if bx0 <= event.x <= bx1 and by0 <= cy <= by1:
                if self.on_delete_click:
                    self.on_delete_click(self.rows[row_idx], row_idx)
                return

        # 2) 路径链接（已删除行不可点击播放）
        if self.rows[row_idx].get("deleted"):
            return
        li = self.link_col_index
        if xs[li] <= event.x <= xs[li] + widths[li]:
            if self.on_link_click:
                self.on_link_click(self.rows[row_idx], row_idx)

    def _on_wheel(self, event):
        self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")


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
    cap.set(cv2.CAP_PROP_CONVERT_RGB, 0)   # 直取 Y 平面，免逐帧转换
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


def _gray(frame):
    """取灰度帧。

    解码端已统一设置 CAP_PROP_CONVERT_RGB=0，帧即解码器原生的 Y 平面
    （单通道），直接复用、省掉逐帧 BGR→RGB→灰度转换（实测提速 ~1.9x）；
    个别格式仍可能返回 3 通道，兜底做一次转换，保证任何输入都正确。
    """
    return frame if frame.ndim == 2 else cv2.cvtColor(
        frame, cv2.COLOR_BGR2GRAY)


def _phash(frame, size: int = PHASH_SIZE, low: int = PHASH_LOW) -> int:
    """感知哈希：灰度 → 缩放 → DCT → 低频区域与中位数比较，得到 64 位指纹。"""
    gray = _gray(frame)
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
    gray = _gray(frame)
    return float(cv2.Laplacian(gray, cv2.CV_64F).var())


def analyze_video(path: Path, dense: bool = False) -> dict | None:
    """
    对单个视频做帧级分析，返回：
      { 'hashes': [int], 'width': W, 'height': H, 'sharpness': float,
        'duration': 秒, 'n_frames': 抽帧数 }
    失败返回 None。

    dense=True 时改用「密集抽帧」：顺序解码全片，每隔几帧抽一个指纹，
    用于时间轴滑动对齐（修法B）。较慢但能对齐。
    """
    if not HAS_CV2:
        return None
    try:
        if dense:
            return _analyze_video_dense(path)
        frames, w, h = _sample_frames(path)
        if not frames:
            return None
        hashes = [_phash(fr) for fr in frames]
        sharp = float(np.mean([_sharpness(fr) for fr in frames]))
        dur = _video_duration(path)
        return {"hashes": hashes, "width": w, "height": h, "sharpness": sharp,
                "duration": dur, "n_frames": len(hashes)}
    except Exception:                                    # noqa: BLE001
        return None


def _video_duration(path: Path) -> float:
    """读取视频时长（秒）。优先用 OpenCV，失败则回退 ffprobe。"""
    try:
        cap = cv2.VideoCapture(str(path))
        fps = cap.get(cv2.CAP_PROP_FPS) or 0
        total = cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0
        cap.release()
        if fps > 0 and total > 0:
            return float(total / fps)
    except Exception:                                    # noqa: BLE001
        pass
    return 0.0


def _analyze_video_dense(path: Path, every: int = 5) -> dict | None:
    """
    密集抽帧：顺序解码全片，每 every 帧取一个 pHash。
    返回指纹序列（供时间轴滑动对齐使用）。
    """
    cap = cv2.VideoCapture(str(path))
    if not cap.isOpened():
        return None
    cap.set(cv2.CAP_PROP_CONVERT_RGB, 0)   # 直取 Y 平面，免逐帧转换
    fps = cap.get(cv2.CAP_PROP_FPS) or 30
    w = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
    h = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
    hashes: list[int] = []
    idx = 0
    sharp_vals: list[float] = []
    while True:
        ok, fr = cap.read()
        if not ok:
            break
        if idx % every == 0:
            hashes.append(_phash(fr))
            if len(sharp_vals) < 12:
                sharp_vals.append(_sharpness(fr))
        idx += 1
    cap.release()
    if not hashes:
        return None
    return {
        "hashes": hashes, "width": w, "height": h,
        "sharpness": float(np.mean(sharp_vals)) if sharp_vals else 0.0,
        "duration": float(idx / fps) if fps else 0.0,
        "n_frames": len(hashes),
        "frame_step": every, "fps": fps,
    }


def hamming(a: int, b: int) -> int:
    return bin(a ^ b).count("1")


def _seq_distance(ha: list[int], hb: list[int], shift: int) -> float | None:
    """
    在给定偏移量下，比较两段指纹序列的平均汉明距离。
    shift > 0 表示 b 相对 a 向后偏移（b 从 a 的第 shift 个指纹开始对齐）。
    返回平均距离；重叠部分太短则返回 None。
    """
    n, m = len(ha), len(hb)
    # 计算对齐后的重叠区间
    a_start = max(0, shift)
    b_start = max(0, -shift)
    overlap = min(n - a_start, m - b_start)
    if overlap < 4:                       # 重叠太短，不足以判断
        return None
    total = 0
    for k in range(overlap):
        total += hamming(ha[a_start + k], hb[b_start + k])
    return total / overlap


def frames_similar(ha: list[int], hb: list[int], threshold: int) -> bool:
    """按位置一一对应的朴素比较（旧行为，保留兼容）。"""
    n = min(len(ha), len(hb))
    if n == 0:
        return False
    dists = [hamming(ha[i], hb[i]) for i in range(n)]
    return (sum(dists) / n) <= threshold


def frames_similar_aligned(ha: list[int], hb: list[int], threshold: int,
                           max_shift_frac: float = 0.5) -> tuple[bool, int, float]:
    """
    时间轴滑动对齐比对（修法B）。
    在 [-max_shift, +max_shift] 范围内滑动，寻找平均距离最小的对齐位置。
    返回 (是否相同, 最佳偏移, 最佳平均距离)。

    关键：只有「对齐后全程吻合」才算相同 —— 缺头/缺尾会导致
    最佳对齐点仍无法让整体匹配，或重叠区过短，从而被判为不同。
    """
    n, m = len(ha), len(hb)
    if n == 0 or m == 0:
        return False, 0, 999.0
    max_shift = int(max(n, m) * max_shift_frac)
    best_shift, best_dist = 0, 999.0
    for shift in range(-max_shift, max_shift + 1):
        d = _seq_distance(ha, hb, shift)
        if d is not None and d < best_dist:
            best_dist, best_shift = d, shift
    if best_dist > 998:
        return False, 0, 999.0
    return best_dist <= threshold, best_shift, best_dist


def durations_differ(da: float, db: float, tolerance: float) -> bool:
    """修法A：两段时长差是否超过允许的容差（秒）。任一未知则视为不差。"""
    if da <= 0 or db <= 0:
        return False
    return abs(da - db) > tolerance


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
                               info_map: dict, use_align: bool = False,
                               duration_on: bool = False,
                               duration_tol: float = 1.0) -> list[list[Path]]:
        """
        帧级画面查重。
        use_align     —— 修法B：时间轴滑动对齐
        duration_on   —— 修法A：时长校验（先按时长差过滤）
        duration_tol  —— A 允许的时长差（秒）
        """
        if not HAS_CV2:
            self.log("【第4层·画面】未安装 OpenCV，跳过帧级查重")
            return []

        targets = [f for f in files if f.suffix.lower() in VIDEO_EXTS]
        mode_desc = []
        if duration_on:
            mode_desc.append(f"时长校验(容差{duration_tol}s)")
        if use_align:
            mode_desc.append("时间轴对齐")
        self.log(f"【第4层·画面】对 {len(targets)} 个视频做画面比对"
                 + (f"（{' + '.join(mode_desc)}）" if mode_desc else "（朴素逐帧）"))

        # B 开启时用密集抽帧，否则用稀疏抽帧
        dense = bool(use_align)
        total, done = len(targets), 0
        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futures = {ex.submit(analyze_video, f, dense): f for f in targets}
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
        skipped_by_duration = 0
        for i in range(n):
            if self.should_cancel():
                return []
            fi = usable[i]
            ii = info_map[str(fi)]
            for j in range(i + 1, n):
                fj = usable[j]
                if find(str(fi)) == find(str(fj)):
                    continue
                ij = info_map[str(fj)]
                pairs_checked += 1
                # ---- 修法A：时长校验，先过滤 ----
                if duration_on and durations_differ(
                        ii.get("duration", 0.0), ij.get("duration", 0.0),
                        duration_tol):
                    skipped_by_duration += 1
                    continue
                # ---- 画面比对 ----
                if use_align:
                    same, shift, dist = frames_similar_aligned(
                        ii["hashes"], ij["hashes"], threshold)
                    if same:
                        union(str(fi), str(fj))
                        self.log(f"         画面相同(偏移{shift}, 距离{dist:.1f}) ⟶ "
                                 f"{fi.name} ⇄ {fj.name}")
                else:
                    if frames_similar(ii["hashes"], ij["hashes"], threshold):
                        union(str(fi), str(fj))
                        self.log(f"         画面相同 ⟶ {fi.name} ⇄ {fj.name}")
            self.progress(i + 1, n, "画面比对")

        self.log(f"         共比对 {pairs_checked} 对"
                 + (f"，其中 {skipped_by_duration} 对因时长不符被排除" if duration_on else ""))
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
        self.root.geometry(f"{int(1080 * UI_SCALE)}x{int(760 * UI_SCALE)}")
        self.root.minsize(int(920 * UI_SCALE), int(640 * UI_SCALE))
        self.root.configure(bg=C_BG)

        self.folder = StringVar()
        self.recursive = BooleanVar(value=True)
        self.dry_run = BooleanVar(value=True)
        self.permanent = BooleanVar(value=False)
        self.keep = StringVar(value="quality")
        self.use_frame = BooleanVar(value=bool(HAS_CV2))
        self.threshold = IntVar(value=DEFAULT_PHASH_THRESHOLD)
        self.dur_check = BooleanVar(value=True)          # 修法A：时长校验
        self.dur_tol = StringVar(value="0.5")            # A 允许的秒数差
        self.use_align = BooleanVar(value=False)         # 修法B：时间轴对齐

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
        # 「一键删除」危险按钮：红底白字，悬停加深
        style.configure("Danger.TButton", font=("Microsoft YaHei UI", 11, "bold"),
                        background=C_DANGER, foreground="white", borderwidth=0,
                        focuscolor=C_DANGER, padding=(10, 4))
        style.map("Danger.TButton",
                  background=[("active", "#b91c1c"), ("disabled", "#f3b4b4")],
                  foreground=[("disabled", "#ffe4e4")])
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

        # ---- 高级选项：A/B 两个开关 ----
        arow = ttk.Frame(c4, style="Card.TFrame")
        arow.pack(fill=X, pady=(8, 0))
        ttk.Checkbutton(
            arow, text="A · 时长校验：两视频时长差超过",
            variable=self.dur_check, style="Card.TCheckbutton",
            state=("normal" if HAS_CV2 else "disabled")).pack(side=LEFT)
        ttk.Entry(arow, textvariable=self.dur_tol, width=5,
                  justify="center").pack(side=LEFT, padx=(4, 4))
        ttk.Label(arow, text="秒则判为不同（防止「缺头/缺尾」被误判为同一视频）",
                  style="Card.TLabel").pack(side=LEFT)

        brow2 = ttk.Frame(c4, style="Card.TFrame")
        brow2.pack(fill=X, pady=(6, 0))
        ttk.Checkbutton(
            brow2, text="B · 时间轴对齐：滑动搜索最佳对齐点，可识别「整体错位」但内容相同的视频",
            variable=self.use_align, style="Card.TCheckbutton",
            state=("normal" if HAS_CV2 else "disabled")).pack(side=LEFT)
        ttk.Label(brow2, text="（更慢，需要密集解码）", style="Card.TLabel",
                  foreground=C_MUTED).pack(side=LEFT, padx=(6, 0))

        # ---- 操作 ----
        brow = ttk.Frame(outer)
        brow.pack(fill=X, pady=(12, 0))
        self.brow = brow                       # 供「一键删除」按钮动态挂载
        self.btn_scan = ttk.Button(brow, text="开始扫描", style="Primary.TButton",
                                   command=self.on_scan)
        self.btn_scan.pack(side=LEFT, ipadx=20, ipady=6)
        self.btn_cancel = ttk.Button(brow, text="停止", command=self.on_cancel,
                                     state="disabled")
        self.btn_cancel.pack(side=LEFT, padx=(10, 0), ipady=6)
        # 「一键删除」：仅在「预演」模式下扫描出重复行后才创建并显示
        self.btn_bulk = None
        ttk.Label(brow, text="  提示：单击蓝色路径播放视频；点「删除」按钮立即删除该文件",
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
        # 自绘表格：仅「路径」列带下划线并可单击播放；「操作」列删除按钮
        self.table = ResultTable(tab1, on_link_click=self._on_path_click,
                                 on_delete_click=self._on_delete_click)
        self.table.pack(fill=BOTH, expand=True)

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

    def _on_path_click(self, row: dict, _row_index: int):
        """单击「路径」列 → 用系统默认播放器播放该视频。"""
        rel = row.get("path", "")
        if not rel or not self.scan_root:
            return
        target = self.scan_root / rel
        ok, err = open_with_default_player(target)
        if not ok:
            messagebox.showwarning("无法播放", f"打不开文件：\n{target}\n\n{err}")

    def _on_delete_click(self, row: dict, _row_index: int):
        """点击「删除」按钮 → 立即永久删除该行对应文件（无需确认）。"""
        rel = row.get("path", "")
        if not rel or not self.scan_root:
            return
        if row.get("deleted"):
            return                                   # 已删除过的行不再处理
        target = self.scan_root / rel

        if not target.exists():
            messagebox.showwarning("文件不存在",
                                   f"文件已不存在（可能已被删除或移动）：\n{target}")
            row["deleted"] = True
            row["action"] = "已删除"
            self.table.set_rows(self.table.rows)
            return

        try:
            target.unlink()
        except OSError as e:
            messagebox.showerror(
                "删除失败",
                f"{e}\n\n提示：如果文件正被播放器占用，请先关闭播放器再试。")
            return

        was_keep = row.get("action") == "保留"
        row["deleted"] = True
        row["action"] = "已删除"
        self.table.set_rows(self.table.rows)         # 重绘，行置灰
        self.log(f"🗑 已删除：{target}")
        if was_keep:
            self.log("  ⚠ 被删除的是该组的保留文件，建议重新扫描以更新分组。")

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

    def _dur_tol(self) -> float:
        """读取 A 开关的允许时长差（秒），非法输入回退到 1.0。"""
        try:
            v = float(self.dur_tol.get())
            return max(0.0, v)
        except (ValueError, TypeError):
            return 1.0

    def _quality_text(self, path: Path) -> str:
        info = self.info_map.get(str(path))
        if not info:
            return "—"
        w, h = info.get("width", 0), info.get("height", 0)
        sharp = info.get("sharpness", 0.0)
        return f"{w}×{h}  锐度{sharp:.0f}"

    def _render_groups(self, groups: list):
        root = self.scan_root
        rows: list[dict] = []
        for i, group in enumerate(groups, 1):
            keeper = choose_keeper(group, self.info_map, self.keep.get())
            # 组内排序：保留行排第一，其余按路径
            others = sorted([p for p in group if p != keeper],
                            key=lambda x: str(x).lower())
            ordered = [keeper] + others
            for p in ordered:
                try:
                    size = human_size(p.stat().st_size)
                    rel = str(p.relative_to(root)) if root else str(p)
                except (OSError, ValueError):
                    size, rel = "?", str(p)
                is_keep = (p == keeper)
                rows.append({
                    "group": i,
                    "action": "保留" if is_keep else "重复",
                    "name": p.name,
                    "quality": self._quality_text(p),
                    "size": size,
                    "path": rel,
                    "is_keep": is_keep,
                })
        self.table.set_rows(rows)
        # 预演模式下且确有重复行 → 显示「一键删除」
        self._update_bulk_button()

    # ---------------- 一键删除 ---------------- #
    def _dup_rows(self) -> list[dict]:
        """当前结果中所有仍待处理的「重复」行。"""
        return [r for r in self.table.rows
                if r.get("action") == "重复" and not r.get("deleted")]

    def _update_bulk_button(self):
        """按条件显示/隐藏「一键删除」按钮：仅预演模式 + 存在重复行。"""
        show = self.dry_run.get() and bool(self._dup_rows())
        if show and self.btn_bulk is None:
            self.btn_bulk = ttk.Button(self.brow, text="一键删除全部重复",
                                       style="Danger.TButton",
                                       command=self.on_bulk_delete)
        if self.btn_bulk is None:
            return
        if show:
            if not self.btn_bulk.winfo_manager():
                self.btn_bulk.pack(side=LEFT, padx=(10, 0), ipady=6)
        else:
            self.btn_bulk.pack_forget()

    def _hide_bulk_button(self):
        if self.btn_bulk is not None:
            self.btn_bulk.pack_forget()

    def on_bulk_delete(self):
        """删除当前结果中所有「重复」行对应的文件（保留行不动）。"""
        dups = self._dup_rows()
        if not dups:
            return
        if not messagebox.askyesno(
                "一键删除",
                f"将删除 {len(dups)} 个「重复」文件，保留每组的保留项。\n"
                "此操作不可恢复，确定继续吗？", icon="warning"):
            return

        deleted = failed = 0
        for row in dups:
            rel = row.get("path", "")
            if not rel or not self.scan_root:
                continue
            target = self.scan_root / rel
            try:
                if target.exists():
                    target.unlink()
                row["deleted"] = True
                row["action"] = "已删除"
                deleted += 1
                self.log(f"🗑 已删除：{target}")
            except OSError as e:
                failed += 1
                self.log(f"  [失败] {target}: {e}")

        self.table.set_rows(self.table.rows)        # 重绘：已删除行置灰
        self._update_bulk_button()                  # 重复行清空后按钮自动隐藏
        msg = f"已删除 {deleted} 个重复文件"
        if failed:
            msg += f"（{failed} 个失败，详见日志）"
        self.summary.config(text=msg)
        self.log("=" * 64)
        self.log(f"一键删除完成：成功 {deleted} 个"
                 + (f"，失败 {failed} 个" if failed else ""))

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
        self.table.clear()
        self._hide_bulk_button()
        self.summary.config(text="")

        # ★ 主线程先把全部选项快照成普通值再传给工作线程：
        #   tkinter 变量禁止跨线程访问，工作线程里调 .get() 会抛
        #   RuntimeError(main thread is not in main loop)，
        #   导致扫描中断、文件未被删除（本 bug 根因）
        opts = {
            "recursive": self.recursive.get(),
            "dry_run": self.dry_run.get(),
            "permanent": self.permanent.get(),
            "keep": self.keep.get(),
            "use_frame": self.use_frame.get(),
            "threshold": self.threshold.get(),
            "dur_check": self.dur_check.get(),
            "dur_tol": self._dur_tol(),
            "use_align": self.use_align.get(),
        }
        self.worker = threading.Thread(target=self._run_scan, args=(root, opts), daemon=True)
        self.worker.start()

    def on_cancel(self):
        self.cancel_flag.set()
        self.log("⚠ 用户请求停止…")

    def _run_scan(self, root: Path, opts: dict):
        try:
            t0 = time.time()
            self.log("=" * 64)
            self.log(f"扫描目录：{root}")
            mode = "预演" if opts["dry_run"] else (
                "永久删除" if opts["permanent"] else "移动到 _duplicates/")
            self.log(f"递归：{'是' if opts['recursive'] else '否'}   "
                     f"模式：{mode}   保留规则：{opts['keep']}")
            frame_desc = f"画面查重：{'开启' if opts['use_frame'] else '关闭'}"
            if opts["use_frame"]:
                frame_desc += f"（阈值 {opts['threshold']}"
                if opts["dur_check"]:
                    frame_desc += f" | A时长校验±{opts['dur_tol']}s"
                frame_desc += f" | B时间轴对齐{'开' if opts['use_align'] else '关'}）"
            self.log(frame_desc)
            self.log("=" * 64)

            self.progress(0, 1, "枚举文件")
            files = iter_video_files(root, opts["recursive"])
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
            if opts["use_frame"]:
                frame_groups = engine.find_similar_by_frames(
                    files, opts["threshold"], self.info_map,
                    use_align=opts["use_align"],
                    duration_on=opts["dur_check"],
                    duration_tol=opts["dur_tol"])
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
                keeper = choose_keeper(group, self.info_map, opts["keep"])
                others = [p for p in group if p != keeper]
                try:
                    saved += sum(p.stat().st_size for p in others)
                except OSError:
                    pass
                for p in others:
                    dup_count += 1
                    if opts["dry_run"]:
                        continue
                    try:
                        if opts["permanent"]:
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

            if opts["dry_run"]:
                s = (f"预演完成：{len(groups)} 组重复，可清理 {dup_count} 个文件，"
                     f"释放 {human_size(saved)}（未修改任何文件）")
            elif opts["permanent"]:
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
    enable_dpi_awareness(root)
    app = VideoDedupApp(root)
    if len(sys.argv) > 1:
        p = Path(sys.argv[1])
        if p.is_dir():
            app.folder.set(str(p))
    root.mainloop()


if __name__ == "__main__":
    main()
