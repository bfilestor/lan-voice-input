# server.py
# -*- coding: utf-8 -*-
import asyncio
import ctypes
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
import tkinter as tk
from ctypes import wintypes
from dataclasses import dataclass
from tkinter import ttk
from typing import List, Tuple, Optional, Set
import shlex

import pyautogui
import pystray
import qrcode
import websockets
from PIL import Image, ImageTk, ImageDraw
from flask import Flask, send_file, jsonify
from pystray import MenuItem as item
from websockets.exceptions import ConnectionClosed, ConnectionClosedError, ConnectionClosedOK

# queue 用于 Tk 线程
import queue

# Windows Toast：winotify
try:
    from winotify import Notification

    WINOTIFY_AVAILABLE = True
except Exception:
    WINOTIFY_AVAILABLE = False

# ===================== 默认端口（自动选择可用）=====================
DEFAULT_HTTP_PORT = 8080
DEFAULT_WS_PORT = 8765
MAX_PORT_TRY = 50

# ===================== 行为配置 =====================
FORCE_CLICK_BEFORE_TYPE = True
FOCUS_SETTLE_DELAY = 0.06

# 只在切换窗口时点击一次，避免每次输入都把光标点回鼠标位置
_LAST_FG_HWND = None

CLEAR_BACKSPACE_MAX = 200
TEST_INJECT_TEXT = "[SendInput Test] 123 ABC 中文 测试"

SERVER_DEDUP_WINDOW_SEC = 1.2

# WebSocket 心跳（让断线更快被识别）
WS_PING_INTERVAL = 20
WS_PING_TIMEOUT = 10

# ===================== 全局状态 =====================
HTTP_PORT: Optional[int] = None
WS_PORT: Optional[int] = None
QR_URL: Optional[str] = None
QR_PAYLOAD_URL: Optional[str] = None

tray_icon = None

CLIENT_COUNT = 0
CLIENT_LOCK = threading.Lock()
WS_CLIENTS: Set[websockets.WebSocketServerProtocol] = set()
WS_LOOP: Optional[asyncio.AbstractEventLoop] = None

# ✅ 用户手动选择的 IP（None = 自动）
USER_IP: Optional[str] = None
CONFIG_DATA: dict = {}
COMMANDS: List[dict] = []


# ===================== PyInstaller 路径工具 =====================
def is_frozen() -> bool:
    return getattr(sys, "frozen", False) is True


def get_exe_dir() -> str:
    """打包后：exe 同级目录；源码：server.py 同级目录"""
    if is_frozen():
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def get_resource_dir() -> str:
    """
    资源目录：
    - onefile 打包：sys._MEIPASS（解压到临时目录，index.html 在这里）
    - 其他情况：server.py 同级目录
    """
    if is_frozen() and hasattr(sys, "_MEIPASS"):
        return getattr(sys, "_MEIPASS")
    return os.path.dirname(os.path.abspath(__file__))


def resource_path(name: str) -> str:
    return os.path.join(get_resource_dir(), name)


# ===================== 配置持久化（优先写 exe 同级 config.json，写失败 fallback 到用户目录）=====================
CONFIG_PATH_PRIMARY = os.path.join(get_exe_dir(), "config.json")
CONFIG_PATH_FALLBACK = os.path.join(os.path.expanduser("~"), "LanVI_config.json")
CONFIG_PATH_IN_USE = CONFIG_PATH_PRIMARY  # 运行时可能切到 fallback


def _try_write_json(path: str, data: dict) -> bool:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        return True
    except Exception:
        return False


def _try_read_json(path: str) -> Optional[dict]:
    try:
        if not os.path.exists(path):
            return None
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def _normalize_commands(raw) -> List[dict]:
    if not isinstance(raw, list):
        return []
    return [c for c in raw if isinstance(c, dict)]


def load_config():
    """
    启动时读取 config：
    - 优先 exe 同级 config.json
    - 否则读取用户目录 LanVI_config.json
    - 两边都没有：创建（优先主路径，失败则 fallback）
    """
    global USER_IP, CONFIG_PATH_IN_USE, CONFIG_DATA, COMMANDS

    # 先读主路径
    data = _try_read_json(CONFIG_PATH_PRIMARY)
    if isinstance(data, dict):
        CONFIG_DATA = data
        COMMANDS = _normalize_commands(data.get("commands"))
        ip = (data.get("user_ip") or "").strip()
        USER_IP = ip if ip else None
        CONFIG_PATH_IN_USE = CONFIG_PATH_PRIMARY
        return

    # 再读 fallback
    data = _try_read_json(CONFIG_PATH_FALLBACK)
    if isinstance(data, dict):
        CONFIG_DATA = data
        COMMANDS = _normalize_commands(data.get("commands"))
        ip = (data.get("user_ip") or "").strip()
        USER_IP = ip if ip else None
        CONFIG_PATH_IN_USE = CONFIG_PATH_FALLBACK
        return

    # 都没有：创建默认（自动）
    USER_IP = None
    CONFIG_DATA = {"user_ip": None, "commands": []}
    COMMANDS = []
    save_config()


def save_config():
    """
    保存当前 USER_IP：
    - 优先写 exe 同级 config.json（你期望的位置）
    - 若无权限/失败：写到用户目录，并切换 CONFIG_PATH_IN_USE
    """
    global CONFIG_PATH_IN_USE, CONFIG_DATA, COMMANDS
    data = dict(CONFIG_DATA) if isinstance(CONFIG_DATA, dict) else {}
    data["user_ip"] = USER_IP
    data["commands"] = COMMANDS

    # 优先写主路径（exe 同级）
    if _try_write_json(CONFIG_PATH_PRIMARY, data):
        CONFIG_PATH_IN_USE = CONFIG_PATH_PRIMARY
        return

    # 主路径失败则写 fallback（保证一定能保存）
    if _try_write_json(CONFIG_PATH_FALLBACK, data):
        CONFIG_PATH_IN_USE = CONFIG_PATH_FALLBACK
        return


# ===================== 通知封装 =====================
def notify(title: str, msg: str, duration=3):
    """托盘气泡 + Windows Toast（winotify），永不抛异常影响主程序"""
    global tray_icon

    # 托盘气泡（稳定兜底）
    try:
        if tray_icon:
            tray_icon.notify(msg, title)
    except Exception:
        pass

    # Windows Toast（winotify）
    if not WINOTIFY_AVAILABLE:
        return

    def _toast():
        try:
            toast = Notification(
                app_id="LAN Voice Input",
                title=title,
                msg=msg,
                duration="short"
            )
            toast.show()
        except Exception:
            pass

    threading.Thread(target=_toast, daemon=True).start()


# ===================== 自动选择可用端口 =====================
def is_port_free(port: int) -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("0.0.0.0", port))
            return True
    except OSError:
        return False


def choose_free_port(start_port: int) -> int:
    for p in range(start_port, start_port + MAX_PORT_TRY):
        if is_port_free(p):
            return p
    raise RuntimeError(f"找不到可用端口（从 {start_port} 起尝试 {MAX_PORT_TRY} 个）")


# ===================== IP & 网卡枚举 =====================
def get_lan_ip_best_effort() -> str:
    """通过 UDP “假连接”拿到默认出口网卡 IP（不真正发包）。"""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
    except Exception:
        ip = "127.0.0.1"
    finally:
        s.close()
    return ip


def is_valid_ipv4(ip: str) -> bool:
    if not ip:
        return False
    if not re.match(r"^\d{1,3}(\.\d{1,3}){3}$", ip):
        return False
    parts = ip.split(".")
    try:
        nums = [int(x) for x in parts]
    except Exception:
        return False
    return all(0 <= n <= 255 for n in nums)


def is_candidate_ipv4(ip: str) -> bool:
    if not is_valid_ipv4(ip):
        return False
    if ip.startswith("127.") or ip.startswith("0.") or ip.startswith("169.254."):
        return False
    return True


def parse_windows_ipconfig() -> List[Tuple[str, str]]:
    """
    Windows：解析 ipconfig，尽量拿到 "网卡名 + IPv4"
    返回 [(label, ip), ...]
    """
    if os.name != "nt":
        return []

    out = ""
    for enc in ("gbk", "utf-8"):
        try:
            out = subprocess.check_output(
                ["ipconfig"], stderr=subprocess.STDOUT, text=True, encoding=enc, errors="ignore"
            )
            if out:
                break
        except Exception:
            continue
    if not out:
        return []

    results: List[Tuple[str, str]] = []
    current_iface = "未知网卡"

    iface_pat = re.compile(r"^\s*([^\r\n:]{3,}adapter\s+.+):\s*$", re.IGNORECASE)
    ipv4_pat = re.compile(r"IPv4.*?:\s*([0-9]+\.[0-9]+\.[0-9]+\.[0-9]+)")

    for line in out.splitlines():
        m_iface = iface_pat.match(line.strip())
        if m_iface:
            current_iface = m_iface.group(1).strip()
            continue

        m_ip = ipv4_pat.search(line)
        if m_ip:
            ip = m_ip.group(1).strip()
            if is_candidate_ipv4(ip):
                results.append((f"{current_iface} - {ip}", ip))

    seen = set()
    dedup = []
    for label, ip in results:
        if ip not in seen:
            seen.add(ip)
            dedup.append((label, ip))
    return dedup


def get_ipv4_candidates() -> List[Tuple[str, str]]:
    """
    综合获取候选 IP：
    1) Windows: ipconfig（含网卡名）
    2) hostname 的 IPv4
    3) 自动推荐（默认出口）
    """
    candidates: List[Tuple[str, str]] = []
    candidates.extend(parse_windows_ipconfig())

    try:
        hostname = socket.gethostname()
        infos = socket.getaddrinfo(hostname, None, family=socket.AF_INET, type=socket.SOCK_STREAM)
        for info in infos:
            ip = info[4][0]
            if is_candidate_ipv4(ip):
                candidates.append((f"{hostname} - {ip}", ip))
    except Exception:
        pass

    ip2 = get_lan_ip_best_effort()
    if is_candidate_ipv4(ip2):
        candidates.append((f"自动推荐（默认出口） - {ip2}", ip2))

    seen = set()
    dedup: List[Tuple[str, str]] = []
    for label, ip in candidates:
        if ip not in seen:
            seen.add(ip)
            dedup.append((label, ip))

    if not dedup:
        dedup = [("本机回环（仅本机可用） - 127.0.0.1", "127.0.0.1")]
    return dedup


# ===================== URL 构建 =====================
def get_effective_ip() -> str:
    global USER_IP
    if USER_IP and USER_IP.strip():
        return USER_IP.strip()
    return get_lan_ip_best_effort()


def build_urls(ip: str):
    global QR_URL, QR_PAYLOAD_URL
    QR_URL = f"http://{ip}:{HTTP_PORT}"
    QR_PAYLOAD_URL = f"{QR_URL}?ws={WS_PORT}"


# ===================== Tk 二维码窗口（内置网卡选择 + 同步刷新）=====================
class QRWindowManager:
    """只启动一次 Tk mainloop，通过线程安全调用显示/刷新二维码窗口"""

    def __init__(self):
        self.cmd_q = queue.Queue()
        self.thread = threading.Thread(target=self._tk_thread, daemon=True)
        self.thread.start()

    def show(self):
        self.cmd_q.put(("show", None))

    def close(self):
        self.cmd_q.put(("close", None))

    def call(self, fn):
        self.cmd_q.put(("call", fn))

    def _tk_thread(self):
        self.root = tk.Tk()
        self.root.withdraw()
        self.root.title("QRRoot")

        self.top = None
        self.tk_img = None

        self.ip_items: List[Tuple[str, str]] = []
        self.ip_var = tk.StringVar()
        self.combo = None

        self.img_label = None
        self.url_label = None
        self.tip_label = None

        self.root.after(100, self._poll_queue)
        self.root.mainloop()

    def _poll_queue(self):
        try:
            while True:
                cmd, data = self.cmd_q.get_nowait()
                if cmd == "show":
                    self._show_window()
                elif cmd == "close":
                    self._close_window()
                elif cmd == "call":
                    try:
                        data()
                    except Exception:
                        pass
        except queue.Empty:
            pass
        self.root.after(100, self._poll_queue)

    def _close_window(self):
        if self.top is not None:
            try:
                self.top.destroy()
            except Exception:
                pass
        self.top = None
        self.tk_img = None
        self.combo = None
        self.img_label = None
        self.url_label = None
        self.tip_label = None

    def _ensure_window(self):
        if self.top is not None:
            return

        self.top = tk.Toplevel(self.root)
        self.top.title("扫码打开语音输入网页")
        self.top.attributes("-topmost", True)
        self.top.protocol("WM_DELETE_WINDOW", self._close_window)

        header = ttk.Frame(self.top)
        header.pack(fill="x", padx=10, pady=(10, 6))

        ttk.Label(header, text="选择网卡/IP：").pack(side="left")

        self.combo = ttk.Combobox(header, textvariable=self.ip_var, state="readonly", width=48)
        self.combo.pack(side="left", padx=6, fill="x", expand=True)

        btn_auto = ttk.Button(header, text="自动推荐", command=self._on_auto_ip)
        btn_auto.pack(side="left", padx=(6, 0))

        self.combo.bind("<<ComboboxSelected>>", lambda e: self._on_ip_selected())

        self.img_label = ttk.Label(self.top)
        self.img_label.pack(padx=10, pady=10)

        self.url_label = ttk.Label(self.top, font=("Arial", 12))
        self.url_label.pack(padx=10, pady=(0, 6))

        self.tip_label = ttk.Label(self.top, font=("Arial", 10), foreground="#333", justify="center")
        self.tip_label.pack(padx=10, pady=(0, 10))

    def _reload_ip_list_and_select_current(self):
        global USER_IP

        self.ip_items = get_ipv4_candidates()
        labels = [lbl for (lbl, _ip) in self.ip_items]
        self.combo["values"] = labels

        current = (USER_IP or "").strip()
        idx = 0

        if current:
            for i, (_lbl, ip) in enumerate(self.ip_items):
                if ip == current:
                    idx = i
                    break
            else:
                USER_IP = None
                save_config()
                current = ""

        if not current:
            for i, (lbl, _ip) in enumerate(self.ip_items):
                if lbl.startswith("自动推荐"):
                    idx = i
                    break

        if labels:
            self.combo.current(idx)
            self.ip_var.set(labels[idx])

    def _selected_ip(self) -> str:
        label = self.ip_var.get()
        for (lbl, ip) in self.ip_items:
            if lbl == label:
                return ip
        return get_effective_ip()

    def _on_ip_selected(self):
        global USER_IP
        ip = self._selected_ip()
        USER_IP = ip
        save_config()

        build_urls(get_effective_ip())
        self._refresh_qr_and_text()

    def _on_auto_ip(self):
        global USER_IP
        USER_IP = None
        save_config()

        build_urls(get_effective_ip())
        self._reload_ip_list_and_select_current()
        self._refresh_qr_and_text()

    def _refresh_qr_and_text(self):
        url = QR_PAYLOAD_URL or ""
        if not url:
            return

        qr = qrcode.QRCode(box_size=8, border=2)
        qr.add_data(url)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white").convert("RGB")
        self.tk_img = ImageTk.PhotoImage(img)

        self.img_label.configure(image=self.tk_img)
        self.url_label.configure(text=url)

        ip_show = get_effective_ip()
        mode = "手动" if (USER_IP and USER_IP.strip()) else "自动"
        self.tip_label.configure(
            text=f"手机扫码打开网页（同一 WiFi / 同网段）\n"
                 f"模式：{mode}  IP：{ip_show}\n"
                 f"HTTP:{HTTP_PORT}  WS:{WS_PORT}\n"
                 f"关闭此窗口不影响后台运行"
                 f"\n配置文件：{CONFIG_PATH_IN_USE}"
        )

    def _show_window(self):
        self._ensure_window()

        try:
            self.top.deiconify()
            self.top.lift()
            self.top.attributes("-topmost", True)
            self.top.after(200, lambda: self.top.attributes("-topmost", False))
        except Exception:
            pass

        self._reload_ip_list_and_select_current()
        build_urls(get_effective_ip())
        self._refresh_qr_and_text()


qr_mgr = QRWindowManager()

# ===================== Windows SendInput =====================
if not hasattr(wintypes, "ULONG_PTR"):
    wintypes.ULONG_PTR = ctypes.c_size_t

user32 = ctypes.WinDLL("user32", use_last_error=True)
kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

INPUT_KEYBOARD = 1
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_UNICODE = 0x0004
WM_CHAR = 0x0102
VK_BACK = 0x08
VK_RETURN = 0x0D


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", wintypes.LONG),
        ("dy", wintypes.LONG),
        ("mouseData", wintypes.DWORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", wintypes.ULONG_PTR),
    ]


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", wintypes.WORD),
        ("wScan", wintypes.WORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", wintypes.ULONG_PTR),
    ]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [
        ("uMsg", wintypes.DWORD),
        ("wParamL", wintypes.WORD),
        ("wParamH", wintypes.WORD),
    ]


class _INPUTunion(ctypes.Union):
    _fields_ = [
        ("mi", MOUSEINPUT),
        ("ki", KEYBDINPUT),
        ("hi", HARDWAREINPUT),
    ]


class INPUT(ctypes.Structure):
    _anonymous_ = ("union",)
    _fields_ = [("type", wintypes.DWORD), ("union", _INPUTunion)]

class GUITHREADINFO(ctypes.Structure):
    _fields_ = [
        ("cbSize", wintypes.DWORD),
        ("flags", wintypes.DWORD),
        ("hwndActive", wintypes.HWND),
        ("hwndFocus", wintypes.HWND),
        ("hwndCapture", wintypes.HWND),
        ("hwndMenuOwner", wintypes.HWND),
        ("hwndMoveSize", wintypes.HWND),
        ("hwndCaret", wintypes.HWND),
        ("rcCaret", wintypes.RECT),
    ]


def _get_focus_hwnd() -> Optional[int]:
    """获取当前具有键盘焦点的窗口（优先精确控件，失败则退化为前台窗口）。"""
    info = GUITHREADINFO()
    info.cbSize = ctypes.sizeof(GUITHREADINFO)
    try:
        if user32.GetGUIThreadInfo(0, ctypes.byref(info)):
            return info.hwndFocus or info.hwndActive or user32.GetForegroundWindow()
    except Exception:
        pass
    try:
        return user32.GetForegroundWindow()
    except Exception:
        return None


def _try_post_chars(text: str) -> bool:
    """
    优先通过 PostMessage(WM_CHAR) 直接把字符送入当前焦点控件。
    在记事本中 SendInput 会出现“首字符丢失/替换”的问题，WM_CHAR 注入更稳定。
    """
    hwnd = _get_focus_hwnd()
    if not hwnd:
        return False
    ok = True
    for ch in text:
        code = ord(ch)
        if code > 0xFFFF:
            return False  # 16 位之外的码位交给 SendInput 处理
        if user32.PostMessageW(hwnd, WM_CHAR, code, 0) == 0:
            ok = False
    return ok


def _send_input(inputs):
    n = len(inputs)
    arr = (INPUT * n)(*inputs)
    cb = ctypes.sizeof(INPUT)
    sent = user32.SendInput(n, arr, cb)
    if sent != n:
        err = ctypes.get_last_error()
        raise ctypes.WinError(err)


def send_unicode_text(text: str):
    text = text or ""
    if not text:
        return

    # 先尝试 WM_CHAR 注入，解决记事本里首字符被吞的问题
    if _try_post_chars(text):
        return

    inputs = []
    print("⌨️ 输入文本：", text)
    for ch in text:
        code = ord(ch)
        inputs.append(INPUT(
            type=INPUT_KEYBOARD,
            ki=KEYBDINPUT(wVk=0, wScan=code, dwFlags=KEYEVENTF_UNICODE, time=0, dwExtraInfo=0)
        ))
        inputs.append(INPUT(
            type=INPUT_KEYBOARD,
            ki=KEYBDINPUT(wVk=0, wScan=code, dwFlags=KEYEVENTF_UNICODE | KEYEVENTF_KEYUP, time=0, dwExtraInfo=0)
        ))
    _send_input(inputs)


def press_vk(vk_code: int, times: int = 1):
    for _ in range(times):
        down = INPUT(type=INPUT_KEYBOARD, ki=KEYBDINPUT(wVk=vk_code, wScan=0, dwFlags=0, time=0, dwExtraInfo=0))
        up = INPUT(type=INPUT_KEYBOARD, ki=KEYBDINPUT(wVk=vk_code, wScan=0, dwFlags=KEYEVENTF_KEYUP, time=0, dwExtraInfo=0))
        _send_input([down, up])


def backspace(n: int):
    if n > 0:
        press_vk(VK_BACK, times=n)


def press_enter():
    press_vk(VK_RETURN, times=1)


# ===================== 剪贴板读取 =====================
def get_clipboard_text() -> str:
    """Best-effort read clipboard text with small retries and detailed logs."""
    CF_UNICODETEXT = 13
    CF_TEXT = 1

    def _read_handle(handle, is_unicode=False):
        if not handle:
            return "", 0
        size = kernel32.GlobalSize(handle)
        ptr = kernel32.GlobalLock(handle)
        if not ptr:
            return "", size
        try:
            if size:
                raw = ctypes.string_at(ptr, size)
            else:
                # 有些应用返回 0 size，但数据仍可读（例如延迟渲染/特殊分配）
                raw = ctypes.string_at(ptr)  # 读取到首个 \0
        finally:
            kernel32.GlobalUnlock(handle)

        if is_unicode:
            try:
                text = raw.decode("utf-16-le").rstrip("\x00")
                return text, size if size else len(text) * 2
            except Exception:
                return "", size
        else:
            for enc in ("utf-8", "gbk", sys.getdefaultencoding()):
                try:
                    text = raw.decode(enc).rstrip("\x00")
                    return text, size if size else len(text)
                except Exception:
                    continue
            return raw.decode("utf-8", errors="ignore").rstrip("\x00"), size

    for _ in range(5):
        opened = user32.OpenClipboard(None)
        if not opened:
            time.sleep(0.05)
            continue
        try:
            if user32.IsClipboardFormatAvailable(CF_UNICODETEXT):
                txt, _size = _read_handle(user32.GetClipboardData(CF_UNICODETEXT), is_unicode=True)
                if txt:
                    return txt
            elif user32.IsClipboardFormatAvailable(CF_TEXT):
                txt, _size = _read_handle(user32.GetClipboardData(CF_TEXT), is_unicode=False)
                if txt:
                    return txt
            else:
                return ""
        except Exception:
            pass
        finally:
            try:
                user32.CloseClipboard()
            except Exception:
                pass
        time.sleep(0.05)
    # Powershell 兜底：有些应用（远程桌面/沙盒）返回不可锁定的句柄，尝试系统 Get-Clipboard
    try:
        out = subprocess.check_output(
            ["powershell", "-NoProfile", "-Command", "Get-Clipboard -Raw"],
            text=True, stderr=subprocess.STDOUT, timeout=3
        )
        if out:
            return out
    except Exception:
        pass
    return ""


# ===================== 指令系统 =====================
@dataclass
class CommandResult:
    handled: bool
    display_text: str = ""
    output: object = ""


class CommandProcessor:
    def __init__(self):
        self.paused = False
        self.history = []
        self.alias = {"豆号": "逗号", "都好": "逗号", "据号": "句号", "聚好": "句号", "句点": "句号"}
        self.punc_map = {"逗号": "，", "句号": "。", "问号": "？", "感叹号": "！", "冒号": "：", "分号": "；", "顿号": "、"}

    def normalize(self, text: str) -> str:
        text = (text or "").strip()
        for k, v in self.alias.items():
            text = text.replace(k, v)
        return text

    def parse_delete_n(self, text: str):
        m = re.search(r"(删除|退格)\s*(\d+)\s*(个字|次)?", text)
        return int(m.group(2)) if m else None

    def handle(self, raw_text: str) -> CommandResult:
        text = self.normalize(raw_text)

        if text in ["暂停输入", "暂停", "停止输入"]:
            self.paused = True
            return CommandResult(True, "⏸ 已暂停输入", "")

        if text in ["继续输入", "继续", "恢复输入"]:
            self.paused = False
            return CommandResult(True, "▶️ 已恢复输入", "")

        if self.paused:
            return CommandResult(True, f"⏸(暂停中) {raw_text}", "")

        if text in ["换行", "回车", "下一行"]:
            return CommandResult(True, "↩️ 换行", ("__ENTER__", 1))

        if text in self.punc_map:
            return CommandResult(True, f"⌨️ {text}", self.punc_map[text])

        if text in ["删除上一句", "撤回上一句", "撤销上一句", "删掉上一句"]:
            if not self.history:
                return CommandResult(True, "⚠️ 没有可删除的内容", "")
            last = self.history.pop()
            return CommandResult(True, f"⌫ 删除上一句：{last}", ("__BACKSPACE__", len(last)))

        n = self.parse_delete_n(text)
        if n is not None:
            return CommandResult(True, f"⌫ 删除 {n} 个字", ("__BACKSPACE__", n))

        if text in ["清空", "清除全部", "全部删除"]:
            return CommandResult(True, "🧹 清空", ("__BACKSPACE__", CLEAR_BACKSPACE_MAX))

        return CommandResult(False, raw_text, raw_text)

    def record_output(self, out: str):
        if out and out != "\n":
            self.history.append(out)


processor = CommandProcessor()


def execute_output(out):
    if out == "":
        return
    if isinstance(out, tuple):
        if out[0] == "__BACKSPACE__":
            backspace(int(out[1]))
            return
        if out[0] == "__ENTER__":
            press_enter()
            return
    if isinstance(out, str):
        send_unicode_text(out)


def focus_target():
    global _LAST_FG_HWND
    if not FORCE_CLICK_BEFORE_TYPE:
        return

    try:
        current_hwnd = user32.GetForegroundWindow()
    except Exception:
        current_hwnd = None

    # 同一个窗口重复输入时不再点击，避免光标被鼠标位置打乱
    if current_hwnd and current_hwnd == _LAST_FG_HWND:
        return

    try:
        x, y = pyautogui.position()
        pyautogui.click(x, y)
        time.sleep(FOCUS_SETTLE_DELAY)
    except Exception:
        pass
    finally:
        try:
            _LAST_FG_HWND = user32.GetForegroundWindow()
        except Exception:
            _LAST_FG_HWND = current_hwnd


_last_msg = ""
_last_time = 0.0
_last_mode = ""
CLIPBOARD_LAST_TEXT = ""
CLIPBOARD_LAST_TIME = 0.0
CLIPBOARD_DEDUP_SEC = 1.0

def server_dedup(text: str, mode: str = "text") -> bool:
    global _last_msg, _last_time, _last_mode
    now = time.time()
    if text == _last_msg and mode == _last_mode and (now - _last_time) < SERVER_DEDUP_WINDOW_SEC:
        return True
    _last_msg = text
    _last_mode = mode
    _last_time = now
    return False


def handle_text(text: str, mode: str = "text"):
    text = (text or "").strip()
    if not text:
        return

    mode = (mode or "text").strip() or "text"

    if server_dedup(text, mode):
        print(f"⏭️ 服务器去重({mode})：", text)
        return

    if text == "__TEST_INJECT__":
        notify("测试注入", "请将鼠标放在记事本输入区，正在注入测试文本…")
        focus_target()
        try:
            send_unicode_text(TEST_INJECT_TEXT)
            press_enter()
            send_unicode_text("✅ 如果你看到这行文字，说明 SendInput 注入成功！")
            press_enter()
            notify("测试注入成功", "请查看记事本是否出现两行测试文本。")
        except Exception as e:
            notify("测试注入失败", str(e))
        return

    # 文本模式：不执行语音指令，直接落入光标
    if mode != "cmd":
        if processor.paused:
            notify("指令执行", f"⏸(暂停中) {text}")
            return
        focus_target()
        execute_output(text)
        processor.record_output(text)
        return

    result = processor.handle(text)
    if result.output == "":
        notify("指令执行", result.display_text)
        return

    focus_target()
    execute_output(result.output)

    if not result.handled and isinstance(result.output, str):
        processor.record_output(result.output)


def _build_command_args(command, args) -> List[str]:
    if isinstance(command, str) and command.strip():
        parts = shlex.split(command, posix=False)
    elif isinstance(command, list):
        parts = [str(x) for x in command if str(x).strip()]
    else:
        parts = []

    if isinstance(args, list):
        parts.extend([str(x) for x in args if str(x).strip()])
    return parts


def _match_command(text: str) -> Optional[dict]:
    text = (text or "").strip()
    if not text:
        return None
    for cmd in COMMANDS:
        match_string = (cmd.get("match-string") or "").strip()
        if match_string and match_string == text:
            return cmd
    return None

def execute_command(text: str) -> CommandResult:
    cmd = _match_command(text)
    if not cmd:
        return CommandResult(True, f"未找到匹配指令：{text}", {"ok": False, "message": "未找到匹配指令"})

    args = _build_command_args(cmd.get("command"), cmd.get("args"))
    if not args:
        return CommandResult(True, f"命令配置错误：{text}", {"ok": False, "message": "命令配置错误"})

    try:
        completed = subprocess.run(args, capture_output=True, text=True)
        ok = completed.returncode == 0
        stderr = (completed.stderr or "").strip()
        if ok:
            msg = f"指令执行成功：{text}"
        else:
            msg = f"指令执行失败：{text}（exit {completed.returncode}）"
            if stderr:
                msg = f"{msg} - {stderr}"
        return CommandResult(True, msg, {"ok": ok, "message": msg})
    except Exception as e:
        return CommandResult(True, f"指令执行异常：{text} - {e}", {"ok": False, "message": f"指令执行异常：{e}"})


# ===================== WebSocket =====================
async def broadcast_json(payload: dict):
    if not WS_CLIENTS:
        return

    data = json.dumps(payload, ensure_ascii=False)
    stale = []
    for ws in list(WS_CLIENTS):
        if ws.closed:
            stale.append(ws)
            continue
        try:
            await ws.send(data)
        except Exception as e:
            print(f"[broadcast] send failed: {e}")
            stale.append(ws)

    for ws in stale:
        WS_CLIENTS.discard(ws)
    if stale:
        print(f"[broadcast] removed stale clients: {len(stale)}")


def schedule_broadcast(payload: dict) -> bool:
    loop = WS_LOOP
    if not loop or not loop.is_running():
        return False
    try:
        asyncio.run_coroutine_threadsafe(broadcast_json(payload), loop)
        return True
    except Exception:
        return False


async def ws_handler(websocket):
    global CLIENT_COUNT, WS_CLIENTS

    with CLIENT_LOCK:
        CLIENT_COUNT += 1
        c = CLIENT_COUNT
    notify("手机已连接", f"连接数：{c}（HTTP:{HTTP_PORT} WS:{WS_PORT}）")
    WS_CLIENTS.add(websocket)
    print(f"[ws] client connected, total={len(WS_CLIENTS)}")

    try:
        async for msg in websocket:
            msg = msg.strip()
            if not msg:
                continue
            print("[ws] 收到：", msg)
            msg_type = "text"
            content = msg
            if msg.startswith("{"):
                try:
                    payload = json.loads(msg)
                    if isinstance(payload, dict):
                        msg_type = (payload.get("type") or "text").strip()
                        content = payload.get("string")
                except Exception:
                    msg_type = "text"
                    content = msg

            if msg_type == "cmd":
                text_cmd = str(content or "").strip()
                if _match_command(text_cmd):
                    result = execute_command(text_cmd)
                    resp = {
                        "type": "cmd_result",
                        "string": text_cmd,
                        "ok": bool(result.output.get("ok")) if isinstance(result.output, dict) else False,
                        "message": result.output.get("message") if isinstance(result.output, dict) else result.display_text,
                    }
                    await websocket.send(json.dumps(resp, ensure_ascii=False))
                else:
                    handle_text(text_cmd, mode="cmd")
            else:
                handle_text(str(content or ""), mode="text")

    except (ConnectionClosedOK, ConnectionClosedError, ConnectionClosed, ConnectionResetError, OSError):
        pass

    finally:
        WS_CLIENTS.discard(websocket)
        with CLIENT_LOCK:
            CLIENT_COUNT -= 1
            c = CLIENT_COUNT
        notify("手机已断开", f"连接数：{c}")
        print(f"[ws] client disconnected, total={len(WS_CLIENTS)}")


async def ws_main():
    global WS_LOOP
    WS_LOOP = asyncio.get_running_loop()
    print("[ws] event loop set, starting websocket server")
    async with websockets.serve(
        ws_handler, "0.0.0.0", WS_PORT,
        ping_interval=WS_PING_INTERVAL,
        ping_timeout=WS_PING_TIMEOUT
    ):
        print(f"WebSocket running at ws://0.0.0.0:{WS_PORT}")
        await asyncio.Future()


# ===================== HTTP =====================
app = Flask(__name__)


@app.route("/")
def index():
    # 打包后 index.html 在 sys._MEIPASS（onefile 临时解压目录）
    path = resource_path("index.html")
    return send_file(path)


@app.route("/config")
def config():
    return jsonify({"ws_port": WS_PORT, "http_port": HTTP_PORT, "url": QR_PAYLOAD_URL})


def run_http():
    app.run(host="0.0.0.0", port=HTTP_PORT, debug=False, use_reloader=False)


def tray_show_qr(icon, _):
    qr_mgr.show()


def tray_send_clipboard(icon, _):
    global CLIPBOARD_LAST_TEXT, CLIPBOARD_LAST_TIME

    text = (get_clipboard_text() or "").strip()
    if not text:
        print("[clipboard] empty or unreadable clipboard")
        notify("剪贴板发送", "剪贴板为空或无法读取")
        return

    now = time.time()
    if text == CLIPBOARD_LAST_TEXT and (now - CLIPBOARD_LAST_TIME) < CLIPBOARD_DEDUP_SEC:
        # 双击或短时间重复触发，直接忽略
        return

    CLIPBOARD_LAST_TEXT = text
    CLIPBOARD_LAST_TIME = now

    preview = text if len(text) < 50 else (text[:50] + "...")
    ok = schedule_broadcast({"type": "clipboard", "string": text})
    if ok:
        notify("剪贴板发送", "已发送到网页，可在手机端复制")
    else:
        notify("剪贴板发送失败", "WebSocket 未运行或无连接")


def tray_quit(icon, _):
    notify("退出", "LAN Voice Input 已退出")
    icon.stop()
    os._exit(0)


def run_tray():
    global tray_icon
    imagePath = resource_path("icon.ico")
    menu = (
        item("发送剪贴板到网页", tray_send_clipboard, default=True),
        item("显示二维码", tray_show_qr),
        item("退出", tray_quit),
    )
    tray_icon = pystray.Icon("LANVoiceInput", Image.open(imagePath), "LAN Voice Input", menu)
    # Windows 下单击默认触发菜单 default 项，设置 default=True 即可生效
    tray_icon.run()


# ===================== main =====================
if __name__ == "__main__":
    # ✅ 启动即读取/创建 config（打包后优先 exe 同级 config.json）
    load_config()

    HTTP_PORT = choose_free_port(DEFAULT_HTTP_PORT)
    WS_PORT = choose_free_port(DEFAULT_WS_PORT)

    build_urls(get_effective_ip())

    print("\n======================================")
    print("✅ 已启动")
    print("📱 手机打开：", QR_PAYLOAD_URL)
    print("HTTP:", HTTP_PORT, "WS:", WS_PORT)
    print("======================================")
    print("CONFIG(primary):", CONFIG_PATH_PRIMARY)
    print("CONFIG(fallback):", CONFIG_PATH_FALLBACK)
    print("CONFIG(in use):", CONFIG_PATH_IN_USE)
    print("======================================\n")

    threading.Thread(target=run_http, daemon=True).start()
    threading.Thread(target=lambda: asyncio.run(ws_main()), daemon=True).start()

    notify("LANVoiceInput 启动成功", f"HTTP:{HTTP_PORT}  WS:{WS_PORT}\n单击托盘图标快速发送剪贴板到网页\n右键托盘菜单可显示二维码")
    # ✅ 启动后自动打开二维码窗口（加一点延迟更稳）
    threading.Timer(0.3, qr_mgr.show).start()

    run_tray()
