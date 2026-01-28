"""Windows input/clipboard helpers (SendInput, focus, clipboard)."""
import ctypes
import subprocess
import sys
import time
from ctypes import wintypes
from typing import Optional

import pyautogui

from settings import FORCE_CLICK_BEFORE_TYPE, FOCUS_SETTLE_DELAY

# Prepare ctypes structures for SendInput
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
    """Get the HWND that owns keyboard focus (fallback to foreground window)."""
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
    Prefer PostMessage(WM_CHAR) injection to avoid first-character loss in Notepad.
    Falls back to SendInput when code points exceed BMP.
    """
    hwnd = _get_focus_hwnd()
    if not hwnd:
        return False
    ok = True
    for ch in text:
        code = ord(ch)
        if code > 0xFFFF:
            return False
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

    if _try_post_chars(text):
        return

    inputs = []
    print("⌨️ 输入文本：", text)
    for ch in text:
        code = ord(ch)
        inputs.append(
            INPUT(
                type=INPUT_KEYBOARD,
                ki=KEYBDINPUT(wVk=0, wScan=code, dwFlags=KEYEVENTF_UNICODE, time=0, dwExtraInfo=0),
            )
        )
        inputs.append(
            INPUT(
                type=INPUT_KEYBOARD,
                ki=KEYBDINPUT(
                    wVk=0, wScan=code, dwFlags=KEYEVENTF_UNICODE | KEYEVENTF_KEYUP, time=0, dwExtraInfo=0
                ),
            )
        )
    _send_input(inputs)


def press_vk(vk_code: int, times: int = 1):
    for _ in range(times):
        down = INPUT(type=INPUT_KEYBOARD, ki=KEYBDINPUT(wVk=vk_code, wScan=0, dwFlags=0, time=0, dwExtraInfo=0))
        up = INPUT(
            type=INPUT_KEYBOARD, ki=KEYBDINPUT(wVk=vk_code, wScan=0, dwFlags=KEYEVENTF_KEYUP, time=0, dwExtraInfo=0)
        )
        _send_input([down, up])


def backspace(n: int):
    if n > 0:
        press_vk(VK_BACK, times=n)


def press_enter():
    press_vk(VK_RETURN, times=1)


_LAST_FG_HWND = None


def focus_target():
    """Optionally click current mouse position once to ensure focus."""
    global _LAST_FG_HWND
    if not FORCE_CLICK_BEFORE_TYPE:
        return

    try:
        current_hwnd = user32.GetForegroundWindow()
    except Exception:
        current_hwnd = None

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


def get_clipboard_text() -> str:
    """Best-effort clipboard read with retries and a PowerShell fallback."""
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
                raw = ctypes.string_at(ptr)  # some apps expose readable data with reported size 0
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

    try:
        out = subprocess.check_output(
            ["powershell", "-NoProfile", "-Command", "Get-Clipboard -Raw"],
            text=True,
            stderr=subprocess.STDOUT,
            timeout=3,
        )
        if out:
            return out
    except Exception:
        pass
    return ""
