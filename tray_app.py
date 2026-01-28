"""System tray menu actions."""
import os
import time

import pystray
from PIL import Image
from pystray import MenuItem as item

from input_control import get_clipboard_text
from notifier import notify, set_tray_icon
from paths import resource_path
from settings import CLIPBOARD_DEDUP_SEC
from websocket_server import schedule_broadcast

CLIPBOARD_LAST_TEXT = ""
CLIPBOARD_LAST_TIME = 0.0
QR_MANAGER = None


def tray_show_qr(icon, _):
    if QR_MANAGER:
        QR_MANAGER.show()


def tray_send_clipboard(icon, _):
    global CLIPBOARD_LAST_TEXT, CLIPBOARD_LAST_TIME

    text = (get_clipboard_text() or "").strip()
    if not text:
        print("[clipboard] empty or unreadable clipboard")
        notify("剪贴板发送", "剪贴板为空或无法读取")
        return

    now = time.time()
    if text == CLIPBOARD_LAST_TEXT and (now - CLIPBOARD_LAST_TIME) < CLIPBOARD_DEDUP_SEC:
        return

    CLIPBOARD_LAST_TEXT = text
    CLIPBOARD_LAST_TIME = now

    ok = schedule_broadcast({"type": "clipboard", "string": text})
    if ok:
        notify("剪贴板发送", "已发送到网页，可在手机端复制")
    else:
        notify("剪贴板发送失败", "WebSocket 未运行或无连接")


def tray_quit(icon, _):
    notify("退出", "LAN Voice Input 已退出")
    icon.stop()
    os._exit(0)


def run_tray(qr_manager):
    global QR_MANAGER
    QR_MANAGER = qr_manager
    image_path = resource_path("icon.ico")
    menu = (
        item("发送剪贴板到网页", tray_send_clipboard, default=True),
        item("显示二维码", tray_show_qr),
        item("退出", tray_quit),
    )
    tray_icon = pystray.Icon("LANVoiceInput", Image.open(image_path), "LAN Voice Input", menu)
    set_tray_icon(tray_icon)
    tray_icon.run()
