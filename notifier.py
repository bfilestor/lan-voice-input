"""System notification helpers (tray balloon + Windows Toast)."""
import threading
from typing import Optional

try:
    from winotify import Notification

    WINOTIFY_AVAILABLE = True
except Exception:
    WINOTIFY_AVAILABLE = False

tray_icon = None  # injected by tray module


def set_tray_icon(icon) -> None:
    """Allow other modules to trigger tray balloons."""
    global tray_icon
    tray_icon = icon


def notify(title: str, msg: str, duration: int = 3) -> None:
    """Fire tray balloon and optional Windows toast without raising."""
    global tray_icon

    try:
        if tray_icon:
            tray_icon.notify(msg, title)
    except Exception:
        pass

    if not WINOTIFY_AVAILABLE:
        return

    def _toast():
        try:
            toast = Notification(
                app_id="LAN Voice Input",
                title=title,
                msg=msg,
                duration="short",
            )
            toast.show()
        except Exception:
            pass

    threading.Thread(target=_toast, daemon=True).start()
