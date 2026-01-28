"""Tkinter QR window with IP selection."""
import queue
import threading
from typing import Callable, List, Optional, Tuple

import qrcode
import tkinter as tk
from PIL import Image, ImageTk
from tkinter import ttk


class QRWindowManager:
    """Run a single Tk mainloop and expose thread-safe show/close/call APIs."""

    def __init__(
        self,
        get_user_ip: Callable[[], Optional[str]],
        on_ip_change: Callable[[Optional[str]], None],
        get_effective_ip: Callable[[], str],
        get_ports: Callable[[], Tuple[int, int]],
        get_payload_url: Callable[[], str],
        get_config_path: Callable[[], str],
        list_candidates: Callable[[], List[Tuple[str, str]]],
    ):
        self.get_user_ip = get_user_ip
        self.on_ip_change = on_ip_change
        self.get_effective_ip = get_effective_ip
        self.get_ports = get_ports
        self.get_payload_url = get_payload_url
        self.get_config_path = get_config_path
        self.list_candidates = list_candidates

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
        current = (self.get_user_ip() or "").strip()

        self.ip_items = self.list_candidates()
        labels = [lbl for (lbl, _ip) in self.ip_items]
        self.combo["values"] = labels

        idx = 0
        if current:
            for i, (_lbl, ip) in enumerate(self.ip_items):
                if ip == current:
                    idx = i
                    break
            else:
                self.on_ip_change(None)  # invalid current -> reset
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
        return self.get_effective_ip()

    def _on_ip_selected(self):
        ip = self._selected_ip()
        self.on_ip_change(ip)
        self._refresh_qr_and_text()

    def _on_auto_ip(self):
        self.on_ip_change(None)
        self._reload_ip_list_and_select_current()
        self._refresh_qr_and_text()

    def _refresh_qr_and_text(self):
        url = self.get_payload_url() or ""
        if not url:
            return

        qr = qrcode.QRCode(box_size=8, border=2)
        qr.add_data(url)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white").convert("RGB")
        self.tk_img = ImageTk.PhotoImage(img)

        self.img_label.configure(image=self.tk_img)
        self.url_label.configure(text=url)

        ip_show = self.get_effective_ip()
        mode = "手动" if (self.get_user_ip() and self.get_user_ip().strip()) else "自动"
        http_port, ws_port = self.get_ports()
        self.tip_label.configure(
            text=f"手机扫码打开网页（同一 WiFi / 同网段）\n"
            f"模式：{mode}  IP：{ip_show}\n"
            f"HTTP:{http_port}  WS:{ws_port}\n"
            f"关闭此窗口不影响后台运行"
            f"\n配置文件：{self.get_config_path()}"
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
        self._refresh_qr_and_text()
