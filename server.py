# server.py
# -*- coding: utf-8 -*-
"""Main entry point for LAN Voice Input (modularized)."""
import asyncio
import threading

import config_store
from config_store import CONFIG_PATH_FALLBACK, CONFIG_PATH_IN_USE, CONFIG_PATH_PRIMARY
from http_server import run_http
from ip_utils import build_urls, choose_free_port, get_effective_ip, get_ipv4_candidates
from notifier import notify
from qr_window import QRWindowManager
from settings import DEFAULT_HTTP_PORT, DEFAULT_WS_PORT
from tray_app import run_tray
from websocket_server import set_ports, ws_main


def main():
    # ✅ 启动即读取/创建 config（打包后优先 exe 同级 config.json）
    config_store.load_config()

    http_port = choose_free_port(DEFAULT_HTTP_PORT)
    ws_port = choose_free_port(DEFAULT_WS_PORT)
    set_ports(http_port, ws_port)

    qr_url, qr_payload_url = build_urls(get_effective_ip(config_store.USER_IP), http_port, ws_port)

    def refresh_urls():
        nonlocal qr_url, qr_payload_url
        qr_url, qr_payload_url = build_urls(get_effective_ip(config_store.USER_IP), http_port, ws_port)
        return qr_payload_url

    def get_url_state():
        return {"http_port": http_port, "ws_port": ws_port, "url": qr_payload_url, "qr_url": qr_url}

    def on_ip_change(new_ip):
        config_store.USER_IP = new_ip
        config_store.save_config()
        refresh_urls()

    qr_mgr = QRWindowManager(
        get_user_ip=lambda: config_store.USER_IP,
        on_ip_change=on_ip_change,
        get_effective_ip=lambda: get_effective_ip(config_store.USER_IP),
        get_ports=lambda: (http_port, ws_port),
        get_payload_url=lambda: qr_payload_url,
        get_config_path=lambda: CONFIG_PATH_IN_USE,
        list_candidates=get_ipv4_candidates,
    )

    print("\n======================================")
    print("✅ 已启动")
    print("📱 手机打开：", qr_payload_url)
    print("HTTP:", http_port, "WS:", ws_port)
    print("======================================")
    print("CONFIG(primary):", CONFIG_PATH_PRIMARY)
    print("CONFIG(fallback):", CONFIG_PATH_FALLBACK)
    print("CONFIG(in use):", CONFIG_PATH_IN_USE)
    print("======================================\n")

    threading.Thread(target=lambda: run_http(get_url_state), daemon=True).start()
    threading.Thread(target=lambda: asyncio.run(ws_main()), daemon=True).start()

    notify(
        "LANVoiceInput 启动成功",
        f"HTTP:{http_port}  WS:{ws_port}\n单击托盘图标快速发送剪贴板到网页\n右键托盘菜单可显示二维码",
    )
    # ✅ 启动后自动打开二维码窗口（加一点延迟更稳）
    threading.Timer(0.3, qr_mgr.show).start()

    run_tray(qr_mgr)


if __name__ == "__main__":
    main()
