"""WebSocket server and broadcast helpers."""
import asyncio
import json
import threading
from typing import Optional, Set

import websockets
from websockets.exceptions import ConnectionClosed, ConnectionClosedError, ConnectionClosedOK

from commands import execute_command, match_command
from notifier import notify
from settings import WS_PING_INTERVAL, WS_PING_TIMEOUT
from text_handler import handle_text

HTTP_PORT: Optional[int] = None
WS_PORT: Optional[int] = None

CLIENT_COUNT = 0
CLIENT_LOCK = threading.Lock()
WS_CLIENTS: Set[websockets.WebSocketServerProtocol] = set()
WS_LOOP: Optional[asyncio.AbstractEventLoop] = None


def set_ports(http_port: int, ws_port: int):
    global HTTP_PORT, WS_PORT
    HTTP_PORT = http_port
    WS_PORT = ws_port


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
                if match_command(text_cmd):
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
        ws_handler,
        "0.0.0.0",
        WS_PORT,
        ping_interval=WS_PING_INTERVAL,
        ping_timeout=WS_PING_TIMEOUT,
    ):
        print(f"WebSocket running at ws://0.0.0.0:{WS_PORT}")
        await asyncio.Future()
