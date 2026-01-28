"""High-level text handling and deduplication."""
import time
from typing import Optional

from commands import CommandResult, processor
from input_control import backspace, focus_target, press_enter, send_unicode_text
from notifier import notify
from settings import SERVER_DEDUP_WINDOW_SEC, TEST_INJECT_TEXT

_last_msg = ""
_last_time = 0.0
_last_mode = ""


def server_dedup(text: str, mode: str = "text") -> bool:
    """Drop duplicate messages within a short window."""
    global _last_msg, _last_time, _last_mode
    now = time.time()
    if text == _last_msg and mode == _last_mode and (now - _last_time) < SERVER_DEDUP_WINDOW_SEC:
        return True
    _last_msg = text
    _last_mode = mode
    _last_time = now
    return False


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

    if mode != "cmd":
        if processor.paused:
            notify("指令执行", f"⏸(暂停中) {text}")
            return
        focus_target()
        execute_output(text)
        processor.record_output(text)
        return

    result: CommandResult = processor.handle(text)
    if result.output == "":
        notify("指令执行", result.display_text)
        return

    focus_target()
    execute_output(result.output)

    if not result.handled and isinstance(result.output, str):
        processor.record_output(result.output)
