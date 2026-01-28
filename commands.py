"""Voice command parsing and configurable command execution."""
import re
import shlex
import subprocess
from dataclasses import dataclass
from typing import List, Optional

import config_store
from settings import CLEAR_BACKSPACE_MAX


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


def match_command(text: str) -> Optional[dict]:
    text = (text or "").strip()
    if not text:
        return None
    for cmd in config_store.COMMANDS:
        match_string = (cmd.get("match-string") or "").strip()
        if match_string and match_string == text:
            return cmd
    return None


def execute_command(text: str) -> CommandResult:
    cmd = match_command(text)
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
