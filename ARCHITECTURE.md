# 项目模块化说明

`server.py` 只负责启动顺序和线程，业务逻辑拆分到下列模块，便于维护和 PyInstaller 打包。

- `paths.py`：可执行/资源路径解析。
- `config_store.py`：配置读取与写回（支持 exe 同级与用户目录双路径）。
- `settings.py`：行为开关、常量集中管理。
- `ip_utils.py`：端口选择、IP 枚举、URL 构建。
- `notifier.py`：托盘气泡 + Windows Toast 封装。
- `input_control.py`：SendInput 注入、焦点处理、剪贴板读取。
- `commands.py`：语音指令解析、外部命令执行。
- `text_handler.py`：去重、文本/指令执行入口。
- `websocket_server.py`：WebSocket server 与广播。
- `http_server.py`：Flask 静态页面与 /config 接口。
- `qr_window.py`：Tk QR 窗口与网卡/IP 选择。
- `tray_app.py`：系统托盘菜单与剪贴板发送。

若需调整行为（端口、心跳间隔、点击聚焦等），优先修改 `settings.py`。入口依旧是 `python server.py` 或 PyInstaller 打包后的 exe。
