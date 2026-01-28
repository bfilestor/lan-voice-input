"""
Runtime configuration flags and shared constants for LAN Voice Input.
Keep values here so behavior tweaks stay in one place.
"""

# Auto-select ports starting from these defaults.
DEFAULT_HTTP_PORT = 8080
DEFAULT_WS_PORT = 8765
MAX_PORT_TRY = 50

# Input behavior tuning.
FORCE_CLICK_BEFORE_TYPE = True
FOCUS_SETTLE_DELAY = 0.06

# Command processing.
CLEAR_BACKSPACE_MAX = 200
TEST_INJECT_TEXT = "[SendInput Test] 123 ABC 中文 测试"
SERVER_DEDUP_WINDOW_SEC = 1.2

# WebSocket heartbeat.
WS_PING_INTERVAL = 20
WS_PING_TIMEOUT = 10

# Clipboard broadcast debounce.
CLIPBOARD_DEDUP_SEC = 1.0
