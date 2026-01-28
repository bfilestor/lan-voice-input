"""Executable and resource path helpers."""
import os
import sys


def is_frozen() -> bool:
    """Return True when running under PyInstaller."""
    return getattr(sys, "frozen", False) is True


def get_exe_dir() -> str:
    """PyInstaller: directory of the exe; source: directory of this file."""
    if is_frozen():
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def get_resource_dir() -> str:
    """
    Resolve where static assets live.
    - onefile: sys._MEIPASS (PyInstaller temp extract)
    - source/onedir: alongside this file
    """
    if is_frozen() and hasattr(sys, "_MEIPASS"):
        return getattr(sys, "_MEIPASS")
    return os.path.dirname(os.path.abspath(__file__))


def resource_path(name: str) -> str:
    """Build an absolute path for a bundled resource."""
    return os.path.join(get_resource_dir(), name)
