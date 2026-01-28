"""Port selection and LAN IP utilities."""
import os
import re
import socket
import subprocess
from typing import List, Optional, Tuple

from settings import DEFAULT_HTTP_PORT, DEFAULT_WS_PORT, MAX_PORT_TRY


def is_port_free(port: int) -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("0.0.0.0", port))
            return True
    except OSError:
        return False


def choose_free_port(start_port: int) -> int:
    for p in range(start_port, start_port + MAX_PORT_TRY):
        if is_port_free(p):
            return p
    raise RuntimeError(f"找不到可用端口（从 {start_port} 起尝试 {MAX_PORT_TRY} 个）")


def get_lan_ip_best_effort() -> str:
    """Get default outbound interface IP via UDP connect (no packets sent)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
    except Exception:
        ip = "127.0.0.1"
    finally:
        s.close()
    return ip


def is_valid_ipv4(ip: str) -> bool:
    if not ip:
        return False
    if not re.match(r"^\d{1,3}(\.\d{1,3}){3}$", ip):
        return False
    parts = ip.split(".")
    try:
        nums = [int(x) for x in parts]
    except Exception:
        return False
    return all(0 <= n <= 255 for n in nums)


def is_candidate_ipv4(ip: str) -> bool:
    if not is_valid_ipv4(ip):
        return False
    if ip.startswith("127.") or ip.startswith("0.") or ip.startswith("169.254."):
        return False
    return True


def parse_windows_ipconfig() -> List[Tuple[str, str]]:
    """Parse ipconfig output and return [(label, ip), ...]."""
    if os.name != "nt":
        return []

    out = ""
    for enc in ("gbk", "utf-8"):
        try:
            out = subprocess.check_output(
                ["ipconfig"], stderr=subprocess.STDOUT, text=True, encoding=enc, errors="ignore"
            )
            if out:
                break
        except Exception:
            continue
    if not out:
        return []

    results: List[Tuple[str, str]] = []
    current_iface = "未知网卡"

    iface_pat = re.compile(r"^\s*([^\r\n:]{3,}adapter\s+.+):\s*$", re.IGNORECASE)
    ipv4_pat = re.compile(r"IPv4.*?:\s*([0-9]+\.[0-9]+\.[0-9]+\.[0-9]+)")

    for line in out.splitlines():
        m_iface = iface_pat.match(line.strip())
        if m_iface:
            current_iface = m_iface.group(1).strip()
            continue

        m_ip = ipv4_pat.search(line)
        if m_ip:
            ip = m_ip.group(1).strip()
            if is_candidate_ipv4(ip):
                results.append((f"{current_iface} - {ip}", ip))

    seen = set()
    dedup = []
    for label, ip in results:
        if ip not in seen:
            seen.add(ip)
            dedup.append((label, ip))
    return dedup


def get_ipv4_candidates() -> List[Tuple[str, str]]:
    """
    Combine possible IPs:
    1) Windows ipconfig (with interface name)
    2) hostname resolved addresses
    3) default outbound interface
    """
    candidates: List[Tuple[str, str]] = []
    candidates.extend(parse_windows_ipconfig())

    try:
        hostname = socket.gethostname()
        infos = socket.getaddrinfo(hostname, None, family=socket.AF_INET, type=socket.SOCK_STREAM)
        for info in infos:
            ip = info[4][0]
            if is_candidate_ipv4(ip):
                candidates.append((f"{hostname} - {ip}", ip))
    except Exception:
        pass

    ip2 = get_lan_ip_best_effort()
    if is_candidate_ipv4(ip2):
        candidates.append((f"自动推荐（默认出口） - {ip2}", ip2))

    seen = set()
    dedup: List[Tuple[str, str]] = []
    for label, ip in candidates:
        if ip not in seen:
            seen.add(ip)
            dedup.append((label, ip))

    if not dedup:
        dedup = [("本机回环（仅本机可用） - 127.0.0.1", "127.0.0.1")]
    return dedup


def get_effective_ip(user_ip: Optional[str]) -> str:
    """Prefer user-selected IP, otherwise auto-detect."""
    if user_ip and user_ip.strip():
        return user_ip.strip()
    return get_lan_ip_best_effort()


def build_urls(ip: str, http_port: int, ws_port: int):
    qr_url = f"http://{ip}:{http_port}"
    qr_payload_url = f"{qr_url}?ws={ws_port}"
    return qr_url, qr_payload_url
