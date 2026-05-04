#!/usr/bin/env python3
"""
Samsung ST200F / Samsung MobileLink replacement tester for Linux.

What this does:
- Listens for the camera's UPnP/DLNA announcements on UDP 1901.
- Finds the Samsung camera at URLs like:
    http://192.168.11.2:<dynamic_port>/SamsungDmsDesc.xml
- Works around the ST200F quirk where SamsungDmsDesc.xml returns 401.
- Uses the working ContentDirectory control URL directly:
    /upnp/control/ContentDirectory1
- Browses folders/photos/videos.
- Shows JPEG_TN thumbnails as preview.
- Downloads the larger/full resource, usually JPEG_LRG/JPG/MP4.
- Supports checkbox-style selection, Select all, Select only new, and batch download.

Run:
    python3 st200f-test-app.py

Optional, for image previews:
    pip install pillow

On Ubuntu/Debian if Tkinter is missing:
    sudo apt install python3-tk
"""

from __future__ import annotations

import binascii
import html
import os
import queue
import socket
import string
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from io import BytesIO
from pathlib import Path
from typing import Callable, Optional

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

try:
    from PIL import Image, ImageTk
except ImportError:
    Image = None
    ImageTk = None

MULTICAST_ADDR = "239.255.255.250"
SSDP_PORTS = [1900, 1901]
SAMSUNG_UDP_PORT = 1901
DEFAULT_CAMERA_IP = "192.168.11.2"
DEFAULT_LOCAL_WIFI_IP = "192.168.11.12"
DEFAULT_DOWNLOAD_DIR = str(Path.home() / "SamsungCameraDownloads")

COMMON_TCP_PORTS = [
    80, 81, 82, 88, 443,
    1024, 1025, 1026, 1900, 1901,
    5000, 5555, 6000, 7000, 7676, 7777,
    8000, 8001, 8080, 8081, 8088, 8895, 9000, 9090,
    *range(49152, 49261),
]

CHECKED = "☑"
UNCHECKED = "☐"


@dataclass
class SSDPDevice:
    location: str
    server: str = ""
    st: str = ""
    usn: str = ""


@dataclass
class ContentDirectoryDevice:
    friendly_name: str
    location: str
    control_url: str
    service_type: str
    udn: str = ""
    manufacturer: str = ""
    model_name: str = ""

    def label(self) -> str:
        model = f" | {self.model_name}" if self.model_name else ""
        return f"{self.friendly_name}{model} | {self.control_url}"


@dataclass
class MediaEntry:
    object_id: str
    parent_id: str
    title: str
    entry_type: str  # container or item
    resource_url: str = ""
    size: str = ""
    protocol_info: str = ""
    thumbnail_url: str = ""
    thumbnail_size: str = ""
    thumbnail_protocol_info: str = ""

    def is_downloadable(self) -> bool:
        return self.entry_type == "item" and bool(self.resource_url)

    def kind(self) -> str:
        text = f"{self.title} {self.protocol_info} {self.resource_url}".lower()
        if self.entry_type == "container":
            return "folder"
        if ".mp4" in text or "video" in text:
            return "video"
        if ".jpg" in text or ".jpeg" in text or "image" in text:
            return "image"
        return "file"

    def display_name(self) -> str:
        if self.entry_type == "container":
            return f"📁 {self.title}"
        return self.title


def format_size(size_value: str) -> str:
    try:
        size = int(size_value)
    except Exception:
        return size_value

    units = ["B", "KB", "MB", "GB"]
    value = float(size)
    unit = units[0]
    for unit in units:
        if value < 1024 or unit == units[-1]:
            break
        value /= 1024
    return f"{int(value)} {unit}" if unit == "B" else f"{value:.1f} {unit}"


def log_exception() -> str:
    return traceback.format_exc(limit=8)


def parse_ssdp_headers(data: bytes) -> dict[str, str]:
    text = data.decode("utf-8", errors="replace")
    headers: dict[str, str] = {}
    for line in text.splitlines():
        if ":" in line:
            key, value = line.split(":", 1)
            headers[key.strip().lower()] = value.strip()
    return headers


def printable_preview(data: bytes, max_len: int = 2500) -> str:
    sample = data[:max_len]
    text = sample.decode("utf-8", errors="replace")
    printable_count = sum(1 for c in text if c in string.printable or c in "\r\n\t")
    ratio = printable_count / max(1, len(text))
    if ratio > 0.75:
        return text
    return binascii.hexlify(sample, sep=" ").decode("ascii")


def safe_filename(name: str) -> str:
    cleaned = "".join(c if c.isalnum() or c in " ._-()[]" else "_" for c in name)
    cleaned = cleaned.strip().strip(".")
    return cleaned or "downloaded_file"


def guess_filename_from_url(url: str, fallback_title: str) -> str:
    """Prefer the camera item title over internal Samsung resource filenames."""
    title_name = safe_filename(fallback_title)
    path = urllib.parse.urlparse(url).path
    basename = os.path.basename(path)
    if not basename:
        return title_name

    url_name = safe_filename(urllib.parse.unquote(basename))
    lower = url_name.lower()

    # Samsung may expose internal resource names like 524.JPEG_TN or 524.JPEG_LRG.
    # Keep the proper camera title: SAM_2380.JPG, SAM_2102.MP4, etc.
    samsung_internal_suffixes = (
        ".jpeg_tn", ".jpg_tn", ".jpeg_lrg", ".jpg_lrg",
        ".jpeg_org", ".jpg_org", ".jpeg_sm", ".jpg_sm",
    )
    if lower.endswith(samsung_internal_suffixes):
        return title_name

    # If URL basename has no normal extension but title does, title is safer.
    if "." not in url_name and "." in title_name:
        return title_name

    return url_name or title_name


def output_path_for_entry(entry: MediaEntry, download_dir: Path) -> Path:
    return download_dir / guess_filename_from_url(entry.resource_url, entry.title)


def choose_best_resource(resources: list[tuple[str, str, str]]) -> tuple[str, str, str]:
    """Choose the full media resource when UPnP returns both thumbnail and full file."""
    if not resources:
        return "", "", ""

    def score(item: tuple[str, str, str]) -> float:
        url, size, protocol = item
        text = f"{url} {protocol}".lower()
        value = 0.0

        if any(marker in text for marker in ["jpeg_tn", "jpg_tn", "_tn", "thumbnail", "thumb"]):
            value -= 10_000

        if any(marker in text for marker in [
            "jpeg_lrg", "jpeg_large", "jpeg_org", "jpg_lrg", "image/jpeg",
            ".jpg", ".jpeg", ".mp4", "video/mp4", "video/",
        ]):
            value += 1_000

        try:
            value += min(int(size) / 1024.0, 10_000)
        except Exception:
            pass

        return value

    return max(resources, key=score)


def choose_thumbnail_resource(resources: list[tuple[str, str, str]]) -> tuple[str, str, str]:
    """Choose the small thumbnail resource for preview display."""
    if not resources:
        return "", "", ""

    def score(item: tuple[str, str, str]) -> float:
        url, size, protocol = item
        text = f"{url} {protocol}".lower()
        value = 0.0

        if any(marker in text for marker in ["jpeg_tn", "jpg_tn", "_tn", "thumbnail", "thumb"]):
            value += 10_000

        if any(marker in text for marker in ["jpeg_lrg", "jpg_lrg", "large", "video/", ".mp4"]):
            value -= 5_000

        try:
            value -= int(size) / 1024.0
        except Exception:
            pass

        return value

    return max(resources, key=score)


def http_get_text(
    url: str,
    timeout: float = 7.0,
    extra_headers: Optional[dict[str, str]] = None,
) -> tuple[int, str, dict[str, str]]:
    headers = {
        "User-Agent": "SamsungCameraUPnPTester/0.4",
        "Connection": "close",
    }
    if extra_headers:
        headers.update(extra_headers)

    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read(512_000)
            return resp.status, raw.decode("utf-8", errors="replace"), dict(resp.headers.items())
    except urllib.error.HTTPError as exc:
        raw = exc.read(64_000)
        headers_dict = dict(exc.headers.items()) if exc.headers else {}
        return exc.code, raw.decode("utf-8", errors="replace"), headers_dict


def child_text(element: ET.Element, local_name: str) -> str:
    for child in element:
        if child.tag.split("}")[-1] == local_name:
            return (child.text or "").strip()
    return ""


def find_children(element: ET.Element, local_name: str) -> list[ET.Element]:
    return [child for child in element.iter() if child.tag.split("}")[-1] == local_name]


def ssdp_discover(
    timeout: float,
    logger: Callable[[str], None],
    local_ip: str = "",
) -> list[SSDPDevice]:
    search_targets = [
        "urn:schemas-upnp-org:service:ContentDirectory:1",
        "urn:schemas-upnp-org:device:MediaServer:1",
        "ssdp:all",
    ]

    found: dict[str, SSDPDevice] = {}
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    sock.settimeout(0.35)
    sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 2)

    if local_ip:
        try:
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(local_ip))
            logger(f"Using multicast interface IP for active discovery: {local_ip}")
        except OSError as exc:
            logger(f"Could not force multicast interface {local_ip}: {exc}")

    try:
        for port in SSDP_PORTS:
            for st in search_targets:
                request = (
                    "M-SEARCH * HTTP/1.1\r\n"
                    f"HOST: {MULTICAST_ADDR}:{port}\r\n"
                    'MAN: "ssdp:discover"\r\n'
                    "MX: 2\r\n"
                    f"ST: {st}\r\n"
                    "\r\n"
                ).encode("ascii")
                logger(f"Sending SSDP search to UDP {port}: {st}")
                sock.sendto(request, (MULTICAST_ADDR, port))

        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                data, addr = sock.recvfrom(65535)
            except socket.timeout:
                continue

            headers = parse_ssdp_headers(data)
            location = headers.get("location", "")
            logger(f"UDP response from {addr[0]}:{addr[1]}\n{printable_preview(data, 1200)}")

            if location and location not in found:
                found[location] = SSDPDevice(
                    location=location,
                    server=headers.get("server", ""),
                    st=headers.get("st", ""),
                    usn=headers.get("usn", ""),
                )
                logger(f"Found LOCATION: {location}")
    finally:
        sock.close()

    return list(found.values())


def listen_udp_1901(
    duration: float,
    logger: Callable[[str], None],
    local_ip: str = "",
) -> list[SSDPDevice]:
    found: dict[str, SSDPDevice] = {}

    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    sock.settimeout(0.5)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

    try:
        sock.bind(("", SAMSUNG_UDP_PORT))
    except OSError:
        sock.bind((MULTICAST_ADDR, SAMSUNG_UDP_PORT))

    try:
        interface_ip = local_ip or "0.0.0.0"
        mreq = socket.inet_aton(MULTICAST_ADDR) + socket.inet_aton(interface_ip)
        sock.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP, mreq)
        if local_ip:
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(local_ip))
            logger(f"Joined multicast group using Wi-Fi IP: {local_ip}")
    except OSError as exc:
        logger(f"Could not join multicast group, but still listening: {exc}")

    logger(f"Listening for UDP multicast on {MULTICAST_ADDR}:{SAMSUNG_UDP_PORT} for {duration:.0f}s...")
    deadline = time.time() + duration

    try:
        while time.time() < deadline:
            try:
                data, addr = sock.recvfrom(65535)
            except socket.timeout:
                continue

            headers = parse_ssdp_headers(data)
            location = headers.get("location", "")
            logger("-" * 70)
            logger(f"UDP packet from {addr[0]}:{addr[1]}, {len(data)} bytes")
            logger(printable_preview(data))

            if location:
                logger(f"Detected LOCATION header: {location}")
                if location not in found:
                    found[location] = SSDPDevice(
                        location=location,
                        server=headers.get("server", ""),
                        st=headers.get("st", ""),
                        usn=headers.get("usn", ""),
                    )
    finally:
        sock.close()

    return list(found.values())


def parse_content_directory(location_url: str, logger: Callable[[str], None]) -> Optional[ContentDirectoryDevice]:
    logger(f"Fetching device description: {location_url}")

    # Samsung ST200F advertises SamsungDmsDesc.xml but may return 401 for it.
    # We still try normal parsing first; if it fails, use the known control URL.
    header_profiles: list[tuple[str, dict[str, str]]] = [
        ("default tester", {}),
        (
            "generic UPnP client",
            {
                "User-Agent": "UPnP/1.0",
                "X-AV-Client-Info": 'av=5.0; cn="Samsung Electronics"; mn="MobileLink"; mv="1.0";',
            },
        ),
        (
            "Samsung Android-like client",
            {
                "User-Agent": "Android/4.0 UPnP/1.0 SamsungMobileLink/1.0",
                "X-AV-Client-Info": 'av=5.0; cn="Samsung Electronics"; mn="Samsung SMART CAMERA App"; mv="1.0";',
            },
        ),
    ]

    last_status = 0
    last_text = ""
    last_headers: dict[str, str] = {}
    root: Optional[ET.Element] = None

    for profile_name, headers in header_profiles:
        logger(f"Trying description GET profile: {profile_name}")
        status, xml_text, response_headers = http_get_text(location_url, extra_headers=headers)
        last_status, last_text, last_headers = status, xml_text, response_headers
        logger(f"HTTP status for description: {status}")
        logger(f"Response headers: {response_headers}")

        if status == 200 and xml_text.strip():
            try:
                root = ET.fromstring(xml_text)
                break
            except ET.ParseError:
                logger("Response was not valid XML; trying next profile.")

    if root is None:
        logger(
            "Could not fetch XML description. Last status: "
            f"{last_status}; last headers: {last_headers}; body length: {len(last_text)}"
        )

        parsed_url = urllib.parse.urlparse(location_url)
        if parsed_url.scheme and parsed_url.netloc:
            fallback_control_url = urllib.parse.urlunparse(
                (parsed_url.scheme, parsed_url.netloc, "/upnp/control/ContentDirectory1", "", "", "")
            )
            logger(f"Using Samsung fallback ContentDirectory control URL: {fallback_control_url}")
            return ContentDirectoryDevice(
                friendly_name="Samsung Camera MediaServer",
                location=location_url,
                control_url=fallback_control_url,
                service_type="urn:schemas-upnp-org:service:ContentDirectory:1",
                manufacturer="Samsung Electronics",
                model_name="Samsung Smart Camera",
            )
        return None

    friendly_name = "Unknown device"
    manufacturer = ""
    model_name = ""
    udn = ""
    base_url = ""

    base_nodes = find_children(root, "URLBase")
    if base_nodes and base_nodes[0].text:
        base_url = base_nodes[0].text.strip()

    device_nodes = find_children(root, "device")
    if device_nodes:
        device = device_nodes[0]
        friendly_name = child_text(device, "friendlyName") or friendly_name
        manufacturer = child_text(device, "manufacturer")
        model_name = child_text(device, "modelName")
        udn = child_text(device, "UDN")

    for service in find_children(root, "service"):
        service_type = child_text(service, "serviceType")
        control_url = child_text(service, "controlURL")
        if "ContentDirectory" not in service_type:
            continue

        join_base = base_url or location_url
        absolute_control_url = urllib.parse.urljoin(join_base, control_url)
        logger(f"ContentDirectory found: {absolute_control_url}")

        return ContentDirectoryDevice(
            friendly_name=friendly_name,
            location=location_url,
            control_url=absolute_control_url,
            service_type=service_type,
            udn=udn,
            manufacturer=manufacturer,
            model_name=model_name,
        )

    logger("No ContentDirectory service found in this device description.")
    return None


def xml_escape(value: str) -> str:
    return html.escape(value, quote=True)


def soap_browse(
    device: ContentDirectoryDevice,
    object_id: str = "0",
    starting_index: int = 0,
    requested_count: int = 0,
    timeout: float = 10.0,
) -> tuple[list[MediaEntry], int]:
    service_type = device.service_type

    body = f'''<?xml version="1.0" encoding="utf-8"?>
<s:Envelope
  xmlns:s="http://schemas.xmlsoap.org/soap/envelope/"
  s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
  <s:Body>
    <u:Browse xmlns:u="{xml_escape(service_type)}">
      <ObjectID>{xml_escape(object_id)}</ObjectID>
      <BrowseFlag>BrowseDirectChildren</BrowseFlag>
      <Filter>*</Filter>
      <StartingIndex>{starting_index}</StartingIndex>
      <RequestedCount>{requested_count}</RequestedCount>
      <SortCriteria></SortCriteria>
    </u:Browse>
  </s:Body>
</s:Envelope>'''.encode("utf-8")

    req = urllib.request.Request(
        device.control_url,
        data=body,
        method="POST",
        headers={
            "Content-Type": 'text/xml; charset="utf-8"',
            "SOAPAction": f'"{service_type}#Browse"',
            "User-Agent": "SamsungCameraUPnPTester/0.4",
            "Connection": "close",
        },
    )

    with urllib.request.urlopen(req, timeout=timeout) as resp:
        response_text = resp.read().decode("utf-8", errors="replace")

    envelope = ET.fromstring(response_text)
    result_text = ""
    total_matches = 0

    for node in envelope.iter():
        local = node.tag.split("}")[-1]
        if local == "Result":
            result_text = node.text or ""
        elif local == "TotalMatches":
            try:
                total_matches = int(node.text or "0")
            except Exception:
                total_matches = 0

    if not result_text.strip():
        return [], total_matches

    didl_xml = html.unescape(result_text)
    didl_root = ET.fromstring(didl_xml)

    entries: list[MediaEntry] = []
    for node in list(didl_root):
        local = node.tag.split("}")[-1]
        if local not in {"container", "item"}:
            continue

        object_id_value = node.attrib.get("id", "")
        parent_id = node.attrib.get("parentID", "")
        title = "Untitled"
        resources: list[tuple[str, str, str]] = []

        for child in node.iter():
            child_local = child.tag.split("}")[-1]
            if child_local == "title" and child.text:
                title = child.text.strip()
            elif child_local == "res" and child.text:
                resources.append(
                    (
                        child.text.strip(),
                        child.attrib.get("size", ""),
                        child.attrib.get("protocolInfo", ""),
                    )
                )

        resource_url, size, protocol_info = choose_best_resource(resources)
        thumbnail_url, thumbnail_size, thumbnail_protocol_info = choose_thumbnail_resource(resources)

        entries.append(
            MediaEntry(
                object_id=object_id_value,
                parent_id=parent_id,
                title=title,
                entry_type=local,
                resource_url=resource_url,
                size=size,
                protocol_info=protocol_info,
                thumbnail_url=thumbnail_url,
                thumbnail_size=thumbnail_size,
                thumbnail_protocol_info=thumbnail_protocol_info,
            )
        )

    return entries, total_matches


def tcp_port_open(ip: str, port: int, timeout: float = 0.35) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(timeout)
        return sock.connect_ex((ip, port)) == 0


def scan_common_tcp_ports(ip: str, logger: Callable[[str], None]) -> list[int]:
    ports = list(dict.fromkeys(COMMON_TCP_PORTS))
    open_ports: list[int] = []
    logger(f"Scanning common TCP ports on {ip}...")

    with ThreadPoolExecutor(max_workers=64) as executor:
        futures = {executor.submit(tcp_port_open, ip, port): port for port in ports}
        for future in as_completed(futures):
            port = futures[future]
            try:
                if future.result():
                    open_ports.append(port)
                    logger(f"OPEN TCP: {ip}:{port}")
            except Exception:
                pass

    open_ports.sort()
    if not open_ports:
        logger("No common TCP ports found open.")
    return open_ports


def download_file(url: str, output_path: Path, progress: Callable[[int, int], None]) -> None:
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "SamsungCameraUPnPTester/0.4", "Connection": "close"},
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        total_header = resp.headers.get("Content-Length")
        try:
            total = int(total_header) if total_header else 0
        except Exception:
            total = 0

        output_path.parent.mkdir(parents=True, exist_ok=True)
        downloaded = 0
        with output_path.open("wb") as f:
            while True:
                chunk = resp.read(1024 * 128)
                if not chunk:
                    break
                f.write(chunk)
                downloaded += len(chunk)
                progress(downloaded, total)


class WorkerThread(threading.Thread):
    def __init__(self, target, on_error: Callable[[str], None]):
        super().__init__(daemon=True)
        self.target = target
        self.on_error = on_error

    def run(self) -> None:
        try:
            self.target()
        except Exception:
            self.on_error(log_exception())


class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("Samsung Camera / MobileLink Tester")
        self.geometry("1240x800")
        self.minsize(1000, 650)

        self.ui_queue: queue.Queue[Callable[[], None]] = queue.Queue()
        self.devices: list[ContentDirectoryDevice] = []
        self.current_device: Optional[ContentDirectoryDevice] = None
        self.current_entries: list[MediaEntry] = []
        self.entry_by_iid: dict[str, MediaEntry] = {}
        self.checked_iids: set[str] = set()
        self.thumbnail_photo = None
        self.history: list[str] = []
        self.current_object_id = "0"

        self.camera_ip = tk.StringVar(value=DEFAULT_CAMERA_IP)
        self.local_wifi_ip = tk.StringVar(value=DEFAULT_LOCAL_WIFI_IP)
        self.download_dir = tk.StringVar(value=DEFAULT_DOWNLOAD_DIR)
        self.manual_url = tk.StringVar(value="")

        self._build_ui()
        self.after(100, self._process_ui_queue)

    def _build_ui(self) -> None:
        root = ttk.Frame(self, padding=10)
        root.pack(fill=tk.BOTH, expand=True)

        top = ttk.LabelFrame(root, text="1) Discovery / protocol sniffing")
        top.pack(fill=tk.X, pady=(0, 8))

        ttk.Button(top, text="Active SSDP discover", command=self.discover).grid(row=0, column=0, padx=6, pady=6, sticky="w")
        ttk.Button(top, text="Listen UDP 1901", command=self.listen_1901).grid(row=0, column=1, padx=6, pady=6, sticky="w")
        ttk.Label(top, text="Camera IP:").grid(row=0, column=2, padx=(12, 4), pady=6, sticky="e")
        ttk.Entry(top, textvariable=self.camera_ip, width=18).grid(row=0, column=3, padx=4, pady=6, sticky="w")
        ttk.Button(top, text="Probe camera IP", command=self.probe_camera_ip).grid(row=0, column=4, padx=6, pady=6, sticky="w")
        ttk.Label(top, text="Laptop Wi-Fi IP:").grid(row=0, column=5, padx=(12, 4), pady=6, sticky="e")
        ttk.Entry(top, textvariable=self.local_wifi_ip, width=18).grid(row=0, column=6, padx=4, pady=6, sticky="w")

        ttk.Label(top, text="Manual device description URL:").grid(row=1, column=0, columnspan=2, padx=6, pady=6, sticky="e")
        ttk.Entry(top, textvariable=self.manual_url, width=70).grid(row=1, column=2, columnspan=3, padx=4, pady=6, sticky="ew")
        ttk.Button(top, text="Load manual URL", command=self.load_manual_url).grid(row=1, column=5, padx=6, pady=6, sticky="w")
        top.columnconfigure(4, weight=1)

        device_frame = ttk.LabelFrame(root, text="2) ContentDirectory device")
        device_frame.pack(fill=tk.X, pady=(0, 8))

        self.device_combo = ttk.Combobox(device_frame, state="readonly")
        self.device_combo.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6, pady=6)
        self.device_combo.bind("<<ComboboxSelected>>", self.select_device)
        ttk.Button(device_frame, text="Browse root", command=self.browse_root).pack(side=tk.LEFT, padx=6, pady=6)

        middle = ttk.Frame(root)
        middle.pack(fill=tk.BOTH, expand=True)

        left = ttk.LabelFrame(middle, text="3) Media browser")
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))

        nav = ttk.Frame(left)
        nav.pack(fill=tk.X, padx=6, pady=6)
        ttk.Button(nav, text="Back", command=self.go_back).pack(side=tk.LEFT)
        self.path_label = ttk.Label(nav, text="ObjectID: -")
        self.path_label.pack(side=tk.LEFT, padx=10)

        actions = ttk.Frame(left)
        actions.pack(fill=tk.X, padx=6, pady=(0, 6))
        ttk.Button(actions, text="Select all", command=self.select_all_visible).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(actions, text="Select only new", command=self.select_only_new).pack(side=tk.LEFT, padx=4)
        ttk.Button(actions, text="Select none", command=self.select_none).pack(side=tk.LEFT, padx=4)
        ttk.Button(actions, text="Download checked", command=self.download_checked).pack(side=tk.LEFT, padx=(12, 4))
        self.checked_label = ttk.Label(actions, text="Checked: 0")
        self.checked_label.pack(side=tk.LEFT, padx=8)

        self.preview_label = ttk.Label(left, text="Select a file to preview", anchor="center")
        self.preview_label.pack(fill=tk.X, padx=6, pady=(0, 6))

        tree_frame = ttk.Frame(left)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))

        self.media_tree = ttk.Treeview(
            tree_frame,
            columns=("check", "name", "kind", "size", "status"),
            show="headings",
            selectmode="browse",
        )
        self.media_tree.heading("check", text="✓")
        self.media_tree.heading("name", text="Name")
        self.media_tree.heading("kind", text="Type")
        self.media_tree.heading("size", text="Size")
        self.media_tree.heading("status", text="Local")
        self.media_tree.column("check", width=42, minwidth=42, stretch=False, anchor="center")
        self.media_tree.column("name", width=260, anchor="w")
        self.media_tree.column("kind", width=70, stretch=False, anchor="center")
        self.media_tree.column("size", width=90, stretch=False, anchor="e")
        self.media_tree.column("status", width=90, stretch=False, anchor="center")
        self.media_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        tree_scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.media_tree.yview)
        tree_scroll.pack(side=tk.LEFT, fill=tk.Y)
        self.media_tree.configure(yscrollcommand=tree_scroll.set)

        self.media_tree.bind("<Button-1>", self.on_tree_click)
        self.media_tree.bind("<Double-Button-1>", self.open_selected)
        self.media_tree.bind("<<TreeviewSelect>>", self.preview_selected)

        right = ttk.LabelFrame(middle, text="4) Download / Log")
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        dl = ttk.Frame(right)
        dl.pack(fill=tk.X, padx=6, pady=6)
        ttk.Label(dl, text="Download folder:").grid(row=0, column=0, sticky="w")
        ttk.Entry(dl, textvariable=self.download_dir).grid(row=0, column=1, sticky="ew", padx=4)
        ttk.Button(dl, text="Choose", command=self.choose_download_dir).grid(row=0, column=2, padx=4)
        ttk.Button(dl, text="Download checked", command=self.download_checked).grid(row=1, column=0, columnspan=3, sticky="ew", pady=(6, 0))
        dl.columnconfigure(1, weight=1)

        self.progress = ttk.Progressbar(right, mode="determinate")
        self.progress.pack(fill=tk.X, padx=6, pady=(0, 6))

        self.log_text = tk.Text(right, height=18, wrap="word")
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))

        bottom = ttk.Frame(root)
        bottom.pack(fill=tk.X, pady=(8, 0))
        ttk.Label(
            bottom,
            text="Tip: connect Linux to camera Wi-Fi → Listen UDP 1901 → Browse root → open 100PHOTO → Select only new → Download checked.",
        ).pack(side=tk.LEFT)

    def post_ui(self, fn: Callable[[], None]) -> None:
        self.ui_queue.put(fn)

    def _process_ui_queue(self) -> None:
        while True:
            try:
                fn = self.ui_queue.get_nowait()
            except queue.Empty:
                break
            fn()
        self.after(100, self._process_ui_queue)

    def log(self, message: str) -> None:
        def _write() -> None:
            self.log_text.insert(tk.END, message.rstrip() + "\n")
            self.log_text.see(tk.END)
        self.post_ui(_write)

    def error(self, message: str) -> None:
        self.log("ERROR:\n" + message)
        self.post_ui(lambda: messagebox.showerror("Error", message[:2000]))

    def current_download_dir(self) -> Path:
        return Path(self.download_dir.get()).expanduser()

    def local_status_for_entry(self, entry: MediaEntry) -> str:
        if not entry.is_downloadable():
            return ""
        path = output_path_for_entry(entry, self.current_download_dir())
        return "exists" if path.exists() else "new"

    def update_checked_label(self) -> None:
        self.checked_label.config(text=f"Checked: {len(self.checked_iids)}")

    def set_checked(self, iid: str, checked: bool) -> None:
        entry = self.entry_by_iid.get(iid)
        if not entry or not entry.is_downloadable():
            return
        if checked:
            self.checked_iids.add(iid)
        else:
            self.checked_iids.discard(iid)
        values = list(self.media_tree.item(iid, "values"))
        if values:
            values[0] = CHECKED if checked else UNCHECKED
            self.media_tree.item(iid, values=values)
        self.update_checked_label()

    def toggle_checked(self, iid: str) -> None:
        self.set_checked(iid, iid not in self.checked_iids)

    def on_tree_click(self, event) -> None:
        row = self.media_tree.identify_row(event.y)
        column = self.media_tree.identify_column(event.x)
        if row and column == "#1":
            self.toggle_checked(row)
            return "break"
        return None

    def selected_iid(self) -> Optional[str]:
        selection = self.media_tree.selection()
        return selection[0] if selection else None

    def selected_entry(self) -> Optional[MediaEntry]:
        iid = self.selected_iid()
        return self.entry_by_iid.get(iid) if iid else None

    def select_all_visible(self) -> None:
        for iid, entry in self.entry_by_iid.items():
            if entry.is_downloadable():
                self.set_checked(iid, True)
        self.log(f"Selected all downloadable items in this folder: {len(self.checked_iids)}")

    def select_none(self) -> None:
        for iid in list(self.checked_iids):
            self.set_checked(iid, False)
        self.log("Cleared checked items.")

    def select_only_new(self) -> None:
        self.select_none()
        count = 0
        for iid, entry in self.entry_by_iid.items():
            if not entry.is_downloadable():
                continue
            if self.local_status_for_entry(entry) == "new":
                self.set_checked(iid, True)
                count += 1
        self.log(f"Selected only new files: {count}")

    def add_content_directory_devices(self, ssdp_devices: list[SSDPDevice]) -> None:
        cd_devices: list[ContentDirectoryDevice] = []
        for dev in ssdp_devices:
            try:
                parsed = parse_content_directory(dev.location, self.log)
                if parsed:
                    cd_devices.append(parsed)
            except Exception:
                self.log(f"Could not parse {dev.location}:\n{log_exception()}")

        def update() -> None:
            self.devices.extend(cd_devices)
            unique: dict[str, ContentDirectoryDevice] = {}
            for d in self.devices:
                unique[d.control_url] = d
            self.devices = list(unique.values())
            self.device_combo["values"] = [d.label() for d in self.devices]
            if self.devices:
                self.device_combo.current(len(self.devices) - 1)
                self.current_device = self.devices[-1]
                self.log(f"Ready. Known ContentDirectory devices: {len(self.devices)}")
            elif ssdp_devices:
                self.log("Found LOCATION URL(s), but none could be converted into ContentDirectory devices.")
            else:
                self.log("No LOCATION URLs found.")
        self.post_ui(update)

    def discover(self) -> None:
        self.log("Starting active SSDP discovery on UDP 1900 and 1901.")

        def task() -> None:
            local_ip = self.local_wifi_ip.get().strip()
            ssdp_devices = ssdp_discover(timeout=5.0, logger=self.log, local_ip=local_ip)
            self.add_content_directory_devices(ssdp_devices)

        WorkerThread(task, self.error).start()

    def listen_1901(self) -> None:
        self.log("Start this listener while the camera is in MobileLink/sharing mode.")

        def task() -> None:
            local_ip = self.local_wifi_ip.get().strip()
            ssdp_devices = listen_udp_1901(duration=30.0, logger=self.log, local_ip=local_ip)
            self.add_content_directory_devices(ssdp_devices)

        WorkerThread(task, self.error).start()

    def probe_camera_ip(self) -> None:
        ip = self.camera_ip.get().strip()
        if not ip:
            messagebox.showwarning("Missing IP", "Enter camera IP first, for example 192.168.11.2")
            return

        def task() -> None:
            open_ports = scan_common_tcp_ports(ip, self.log)
            self.log(f"Open TCP ports: {open_ports}")

        WorkerThread(task, self.error).start()

    def load_manual_url(self) -> None:
        url = self.manual_url.get().strip()
        if not url:
            messagebox.showwarning("Missing URL", "Enter a UPnP device description URL first.")
            return

        def task() -> None:
            parsed = parse_content_directory(url, self.log)
            if not parsed:
                self.log("Manual URL loaded, but no ContentDirectory service was found.")
                return

            def update() -> None:
                self.devices.append(parsed)
                self.device_combo["values"] = [d.label() for d in self.devices]
                self.device_combo.current(len(self.devices) - 1)
                self.current_device = parsed
                self.log("Manual ContentDirectory device loaded.")
            self.post_ui(update)

        WorkerThread(task, self.error).start()

    def select_device(self, _event=None) -> None:
        idx = self.device_combo.current()
        if 0 <= idx < len(self.devices):
            self.current_device = self.devices[idx]
            self.log(f"Selected: {self.current_device.label()}")

    def browse_root(self) -> None:
        self.history.clear()
        self.browse_object("0", remember=False)

    def browse_object(self, object_id: str, remember: bool = True) -> None:
        if not self.current_device:
            messagebox.showwarning("No device", "Discover or load a ContentDirectory device first.")
            return

        previous_id = self.current_object_id
        device = self.current_device
        self.log(f"Browsing ObjectID={object_id}")

        def task() -> None:
            entries, total = soap_browse(device, object_id=object_id)
            entries.sort(key=lambda e: (e.entry_type != "container", e.title.lower()))

            def update() -> None:
                if remember:
                    self.history.append(previous_id)
                self.current_object_id = object_id
                self.current_entries = entries
                self.checked_iids.clear()
                self.entry_by_iid.clear()
                self.media_tree.delete(*self.media_tree.get_children())
                self.thumbnail_photo = None
                self.preview_label.config(text="Select a file to preview", image="")

                for idx, entry in enumerate(entries):
                    iid = f"{idx}:{entry.object_id}"
                    self.entry_by_iid[iid] = entry
                    check = UNCHECKED if entry.is_downloadable() else ""
                    local_status = self.local_status_for_entry(entry)
                    self.media_tree.insert(
                        "",
                        tk.END,
                        iid=iid,
                        values=(
                            check,
                            entry.display_name(),
                            entry.kind(),
                            format_size(entry.size) if entry.size else "",
                            local_status,
                        ),
                    )

                self.path_label.config(text=f"ObjectID: {object_id} | entries: {len(entries)} | total: {total}")
                self.update_checked_label()
                self.log(f"Browse complete: {len(entries)} visible entries, TotalMatches={total}")
            self.post_ui(update)

        WorkerThread(task, self.error).start()

    def go_back(self) -> None:
        if not self.history:
            self.log("No previous folder.")
            return
        previous = self.history.pop()
        self.browse_object(previous, remember=False)

    def preview_selected(self, _event=None) -> None:
        entry = self.selected_entry()
        if not entry or entry.entry_type != "item":
            self.thumbnail_photo = None
            self.preview_label.config(text="Select a file to preview", image="")
            return

        if Image is None or ImageTk is None:
            self.preview_label.config(text="Install Pillow for previews: pip install pillow", image="")
            return

        thumb_url = entry.thumbnail_url or entry.resource_url
        if not thumb_url:
            self.preview_label.config(text="No thumbnail URL for this item", image="")
            return

        def task() -> None:
            try:
                req = urllib.request.Request(
                    thumb_url,
                    headers={"User-Agent": "SamsungCameraUPnPTester/0.4", "Connection": "close"},
                )
                with urllib.request.urlopen(req, timeout=8) as resp:
                    raw = resp.read(512_000)

                img = Image.open(BytesIO(raw))
                img.thumbnail((340, 220))
                photo = ImageTk.PhotoImage(img)

                def update() -> None:
                    self.thumbnail_photo = photo
                    self.preview_label.config(text=entry.title, image=photo, compound="top")
                self.post_ui(update)
            except Exception:
                self.log(f"Could not load thumbnail for {entry.title}:\n{log_exception()}")

        WorkerThread(task, self.error).start()

    def open_selected(self, _event=None) -> None:
        entry = self.selected_entry()
        iid = self.selected_iid()
        if not entry:
            return
        if entry.entry_type == "container":
            self.browse_object(entry.object_id, remember=True)
        elif iid:
            self.toggle_checked(iid)
            self.log(f"Selected file: {entry.title}")
            self.log(f"Full resource URL: {entry.resource_url}")
            if entry.thumbnail_url:
                self.log(f"Thumbnail URL: {entry.thumbnail_url}")

    def choose_download_dir(self) -> None:
        folder = filedialog.askdirectory(initialdir=self.download_dir.get() or str(Path.home()))
        if folder:
            self.download_dir.set(folder)
            # Refresh local status column.
            for iid, entry in self.entry_by_iid.items():
                values = list(self.media_tree.item(iid, "values"))
                if len(values) >= 5:
                    values[4] = self.local_status_for_entry(entry)
                    self.media_tree.item(iid, values=values)

    def checked_entries(self) -> list[tuple[str, MediaEntry]]:
        result: list[tuple[str, MediaEntry]] = []
        for iid in list(self.checked_iids):
            entry = self.entry_by_iid.get(iid)
            if entry and entry.is_downloadable():
                result.append((iid, entry))
        result.sort(key=lambda pair: pair[1].title.lower())
        return result

    def download_checked(self) -> None:
        entries = self.checked_entries()
        if not entries:
            messagebox.showwarning("No checked files", "Tick files first, or use Select all / Select only new.")
            return

        out_dir = self.current_download_dir()
        self.log(f"Starting batch download of {len(entries)} checked item(s) into {out_dir}")
        self.progress["mode"] = "determinate"
        self.progress["maximum"] = len(entries)
        self.progress["value"] = 0

        def task() -> None:
            downloaded_count = 0
            skipped_count = 0
            failed_count = 0

            for index, (iid, entry) in enumerate(entries, start=1):
                out_path = output_path_for_entry(entry, out_dir)

                if out_path.exists():
                    skipped_count += 1
                    self.log(f"SKIP exists: {out_path.name}")
                    self.post_ui(lambda idx=index: self.progress.config(value=idx))
                    continue

                self.log(f"Downloading {index}/{len(entries)}: {entry.title}")
                self.log(f"URL: {entry.resource_url}")

                def per_file_progress(downloaded: int, total: int, idx=index) -> None:
                    # Main progress is per-file count; detailed byte progress stays in log if needed later.
                    pass

                try:
                    download_file(entry.resource_url, out_path, per_file_progress)
                    downloaded_count += 1
                    self.log(f"DONE: {out_path}")

                    def mark_done(row_iid=iid, idx=index) -> None:
                        self.set_checked(row_iid, False)
                        values = list(self.media_tree.item(row_iid, "values"))
                        if len(values) >= 5:
                            values[4] = "exists"
                            self.media_tree.item(row_iid, values=values)
                        self.progress.config(value=idx)
                    self.post_ui(mark_done)

                except Exception:
                    failed_count += 1
                    self.log(f"FAILED: {entry.title}\n{log_exception()}")
                    self.post_ui(lambda idx=index: self.progress.config(value=idx))

            def done() -> None:
                self.update_checked_label()
                messagebox.showinfo(
                    "Batch download complete",
                    f"Downloaded: {downloaded_count}\nSkipped existing: {skipped_count}\nFailed: {failed_count}",
                )
                self.log(
                    f"Batch complete. Downloaded={downloaded_count}, "
                    f"Skipped existing={skipped_count}, Failed={failed_count}"
                )
            self.post_ui(done)

        WorkerThread(task, self.error).start()


if __name__ == "__main__":
    app = App()
    app.mainloop()

