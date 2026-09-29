# -*- coding: utf-8 -*-
"""
远程 zealman-U26-H3 视频插件（iframe 设置页）

插件目录结构：
  zealman-U26-H3/
  ├── main.py
  ├── info.json
  └── ui/
      └── index.html   ← 主应用 iframe 加载，依赖 ../../../plugin-sdk.js

约定与软件：
- get_info / generate(context) 为视频插件入口
- 配置存 user_resources/plugins/video_plugins/zealman-U26-H3/config.json

API 流程（与你提供的 fetch 一致）：
1. POST {base_url}/api/workflow/generate
   Headers: Content-Type: application/json
   Body: { "workflow_id", "input_values", "client_id"（可选，与 WebSocket 一致）}
2. 从响应取 prompt_id；可选 wss …/comfyui-ws 同步 progress_callback；轮询 GET {history_path}?prompt_id=
   - 推荐新接口 /api/workflow/result：返回 { success, pending, results:[{type,url,filename}] }
     pending=true 继续轮询；pending=false 即完成；results[].url 为 /output/... 相对地址，拼上 base_url 直接下载
   - 兼容旧接口 /api/comfy/proxy/history：返回 { <prompt_id>: { outputs:{ node:{ gifs/videos:[...] } } } }
3. 从结果中提取视频 URL 或 filename，下载保存为 mp4/webm/gif
"""

import copy
import base64
import hashlib
import json
import mimetypes
import os
import random
import re
import shutil
import ssl
import struct
import sys
import tempfile
import threading
import time
import uuid
import zipfile
import zlib
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from typing import Any, Callable, Dict, List, Optional, Tuple
from urllib.parse import urlencode, urlsplit, urlunsplit

import requests
import urllib3

try:
    import websocket
    from websocket import WebSocketTimeoutException

    _HAS_WEBSOCKET = True
except ImportError:
    websocket = None
    WebSocketTimeoutException = Exception  # type: ignore
    _HAS_WEBSOCKET = False

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

sys.path.append(os.path.dirname(os.path.dirname(__file__)))
sys.path.append(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
from plugin_utils import load_plugin_config

_PLUGIN_FILE = __file__
_PLUGIN_DIR = os.path.dirname(os.path.abspath(__file__))
_PRESETS_FILE = os.path.join(_PLUGIN_DIR, "presets.json")
_PLUGIN_ID = "zealman-U26-H3-粟粟直连"
_PLUGIN_VERSION = "1.0.9"
_UPDATE_MANIFEST_URLS = (
    "https://raw.githubusercontent.com/Susuys1232/zealman-u26-h3-zizi-plugin/main/manifest.json",
    "https://cdn.jsdelivr.net/gh/Susuys1232/zealman-u26-h3-zizi-plugin@main/manifest.json",
    "https://api.github.com/repos/Susuys1232/zealman-u26-h3-zizi-plugin/contents/manifest.json",
)

_DEFAULT_PARAMS = {
    "base_url": "",
    "server_urls": [],
    "per_server_concurrency": 1,
    "workflow_id": "",
    "prompt_key": "187:text",
    "negative_prompt_key": "437:text",
    "width_key": "515:value",
    "height_key": "516:value",
    "seed_key": "3:seed",
    "seed_value": 27296748841994,
    "randomize_seed": False,
    "output_width": 1280,
    "output_height": 720,
    "fixed_input_values": {},
    "custom_input_values": [],
    "image_input_mappings": [],
    "video_input_mappings": [],
    "audio_input_mappings": [],
    "reference_label_prefix": True,
    "poll_interval_sec": 2,
    "max_wait_sec": 1800,
    "request_timeout": 120,
    "generate_url_path": "/api/workflow/generate",
    "history_url_path": "/api/workflow/result",
    "upload_url_path": "",
    "upload_form_type": "input",
    "view_url_template": "",
    "view_url_path": "",
    "extra_headers": {},
    "enable_ws_progress": False,
    "ws_path": "/comfyui-ws",
    "ws_estimated_nodes": 32,
    "client_id": "",
    "free_vram_between_generate": True,
}


def get_info():
    return {
        "name": "zealman-U26-H3-粟粟直连",
        "description": "POST /api/workflow/generate + client_id；GET 轮询 /api/workflow/result（pending/results 简化结构），向下兼容旧 /api/comfy/proxy/history。无需 API Key。",
        "version": _PLUGIN_VERSION,
        "author": "粟粟",
    }


_PRESET_FIELDS = (
    "workflow_id",
    "workflow_template",
    "prompt_key",
    "negative_prompt_key",
    "width_key",
    "height_key",
    "seed_key",
    "seed_value",
    "randomize_seed",
    "output_width",
    "output_height",
    "image_input_mappings",
    "video_input_mappings",
    "audio_input_mappings",
    "reference_label_prefix",
    "custom_input_values",
    "fixed_input_values",
)


def _apply_active_preset(params: Dict[str, Any], cfg: Dict[str, Any]) -> Dict[str, Any]:
    """如果 config 里保存了 api_presets 数组，把当前 active_preset_index 指向的预设
    覆盖到 params 顶层，下游业务逻辑无需任何感知。"""
    presets = cfg.get("api_presets")
    if not isinstance(presets, list) or not presets:
        return params
    idx = cfg.get("active_preset_index")
    if not isinstance(idx, int) or idx < 0 or idx >= len(presets):
        idx = 0
    active = presets[idx]
    if not isinstance(active, dict):
        return params
    for k in _PRESET_FIELDS:
        if k in active:
            params[k] = active[k]
    return params


def _load_builtin_api_presets() -> List[Dict[str, Any]]:
    try:
        with open(_PRESETS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return [p for p in data if isinstance(p, dict) and p.get("workflow_id")]
    except Exception as e:
        print(f"[zealman-U26-H3] 读取内置预设失败: {e}")
    return []


def _normalize_preset_source(source: Any) -> str:
    s = str(source or "").strip()
    m = re.fullmatch(r"参考图(\d+)", s)
    if m:
        return f"图{m.group(1)}"
    m = re.fullmatch(r"参考音频(\d+)", s)
    if m:
        return f"音频{m.group(1)}"
    m = re.fullmatch(r"参考视频(\d+)", s)
    if m:
        return f"视频{m.group(1)}"
    return s


def _builtin_slots_to_mappings(slots: Any, kind: str) -> List[Dict[str, str]]:
    out: List[Dict[str, str]] = []
    if not isinstance(slots, list):
        return out
    for idx, slot in enumerate(slots):
        if not isinstance(slot, dict):
            continue
        key = str(slot.get("key") or "").strip()
        if not key:
            continue
        source = str(slot.get("source") or "").strip()
        if not source and kind == "image":
            source = f"参考图{idx + 1}"
        elif not source and kind == "audio":
            source = f"参考音频{idx + 1}"
        out.append({"key": key, "source": _normalize_preset_source(source)})
    return out


def _normalize_builtin_api_preset(raw: Dict[str, Any]) -> Dict[str, Any]:
    preset: Dict[str, Any] = {
        "_builtin_id": str(raw.get("id") or raw.get("workflow_id") or raw.get("name") or ""),
        "name": str(raw.get("ui_name") or raw.get("name") or raw.get("workflow_id") or "内置API"),
        "workflow_id": str(raw.get("workflow_id") or raw.get("id") or ""),
        "prompt_key": str(raw.get("prompt_key") or ""),
        "negative_prompt_key": str(raw.get("negative_prompt_key") or ""),
        "width_key": str(raw.get("width_key") or ""),
        "height_key": str(raw.get("height_key") or ""),
        "seed_key": str(raw.get("seed_key") or ""),
        "seed_value": raw.get("seed_value", 0),
        "randomize_seed": bool(raw.get("randomize_seed", False)),
        "output_width": raw.get("output_width", 1280),
        "output_height": raw.get("output_height", 720),
        "reference_label_prefix": True,
        "custom_input_values": raw.get("custom_input_values") if isinstance(raw.get("custom_input_values"), list) else [],
        "fixed_input_values": raw.get("fixed_input_values") if isinstance(raw.get("fixed_input_values"), dict) else {},
    }
    if isinstance(raw.get("workflow_template"), dict):
        preset["workflow_template"] = copy.deepcopy(raw["workflow_template"])

    image_maps = raw.get("image_input_mappings")
    if isinstance(image_maps, list):
        preset["image_input_mappings"] = [
            {"key": str(item.get("key") or ""), "source": _normalize_preset_source(item.get("source"))}
            for item in image_maps
            if isinstance(item, dict) and item.get("key")
        ]
    else:
        preset["image_input_mappings"] = _builtin_slots_to_mappings(raw.get("image_slots"), "image")

    video_maps = raw.get("video_input_mappings")
    if isinstance(video_maps, list):
        preset["video_input_mappings"] = [
            {"key": str(item.get("key") or ""), "source": _normalize_preset_source(item.get("source"))}
            for item in video_maps
            if isinstance(item, dict) and item.get("key")
        ]
    else:
        preset["video_input_mappings"] = _builtin_slots_to_mappings(raw.get("video_slots"), "video")

    audio_maps = raw.get("audio_input_mappings")
    if isinstance(audio_maps, list):
        preset["audio_input_mappings"] = [
            {"key": str(item.get("key") or ""), "source": _normalize_preset_source(item.get("source"))}
            for item in audio_maps
            if isinstance(item, dict) and item.get("key")
        ]
    else:
        preset["audio_input_mappings"] = _builtin_slots_to_mappings(raw.get("audio_slots"), "audio")

    return preset


def _legacy_config_as_preset(cfg: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if not any(k in cfg for k in _PRESET_FIELDS):
        return None
    preset: Dict[str, Any] = {"name": "默认"}
    for k in _PRESET_FIELDS:
        if k in cfg:
            preset[k] = cfg[k]
    return preset


def _merge_builtin_api_presets(cfg: Dict[str, Any]) -> List[Dict[str, Any]]:
    """内置 U26/U24 始终存在并置顶，过滤宿主自动创建的空 API。"""
    raw_existing = cfg.get("api_presets")
    if isinstance(raw_existing, list) and raw_existing:
        existing = [
            copy.deepcopy(p)
            for p in raw_existing
            if isinstance(p, dict) and str(p.get("workflow_id") or "").strip()
        ]
    else:
        legacy = _legacy_config_as_preset(cfg)
        existing = [legacy] if legacy and str(legacy.get("workflow_id") or "").strip() else []

    builtins = [copy.deepcopy(raw) for raw in _load_builtin_api_presets()]
    builtin_ids = {
        str(preset.get("workflow_id") or preset.get("id") or preset.get("name") or "")
        for preset in builtins
    }
    presets = builtins
    seen = set(builtin_ids)
    for preset in existing:
        ident = str(preset.get("workflow_id") or preset.get("id") or preset.get("name") or "")
        if ident in builtin_ids:
            # 用户保存过的内置预设参数优先，但模板缺失时由内置版本补全。
            index = next(
                i for i, item in enumerate(presets)
                if str(item.get("workflow_id") or item.get("id") or item.get("name") or "") == ident
            )
            if not isinstance(preset.get("workflow_template"), dict):
                preset["workflow_template"] = copy.deepcopy(presets[index].get("workflow_template"))
            presets[index] = preset
            continue
        if ident and ident not in seen:
            presets.append(preset)
            seen.add(ident)
    return presets


def get_params():
    params = _DEFAULT_PARAMS.copy()
    cfg = load_plugin_config(_PLUGIN_FILE)
    params.update(cfg)
    merged_presets = _merge_builtin_api_presets(cfg)
    params["api_presets"] = merged_presets
    _apply_active_preset(
        params,
        {
            "api_presets": merged_presets,
            "active_preset_index": cfg.get("active_preset_index", 0),
        },
    )
    params["server_urls"] = _normalize_server_entries(params.get("server_urls"), params.get("base_url"))
    params["builtin_api_presets"] = _load_builtin_api_presets()
    return params


# ==========================================================================
# 面板地址池：支持配置多个 zealman 面板地址，多任务并发时分摊到不同机器。
# 约定所有面板都是同一镜像克隆，共享同一个 workflow_id。
# ==========================================================================

_MAX_SERVER_SLOTS = 10
_SERVER_STATUS_VALUES = ("none", "empty", "green", "yellow", "red")

_RR_LOCK = threading.Lock()
_RR_CURSOR = 0

_RUNNING_LOCK = threading.Lock()
# server_index -> {task_id, ...}；UI 侧据此显示每台机器的在飞任务数
_RUNNING_SERVERS: Dict[int, set] = {}


def _clean_server_url(url: Any) -> str:
    u = _strip_json_paste_artifacts(str(url or "")).strip()
    return u.rstrip("/")


def _normalize_server_entries(raw: Any, base_url: Any = "") -> List[Dict[str, Any]]:
    """把配置里的地址池补齐成固定 10 个槽位。

    首次使用（server_urls 为空）时，把旧的单地址 base_url 迁移到槽位 1，
    保证老用户升级后无需重新填地址。
    """
    by_index: Dict[int, Dict[str, Any]] = {}
    if isinstance(raw, list):
        for item in raw:
            if isinstance(item, dict):
                try:
                    idx = int(item.get("index") or 0)
                except Exception:
                    continue
                url = _clean_server_url(item.get("url"))
                status = str(item.get("status") or "").strip()
            elif isinstance(item, str):
                idx = len(by_index) + 1
                url = _clean_server_url(item)
                status = "green" if url else "empty"
            else:
                continue
            if idx < 1 or idx > _MAX_SERVER_SLOTS or idx in by_index:
                continue
            if status not in _SERVER_STATUS_VALUES:
                status = "green" if url else "empty"
            if status != "none" and not url:
                status = "empty"
            by_index[idx] = {"index": idx, "url": url, "status": status}

    entries: List[Dict[str, Any]] = []
    for idx in range(1, _MAX_SERVER_SLOTS + 1):
        entries.append(by_index.get(idx) or {"index": idx, "url": "", "status": "none"})

    migrated = _clean_server_url(base_url)
    if not any(e["status"] != "none" for e in entries):
        entries[0] = {
            "index": 1,
            "url": migrated,
            "status": "green" if migrated else "empty",
        }
    elif migrated and not entries[0]["url"] and entries[0]["status"] == "none":
        entries[0] = {"index": 1, "url": migrated, "status": "green"}
    return entries


def _candidate_servers(params: dict) -> List[Dict[str, Any]]:
    """可用面板列表：优先只用检测通过（green）的；全都没检测过时退化为所有已填地址。"""
    entries = _normalize_server_entries(params.get("server_urls"), params.get("base_url"))
    active = [e for e in entries if e["status"] != "none" and e["url"]]
    green = [e for e in active if e["status"] == "green"]
    # 全都标红（可能是检测结果过期）时不要直接判定无机可用，仍然按原样尝试
    return green or [e for e in active if e["status"] != "red"] or active


def _running_counts() -> Dict[int, int]:
    with _RUNNING_LOCK:
        return {idx: len(tasks) for idx, tasks in _RUNNING_SERVERS.items() if tasks}


def _mark_server_running(server_index: int, task_id: str) -> None:
    with _RUNNING_LOCK:
        _RUNNING_SERVERS.setdefault(int(server_index), set()).add(str(task_id))


def _mark_server_done(server_index: int, task_id: str) -> None:
    with _RUNNING_LOCK:
        tasks = _RUNNING_SERVERS.get(int(server_index))
        if tasks:
            tasks.discard(str(task_id))
            if not tasks:
                _RUNNING_SERVERS.pop(int(server_index), None)


def _remote_server_loads(
    candidates: List[Dict[str, Any]],
    params: dict,
) -> Dict[int, int]:
    """读取各面板当前总任务数：进行中 + 排队。

    队列接口逐台查询会拖慢提交，所以并行请求；某台接口不可用时不写入结果，
    由调用方回退到本地在飞任务数和轮询策略。
    """
    if not candidates:
        return {}

    def _probe(entry: Dict[str, Any]) -> Tuple[int, Optional[int]]:
        try:
            result = _probe_queue_status(
                entry["url"],
                _history_get_headers(params),
                timeout=8,
            )
            if not result.get("available"):
                return entry["index"], None
            running = max(0, int(result.get("running") or 0))
            queued = max(0, int(result.get("queued") or 0))
            return entry["index"], running + queued
        except Exception as exc:
            print(
                f"[zealman-U26-H3] 查询面板{entry['index']}队列失败: {exc}"
            )
            return entry["index"], None

    loads: Dict[int, int] = {}
    workers = min(len(candidates), 8)
    with ThreadPoolExecutor(max_workers=max(1, workers)) as executor:
        for server_index, load in executor.map(_probe, candidates):
            if load is not None:
                loads[int(server_index)] = load
    return loads


def _pick_server(
    candidates: List[Dict[str, Any]],
    params: Optional[dict] = None,
    exclude: Optional[set] = None,
) -> Optional[Dict[str, Any]]:
    """按面板实际总任务数选择机器，并列时按轮询顺序打散。"""
    global _RR_CURSOR
    pool = [e for e in candidates if not exclude or e["index"] not in exclude]
    if not pool:
        return None
    local_busy = _running_counts()
    remote_busy = _remote_server_loads(pool, params or {}) if params is not None else {}
    busy = {
        entry["index"]: max(
            remote_busy.get(entry["index"], 0),
            local_busy.get(entry["index"], 0),
        )
        for entry in pool
    }
    with _RR_LOCK:
        cursor = _RR_CURSOR
        _RR_CURSOR = (cursor + 1) % max(1, len(pool))
    ordered = pool[cursor % len(pool):] + pool[: cursor % len(pool)]
    selected = min(ordered, key=lambda e: busy.get(e["index"], 0))
    print(
        "[zealman-U26-H3] 任务分配："
        + "，".join(
            f"面板{entry['index']}={busy.get(entry['index'], 0)}"
            for entry in ordered
        )
        + f" -> 面板{selected['index']}"
    )
    return selected


def _safe_progress_callback(cb: Optional[Callable[..., None]], message: str, percent: Optional[int] = None) -> None:
    if cb is None:
        return
    try:
        if percent is not None:
            cb(message, percent)
        else:
            cb(message)
    except TypeError:
        try:
            cb(message)
        except Exception:
            pass
    except Exception:
        pass


def _http_base_to_ws(base: str) -> str:
    b = (base or "").strip().rstrip("/")
    if b.startswith("https://"):
        return "wss://" + b[len("https://") :]
    if b.startswith("http://"):
        return "ws://" + b[len("http://") :]
    return b


def _ws_progress_worker(
    base: str,
    ws_path: str,
    client_id: str,
    prompt_id: str,
    progress_callback: Callable[..., None],
    stop_event: threading.Event,
    total_nodes_est: int,
    extra_headers: Optional[dict] = None,
) -> None:
    if not _HAS_WEBSOCKET or not websocket:
        return
    ws_url_base = _http_base_to_ws(base)
    if not ws_url_base.startswith(("ws://", "wss://")):
        return
    path = (ws_path or "/comfyui-ws").strip()
    if not path.startswith("/"):
        path = "/" + path
    q = urlencode({"clientId": client_id})
    url = f"{ws_url_base}{path}?{q}"

    header_list: List[str] = []
    ex = extra_headers or {}
    if isinstance(ex, dict):
        for k, v in ex.items():
            header_list.append(f"{str(k)}: {str(v)}")

    ws = None
    executed_nodes = 0
    total_est = max(8, int(total_nodes_est or 32))
    try:
        ws = websocket.create_connection(
            url,
            timeout=20,
            header=header_list if header_list else None,
            sslopt={"cert_reqs": ssl.CERT_NONE},
            enable_multithread=True,
        )
    except Exception as e:
        print(f"[zealman-U26-H3] WebSocket 未连接（将仅轮询 history）: {e}")
        return

    try:
        while not stop_event.is_set():
            try:
                if ws:
                    ws.settimeout(0.5)
                raw = ws.recv() if ws else ""
            except WebSocketTimeoutException:
                continue
            except Exception:
                break
            try:
                data = json.loads(raw)
            except Exception:
                continue
            if not isinstance(data, dict):
                continue
            pdata = data.get("data")
            if isinstance(pdata, dict):
                ep = pdata.get("prompt_id")
                if ep is not None and str(ep) != str(prompt_id):
                    continue

            typ = data.get("type")
            if typ == "executing" and isinstance(pdata, dict):
                node = pdata.get("node")
                if node is not None:
                    executed_nodes += 1
                    pct = min(99, int(executed_nodes * 100 / total_est))
                    _safe_progress_callback(progress_callback, "生成中", pct)
            elif typ == "progress" and isinstance(pdata, dict):
                v, m = pdata.get("value"), pdata.get("max")
                if isinstance(v, (int, float)) and isinstance(m, (int, float)) and m > 0:
                    pct = min(99, int(round(float(v) * 100 / float(m))))
                    _safe_progress_callback(progress_callback, "生成中", pct)
            elif typ == "executed":
                _safe_progress_callback(progress_callback, "生成中", 99)
    finally:
        if ws:
            try:
                ws.close()
            except Exception:
                pass


def _merge_extra_headers(params: dict) -> dict:
    extra = params.get("extra_headers") or {}
    if not isinstance(extra, dict):
        return {}
    return {str(k): str(v) for k, v in extra.items()}


def _post_generate_headers(params: dict) -> dict:
    """与浏览器 fetch 一致：POST 仅 Content-Type: application/json（可选合并 extra_headers）。"""
    h = {"Content-Type": "application/json"}
    h.update(_merge_extra_headers(params))
    return h


def _history_get_headers(params: dict) -> dict:
    """轮询 history 的 GET；默认不带 Content-Type（与常见 fetch 一致），仅合并 extra_headers。"""
    return dict(_merge_extra_headers(params))


def _media_download_headers() -> dict:
    """拉取媒体二进制，不使用 application/json。"""
    return {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Accept": "video/*,image/*,application/octet-stream,*/*;q=0.8",
    }


def _normalize_reference_images(context: dict) -> dict:
    reference_images = context.get("reference_images", {}) or {}

    if reference_images and "参考图片MAP" not in reference_images:
        if all(isinstance(k, int) or (isinstance(k, str) and str(k).isdigit()) for k in reference_images.keys()):
            reference_images = {"参考图片MAP": reference_images.copy()}

    ref_map_raw = reference_images.get("参考图片MAP")
    if isinstance(ref_map_raw, dict):
        reference_images["参考图片MAP"] = {
            int(k) if isinstance(k, str) and k.isdigit() else k: v for k, v in ref_map_raw.items()
        }

    first_frame_path = context.get("first_frame_path")
    end_frame_path = context.get("end_frame_path")
    if first_frame_path:
        reference_images["首帧"] = first_frame_path
    if end_frame_path:
        reference_images["尾帧"] = end_frame_path

    return reference_images


def _normalize_reference_videos(context: dict) -> dict:
    reference_videos = context.get("reference_videos", {}) or {}
    if not isinstance(reference_videos, dict):
        reference_videos = {}

    if reference_videos and "参考视频MAP" not in reference_videos:
        if all(isinstance(k, int) or (isinstance(k, str) and str(k).isdigit()) for k in reference_videos.keys()):
            reference_videos = {"参考视频MAP": reference_videos.copy()}

    ref_map_raw = reference_videos.get("参考视频MAP")
    if isinstance(ref_map_raw, dict):
        reference_videos["参考视频MAP"] = {
            int(k) if isinstance(k, str) and k.isdigit() else k: v for k, v in ref_map_raw.items()
        }

    source_video = (
        context.get("video_path")
        or context.get("source_video_path")
        or context.get("input_video_path")
        or context.get("video_file_path")
    )
    if source_video:
        reference_videos["原视频"] = str(source_video)

    return reference_videos


def _normalize_reference_audios(context: dict) -> dict:
    """整理音频来源。

    除了 context["reference_audios"]（参考音频MAP）之外，
    分镜自带的配音（audio_path）和用户导入的外部音频（external_audio_path）
    也一起收进来，方便对口型 / 音驱类工作流直接选用。
    """
    reference_audios = context.get("reference_audios", {}) or {}
    if not isinstance(reference_audios, dict):
        reference_audios = {}

    if reference_audios and "参考音频MAP" not in reference_audios:
        if all(isinstance(k, int) or (isinstance(k, str) and str(k).isdigit()) for k in reference_audios.keys()):
            reference_audios = {"参考音频MAP": reference_audios.copy()}

    ref_map_raw = reference_audios.get("参考音频MAP")
    if isinstance(ref_map_raw, dict):
        reference_audios["参考音频MAP"] = {
            int(k) if isinstance(k, str) and k.isdigit() else k: v for k, v in ref_map_raw.items()
        }

    scene_audio = context.get("scene_audio_path") or context.get("audio_path")
    if scene_audio:
        reference_audios["分镜音频"] = str(scene_audio)

    external_audio = context.get("external_audio_path")
    if external_audio:
        reference_audios["外部音频"] = str(external_audio)

    return reference_audios


_MAX_REF_IMAGE_SLOTS = 14
_MAX_REF_VIDEO_SLOTS = 14
_MAX_REF_AUDIO_SLOTS = 14
_PLACEHOLDER_SOURCES = ("占位图", "占位白图", "占位图256")


_PLACEHOLDER_LOCK = threading.Lock()


def _placeholder_image_path(size: int = 256, variant: int = 0) -> str:
    """生成白色占位图。部分工作流的图像输入必填，不给值会直接报错。

    批内并发时多个任务会同时命中这个缓存，用锁 + 临时文件改名，
    避免有人读到另一个线程刚写了一半的 PNG。
    """
    cache_dir = os.path.join(tempfile.gettempdir(), "zzdh_plugin_placeholder")
    suffix = "" if variant <= 0 else f"_{variant}"
    path = os.path.join(cache_dir, f"white_{size}x{size}{suffix}.png")
    if os.path.isfile(path) and os.path.getsize(path) > 0:
        return path

    def _chunk(tag: bytes, data: bytes) -> bytes:
        body = tag + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)

    with _PLACEHOLDER_LOCK:
        if os.path.isfile(path) and os.path.getsize(path) > 0:
            return path
        os.makedirs(cache_dir, exist_ok=True)
        rows = b"".join(b"\x00" + b"\xff" * (size * 3) for _ in range(size))
        png = b"\x89PNG\r\n\x1a\n"
        png += _chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0))
        png += _chunk(b"IDAT", zlib.compress(rows, 9))
        png += _chunk(b"IEND", b"")
        tmp_path = f"{path}.{os.getpid()}.{threading.get_ident()}.tmp"
        with open(tmp_path, "wb") as f:
            f.write(png)
        os.replace(tmp_path, path)
    return path


def _get_reference_image_path(reference_images: dict, source: str) -> str:
    source = str(source or "").strip()
    if not source:
        return ""
    if source in _PLACEHOLDER_SOURCES:
        return _placeholder_image_path()
    if source in ("首帧图片", "首帧"):
        return str(reference_images.get("首帧") or "")
    if source in ("尾帧图片", "尾帧"):
        return str(reference_images.get("尾帧") or "")
    m = re.fullmatch(r"参考图(\d+)", source)
    if not m:
        m = re.fullmatch(r"图(\d+)", source)
    if m:
        try:
            slot = int(m.group(1))
            if slot < 1 or slot > _MAX_REF_IMAGE_SLOTS:
                return ""
            idx = slot - 1
        except Exception:
            return ""
        ref_map = reference_images.get("参考图片MAP", {}) or {}
        return str(ref_map.get(idx) or "")
    return ""


def _get_reference_video_path(reference_videos: dict, source: str) -> str:
    source = str(source or "").strip()
    if not source:
        return ""
    if source in ("原视频", "视频", "源视频", "输入视频"):
        return str(reference_videos.get("原视频") or "")
    m = re.fullmatch(r"参考视频(\d+)", source)
    if not m:
        m = re.fullmatch(r"视频(\d+)", source)
    if m:
        try:
            slot = int(m.group(1))
            if slot < 1 or slot > _MAX_REF_VIDEO_SLOTS:
                return ""
            idx = slot - 1
        except Exception:
            return ""
        ref_map = reference_videos.get("参考视频MAP", {}) or {}
        return str(ref_map.get(idx) or "")
    return ""


def _get_reference_audio_path(reference_audios: dict, source: str) -> str:
    source = str(source or "").strip()
    if not source:
        return ""
    if source in ("分镜音频", "配音", "场景音频"):
        return str(reference_audios.get("分镜音频") or "")
    if source in ("外部音频", "导入音频"):
        return str(reference_audios.get("外部音频") or "")
    m = re.fullmatch(r"参考音频(\d+)", source)
    if not m:
        m = re.fullmatch(r"音频(\d+)", source)
    if m:
        try:
            slot = int(m.group(1))
            if slot < 1 or slot > _MAX_REF_AUDIO_SLOTS:
                return ""
            idx = slot - 1
        except Exception:
            return ""
        ref_map = reference_audios.get("参考音频MAP", {}) or {}
        return str(ref_map.get(idx) or "")
    return ""


# ==========================================================================
# 参考素材实体名：宿主按槽位算好了每个参考素材对应的角色/场景/物品名，通过
# context["reference_image_labels"] / ["reference_video_labels"] / ["reference_audio_labels"]
# 下发（形如 {0: "人物张三", 1: "场景客厅"}），key 与对应 MAP 的索引一一对应。
# 工作流里靠提示词区分多个主体时，把这层对应关系补进提示词能明显减少串脸。
# ==========================================================================

_REF_IMAGE_SLOT_RE = re.compile(r"(?:参考图|图)(\d+)")
_REF_VIDEO_SLOT_RE = re.compile(r"(?:参考视频|视频)(\d+)")
_REF_AUDIO_SLOT_RE = re.compile(r"(?:参考音频|音频)(\d+)")


def _normalize_entity_labels(raw: Any) -> Dict[int, str]:
    """把宿主给的标签容器统一成 {0 基索引: 名字}，空名字直接丢弃。"""
    if isinstance(raw, (list, tuple)):
        raw = dict(enumerate(raw))
    if not isinstance(raw, dict):
        return {}
    labels: Dict[int, str] = {}
    for k, v in raw.items():
        try:
            idx = int(k)
        except (TypeError, ValueError):
            continue
        name = str(v or "").strip()
        if name:
            labels[idx] = name
    return labels


def _slot_index(pattern: "re.Pattern", source: str, max_slots: int) -> int:
    """把映射里的 "参考图3"/"参考视频2" 还原成 MAP 的 0 基索引；非编号槽位返回 -1。"""
    m = pattern.fullmatch(str(source or "").strip())
    if not m:
        return -1
    slot = int(m.group(1))
    if slot < 1 or slot > max_slots:
        return -1
    return slot - 1


def _collect_named_slots(
    mappings: Any,
    labels: Dict[int, str],
    pattern: "re.Pattern",
    max_slots: int,
    resolver: Callable[[str], str],
) -> Dict[int, str]:
    """挑出既接入了工作流、又能取到实体名的槽位。

    只统计真正上传给工作流的槽位，避免提示词里提到模型根本看不见的素材。
    """
    if not labels or not isinstance(mappings, list):
        return {}
    named: Dict[int, str] = {}
    for mapping in mappings:
        if not isinstance(mapping, dict):
            continue
        if not _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip():
            continue
        source = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
        idx = _slot_index(pattern, source, max_slots)
        if idx < 0 or idx in named:
            continue
        name = labels.get(idx)
        if not name:
            continue
        path = resolver(source)
        if not path or not os.path.isfile(path):
            continue
        named[idx] = name
    return named


def _build_reference_label_prefix(params: dict, context: dict) -> str:
    """拼出 "图1 是人物张三，视频1 是场景客厅，音频1 是张三的音色，" 这样的提示词前缀。"""
    specs = (
        ("图", "image_input_mappings", "reference_image_labels", _REF_IMAGE_SLOT_RE,
         _MAX_REF_IMAGE_SLOTS, _normalize_reference_images(context), _get_reference_image_path),
        ("视频", "video_input_mappings", "reference_video_labels", _REF_VIDEO_SLOT_RE,
         _MAX_REF_VIDEO_SLOTS, _normalize_reference_videos(context), _get_reference_video_path),
        ("音频", "audio_input_mappings", "reference_audio_labels", _REF_AUDIO_SLOT_RE,
         _MAX_REF_AUDIO_SLOTS, _normalize_reference_audios(context), _get_reference_audio_path),
    )

    parts: List[str] = []
    for word, map_key, label_key, pattern, max_slots, sources, resolve in specs:
        named = _collect_named_slots(
            params.get(map_key),
            _normalize_entity_labels(context.get(label_key)),
            pattern,
            max_slots,
            lambda s, _src=sources, _r=resolve: _r(_src, s),
        )
        parts.extend(f"{word}{idx + 1} 是{name}" for idx, name in sorted(named.items()))

    if not parts:
        return ""
    return "，".join(parts) + "，"


def _strip_json_paste_artifacts(s: str) -> str:
    """
    用户从 API 文档 / JSON 里复制时，常多带成对引号或行尾逗号。
    去掉首尾空白、外层成对 ' 或 \"，并反复去掉末尾逗号后再剥引号。
    """
    t = str(s).strip()
    while True:
        t = t.rstrip().rstrip(",").strip()
        if len(t) >= 2 and t[0] == t[-1] and t[0] in ("'", '"'):
            t = t[1:-1].strip()
            continue
        break
    return t


def _coerce_custom_value(val: Any) -> Any:
    if val is None:
        return ""
    if isinstance(val, bool):
        return val
    if isinstance(val, int) and not isinstance(val, bool):
        return val
    if isinstance(val, float):
        return val
    s = _strip_json_paste_artifacts(str(val))
    if s == "":
        return ""
    if re.fullmatch(r"-?\d+", s):
        try:
            return int(s)
        except Exception:
            return s
    if re.fullmatch(r"-?\d+\.\d+", s):
        try:
            return float(s)
        except Exception:
            return s
    low = s.lower()
    if low in ("true", "false"):
        return low == "true"
    return s


def _normalize_workflow_input_value(key: str, value: Any) -> Any:
    """把界面显示用的宽高比名称转换为 H3 节点实际接受的值。"""
    if not str(key or "").strip().lower().endswith(":aspect"):
        return value
    if not isinstance(value, str):
        return value
    aspect_aliases = {
        "1:1 (Square)": "1:1",
        "2:3 (Portrait Photo)": "2:3",
        "3:2 (Photo)": "3:2",
        "3:4 (Portrait Standard)": "3:4",
        "4:3 (Standard)": "4:3",
        "9:16 (Portrait Widescreen)": "9:16",
        "16:9 (Widescreen)": "16:9",
        "21:9 (Ultrawide)": "21:9",
    }
    return aspect_aliases.get(value.strip(), value)


def _preset_input_values(params: dict) -> Dict[str, Any]:
    fixed = params.get("fixed_input_values") or {}
    if not isinstance(fixed, dict):
        fixed = {}
    preset: Dict[str, Any] = {}
    for k, v in fixed.items():
        nk = _strip_json_paste_artifacts(str(k))
        if nk and not nk.startswith("__h3_optimizer.") and nk != "__u26_model_source":
            preset[nk] = _normalize_workflow_input_value(nk, _coerce_custom_value(v))
    custom_list = params.get("custom_input_values") or []
    if isinstance(custom_list, list):
        for item in custom_list:
            if not isinstance(item, dict):
                continue
            ck = _strip_json_paste_artifacts(str(item.get("key") or ""))
            if not ck or ck.startswith("__h3_optimizer.") or ck == "__u26_model_source":
                continue
            preset[ck] = _normalize_workflow_input_value(
                ck, _coerce_custom_value(item.get("value"))
            )
    return preset


_H3_OPTIMIZER_PREFIX = "__h3_optimizer."
_H3_OPTIMIZER_BOOL_FIELDS = {"auto_optimize", "read_media", "has_api_key"}
_H3_OPTIMIZER_INT_FIELDS = {"max_tokens"}
_H3_OPTIMIZER_FIELDS = (
    "mode",
    "provider",
    "api_url",
    "api_key",
    "model",
    "protocol",
    "read_media",
    "output_language",
    "local_model",
    "local_mmproj",
    "local_device",
    "max_tokens",
    "auto_optimize",
    "has_api_key",
    "runninghub_api_key",
    "runninghub_overseas_api_key",
)


def _collect_h3_optimizer_settings(params: dict) -> Dict[str, Any]:
    settings: Dict[str, Any] = {}
    custom_list = params.get("custom_input_values") or []
    if not isinstance(custom_list, list):
        return settings
    for item in custom_list:
        if not isinstance(item, dict):
            continue
        key = _strip_json_paste_artifacts(str(item.get("key") or "")).strip()
        if not key.startswith(_H3_OPTIMIZER_PREFIX):
            continue
        field = key[len(_H3_OPTIMIZER_PREFIX):]
        if field not in _H3_OPTIMIZER_FIELDS:
            continue
        raw = item.get("value")
        if field in _H3_OPTIMIZER_BOOL_FIELDS:
            value = _truthy(raw, False)
        elif field in _H3_OPTIMIZER_INT_FIELDS:
            try:
                value = int(raw)
            except Exception:
                continue
        else:
            value = _strip_json_paste_artifacts(str(raw or ""))
        settings[field] = value
    return settings


def _u26_model_source(params: dict) -> str:
    custom_list = params.get("custom_input_values") or []
    if isinstance(custom_list, list):
        for item in custom_list:
            if not isinstance(item, dict) or item.get("key") != "__u26_model_source":
                continue
            value = str(item.get("value") or "253").strip()
            return value if value in ("253", "264") else "253"
    return "253"


def _optimizer_data_url(path: str) -> str:
    if not path or not os.path.isfile(path):
        return ""
    mime = mimetypes.guess_type(path)[0] or "application/octet-stream"
    try:
        with open(path, "rb") as fh:
            data = base64.b64encode(fh.read()).decode("ascii")
        return f"data:{mime};base64,{data}"
    except Exception as exc:
        print(f"[zealman-U26-H3] 读取提示词优化素材失败: {path}: {exc}")
        return ""


def _optimizer_base_url(panel_base: str) -> str:
    """优化接口未经过 zealman 双 u 网关，自动切到同实例的单 u ComfyUI 地址。"""
    base = str(panel_base or "").strip().rstrip("/")
    try:
        parts = urlsplit(base)
        host = parts.hostname or ""
        if host.startswith("uu"):
            host = host[1:]
            netloc = host
            if parts.port:
                netloc += f":{parts.port}"
            return urlunsplit((parts.scheme, netloc, parts.path, "", "")).rstrip("/")
    except Exception:
        pass
    return base


def _run_h3_prompt_optimizer(
    base: str,
    prompt: str,
    optimizer_settings: Dict[str, Any],
    reference_images: Dict[str, str],
    reference_videos: Dict[str, str],
    reference_audios: Dict[str, str],
    input_values: Dict[str, Any],
    timeout: int,
) -> str:
    """调用镜像内置 H3 优化接口，返回优化后的 prompt。"""
    if not _truthy(optimizer_settings.get("auto_optimize"), False):
        return prompt
    media = []
    for kind, prefix, refs in (
        ("image", "Picture", reference_images),
        ("video", "Video", reference_videos),
        ("audio", "Audio", reference_audios),
    ):
        for number in range(1, 15):
            source = f"图{number}" if kind == "image" else (f"视频{number}" if kind == "video" else f"音频{number}")
            input_key = f"185:ref_{kind}_{number}"
            if not str(input_values.get(input_key) or "").strip():
                continue
            if kind == "image":
                path = _get_reference_image_path(reference_images, source)
            elif kind == "video":
                path = _get_reference_video_path(reference_videos, source)
            else:
                path = _get_reference_audio_path(reference_audios, source)
            if not path or not os.path.isfile(path):
                continue
            item: Dict[str, Any] = {
                "kind": kind,
                "label": f"<{prefix} {number}>",
            }
            if kind == "image":
                data_url = _optimizer_data_url(path)
                if data_url:
                    item["images"] = [data_url]
            elif kind == "video":
                item["source_name"] = os.path.basename(str(input_values.get(input_key) or path))
            else:
                item["source_name"] = os.path.basename(str(input_values.get(input_key) or path))
            media.append(item)

    provider = str(optimizer_settings.get("provider") or "runninghub")
    active_api_key = str(optimizer_settings.get("api_key") or "").strip()
    api_keys = {
        "runninghub": str(optimizer_settings.get("runninghub_api_key") or ""),
        "runninghub_overseas": str(optimizer_settings.get("runninghub_overseas_api_key") or ""),
    }
    if active_api_key:
        api_keys[provider] = active_api_key
    config = dict(optimizer_settings)
    config["api_keys"] = api_keys
    config["provider"] = provider
    config["api_key"] = active_api_key or api_keys.get(provider, "")
    config["has_api_key"] = bool(
        config["api_key"]
    )
    config["provider_models"] = {
        provider: str(config.get("model") or ""),
    }
    request_id = uuid.uuid4().hex
    body = {
        "request_id": request_id,
        "prompt": prompt,
        "task": "Hybrid",
        "duration": int(_coerce_custom_value(input_values.get("185:duration_seconds", 5)) or 5),
        "media": media,
        "context": {
            "main_mode": str(input_values.get("185:main_mode") or "text_keyframes"),
            "keyframes": [],
            "audio_mode": str(input_values.get("185:audio_mode") or "native"),
        },
        "config": config,
    }
    optimizer_base = _optimizer_base_url(base)
    url = f"{optimizer_base}/goohai/minimax-h3/prompt-optimizer/optimize"
    print(
        f"[zealman-U26-H3] 调用提示词优化接口: {optimizer_base}, provider={provider}, "
        f"model={config.get('model')}, media={len(media)}, has_api_key={config['has_api_key']}"
    )
    response = requests.post(
        url,
        json=body,
        headers={"Content-Type": "application/json", "Accept": "application/json"},
        timeout=max(30, min(240, int(timeout or 120))),
        verify=False,
    )
    if response.status_code >= 400:
        raise RuntimeError(f"提示词优化 HTTP {response.status_code}: {response.text[:800]}")
    if _response_looks_like_html(response):
        raise RuntimeError(
            "提示词优化接口返回了控制面板 HTML，请确认单 u ComfyUI 地址可访问: "
            f"{optimizer_base}"
        )
    try:
        result = response.json()
    except Exception as exc:
        raise RuntimeError(f"提示词优化返回不是 JSON: {response.text[:500]}") from exc
    optimized = str(result.get("prompt") or result.get("optimized_prompt") or "").strip()
    if not optimized:
        raise RuntimeError(f"提示词优化未返回 prompt: {json.dumps(result, ensure_ascii=False)[:800]}")
    print(f"[zealman-U26-H3] 提示词优化完成: 原始{len(prompt)}字 -> 优化后{len(optimized)}字")
    return optimized


def _apply_h3_optimizer_settings(state: Dict[str, Any], settings: Dict[str, Any]) -> None:
    if not settings:
        return
    optimizer = state.get("optimizer")
    if not isinstance(optimizer, dict):
        optimizer = {}
    api_keys = optimizer.get("api_keys")
    if not isinstance(api_keys, dict):
        api_keys = {}
    for key, value in settings.items():
        if key == "runninghub_api_key":
            api_keys["runninghub"] = value
        elif key == "runninghub_overseas_api_key":
            api_keys["runninghub_overseas"] = value
        else:
            optimizer[key] = value
    optimizer["api_keys"] = api_keys
    provider = str(optimizer.get("provider") or "")
    if provider in api_keys:
        optimizer["api_key"] = api_keys.get(provider) or optimizer.get("api_key", "")
    provider_defaults = {
        "runninghub": ("https://www.runninghub.cn/openapi/v2", "runninghub"),
        "runninghub_overseas": ("https://www.runninghub.ai/openapi/v2", "runninghub"),
        "openai": ("https://api.openai.com/v1", "openai"),
        "gemini": ("https://generativelanguage.googleapis.com/v1beta", "gemini"),
        "openrouter": ("https://openrouter.ai/api/v1", "openai"),
        "dashscope": ("https://dashscope.aliyuncs.com/compatible-mode/v1", "openai"),
        "siliconflow": ("https://api.siliconflow.cn/v1", "openai"),
    }
    if provider in provider_defaults:
        optimizer["api_url"], optimizer["protocol"] = provider_defaults[provider]
    state["optimizer"] = optimizer


def _truthy(value: Any, default: bool = False) -> bool:
    """配置里布尔值可能被存成字符串，统一按字面量解析；无法识别时回落到默认值。"""
    if value is None:
        return default
    if isinstance(value, str):
        t = value.strip().lower()
        if t in ("1", "true", "yes", "on"):
            return True
        if t in ("0", "false", "no", "off"):
            return False
        return default
    return bool(value)


def _truthy_randomize_seed(params: dict) -> bool:
    v = params.get("randomize_seed", False)
    if isinstance(v, str):
        t = v.strip().lower()
        if t in ("1", "true", "yes", "on"):
            return True
        if t in ("0", "false", "no", "off", ""):
            return False
    return bool(v)


def _response_looks_like_html(response: requests.Response) -> bool:
    ct = (response.headers.get("Content-Type") or "").lower()
    if "text/html" in ct:
        return True
    head = (response.text or "").lstrip()[:80].lower()
    return head.startswith("<!doctype") or head.startswith("<html")


# 扩展名必须原样保留：ComfyUI 的 LoadImage / LoadVideo / LoadAudio 都按后缀
# 过滤 input 目录，被改成 .bin 的文件在节点下拉里根本不会出现。
_ALLOWED_UPLOAD_EXTS = frozenset((
    ".png", ".jpg", ".jpeg", ".webp", ".gif", ".bmp",
    ".mp4", ".webm", ".mov", ".mkv", ".avi", ".m4v",
    ".wav", ".mp3", ".flac", ".m4a", ".ogg", ".aac", ".opus", ".wma",
))


def _safe_multipart_basename(file_path: str) -> str:
    base = os.path.basename(file_path) or "upload"
    stem, ext = os.path.splitext(base)
    ext_l = (ext or "").lower()
    if ext_l not in _ALLOWED_UPLOAD_EXTS:
        ext_l = ".bin"
    safe_stem = re.sub(r"[^A-Za-z0-9._-]+", "_", stem).strip("._") or "upload"
    safe_stem = safe_stem[:80]
    return f"{safe_stem}{ext_l}"


# 面板文档《zealman-api接口说明》「文件上传」一节：
#   /api/comfy/upload/file  —— 推荐，通用文件上传，图片/视频/音频都收，
#                              表单字段名兼容 file / image / video / audio
#   /api/comfy/upload/image —— 旧兼容接口，只接受 image 字段且仅限图片
# 所以通用口必须排在前面，否则音频、视频会先撞上只认图片的旧口。
_UPLOAD_PATHS = (
    "/api/comfy/upload/file",
    "/api/comfy/upload/image",
    "/upload/image",
    "/api/upload/image",
    "/api/comfy/proxy/upload/image",
)

_MEDIA_KIND_LABELS = {"image": "图片", "video": "视频", "audio": "音频"}


def _upload_file_for_workflow(
    base_url: str,
    file_path: str,
    timeout: int,
    upload_url_path: str = "",
    extra_headers: Optional[dict] = None,
    form_type: str = "input",
    kind: str = "image",
) -> str:
    kind_label = _MEDIA_KIND_LABELS.get(kind, "文件")
    if not file_path or not os.path.exists(file_path):
        raise RuntimeError(f"文件不存在: {file_path}")

    upload_name = _safe_multipart_basename(file_path)
    ft = str(form_type or "").strip() or "input"
    base_headers = dict(extra_headers or {})

    # 文档推荐通用上传口字段名为 file；再按素材类型与旧 image 字段兜底。
    file_fields = tuple(dict.fromkeys(("file", kind, "image", "video", "audio")))

    candidate_paths: List[str] = []
    custom = str(upload_url_path or "").strip()
    if custom:
        if not custom.startswith("/"):
            custom = "/" + custom
        candidate_paths.append(custom)
    for p in _UPLOAD_PATHS:
        if p not in candidate_paths:
            candidate_paths.append(p)

    attempts: List[str] = []
    last_status: Optional[int] = None
    last_text = ""
    base_root = base_url.rstrip("/")

    def try_upload(url: str, method: str, file_field: str) -> Optional[str]:
        nonlocal last_status, last_text
        req_headers = dict(base_headers)
        req_headers.setdefault("Accept", "application/json, text/plain, */*")
        with open(file_path, "rb") as f:
            files = {file_field: (upload_name, f)}
            data = {"overwrite": "true", "type": ft, "subfolder": ""}
            response = requests.request(
                method.upper(),
                url,
                files=files,
                data=data,
                headers=req_headers,
                timeout=timeout,
                verify=False,
            )
        rel = url.replace(base_root, "", 1) if url.startswith(base_root) else url
        snippet = ""
        if _response_looks_like_html(response):
            snippet = "body≈HTML控制台页"
        elif response.text:
            snippet = (response.text[:120] + "…") if len(response.text) > 120 else response.text[:120]
        attempts.append(f"{method.upper()} {file_field} {rel} -> {response.status_code} {snippet[:40]}")
        if response.status_code >= 400:
            last_status = response.status_code
            last_text = (response.text or "")[:300]
            return None
        if _response_looks_like_html(response):
            last_status = response.status_code
            last_text = (
                "该 URL 返回了 HTML（多为控制台首页或未映射的上传路由），"
                "请核对 base_url 或在「文件上传路径」填写镜像文档中的实际上传地址。"
            )
            return None
        try:
            payload = response.json()
        except Exception:
            last_status = response.status_code
            last_text = (response.text or "")[:300] or "空响应"
            return None
        if not isinstance(payload, dict):
            last_text = str(payload)[:300]
            return None
        file_name = payload.get("name") or payload.get("filename")
        if not file_name:
            last_text = f"JSON 无 name 字段: {str(payload)[:300]}"
            return None
        print(f"[zealman-U26-H3] 上传成功: {file_name}")
        return str(file_name)

    for path in candidate_paths:
        url = f"{base_root}{path}"
        fields = file_fields
        if path.rstrip("/").lower().endswith("/upload/image"):
            fields = tuple(dict.fromkeys(("image", *file_fields)))
        for file_field in fields:
            got = try_upload(url, "post", file_field)
            if got:
                return got
        if custom and path == custom:
            for file_field in fields:
                got = try_upload(url, "put", file_field)
                if got:
                    return got

    detail = "; ".join(attempts[-12:])
    raise RuntimeError(
        f"上传{kind_label}失败（最后线索 HTTP {last_status}）: {last_text} | 已尝试: {detail}。"
        f"若多条路径均返回 HTML 控制台页，请设置正确的 upload_url_path。"
    )


def _should_free_vram(params: dict) -> bool:
    raw = params.get("free_vram_between_generate", True)
    if isinstance(raw, bool):
        return raw
    return str(raw).strip().lower() not in ("0", "false", "no", "off")


def _free_comfy_memory(
    base: str,
    headers: dict,
    timeout: int,
    *,
    unload_models: bool = True,
    free_memory: bool = True,
) -> None:
    """请求镜像清理 ComfyUI 显存；失败只记录，不阻断视频生成。"""
    url = f"{base.rstrip('/')}/api/comfy/proxy/free"
    req_headers = dict(headers or {})
    req_headers.setdefault("Content-Type", "application/json")
    req_headers.setdefault("Accept", "application/json, text/plain, */*")
    wait = min(30, max(5, int(timeout or 30)))
    try:
        response = requests.post(
            url,
            json={"unload_models": bool(unload_models), "free_memory": bool(free_memory)},
            headers=req_headers,
            timeout=wait,
            verify=False,
        )
        if response.status_code >= 400:
            print(
                f"[zealman-U26-H3] 清显存 HTTP {response.status_code}: "
                f"{(response.text or '')[:200]}"
            )
            return
        print("[zealman-U26-H3] 已请求清显存 /api/comfy/proxy/free")
    except Exception as exc:
        print(f"[zealman-U26-H3] 清显存失败（忽略，继续生成）: {exc}")


def _post_generate(
    base: str,
    generate_path: str,
    workflow_id: str,
    input_values: dict,
    headers: dict,
    timeout: int,
    client_id: Optional[str] = None,
    workflow_template: Optional[dict] = None,
) -> dict:
    url = f"{base.rstrip('/')}{generate_path}"
    body: Dict[str, Any] = {"workflow_id": workflow_id, "input_values": input_values}
    if isinstance(workflow_template, dict) and workflow_template:
        body["workflow_template"] = workflow_template
    if client_id:
        body["client_id"] = client_id
    r = requests.post(url, json=body, headers=headers, timeout=timeout, verify=False)
    if r.status_code >= 400:
        raise RuntimeError(f"generate HTTP {r.status_code}: {r.text[:500]}")
    return r.json()


_H3_MEDIA_INPUT_NAMES = (
    "first_frame",
    "last_frame",
    "hybrid_audio",
    "ref_image_1",
    "ref_image_2",
    "ref_image_3",
    "ref_image_4",
    "ref_image_5",
    "ref_image_6",
    "ref_image_7",
    "ref_image_8",
    "ref_image_9",
    "ref_video_1",
    "ref_video_2",
    "ref_video_3",
    "ref_audio_1",
    "ref_audio_2",
    "ref_audio_3",
)


def _prompt_media_tag_slots(prompt: str) -> Dict[str, set]:
    slots = {"Picture": set(), "Video": set(), "Audio": set()}
    for kind, number in re.findall(r"<(Picture|Video|Audio)\s+(\d+)>", str(prompt or ""), re.IGNORECASE):
        slots[kind.capitalize()].add(int(number))
    return slots


def _is_h3_template(workflow_template: Any) -> bool:
    if not isinstance(workflow_template, dict):
        return False
    node = workflow_template.get("185")
    return isinstance(node, dict) and node.get("class_type") == "MiniMaxH3IntegrationGH"


def _h3_mapping_is_referenced(key: str, tags: Dict[str, set]) -> bool:
    match = re.fullmatch(r"185:ref_(image|video|audio)_(\d+)", str(key or ""))
    if not match:
        return True
    kind = {"image": "Picture", "video": "Video", "audio": "Audio"}[match.group(1)]
    # H3 的标签校验按同类素材的连续数量判断。比如提示词用了 <Picture 7>，
    # 即使没有直接写 <Picture 4>/<Picture 6>，也要把前面的图片槽位补齐，
    # 否则节点会认为第 7 个图片标签不存在。
    max_slot = max(tags.get(kind) or {0})
    return int(match.group(2)) <= max_slot


def _sync_h3_state_json(
    raw_state: Any,
    node_inputs: Dict[str, Any],
    optimizer_settings: Optional[Dict[str, Any]] = None,
) -> str:
    """同步 H3 节点内部 GUI 状态，避免继续引用导入时的旧素材和旧提示词。"""
    state: Dict[str, Any] = {}
    if isinstance(raw_state, str) and raw_state.strip():
        try:
            parsed = json.loads(raw_state)
            if isinstance(parsed, dict):
                state = parsed
        except Exception:
            pass
    elif isinstance(raw_state, dict):
        state = copy.deepcopy(raw_state)

    mode = str(node_inputs.get("main_mode") or "text_keyframes")
    prompt = str(node_inputs.get("prompt") or "")
    # H3 的标签序号按媒体类型分别计算。固定为“首帧/尾帧、参考图、参考视频、音频”的
    # 顺序，避免模板原先的 hybrid_audio 或旧素材顺序影响 Picture/Audio 编号。
    media = []
    ordered_names = (
        "first_frame",
        "last_frame",
        "ref_image_1",
        "ref_image_2",
        "ref_image_3",
        "ref_image_4",
        "ref_image_5",
        "ref_image_6",
        "ref_image_7",
        "ref_image_8",
        "ref_image_9",
        "ref_video_1",
        "ref_video_2",
        "ref_video_3",
        "hybrid_audio",
        "ref_audio_1",
        "ref_audio_2",
        "ref_audio_3",
    )
    for name in ordered_names:
        value = str(node_inputs.get(name) or "").strip()
        if not value:
            continue
        if name == "hybrid_audio" or name.startswith("ref_audio_"):
            kind = "audio"
        elif name.startswith("ref_video_"):
            kind = "video"
        else:
            kind = "image"
        media.append([name, {"name": value, "kind": kind}])

    state["mode"] = mode
    state["media"] = media
    state["vacantMediaSlots"] = [
        name for name in ordered_names
        if not str(node_inputs.get(name) or "").strip()
    ]
    state["prompt"] = prompt
    prompts = state.get("prompts")
    if not isinstance(prompts, dict):
        prompts = {}
    prompts[mode] = prompt
    state["prompts"] = prompts
    state.setdefault("all_reference", "")
    _apply_h3_optimizer_settings(state, optimizer_settings or {})
    # optimizerCache 可能包含上一任务的文件名、提示词和媒体配置，不能复用。
    state.pop("optimizerCache", None)
    return json.dumps(state, ensure_ascii=False, separators=(",", ":"))


def _prepare_workflow_template(
    workflow_template: Any,
    input_values: Dict[str, Any],
    optimizer_settings: Optional[Dict[str, Any]] = None,
    u26_model_source: str = "253",
) -> Optional[dict]:
    """把本次任务的 input_values 合并进模板，尤其同步 H3 节点媒体状态。"""
    if not isinstance(workflow_template, dict) or not workflow_template:
        return None
    template = copy.deepcopy(workflow_template)

    node_243 = template.get("243")
    if isinstance(node_243, dict) and isinstance(node_243.get("inputs"), dict):
        selected = "253" if str(u26_model_source) == "253" else "264"
        node_243["inputs"]["model"] = [selected, 0]
        print(f"[zealman-U26-H3] 去油开关模型连线: 节点{selected} -> 节点243")

    h3_node = template.get("185")
    if isinstance(h3_node, dict) and isinstance(h3_node.get("inputs"), dict):
        node_inputs = h3_node["inputs"]
        # H3 的媒体输入不能沿用模板上一次任务的文件名。
        for name in _H3_MEDIA_INPUT_NAMES:
            node_inputs[name] = ""
        for key, value in input_values.items():
            if key.startswith("185:"):
                node_inputs[key[4:]] = value
        # 字字生成的 H3 提示词会包含 <Subject N>、<d> 等结构标签；
        # Goohai H3 的严格素材标签校验容易把这些也当素材标签检查，
        # 导致“当前提示词引用了不存在的素材标签”。API 提交时关闭严格模式，
        # Picture/Audio 的实际文件映射仍由 gh_state_json 和节点输入保证。
        node_inputs["strict_prompt_tags"] = False
        node_inputs["gh_state_json"] = _sync_h3_state_json(
            node_inputs.get("gh_state_json"),
            node_inputs,
            optimizer_settings,
        )
        print(
            "[zealman-U26-H3] H3节点185最终素材状态: "
            + json.dumps(
                {
                    name: node_inputs.get(name)
                    for name in _H3_MEDIA_INPUT_NAMES
                    if str(node_inputs.get(name) or "").strip()
                },
                ensure_ascii=False,
                default=str,
            )
        )

    # 兼容只读取 workflow_template 的网关实现。
    for key, value in input_values.items():
        if ":" not in key:
            continue
        node_id, input_name = key.split(":", 1)
        node = template.get(node_id)
        if isinstance(node, dict) and isinstance(node.get("inputs"), dict):
            node["inputs"][input_name] = value

    # U26 同时有一采和二采两个 VHS_VideoCombine。
    # 二采必须落盘到镜像 output/assets，否则即使后续节点执行完成，
    # /api/workflow/result 也不会返回二采视频。不要依赖 AnyExists 的
    # 动态 BOOLEAN 连线，提交给远端 API 时明确打开二采保存。
    for node in template.values():
        if not isinstance(node, dict) or not isinstance(node.get("inputs"), dict):
            continue
        if node.get("class_type") != "VHS_VideoCombine":
            continue
        prefix = str(node["inputs"].get("filename_prefix") or "")
        if "二采" in prefix or "2采" in prefix:
            node["inputs"]["save_output"] = True
    return template


def _get_history(
    base: str,
    history_path: str,
    prompt_id: str,
    headers: dict,
    timeout: int,
) -> Any:
    url = f"{base.rstrip('/')}{history_path}"
    r = requests.get(
        url,
        params={"prompt_id": prompt_id},
        headers=headers,
        timeout=timeout,
        verify=False,
    )
    if r.status_code >= 400:
        raise RuntimeError(f"history HTTP {r.status_code}: {r.text[:500]}")
    try:
        return r.json()
    except Exception:
        return r.text


def _queue_prompt_state(
    base: str,
    prompt_id: str,
    headers: dict,
    timeout: int,
) -> Optional[str]:
    """返回当前 prompt 在 ComfyUI 队列中的状态：running / pending / None。"""
    url = f"{base.rstrip('/')}/api/comfy/proxy/queue"
    try:
        response = requests.get(
            url,
            headers=headers,
            timeout=min(10, max(3, int(timeout or 10))),
            verify=False,
        )
        if response.status_code >= 400 or _response_looks_like_html(response):
            return None
        payload = response.json()
    except Exception:
        return None
    if not isinstance(payload, dict):
        return None

    wanted = str(prompt_id)
    for state, key in (("running", "queue_running"), ("pending", "queue_pending")):
        items = payload.get(key)
        if not isinstance(items, list):
            continue
        for item in items:
            if not isinstance(item, (list, tuple)):
                continue
            if any(str(part) == wanted for part in item[:2]):
                return state
    return None


_URL_RE = re.compile(r"https?://[^\s\"'<>]+", re.I)


def _extract_urls_from_text(s: str) -> List[str]:
    return _URL_RE.findall(s or "")


def _walk_collect_video_candidates(obj: Any, out: List[dict]) -> None:
    if obj is None:
        return
    if isinstance(obj, str):
        if obj.startswith("http://") or obj.startswith("https://"):
            out.append({"kind": "url", "url": obj})
        low = obj.lower()
        if low.endswith((".mp4", ".webm", ".mov", ".mkv", ".gif")) and not obj.startswith("http"):
            out.append({"kind": "filename", "filename": obj, "subfolder": "", "type": "output"})
        return
    if isinstance(obj, dict):
        if "url" in obj and isinstance(obj["url"], str):
            out.append({"kind": "url", "url": obj["url"]})
        fn = obj.get("filename")
        if isinstance(fn, str) and fn.strip():
            out.append(
                {
                    "kind": "filename",
                    "filename": fn,
                    "subfolder": str(obj.get("subfolder") or ""),
                    "type": str(obj.get("type") or "output"),
                }
            )
        for v in obj.values():
            _walk_collect_video_candidates(v, out)
        return
    if isinstance(obj, (list, tuple)):
        for v in obj:
            _walk_collect_video_candidates(v, out)


def _history_completed_or_failed(history_data: Any) -> Tuple[bool, Optional[str]]:
    """尽力判断 Comfy history 是否已有 outputs 或显式失败。"""
    if isinstance(history_data, dict):
        if history_data.get("error"):
            return True, str(history_data.get("error"))
        st = history_data.get("status")
        if isinstance(st, dict):
            if st.get("status_str") == "error" or st.get("error"):
                return True, str(st.get("error") or st.get("status_str"))
        outs = history_data.get("outputs")
        if isinstance(outs, dict) and outs:
            return True, None
    if isinstance(history_data, str) and history_data.strip():
        if "error" in history_data.lower() and len(history_data) < 2000:
            return True, history_data[:500]
    return False, None


def _dedupe_media_items(items: List[dict]) -> List[dict]:
    seen = set()
    uniq = []
    for item in items:
        key = json.dumps(item, sort_keys=True, ensure_ascii=False)
        if key not in seen:
            seen.add(key)
            uniq.append(item)
    return uniq


def _extract_output_videos_from_history(history_data: Any) -> List[dict]:
    """
    优先按官方 HTML 示例的方式解析：
    只读取 history[prompt_id].outputs.*.gifs / videos，
    避免把输入图 filename 或其它中间字段误判为结果视频。
    """
    items: List[dict] = []
    if not isinstance(history_data, dict):
        return items

    outputs = history_data.get("outputs")
    if not isinstance(outputs, dict):
        return items

    for node_id, node_output in outputs.items():
        if not isinstance(node_output, dict):
            continue
        for field_name in ("gifs", "videos"):
            media_list = node_output.get(field_name)
            if not isinstance(media_list, list):
                continue
            for media in media_list:
                if not isinstance(media, dict):
                    continue
                filename = media.get("filename")
                if isinstance(filename, str) and filename.strip():
                    items.append(
                        {
                            "kind": "filename",
                            "filename": filename,
                            "subfolder": str(media.get("subfolder") or ""),
                            "type": str(media.get("type") or "output"),
                            "node_id": str(node_id),
                        }
                    )
                elif isinstance(media.get("url"), str):
                    items.append(
                        {
                            "kind": "url",
                            "url": media["url"],
                            "node_id": str(node_id),
                        }
                    )
    return _dedupe_media_items(items)


def _first_videos_from_history(history_data: Any) -> List[dict]:
    explicit_outputs = _extract_output_videos_from_history(history_data)
    if explicit_outputs:
        return explicit_outputs

    # 回退：某些网关 history 结构可能不标准，再做宽松扫描
    found: List[dict] = []
    _walk_collect_video_candidates(history_data, found)
    return _dedupe_media_items(found)


_VIDEO_EXT_SET = (".mp4", ".webm", ".mov", ".mkv", ".gif")


def _is_workflow_result_payload(payload: Any) -> bool:
    """新接口 /api/workflow/result 的响应特征：含 pending 字段，或顶层 results 数组（区别于含 outputs 的旧 history 结构）。"""
    if not isinstance(payload, dict):
        return False
    if "pending" in payload:
        return True
    if isinstance(payload.get("results"), list) and "outputs" not in payload:
        return True
    return False


def _workflow_result_status(payload: Any) -> Tuple[bool, Optional[str]]:
    """解析 /api/workflow/result 状态：返回 (done, error_message)。"""
    if not isinstance(payload, dict):
        return False, None
    if payload.get("pending") is True:
        return False, None
    if payload.get("success") is False:
        err = payload.get("error") or payload.get("message")
        return True, str(err) if err else "任务失败（success=false）"
    if payload.get("pending") is False:
        return True, None
    if isinstance(payload.get("results"), list):
        return True, None
    return False, None


def _abs_url_from_relative(base_url: str, url: str) -> str:
    if url.startswith("http://") or url.startswith("https://"):
        return url
    base = base_url.rstrip("/")
    return base + url if url.startswith("/") else f"{base}/{url}"


_RAW_TYPE_PRIORITY = {"output": 0, "": 1, "input": 2, "temp": 3}


def _workflow_result_video_items(payload: Any, base_url: str) -> List[dict]:
    """从 /api/workflow/result.results 里筛出视频/动图下载项，url 已拼成绝对地址。

    优先按 type in {video, gif} 选；否则按 filename/url 扩展名兜底。
    实测服务器一次任务可能同时返回 temp 预览与 output 正片；
    这里按 raw.type 排序保证 output 在 temp 之前，调用方 [0] 即可拿到正片。
    兼容 filename 嵌套在 raw 字段里的实际响应。
    """
    if not isinstance(payload, dict):
        return []
    results = payload.get("results")
    if not isinstance(results, list):
        return []
    items: List[dict] = []
    for r in results:
        if not isinstance(r, dict):
            continue
        typ = str(r.get("type") or "").lower()
        url = r.get("url")
        raw_info = r.get("raw") if isinstance(r.get("raw"), dict) else {}
        filename = r.get("filename") or raw_info.get("filename") or ""
        raw_type = str(raw_info.get("type") or "").lower()
        node_id = (
            r.get("node_id")
            or r.get("nodeId")
            or r.get("output_node_id")
            or r.get("outputNodeId")
            or raw_info.get("node_id")
            or raw_info.get("nodeId")
            or raw_info.get("output_node_id")
            or raw_info.get("outputNodeId")
        )
        looks_like_video = typ in ("video", "gif")
        if not looks_like_video and isinstance(filename, str) and filename.lower().endswith(_VIDEO_EXT_SET):
            looks_like_video = True
        if not looks_like_video and isinstance(url, str):
            stem = url.lower().split("?", 1)[0]
            if stem.endswith(_VIDEO_EXT_SET):
                looks_like_video = True
        if not looks_like_video:
            continue
        if not isinstance(url, str) or not url.strip():
            continue
        items.append(
            {
                "kind": "url",
                "url": _abs_url_from_relative(base_url, url.strip()),
                "filename": str(filename or ""),
                "_raw_type": raw_type,
                "type": raw_type,
                "node_id": str(node_id) if node_id is not None else "",
            }
        )
    items = _dedupe_media_items(items)
    items.sort(key=lambda i: _RAW_TYPE_PRIORITY.get(str(i.get("_raw_type") or ""), 1))
    for i in items:
        i.pop("_raw_type", None)
    return items


def _video_item_text(item: dict) -> str:
    """把候选视频的可识别信息合并，供二采输出优先级判断。"""
    return " ".join(
        str(item.get(key) or "")
        for key in ("node_id", "filename", "url", "subfolder", "type")
    ).lower()


def _video_item_priority(item: dict) -> int:
    """
    U26 工作流有两个 VHS_VideoCombine：
      12  = 一采输出
      207 = 二采输出
    优先节点 207；部分网关会丢掉 node_id，此时再从文件名或 URL 中判断。
    """
    node_id = str(item.get("node_id") or "").strip()
    text = _video_item_text(item)
    if node_id == "207":
        return 1000
    if re.search(r"(^|[^0-9])207([^0-9]|$)", text):
        return 950
    if "二采" in text or "second" in text or "refine" in text or "upscale" in text:
        return 900
    if node_id == "12" or re.search(r"(^|[^0-9])12([^0-9]|$)", text):
        return 100
    if "一采" in text or "first" in text:
        return 90
    # 新接口不返回节点编号，但 results 按节点输出顺序排列。
    # 让调用方在同优先级时选择最后一个，兼容 U26 的 12 -> 207。
    raw_type = str(item.get("type") or item.get("_raw_type") or "").lower()
    if raw_type == "output":
        return 530
    if raw_type == "temp":
        return 470
    return 500


def _select_preferred_video(items: List[dict]) -> Optional[dict]:
    """从一个任务的多个视频候选中选择最终回传字字的文件。"""
    if not items:
        return None
    selected = max(
        enumerate(items),
        key=lambda pair: (_video_item_priority(pair[1]), pair[0]),
    )[1]
    descriptions = []
    for item in items:
        descriptions.append(
            "node={node} filename={filename} url={url}".format(
                node=str(item.get("node_id") or "?"),
                filename=str(item.get("filename") or ""),
                url=str(item.get("url") or ""),
            )
        )
    print(
        "[zealman-U26-H3] 结果候选: "
        + " | ".join(descriptions)[:4000]
    )
    print(
        "[zealman-U26-H3] 选择最终视频: "
        f"node={str(selected.get('node_id') or '?')} "
        f"filename={str(selected.get('filename') or '')}"
    )
    return selected


def _unwrap_history_payload(history_data: Any, prompt_id: str) -> Any:
    """兼容 history 外层再包一层 prompt_id / data。"""
    if isinstance(history_data, dict):
        if prompt_id in history_data and len(history_data) == 1:
            return history_data[prompt_id]
        if "data" in history_data and isinstance(history_data["data"], dict):
            inner = history_data["data"]
            if prompt_id in inner:
                return inner[prompt_id]
            return inner
    return history_data


def _looks_like_html_bytes(data: bytes) -> bool:
    prefix = (data or b"")[:200].lstrip().lower()
    return prefix.startswith(b"<!doctype html") or prefix.startswith(b"<html")


def _looks_like_video_bytes(data: bytes) -> bool:
    if not data or len(data) < 12:
        return False
    if data[:6] in (b"GIF87a", b"GIF89a"):
        return True
    if data[4:8] == b"ftyp":
        return True
    if data[:4] == b"\x1a\x45\xdf\xa3":
        return True
    return False


def _looks_like_video_response(resp: requests.Response) -> bool:
    content_type = str(resp.headers.get("Content-Type") or "").lower()
    if _looks_like_html_bytes(resp.content):
        return False
    if content_type.startswith("video/"):
        return True
    if "gif" in content_type:
        return True
    if "application/octet-stream" in content_type and len(resp.content) > 1024:
        return True
    return _looks_like_video_bytes(resp.content)


def _guess_video_extension(item: dict, raw: bytes, content_type: str) -> str:
    filename = str(item.get("filename") or "")
    ext = os.path.splitext(filename)[1].lower()
    if ext in (".mp4", ".webm", ".mov", ".mkv", ".gif"):
        return ext
    content_type = (content_type or "").lower()
    if "webm" in content_type or raw[:4] == b"\x1a\x45\xdf\xa3":
        return ".webm"
    if "gif" in content_type or raw[:6] in (b"GIF87a", b"GIF89a"):
        return ".gif"
    return ".mp4"


def _view_fetch_urls(
    base_url: str,
    history_path: str,
    view_url_path: str,
) -> List[str]:
    """
    zealman 控制台示例（comfy-workflow-api-*.html）拉图地址为：
      {base}/api/comfy/view?filename=&subfolder=&type=
    另兼容部分网关的 /api/comfy/proxy/view、根 /view。
    """
    base = base_url.rstrip("/")
    out: List[str] = []
    vup = (view_url_path or "").strip()
    if vup:
        if vup.startswith("http://") or vup.startswith("https://"):
            out.append(vup.rstrip("/"))
        else:
            out.append(base + (vup if vup.startswith("/") else "/" + vup))
    # 与官方 HTML 示例一致（优先）
    out.append(base + "/api/comfy/view")
    hp = (history_path or "").strip()
    if hp.endswith("/history"):
        out.append(base + hp[: -len("/history")] + "/view")
    out.append(base + "/api/comfy/proxy/view")
    out.append(base + "/view")
    seen = set()
    uniq: List[str] = []
    for u in out:
        if u and u not in seen:
            seen.add(u)
            uniq.append(u)
    return uniq


def _download_or_resolve_video(
    item: dict,
    base_url: str,
    view_template: str,
    timeout: int,
    history_path: str,
    view_url_path: str = "",
) -> Tuple[bytes, str]:
    media_headers = _media_download_headers()
    if item["kind"] == "url":
        u = item["url"]
        r = requests.get(u, headers=media_headers, timeout=timeout, verify=False)
        if r.status_code >= 400:
            raise RuntimeError(f"下载视频 HTTP {r.status_code}")
        if not _looks_like_video_response(r):
            raise RuntimeError(f"视频 URL 返回非视频: {u[:120]}")
        return r.content, str(r.headers.get("Content-Type") or "")
    filename = item["filename"]
    subfolder = item.get("subfolder") or ""
    typ = item.get("type") or "output"
    if view_template.strip():
        tpl = view_template
        url = (
            tpl.replace("{base_url}", base_url.rstrip("/"))
            .replace("{filename}", requests.utils.quote(filename, safe=""))
            .replace("{subfolder}", requests.utils.quote(subfolder, safe=""))
            .replace("{type}", requests.utils.quote(typ, safe=""))
        )
        r = requests.get(url, headers=media_headers, timeout=timeout, verify=False)
        if r.status_code >= 400:
            raise RuntimeError(f"view 拉视频 HTTP {r.status_code}: {url[:200]}")
        if not _looks_like_video_response(r):
            raise RuntimeError(f"view 返回非视频: {url[:120]}")
        return r.content, str(r.headers.get("Content-Type") or "")

    params = {"filename": filename, "type": typ, "subfolder": subfolder}
    tried: List[str] = []
    last_detail = ""
    for root in _view_fetch_urls(base_url, history_path, view_url_path):
        try:
            r = requests.get(root, params=params, headers=media_headers, timeout=timeout, verify=False)
            tried.append(f"{r.status_code} {root}")
            if r.status_code == 200 and _looks_like_video_response(r):
                print(f"[zealman-U26-H3] 已拉视频: {root}?filename=...")
                return r.content, str(r.headers.get("Content-Type") or "")
            last_detail = f"HTTP {r.status_code}, body[:80]={r.content[:80]!r}"
        except Exception as e:
            last_detail = str(e)
            tried.append(f"err {root}: {e}")
    raise RuntimeError(
        f"无法解析视频：filename={filename!r}。已尝试 GET view: {tried} 最后: {last_detail}。"
        f"若网关路径不同，请在 config.json 设置 view_url_path（如 /api/comfy/proxy/view）或完整 view_url_template。"
    )


def _bytes_to_file(raw: bytes, out_path: str) -> str:
    with open(out_path, "wb") as f:
        f.write(raw)
    return out_path


def _run_one_generation(
    prompt: str,
    width: int,
    height: int,
    params: dict,
    context: dict,
    base_override: str = "",
) -> str:
    progress_callback = context.get("progress_callback")
    base = _clean_server_url(base_override) or _clean_server_url(params.get("base_url"))
    workflow_id = _strip_json_paste_artifacts(str(params.get("workflow_id", "") or "")).strip()
    if not base or not workflow_id:
        raise RuntimeError("未配置 base_url 或 workflow_id")

    client_id = _strip_json_paste_artifacts(str(params.get("client_id") or "")).strip()
    if not client_id:
        client_id = f"api-client-{uuid.uuid4().hex[:12]}"
    _safe_progress_callback(progress_callback, "准备中")

    pk = _strip_json_paste_artifacts(str(params.get("prompt_key", "187:text") or "")).strip()
    npk = _strip_json_paste_artifacts(str(params.get("negative_prompt_key", "437:text") or "")).strip()
    wk = _strip_json_paste_artifacts(str(params.get("width_key", "515:value") or "")).strip()
    hk = _strip_json_paste_artifacts(str(params.get("height_key", "516:value") or "")).strip()
    negative_prompt = str(context.get("negative_prompt", "") or "").strip()
    reference_images = _normalize_reference_images(context)
    reference_videos = _normalize_reference_videos(context)
    reference_audios = _normalize_reference_audios(context)

    preset = _preset_input_values(params)
    input_values = dict(preset)
    if pk:
        input_values[pk] = prompt
    if npk and negative_prompt:
        input_values[npk] = negative_prompt
    if wk:
        input_values[wk] = width
    if hk:
        input_values[hk] = height

    workflow_template = params.get("workflow_template")
    h3_tag_filter = _is_h3_template(workflow_template)
    media_tags = _prompt_media_tag_slots(prompt) if h3_tag_filter else None
    has_media_tags = bool(media_tags and any(media_tags.values()))
    if h3_tag_filter:
        # 不继承预设或上次任务里的媒体文件名；下面只重新填入本次实际选中的素材。
        for name in _H3_MEDIA_INPUT_NAMES:
            input_values[f"185:{name}"] = ""
        if has_media_tags:
            print(
                "[zealman-U26-H3] H3 标签筛选: "
                + ", ".join(
                    f"<{kind} {number}>"
                    for kind in ("Picture", "Video", "Audio")
                    for number in sorted(media_tags[kind])
                )
            )

    seed_key = _strip_json_paste_artifacts(str(params.get("seed_key", "3:seed") or "")).strip()
    if seed_key:
        if _truthy_randomize_seed(params):
            s = random.randint(1, 10**15 - 1)
            input_values[seed_key] = s
            print(f"[zealman-U26-H3] {seed_key}={s} (randomize_seed)")
        elif seed_key not in preset:
            raw_seed = params.get("seed_value", "")
            if isinstance(raw_seed, (int, float)) and not isinstance(raw_seed, bool):
                s = int(raw_seed)
            else:
                rs = _strip_json_paste_artifacts(str(raw_seed))
                if rs == "":
                    s = random.randint(1, 10**15 - 1)
                else:
                    try:
                        s = int(rs)
                    except Exception as e:
                        raise RuntimeError(f"seed_value 非法（需整数）: {raw_seed}") from e
            input_values[seed_key] = s
            print(f"[zealman-U26-H3] {seed_key}={s}")

    image_mappings = params.get("image_input_mappings") or []
    if isinstance(image_mappings, list):
        timeout = int(params.get("request_timeout", 120))
        for mapping in image_mappings:
            if not isinstance(mapping, dict):
                continue
            key_u = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source_u = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key_u or not source_u:
                continue
            path_u = _get_reference_image_path(reference_images, source_u)
            if path_u and os.path.isfile(path_u):
                _safe_progress_callback(progress_callback, "上传参考图")
                break
        for mapping in image_mappings:
            if not isinstance(mapping, dict):
                continue
            key = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key or not source:
                continue
            if has_media_tags and not _h3_mapping_is_referenced(key, media_tags):
                print(f"[zealman-U26-H3] 跳过未引用图片 {key} <- {source}")
                continue
            image_path = _get_reference_image_path(reference_images, source)
            if not image_path:
                print(f"[zealman-U26-H3] 跳过图片映射 {key}: 未找到 {source}")
                continue
            if not os.path.isfile(image_path):
                print(f"[zealman-U26-H3] 跳过图片映射 {key}: 路径无效 {image_path!r}")
                continue
            # 勿因 preset/custom 里已有同名键而跳过上传；重新生成时必须再传文件
            uploaded_name = _upload_file_for_workflow(
                base,
                image_path,
                timeout,
                _strip_json_paste_artifacts(str(params.get("upload_url_path") or "")).strip(),
                _merge_extra_headers(params),
                _strip_json_paste_artifacts(str(params.get("upload_form_type") or "input")).strip() or "input",
                kind="image",
            )
            input_values[key] = uploaded_name
            print(f"[zealman-U26-H3] {key} <- {source} -> {uploaded_name}")

    video_mappings = params.get("video_input_mappings") or []
    if isinstance(video_mappings, list):
        timeout = int(params.get("request_timeout", 120))
        for mapping in video_mappings:
            if not isinstance(mapping, dict):
                continue
            key_v = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source_v = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key_v or not source_v:
                continue
            path_v = _get_reference_video_path(reference_videos, source_v)
            if path_v and os.path.isfile(path_v):
                _safe_progress_callback(progress_callback, "上传源视频")
                break
        for mapping in video_mappings:
            if not isinstance(mapping, dict):
                continue
            key = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key or not source:
                continue
            if has_media_tags and not _h3_mapping_is_referenced(key, media_tags):
                print(f"[zealman-U26-H3] 跳过未引用视频 {key} <- {source}")
                continue
            video_path = _get_reference_video_path(reference_videos, source)
            if not video_path:
                print(f"[zealman-U26-H3] 跳过视频映射 {key}: 未找到 {source}")
                continue
            if not os.path.isfile(video_path):
                print(f"[zealman-U26-H3] 跳过视频映射 {key}: 路径无效 {video_path!r}")
                continue
            uploaded_name = _upload_file_for_workflow(
                base,
                video_path,
                timeout,
                _strip_json_paste_artifacts(str(params.get("upload_url_path") or "")).strip(),
                _merge_extra_headers(params),
                _strip_json_paste_artifacts(str(params.get("upload_form_type") or "input")).strip() or "input",
                kind="video",
            )
            input_values[key] = uploaded_name
            print(f"[zealman-U26-H3] {key} <- {source} -> {uploaded_name}")

    audio_mappings = params.get("audio_input_mappings") or []
    if isinstance(audio_mappings, list):
        timeout = int(params.get("request_timeout", 120))
        for mapping in audio_mappings:
            if not isinstance(mapping, dict):
                continue
            key_a = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source_a = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key_a or not source_a:
                continue
            path_a = _get_reference_audio_path(reference_audios, source_a)
            if path_a and os.path.isfile(path_a):
                _safe_progress_callback(progress_callback, "上传音频")
                break
        for mapping in audio_mappings:
            if not isinstance(mapping, dict):
                continue
            key = _strip_json_paste_artifacts(str(mapping.get("key") or "")).strip()
            source = _strip_json_paste_artifacts(str(mapping.get("source") or "")).strip()
            if not key or not source:
                continue
            if has_media_tags and not _h3_mapping_is_referenced(key, media_tags):
                print(f"[zealman-U26-H3] 跳过未引用音频 {key} <- {source}")
                continue
            audio_path = _get_reference_audio_path(reference_audios, source)
            if not audio_path:
                print(f"[zealman-U26-H3] 跳过音频映射 {key}: 未找到 {source}")
                continue
            if not os.path.isfile(audio_path):
                print(f"[zealman-U26-H3] 跳过音频映射 {key}: 路径无效 {audio_path!r}")
                continue
            uploaded_name = _upload_file_for_workflow(
                base,
                audio_path,
                timeout,
                _strip_json_paste_artifacts(str(params.get("upload_url_path") or "")).strip(),
                _merge_extra_headers(params),
                _strip_json_paste_artifacts(str(params.get("upload_form_type") or "input")).strip() or "input",
                kind="audio",
            )
            input_values[key] = uploaded_name
            print(f"[zealman-U26-H3] {key} <- {source} -> {uploaded_name}")

    post_headers = _post_generate_headers(params)
    get_headers = _history_get_headers(params)
    timeout = int(params.get("request_timeout", 120))
    gen_path = _strip_json_paste_artifacts(
        str(params.get("generate_url_path") or "/api/workflow/generate")
    ).strip() or "/api/workflow/generate"
    hist_path = _strip_json_paste_artifacts(
        str(params.get("history_url_path") or "/api/workflow/result")
    ).strip() or "/api/workflow/result"

    if _should_free_vram(params):
        _free_comfy_memory(base, post_headers, timeout)

    optimizer_settings = _collect_h3_optimizer_settings(params)
    if _truthy(optimizer_settings.get("auto_optimize"), False):
        optimized_prompt = _run_h3_prompt_optimizer(
            base,
            prompt,
            optimizer_settings,
            reference_images,
            reference_videos,
            reference_audios,
            input_values,
            timeout,
        )
        if pk:
            input_values[pk] = optimized_prompt
        prompt = optimized_prompt
        print("[zealman-U26-H3] 本次任务将使用优化后的提示词提交")
    workflow_template = _prepare_workflow_template(
        workflow_template,
        input_values,
        optimizer_settings,
        _u26_model_source(params),
    )
    print(
        "[zealman-U26-H3] 本次 API 参数: "
        + json.dumps(
            {
                key: value
                for key, value in input_values.items()
                if key.startswith("185:") or key == "228:值"
            },
            ensure_ascii=False,
            default=str,
        )[:3000]
    )
    gen_resp = _post_generate(
        base,
        gen_path,
        workflow_id,
        input_values,
        post_headers,
        timeout,
        client_id=client_id,
        workflow_template=workflow_template,
    )
    prompt_id = (
        gen_resp.get("prompt_id")
        or gen_resp.get("promptId")
        or (gen_resp.get("data") or {}).get("prompt_id")
    )
    if not prompt_id:
        raise RuntimeError(f"generate 响应中无 prompt_id: {str(gen_resp)[:800]}")

    interval = max(0.5, float(params.get("poll_interval_sec", 2)))
    max_wait = max(interval, float(params.get("max_wait_sec", 1800)))
    deadline = time.monotonic() + max_wait
    history_payload: Any = None

    # 严格串行：不启用后台 WS 线程，统一由主线程轮询 history/result。
    queue_state = _queue_prompt_state(base, str(prompt_id), get_headers, timeout)
    last_progress_state = queue_state
    if progress_callback:
        _safe_progress_callback(
            progress_callback,
            "排队中" if queue_state == "pending" else "生成中",
            0,
        )

    view_tpl = _strip_json_paste_artifacts(str(params.get("view_url_template") or "")).strip()
    view_path = _strip_json_paste_artifacts(str(params.get("view_url_path") or "")).strip()

    def _save_video_bytes(raw: bytes, item: dict, content_type: str) -> str:
        output_dir = context.get("output_dir") or "."
        os.makedirs(output_dir, exist_ok=True)
        viewer_index = int(context.get("viewer_index", 0))
        ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        ext = _guess_video_extension(item, raw, content_type)
        name = f"{viewer_index:04d}_workflow_{ts}_{uuid.uuid4().hex[:8]}{ext}"
        path = os.path.join(output_dir, name)
        _safe_progress_callback(progress_callback, "生成中", 100)
        return _bytes_to_file(raw, path)

    try:
        while time.monotonic() < deadline:
            queue_state = _queue_prompt_state(base, str(prompt_id), get_headers, timeout)
            if queue_state != last_progress_state and queue_state in ("pending", "running"):
                _safe_progress_callback(
                    progress_callback,
                    "排队中" if queue_state == "pending" else "生成中",
                    0,
                )
                last_progress_state = queue_state
            history_payload = _get_history(base, hist_path, str(prompt_id), get_headers, timeout)

            # —— 优先：新接口 /api/workflow/result 的简化结构 ——
            if _is_workflow_result_payload(history_payload):
                done, err = _workflow_result_status(history_payload)
                if err:
                    raise RuntimeError(f"任务失败: {err}")
                if done:
                    videos = _workflow_result_video_items(history_payload, base)
                    selected_video = _select_preferred_video(videos)
                    if selected_video:
                        _safe_progress_callback(progress_callback, "下载中")
                        raw, content_type = _download_or_resolve_video(
                            selected_video, base, view_tpl, timeout, hist_path, view_path
                        )
                        return _save_video_bytes(raw, selected_video, content_type)
                    blob = json.dumps(history_payload, ensure_ascii=False)[:2000]
                    for u in _extract_urls_from_text(blob):
                        try:
                            resp = requests.get(
                                u, headers=_media_download_headers(), timeout=timeout, verify=False
                            )
                            if resp.status_code == 200 and _looks_like_video_response(resp):
                                _safe_progress_callback(progress_callback, "下载中")
                                return _save_video_bytes(
                                    resp.content,
                                    {"url": u},
                                    str(resp.headers.get("Content-Type") or ""),
                                )
                        except Exception:
                            continue
                    raise RuntimeError(f"任务已结束但 results 中无视频: {blob}")
                time.sleep(interval)
                continue

            # —— 兜底：旧接口 /api/comfy/proxy/history 的原始结构 ——
            inner = _unwrap_history_payload(history_payload, str(prompt_id))
            done, err = _history_completed_or_failed(inner)
            videos = _first_videos_from_history(inner)
            if err:
                raise RuntimeError(f"任务失败: {err}")
            selected_video = _select_preferred_video(videos)
            if selected_video:
                _safe_progress_callback(progress_callback, "下载中")
                raw, content_type = _download_or_resolve_video(
                    selected_video, base, view_tpl, timeout, hist_path, view_path
                )
                return _save_video_bytes(raw, selected_video, content_type)
            if done and not videos:
                blob = json.dumps(inner, ensure_ascii=False)[:2000]
                for u in _extract_urls_from_text(blob):
                    try:
                        resp = requests.get(
                            u, headers=_media_download_headers(), timeout=timeout, verify=False
                        )
                        if resp.status_code == 200 and _looks_like_video_response(resp):
                            _safe_progress_callback(progress_callback, "下载中")
                            return _save_video_bytes(
                                resp.content,
                                {"url": u},
                                str(resp.headers.get("Content-Type") or ""),
                            )
                    except Exception:
                        continue
                raise RuntimeError(f"任务已结束但未解析到视频，history 片段: {blob}")
            time.sleep(interval)

        raise RuntimeError(f"等待结果超时（>{max_wait}s），最后响应: {str(history_payload)[:500]}")
    finally:
        if _should_free_vram(params):
            _free_comfy_memory(base, post_headers, timeout)


class _BatchProgress:
    """批内并发时把各子任务的百分比合成一个总进度，避免多个任务互相把进度条拽来拽去。"""

    def __init__(self, callback: Optional[Callable[..., None]], total: int):
        self._callback = callback
        self._total = max(1, int(total))
        self._pcts: Dict[int, int] = {}
        self._lock = threading.Lock()

    def child(self, task_index: int) -> Callable[..., None]:
        def _cb(message: str, percent: Optional[int] = None) -> None:
            if percent is None:
                return
            with self._lock:
                self._pcts[task_index] = max(0, min(100, int(percent)))
                overall = int(sum(self._pcts.values()) / self._total)
                done = sum(1 for v in self._pcts.values() if v >= 100)
            if done < self._total:
                overall = min(99, overall)
            _safe_progress_callback(self._callback, f"{message} {done}/{self._total}", overall)

        return _cb

    def finish(self, task_index: int) -> None:
        self.child(task_index)("生成中", 100)


def _run_one_with_failover(
    prompt: str,
    width: int,
    height: int,
    params: dict,
    context: dict,
    task_label: str,
) -> str:
    """选一台面板执行；该台失败（离线/超时/网关报错）就换一台没试过的重试。"""
    candidates = _candidate_servers(params)
    if not candidates:
        raise RuntimeError("未配置任何 zealman 面板地址")

    max_retries = max(1, min(len(candidates), int(params.get("max_server_retries") or len(candidates))))
    task_id = f"{task_label}-{uuid.uuid4().hex[:8]}"
    tried: set = set()
    last_error: Optional[Exception] = None

    for attempt in range(1, max_retries + 1):
        entry = _pick_server(candidates, params=params, exclude=tried)
        if entry is None:
            break
        tried.add(entry["index"])
        server_index, server_url = entry["index"], entry["url"]
        _mark_server_running(server_index, task_id)
        try:
            print(f"[zealman-U26-H3] {task_label} -> 面板{server_index} {server_url}")
            return _run_one_generation(prompt, width, height, params, context, base_override=server_url)
        except Exception as e:
            last_error = e
            print(f"[zealman-U26-H3] {task_label} 面板{server_index} 失败({attempt}/{max_retries}): {e}")
        finally:
            _mark_server_done(server_index, task_id)

    raise last_error or RuntimeError("没有可用的 zealman 面板地址")


# ==========================================================================
# iframe UI 入口：面板连通性检测 + 在飞任务数
# 地址池本身由 UI 通过常规 saveParam 写入 server_urls，保持单一写入方，
# 避免 UI 与后端同时改同一个配置键。
# ==========================================================================


def _format_uptime(seconds: float) -> str:
    total = int(seconds)
    if total < 60:
        return f"{total}秒"
    if total < 3600:
        return f"{total // 60}分钟"
    if total < 86400:
        return f"{total // 3600}小时{total % 3600 // 60}分钟"
    return f"{total // 86400}天{total % 86400 // 3600}小时"


def _health_probe_detail(response) -> str:
    """面板 /api/health 返回 {status, timestamp, uptime}，把已运行时长带进状态提示。"""
    try:
        payload = response.json()
    except Exception:
        return "/api/health HTTP 200"
    if not isinstance(payload, dict):
        return "/api/health HTTP 200"
    status = str(payload.get("status") or "ok")
    uptime = payload.get("uptime")
    if isinstance(uptime, (int, float)) and uptime > 0:
        return f"/api/health {status} · 已运行 {_format_uptime(uptime)}"
    return f"/api/health {status}"


def _probe_server(url: str, history_path: str, headers: dict, timeout: int = 8) -> Tuple[bool, str]:
    """优先用面板文档的标准探针 GET /api/health（返回 200 即视为可用）；
    老镜像可能没有该路由，再退回结果接口与首页两级兜底。"""
    base = _clean_server_url(url)
    if not base:
        return False, "地址为空"
    if not base.startswith(("http://", "https://")):
        return False, "地址需以 http:// 或 https:// 开头"

    tried: List[str] = []

    def note(label: str, response) -> None:
        if _response_looks_like_html(response):
            tried.append(f"{label} HTTP {response.status_code} 返回HTML")
        else:
            tried.append(f"{label} HTTP {response.status_code}")

    try:
        r = requests.get(f"{base}/api/health", headers=headers, timeout=timeout, verify=False)
        # 未映射的路由常被网关兜回控制台首页，HTML 不能当成健康
        if r.status_code == 200 and not _response_looks_like_html(r):
            return True, _health_probe_detail(r)
        note("/api/health", r)
    except Exception as e:
        tried.append(f"/api/health {e}")

    path = history_path if history_path.startswith("/") else "/" + history_path
    try:
        r = requests.get(
            f"{base}{path}",
            params={"prompt_id": "zzdh-health-probe"},
            headers=headers,
            timeout=timeout,
            verify=False,
        )
        # 探针 prompt_id 不存在，网关一般回 200/404 的 JSON；只要不是 5xx 且不是控制台 HTML 就算通
        if r.status_code < 500 and not _response_looks_like_html(r):
            return True, f"{path} HTTP {r.status_code}"
        note(path, r)
    except Exception as e:
        tried.append(f"{path} {e}")

    # 最后一级只证明机器活着；API 探针都没通时如实写进提示，别让绿灯误导
    try:
        r = requests.get(base, timeout=timeout, verify=False)
        if r.status_code < 400:
            return True, f"仅首页可达 HTTP {r.status_code}（API 探针未通: {'；'.join(tried)}）"
        note("/", r)
    except Exception as e:
        tried.append(f"/ {e}")

    return False, "；".join(tried)


def _count_items(value: Any) -> int:
    if isinstance(value, list):
        return len(value)
    if isinstance(value, dict):
        return len(value)
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return max(0, int(value))
    return 0


def _extract_queue_counts(payload: Any) -> Optional[Tuple[int, int]]:
    """从 ComfyUI /queue 或 zealman queue-status 的不同返回格式里取进行中/排队数量。"""
    if not isinstance(payload, dict):
        return None

    running_keys = (
        "queue_running",
        "running",
        "running_tasks",
        "active",
        "executing",
        "processing",
    )
    queued_keys = (
        "queue_pending",
        "pending",
        "queued",
        "waiting",
        "pending_tasks",
        "queue",
    )

    running = 0
    queued = 0
    found = False
    for key in running_keys:
        if key in payload:
            running = _count_items(payload.get(key))
            found = True
            break
    for key in queued_keys:
        if key in payload:
            queued = _count_items(payload.get(key))
            found = True
            break

    # 部分面板只回 busy=true，没有细分数量；按“至少有 1 个进行中或排队”兜底显示。
    if not found and isinstance(payload.get("busy"), bool):
        return (1 if payload.get("busy") else 0), 0

    exec_info = payload.get("exec_info")
    if isinstance(exec_info, dict) and "queue_remaining" in exec_info:
        queued = _count_items(exec_info.get("queue_remaining"))
        running = 1 if queued > 0 and payload.get("busy") is True else running
        found = True

    results = payload.get("results")
    if isinstance(results, list):
        running = sum(1 for item in results if isinstance(item, dict) and item.get("status") == "running")
        queued = sum(1 for item in results if isinstance(item, dict) and item.get("status") == "queued")
        found = True

    if found:
        return running, queued
    return None


def _probe_queue_status(base_url: str, headers: dict, timeout: int = 8) -> Dict[str, Any]:
    base = _clean_server_url(base_url)
    if not base:
        return {"available": False, "running": 0, "queued": 0, "detail": "地址为空"}

    paths = (
        "/api/comfy/proxy/queue",
        "/api/comfy/queue",
        "/queue",
        "/api/comfy/proxy/prompt",
        "/prompt",
        "/api/comfy/queue-status",
    )
    tried: List[str] = []
    for path in paths:
        url = f"{base}{path}"
        try:
            response = requests.get(url, headers=headers, timeout=timeout, verify=False)
        except Exception as e:
            tried.append(f"{path} {e}")
            continue
        if response.status_code >= 400:
            tried.append(f"{path} HTTP {response.status_code}")
            continue
        if _response_looks_like_html(response):
            tried.append(f"{path} 返回HTML")
            continue
        try:
            payload = response.json()
        except Exception:
            tried.append(f"{path} 非JSON")
            continue
        counts = _extract_queue_counts(payload)
        if counts is None:
            tried.append(f"{path} 无队列字段")
            continue
        running, queued = counts
        return {
            "available": True,
            "running": running,
            "queued": queued,
            "detail": f"{path} 跑{running} 排{queued}",
            "source": path,
        }

    return {
        "available": False,
        "running": 0,
        "queued": 0,
        "detail": "未取到队列信息：" + "；".join(tried[-4:]),
    }


def _version_tuple(value: Any) -> Tuple[int, ...]:
    numbers = re.findall(r"d+", str(value or ""))
    return tuple(int(number) for number in numbers[:4]) or (0,)


def _check_plugin_update() -> Dict[str, Any]:
    manifests: List[Tuple[Tuple[int, ...], Dict[str, Any], str]] = []
    errors: List[str] = []
    headers = {"User-Agent": "zealman-u26-h3-zizi-plugin"}
    for url in _UPDATE_MANIFEST_URLS:
        try:
            response = requests.get(url, headers=headers, timeout=(5, 12))
            response.raise_for_status()
            payload = response.json()
            if "api.github.com" in url and isinstance(payload, dict) and payload.get("content"):
                raw = base64.b64decode(str(payload["content"])).decode("utf-8-sig")
                payload = json.loads(raw)
            if not isinstance(payload, dict):
                raise ValueError("返回内容不是 JSON 对象")
            version = str(payload.get("version") or "").strip()
            if not version:
                raise ValueError("清单缺少 version")
            manifests.append((_version_tuple(version), payload, url))
        except Exception as exc:
            errors.append(f"{url}: {exc}")
    if not manifests:
        print("[zealman-U26-H3] 检查更新失败: " + " | ".join(errors))
        return {"ok": False, "error": "连接更新服务器超时，请稍后重试"}
    _, manifest, manifest_url = max(manifests, key=lambda item: item[0])
    if not isinstance(manifest, dict):
        return {"ok": False, "error": "更新清单格式错误"}
    latest = str(manifest.get("version") or "").strip()
    download_url = str(manifest.get("download_url") or "").strip()
    if not latest or not download_url:
        return {"ok": False, "error": "更新清单缺少 version 或 download_url"}
    return {
        "ok": True,
        "has_update": _version_tuple(latest) > _version_tuple(_PLUGIN_VERSION),
        "current_version": _PLUGIN_VERSION,
        "latest_version": latest,
        "download_url": download_url,
        "sha256": str(manifest.get("sha256") or "").strip().lower(),
        "notes": str(manifest.get("changelog") or "").strip() or "无更新说明",
        "manifest_url": manifest_url,
    }


def _sha256_file(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().lower()


def _find_plugin_payload(root: str) -> Optional[str]:
    direct = os.path.join(root, _PLUGIN_ID)
    if os.path.isfile(os.path.join(direct, "main.py")):
        return direct
    if os.path.isfile(os.path.join(root, "main.py")):
        return root
    for current, dirs, files in os.walk(root):
        dirs[:] = [name for name in dirs if name != "__MACOSX"]
        if "main.py" in files and "info.json" in files:
            return current
    return None


def _apply_plugin_update(download_url: str, expected_sha256: str = "") -> Dict[str, Any]:
    checked = _check_plugin_update()
    if not checked.get("ok"):
        return checked
    url = str(download_url or checked.get("download_url") or "").strip()
    expected = str(expected_sha256 or checked.get("sha256") or "").strip().lower()
    if not url:
        return {"ok": False, "error": "更新包地址为空"}

    temp_dir = tempfile.mkdtemp(prefix="zealman_u26_update_")
    package_path = os.path.join(temp_dir, "plugin.zip")
    extract_dir = os.path.join(temp_dir, "extract")
    try:
        with requests.get(url, timeout=(10, 180), stream=True) as response:
            response.raise_for_status()
            with open(package_path, "wb") as output:
                for chunk in response.iter_content(1024 * 1024):
                    if chunk:
                        output.write(chunk)
        actual = _sha256_file(package_path)
        if expected and actual != expected:
            raise RuntimeError(f"SHA256 校验失败: {actual}")
        os.makedirs(extract_dir, exist_ok=True)
        with zipfile.ZipFile(package_path, "r") as archive:
            archive.extractall(extract_dir)
        payload = _find_plugin_payload(extract_dir)
        if not payload:
            raise RuntimeError("更新包内未找到插件文件")

        backup_dir = f"{_PLUGIN_DIR}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        shutil.copytree(_PLUGIN_DIR, backup_dir)
        allowed_files = ("main.py", "info.json", "presets.json")
        for name in allowed_files:
            source = os.path.join(payload, name)
            if os.path.isfile(source):
                shutil.copy2(source, os.path.join(_PLUGIN_DIR, name))
        source_ui = os.path.join(payload, "ui")
        target_ui = os.path.join(_PLUGIN_DIR, "ui")
        if os.path.isdir(source_ui):
            if os.path.isdir(target_ui):
                shutil.rmtree(target_ui)
            shutil.copytree(source_ui, target_ui)
        return {
            "ok": True,
            "applied_version": checked.get("latest_version"),
            "backup_dir": backup_dir,
            "message": "更新完成，请重启字字动画生效",
        }
    except Exception as exc:
        return {"ok": False, "error": f"更新失败: {exc}"}
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def _list_optimizer_models(data: Dict[str, Any]) -> Dict[str, Any]:
    base = str(data.get("api_url") or "").strip().rstrip("/")
    api_key = str(data.get("api_key") or "").strip()
    protocol = str(data.get("protocol") or "openai").strip().lower()
    if not base:
        return {"ok": False, "error": "请先填写 API 地址"}
    if not api_key:
        return {"ok": False, "error": "请先填写 API Key"}

    try:
        if protocol == "gemini":
            url = f"{base}/models"
            response = requests.get(
                url,
                params={"key": api_key, "pageSize": 1000},
                headers={"Accept": "application/json"},
                timeout=(8, 30),
            )
        else:
            url = f"{base}/models"
            response = requests.get(
                url,
                headers={
                    "Authorization": f"Bearer {api_key}",
                    "Accept": "application/json",
                    "User-Agent": "zealman-u26-h3-zizi-plugin",
                },
                timeout=(8, 30),
            )
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        detail = ""
        try:
            detail = str(response.text or "")[:300]
        except Exception:
            pass
        print(f"[zealman-U26-H3] 获取模型列表失败: {exc}; {detail}")
        return {"ok": False, "error": f"获取模型列表失败: {exc}"}

    models: List[str] = []
    if isinstance(payload, dict):
        items = payload.get("data")
        if not isinstance(items, list):
            items = payload.get("models")
        if isinstance(items, list):
            for item in items:
                if isinstance(item, str):
                    model_id = item
                elif isinstance(item, dict):
                    model_id = item.get("id") or item.get("name") or item.get("model")
                else:
                    model_id = ""
                model_id = str(model_id or "").strip()
                if model_id:
                    models.append(model_id)
    models = sorted(set(models), key=str.lower)
    return {"ok": True, "models": models, "count": len(models)}


def _test_optimizer_api(data: Dict[str, Any]) -> Dict[str, Any]:
    base = str(data.get("api_url") or "").strip().rstrip("/")
    api_key = str(data.get("api_key") or "").strip()
    model = str(data.get("model") or "").strip()
    protocol = str(data.get("protocol") or "openai").strip().lower()
    if not base:
        return {"ok": False, "error": "请先填写 API 地址"}
    if not api_key:
        return {"ok": False, "error": "请先填写 API Key"}
    if not model:
        return {"ok": False, "error": "请先选择或输入模型"}

    started = time.monotonic()
    try:
        if protocol == "gemini":
            model_name = model.removeprefix("models/")
            url = f"{base}/models/{model_name}:generateContent"
            response = requests.post(
                url,
                params={"key": api_key},
                json={
                    "contents": [{"role": "user", "parts": [{"text": "只回复：测试成功"}]}],
                    "generationConfig": {"maxOutputTokens": 32, "temperature": 0},
                },
                headers={"Content-Type": "application/json"},
                timeout=(8, 60),
            )
        elif protocol == "responses":
            response = requests.post(
                f"{base}/responses",
                json={"model": model, "input": "只回复：测试成功", "max_output_tokens": 32},
                headers={
                    "Authorization": f"Bearer {api_key}",
                    "Content-Type": "application/json",
                },
                timeout=(8, 60),
            )
        else:
            response = requests.post(
                f"{base}/chat/completions",
                json={
                    "model": model,
                    "messages": [{"role": "user", "content": "只回复：测试成功"}],
                    "max_tokens": 32,
                    "temperature": 0,
                },
                headers={
                    "Authorization": f"Bearer {api_key}",
                    "Content-Type": "application/json",
                },
                timeout=(8, 60),
            )
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        detail = ""
        try:
            detail = str(response.text or "")[:300]
        except Exception:
            pass
        print(f"[zealman-U26-H3] 优化 API 测试失败: {exc}; {detail}")
        return {"ok": False, "error": f"测试失败: {exc}"}

    elapsed_ms = int((time.monotonic() - started) * 1000)
    text = ""
    try:
        if protocol == "gemini":
            text = payload["candidates"][0]["content"]["parts"][0]["text"]
        elif protocol == "responses":
            text = payload.get("output_text") or ""
            if not text:
                text = payload["output"][0]["content"][0]["text"]
        else:
            text = payload["choices"][0]["message"]["content"]
    except Exception:
        text = "接口已返回有效 JSON"
    return {
        "ok": True,
        "elapsed_ms": elapsed_ms,
        "model": str(payload.get("model") or model) if isinstance(payload, dict) else model,
        "message": str(text or "测试成功")[:200],
    }


def handle_action(action, data, context=None):
    data = data if isinstance(data, dict) else {}

    if action == "check_server_status":
        params = get_params()
        hist_path = _strip_json_paste_artifacts(
            str(params.get("history_url_path") or "/api/workflow/result")
        ).strip() or "/api/workflow/result"
        url = _clean_server_url(data.get("url"))
        healthy, detail = _probe_server(url, hist_path, _history_get_headers(params))
        task_info = _probe_queue_status(url, _history_get_headers(params))
        if task_info.get("available"):
            detail = f"{detail} · {task_info.get('detail')}"
        return {
            "ok": True,
            "healthy": healthy,
            "detail": detail,
            "task_info": task_info,
            "_index": data.get("_index"),
            "url": url,
        }

    if action == "get_running_servers":
        return {"ok": True, "running_servers": {str(k): v for k, v in _running_counts().items()}}

    if action == "get_api_presets":
        params = get_params()
        return {
            "ok": True,
            "api_presets": params.get("api_presets") or [],
            "builtin_api_presets": params.get("builtin_api_presets") or [],
            "active_preset_index": params.get("active_preset_index", 0),
        }

    if action == "check_update":
        return _check_plugin_update()

    if action == "apply_update":
        return _apply_plugin_update(
            str(data.get("download_url") or ""),
            str(data.get("sha256") or ""),
        )

    if action == "list_optimizer_models":
        return _list_optimizer_models(data)

    if action == "test_optimizer_api":
        return _test_optimizer_api(data)

    return {"ok": False, "error": f"未知动作: {action}"}


def generate(context):
    print("\n" + "=" * 60)
    print("zealman-U26-H3 插件开始生成")
    print("=" * 60)

    plugin_params = context.get("plugin_params") or get_params()
    prompt = context.get("prompt", "").strip()
    batch_num = max(1, int(context.get("batch_num", 1)))
    reference_images = _normalize_reference_images(context)
    if reference_images:
        print(f"[zealman-U26-H3] 参考图片已就绪: {list(reference_images.keys())}")

    if _truthy(plugin_params.get("reference_label_prefix"), True):
        prefix = _build_reference_label_prefix(plugin_params, context)
        if prefix:
            prompt = prefix + prompt
            print(f"[zealman-U26-H3] 参考素材实体名前缀: {prefix}")

    candidates = _candidate_servers(plugin_params)
    print(f"[zealman-U26-H3] 可用面板 {len(candidates)} 个: " + ", ".join(
        f"{e['index']}:{e['url']}" for e in candidates
    ))

    cw = int(plugin_params.get("output_width") or plugin_params.get("custom_width") or 1280)
    ch = int(plugin_params.get("output_height") or plugin_params.get("custom_height") or 720)

    try:
        per_server = max(1, int(plugin_params.get("per_server_concurrency") or 1))
    except Exception:
        per_server = 1
    workers = min(batch_num, max(1, len(candidates) * per_server))

    try:
        if workers <= 1 or batch_num <= 1:
            paths: List[str] = []
            for i in range(batch_num):
                print(f"--- 第 {i + 1}/{batch_num} 个 ---")
                p = _run_one_with_failover(prompt, cw, ch, plugin_params, context, f"视频{i + 1}")
                paths.append(p)
                print(f"OK {p}")
            return paths

        print(f"[zealman-U26-H3] 批内并发 {workers} 路（共 {batch_num} 个）")
        aggregator = _BatchProgress(context.get("progress_callback"), batch_num)

        def _task(index: int) -> str:
            task_context = dict(context)
            task_context["progress_callback"] = aggregator.child(index)
            path = _run_one_with_failover(prompt, cw, ch, plugin_params, task_context, f"视频{index + 1}")
            aggregator.finish(index)
            print(f"OK 第 {index + 1}/{batch_num} 个 {path}")
            return path

        with ThreadPoolExecutor(max_workers=workers) as pool:
            # map 保序：返回的第 i 个路径始终对应第 i 个任务
            return list(pool.map(_task, range(batch_num)))
    except Exception as e:
        msg = f"生成失败: {e}"
        print(f"ERROR {msg}")
        import traceback

        traceback.print_exc()
        raise Exception(f"PLUGIN_ERROR:::{msg}")


