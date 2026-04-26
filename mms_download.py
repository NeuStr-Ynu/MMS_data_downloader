from __future__ import annotations

import re
import time
import threading
from pathlib import Path
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin
from concurrent.futures import ThreadPoolExecutor, as_completed, CancelledError

import requests
from bs4 import BeautifulSoup

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText


SOURCE_PRESETS = {
    "SPDF": {
        "label": "NASA SPDF",
        "root_url": "https://spdf.gsfc.nasa.gov/pub/data/mms/",
    },
    "LASP": {
        "label": "LASP SDC",
        "root_url": "https://lasp.colorado.edu/mms/sdc/public/about/browse/",
    },
}

THEMIS_ROOT_URL = "https://spdf.gsfc.nasa.gov/pub/data/themis/"


# =========================
# Core downloader
# =========================


def get_source_config(source_name):
    source_key = str(source_name or "SPDF").strip().upper()
    if source_key not in SOURCE_PRESETS:
        valid = ", ".join(SOURCE_PRESETS.keys())
        raise ValueError(f"Unknown MMS source '{source_name}'. Available: {valid}")
    return SOURCE_PRESETS[source_key]


def build_source_page_urls(source_name, var_dir, year, month, day):
    source = get_source_config(source_name)
    root_url = ensure_trailing_slash(source["root_url"])
    day_url = f"{root_url}{var_dir}/{year:04d}/{month:02d}/{day:02d}/"
    month_url = f"{root_url}{var_dir}/{year:04d}/{month:02d}/"
    return day_url, month_url


def describe_source(source_name):
    source = get_source_config(source_name)
    return f"{str(source_name).upper()} ({source['label']}) - {source['root_url']}"


def is_burst_mode(parts):
    return any(str(part).lower() == "brst" for part in parts)


def render_progress_bar(pct, width=20):
    filled = max(0, min(width, int(pct / 100 * width)))
    return "[" + "█" * filled + "░" * (width - filled) + "]"


def format_bytes(n):
    if n is None or n <= 0:
        return "??"
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024.0:
            return f"{n:.1f}{unit}"
        n /= 1024.0
    return f"{n:.1f}TB"


# =========================
# Task collection (scan only, no download)
# =========================


def mms_collect_tasks(file_prefix, tint, destination_dir, opts, log_func=None, stop_event=None):
    """
    Scan MMS directory pages and return (tasks, skipped_files) without downloading.
    Each task dict: {"file_url", "local_path", "fname"}
    """
    opts = set_default_opts(opts or {})
    destination_dir = Path(destination_dir)

    def log(msg):
        if log_func:
            log_func(msg)
        elif opts["Verbose"]:
            print(msg)

    t0, t1 = normalize_tint(tint)
    var_parts = file_prefix.split("_")
    var_dir = "/".join(var_parts)
    dir_parts = var_parts

    dt_start = datetime(t0.year, t0.month, t0.day, 0, 0, 0, tzinfo=timezone.utc)
    dt_end = datetime(t1.year, t1.month, t1.day, 0, 0, 0, tzinfo=timezone.utc)

    day_list = []
    cur = dt_start
    while cur <= dt_end:
        day_list.append(cur)
        cur += timedelta(days=1)

    month_cache = {}
    skipped_files = []
    tasks = []
    seen_local_paths = set()
    download_prev_pending = opts["DownloadPrev"]

    session = requests.Session()
    session.headers.update({"User-Agent": "Mozilla/5.0 (Python MMS downloader GUI)"})
    source_name = opts["SourceSite"]

    for dt_day in day_list:
        if stop_event and stop_event.is_set():
            log("  ⛔ Scan stopped.")
            break

        Y, M, D = dt_day.year, dt_day.month, dt_day.day
        day_url, month_url = build_source_page_urls(source_name, var_dir, Y, M, D)

        html_content = ""
        base_url_used = ""

        try:
            html_content = read_page(session, day_url, opts["TimeoutSec"])
            base_url_used = ensure_trailing_slash(day_url)
            log(f"[{dt_day.strftime('%Y-%m-%d')}] Use DAY page: {day_url}")
        except Exception as e_day:
            if opts["Debug"]:
                log(f"[{dt_day.strftime('%Y-%m-%d')}] DAY page failed: {e_day}")
            if month_url in month_cache:
                html_content = month_cache[month_url]
                base_url_used = ensure_trailing_slash(month_url)
                log(f"[{dt_day.strftime('%Y-%m-%d')}] Use MONTH page (cache): {month_url}")
            else:
                try:
                    html_content = read_page(session, month_url, opts["TimeoutSec"])
                    month_cache[month_url] = html_content
                    base_url_used = ensure_trailing_slash(month_url)
                    log(f"[{dt_day.strftime('%Y-%m-%d')}] Use MONTH page: {month_url}")
                except Exception as e_month:
                    log(f"⚠️ 页面读取失败: {month_url}")
                    if opts["Debug"]:
                        log(f"  DAY error  : {e_day}")
                        log(f"  MONTH error: {e_month}")
                    continue

        hrefs = extract_cdf_hrefs_bs4(html_content, debug=False)
        if not hrefs:
            log("  (no .cdf links found on page)")
            continue

        basenames = []
        time_infos = []
        for href in hrefs:
            fname = href_basename(href)
            basenames.append(fname)
            dt, mode = extract_timestamp_from_mms_filename(fname)
            time_infos.append((dt, mode))

        if opts["Debug"]:
            valid_times = [dt for dt, mode in time_infos if dt is not None]
            log(f"  href count = {len(hrefs)}, valid time count = {len(valid_times)}")
            if valid_times:
                log(f"  first file time = {valid_times[0]}, last = {valid_times[-1]}")
            log(f"  request t0 = {t0}, t1 = {t1}")

        hit_idx = []
        for i, (dt, mode) in enumerate(time_infos):
            if dt is None:
                continue
            if mode == "datetime14":
                ep = dt.timestamp()
                if t0.timestamp() <= ep <= t1.timestamp():
                    hit_idx.append(i)
            elif mode == "date8":
                day_start = dt
                day_end = dt + timedelta(days=1)
                if day_end > t0 and day_start <= t1:
                    hit_idx.append(i)

        if opts["Debug"]:
            log(f"  hit_idx count = {len(hit_idx)}")

        if not hit_idx:
            continue

        dl_idx_list = list(hit_idx)
        if download_prev_pending:
            i0 = hit_idx[0]
            if i0 > 0:
                dl_idx_list = [i0 - 1] + dl_idx_list
            download_prev_pending = False

        dl_idx_list = unique_stable(dl_idx_list)

        if is_burst_mode(dir_parts):
            save_dir = destination_dir.joinpath(*dir_parts, f"{Y:04d}", f"{M:02d}", f"{D:02d}")
        else:
            save_dir = destination_dir.joinpath(*dir_parts, f"{Y:04d}", f"{M:02d}")
        save_dir.mkdir(parents=True, exist_ok=True)

        for i in dl_idx_list:
            href = hrefs[i]
            fname = basenames[i]
            local_path = save_dir / fname

            if str(local_path) in seen_local_paths:
                continue
            seen_local_paths.add(str(local_path))

            if local_path.exists():
                skipped_files.append(str(local_path))
                log(f"  ⏭️ Skip (exists): {fname}")
                continue

            file_url = build_url_from_href(base_url_used, href)
            tasks.append({"file_url": file_url, "local_path": local_path, "fname": fname})
            if opts["Debug"]:
                log(f"  queued: {file_url}")

    return tasks, skipped_files


def themis_collect_tasks(file_prefix, tint, destination_dir, opts, log_func=None, stop_event=None):
    """
    Scan THEMIS directory pages and return (tasks, skipped_files) without downloading.
    """
    opts = set_default_opts(opts or {})
    destination_dir = Path(destination_dir)

    def log(msg):
        if log_func:
            log_func(msg)
        elif opts["Verbose"]:
            print(msg)

    t0, t1 = normalize_tint(tint)
    var_parts = file_prefix.split("_")
    var_dir = "/".join(var_parts)

    root_url = ensure_trailing_slash(THEMIS_ROOT_URL)
    year_list = list(range(t0.year, t1.year + 1))

    skipped_files = []
    tasks = []
    seen_local_paths = set()

    session = requests.Session()
    session.headers.update({"User-Agent": "Mozilla/5.0 (Python THEMIS downloader GUI)"})

    for Y in year_list:
        if stop_event and stop_event.is_set():
            log("  ⛔ Scan stopped.")
            break

        year_url = f"{root_url}{var_dir}/{Y:04d}/"
        try:
            html_content = read_page(session, year_url, opts["TimeoutSec"])
            log(f"[{Y:04d}] YEAR page: {year_url}")
        except Exception as e:
            log(f"⚠️ 页面读取失败: {year_url} ({e})")
            continue

        hrefs = extract_cdf_hrefs_bs4(html_content)
        if not hrefs:
            log("  (no .cdf links found on page)")
            continue

        save_dir = destination_dir.joinpath(*var_parts, f"{Y:04d}")
        save_dir.mkdir(parents=True, exist_ok=True)

        for href in hrefs:
            fname = href_basename(href)
            dt, mode = extract_timestamp_from_mms_filename(fname)
            if dt is None:
                continue

            if mode == "datetime14":
                ep = dt.timestamp()
                if not (t0.timestamp() <= ep <= t1.timestamp()):
                    continue
            elif mode == "date8":
                day_start = dt
                day_end = dt + timedelta(days=1)
                if not (day_end > t0 and day_start <= t1):
                    continue

            local_path = save_dir / fname
            if str(local_path) in seen_local_paths:
                continue
            seen_local_paths.add(str(local_path))

            if local_path.exists():
                skipped_files.append(str(local_path))
                log(f"  ⏭️ Skip (exists): {fname}")
                continue

            file_url = build_url_from_href(ensure_trailing_slash(year_url), href)
            tasks.append({"file_url": file_url, "local_path": local_path, "fname": fname})
            if opts["Debug"]:
                log(f"  queued: {file_url}")

    return tasks, skipped_files


# =========================
# Unified download executor
# =========================


def execute_downloads(tasks, opts, log_func=None, overall_progress_func=None,
                      stop_event=None, pause_event=None,
                      on_file_start=None, on_file_progress=None, on_file_finish=None):
    """
    Download all tasks concurrently with full thread-pool utilisation.

    Callbacks (all optional, called from worker threads — must be thread-safe):
      on_file_start(task_id, fname)
      on_file_progress(task_id, fname, pct, done_bytes, total_bytes)
      on_file_finish(task_id, fname, ok, msg)
    """
    opts = set_default_opts(opts)
    ok_files = []
    fail_files = []
    total = len(tasks)
    done = 0

    if overall_progress_func:
        overall_progress_func(0, total)

    if not tasks:
        return ok_files, fail_files

    def make_callbacks(task_id, fname):
        _state = [0.0, -10.0]  # [last_update_time, last_pct]

        def _on_start():
            if on_file_start:
                on_file_start(task_id, fname)

        def _progress(done_bytes, total_bytes):
            if on_file_progress:
                now = time.monotonic()
                pct = (done_bytes / total_bytes * 100) if total_bytes > 0 else -1
                if now - _state[0] >= 0.3 or (pct >= 0 and abs(pct - _state[1]) >= 5.0):
                    _state[0] = now
                    _state[1] = pct
                    on_file_progress(task_id, fname, pct, done_bytes, total_bytes)

        return _on_start, _progress

    with ThreadPoolExecutor(max_workers=opts["MaxWorkers"]) as executor:
        future_to_info = {}
        for i, task in enumerate(tasks):
            fname = task.get("fname", Path(task["local_path"]).name)
            on_start_cb, prog_cb = make_callbacks(i, fname)
            future = executor.submit(
                download_one_file,
                task["file_url"], task["local_path"], opts,
                stop_event, pause_event, prog_cb, on_start_cb,
            )
            future_to_info[future] = (i, fname, task["file_url"])

        cancelled_early = False
        for future in as_completed(future_to_info):
            task_id, fname, file_url = future_to_info[future]

            try:
                local_path, ok, msg, _ = future.result()
            except CancelledError:
                # Future was cancelled before it started - skip silently
                continue
            except Exception as e:
                ok, msg, local_path = False, str(e), None

            if on_file_finish:
                on_file_finish(task_id, fname, ok, msg)
            else:
                if ok and log_func:
                    log_func(f"  ✅ Downloaded: {local_path}")
                elif not ok and log_func:
                    log_func(f"  ❌ Failed: {file_url} | {msg}")

            if ok:
                ok_files.append(str(local_path))
            else:
                fail_files.append(f"{file_url} | {msg}")

            done += 1
            if overall_progress_func:
                overall_progress_func(done, total)

            if stop_event and stop_event.is_set() and not cancelled_early:
                cancelled_early = True
                for f in future_to_info:
                    if not f.done():
                        f.cancel()
                if log_func:
                    log_func("  ⛔ Downloads stopped by user.")

    return ok_files, fail_files


# =========================
# High-level wrappers (backward-compatible)
# =========================


def mms_download_v3_bs4_mt(file_prefix, tint, destination_dir, opts=None, log_func=None, progress_func=None):
    """MMS downloader — backward-compatible wrapper."""
    opts = set_default_opts(opts or {})

    def log(msg):
        if log_func:
            log_func(msg)
        elif opts["Verbose"]:
            print(msg)

    tasks, skipped_files = mms_collect_tasks(file_prefix, tint, destination_dir, opts, log)

    log("============ Task summary before download ============")
    log(f"To download : {len(tasks)}")
    log(f"Skipped     : {len(skipped_files)}")
    log("=====================================================")

    ok_files, fail_files = execute_downloads(tasks, opts, log_func=log, overall_progress_func=progress_func)

    log("============ MMS download summary ============")
    log(f"OK      : {len(ok_files)}")
    log(f"Skipped : {len(skipped_files)}")
    log(f"Failed  : {len(fail_files)}")
    if fail_files:
        log("--- Failed list (up to 20) ---")
        for item in fail_files[:20]:
            log(item)
    log("=============================================")

    return ok_files, skipped_files, fail_files


def themis_download_bs4_mt(file_prefix, tint, destination_dir, opts=None, log_func=None, progress_func=None):
    """THEMIS downloader — backward-compatible wrapper."""
    opts = set_default_opts(opts or {})

    def log(msg):
        if log_func:
            log_func(msg)
        elif opts["Verbose"]:
            print(msg)

    tasks, skipped_files = themis_collect_tasks(file_prefix, tint, destination_dir, opts, log)

    log("============ Task summary before download ============")
    log(f"To download : {len(tasks)}")
    log(f"Skipped     : {len(skipped_files)}")
    log("=====================================================")

    ok_files, fail_files = execute_downloads(tasks, opts, log_func=log, overall_progress_func=progress_func)

    log("============ THEMIS download summary ============")
    log(f"OK      : {len(ok_files)}")
    log(f"Skipped : {len(skipped_files)}")
    log(f"Failed  : {len(fail_files)}")
    if fail_files:
        log("--- Failed list (up to 20) ---")
        for item in fail_files[:20]:
            log(item)
    log("=================================================")

    return ok_files, skipped_files, fail_files


# =========================
# Helpers
# =========================

def set_default_opts(opts):
    return {
        "TimeoutSec": opts.get("TimeoutSec", 60),
        "MaxRetry": opts.get("MaxRetry", 3),
        "BackoffSec": opts.get("BackoffSec", 1.0),
        "DownloadPrev": opts.get("DownloadPrev", True),
        "Verbose": opts.get("Verbose", True),
        "Debug": opts.get("Debug", False),
        "MaxWorkers": opts.get("MaxWorkers", 6),
        "ChunkSize": opts.get("ChunkSize", 1024 * 1024),
        "SourceSite": str(opts.get("SourceSite", "SPDF")).upper(),
    }


def normalize_tint(tint):
    t0, t1 = tint

    if isinstance(t0, (int, float)) and isinstance(t1, (int, float)):
        return (
            datetime.fromtimestamp(t0, tz=timezone.utc),
            datetime.fromtimestamp(t1, tz=timezone.utc),
        )

    if isinstance(t0, datetime) and isinstance(t1, datetime):
        if t0.tzinfo is None:
            t0 = t0.replace(tzinfo=timezone.utc)
        else:
            t0 = t0.astimezone(timezone.utc)

        if t1.tzinfo is None:
            t1 = t1.replace(tzinfo=timezone.utc)
        else:
            t1 = t1.astimezone(timezone.utc)

        return t0, t1

    raise TypeError("tint must be (datetime, datetime) or (unix_sec, unix_sec)")


def ensure_trailing_slash(s):
    return s if s.endswith("/") else s + "/"


def read_page(session, url, timeout):
    r = session.get(url, timeout=timeout)
    r.raise_for_status()
    return r.text


def extract_cdf_hrefs_bs4(html_content, debug=False):
    soup = BeautifulSoup(html_content, "html.parser")
    hrefs = []
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if ".cdf" in href.lower():
            hrefs.append(href)
    return unique_stable(hrefs)


def unique_stable(seq):
    seen = set()
    out = []
    for x in seq:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def href_basename(href):
    return href.rstrip("/").split("/")[-1]


def extract_timestamp_from_mms_filename(fname):
    m14 = re.search(r"(?<!\d)(\d{14})(?!\d)", fname)
    if m14:
        s = m14.group(1)
        try:
            dt = datetime.strptime(s, "%Y%m%d%H%M%S").replace(tzinfo=timezone.utc)
            return dt, "datetime14"
        except ValueError:
            pass

    m8 = re.search(r"(?<!\d)(\d{8})(?!\d)", fname)
    if m8:
        s = m8.group(1)
        try:
            dt = datetime.strptime(s, "%Y%m%d").replace(tzinfo=timezone.utc)
            return dt, "date8"
        except ValueError:
            pass

    return None, None


def parse_file_prefixes(text: str):
    text = text.replace("；", ";").replace("，", ",")
    text = text.replace(",", ";").replace("\n", ";")
    prefixes = []
    for item in text.split(";"):
        prefix = item.strip()
        if not prefix:
            continue
        if "mms?" in prefix.lower():
            prefixes.extend(expand_mms_wildcard(prefix))
        else:
            prefixes.append(prefix)
    return prefixes


def expand_mms_wildcard(prefix: str):
    return [re.sub(r"mms\?", f"mms{i}", prefix, flags=re.IGNORECASE) for i in range(1, 5)]


def parse_themis_prefixes(text: str):
    text = text.replace("；", ";").replace("，", ",")
    text = text.replace(",", ";").replace("\n", ";")
    prefixes = []
    for item in text.split(";"):
        prefix = item.strip()
        if not prefix:
            continue
        if re.search(r"th\?", prefix, flags=re.IGNORECASE):
            prefixes.extend(expand_themis_wildcard(prefix))
        else:
            prefixes.append(prefix)
    return prefixes


def expand_themis_wildcard(prefix: str):
    probes = ["a", "b", "c", "d", "e"]
    return [re.sub(r"th\?", f"th{p}", prefix, flags=re.IGNORECASE) for p in probes]


def build_url_from_href(base_url_used, href):
    if href.startswith("http://") or href.startswith("https://"):
        return href
    return urljoin(base_url_used, href)


def download_one_file(file_url, local_path, opts,
                      stop_event=None, pause_event=None,
                      progress_callback=None, on_start=None):
    local_path = Path(local_path)
    timeout = opts["TimeoutSec"]
    max_retry = opts["MaxRetry"]
    backoff_sec = opts["BackoffSec"]
    chunk_size = opts["ChunkSize"]

    session = requests.Session()
    session.headers.update({"User-Agent": "Mozilla/5.0 (Python MMS downloader worker)"})

    last_msg = ""
    started = False
    tmp_path = local_path.with_suffix(local_path.suffix + ".part")

    for r in range(max_retry):
        if stop_event and stop_event.is_set():
            return local_path, False, "Stopped", file_url

        try:
            with session.get(file_url, stream=True, timeout=timeout) as resp:
                resp.raise_for_status()
                total_size = int(resp.headers.get("content-length", 0))
                done_bytes = 0

                if not started:
                    started = True
                    if on_start:
                        on_start()
                    if progress_callback:
                        progress_callback(0, total_size)

                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=chunk_size):
                        if stop_event and stop_event.is_set():
                            return local_path, False, "Stopped", file_url
                        while pause_event and pause_event.is_set():
                            if stop_event and stop_event.is_set():
                                return local_path, False, "Stopped", file_url
                            time.sleep(0.1)
                        if chunk:
                            f.write(chunk)
                            done_bytes += len(chunk)
                            if progress_callback:
                                progress_callback(done_bytes, total_size)

            tmp_path.replace(local_path)
            if progress_callback:
                final = total_size if total_size > 0 else done_bytes
                progress_callback(final, final)
            return local_path, True, "", file_url

        except Exception as e:
            last_msg = str(e)
            if tmp_path.exists():
                try:
                    tmp_path.unlink()
                except Exception:
                    pass
            if r < max_retry - 1:
                time.sleep(backoff_sec * (2 ** r))

    return local_path, False, last_msg, file_url


# =========================
# Tkinter GUI - Home Tab
# =========================

class HomeTab(ttk.Frame):
    SATELLITES = [
        (
            "MMS",
            "Magnetospheric Multiscale Mission (NASA)\n"
            "Downloads CDF files from SPDF or LASP SDC.\n"
            "Supports survey (srvy) and burst (brst) mode data.",
        ),
        (
            "THEMIS",
            "Time History of Events and Macroscale Interactions during Substorms (NASA)\n"
            "Downloads CDF files from NASA SPDF.\n"
            "Probes: tha / thb / thc / thd / the  (use th? for all five).",
        ),
    ]

    def __init__(self, parent, notebook: ttk.Notebook):
        super().__init__(parent)
        self._notebook = notebook
        self._build_ui()

    def _build_ui(self):
        ttk.Label(self, text="Satellite Data Downloader", font=("Segoe UI", 18, "bold")).pack(pady=(30, 6))
        ttk.Label(self, text="Select a satellite mission below to open its downloader.",
                  font=("Segoe UI", 10), foreground="#555555").pack(pady=(0, 24))

        cards_frame = ttk.Frame(self)
        cards_frame.pack(padx=40, fill="x")

        for tab_label, description in self.SATELLITES:
            self._make_card(cards_frame, tab_label, description)

    def _make_card(self, parent, tab_label: str, description: str):
        card = ttk.LabelFrame(parent, text=tab_label, padding=12)
        card.pack(fill="x", pady=8)
        ttk.Label(card, text=description, justify="left", wraplength=700).pack(side="left", fill="x", expand=True)
        ttk.Button(card, text=f"Open {tab_label}", command=lambda t=tab_label: self._open_tab(t)).pack(side="right", padx=8)

    def _open_tab(self, tab_label: str):
        for idx in range(self._notebook.index("end")):
            if self._notebook.tab(idx, "text") == tab_label:
                self._notebook.select(idx)
                return


# =========================
# Tkinter GUI - MMS Tab
# =========================

class MMSDownloaderTab(ttk.Frame):
    """MMS downloader UI — collects all tasks first, then downloads together."""

    def __init__(self, parent):
        super().__init__(parent)
        self.is_downloading = False
        self._stop_event = threading.Event()
        self._pause_event = threading.Event()
        self._build_ui()

    # ------------------------------------------------------------------
    # UI construction
    # ------------------------------------------------------------------

    def _build_ui(self):
        pad = {"padx": 8, "pady": 6}

        form = ttk.LabelFrame(self, text="Download Parameters")
        form.pack(fill="x", padx=10, pady=10)

        ttk.Label(form, text="Data name / filePrefix(s):").grid(row=0, column=0, sticky="w", **pad)
        self.file_prefix_var = tk.StringVar(value="mms1_fgm_srvy_l2;mms2_fgm_srvy_l2")
        ttk.Entry(form, textvariable=self.file_prefix_var, width=40).grid(row=0, column=1, sticky="we", **pad)

        ttk.Label(form, text="Start time (UTC):").grid(row=1, column=0, sticky="w", **pad)
        self.start_var = tk.StringVar(value="2020-02-01 07:50:00")
        ttk.Entry(form, textvariable=self.start_var, width=25).grid(row=1, column=1, sticky="w", **pad)

        ttk.Label(form, text="End time (UTC):").grid(row=2, column=0, sticky="w", **pad)
        self.end_var = tk.StringVar(value="2020-02-01 08:30:00")
        ttk.Entry(form, textvariable=self.end_var, width=25).grid(row=2, column=1, sticky="w", **pad)

        ttk.Label(form, text="Save folder:").grid(row=3, column=0, sticky="w", **pad)
        self.dest_var = tk.StringVar(value=str(Path.cwd() / "data"))
        ttk.Entry(form, textvariable=self.dest_var, width=60).grid(row=3, column=1, sticky="we", **pad)
        ttk.Button(form, text="Browse...", command=self.choose_folder).grid(row=3, column=2, sticky="w", **pad)

        ttk.Label(form, text="Source site:").grid(row=4, column=0, sticky="w", **pad)
        source_values = [f"{key} - {cfg['label']}" for key, cfg in SOURCE_PRESETS.items()]
        self.source_site_combo = ttk.Combobox(form, values=source_values, state="readonly", width=36)
        self.source_site_combo.grid(row=4, column=1, sticky="w", **pad)
        self.source_site_combo.set("SPDF - NASA SPDF")

        options = ttk.LabelFrame(self, text="Options")
        options.pack(fill="x", padx=10, pady=4)

        self.max_workers_var = tk.IntVar(value=6)
        self.timeout_var = tk.IntVar(value=60)
        self.max_retry_var = tk.IntVar(value=3)
        self.backoff_var = tk.DoubleVar(value=1.0)
        self.download_prev_var = tk.BooleanVar(value=True)
        self.debug_var = tk.BooleanVar(value=False)

        ttk.Label(options, text="Threads:").grid(row=0, column=0, sticky="w", **pad)
        ttk.Spinbox(options, from_=1, to=32, textvariable=self.max_workers_var, width=8).grid(row=0, column=1, sticky="w", **pad)

        ttk.Label(options, text="Timeout (s):").grid(row=0, column=2, sticky="w", **pad)
        ttk.Spinbox(options, from_=5, to=300, textvariable=self.timeout_var, width=8).grid(row=0, column=3, sticky="w", **pad)

        ttk.Label(options, text="Retries:").grid(row=0, column=4, sticky="w", **pad)
        ttk.Spinbox(options, from_=1, to=10, textvariable=self.max_retry_var, width=8).grid(row=0, column=5, sticky="w", **pad)

        ttk.Label(options, text="Backoff (s):").grid(row=0, column=6, sticky="w", **pad)
        ttk.Entry(options, textvariable=self.backoff_var, width=8).grid(row=0, column=7, sticky="w", **pad)

        ttk.Checkbutton(options, text="Download previous file on first hit", variable=self.download_prev_var).grid(row=1, column=0, columnspan=4, sticky="w", **pad)
        ttk.Checkbutton(options, text="Debug logs", variable=self.debug_var).grid(row=1, column=4, columnspan=2, sticky="w", **pad)

        # Action buttons
        actions = ttk.Frame(self)
        actions.pack(fill="x", padx=10, pady=6)

        self.start_btn = ttk.Button(actions, text="Start Download", command=self.start_download)
        self.start_btn.pack(side="left", padx=6)

        self._pause_btn = ttk.Button(actions, text="Pause", command=self._toggle_pause, state="disabled")
        self._pause_btn.pack(side="left", padx=4)

        self._stop_btn = ttk.Button(actions, text="Stop", command=self._stop_download, state="disabled")
        self._stop_btn.pack(side="left", padx=4)

        ttk.Button(actions, text="Clear Log", command=self.clear_log).pack(side="left", padx=6)

        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(actions, textvariable=self.status_var).pack(side="right", padx=6)

        # Overall progress bar
        progress_frame = ttk.LabelFrame(self, text="Overall Progress")
        progress_frame.pack(fill="x", padx=10, pady=4)

        self.progress = ttk.Progressbar(progress_frame, orient="horizontal", mode="determinate")
        self.progress.pack(fill="x", padx=10, pady=10)
        self.progress_label_var = tk.StringVar(value="0 / 0")
        ttk.Label(progress_frame, textvariable=self.progress_label_var).pack(anchor="e", padx=10, pady=(0, 8))

        # Log
        log_frame = ttk.LabelFrame(self, text="Log")
        log_frame.pack(fill="both", expand=True, padx=10, pady=10)

        self.log_text = ScrolledText(log_frame, wrap="word", height=20)
        self.log_text.pack(fill="both", expand=True, padx=8, pady=8)
        self.log_text.configure(font=("Consolas", 10))

        hint = (
            "Time format: YYYY-MM-DD HH:MM:SS  (UTC)\n"
            "Multiple data names are supported. Separate them with ';'.\n"
            "Examples:\n"
            "  mms1_fgm_srvy_l2;mms2_fgm_srvy_l2\n"
            "  mms?_fgm_srvy_l2   -> mms1 to mms4\n"
            "  mms1_fgm_brst_l2;mms2_fgm_brst_l2\n"
            "Folder rule:\n"
            "  - brst -> YYYY/MM/DD\n"
            "  - non-brst (e.g. srvy) -> YYYY/MM\n"
            "Time filtering rule:\n"
            "  - 14-digit timestamps (e.g. brst) are filtered by exact time in filename\n"
            "  - 8-digit dates (e.g. srvy) are treated as whole-day files and checked for overlap\n"
        )
        self.append_log(hint)
        form.columnconfigure(1, weight=1)

    # ------------------------------------------------------------------
    # Control callbacks
    # ------------------------------------------------------------------

    def _toggle_pause(self):
        if self._pause_event.is_set():
            self._pause_event.clear()
            self._pause_btn.configure(text="Pause")
            self.status_var.set("Downloading...")
        else:
            self._pause_event.set()
            self._pause_btn.configure(text="Resume")
            self.status_var.set("Paused")

    def _stop_download(self):
        self._stop_event.set()
        self._pause_event.clear()  # unblock any paused threads so they see the stop
        self._stop_btn.configure(state="disabled")
        self._pause_btn.configure(state="disabled")
        self.status_var.set("Stopping...")

    def choose_folder(self):
        folder = filedialog.askdirectory(title="Choose download folder")
        if folder:
            self.dest_var.set(folder)

    def clear_log(self):
        self.log_text.delete("1.0", tk.END)

    # ------------------------------------------------------------------
    # Log helpers
    # ------------------------------------------------------------------

    def append_log(self, msg: str):
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)

    def thread_safe_log(self, msg: str):
        self.winfo_toplevel().after(0, lambda: self.append_log(msg))

    # Per-file progress line in log (tag-based in-place update)

    def _log_file_start(self, task_id: int, fname: str):
        def _do():
            tag = f"fp_{task_id}"
            bar = render_progress_bar(0)
            line = f"  ⬇ {fname}  {bar}   0%"
            self.log_text.insert(tk.END, line, (tag,))
            self.log_text.insert(tk.END, "\n")
            self.log_text.see(tk.END)
        self.winfo_toplevel().after(0, _do)

    def _log_file_progress(self, task_id: int, fname: str, pct: float, done_bytes: int, total_bytes: int):
        def _do():
            tag = f"fp_{task_id}"
            ranges = self.log_text.tag_ranges(tag)
            if not ranges:
                return
            if pct < 0:
                bar = render_progress_bar(0)
                line = f"  ⬇ {fname}  {bar}  ??%  {format_bytes(done_bytes)}"
            else:
                bar = render_progress_bar(pct)
                line = f"  ⬇ {fname}  {bar}  {pct:3.0f}%  {format_bytes(done_bytes)}/{format_bytes(total_bytes)}"
            self.log_text.delete(ranges[0], ranges[1])
            self.log_text.insert(ranges[0], line, (tag,))
        self.winfo_toplevel().after(0, _do)

    def _log_file_finish(self, task_id: int, fname: str, ok: bool, msg: str):
        def _do():
            tag = f"fp_{task_id}"
            ranges = self.log_text.tag_ranges(tag)
            if not ranges:
                # No progress line was created (task never started); append a new line
                if ok:
                    self.append_log(f"  ✅ {fname}")
                else:
                    self.append_log(f"  ❌ {fname}  |  {msg[:80]}")
                return
            if ok:
                line = f"  ✅ {fname}"
            else:
                line = f"  ❌ {fname}  |  {msg[:80]}"
            self.log_text.delete(ranges[0], ranges[1])
            self.log_text.insert(ranges[0], line)
            try:
                self.log_text.tag_delete(tag)
            except Exception:
                pass
        self.winfo_toplevel().after(0, _do)

    # ------------------------------------------------------------------
    # Overall progress bar
    # ------------------------------------------------------------------

    def update_progress(self, done: int, total: int):
        def _update():
            self.progress["maximum"] = max(total, 1)
            self.progress["value"] = done
            self.progress_label_var.set(f"{done} / {total}")
            if total == 0:
                self.status_var.set("No files to download")
            elif done < total:
                if not self._pause_event.is_set() and not self._stop_event.is_set():
                    self.status_var.set(f"Downloading... {done}/{total}")
            else:
                self.status_var.set("Finished")
        self.winfo_toplevel().after(0, _update)

    # ------------------------------------------------------------------
    # Start / worker
    # ------------------------------------------------------------------

    def parse_time(self, s: str) -> datetime:
        return datetime.strptime(s.strip(), "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)

    def get_selected_source_site(self):
        selected = self.source_site_combo.get().strip()
        if not selected:
            return "SPDF"
        return selected.split(" - ", 1)[0].strip().upper()

    def start_download(self):
        if self.is_downloading:
            messagebox.showinfo("Info", "A download task is already running.")
            return

        try:
            raw_prefix_text = self.file_prefix_var.get().strip()
            prefixes = parse_file_prefixes(raw_prefix_text)
            if not prefixes:
                raise ValueError("At least one data name is required.")

            t0 = self.parse_time(self.start_var.get())
            t1 = self.parse_time(self.end_var.get())
            if t1 < t0:
                raise ValueError("End time must be later than start time.")

            dest = self.dest_var.get().strip()
            if not dest:
                raise ValueError("Save folder cannot be empty.")
            Path(dest).mkdir(parents=True, exist_ok=True)

            opts = {
                "TimeoutSec": int(self.timeout_var.get()),
                "MaxRetry": int(self.max_retry_var.get()),
                "BackoffSec": float(self.backoff_var.get()),
                "DownloadPrev": bool(self.download_prev_var.get()),
                "Verbose": True,
                "Debug": bool(self.debug_var.get()),
                "MaxWorkers": int(self.max_workers_var.get()),
                "SourceSite": self.get_selected_source_site(),
            }
        except Exception as e:
            messagebox.showerror("Input Error", str(e))
            return

        self._stop_event.clear()
        self._pause_event.clear()
        self.is_downloading = True
        self.start_btn.configure(state="disabled")
        self._pause_btn.configure(state="normal", text="Pause")
        self._stop_btn.configure(state="normal")
        self.progress["value"] = 0
        self.progress_label_var.set("0 / 0")
        self.status_var.set("Scanning...")
        self.append_log("\n===== New Task =====")
        self.append_log(f"filePrefixes = {prefixes}")
        self.append_log(f"start UTC    = {t0}")
        self.append_log(f"end UTC      = {t1}")
        self.append_log(f"save dir     = {dest}")
        self.append_log(f"source site  = {describe_source(opts['SourceSite'])}")

        threading.Thread(
            target=self._download_worker,
            args=(prefixes, (t0, t1), dest, opts),
            daemon=True,
        ).start()

    def _download_worker(self, prefixes, tint, dest, opts):
        root = self.winfo_toplevel()
        try:
            all_tasks = []
            all_skipped = []
            total_prefixes = len(prefixes)

            # ── Phase 1: Scan all prefixes ─────────────────────────────
            for idx, prefix in enumerate(prefixes, start=1):
                self.thread_safe_log("")
                self.thread_safe_log(f"===== [{idx}/{total_prefixes}] Scanning: {prefix} =====")

                if self._stop_event.is_set():
                    self.thread_safe_log("⛔ Scan aborted by user.")
                    break

                tasks, skipped = mms_collect_tasks(
                    file_prefix=prefix,
                    tint=tint,
                    destination_dir=dest,
                    opts=opts,
                    log_func=self.thread_safe_log,
                    stop_event=self._stop_event,
                )
                all_tasks.extend(tasks)
                all_skipped.extend(skipped)

            if self._stop_event.is_set():
                self.thread_safe_log("⛔ Task stopped during scan phase.")
                return

            self.thread_safe_log("")
            self.thread_safe_log("============ All prefixes scanned ============")
            self.thread_safe_log(f"Total to download : {len(all_tasks)}")
            self.thread_safe_log(f"Total skipped     : {len(all_skipped)}")
            self.thread_safe_log("=============================================")

            # ── Phase 2: Download all tasks together ───────────────────
            ok_files, fail_files = execute_downloads(
                all_tasks, opts,
                log_func=self.thread_safe_log,
                overall_progress_func=self.update_progress,
                stop_event=self._stop_event,
                pause_event=self._pause_event,
                on_file_start=self._log_file_start,
                on_file_progress=self._log_file_progress,
                on_file_finish=self._log_file_finish,
            )

            stopped = self._stop_event.is_set()
            title = "Stopped" if stopped else "Done"
            summary = (
                f"{'Download stopped early.' if stopped else 'Download finished.'}\n\n"
                f"OK: {len(ok_files)}\n"
                f"Skipped: {len(all_skipped)}\n"
                f"Failed: {len(fail_files)}"
            )
            root.after(0, lambda: messagebox.showinfo(title, summary))

        except Exception as e:
            root.after(0, lambda: messagebox.showerror("Error", str(e)))
        finally:
            def _finish():
                self.is_downloading = False
                self.start_btn.configure(state="normal")
                self._pause_btn.configure(state="disabled", text="Pause")
                self._stop_btn.configure(state="disabled")
                if self._stop_event.is_set():
                    self.status_var.set("Stopped")
                elif self.status_var.get() not in ("Finished", "No files to download"):
                    self.status_var.set("Idle")
            root.after(0, _finish)


# =========================
# Tkinter GUI - THEMIS Tab
# =========================

class THEMISDownloaderTab(ttk.Frame):
    """THEMIS downloader UI — collects all tasks first, then downloads together."""

    def __init__(self, parent):
        super().__init__(parent)
        self.is_downloading = False
        self._stop_event = threading.Event()
        self._pause_event = threading.Event()
        self._build_ui()

    # ------------------------------------------------------------------
    # UI construction
    # ------------------------------------------------------------------

    def _build_ui(self):
        pad = {"padx": 8, "pady": 6}

        form = ttk.LabelFrame(self, text="Download Parameters")
        form.pack(fill="x", padx=10, pady=10)

        ttk.Label(form, text="File prefix(es):").grid(row=0, column=0, sticky="w", **pad)
        self.file_prefix_var = tk.StringVar(value="tha_l2_fgm;thb_l2_fgm")
        ttk.Entry(form, textvariable=self.file_prefix_var, width=40).grid(row=0, column=1, sticky="we", **pad)

        ttk.Label(form, text="Start time (UTC):").grid(row=1, column=0, sticky="w", **pad)
        self.start_var = tk.StringVar(value="2020-02-01 00:00:00")
        ttk.Entry(form, textvariable=self.start_var, width=25).grid(row=1, column=1, sticky="w", **pad)

        ttk.Label(form, text="End time (UTC):").grid(row=2, column=0, sticky="w", **pad)
        self.end_var = tk.StringVar(value="2020-02-01 23:59:59")
        ttk.Entry(form, textvariable=self.end_var, width=25).grid(row=2, column=1, sticky="w", **pad)

        ttk.Label(form, text="Save folder:").grid(row=3, column=0, sticky="w", **pad)
        self.dest_var = tk.StringVar(value=str(Path.cwd() / "data"))
        ttk.Entry(form, textvariable=self.dest_var, width=60).grid(row=3, column=1, sticky="we", **pad)
        ttk.Button(form, text="Browse...", command=self.choose_folder).grid(row=3, column=2, sticky="w", **pad)

        options = ttk.LabelFrame(self, text="Options")
        options.pack(fill="x", padx=10, pady=4)

        self.max_workers_var = tk.IntVar(value=6)
        self.timeout_var = tk.IntVar(value=60)
        self.max_retry_var = tk.IntVar(value=3)
        self.backoff_var = tk.DoubleVar(value=1.0)
        self.debug_var = tk.BooleanVar(value=False)

        ttk.Label(options, text="Threads:").grid(row=0, column=0, sticky="w", **pad)
        ttk.Spinbox(options, from_=1, to=32, textvariable=self.max_workers_var, width=8).grid(row=0, column=1, sticky="w", **pad)

        ttk.Label(options, text="Timeout (s):").grid(row=0, column=2, sticky="w", **pad)
        ttk.Spinbox(options, from_=5, to=300, textvariable=self.timeout_var, width=8).grid(row=0, column=3, sticky="w", **pad)

        ttk.Label(options, text="Retries:").grid(row=0, column=4, sticky="w", **pad)
        ttk.Spinbox(options, from_=1, to=10, textvariable=self.max_retry_var, width=8).grid(row=0, column=5, sticky="w", **pad)

        ttk.Label(options, text="Backoff (s):").grid(row=0, column=6, sticky="w", **pad)
        ttk.Entry(options, textvariable=self.backoff_var, width=8).grid(row=0, column=7, sticky="w", **pad)

        ttk.Checkbutton(options, text="Debug logs", variable=self.debug_var).grid(row=1, column=0, columnspan=4, sticky="w", **pad)

        # Action buttons
        actions = ttk.Frame(self)
        actions.pack(fill="x", padx=10, pady=6)

        self.start_btn = ttk.Button(actions, text="Start Download", command=self.start_download)
        self.start_btn.pack(side="left", padx=6)

        self._pause_btn = ttk.Button(actions, text="Pause", command=self._toggle_pause, state="disabled")
        self._pause_btn.pack(side="left", padx=4)

        self._stop_btn = ttk.Button(actions, text="Stop", command=self._stop_download, state="disabled")
        self._stop_btn.pack(side="left", padx=4)

        ttk.Button(actions, text="Clear Log", command=self.clear_log).pack(side="left", padx=6)

        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(actions, textvariable=self.status_var).pack(side="right", padx=6)

        # Overall progress bar
        progress_frame = ttk.LabelFrame(self, text="Overall Progress")
        progress_frame.pack(fill="x", padx=10, pady=4)

        self.progress = ttk.Progressbar(progress_frame, orient="horizontal", mode="determinate")
        self.progress.pack(fill="x", padx=10, pady=10)
        self.progress_label_var = tk.StringVar(value="0 / 0")
        ttk.Label(progress_frame, textvariable=self.progress_label_var).pack(anchor="e", padx=10, pady=(0, 8))

        # Log
        log_frame = ttk.LabelFrame(self, text="Log")
        log_frame.pack(fill="both", expand=True, padx=10, pady=10)

        self.log_text = ScrolledText(log_frame, wrap="word", height=20)
        self.log_text.pack(fill="both", expand=True, padx=8, pady=8)
        self.log_text.configure(font=("Consolas", 10))

        hint = (
            "Data source: NASA SPDF  https://spdf.gsfc.nasa.gov/pub/data/themis/\n"
            "Time format: YYYY-MM-DD HH:MM:SS  (UTC)\n"
            "Multiple prefixes separated by ';'.\n"
            "Examples:\n"
            "  tha_l2_fgm;thb_l2_fgm\n"
            "  th?_l2_fgm   ->  tha / thb / thc / thd / the\n"
            "  tha_l2_esa_peif\n"
            "Folder structure mirrors SPDF:\n"
            "  {save folder}/{probe}/{level}/{instrument}/{YYYY}/\n"
        )
        self.append_log(hint)
        form.columnconfigure(1, weight=1)

    # ------------------------------------------------------------------
    # Control callbacks
    # ------------------------------------------------------------------

    def _toggle_pause(self):
        if self._pause_event.is_set():
            self._pause_event.clear()
            self._pause_btn.configure(text="Pause")
            self.status_var.set("Downloading...")
        else:
            self._pause_event.set()
            self._pause_btn.configure(text="Resume")
            self.status_var.set("Paused")

    def _stop_download(self):
        self._stop_event.set()
        self._pause_event.clear()
        self._stop_btn.configure(state="disabled")
        self._pause_btn.configure(state="disabled")
        self.status_var.set("Stopping...")

    def choose_folder(self):
        folder = filedialog.askdirectory(title="Choose download folder")
        if folder:
            self.dest_var.set(folder)

    def clear_log(self):
        self.log_text.delete("1.0", tk.END)

    # ------------------------------------------------------------------
    # Log helpers
    # ------------------------------------------------------------------

    def append_log(self, msg: str):
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)

    def thread_safe_log(self, msg: str):
        self.winfo_toplevel().after(0, lambda: self.append_log(msg))

    def _log_file_start(self, task_id: int, fname: str):
        def _do():
            tag = f"fp_{task_id}"
            bar = render_progress_bar(0)
            line = f"  ⬇ {fname}  {bar}   0%"
            self.log_text.insert(tk.END, line, (tag,))
            self.log_text.insert(tk.END, "\n")
            self.log_text.see(tk.END)
        self.winfo_toplevel().after(0, _do)

    def _log_file_progress(self, task_id: int, fname: str, pct: float, done_bytes: int, total_bytes: int):
        def _do():
            tag = f"fp_{task_id}"
            ranges = self.log_text.tag_ranges(tag)
            if not ranges:
                return
            if pct < 0:
                bar = render_progress_bar(0)
                line = f"  ⬇ {fname}  {bar}  ??%  {format_bytes(done_bytes)}"
            else:
                bar = render_progress_bar(pct)
                line = f"  ⬇ {fname}  {bar}  {pct:3.0f}%  {format_bytes(done_bytes)}/{format_bytes(total_bytes)}"
            self.log_text.delete(ranges[0], ranges[1])
            self.log_text.insert(ranges[0], line, (tag,))
        self.winfo_toplevel().after(0, _do)

    def _log_file_finish(self, task_id: int, fname: str, ok: bool, msg: str):
        def _do():
            tag = f"fp_{task_id}"
            ranges = self.log_text.tag_ranges(tag)
            if not ranges:
                if ok:
                    self.append_log(f"  ✅ {fname}")
                else:
                    self.append_log(f"  ❌ {fname}  |  {msg[:80]}")
                return
            line = f"  ✅ {fname}" if ok else f"  ❌ {fname}  |  {msg[:80]}"
            self.log_text.delete(ranges[0], ranges[1])
            self.log_text.insert(ranges[0], line)
            try:
                self.log_text.tag_delete(tag)
            except Exception:
                pass
        self.winfo_toplevel().after(0, _do)

    # ------------------------------------------------------------------
    # Overall progress bar
    # ------------------------------------------------------------------

    def update_progress(self, done: int, total: int):
        def _update():
            self.progress["maximum"] = max(total, 1)
            self.progress["value"] = done
            self.progress_label_var.set(f"{done} / {total}")
            if total == 0:
                self.status_var.set("No files to download")
            elif done < total:
                if not self._pause_event.is_set() and not self._stop_event.is_set():
                    self.status_var.set(f"Downloading... {done}/{total}")
            else:
                self.status_var.set("Finished")
        self.winfo_toplevel().after(0, _update)

    # ------------------------------------------------------------------
    # Start / worker
    # ------------------------------------------------------------------

    def parse_time(self, s: str) -> datetime:
        return datetime.strptime(s.strip(), "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)

    def start_download(self):
        if self.is_downloading:
            messagebox.showinfo("Info", "A download task is already running.")
            return

        try:
            raw_prefix_text = self.file_prefix_var.get().strip()
            prefixes = parse_themis_prefixes(raw_prefix_text)
            if not prefixes:
                raise ValueError("At least one file prefix is required.")

            t0 = self.parse_time(self.start_var.get())
            t1 = self.parse_time(self.end_var.get())
            if t1 < t0:
                raise ValueError("End time must be later than start time.")

            dest = self.dest_var.get().strip()
            if not dest:
                raise ValueError("Save folder cannot be empty.")
            Path(dest).mkdir(parents=True, exist_ok=True)

            opts = {
                "TimeoutSec": int(self.timeout_var.get()),
                "MaxRetry": int(self.max_retry_var.get()),
                "BackoffSec": float(self.backoff_var.get()),
                "DownloadPrev": False,
                "Verbose": True,
                "Debug": bool(self.debug_var.get()),
                "MaxWorkers": int(self.max_workers_var.get()),
            }
        except Exception as e:
            messagebox.showerror("Input Error", str(e))
            return

        self._stop_event.clear()
        self._pause_event.clear()
        self.is_downloading = True
        self.start_btn.configure(state="disabled")
        self._pause_btn.configure(state="normal", text="Pause")
        self._stop_btn.configure(state="normal")
        self.progress["value"] = 0
        self.progress_label_var.set("0 / 0")
        self.status_var.set("Scanning...")
        self.append_log("\n===== New Task =====")
        self.append_log(f"filePrefixes = {prefixes}")
        self.append_log(f"start UTC    = {t0}")
        self.append_log(f"end UTC      = {t1}")
        self.append_log(f"save dir     = {dest}")
        self.append_log(f"source       = NASA SPDF ({THEMIS_ROOT_URL})")

        threading.Thread(
            target=self._download_worker,
            args=(prefixes, (t0, t1), dest, opts),
            daemon=True,
        ).start()

    def _download_worker(self, prefixes, tint, dest, opts):
        root = self.winfo_toplevel()
        try:
            all_tasks = []
            all_skipped = []
            total_prefixes = len(prefixes)

            # ── Phase 1: Scan all prefixes ─────────────────────────────
            for idx, prefix in enumerate(prefixes, start=1):
                self.thread_safe_log("")
                self.thread_safe_log(f"===== [{idx}/{total_prefixes}] Scanning: {prefix} =====")

                if self._stop_event.is_set():
                    self.thread_safe_log("⛔ Scan aborted by user.")
                    break

                tasks, skipped = themis_collect_tasks(
                    file_prefix=prefix,
                    tint=tint,
                    destination_dir=dest,
                    opts=opts,
                    log_func=self.thread_safe_log,
                    stop_event=self._stop_event,
                )
                all_tasks.extend(tasks)
                all_skipped.extend(skipped)

            if self._stop_event.is_set():
                self.thread_safe_log("⛔ Task stopped during scan phase.")
                return

            self.thread_safe_log("")
            self.thread_safe_log("============ All prefixes scanned ============")
            self.thread_safe_log(f"Total to download : {len(all_tasks)}")
            self.thread_safe_log(f"Total skipped     : {len(all_skipped)}")
            self.thread_safe_log("=============================================")

            # ── Phase 2: Download all tasks together ───────────────────
            ok_files, fail_files = execute_downloads(
                all_tasks, opts,
                log_func=self.thread_safe_log,
                overall_progress_func=self.update_progress,
                stop_event=self._stop_event,
                pause_event=self._pause_event,
                on_file_start=self._log_file_start,
                on_file_progress=self._log_file_progress,
                on_file_finish=self._log_file_finish,
            )

            stopped = self._stop_event.is_set()
            title = "Stopped" if stopped else "Done"
            summary = (
                f"{'Download stopped early.' if stopped else 'Download finished.'}\n\n"
                f"OK: {len(ok_files)}\n"
                f"Skipped: {len(all_skipped)}\n"
                f"Failed: {len(fail_files)}"
            )
            root.after(0, lambda: messagebox.showinfo(title, summary))

        except Exception as e:
            root.after(0, lambda: messagebox.showerror("Error", str(e)))
        finally:
            def _finish():
                self.is_downloading = False
                self.start_btn.configure(state="normal")
                self._pause_btn.configure(state="disabled", text="Pause")
                self._stop_btn.configure(state="disabled")
                if self._stop_event.is_set():
                    self.status_var.set("Stopped")
                elif self.status_var.get() not in ("Finished", "No files to download"):
                    self.status_var.set("Idle")
            root.after(0, _finish)


# =========================
# Tkinter GUI - Main App
# =========================

SATELLITE_TABS = [
    ("MMS", MMSDownloaderTab),
    ("THEMIS", THEMISDownloaderTab),
]


class MainApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Satellite Data Downloader")
        self.root.geometry("1000x800")

        notebook = ttk.Notebook(root)
        notebook.pack(fill="both", expand=True, padx=6, pady=6)

        home_tab = HomeTab(notebook, notebook)
        notebook.add(home_tab, text="Home")

        for label, TabClass in SATELLITE_TABS:
            tab = TabClass(notebook)
            notebook.add(tab, text=label)


def main():
    root = tk.Tk()
    try:
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    MainApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
