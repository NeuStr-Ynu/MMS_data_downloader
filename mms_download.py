from __future__ import annotations

import re
import time
import threading
from pathlib import Path
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
from bs4 import BeautifulSoup
from tqdm import tqdm

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText


# =========================
# Core downloader
# =========================

def mms_download_v3_bs4_mt(file_prefix, tint, destination_dir, opts=None, log_func=None, progress_func=None):
    """
    MMS downloader with:
    - BeautifulSoup page parsing
    - multithreaded downloads
    - original time filtering logic preserved:
      file timestamp parsed from filename must be inside [t0, t1]
    - strict save path based on actual page level used
    - real href-based file URLs

    Parameters
    ----------
    file_prefix : str
        e.g. 'mms1_fgm_brst_l2'
    tint : tuple
        (start, end), either UTC datetimes or unix timestamps
    destination_dir : str | Path
    opts : dict
    log_func : callable(str) | None
        GUI/logger callback
    progress_func : callable(done:int, total:int) | None
        progress callback
    """
    opts = set_default_opts(opts or {})
    destination_dir = Path(destination_dir)

    def log(msg: str):
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
    ok_files = []
    skipped_files = []
    fail_files = []
    download_prev_pending = opts["DownloadPrev"]
    tasks = []
    seen_local_paths = set()

    session = requests.Session()
    session.headers.update({
        "User-Agent": "Mozilla/5.0 (Python MMS downloader GUI)"
    })

    for dt_day in day_list:
        Y, M, D = dt_day.year, dt_day.month, dt_day.day

        day_url = f"https://spdf.gsfc.nasa.gov/pub/data/mms/{var_dir}/{Y:04d}/{M:02d}/{D:02d}/"
        month_url = f"https://spdf.gsfc.nasa.gov/pub/data/mms/{var_dir}/{Y:04d}/{M:02d}/"

        html_content = ""
        base_url_used = ""
        page_level = "day"

        try:
            html_content = read_page(session, day_url, opts["TimeoutSec"])
            base_url_used = ensure_trailing_slash(day_url)
            page_level = "day"
            log(f"[{dt_day.strftime('%Y-%m-%d')}] Use DAY page: {day_url}")
        except Exception as e_day:
            if opts["Debug"]:
                log(f"[{dt_day.strftime('%Y-%m-%d')}] DAY page failed: {e_day}")

            page_level = "month"
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
            log(f"  href count = {len(hrefs)}")
            log(f"  valid time count = {len(valid_times)}")
            if valid_times:
                log(f"  first file time = {valid_times[0]}")
                log(f"  last  file time = {valid_times[-1]}")
            log(f"  request t0 = {t0}")
            log(f"  request t1 = {t1}")

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

        if page_level == "day":
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
                log(f"  ⏭️ Skip (exists): {local_path}")
                continue

            file_url = build_url_from_href(base_url_used, href)
            tasks.append({"file_url": file_url, "local_path": local_path})
            if opts["Debug"]:
                log(f"  queued: {file_url}")

    log("============ Task summary before download ============")
    log(f"To download : {len(tasks)}")
    log(f"Skipped     : {len(skipped_files)}")
    log("=====================================================")

    total = len(tasks)
    done = 0
    if progress_func:
        progress_func(done, total)

    if tasks:
        with ThreadPoolExecutor(max_workers=opts["MaxWorkers"]) as executor:
            futures = [
                executor.submit(download_one_file, task["file_url"], task["local_path"], opts)
                for task in tasks
            ]

            for future in as_completed(futures):
                local_path, ok, msg, file_url = future.result()
                if ok:
                    ok_files.append(str(local_path))
                    log(f"  ✅ Downloaded: {local_path}")
                else:
                    fail_files.append(f"{file_url} | {msg}")
                    log(f"  ❌ Failed: {file_url} | {msg}")
                done += 1
                if progress_func:
                    progress_func(done, total)

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
    all_links = soup.find_all("a", href=True)

    hrefs = []
    for a in all_links:
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
    """
    Returns
    -------
    (dt, mode)
        mode = 'datetime14' for YYYYMMDDHHMMSS
        mode = 'date8' for YYYYMMDD
        mode = None if not recognized
    """
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
    return [x.strip() for x in text.split(";") if x.strip()]


def build_url_from_href(base_url_used, href):
    if href.startswith("http://") or href.startswith("https://"):
        return href
    return urljoin(base_url_used, href)


def download_one_file(file_url, local_path, opts):
    local_path = Path(local_path)
    timeout = opts["TimeoutSec"]
    max_retry = opts["MaxRetry"]
    backoff_sec = opts["BackoffSec"]
    chunk_size = opts["ChunkSize"]

    session = requests.Session()
    session.headers.update({
        "User-Agent": "Mozilla/5.0 (Python MMS downloader worker)"
    })

    last_msg = ""
    tmp_path = local_path.with_suffix(local_path.suffix + ".part")

    for r in range(max_retry):
        try:
            with session.get(file_url, stream=True, timeout=timeout) as resp:
                resp.raise_for_status()
                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=chunk_size):
                        if chunk:
                            f.write(chunk)

            tmp_path.replace(local_path)
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
# Tkinter GUI
# =========================

class MMSDownloaderGUI:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("MMS Data Downloader")
        self.root.geometry("980x760")

        self.queue_lock = threading.Lock()
        self.is_downloading = False

        self._build_ui()

    def _build_ui(self):
        pad = {"padx": 8, "pady": 6}

        main = ttk.Frame(self.root)
        main.pack(fill="both", expand=True)

        form = ttk.LabelFrame(main, text="Download Parameters")
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

        # Options
        options = ttk.LabelFrame(main, text="Options")
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

        # Buttons
        actions = ttk.Frame(main)
        actions.pack(fill="x", padx=10, pady=6)

        self.start_btn = ttk.Button(actions, text="Start Download", command=self.start_download)
        self.start_btn.pack(side="left", padx=6)

        ttk.Button(actions, text="Clear Log", command=self.clear_log).pack(side="left", padx=6)

        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(actions, textvariable=self.status_var).pack(side="right", padx=6)

        # Progress
        progress_frame = ttk.LabelFrame(main, text="Progress")
        progress_frame.pack(fill="x", padx=10, pady=4)

        self.progress = ttk.Progressbar(progress_frame, orient="horizontal", mode="determinate")
        self.progress.pack(fill="x", padx=10, pady=10)
        self.progress_label_var = tk.StringVar(value="0 / 0")
        ttk.Label(progress_frame, textvariable=self.progress_label_var).pack(anchor="e", padx=10, pady=(0, 8))

        # Log
        log_frame = ttk.LabelFrame(main, text="Log")
        log_frame.pack(fill="both", expand=True, padx=10, pady=10)

        self.log_text = ScrolledText(log_frame, wrap="word", height=26)
        self.log_text.pack(fill="both", expand=True, padx=8, pady=8)
        self.log_text.configure(font=("Consolas", 10))

        # Help hint
        hint = (
            "Time format: YYYY-MM-DD HH:MM:SS  (UTC)\n"
            "Multiple data names are supported. Separate them with ';'.\n"
            "Examples:\n"
            "  mms1_fgm_srvy_l2;mms2_fgm_srvy_l2\n"
            "  mms1_fgm_brst_l2;mms2_fgm_brst_l2\n"
            "Rule used now:\n"
            "  - 14-digit timestamps (e.g. brst) are filtered by exact time in filename\n"
            "  - 8-digit dates (e.g. srvy) are treated as whole-day files and checked for overlap\n"
        )
        self.append_log(hint)

        form.columnconfigure(1, weight=1)

    def choose_folder(self):
        folder = filedialog.askdirectory(title="Choose download folder")
        if folder:
            self.dest_var.set(folder)

    def clear_log(self):
        self.log_text.delete("1.0", tk.END)

    def append_log(self, msg: str):
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)

    def thread_safe_log(self, msg: str):
        self.root.after(0, lambda: self.append_log(msg))

    def update_progress(self, done: int, total: int):
        def _update():
            self.progress["maximum"] = max(total, 1)
            self.progress["value"] = done
            self.progress_label_var.set(f"{done} / {total}")
            if total == 0:
                self.status_var.set("No files to download")
            elif done < total:
                self.status_var.set(f"Downloading... {done}/{total}")
            else:
                self.status_var.set("Finished")
        self.root.after(0, _update)

    def parse_time(self, s: str) -> datetime:
        s = s.strip()
        return datetime.strptime(s, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)

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
            }

        except Exception as e:
            messagebox.showerror("Input Error", str(e))
            return

        self.is_downloading = True
        self.start_btn.configure(state="disabled")
        self.progress["value"] = 0
        self.progress_label_var.set("0 / 0")
        self.status_var.set("Preparing...")
        self.append_log("\n===== New Task =====")
        self.append_log(f"filePrefixes = {prefixes}")
        self.append_log(f"start UTC    = {t0}")
        self.append_log(f"end UTC      = {t1}")
        self.append_log(f"save dir     = {dest}")

        worker = threading.Thread(
            target=self._download_worker,
            args=(prefixes, (t0, t1), dest, opts),
            daemon=True,
        )
        worker.start()

    def _download_worker(self, prefixes, tint, dest, opts):
        try:
            all_ok = []
            all_skipped = []
            all_fail = []

            total_prefixes = len(prefixes)
            self.update_progress(0, total_prefixes)

            for idx, prefix in enumerate(prefixes, start=1):
                self.thread_safe_log("")
                self.thread_safe_log(f"===== [{idx}/{total_prefixes}] Start: {prefix} =====")
                self.root.after(0, lambda i=idx, n=total_prefixes, p=prefix: self.status_var.set(f"Scanning {i}/{n}: {p}"))

                ok, skipped, fail = mms_download_v3_bs4_mt(
                    file_prefix=prefix,
                    tint=tint,
                    destination_dir=dest,
                    opts=opts,
                    log_func=self.thread_safe_log,
                    progress_func=None,
                )

                all_ok.extend(ok)
                all_skipped.extend(skipped)
                all_fail.extend(fail)
                self.update_progress(idx, total_prefixes)

            self.root.after(0, lambda: messagebox.showinfo(
                "Done",
                f"Download finished.\n\nOK: {len(all_ok)}\nSkipped: {len(all_skipped)}\nFailed: {len(all_fail)}"
            ))
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Error", str(e)))
        finally:
            def _finish():
                self.is_downloading = False
                self.start_btn.configure(state="normal")
                if self.status_var.get() != "Finished":
                    self.status_var.set("Idle")
            self.root.after(0, _finish)


def main():
    root = tk.Tk()
    try:
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    app = MMSDownloaderGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
