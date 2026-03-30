import logging
import json
import os
import platform
import threading
import time
from datetime import date
from importlib.util import find_spec
from pathlib import Path
from queue import Empty, Queue
from typing import Any, Dict, Optional

import requests
import streamlit as st
import streamlit.components.v1 as components

from main import SciJudgmentScraper, build_arg_parser, format_duration

STARTUP_CHECK_CACHE_SECONDS = 30
APP_OUTPUT_FOLDER_NAME = "SCIJudgmentDownloader"
INTERNAL_DATA_DIR_NAME = ".scijudgment_data"
CAPTCHA_MODE_LABELS = {
    "inline": "Solve as prompts appear",
    "solve_all_first": "Solve all CAPTCHAs first (Recommended)",
    "solve_in_batches": "Solve in batches",
}
REPORTABLE_CHECK_LABELS = {
    "pdf": "Check PDF content only (Recommended)",
    "metadata_or_pdf": "Check metadata first, then PDF",
    "metadata": "Check metadata only (Fastest)",
}
DOWNLOAD_MODE_LABELS = {
    "reportable": "Only reportable judgments (Recommended)",
    "all": "All judgments (reportable + non-reportable)",
}
STARTUP_FAILURE_LABELS = {
    "Writable output folder": "Cannot write to output folder",
    "Network/SSL to sci.gov.in": "Cannot reach sci.gov.in",
    "Dependency/runtime summary": "Required components missing",
}


class QueueLogHandler(logging.Handler):
    def __init__(self, event_queue: Queue) -> None:
        super().__init__()
        self.event_queue = event_queue

    def emit(self, record: logging.LogRecord) -> None:
        try:
            self.event_queue.put(
                {
                    "type": "log",
                    "message": self.format(record),
                }
            )
        except Exception:
            pass


class FrontendRunBridge:
    def __init__(self) -> None:
        self.event_queue: Queue = Queue()
        self.answer_event = threading.Event()
        self.answer_lock = threading.Lock()
        self.stop_event = threading.Event()
        self.pending_answer = ""
        self.thread: Optional[threading.Thread] = None
        self.running = False

    def start(self, args) -> None:
        self.stop_event.clear()
        self.running = True
        self.thread = threading.Thread(target=self._run_worker, args=(args,), daemon=True)
        self.thread.start()

    def _run_worker(self, args) -> None:
        root_logger = logging.getLogger()
        log_handler = QueueLogHandler(self.event_queue)
        log_handler.setFormatter(
            logging.Formatter(
                "%(asctime)s | %(levelname)s | %(message)s",
                datefmt="%Y-%m-%d %H:%M:%S",
            )
        )
        root_logger.addHandler(log_handler)
        root_logger.setLevel(getattr(logging, args.log_level.upper(), logging.INFO))

        try:
            scraper = SciJudgmentScraper(
                args,
                captcha_provider=self.captcha_provider,
                progress_callback=self.progress_callback,
                enable_terminal_progress=False,
                stop_event=self.stop_event,
            )
            summary = scraper.run()
            self.event_queue.put({"type": "complete", "summary": summary})
        except KeyboardInterrupt as exc:
            logging.info("Frontend run stopped: %s", exc)
            self.event_queue.put({"type": "stopped", "message": str(exc) or "Stopped by user"})
        except Exception as exc:
            logging.exception("Frontend run failed: %s", exc)
            self.event_queue.put({"type": "error", "message": str(exc)})
        finally:
            self.running = False
            root_logger.removeHandler(log_handler)

    def captcha_provider(self, captcha_path, prompt: str) -> str:
        self.event_queue.put(
            {
                "type": "captcha",
                "path": str(captcha_path),
                "prompt": prompt,
            }
        )
        self.answer_event.clear()
        self.answer_event.wait()
        with self.answer_lock:
            answer = self.pending_answer
            self.pending_answer = ""
        return answer

    def submit_answer(self, answer: str) -> None:
        with self.answer_lock:
            self.pending_answer = answer
        self.answer_event.set()

    def request_stop(self) -> None:
        self.stop_event.set()
        # If worker is waiting for CAPTCHA input, unblock it immediately.
        self.submit_answer("q")

    def progress_callback(self, payload: Dict[str, Any]) -> None:
        self.event_queue.put({"type": "progress", "payload": payload})


def default_output_dir() -> str:
    local_app_data = os.environ.get("LOCALAPPDATA")
    if local_app_data:
        return str(Path(local_app_data) / "SCIJudgmentDownloaderUI" / APP_OUTPUT_FOLDER_NAME)
    return str(Path.home() / "SCIJudgmentDownloaderUI" / APP_OUTPUT_FOLDER_NAME)


def normalize_output_dir(path_str: str) -> str:
    base = Path(path_str).expanduser()
    if base.name.lower() == APP_OUTPUT_FOLDER_NAME.lower():
        return str(base)
    return str(base / APP_OUTPUT_FOLDER_NAME)


def format_duration_whole_seconds(seconds: float) -> str:
    total = max(0, int(seconds))
    hours, rem = divmod(total, 3600)
    minutes, secs = divmod(rem, 60)
    if hours:
        return f"{hours}h {minutes}m {secs}s"
    if minutes:
        return f"{minutes}m {secs}s"
    return f"{secs}s"


def ensure_state() -> None:
    state = st.session_state
    state.setdefault("bridge", None)
    state.setdefault("logs", [])
    state.setdefault(
        "progress",
        {"completed": 0, "total": 0, "downloaded": 0, "skipped": 0, "failed": 0, "phase": "Waiting to start"},
    )
    state.setdefault("captcha", None)
    state.setdefault("summary", None)
    state.setdefault("run_active", False)
    state.setdefault("error_message", "")
    state.setdefault("output_dir", default_output_dir())
    state.setdefault("active_output_dir", default_output_dir())
    state.setdefault("date_mode", "Month")
    state.setdefault("ui_mode", "Simple")
    state.setdefault("ui_mode_toggle", state.get("ui_mode", "Simple") == "Advanced")
    state.setdefault("prev_ui_mode_toggle", state.get("ui_mode_toggle", False))
    state.setdefault("month_year_value", date.today().year)
    state.setdefault("month_number_value", date.today().month)
    state.setdefault("year_value", date.today().year)
    state.setdefault("from_date_value", date.today().replace(day=1))
    state.setdefault("to_date_value", date.today())
    state.setdefault("download_workers", 16)
    state.setdefault("reportable_mode", "reportable")
    state.setdefault("reportable_check", "pdf")
    state.setdefault("keep_run_diagnostics", False)
    state.setdefault("captcha_solve_mode", "solve_all_first")
    state.setdefault("captcha_batch_size", 5)
    if state.get("captcha_solve_mode") not in {"inline", "solve_all_first", "solve_in_batches"}:
        state["captcha_solve_mode"] = "solve_all_first"
    state.setdefault("log_level", "INFO")
    state.setdefault("has_started_run", False)
    state.setdefault("startup_checks", None)
    state.setdefault("startup_checks_at", 0.0)
    state.setdefault("startup_checks_target", "")
    state.setdefault("startup_blocking_error", "")
    state.setdefault("captcha_seq", 0)
    state.setdefault("captcha_progress", {"total": 0, "solved": 0, "remaining": 0})
    state.setdefault("confirm_stop_exit", False)
    state.setdefault("confirm_exit_app", False)
    state.setdefault("stop_notice", False)
    state.setdefault("stopping_run", False)
    state.setdefault("exit_requested", False)
    state.setdefault("run_started_at_monotonic", 0.0)
    state.setdefault("exit_cleanup_count", 0)
    state.setdefault("show_success_banner", False)
    state.setdefault("show_output_folder_fallback", False)
    state.setdefault("phase_dot_count", 0)


def cleanup_partial_downloads(output_dir: str) -> int:
    removed = 0
    try:
        root = Path(output_dir)
        if not root.exists():
            return 0
        for partial in root.rglob("*.pdf.partial"):
            try:
                partial.unlink(missing_ok=True)
                removed += 1
            except Exception:
                pass
    except Exception:
        return removed
    return removed


def build_ui_args() -> Any:
    parser = build_arg_parser()
    args = parser.parse_args([])
    args.human_captcha = True
    args.interactive_captcha = False
    args.allow_admin_ajax = True
    args.output_dir = resolve_run_output_dir()
    st.session_state.active_output_dir = args.output_dir
    args.download_workers = st.session_state.download_workers
    args.reportable_mode = st.session_state.reportable_mode
    args.reportable_check = st.session_state.reportable_check
    args.keep_run_diagnostics = bool(st.session_state.get("keep_run_diagnostics", False))
    args.captcha_solve_mode = str(st.session_state.get("captcha_solve_mode", "solve_all_first"))
    args.captcha_batch_size = int(st.session_state.get("captcha_batch_size", 5))
    args.log_level = st.session_state.log_level

    mode = st.session_state.date_mode
    args.year = None
    args.month = None
    args.from_date = None
    args.to_date = None
    if mode == "Year":
        args.year = int(st.session_state.year_value)
    elif mode == "Month":
        args.month = f"{int(st.session_state.month_year_value)}-{int(st.session_state.month_number_value):02d}"
    else:
        args.from_date = st.session_state.from_date_value.strftime("%Y-%m-%d")
        args.to_date = st.session_state.to_date_value.strftime("%Y-%m-%d")
    return args


def resolve_run_output_dir() -> str:
    chosen = st.session_state.output_dir.strip() or default_output_dir()
    return normalize_output_dir(chosen)


def check_output_folder_writable(path_str: str) -> Dict[str, str]:
    try:
        folder = Path(path_str).resolve()
        folder.mkdir(parents=True, exist_ok=True)
        probe = folder / ".write_test.tmp"
        with probe.open("w", encoding="utf-8") as f:
            f.write("ok")
        probe.unlink(missing_ok=True)
        return {
            "name": "Writable output folder",
            "status": "pass",
            "message": str(folder),
        }
    except Exception as exc:
        return {
            "name": "Writable output folder",
            "status": "fail",
            "message": f"{path_str} ({exc})",
        }


def check_sci_network_ssl() -> Dict[str, str]:
    url = "https://www.sci.gov.in/"
    try:
        response = requests.get(url, timeout=8)
        response.raise_for_status()
        return {
            "name": "Network/SSL to sci.gov.in",
            "status": "pass",
            "message": f"{url} -> {response.status_code}",
        }
    except requests.exceptions.SSLError as exc:
        return {
            "name": "Network/SSL to sci.gov.in",
            "status": "fail",
            "message": f"SSL certificate verification failed ({exc})",
        }
    except Exception as exc:
        return {
            "name": "Network/SSL to sci.gov.in",
            "status": "fail",
            "message": str(exc),
        }


def check_dependencies_and_runtime() -> Dict[str, Any]:
    dependencies = [
        "requests",
        "bs4",
        "pypdf",
        "sqlite3",
        "tkinter",
    ]
    missing = [name for name in dependencies if find_spec(name) is None]
    runtime_notes = [
        f"Python {platform.python_version()} ({platform.architecture()[0]})",
        f"Streamlit {st.__version__}",
    ]
    if missing:
        return {
            "item": {
                "name": "Dependency/runtime summary",
                "status": "fail",
                "message": f"Missing modules: {', '.join(missing)}",
            },
            "notes": runtime_notes,
        }
    return {
        "item": {
            "name": "Dependency/runtime summary",
            "status": "pass",
            "message": "All required modules are available",
        },
        "notes": runtime_notes,
    }


def run_startup_checks(force: bool = False) -> None:
    now = time.monotonic()
    target = resolve_run_output_dir()
    last_target = st.session_state.get("startup_checks_target", "")
    last_at = float(st.session_state.get("startup_checks_at", 0.0))
    if not force and last_target == target and (now - last_at) < STARTUP_CHECK_CACHE_SECONDS:
        return

    output_item = check_output_folder_writable(target)
    network_item = check_sci_network_ssl()
    dep_result = check_dependencies_and_runtime()
    items = [output_item, network_item, dep_result["item"]]

    blocking_failures = [item["name"] for item in items if item["status"] == "fail"]
    st.session_state.startup_checks = {
        "items": items,
        "runtime_notes": dep_result["notes"],
        "blocking_failures": blocking_failures,
    }
    st.session_state.startup_checks_at = now
    st.session_state.startup_checks_target = target
    if blocking_failures:
        st.session_state.startup_blocking_error = "; ".join(blocking_failures)
    else:
        st.session_state.startup_blocking_error = ""


def render_startup_checks() -> None:
    checks = st.session_state.get("startup_checks")
    if not checks:
        return
    if not checks["blocking_failures"]:
        return
    if st.session_state.get("has_started_run", False):
        return

    friendly_failures = [
        STARTUP_FAILURE_LABELS.get(name, name) for name in checks["blocking_failures"]
    ]
    st.error(
        "Please fix the following before starting download:\n\n"
        + "\n".join(f"- {name}" for name in friendly_failures)
    )
    if st.button("Retry checks"):
        run_startup_checks(force=True)
        st.rerun()


def pick_output_folder(initial_dir: str) -> Optional[str]:
    try:
        import tkinter as tk
        from tkinter import filedialog
    except Exception:
        return None

    try:
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        selected = filedialog.askdirectory(
            title="Select output folder",
            initialdir=initial_dir if initial_dir else os.getcwd(),
        )
        root.destroy()
    except Exception:
        return None

    if selected:
        return selected
    return None


def drain_events() -> bool:
    bridge = st.session_state.bridge
    if bridge is None:
        return False
    needs_full_rerun = False

    while True:
        try:
            event = bridge.event_queue.get_nowait()
        except Empty:
            break

        if event["type"] == "log":
            st.session_state.logs.append(event["message"])
            st.session_state.logs = st.session_state.logs[-300:]
        elif event["type"] == "progress":
            payload = event["payload"]
            if payload.get("event") == "progress":
                current = dict(st.session_state.get("progress", {}))
                merged = dict(payload)
                if "phase" not in merged:
                    merged["phase"] = current.get("phase", "")
                st.session_state.progress = merged
            elif payload.get("event") == "phase":
                current = dict(st.session_state.get("progress", {}))
                current["phase"] = str(payload.get("phase", "")).strip() or current.get("phase", "")
                st.session_state.progress = current
            elif payload.get("event") == "summary":
                st.session_state.summary = payload
            elif payload.get("event") == "captcha_progress":
                st.session_state.captcha_progress = {
                    "total": int(payload.get("total", 0)),
                    "solved": int(payload.get("solved", 0)),
                    "remaining": int(payload.get("remaining", 0)),
                }
        elif event["type"] == "captcha":
            st.session_state.captcha_seq = int(st.session_state.get("captcha_seq", 0)) + 1
            st.session_state.captcha = event
        elif event["type"] == "complete":
            st.session_state.summary = {
                "processed": event["summary"].processed,
                "downloaded": event["summary"].downloaded,
                "skipped": event["summary"].skipped,
                "failed": event["summary"].failed,
                "total_elapsed_seconds": event["summary"].total_elapsed_seconds,
                "average_per_processed_seconds": event["summary"].average_per_processed_seconds,
            }
            st.session_state.run_active = False
            st.session_state.stopping_run = False
            st.session_state.captcha = None
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            st.session_state.show_success_banner = event["summary"].failed == 0
            needs_full_rerun = True
        elif event["type"] == "stopped":
            st.session_state.run_active = False
            st.session_state.stopping_run = False
            st.session_state.captcha = None
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            st.session_state.show_success_banner = False
            st.session_state.stop_notice = True
            st.session_state.exit_cleanup_count = cleanup_partial_downloads(
                st.session_state.get("active_output_dir", resolve_run_output_dir())
            )
            needs_full_rerun = True
        elif event["type"] == "error":
            st.session_state.error_message = event["message"]
            st.session_state.run_active = False
            st.session_state.stopping_run = False
            st.session_state.captcha = None
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            st.session_state.show_success_banner = False
            needs_full_rerun = True
    return needs_full_rerun


def render_sidebar() -> None:
    st.sidebar.header("Run Options")
    today = date.today()
    previous_advanced = bool(st.session_state.get("prev_ui_mode_toggle", False))
    st.sidebar.toggle(
        "Advanced mode",
        key="ui_mode_toggle",
        disabled=st.session_state.run_active,
    )
    current_advanced = bool(st.session_state.ui_mode_toggle)
    st.session_state.ui_mode = "Advanced" if current_advanced else "Simple"
    if previous_advanced and not current_advanced:
        # Revert hidden advanced settings back to simple-mode defaults.
        st.session_state.download_workers = 16
        st.session_state.reportable_mode = "reportable"
        st.session_state.reportable_check = "pdf"
        st.session_state.log_level = "INFO"
        st.session_state.keep_run_diagnostics = False
        st.session_state.captcha_solve_mode = "solve_all_first"
        st.session_state.captcha_batch_size = 5
    st.session_state.prev_ui_mode_toggle = current_advanced

    st.sidebar.radio(
        "Date filter",
        ["Month", "Year", "Custom Range"],
        key="date_mode",
        horizontal=True,
        disabled=st.session_state.run_active,
    )
    year_options = list(range(today.year, 1949, -1))
    validation_error = ""
    if st.session_state.date_mode == "Month":
        selected_month_year = int(st.session_state.get("month_year_value", today.year))
        if selected_month_year not in year_options:
            selected_month_year = today.year
        month_col1, month_col2 = st.sidebar.columns(2)
        st.session_state.month_year_value = month_col1.selectbox(
            "Year",
            options=year_options,
            index=year_options.index(selected_month_year),
            disabled=st.session_state.run_active,
        )
        month_labels = [
            "January",
            "February",
            "March",
            "April",
            "May",
            "June",
            "July",
            "August",
            "September",
            "October",
            "November",
            "December",
        ]
        max_month = today.month if st.session_state.month_year_value == today.year else 12
        allowed_month_labels = month_labels[:max_month]
        selected_month_number = int(st.session_state.get("month_number_value", today.month))
        if selected_month_number < 1 or selected_month_number > max_month:
            selected_month_number = max_month
        selected_month_label = month_col2.selectbox(
            "Month",
            options=allowed_month_labels,
            index=selected_month_number - 1,
            disabled=st.session_state.run_active,
        )
        st.session_state.month_number_value = allowed_month_labels.index(selected_month_label) + 1
    elif st.session_state.date_mode == "Year":
        selected_year = int(st.session_state.get("year_value", today.year))
        if selected_year not in year_options:
            selected_year = today.year
        year_col1, _year_col2 = st.sidebar.columns(2)
        st.session_state.year_value = year_col1.selectbox(
            "Year",
            options=year_options,
            index=year_options.index(selected_year),
            disabled=st.session_state.run_active,
        )
    else:
        range_col1, range_col2 = st.sidebar.columns(2)
        st.session_state.from_date_value = range_col1.date_input(
            "From date",
            value=st.session_state.get("from_date_value"),
            min_value=date(1950, 1, 1),
            max_value=today,
            disabled=st.session_state.run_active,
        )
        st.session_state.to_date_value = range_col2.date_input(
            "To date",
            value=st.session_state.get("to_date_value"),
            min_value=st.session_state.from_date_value,
            max_value=today,
            disabled=st.session_state.run_active,
        )
        if st.session_state.from_date_value > st.session_state.to_date_value:
            validation_error = "From date cannot be later than To date."
        elif st.session_state.from_date_value > today or st.session_state.to_date_value > today:
            validation_error = "Future dates are not allowed."

    if st.session_state.date_mode == "Year" and st.session_state.year_value > today.year:
        validation_error = "Future years are not allowed."
    if st.session_state.date_mode == "Month":
        if st.session_state.month_year_value > today.year:
            validation_error = "Future months are not allowed."
        elif (
            st.session_state.month_year_value == today.year
            and st.session_state.month_number_value > today.month
        ):
            validation_error = "Future months are not allowed."

    st.sidebar.caption(f"Output folder: `{st.session_state.get('output_dir', default_output_dir())}`")
    browse_disabled = st.session_state.run_active
    if st.sidebar.button("Browse output folder", disabled=browse_disabled):
        current = st.session_state.get("output_dir", default_output_dir())
        selected = pick_output_folder(current)
        if selected:
            st.session_state.output_dir = selected
            st.session_state.show_output_folder_fallback = False
            st.rerun()
        else:
            st.session_state.show_output_folder_fallback = True
            st.sidebar.info("Could not open folder browser. You can keep this path or use the default folder.")
    if st.session_state.get("show_output_folder_fallback", False):
        if st.sidebar.button("Use default folder", disabled=browse_disabled):
            st.session_state.output_dir = default_output_dir()
            st.session_state.show_output_folder_fallback = False
            st.rerun()
    if st.session_state.ui_mode == "Advanced":
        st.session_state.download_workers = st.sidebar.slider(
            "Parallel download workers",
            min_value=1,
            max_value=20,
            value=int(st.session_state.get("download_workers", 16)),
            disabled=st.session_state.run_active,
        )
        st.session_state.reportable_mode = st.sidebar.selectbox(
            "Download mode",
            ["reportable", "all"],
            index=["reportable", "all"].index(st.session_state.get("reportable_mode", "reportable")),
            format_func=lambda value: DOWNLOAD_MODE_LABELS.get(value, value),
            disabled=st.session_state.run_active,
        )
        st.session_state.reportable_check = st.sidebar.selectbox(
            "Reportable check",
            ["pdf", "metadata_or_pdf", "metadata"],
            index=["pdf", "metadata_or_pdf", "metadata"].index(
                st.session_state.get("reportable_check", "pdf")
            ),
            format_func=lambda value: REPORTABLE_CHECK_LABELS.get(value, value),
            disabled=st.session_state.run_active,
            help=(
                "How to identify reportable judgments. "
                "PDF content is most reliable; metadata-only is fastest but may miss/mislabel some files."
            ),
        )
        st.sidebar.selectbox(
            "CAPTCHA interaction",
            ["solve_all_first", "inline", "solve_in_batches"],
            key="captcha_solve_mode",
            format_func=lambda mode: CAPTCHA_MODE_LABELS.get(mode, mode),
            disabled=st.session_state.run_active,
            help="Choose whether to solve CAPTCHA per chunk, upfront for all chunks, or in batches.",
        )
        if st.session_state.captcha_solve_mode == "solve_in_batches":
            st.sidebar.number_input(
                "CAPTCHA batch size",
                min_value=1,
                max_value=30,
                step=1,
                key="captcha_batch_size",
                disabled=st.session_state.run_active,
            )
        with st.sidebar.expander("Diagnostics", expanded=False):
            st.session_state.log_level = st.selectbox(
                "Log level",
                ["INFO", "DEBUG", "WARNING", "ERROR"],
                index=["INFO", "DEBUG", "WARNING", "ERROR"].index(st.session_state.get("log_level", "INFO")),
                disabled=st.session_state.run_active,
            )
            st.session_state.keep_run_diagnostics = st.toggle(
                "Keep run diagnostics",
                value=bool(st.session_state.get("keep_run_diagnostics", False)),
                disabled=st.session_state.run_active,
                help="When enabled, stores per-run manifest JSON files for troubleshooting.",
            )

    if validation_error:
        st.sidebar.error(validation_error)

    startup_blocked = bool(st.session_state.get("startup_blocking_error")) and not st.session_state.get(
        "has_started_run", False
    )

    if not st.session_state.run_active:
        if st.sidebar.button(
            "Start Download",
            disabled=bool(validation_error) or startup_blocked,
        ):
            bridge = FrontendRunBridge()
            st.session_state.bridge = bridge
            st.session_state.logs = []
            st.session_state.progress = {
                "completed": 0,
                "total": 0,
                "downloaded": 0,
                "skipped": 0,
                "failed": 0,
                "phase": "Solving CAPTCHAs",
            }
            st.session_state.summary = None
            st.session_state.captcha = None
            st.session_state.error_message = ""
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            st.session_state.run_active = True
            st.session_state.run_started_at_monotonic = time.monotonic()
            st.session_state.has_started_run = True
            st.session_state.confirm_stop_exit = False
            st.session_state.stop_notice = False
            st.session_state.stopping_run = False
            st.session_state.exit_cleanup_count = 0
            st.session_state.show_success_banner = False
            bridge.start(build_ui_args())
            st.rerun()
    else:
        if st.session_state.get("stopping_run", False):
            st.sidebar.info("Stopping download...")
        elif not st.session_state.get("confirm_stop_exit", False):
            if st.sidebar.button("Stop Download"):
                st.session_state.confirm_stop_exit = True
                st.rerun()
        else:
            st.sidebar.warning("Are you sure you want to stop the current download?")
            col1, col2 = st.sidebar.columns(2)
            if col1.button("Confirm Stop"):
                bridge = st.session_state.get("bridge")
                if bridge is not None:
                    try:
                        bridge.request_stop()
                    except Exception:
                        pass
                st.session_state.stopping_run = True
                st.session_state.confirm_stop_exit = False
                st.rerun()
            if col2.button("Cancel"):
                st.session_state.confirm_stop_exit = False
                st.rerun()

    if st.session_state.run_active:
        st.sidebar.caption("Stop the current download to enable Exit App.")
    else:
        if not st.session_state.get("confirm_exit_app", False):
            if st.sidebar.button("Exit App"):
                st.session_state.confirm_exit_app = True
                st.rerun()
        else:
            st.sidebar.warning("Are you sure you want to exit the app?")
            col1, col2 = st.sidebar.columns(2)
            if col1.button("Confirm Exit"):
                st.session_state.confirm_exit_app = False
                st.session_state.exit_requested = True
                st.rerun()
            if col2.button("Cancel"):
                st.session_state.confirm_exit_app = False
                st.rerun()


def render_run_setup() -> None:
    with st.container(border=True):
        st.subheader("Run Setup")
        mode = str(st.session_state.get("date_mode", "Month"))
        if mode == "Year":
            selected = f"{int(st.session_state.get('year_value', date.today().year))}"
        elif mode == "Month":
            selected = (
                f"{int(st.session_state.get('month_year_value', date.today().year))}-"
                f"{int(st.session_state.get('month_number_value', date.today().month)):02d}"
            )
        else:
            from_date = st.session_state.get("from_date_value", date.today().replace(day=1))
            to_date = st.session_state.get("to_date_value", date.today())
            selected = f"{from_date.isoformat()} to {to_date.isoformat()}"

        c1, c2, c3 = st.columns(3)
        c1.write(f"Date filter: `{mode}`")
        c2.write(f"Selected range: `{selected}`")
        c3.write(f"Output folder: `{resolve_run_output_dir()}`")


def render_status() -> None:
    progress = st.session_state.progress
    total = int(progress.get("total", 0))
    completed = int(progress.get("completed", 0))
    ratio = (completed / total) if total else 0.0

    summary = st.session_state.summary
    if not summary:
        with st.container(border=True):
            st.subheader("Progress")
            phase = str(progress.get("phase", "")).strip()
            if phase:
                st.session_state.phase_dot_count = (int(st.session_state.get("phase_dot_count", 0)) % 3) + 1
                dot_count = int(st.session_state.phase_dot_count)
                st.caption(f"{phase}{'.' * dot_count}")
            progress_text = (
                f"{completed} / {total} completed"
                if total
                else "Choose date range and click Start Download."
            )
            st.progress(ratio, text=progress_text)

            started_at = float(st.session_state.get("run_started_at_monotonic", 0.0) or 0.0)
            elapsed_seconds = max(0.0, time.monotonic() - started_at) if started_at > 0 else 0.0
            eta_text = "Pending downloads..."
            if total > 0 and completed >= 5 and elapsed_seconds > 0 and completed < total:
                throughput = completed / elapsed_seconds
                if throughput > 0:
                    eta_seconds = max(0.0, (total - completed) / throughput)
                    eta_text = format_duration_whole_seconds(eta_seconds)
                else:
                    eta_text = "Calculating..."
            elif total > 0 and completed >= total:
                eta_text = "0s"
            elif total > 0 and completed > 0:
                eta_text = "Calculating..."

            t1, t2 = st.columns(2)
            t1.write(f"Elapsed time: `{format_duration_whole_seconds(elapsed_seconds)}`")
            t2.write(f"ETA: `{eta_text}`")

            col1, col2, col3, col4 = st.columns(4)
            col1.metric("Downloaded", progress.get("downloaded", 0))
            col2.metric("Skipped", progress.get("skipped", 0))
            col3.metric("Failed", progress.get("failed", 0))
            col4.metric("Queued", max(total - completed, 0))

    if summary:
        with st.container(border=True):
            st.subheader("Results")
            c1, c2, c3 = st.columns(3)
            c1.metric("Downloaded", int(summary.get("downloaded", 0)))
            c2.metric("Skipped", int(summary.get("skipped", 0)))
            c3.metric("Failed", int(summary.get("failed", 0)))
            st.write(
                f"Total time: `{format_duration(float(summary.get('total_elapsed_seconds', 0.0)))}`"
                " | "
                f"Average time per document: `{format_duration(float(summary.get('average_per_processed_seconds', 0.0)))}`"
            )
            st.write(f"Output folder: `{st.session_state.active_output_dir}`")
            if st.button("Open Output Folder"):
                output_dir = Path(st.session_state.active_output_dir)
                try:
                    output_dir.mkdir(parents=True, exist_ok=True)
                    if os.name == "nt" and hasattr(os, "startfile"):
                        os.startfile(str(output_dir))  # type: ignore[attr-defined]
                    else:
                        st.info(f"Open this folder manually: {output_dir}")
                except Exception as exc:
                    st.error(f"Could not open output folder: {exc}")

    if st.session_state.error_message:
        st.error(st.session_state.error_message)


def render_captcha() -> None:
    captcha_progress = st.session_state.get("captcha_progress", {"total": 0, "solved": 0, "remaining": 0})
    total = int(captcha_progress.get("total", 0))
    solved = int(captcha_progress.get("solved", 0))
    remaining = int(captcha_progress.get("remaining", 0))

    challenge = st.session_state.captcha
    solve_mode = str(st.session_state.get("captcha_solve_mode", "solve_all_first"))
    keep_card_while_waiting = (
        challenge is None
        and st.session_state.get("run_active", False)
        and solve_mode == "solve_all_first"
        and total > 0
        and solved < total
    )
    if not challenge and not keep_card_while_waiting:
        return

    with st.container(border=True):
        st.subheader("CAPTCHA")
        if total > 0 and solved < total:
            st.caption(f"Solved {solved}/{total} | Remaining {remaining}")
            ratio = max(0.0, min(1.0, solved / total))
            st.progress(ratio)
        if challenge is None:
            st.info("Loading next CAPTCHA...")
        else:
            st.write("Enter the CAPTCHA result below.")
            st.image(challenge["path"], use_container_width=False)
            captcha_input_key = f"captcha_answer_{int(st.session_state.get('captcha_seq', 0))}"
            with st.form(key=f"captcha_form_{int(st.session_state.get('captcha_seq', 0))}"):
                answer_raw = st.text_input(
                    "CAPTCHA answer",
                    key=captcha_input_key,
                    placeholder="Numbers only",
                )
                st.caption("Press Enter to submit.")
                submitted = st.form_submit_button("Submit CAPTCHA")
            if submitted:
                answer_str = str(answer_raw).strip()
                if not answer_str:
                    st.warning("Please enter the CAPTCHA value.")
                elif not answer_str.isdigit():
                    st.warning("Please enter numbers only.")
                else:
                    st.session_state.bridge.submit_answer(answer_str)
                    st.session_state.captcha = None
                    st.rerun()

            if st.button("Refresh CAPTCHA"):
                st.session_state.bridge.submit_answer("r")
                st.session_state.captcha = None
                st.rerun()

    # Best-effort autofocus for the CAPTCHA field on each new challenge.
    current_captcha_seq = int(st.session_state.get("captcha_seq", 0))
    components.html(
        """
        <script>
          const CAPTCHA_SEQ = %d;
          const docs = [];
          try { if (window.parent && window.parent.document) docs.push(window.parent.document); } catch (e) {}
          try { if (window.top && window.top.document) docs.push(window.top.document); } catch (e) {}
          if (!docs.length) docs.push(document);

          const findCaptchaInput = (doc) => {
            const exact =
              doc.querySelector('input[placeholder="Numbers only"]:not([disabled])') ||
              doc.querySelector('input[aria-label="CAPTCHA answer"]:not([disabled])');
            if (exact) return exact;

            const inputs = Array.from(doc.querySelectorAll('input[type="text"]:not([disabled])'));
            for (const el of inputs) {
              const ph = (el.getAttribute("placeholder") || "").toLowerCase();
              const al = (el.getAttribute("aria-label") || "").toLowerCase();
              if (ph.includes("captcha") || ph.includes("numbers only") || al.includes("captcha")) {
                return el;
              }
            }
            return null;
          };

          const tryFocus = () => {
            for (const doc of docs) {
              const input = findCaptchaInput(doc);
              if (input && input.offsetParent !== null) {
                input.focus();
                input.select();
                return true;
              }
            }
            return false;
          };

          if (tryFocus()) {
            // done
          } else {
            const started = Date.now();
            const timer = setInterval(() => {
              if (tryFocus() || (Date.now() - started > 15000)) {
                clearInterval(timer);
              }
            }, 120);

            // Also observe DOM mutations so focus happens immediately on mount.
            const observers = [];
            for (const doc of docs) {
              try {
                const obs = new MutationObserver(() => {
                  if (tryFocus()) {
                    for (const o of observers) { try { o.disconnect(); } catch (e) {} }
                  }
                });
                obs.observe(doc.body || doc.documentElement, { childList: true, subtree: true });
                observers.push(obs);
              } catch (e) {}
            }
            setTimeout(() => {
              for (const o of observers) { try { o.disconnect(); } catch (e) {} }
            }, 15000);
          }
        </script>
        """
        % current_captcha_seq,
        height=0,
    )


def render_outputs() -> None:
    output_dir = st.session_state.active_output_dir
    st.subheader("Output Files")
    st.write(f"Current output directory: `{output_dir}`")

    import pathlib

    internal_data_dir = pathlib.Path(output_dir) / INTERNAL_DATA_DIR_NAME
    metadata_file = internal_data_dir / "metadata.csv"
    failed_file = internal_data_dir / "failed_downloads.csv"
    decision_file = internal_data_dir / "decision_log.csv"

    col1, col2, col3 = st.columns(3)
    if metadata_file.exists():
        with metadata_file.open("rb") as f:
            col1.download_button("Download metadata.csv", data=f.read(), file_name="metadata.csv")
    if failed_file.exists():
        with failed_file.open("rb") as f:
            col2.download_button("Download failed_downloads.csv", data=f.read(), file_name="failed_downloads.csv")
    if decision_file.exists():
        with decision_file.open("rb") as f:
            col3.download_button("Download decision_log.csv", data=f.read(), file_name="decision_log.csv")


def render_logs() -> None:
    st.subheader("Logs")
    st.text_area("Run log", value="\n".join(st.session_state.logs[-120:]), height=320)


def render_copy_logs_footer() -> None:
    st.markdown("---")
    st.caption("Support")
    logs_text = "\n".join(st.session_state.logs)
    logs_payload = json.dumps(logs_text)
    disabled_attr = "disabled" if not logs_text else ""
    components.html(
        f"""
        <div style="display:flex;align-items:center;gap:10px;">
          <button id="copy-logs-btn" {disabled_attr}
            style="
              background:#111827;
              color:#f9fafb;
              border:1px solid #374151;
              border-radius:8px;
              padding:8px 12px;
              cursor:pointer;
              font-size:14px;">
            Copy logs
          </button>
          <span id="copy-logs-status" style="font-size:13px;color:#9ca3af;"></span>
        </div>
        <script>
          const btn = document.getElementById("copy-logs-btn");
          const status = document.getElementById("copy-logs-status");
          const text = {logs_payload};
          if (btn) {{
            btn.addEventListener("click", async () => {{
              try {{
                await navigator.clipboard.writeText(text);
                status.textContent = "Logs copied to clipboard.";
                status.style.color = "#22c55e";
              }} catch (e) {{
                status.textContent = "Clipboard blocked by browser. Please use logs from Advanced mode.";
                status.style.color = "#f59e0b";
              }}
            }});
          }}
        </script>
        """,
        height=70,
    )


@st.fragment(run_every="1s")
def render_live_sections() -> None:
    if drain_events():
        st.rerun()
    render_captcha()
    render_status()
    if st.session_state.ui_mode == "Advanced":
        render_outputs()
        render_logs()


def main() -> None:
    st.set_page_config(page_title="SCI Judgment Downloader", layout="wide")
    st.markdown(
        """
        <style>
          div.block-container {
            max-width: 1000px;
            padding-top: 2rem;
            padding-bottom: 2rem;
          }
        </style>
        """,
        unsafe_allow_html=True,
    )
    ensure_state()
    if st.session_state.get("exit_requested", False):
        st.title("SCI Judgment Downloader")
        st.success("Application closed. You may close this tab.")
        time.sleep(1.0)
        os._exit(0)
    run_startup_checks(force=False)

    st.title("SCI Judgment Downloader")
    if st.session_state.get("show_success_banner", False):
        st.success("Download finished successfully.")
    if st.session_state.get("stop_notice", False):
        st.info("Download stopped.")
        removed_count = int(st.session_state.get("exit_cleanup_count", 0))
        if removed_count > 0:
            st.caption(f"Cleaned up {removed_count} partial download file(s).")
    render_startup_checks()

    render_sidebar()
    render_run_setup()
    render_live_sections()
    if st.session_state.ui_mode == "Advanced":
        render_copy_logs_footer()


if __name__ == "__main__":
    main()
