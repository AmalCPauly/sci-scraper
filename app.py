import logging
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
        self.pending_answer = ""
        self.thread: Optional[threading.Thread] = None
        self.running = False

    def start(self, args) -> None:
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
            )
            summary = scraper.run()
            self.event_queue.put({"type": "complete", "summary": summary})
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

    def progress_callback(self, payload: Dict[str, Any]) -> None:
        self.event_queue.put({"type": "progress", "payload": payload})


def default_output_dir() -> str:
    local_app_data = os.environ.get("LOCALAPPDATA")
    if local_app_data:
        return str(Path(local_app_data) / "SCIJudgmentDownloaderUI" / "downloads")
    return str(Path.home() / "SCIJudgmentDownloaderUI" / "downloads")


def ensure_state() -> None:
    state = st.session_state
    state.setdefault("bridge", None)
    state.setdefault("logs", [])
    state.setdefault("progress", {"completed": 0, "total": 0, "downloaded": 0, "skipped": 0, "failed": 0})
    state.setdefault("captcha", None)
    state.setdefault("summary", None)
    state.setdefault("run_active", False)
    state.setdefault("error_message", "")
    state.setdefault("output_dir", default_output_dir())
    state.setdefault("active_output_dir", default_output_dir())
    state.setdefault("date_mode", "Month")
    state.setdefault("ui_mode", "Simple")
    state.setdefault("ui_mode_toggle", False)
    state.setdefault("month_year_value", date.today().year)
    state.setdefault("month_number_value", date.today().month)
    state.setdefault("year_value", date.today().year)
    state.setdefault("from_date_value", date.today().replace(day=1))
    state.setdefault("to_date_value", date.today())
    state.setdefault("download_workers", 16)
    state.setdefault("reportable_mode", "reportable")
    state.setdefault("reportable_check", "pdf")
    state.setdefault("log_level", "INFO")
    state.setdefault("has_started_run", False)
    state.setdefault("startup_checks", None)
    state.setdefault("startup_checks_at", 0.0)
    state.setdefault("startup_checks_target", "")
    state.setdefault("startup_blocking_error", "")
    state.setdefault("captcha_seq", 0)
    state.setdefault("captcha_progress", {"total": 0, "solved": 0, "remaining": 0})


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
    return str(Path(chosen))


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

    st.error(
        "App setup checks failed. Please fix the issue below before starting download:\n\n"
        + "\n".join(f"- {name}" for name in checks["blocking_failures"])
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
                st.session_state.progress = payload
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
            st.session_state.captcha = None
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            needs_full_rerun = True
        elif event["type"] == "error":
            st.session_state.error_message = event["message"]
            st.session_state.run_active = False
            st.session_state.captcha = None
            st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
            needs_full_rerun = True
    return needs_full_rerun


def render_sidebar() -> None:
    st.sidebar.header("Run Options")
    today = date.today()
    ui_mode_enabled = st.sidebar.toggle(
        "Advanced mode",
        value=st.session_state.get("ui_mode", "Simple") == "Advanced",
        key="ui_mode_toggle",
        disabled=st.session_state.run_active,
    )
    if ui_mode_enabled:
        st.session_state.ui_mode = "Advanced"
    else:
        st.session_state.ui_mode = "Simple"

    st.sidebar.radio(
        "Date filter",
        ["Month", "Year", "Custom Range"],
        key="date_mode",
        disabled=st.session_state.run_active,
    )
    year_options = list(range(today.year, 1949, -1))
    validation_error = ""
    if st.session_state.date_mode == "Month":
        selected_month_year = int(st.session_state.get("month_year_value", today.year))
        if selected_month_year not in year_options:
            selected_month_year = today.year
        st.session_state.month_year_value = st.sidebar.selectbox(
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
        selected_month_label = st.sidebar.selectbox(
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
        st.session_state.year_value = st.sidebar.selectbox(
            "Year",
            options=year_options,
            index=year_options.index(selected_year),
            disabled=st.session_state.run_active,
        )
    else:
        st.session_state.from_date_value = st.sidebar.date_input(
            "From date",
            value=st.session_state.get("from_date_value"),
            max_value=today,
            disabled=st.session_state.run_active,
        )
        st.session_state.to_date_value = st.sidebar.date_input(
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
            st.rerun()
        else:
            st.sidebar.warning(
                f"Folder picker is unavailable on this system. Using default: {default_output_dir()}"
            )
    st.sidebar.caption("Already-downloaded files in this folder will be skipped.")
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
            disabled=st.session_state.run_active,
        )
        st.session_state.reportable_check = st.sidebar.selectbox(
            "Reportable check",
            ["pdf", "metadata_or_pdf", "metadata"],
            index=["pdf", "metadata_or_pdf", "metadata"].index(
                st.session_state.get("reportable_check", "pdf")
            ),
            disabled=st.session_state.run_active,
        )
        st.session_state.log_level = st.sidebar.selectbox(
            "Log level",
            ["INFO", "DEBUG", "WARNING", "ERROR"],
            index=["INFO", "DEBUG", "WARNING", "ERROR"].index(st.session_state.get("log_level", "INFO")),
            disabled=st.session_state.run_active,
        )

    if validation_error:
        st.sidebar.error(validation_error)

    startup_blocked = bool(st.session_state.get("startup_blocking_error")) and not st.session_state.get(
        "has_started_run", False
    )

    if st.sidebar.button(
        "Start Download",
        disabled=st.session_state.run_active or bool(validation_error) or startup_blocked,
    ):
        bridge = FrontendRunBridge()
        st.session_state.bridge = bridge
        st.session_state.logs = []
        st.session_state.progress = {"completed": 0, "total": 0, "downloaded": 0, "skipped": 0, "failed": 0}
        st.session_state.summary = None
        st.session_state.captcha = None
        st.session_state.error_message = ""
        st.session_state.captcha_progress = {"total": 0, "solved": 0, "remaining": 0}
        st.session_state.run_active = True
        st.session_state.has_started_run = True
        bridge.start(build_ui_args())
        st.rerun()

    if st.sidebar.button("Stop and Exit"):
        bridge = st.session_state.get("bridge")
        if bridge is not None:
            try:
                bridge.submit_answer("q")
            except Exception:
                pass
        # Terminate the Streamlit process (and packaged EXE) immediately.
        os._exit(0)


def render_status() -> None:
    progress = st.session_state.progress
    total = int(progress.get("total", 0))
    completed = int(progress.get("completed", 0))
    ratio = (completed / total) if total else 0.0

    st.subheader("Progress")
    st.progress(ratio, text=f"{completed} / {total} completed" if total else "Waiting to start")

    col1, col2, col3, col4 = st.columns(4)
    col1.metric("Downloaded", progress.get("downloaded", 0))
    col2.metric("Skipped", progress.get("skipped", 0))
    col3.metric("Failed", progress.get("failed", 0))
    col4.metric("Queued", max(total - completed, 0))

    summary = st.session_state.summary
    if summary:
        st.subheader("Summary")
        st.write(
            f"Processed `{summary['processed']}`, downloaded `{summary['downloaded']}`, "
            f"skipped `{summary['skipped']}`, failed `{summary['failed']}`."
        )
        st.write(
            f"Total time: `{format_duration(summary['total_elapsed_seconds'])}` | "
            f"Average per processed document: `{format_duration(summary['average_per_processed_seconds'])}`"
        )
        st.write(f"Output folder: `{st.session_state.active_output_dir}`")

    if st.session_state.error_message:
        st.error(st.session_state.error_message)


def render_captcha() -> None:
    captcha_progress = st.session_state.get("captcha_progress", {"total": 0, "solved": 0, "remaining": 0})
    total = int(captcha_progress.get("total", 0))
    solved = int(captcha_progress.get("solved", 0))
    remaining = int(captcha_progress.get("remaining", 0))
    if total > 0 and solved < total:
        st.subheader("CAPTCHA Progress")
        ratio = max(0.0, min(1.0, solved / total))
        st.progress(ratio, text=f"Solved {solved}/{total} | Remaining {remaining}")

    challenge = st.session_state.captcha
    if not challenge:
        return

    st.subheader("CAPTCHA Required")
    st.write(challenge["prompt"])
    st.image(challenge["path"], caption="Solve this CAPTCHA to continue", use_container_width=False)
    captcha_input_key = f"captcha_answer_{int(st.session_state.get('captcha_seq', 0))}"
    with st.form(key=f"captcha_form_{int(st.session_state.get('captcha_seq', 0))}"):
        answer = st.text_input("CAPTCHA answer", key=captcha_input_key)
        submitted = st.form_submit_button("Submit CAPTCHA")
    if submitted:
        st.session_state.bridge.submit_answer(answer)
        st.session_state.captcha = None
        st.rerun()

    # Best-effort autofocus for the CAPTCHA field on each new challenge.
    components.html(
        """
        <script>
          const focusCaptcha = () => {
            const root = window.parent?.document || document;
            const input = root.querySelector('input[aria-label="CAPTCHA answer"]');
            if (input) { input.focus(); input.select(); }
          };
          setTimeout(focusCaptcha, 0);
          setTimeout(focusCaptcha, 150);
        </script>
        """,
        height=0,
    )

    col1, col2 = st.columns(2)
    if col1.button("Refresh CAPTCHA"):
        st.session_state.bridge.submit_answer("r")
        st.session_state.captcha = None
        st.rerun()
    if col2.button("Abort Run"):
        st.session_state.bridge.submit_answer("q")
        st.session_state.captcha = None
        st.session_state.run_active = False
        st.rerun()


def render_outputs() -> None:
    output_dir = st.session_state.active_output_dir
    st.subheader("Output Files")
    st.write(f"Current output directory: `{output_dir}`")

    import pathlib

    metadata_file = pathlib.Path(output_dir) / "metadata.csv"
    failed_file = pathlib.Path(output_dir) / "failed_downloads.csv"

    col1, col2 = st.columns(2)
    if metadata_file.exists():
        with metadata_file.open("rb") as f:
            col1.download_button("Download metadata.csv", data=f.read(), file_name="metadata.csv")
    if failed_file.exists():
        with failed_file.open("rb") as f:
            col2.download_button("Download failed_downloads.csv", data=f.read(), file_name="failed_downloads.csv")


def render_logs() -> None:
    st.subheader("Logs")
    st.text_area("Run log", value="\n".join(st.session_state.logs[-120:]), height=320)


@st.fragment(run_every="1s")
def render_live_sections() -> None:
    if drain_events():
        st.rerun()
    render_captcha()
    render_status()
    render_outputs()
    if st.session_state.ui_mode == "Advanced":
        render_logs()


def main() -> None:
    st.set_page_config(page_title="SCI Judgement Downloader", layout="wide")
    ensure_state()
    run_startup_checks(force=False)

    st.title("SCI Judgement Downloader")
    st.caption("Local frontend for Supreme Court of India judgment downloads.")
    render_startup_checks()

    render_sidebar()
    render_live_sections()


if __name__ == "__main__":
    main()
