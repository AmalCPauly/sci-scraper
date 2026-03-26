import os
import sys
import tempfile
import time
import traceback
from datetime import datetime
from pathlib import Path

_STDIO_GUARDS = []


def resolve_app_path() -> Path:
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "app.py"
    return Path(__file__).resolve().parent / "app.py"


def main() -> int:
    from streamlit import config as st_config
    from streamlit.web import bootstrap

    app_path = str(resolve_app_path())
    flag_options = {
        "global.developmentMode": False,
        "server.address": "127.0.0.1",
        "server.port": 8501,
        "server.headless": False,
        "browser.serverAddress": "127.0.0.1",
        "browser.gatherUsageStats": False,
    }

    os.environ["STREAMLIT_GLOBAL_DEVELOPMENT_MODE"] = "false"
    os.environ.setdefault("STREAMLIT_BROWSER_GATHER_USAGE_STATS", "false")
    st_config._main_script_path = os.path.abspath(app_path)
    bootstrap.load_config_options(flag_options)
    bootstrap.run(app_path, False, [], flag_options)
    return 0


def get_runtime_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def get_log_dir() -> Path:
    local_app_data = os.environ.get("LOCALAPPDATA")
    if local_app_data:
        path = Path(local_app_data) / "SCIJudgmentDownloaderUI"
        path.mkdir(parents=True, exist_ok=True)
        return path
    path = Path(tempfile.gettempdir()) / "SCIJudgmentDownloaderUI"
    path.mkdir(parents=True, exist_ok=True)
    return path


def show_error_dialog(message: str) -> None:
    try:
        import ctypes

        ctypes.windll.user32.MessageBoxW(0, message, "SCIJudgmentDownloaderUI Error", 0x10)
    except Exception:
        pass


def append_launcher_log(message: str) -> None:
    log_path = get_log_dir() / "launcher.log"
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    try:
        with log_path.open("a", encoding="utf-8") as f:
            f.write(f"{timestamp} | {message}\n")
    except Exception:
        pass


def ensure_runtime_dirs() -> None:
    # Ensure user-level writable runtime paths exist before Streamlit starts.
    local_app = get_log_dir()
    local_app.mkdir(parents=True, exist_ok=True)
    user_profile = os.environ.get("USERPROFILE")
    if user_profile:
        streamlit_dir = Path(user_profile) / ".streamlit"
        streamlit_dir.mkdir(parents=True, exist_ok=True)


def ensure_stdio_streams() -> None:
    global _STDIO_GUARDS
    for name in ("stdout", "stderr"):
        if getattr(sys, name, None) is None:
            stream = open(os.devnull, "w", encoding="utf-8")
            setattr(sys, name, stream)
            _STDIO_GUARDS.append(stream)


def run_with_retries(max_attempts: int = 3) -> int:
    ensure_stdio_streams()
    ensure_runtime_dirs()
    last_error = None
    for attempt in range(1, max_attempts + 1):
        append_launcher_log(f"startup attempt {attempt}/{max_attempts}")
        try:
            return main()
        except Exception:
            last_error = traceback.format_exc()
            append_launcher_log(last_error)
            if attempt < max_attempts:
                time.sleep(1.0)
    if last_error is None:
        last_error = "Unknown launcher error."
    error_path = get_log_dir() / "launcher_error.log"
    try:
        error_path.write_text(last_error, encoding="utf-8")
    except Exception:
        pass
    show_error_dialog(
        "The application failed to start.\n\n"
        f"Details were written to:\n{error_path}"
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(run_with_retries())
