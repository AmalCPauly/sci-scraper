import os
import sys
import tempfile
import traceback
from pathlib import Path


def resolve_app_path() -> Path:
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "app.py"
    return Path(__file__).resolve().parent / "app.py"


def main() -> int:
    from streamlit import config as st_config
    from streamlit.runtime.credentials import check_credentials
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
    st_config._main_script_path = os.path.abspath(app_path)
    bootstrap.load_config_options(flag_options)
    check_credentials()
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


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception:
        log_path = get_log_dir() / "launcher_error.log"
        error_text = traceback.format_exc()
        try:
            log_path.write_text(error_text, encoding="utf-8")
        except Exception:
            pass
        show_error_dialog(
            "The application failed to start.\n\n"
            f"Details were written to:\n{log_path}"
        )
        raise
