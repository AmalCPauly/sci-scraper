import sys
from pathlib import Path


def resolve_app_path() -> Path:
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "app.py"
    return Path(__file__).resolve().parent / "app.py"


def main() -> int:
    from streamlit.web import cli as stcli

    sys.argv = [
        "streamlit",
        "run",
        str(resolve_app_path()),
        "--server.headless=true",
        "--browser.gatherUsageStats=false",
    ]
    return stcli.main()


if __name__ == "__main__":
    raise SystemExit(main())
