@echo off
setlocal

set "VENV_PYTHON=%~dp0venv\Scripts\python.exe"
set "APP_PATH=%~dp0app.py"

if not exist "%VENV_PYTHON%" (
  echo Project venv Python not found at "%VENV_PYTHON%"
  exit /b 1
)

if not exist "%APP_PATH%" (
  echo Streamlit app not found at "%APP_PATH%"
  exit /b 1
)

"%VENV_PYTHON%" -m streamlit run "%APP_PATH%" --server.headless=true --browser.gatherUsageStats=false
