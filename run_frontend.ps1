$ErrorActionPreference = "Stop"

$venvPython = Join-Path $PSScriptRoot "venv\Scripts\python.exe"
$appPath = Join-Path $PSScriptRoot "app.py"

if (-not (Test-Path $venvPython)) {
  throw "Project venv Python not found at $venvPython"
}

if (-not (Test-Path $appPath)) {
  throw "Streamlit app not found at $appPath"
}

& $venvPython -m streamlit run $appPath --global.developmentMode=false --server.address=127.0.0.1 --server.port=8501 --server.headless=false --browser.gatherUsageStats=false
