$ErrorActionPreference = "Stop"

$venvPython = Join-Path $PSScriptRoot "venv\Scripts\python.exe"
$appPath = Join-Path $PSScriptRoot "app.py"

if (-not (Test-Path $venvPython)) {
  throw "Project venv Python not found at $venvPython"
}

if (-not (Test-Path $appPath)) {
  throw "Streamlit app not found at $appPath"
}

& $venvPython -m streamlit run $appPath --server.headless=true --browser.gatherUsageStats=false
