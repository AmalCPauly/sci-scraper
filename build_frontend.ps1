$ErrorActionPreference = "Stop"

$appName = "SCIJudgmentDownloaderUI"
$venvPython = Join-Path $PSScriptRoot "venv\Scripts\python.exe"

if (-not (Test-Path $venvPython)) {
  throw "Project venv Python not found at $venvPython"
}

& $venvPython -m PyInstaller `
  --noconfirm `
  --clean `
  --name $appName `
  --noconsole `
  --add-data "app.py;." `
  --collect-all streamlit `
  launch_frontend.py

Write-Host ""
Write-Host "Build complete. Executable is in .\\dist\\$appName\\"
