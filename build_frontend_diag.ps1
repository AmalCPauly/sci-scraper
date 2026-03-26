$ErrorActionPreference = "Stop"

$appName = "SCIJudgmentDownloaderUI-Diag"
$venvPython = Join-Path $PSScriptRoot "venv\Scripts\python.exe"

if (-not (Test-Path $venvPython)) {
  throw "Project venv Python not found at $venvPython"
}

& $venvPython -m PyInstaller `
  --noconfirm `
  --clean `
  --name $appName `
  --console `
  --debug all `
  --add-data "app.py;." `
  --add-data "main.py;." `
  --hidden-import urllib.robotparser `
  --hidden-import tkinter `
  --hidden-import tkinter.filedialog `
  --collect-all pypdf `
  --collect-all streamlit `
  launch_frontend.py

Write-Host ""
Write-Host "Diagnostic build complete. Executable is in .\\dist\\$appName\\"
Write-Host "Run it from CMD/PowerShell to capture startup errors."
