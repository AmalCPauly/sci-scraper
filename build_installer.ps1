$ErrorActionPreference = "Stop"

$appVersion = (Get-Date).ToString("yyyy.MM.dd")
$scriptRoot = $PSScriptRoot
$vcRedistPath = Join-Path $scriptRoot "prereqs\vc_redist.x64.exe"
$issPath = Join-Path $scriptRoot "installer.iss"

if (-not (Test-Path $vcRedistPath)) {
  throw "Missing VC++ redistributable at $vcRedistPath. Download vc_redist.x64.exe from Microsoft and place it in .\prereqs\."
}

if (-not (Test-Path $issPath)) {
  throw "Installer script not found: $issPath"
}

& (Join-Path $scriptRoot "build_frontend.ps1")

$isccCommand = Get-Command iscc.exe -ErrorAction SilentlyContinue
if ($null -eq $isccCommand) {
  $commonPaths = @(
    "${env:ProgramFiles(x86)}\Inno Setup 6\ISCC.exe",
    "${env:ProgramFiles}\Inno Setup 6\ISCC.exe"
  )
  foreach ($candidate in $commonPaths) {
    if (Test-Path $candidate) {
      $isccCommand = @{ Source = $candidate }
      break
    }
  }
}

if ($null -eq $isccCommand) {
  throw "Inno Setup compiler (ISCC.exe) not found. Install Inno Setup 6 and retry."
}

& $isccCommand.Source "/DMyAppVersion=$appVersion" $issPath

Write-Host ""
Write-Host "Installer build complete."
Write-Host "Output folder: .\installer-output\"

