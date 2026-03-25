#ifndef MyAppVersion
  #define MyAppVersion "1.0.0"
#endif

#define MyAppName "SCI Judgment Downloader"
#define MyAppPublisher "SCI Judgment Downloader"
#define MyAppExeName "SCIJudgmentDownloaderUI.exe"
#define MyAppSourceDir "dist\\SCIJudgmentDownloaderUI"
#define VCRedistPath "prereqs\\vc_redist.x64.exe"

[Setup]
AppId={{6D44BDB8-55C0-4D8A-8D78-7C6C4CBF9870}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={autopf}\SCIJudgmentDownloaderUI
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=installer-output
OutputBaseFilename=SCIJudgmentDownloaderUI-Setup-{#MyAppVersion}
Compression=lzma
SolidCompression=yes
ArchitecturesAllowed=x64compatible
ArchitecturesInstallIn64BitMode=x64compatible
PrivilegesRequired=admin
WizardStyle=modern
SetupLogging=yes

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[Tasks]
Name: "desktopicon"; Description: "Create a &desktop shortcut"; GroupDescription: "Additional shortcuts:"; Flags: unchecked

[Files]
Source: "{#MyAppSourceDir}\*"; DestDir: "{app}"; Flags: recursesubdirs createallsubdirs ignoreversion
Source: "{#VCRedistPath}"; DestDir: "{tmp}"; Flags: deleteafterinstall; Check: VCPrereqNeeded

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Run]
Filename: "{tmp}\vc_redist.x64.exe"; Parameters: "/install /quiet /norestart"; Flags: waituntilterminated runhidden; StatusMsg: "Installing Microsoft Visual C++ Runtime..."; Check: VCPrereqNeeded
Filename: "{app}\{#MyAppExeName}"; Description: "Launch {#MyAppName}"; Flags: nowait postinstall skipifsilent

[Code]
function VCPrereqNeeded: Boolean;
var
  Installed: Cardinal;
begin
  Result := True;
  if RegQueryDWordValue(HKLM64, 'SOFTWARE\Microsoft\VisualStudio\14.0\VC\Runtimes\x64', 'Installed', Installed) then
    Result := Installed <> 1;
end;

