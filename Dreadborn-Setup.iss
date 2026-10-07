; Instalador Inno Setup do Dreadborn v1.4.2
#define MyAppName "Dreadborn"
#define MyAppVersion "1.4.2"
#define MyAppPublisher "Dreadborn"
#define MyAppExeName "Dreadborn.exe"

[Setup]
AppId={{8F3A2B1C-DREAD-BORN-142-000000000001}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={localappdata}\Dreadborn
DefaultGroupName=Dreadborn
DisableProgramGroupPage=yes
PrivilegesRequired=lowest
OutputDir=dist-installer
OutputBaseFilename=Dreadborn-Setup-Inno
Compression=lzma2/max
SolidCompression=yes
WizardStyle=modern
UninstallDisplayName=Dreadborn

[Languages]
Name: "portuguese"; MessagesFile: "compiler:Languages\Portuguese.isl"

[Files]
Source: "dist\Dreadborn.exe"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{group}\Dreadborn"; Filename: "{app}\{#MyAppExeName}"
Name: "{group}\Desinstalar Dreadborn"; Filename: "{uninstallexe}"

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "Executar Dreadborn"; Flags: nowait postinstall skipifsilent
