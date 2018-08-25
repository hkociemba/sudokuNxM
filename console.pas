// ******************************************************************************
// Code to retrieve the output of a console window.
// code taken from:
// http://www.delphipraxis.net/164364-doskonsole-nutzen-und-rueckgabewerte-einlesen.html
// ******************************************************************************
unit console;

interface

uses
  Windows, Messages, SysUtils, Classes, Graphics, Controls, Forms, Dialogs,
  StdCtrls, ExtCtrls;

var
  SATPID: DWord;

function GetConsoleOutput(Command: string; Output, Errors: TStringList)
  : Boolean;

implementation

function GetConsoleOutput(Command: string; Output, Errors: TStringList)
  : Boolean;
var
  Buffer: array [0 .. 255] of Char;
  CreationFlags: DWord;
  NumberOfBytesRead: DWord;
  PipeErrorsRead: THandle;
  PipeErrorsWrite: THandle;
  PipeOutputRead: THandle;
  PipeOutputWrite: THandle;
  ProcessInfo: TProcessInformation;
  SecurityAttr: TSecurityAttributes;
  StartupInfo: TStartupInfo;
  Stream: TMemoryStream;
begin
  // Initialisierung ProcessInfo
  FillChar(ProcessInfo, SizeOf(TProcessInformation), 0);

  // Initialisierung SecurityAttr
  FillChar(SecurityAttr, SizeOf(TSecurityAttributes), 0);
  SecurityAttr.nLength := SizeOf(TSecurityAttributes);
  SecurityAttr.bInheritHandle := True;
  SecurityAttr.lpSecurityDescriptor := nil;

  // Pipes erzeugen
  CreatePipe(PipeOutputRead, PipeOutputWrite, @SecurityAttr, 0);
  CreatePipe(PipeErrorsRead, PipeErrorsWrite, @SecurityAttr, 0);

  // Initialisierung StartupInfo
  FillChar(StartupInfo, SizeOf(TStartupInfo), 0);
  StartupInfo.cb := SizeOf(TStartupInfo);
  StartupInfo.hStdInput := 0;
  StartupInfo.hStdOutput := PipeOutputWrite;
  StartupInfo.hStdError := PipeErrorsWrite;
  StartupInfo.wShowWindow := SW_HIDE;
  StartupInfo.dwFlags := STARTF_USESHOWWINDOW or STARTF_USESTDHANDLES;

  CreationFlags := CREATE_DEFAULT_ERROR_MODE or CREATE_NEW_CONSOLE or
    NORMAL_PRIORITY_CLASS;

  // Folgende Zeile ist nur für Delphi ab 2009 erforderlich:
  UniqueString(Command);

  if CreateProcess(nil, PChar(Command), nil, nil, True, CreationFlags, nil, nil,
    StartupInfo, ProcessInfo) then
  begin
    Result := True;
    SATPID:= ProcessInfo.dwProcessId;
    // Write-Pipes schließen
    CloseHandle(PipeOutputWrite);
    CloseHandle(PipeErrorsWrite);

    // Ausgabe Read-Pipe auslesen
    Stream := TMemoryStream.Create;
    try
      while ReadFile(PipeOutputRead, Buffer, 255, NumberOfBytesRead, nil) do
      begin
        Stream.Write(Buffer, NumberOfBytesRead);
      end;
      Stream.Position := 0;
      Output.LoadFromStream(Stream);
    finally
      Stream.Free;
    end;
    CloseHandle(PipeOutputRead);

    // Fehler Read-Pipe auslesen
    Stream := TMemoryStream.Create;
    try
      while ReadFile(PipeErrorsRead, Buffer, 255, NumberOfBytesRead, nil) do
      begin
        Stream.Write(Buffer, NumberOfBytesRead);
      end;
      Stream.Position := 0;
      Errors.LoadFromStream(Stream);
    finally
      Stream.Free;
    end;
    CloseHandle(PipeErrorsRead);

    WaitForSingleObject(ProcessInfo.hProcess, INFINITE);
    CloseHandle(ProcessInfo.hProcess);
  end
  else
  begin
    Result := False;
    CloseHandle(PipeOutputRead);
    CloseHandle(PipeOutputWrite);
    CloseHandle(PipeErrorsRead);
    CloseHandle(PipeErrorsWrite);
  end;
end;

end.
