program satsolver;

uses
  Vcl.Forms,
  main in 'main.pas' {Form1},
  console in 'console.pas',
  cnf in 'cnf.pas';

{$R *.res}

begin
  Application.Initialize;
  Application.MainFormOnTaskbar := True;
  Application.CreateForm(TForm1, Form1);
  Application.Run;
end.
