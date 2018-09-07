unit main;

{$Define BIG}

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants,
  System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.StdCtrls, Vcl.Samples.Spin,
  Vcl.Menus, Vcl.ExtCtrls;

const

{$IFDEF BIG}
  N_MAXBOXLENGTH = 21; // Values up to 31 possible
  N_BIG = (N_MAXBOXLENGTH * N_MAXBOXLENGTH) div 64 + 1;
{$ELSE}
  N_MAXBOXLENGTH = 15;
  N_BIG = 4;
{$ENDIF}
  STRICT_POINTCLAIM = false;
  // for pointing/claiming are two elements needed if true;

type
  TForm1 = class(TForm)
    Memo1: TMemo;
    OpenDialog1: TOpenDialog;
    GroupBox1: TGroupBox;
    CheckNakedSingles: TCheckBox;
    CheckHiddenSingles: TCheckBox;
    CheckBlockLineInteraction: TCheckBox;
    CheckNakedTuple: TCheckBox;
    CheckHiddenTuple: TCheckBox;
    Label3: TLabel;
    SpinEditMaxHiddenTuple: TSpinEdit;
    CheckSATSolver: TCheckBox;
    PopupMenu1: TPopupMenu;
    Paste1: TMenuItem;
    GroupBox2: TGroupBox;
    BLoad: TButton;
    SpinEditRow: TSpinEdit;
    Label2: TLabel;
    SpinEditCol: TSpinEdit;
    Label1: TLabel;
    GroupBox3: TGroupBox;
    BSATSolver: TButton;
    CheckVerbose: TCheckBox;
    CheckSudokuX: TCheckBox;
    BCheckSolution: TButton;
    BAddSolution: TButton;
    GroupBox4: TGroupBox;
    BReduceBasic: TButton;
    BStop: TButton;
    CheckSingleStep: TCheckBox;
    CheckBasicFish: TCheckBox;
    Label4: TLabel;
    SpinEditMaxFish: TSpinEdit;
    SpinEditMaxNakedTuple: TSpinEdit;
    Label5: TLabel;
    Splitter2: TSplitter;
    Splitter1: TSplitter;
    GroupBox5: TGroupBox;
    BPrintPuzzle: TButton;
    CheckOutlineBoxes: TCheckBox;
    GroupBox6: TGroupBox;
    CheckCenterLineHor: TCheckBox;
    CheckCenterLineVer: TCheckBox;
    CheckDiagonal: TCheckBox;
    GroupBox7: TGroupBox;
    RadioOneFold: TRadioButton;
    RadioFourFold: TRadioButton;
    RadioTwoFold: TRadioButton;
    GroupBox8: TGroupBox;
    BCreate: TButton;
    BDefault: TButton;
    BPermute: TButton;
    CheckSudokuP: TCheckBox;
    BReduceSAT: TButton;
    BLowClueGrid: TButton;
    procedure BSATSolverClick(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure BLoadClick(Sender: TObject);
    procedure SpinEditColChange(Sender: TObject);
    procedure SpinEditRowChange(Sender: TObject);
    procedure BAddSolutionClick(Sender: TObject);
    procedure SEMaxHiddenTupleChange(Sender: TObject);
    procedure BReduceBasicClick(Sender: TObject);
    procedure BStopClick(Sender: TObject);
    procedure BPrintPuzzleClick(Sender: TObject);
    procedure Paste1Click(Sender: TObject);
    procedure BCheckSolutionClick(Sender: TObject);
    procedure RbSymClick(Sender: TObject);
    procedure CheckCenterLineHorClick(Sender: TObject);
    procedure CheckCenterLineVerClick(Sender: TObject);
    procedure CheckDiagonalClick(Sender: TObject);
    procedure BCreateClick(Sender: TObject);
    procedure BDefaultClick(Sender: TObject);
    procedure BPermuteClick(Sender: TObject);
    procedure BReduceSATClick(Sender: TObject);
    procedure BLowClueGridClick(Sender: TObject);
  private
    nochange: Boolean;
    sym: Integer; // demanded symmetry for puzzle enries
  public
    function PrintCurrentPuzzle: Integer;
  end;

  TSATThread = class(TThread)
    procedure Execute; override;
  end;

  BigInteger = record
    b: array [0 .. N_BIG - 1] of UINT64;
  end;

{$IFDEF BIG}

  ByteArr = array of Word;
{$ELSE}
  ByteArr = array of Byte;
{$ENDIF}
  BigIntArr = array of BigInteger;

var
  Form1: TForm1;
  B_ROW, B_COL, DIM, DIM2, DIM3: Integer;
  // Block size may be different in both directions
  rc_n, rn_c, cn_r, bn_k, pn_k: BigIntArr;

  empty: BigInteger; // Bitmask for empty entry
  // Bitmasks for block-candidates-in-row detection
  rowmask, rowmask2, colmask, colmask2: array of BigInteger;
  n_set, n_cand_del: Integer; // n_cand_del number of deleted candidates
  verbose: Boolean;
  simpleCheck, firstLoad, solFound: Boolean;
  // simpleCheck: determines if after succesfully applying ame
  rc_set: ByteArr; // the numbers set
  info: array [0 .. 50] of Integer;
  solution: TStringList;
  stopComputation, SATKilled, satFailed: Boolean;
  curDefString: String;

  output, errors: TStringList;
  satError: String;
  satThread: TSATThread;

function rcQ(r, c, n: Integer): Boolean;
function bk_to_r(box, index: Integer): Integer;
function bk_to_c(box, index: Integer): Integer;

function custom_split(input: string): TArray<string>;

implementation

uses ShellApi, Math, Clipbrd, console, cnf; // TlHelp32
{$R *.dfm}

procedure printFail;
begin
  Form1.Memo1.Lines.Add('ERROR: could not start SAT-solver!');
end;

procedure TSATThread.Execute;
var
  b: Boolean;
begin
  b := GetConsoleOutput('java.exe -server  -jar org.sat4j.core.jar cnf.txt',
    output, errors);
  // GetConsoleOutput
  // ('C:\"Program Files (x86)\Java\jre1.8.0_171\bin\java.exe" -server  -jar org.sat4j.core.jar cnf.txt',
  // output, errors);

  if not b then
  begin
    satFailed := true;
    satError := ('ERROR: SAT-solver failed. Result is invald!');
  end
  else if errors.Count > 0 then
  begin
    satFailed := true;
    satError := errors[0] + '. Result is invalid!';
  end
  else
    satFailed := false;
  Terminate;
end;

function KillProcess(PID: DWord): Bool;
var
  hProcess: THandle;
begin
  hProcess := OpenProcess(PROCESS_TERMINATE, false, PID);
  Result := TerminateProcess(hProcess, 0);
end;

procedure permuteArray(var a: array of Integer);
// Fisher-Yates shuffle
var
  n, i, j, tmp: Integer;
begin
  n := Length(a);
  for i := n - 1 downto 1 do
  begin
    j := Random(i + 1);
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
  end;
end;

function shrOneBig(a: BigInteger): BigInteger;
var
  m: Integer;
  temp: BigInteger;
begin
  for m := 0 to N_BIG - 1 do
    temp.b[m] := a.b[m];
  Result.b[N_BIG - 1] := temp.b[N_BIG - 1] shr 1;
  for m := 0 to N_BIG - 2 do
    Result.b[m] := temp.b[m] shr 1 or temp.b[m + 1] shl 63;
end;

function NotBig(a: BigInteger): BigInteger;
var
  m: Integer;
begin
  for m := 0 to N_BIG - 1 do
    Result.b[m] := not a.b[m]
end;

function EqualBig(a, c: BigInteger): Boolean;
var
  m: Integer;
begin
  for m := 0 to N_BIG - 1 do
    if a.b[m] <> c.b[m] then
      Exit(false);
  Result := true;
end;

function AndBig(a, c: BigInteger): BigInteger;
var
  m: Integer;
begin
  for m := 0 to N_BIG - 1 do
    Result.b[m] := a.b[m] and c.b[m]
end;

function OrBig(a, c: BigInteger): BigInteger;
var
  m: Integer;
begin
  for m := 0 to N_BIG - 1 do
    Result.b[m] := a.b[m] or c.b[m]
end;

function notZero(n: BigInteger): Boolean;
var
  i: Integer;
begin
  for i := 0 to N_BIG - 1 do
    if n.b[i] <> 0 then
      Exit(true);
  Result := false;
end;

function BigZero: BigInteger;
var
  i: Integer;
begin
  for i := 0 to N_BIG - 1 do
    Result.b[i] := UINT64(0);
end;

function bitCount64(num: UINT64): Integer;
asm
  POPCNT    rax, num
end;

function bitCount(num: BigInteger): Integer;
var
  i, s: Integer;
begin
  s := 0;
  for i := 0 to N_BIG - 1 do
    Inc(s, bitCount64(num.b[i]));
  Result := s
end;

function bitPos_low64(num: UINT64): Integer;
asm
  bsf    rax, num
end;

function bitPos_low(num: BigInteger): Integer;
var
  i: Integer;
begin
  i := 0;
  while num.b[i] = 0 do
    Inc(i);
  Result := bitPos_low64(num.b[i]) + 64 * i;
end;

function bitPos_high64(num: UINT64): Integer;
asm
  bsr    rax, num
end;

function bitPos_high(num: BigInteger): Integer;
var
  i: Integer;
begin
  i := N_BIG - 1;
  while num.b[i] = 0 do
    Dec(i);
  Result := bitPos_high64(num.b[i]) + 64 * i;
end;

procedure init_bitmasks;
var
  i, j, base, offset: Integer;
begin
  empty := BigZero;
  // for i := 0 to N_BIG - 1 do
  // empty.b[i] := 0;
  for i := 0 to DIM - 1 do
  begin
    base := i div 64;
    offset := i mod 64;
    empty.b[base] := empty.b[base] or UINT64(1) shl offset;
  end;

  for i := 0 to N_BIG - 1 do
    rowmask[0].b[i] := 0;
  for i := 0 to B_COL - 1 do
  begin
    base := i div 64;
    offset := i mod 64;
    rowmask[0].b[base] := rowmask[0].b[base] or UINT64(1) shl offset;
  end;

  rowmask2[0] := BigZero;
  for i := 0 to B_COL - 1 do
  begin
    base := i * B_ROW div 64;
    offset := i * B_ROW mod 64;
    rowmask2[0].b[base] := rowmask2[0].b[base] or UINT64(1) shl offset;
  end;

  colmask[0] := BigZero;
  for i := 0 to B_ROW - 1 do
  begin
    base := i div 64;
    offset := i mod 64;
    colmask[0].b[base] := colmask[0].b[base] or UINT64(1) shl offset;
  end;

  colmask2[0] := BigZero;
  for i := 0 to B_ROW - 1 do
  begin
    base := i * B_COL div 64;
    offset := i * B_COL mod 64;
    colmask2[0].b[base] := colmask2[0].b[base] or UINT64(1) shl offset;
  end;

  for i := 1 to B_ROW - 1 do
  begin
    rowmask[i].b[0] := rowmask[i - 1].b[0] shl B_COL;
    for j := 1 to N_BIG - 1 do
    begin
      rowmask[i].b[j] := rowmask[i - 1].b[j] shl B_COL or
        rowmask[i - 1].b[j - 1] shr (64 - B_COL);
    end;
  end;

  for i := 1 to B_ROW - 1 do
  begin
    rowmask2[i].b[0] := rowmask2[i - 1].b[0] shl 1;
    for j := 1 to N_BIG - 1 do
    begin
      rowmask2[i].b[j] := rowmask2[i - 1].b[j] shl 1 or
        rowmask2[i - 1].b[j - 1] shr 63;
    end;
  end;

  for i := 1 to B_COL - 1 do
  begin
    colmask[i].b[0] := colmask[i - 1].b[0] shl B_ROW;
    for j := 1 to N_BIG - 1 do
    begin
      colmask[i].b[j] := colmask[i - 1].b[j] shl B_ROW or
        colmask[i - 1].b[j - 1] shr (64 - B_ROW);
    end;
  end;

  for i := 1 to B_COL - 1 do
  begin
    colmask2[i].b[0] := colmask2[i - 1].b[0] shl 1;
    for j := 1 to N_BIG - 1 do
    begin
      colmask2[i].b[j] := colmask2[i - 1].b[j] shl 1 or
        colmask2[i - 1].b[j - 1] shr 63;
    end;
  end;
end;

// clear number n in numbervector of row r and column c
procedure clear_rc(r, c, n: Integer);
var
  b, base, offset: Integer;
begin
  b := DIM * r + c;
  base := n div 64;
  offset := n mod 64;
  rc_n[b].b[base] := rc_n[b].b[base] and not(UINT64(1) shl offset);
end;

procedure set_rc(r, c, n: Integer);
var
  b, base, offset: Integer;
begin
  b := DIM * r + c;
  base := n div 64;
  offset := n mod 64;
  rc_n[b].b[base] := rc_n[b].b[base] or (UINT64(1) shl offset);
end;

function rcQ(r, c, n: Integer): Boolean;
var
  base, offset: Integer;
begin
  base := n div 64;
  offset := n mod 64;
  if rc_n[DIM * r + c].b[base] and (UINT64(1) shl offset) <> 0 then
    Result := true
  else
    Result := false;
end;

// returns row for cell with index in box
function bk_to_r(box, index: Integer): Integer;
begin
  Result := B_ROW * (box div B_ROW) + index div B_COL
end;

// returns column for cell with index in box
function bk_to_c(box, index: Integer): Integer;
begin
  Result := B_COL * (box mod B_ROW) + index mod B_COL
end;

// returns row for cell with index in pset
function pk_to_r(pset, index: Integer): Integer;
begin
  Result := B_ROW * (index div B_ROW) + pset div B_COL
end;

// returns column for cell with index in pset
function pk_to_c(pset, index: Integer): Integer;
begin
  Result := B_COL * (index mod B_ROW) + pset mod B_COL
end;

// clear column c in columnvector of row r and number n
procedure clear_rn(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * r + n;
  base := c div 64;
  offset := c mod 64;
  rn_c[bse].b[base] := rn_c[bse].b[base] and not(UINT64(1) shl offset);
end;

procedure set_rn(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * r + n;
  base := c div 64;
  offset := c mod 64;
  rn_c[bse].b[base] := rn_c[bse].b[base] or (UINT64(1) shl offset);
end;

// clear row r in rowvector of column c and number n
procedure clear_cn(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * c + n;
  base := r div 64;
  offset := r mod 64;
  cn_r[bse].b[base] := cn_r[bse].b[base] and not(UINT64(1) shl offset);
end;

procedure set_cn(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * c + n;
  base := r div 64;
  offset := r mod 64;
  cn_r[bse].b[base] := cn_r[bse].b[base] or (UINT64(1) shl offset);
end;

// clear blockposition k in blockvector of block b and number n
// b and k are computed from r and c
procedure clear_bn(r, c, n: Integer);
var
  bse, b, k, base, offset: Integer;
begin
  b := B_ROW * (r div B_ROW) + c div B_COL; // block index
  bse := DIM * b + n;
  k := B_COL * (r mod B_ROW) + c mod B_COL; // cell index in block
  base := k div 64;
  offset := k mod 64;
  bn_k[bse].b[base] := bn_k[bse].b[base] and not(UINT64(1) shl offset);
end;

procedure set_bn(r, c, n: Integer);
var
  bse, b, k, base, offset: Integer;
begin
  b := B_ROW * (r div B_ROW) + c div B_COL; // block index
  bse := DIM * b + n;
  k := B_COL * (r mod B_ROW) + c mod B_COL; // cell index in block
  base := k div 64;
  offset := k mod 64;
  bn_k[bse].b[base] := bn_k[bse].b[base] or (UINT64(1) shl offset);
end;

// clear position k in psetvector of pset p  and number n
// b and k are computed from r and c
procedure clear_pn(r, c, n: Integer);
var
  bse, p, k, base, offset: Integer;
begin
  p := B_COL * (r mod B_ROW) + c mod B_COL; // pset index
  bse := DIM * p + n;
  k := B_ROW * (r div B_ROW) + c div B_COL; // cell index in pset
  base := k div 64;
  offset := k mod 64;
  pn_k[bse].b[base] := pn_k[bse].b[base] and not(UINT64(1) shl offset);
end;

procedure set_pn(r, c, n: Integer);
var
  bse, p, k, base, offset: Integer;
begin
  p := B_COL * (r mod B_ROW) + c mod B_COL; // pset index
  bse := DIM * p + n;
  k := B_ROW * (r div B_ROW) + c div B_COL; // cell index in pset
  base := k div 64;
  offset := k mod 64;
  pn_k[bse].b[base] := pn_k[bse].b[base] or (UINT64(1) shl offset);
end;

procedure deleteCandidate(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * r + c;
  base := n div 64;
  offset := n mod 64;
  if rc_n[bse].b[base] <> rc_n[bse].b[base] and not(UINT64(1) shl offset) then
  // not cleared yet
  begin

    Inc(n_cand_del);
    clear_rc(r, c, n);
    clear_rn(r, c, n);
    clear_cn(r, c, n);
    clear_bn(r, c, n);

    if Form1.CheckSudokuP.Checked then
      clear_pn(r, c, n);
  end;
end;

// this procedure is only usefull if you have used isCandidate before
procedure addCandidate(r, c, n: Integer);
var
  bse, base, offset: Integer;
begin
  bse := DIM * r + c;
  base := n div 64;
  offset := n mod 64;
  if rc_n[bse].b[base] <> rc_n[bse].b[base] or (UINT64(1) shl offset) then
  // yet clear
  begin
    Dec(n_cand_del);
    set_rc(r, c, n);
    set_rn(r, c, n);
    set_cn(r, c, n);
    set_bn(r, c, n);

    if Form1.CheckSudokuP.Checked then
      set_pn(r, c, n);
  end;
end;

function isCandidate(r, c, n: Integer): Boolean;
var
  i, b, p: Integer;
begin
  if rc_set[DIM * r + c] <> 0 then // cell ocupied-> no candidates any more
    Exit(false);
  // check if number n is anywhere in column
  for i := 0 to DIM - 1 do
    if rc_set[DIM * i + c] = n + 1 then
      Exit(false);
  // check if number n is anywhere in row
  for i := 0 to DIM - 1 do
    if rc_set[DIM * r + i] = n + 1 then
      Exit(false);
  // check if number n is anywhere in block
  b := B_ROW * (r div B_ROW) + c div B_COL; // block index
  for i := 0 to DIM - 1 do
    if rc_set[DIM * bk_to_r(b, i) + bk_to_c(b, i)] = n + 1 then
      Exit(false);
  if Form1.CheckSudokuP.Checked then
  begin
    p := B_COL * (r mod B_ROW) + c mod B_COL; // pset index;
    for i := 0 to DIM - 1 do
      if rc_set[DIM * pk_to_r(p, i) + pk_to_c(p, i)] = n + 1 then
        Exit(false);
  end;
  Result := true;
end;

procedure setNumber(r, c, n: Integer);
var
  j, b, p: Integer;
begin
  Inc(n_set);
  b := B_ROW * (r div B_ROW) + c div B_COL;
  for j := 0 to DIM - 1 do
  begin
    deleteCandidate(r, c, j);
    deleteCandidate(r, j, n);
    deleteCandidate(j, c, n);
    deleteCandidate(bk_to_r(b, j), bk_to_c(b, j), n);
  end;

  if Form1.CheckSudokuP.Checked then
  begin
    p := B_COL * (r mod B_ROW) + c mod B_COL; // pset index;
    for j := 0 to DIM - 1 do
      deleteCandidate(pk_to_r(p, j), pk_to_c(p, j), n);
  end;

  if Form1.CheckSudokuX.Checked then
  begin
    if r = c then // set on diagonal
      for j := 0 to DIM - 1 do
        deleteCandidate(j, j, n);
    if r = DIM - 1 - c then // set on antidiagonal
      for j := 0 to DIM - 1 do
        deleteCandidate(j, DIM - 1 - j, n);
  end;

  rc_set[DIM * r + c] := n + 1;
end;

procedure deleteNumber(r, c, n: Integer);
var
  j, b, p: Integer;
begin
  Dec(n_set);
  b := B_ROW * (r div B_ROW) + c div B_COL;
  for j := 0 to DIM - 1 do
  begin
    if isCandidate(r, c, j) then
      addCandidate(r, c, j);
    if isCandidate(r, j, n) then
      addCandidate(r, j, n);
    if isCandidate(j, c, n) then
      addCandidate(j, c, n);
    if isCandidate(bk_to_r(b, j), bk_to_c(b, j), n) then
      addCandidate(bk_to_r(b, j), bk_to_c(b, j), n);
  end;

  if Form1.CheckSudokuP.Checked then
  begin
    p := B_COL * (r mod B_ROW) + c mod B_COL; // pset index;
    for j := 0 to DIM - 1 do
      if isCandidate(pk_to_r(p, j), pk_to_c(p, j), n) then
        addCandidate(pk_to_r(p, j), pk_to_c(p, j), n);
  end;

  if Form1.CheckSudokuX.Checked then
  begin
    if r = c then // set on diagonal
      for j := 0 to DIM - 1 do
        if isCandidate(j, j, n) then
          addCandidate(j, j, n);
    if r = DIM - 1 - c then // set on antidiagonal
      for j := 0 to DIM - 1 do
        if isCandidate(j, DIM - 1 - j, n) then
          addCandidate(j, DIM - 1 - j, n);

  end;
end;

function custom_split(input: string): TArray<string>;
var
  delimiterSet: array [0 .. 1] of char;
  // split works with char array, not a single char
begin
  delimiterSet[0] := ' '; // some character
  delimiterSet[1] := '|';
  Result := input.Split(delimiterSet);
end;

// The givens have to be specified in rc_set
procedure initBitArraysFromGivens;
var
  i, r, c: Integer;
begin
  n_set := 0;
  n_cand_del := 0;

  for i := 0 to DIM2 - 1 do
  begin
    rc_n[i] := empty;
    rn_c[i] := empty;
    cn_r[i] := empty;
    bn_k[i] := empty;
    pn_k[i] := empty;
  end;

  for r := 0 to DIM - 1 do
    for c := 0 to DIM - 1 do
      if rc_set[DIM * r + c] > 0 then
      begin
        setNumber(r, c, rc_set[DIM * r + c] - 1);
      end;
end;

// String s contains the givens of the sudoku. Entries have to be separated by
// spaces, an empty entry is given by '0' or '.'
procedure initBitArraysFromString(s: String);
var
  i, r, c, n, idx: Integer;
  data: TArray<string>;
  t: String;
begin

  n_set := 0;
  n_cand_del := 0;

  for i := 0 to DIM2 - 1 do
  begin
    rc_n[i] := empty;
    rn_c[i] := empty;
    cn_r[i] := empty;
    bn_k[i] := empty;
    pn_k[i] := empty;
    rc_set[i] := 0;
  end;

  s := s.ToUpper;
  t := '';
  for i := 1 to Length(s) do
  begin
    if s[i] <> '.' then
      t := t + s[i]
    else
      t := t + ' . '
  end;
  s := t;

  data := custom_split(s);
  n := Length(data);
  idx := 0;
  for i := 0 to n - 1 do
    if data[i] <> '' then
    begin
      data[idx] := data[i];
      Inc(idx);
    end;

  // idx sollte jetzt SZ4 sein
  for i := 0 to DIM2 - 1 do
  begin
    r := i div DIM;
    c := i mod DIM;
    if (data[i] = '.') or (data[i] = '0') then
      continue;
    n := StrToInt(data[i]) - 1;
    setNumber(r, c, n);
  end;
end;

function solutionValid: Boolean;
var
  b, r, c, i: Integer;
  t: array of Integer;
begin
  // for i := 0 to DIM-1 do
  // t[i]:=0;
  for r := 0 to DIM - 1 do
  begin
    SetLength(t, DIM); // zero initialization!
    for c := 0 to DIM - 1 do
    begin
      if rc_set[DIM * r + c] = 0 then
        Exit(false); // not all cells filled
      Inc(t[rc_set[DIM * r + c] - 1]);
    end;
    for i := 0 to DIM - 1 do
      if t[i] <> 1 then
        Exit(false);
    SetLength(t, 0);
  end;
  for c := 0 to DIM - 1 do
  begin
    SetLength(t, DIM);
    for r := 0 to DIM - 1 do
      Inc(t[rc_set[DIM * r + c] - 1]);
    for i := 0 to DIM - 1 do
      if t[i] <> 1 then
        Exit(false);
    SetLength(t, 0);
  end;
  for b := 0 to DIM - 1 do
  begin
    SetLength(t, DIM);
    for i := 0 to DIM - 1 do
    begin
      r := bk_to_r(b, i);
      c := bk_to_c(b, i);
      Inc(t[rc_set[DIM * r + c] - 1]);
    end;
    for i := 0 to DIM - 1 do
      if t[i] <> 1 then
        Exit(false);
    SetLength(t, 0);

    if Form1.CheckSudokuX.Checked then
    begin
      SetLength(t, DIM);
      for r := 0 to DIM - 1 do
        Inc(t[rc_set[DIM * r + r] - 1]);
      for i := 0 to DIM - 1 do
        if t[i] <> 1 then
          Exit(false);
      SetLength(t, 0);
      SetLength(t, DIM);
      for r := 0 to DIM - 1 do
        Inc(t[rc_set[DIM * (DIM - r - 1) + r] - 1]);
      for i := 0 to DIM - 1 do
        if t[i] <> 1 then
          Exit(false);
      SetLength(t, 0);
    end;
  end;

  Result := true;
end;

procedure hidden_single_pset;
var
  i, p, k: Integer;
begin
  for i := 0 to DIM2 - 1 do
    if bitCount(pn_k[i]) = 1 then
    begin
      p := i div DIM; // pset number
      k := bitPos_low(pn_k[i]); // index of cell in block
      if verbose then
        Form1.Memo1.Lines.Add('hidden single in pset ' + IntToStr(p + 1) + ': r'
          + IntToStr(pk_to_r(p, k) + 1) + 'c' + IntToStr(pk_to_c(p, k) + 1) +
          ' = ' + IntToStr(i mod DIM + 1));
      setNumber(pk_to_r(p, k), pk_to_c(p, k), i mod DIM);
      if simpleCheck then
        Exit; // try simpler methods
    end;
end;

procedure hidden_single_block;
var
  i, b, k: Integer;
begin
  for i := 0 to DIM2 - 1 do
    if bitCount(bn_k[i]) = 1 then
    begin
      b := i div DIM; // block number
      k := bitPos_low(bn_k[i]); // index of cell in block
      if verbose then
        Form1.Memo1.Lines.Add('hidden single in box ' + IntToStr(b + 1) + ': r'
          + IntToStr(bk_to_r(b, k) + 1) + 'c' + IntToStr(bk_to_c(b, k) + 1) +
          ' = ' + IntToStr(i mod DIM + 1));
      setNumber(bk_to_r(b, k), bk_to_c(b, k), i mod DIM);
      // if simpleCheck then  //this is unnecessary
      // Exit; // retry from start
    end;
end;

procedure hidden_single_row;
var
  i: Integer;
begin
  for i := 0 to DIM2 - 1 do
    if bitCount(rn_c[i]) = 1 then
    begin
      if verbose then
        Form1.Memo1.Lines.Add('hidden single in row: r' +
          IntToStr(i div DIM + 1) + 'c' + IntToStr(bitPos_low(rn_c[i]) + 1) +
          ' = ' + IntToStr(i mod DIM + 1));
      setNumber(i div DIM, bitPos_low(rn_c[i]), i mod DIM);
      if simpleCheck then
        Exit; // try simpler methods
    end;
end;

procedure hidden_single_col;
var
  i: Integer;
begin
  for i := 0 to DIM2 - 1 do
    if bitCount(cn_r[i]) = 1 then
    begin
      if verbose then
        Form1.Memo1.Lines.Add('hidden single in column ' +
          IntToStr(i div DIM + 1) + ': r' + IntToStr(bitPos_low(cn_r[i]) + 1) +
          'c' + IntToStr(i div DIM + 1) + ' = ' + IntToStr(i mod DIM + 1));
      setNumber(bitPos_low(cn_r[i]), i div DIM, i mod DIM);
      if simpleCheck then
        Exit; // try simpler methods
    end;
end;

procedure naked_single;
var
  i: Integer;
begin
  for i := 0 to DIM2 - 1 do
    if bitCount(rc_n[i]) = 1 then
    begin
      if verbose then
        Form1.Memo1.Lines.Add('Naked single: r' + IntToStr(i div DIM + 1) + 'c'
          + IntToStr(i mod DIM + 1) + ' = ' +
          IntToStr(bitPos_low(rc_n[i]) + 1));
      setNumber(i div DIM, i mod DIM, bitPos_low(rc_n[i]));
      if simpleCheck then
        Exit; // try simpler methods
    end;
end;

procedure hidden_tuple_singlepset(n_tup, pset, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleNumber: Boolean;
begin

  if todo = 0 then // tuple found
  begin
    // delete corresponding values
    // bitmask contains the positions of the tuple elements in the block
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then // i is blockindex of a tuple position
      begin
        new_mask := rc_n[DIM * pk_to_r(pset, i) + pk_to_c(pset, i)];
        // numbers
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains number
          begin
            isTupleNumber := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleNumber := true;
            if not isTupleNumber then
            begin
              s1 := s1 + IntToStr(j + 1) + ',';
              deleteCandidate(pk_to_r(pset, i), pk_to_c(pset, i), j);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          SetLength(s1, Length(s1) - 1); // delete last comma
          s1 := s1 + ' ';
          s := s + 'r' + IntToStr(pk_to_r(pset, i) + 1) + 'c' +
            IntToStr(pk_to_c(pset, i) + 1) + ' <> ' + s1 + ' ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('hidden tuple of size ' + IntToStr(n_tup) +
        ' with numbers ' + st + ' in pset ' + IntToStr(pset + 1) + ': ' + s);
    end;
    Exit;

  end;

  for i := start to DIM - todo do // iterate all numbers
  begin
    if simpleCheck and solFound then
      Exit;

    if not notZero(pn_k[DIM * pset + i]) then
      continue; // number does not appear in block

    new_mask := OrBig(bitmask, pn_k[DIM * pset + i]);

    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      hidden_tuple_singlepset(n_tup, pset, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure hidden_tuple_pset(n_tup: Integer);
var
  p: Integer;
begin
  solFound := false;
  for p := 0 to DIM - 1 do
  begin
    hidden_tuple_singlepset(n_tup, p, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;

procedure hidden_tuple_singleblock(n_tup, block, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleNumber: Boolean;
begin

  if todo = 0 then // tuple found
  begin
    // delete corresponding values
    // bitmask contains the positions of the tuple elements in the block
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then // i is blockindex of a tuple position
      begin
        new_mask := rc_n[DIM * bk_to_r(block, i) + bk_to_c(block, i)];
        // numbers
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains number
          begin
            isTupleNumber := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleNumber := true;
            if not isTupleNumber then
            begin
              s1 := s1 + IntToStr(j + 1) + ',';
              deleteCandidate(bk_to_r(block, i), bk_to_c(block, i), j);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          SetLength(s1, Length(s1) - 1); // delete last comma
          s1 := s1 + ' ';
          s := s + 'r' + IntToStr(bk_to_r(block, i) + 1) + 'c' +
            IntToStr(bk_to_c(block, i) + 1) + ' <> ' + s1 + ' ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('hidden tuple of size ' + IntToStr(n_tup) +
        ' with numbers ' + st + ' in box ' + IntToStr(block + 1) + ': ' + s);
    end;
    Exit;

  end;

  for i := start to DIM - todo do // iterate all numbers
  begin
    if simpleCheck and solFound then
      Exit;

    if not notZero(bn_k[DIM * block + i]) then
      continue; // number does not appear in block

    new_mask := OrBig(bitmask, bn_k[DIM * block + i]);

    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      hidden_tuple_singleblock(n_tup, block, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure hidden_tuple_block(n_tup: Integer);
var
  b: Integer;
begin
  solFound := false;
  for b := 0 to DIM - 1 do
  begin
    hidden_tuple_singleblock(n_tup, b, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;

// *****************************************************************************

procedure hidden_tuple_singlerow(n_tup, row, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleNumber: Boolean;
begin

  if todo = 0 then // tuple found
  begin
    // bitmask contains the positions of the tuple elements in the row
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is columnindex of a tuple position
      begin
        new_mask := rc_n[DIM * row + i];
        // numbers
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains number
          begin
            isTupleNumber := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleNumber := true;
            if not isTupleNumber then
            begin
              s1 := s1 + IntToStr(j + 1) + ',';
              deleteCandidate(row, i, j);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          SetLength(s1, Length(s1) - 1); // delete last comma
          s1 := s1 + ' ';
          s := s + 'r' + IntToStr(row + 1) + 'c' + IntToStr(i + 1) + ' <> '
            + s1 + ' ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('hidden tuple of size ' + IntToStr(n_tup) +
        ' with numbers ' + st + ' in row ' + IntToStr(row + 1) + ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do // iterate all numbers
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(rn_c[DIM * row + i]) then
      continue;
    // number does not appear in row
    new_mask := OrBig(bitmask, rn_c[DIM * row + i]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      hidden_tuple_singlerow(n_tup, row, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure hidden_tuple_row(n_tup: Integer);
var
  r: Integer;
begin
  solFound := false;
  for r := 0 to DIM - 1 do
  begin
    hidden_tuple_singlerow(n_tup, r, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;

procedure hidden_tuple_singlecol(n_tup, col, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleNumber: Boolean;
begin

  if todo = 0 then // tuple found
  begin
    // bitmask contains the positions of the tuple elements in the column
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is rowindex of a tuple position
      begin
        new_mask := rc_n[DIM * i + col]; // numbers
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains number
          begin
            isTupleNumber := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleNumber := true;
            if not isTupleNumber then
            begin
              s1 := s1 + IntToStr(j + 1) + ',';
              deleteCandidate(i, col, j);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          SetLength(s1, Length(s1) - 1); // delete last comma
          s1 := s1 + ' ';
          s := s + 'r' + IntToStr(i + 1) + 'c' + IntToStr(col + 1) + ' <> '
            + s1 + ' ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('hidden tuple of size ' + IntToStr(n_tup) +
        ' with numbers ' + st + ' in column ' + IntToStr(col + 1) + ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do
  // iterate all numbers  ///AUSSTEIGEN, FALLS nur eine Berchnng durchgeführt werden soll!!
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(cn_r[DIM * col + i]) then
      continue;
    // number does not appear in column
    new_mask := OrBig(bitmask, cn_r[DIM * col + i]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      hidden_tuple_singlecol(n_tup, col, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure hidden_tuple_col(n_tup: Integer);
var
  c: Integer;
begin
  solFound := false;
  for c := 0 to DIM - 1 do
  begin
    hidden_tuple_singlecol(n_tup, c, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;

// *****************************************************************************

procedure naked_tuple_singlepset(n_tup, pset, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1, m1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then // tuple found
  begin
    // bitmask contains the numbers of the tuple in the block
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is number of the tuple
      begin
        // new_mask := rc_n[DIM * bk_to_r(block, i) + bk_to_c(block, i)];
        new_mask := pn_k[DIM * pset + i];
        // positionindices of number i in the block
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains position index in block
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(pk_to_r(pset, j) + 1) + 'c' +
                IntToStr(pk_to_c(pset, j) + 1) + ' ';
              deleteCandidate(pk_to_r(pset, j), pk_to_c(pset, j), i);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1 + '<> ' + IntToStr(i + 1) + '  ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('naked tuple of size ' + IntToStr(n_tup) +
        ' at pset positions ' + st + ' in pset ' + IntToStr(pset + 1) +
        ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do // i ist positionindex im Block
  begin
    if simpleCheck and solFound then
      Exit;
    m1 := rc_n[DIM * (pk_to_r(pset, i)) + pk_to_c(pset, i)];
    // m1 gibt die numbers an dieser Position an
    if not notZero(m1) then
      continue; // cell occupied
    new_mask := OrBig(bitmask, m1);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      // positionindex wo die Zahlen sitzen
      naked_tuple_singlepset(n_tup, pset, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure naked_tuple_pset(n_tup: Integer);
var
  p: Integer;
begin
  solFound := false;
  for p := 0 to DIM - 1 do
  begin
    naked_tuple_singlepset(n_tup, p, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;
// *****************************************************************************

procedure naked_tuple_singleblock(n_tup, block, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1, m1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then // tuple found
  begin
    // bitmask contains the numbers of the tuple in the block
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is number of the tuple
      begin
        // new_mask := rc_n[DIM * bk_to_r(block, i) + bk_to_c(block, i)];
        new_mask := bn_k[DIM * block + i];
        // positionindices of number i in the block
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains position index in block
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(bk_to_r(block, j) + 1) + 'c' +
                IntToStr(bk_to_c(block, j) + 1) + ' ';
              deleteCandidate(bk_to_r(block, j), bk_to_c(block, j), i);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1 + '<> ' + IntToStr(i + 1) + '  ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('naked tuple of size ' + IntToStr(n_tup) +
        ' at box positions ' + st + ' in box ' + IntToStr(block + 1) +
        ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do // i ist positionindex im Block
  begin
    if simpleCheck and solFound then
      Exit;
    m1 := rc_n[DIM * (bk_to_r(block, i)) + bk_to_c(block, i)];
    // m1 gibt die numbers an dieser Position an
    if not notZero(m1) then
      continue; // cell occupied
    new_mask := OrBig(bitmask, m1);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      // positionindex wo die Zahlen sitzen
      naked_tuple_singleblock(n_tup, block, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure naked_tuple_block(n_tup: Integer);
var
  b: Integer;
begin
  solFound := false;
  for b := 0 to DIM - 1 do
  begin
    naked_tuple_singleblock(n_tup, b, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;
// *****************************************************************************

procedure naked_tuple_singlerow(n_tup, row, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then
  begin
    // bitmask contains the numbers of the tuple in the row
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is number of the tuple
      begin
        new_mask := rn_c[DIM * row + i];
        // column indices of number i in the row
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains column index in row
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(row + 1) + 'c' + IntToStr(j + 1) + ' ';
              deleteCandidate(row, j, i);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1 + '<> ' + IntToStr(i + 1) + '  ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('naked tuple of size ' + IntToStr(n_tup) +
        ' at column positions ' + st + ' in row ' + IntToStr(row + 1) +
        ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(rc_n[DIM * row + i]) then
      continue; // cell occupied
    new_mask := OrBig(bitmask, rc_n[DIM * row + i]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      naked_tuple_singlerow(n_tup, row, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure naked_tuple_row(n_tup: Integer);
var
  r: Integer;
begin
  solFound := false;
  for r := 0 to DIM - 1 do
  begin
    naked_tuple_singlerow(n_tup, r, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;
// *****************************************************************************

// *****************************************************************************
procedure naked_tuple_singlecol(n_tup, col, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then
  // tuple found, delete corresponding values
  begin
    // bitmask contains the numbers of the tuple in the column
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is number of the tuple
      begin
        new_mask := cn_r[DIM * col + i];
        // row indices of number i in the column
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains row index in column col
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(j + 1) + 'c' + IntToStr(col + 1) + ' ';
              deleteCandidate(j, col, i);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1 + '<> ' + IntToStr(i + 1) + '  ';
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('naked tuple of size ' + IntToStr(n_tup) +
        ' at row positions ' + st + ' in column ' + IntToStr(col + 1) +
        ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(rc_n[DIM * i + col]) then
      continue; // cell occupied
    new_mask := OrBig(bitmask, rc_n[DIM * i + col]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      naked_tuple_singlecol(n_tup, col, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure naked_tuple_col(n_tup: Integer);
var
  c: Integer;
begin
  solFound := false;
  for c := 0 to DIM - 1 do
  begin
    naked_tuple_singlecol(n_tup, c, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;
// ******************************************************************************

procedure basicfish_tuple_single_row(n_tup, num, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then
  // tuple found, delete corresponding values
  begin
    // bitmask contains the columns positions of the number
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is column position of the tuple
      begin
        new_mask := cn_r[DIM * i + num];
        // row indices of number num in the column i
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains row index in column i
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(j + 1) + 'c' + IntToStr(i + 1) + ' ';
              deleteCandidate(j, i, num);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1;
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      s := s + '<> ' + IntToStr(num + 1) + '  ';
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('basic fish of size ' + IntToStr(n_tup) +
        ' with basesets at row positions ' + st + ' and fish digit ' +
        IntToStr(num + 1) + ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do // iterate rows
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(rn_c[DIM * i + num]) then
      continue;
    // number num not in row
    new_mask := OrBig(bitmask, rn_c[DIM * i + num]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      basicfish_tuple_single_row(n_tup, num, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure basicfish_tuple_row(n_tup: Integer);
var
  n: Integer;
begin
  solFound := false;
  for n := 0 to DIM - 1 do
  // iterate all numbers
  begin
    basicfish_tuple_single_row(n_tup, n, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;

procedure basicfish_tuple_single_col(n_tup, num, start, todo: Integer;
  bitmask: BigInteger);
var
  i, j, k: Integer;
  new_mask, bitmask1: BigInteger;
  s, s1, st: String;
  isTupleIndex: Boolean;
begin
  if todo = 0 then
  // tuple found, delete corresponding values
  begin
    // bitmask contains the row positions of the number
    bitmask1 := bitmask;
    s := '';
    i := 0;
    while notZero(bitmask1) do
    begin
      if odd(bitmask1.b[0]) then
      // i is row position of the tuple
      begin
        new_mask := rn_c[DIM * i + num];
        // column indices of number num in the row i
        j := 0;
        s1 := '';
        while notZero(new_mask) do
        begin
          if odd(new_mask.b[0]) then // j contains column index in row i
          begin
            isTupleIndex := false;
            for k := 1 to n_tup do
              if info[k] = j then
                isTupleIndex := true;
            if not isTupleIndex then
            begin
              s1 := s1 + 'r' + IntToStr(i + 1) + 'c' + IntToStr(j + 1) + ' ';
              deleteCandidate(i, j, num);
            end;
          end;
          new_mask := shrOneBig(new_mask);
          Inc(j)
        end;
        if s1 <> '' then
        begin
          s := s + s1;
        end;
      end;
      bitmask1 := shrOneBig(bitmask1);
      Inc(i)
    end;
    if s <> '' then
      solFound := true;
    if verbose and (s <> '') then
    begin
      s := s + '<> ' + IntToStr(num + 1) + '  ';
      st := '';
      for j := n_tup downto 2 do
        st := st + IntToStr(info[j] + 1) + ', ';
      st := st + IntToStr(info[1] + 1);
      Form1.Memo1.Lines.Add('basic fish of size ' + IntToStr(n_tup) +
        ' with basesets at column positions ' + st + ' and fish digit ' +
        IntToStr(num + 1) + ': ' + s);
    end;
    Exit;
  end;

  for i := start to DIM - todo do // iterate columns
  begin
    if simpleCheck and solFound then
      Exit;
    if not notZero(cn_r[DIM * i + num]) then
      continue;
    // number num not in column
    new_mask := OrBig(bitmask, cn_r[DIM * i + num]);
    if bitCount(new_mask) <= n_tup then
    begin
      info[todo] := i;
      basicfish_tuple_single_col(n_tup, num, i + 1, todo - 1, new_mask);
    end;
  end;
end;

procedure basicfish_tuple_col(n_tup: Integer);
var
  n: Integer;
begin
  solFound := false;
  for n := 0 to DIM - 1 do
  // iterate all numbers
  begin
    basicfish_tuple_single_col(n_tup, n, 0, n_tup, BigZero);
    if simpleCheck and solFound then
      Exit;
  end;
end;
// ******************************************************************************

procedure block_candidates_in_row;
var
  b, n, r, i, j, progress: Integer;
  k, colpos: BigInteger;
  s: String;
begin
  for b := 0 to DIM - 1 do
  begin
    progress := n_cand_del;
    for n := 0 to DIM - 1 do
    begin
      k := bn_k[DIM * b + n];
      // blockindices of number n in block b

{$IF STRICT_POINTCLAIM=true}
      if bitCount(k) < 2 then
        continue;
{$IFEND}
      for i := 0 to B_ROW - 1 do // i is relative index of row in block
        if (notZero(k)) and EqualBig(AndBig(k, rowmask[i]), k) then
        begin
          r := B_ROW * (b div B_ROW) + i;
          colpos := AndBig(rn_c[DIM * r + n], NotBig(rowmask[b mod B_ROW]));
          // column positions of deleteable candidates
          j := 0;
          s := '';
          while notZero(colpos) do
          begin
            if odd(colpos.b[0]) then
            begin
              deleteCandidate(r, j, n);
              if verbose then
                s := s + 'c' + IntToStr(j + 1);
            end;
            colpos := shrOneBig(colpos);
            Inc(j)
          end;
          if verbose and (s <> '') then
            Form1.Memo1.Lines.Add('box ' + IntToStr(b + 1) +
              ' candidates for number ' + IntToStr(n + 1) + ' all in row ' +
              IntToStr(r + 1) + ' (pointing): r' + IntToStr(r + 1) + ' ' + s +
              ' <> ' + IntToStr(n + 1));
        end;
    end;
    if simpleCheck and (n_cand_del > progress) then
      Exit;
  end;

end;

procedure block_candidates_in_col;
var
  b, n, c, i, j, progress: Integer;
  k, rowpos: BigInteger;
  s: String;
begin
  for b := 0 to DIM - 1 do
  begin
    progress := n_cand_del;
    for n := 0 to DIM - 1 do
    begin
      k := bn_k[DIM * b + n];
      // indices of number n in block b;

{$IF STRICT_POINTCLAIM=true}
      if bitCount(k) < 2 then
        continue;
{$IFEND}
      for i := 0 to B_COL - 1 do // i is relative index of column in block
        if (notZero(k)) and EqualBig(AndBig(k, colmask2[i]), k) then
        begin
          c := B_COL * (b mod B_ROW) + i;
          rowpos := AndBig(cn_r[DIM * c + n], NotBig(colmask[b div B_ROW]));
          // row positions of deleteable candidates
          j := 0;
          s := '';
          while notZero(rowpos) do
          begin
            if odd(rowpos.b[0]) then
            begin
              deleteCandidate(j, c, n);
              if verbose then
                s := s + 'r' + IntToStr(j + 1);
            end;
            rowpos := shrOneBig(rowpos);
            Inc(j)
          end;
          if verbose and (s <> '') then
            Form1.Memo1.Lines.Add('box ' + IntToStr(b + 1) +
              ' candidates for number ' + IntToStr(n + 1) + ' all in column ' +
              IntToStr(c + 1) + ' (pointing): ' + s + ' c' + IntToStr(c + 1) +
              ' <> ' + IntToStr(n + 1));
        end;
    end;
    if simpleCheck and (n_cand_del > progress) then
      Exit;
  end;
end;
// *****************************************************************************

// ************************ locked candidates type 2 (claiming) ***************************
procedure row_candidates_in_block;
var
  r, n, i, j, b, progress: Integer;
  c, idxpos: BigInteger;
  s: String;
begin
  for r := 0 to DIM - 1 do
  begin
    progress := n_cand_del;
    for n := 0 to DIM - 1 do
    begin
      c := rn_c[DIM * r + n];
      // indices of number n in row r
{$IF STRICT_POINTCLAIM=true}
      if bitCount(c) < 2 then
        continue;
{$IFEND}
      for i := 0 to B_ROW - 1 do // relative index of block in row
        if (notZero(c)) and EqualBig(AndBig(c, rowmask[i]), c) then
        begin

          b := B_ROW * (r div B_ROW) + i;
          idxpos := AndBig(bn_k[DIM * b + n], NotBig(rowmask[r mod B_ROW]));
          j := 0;
          s := '';
          while notZero(idxpos) do
          begin
            if odd(idxpos.b[0]) then
            begin
              deleteCandidate(bk_to_r(b, j), bk_to_c(b, j), n);
              if verbose then
                s := s + 'r' + IntToStr(bk_to_r(b, j) + 1) + 'c' +
                  IntToStr(bk_to_c(b, j) + 1) + ' ';
            end;
            idxpos := shrOneBig(idxpos);
            Inc(j)
          end;
          if verbose and (s <> '') then
            Form1.Memo1.Lines.Add('row ' + IntToStr(r + 1) +
              ' candidates for number ' + IntToStr(n + 1) + ' all in box ' +
              IntToStr(b + 1) + ' (claiming): ' + s + '<> ' + IntToStr(n + 1));
        end;
    end;
    if simpleCheck and (n_cand_del > progress) then
      Exit;
  end;
end;

procedure col_candidates_in_block;
var
  n, c, i, j, b, progress: Integer;
  r, idxpos: BigInteger;
  s: String;
begin
  for c := 0 to DIM - 1 do
  begin
    progress := n_cand_del;
    for n := 0 to DIM - 1 do
    begin
      r := cn_r[DIM * c + n];
      // indices of number n in column c
{$IF STRICT_POINTCLAIM=true}
      if bitCount(r) < 2 then
        continue;
{$IFEND}
      for i := 0 to B_COL - 1 do // relative index of block in column
        if (notZero(r)) and EqualBig(AndBig(r, colmask[i]), r) then
        begin
          b := B_ROW * i + c div B_COL;
          idxpos := AndBig(bn_k[DIM * b + n], NotBig(colmask2[c mod B_COL]));
          j := 0;
          s := '';
          while notZero(idxpos) do
          begin
            if odd(idxpos.b[0]) then
            begin
              deleteCandidate(bk_to_r(b, j), bk_to_c(b, j), n);
              if verbose then
                s := s + 'r' + IntToStr(bk_to_r(b, j) + 1) + 'c' +
                  IntToStr(bk_to_c(b, j) + 1) + ' ';
            end;
            idxpos := shrOneBig(idxpos);
            Inc(j)
          end;
          if verbose and (s <> '') then
            Form1.Memo1.Lines.Add('column ' + IntToStr(c + 1) +
              ' candidates for number ' + IntToStr(n + 1) + ' all in box ' +
              IntToStr(b + 1) + ' (claiming): ' + s + '<> ' + IntToStr(n + 1));
        end;
    end;
    if simpleCheck and (n_cand_del > progress) then
      Exit;
  end;
end;
// *****************************************************************************

function solveWithoutSat: Integer;
// returns the number of unsolved cells
var
  // clauses, output, errors: TStringList;
  progress: Integer;
  i, mx: Integer;
Label restart;
begin
  verbose := false;

  mx := max(Form1.SpinEditMaxHiddenTuple.Value,
    Form1.SpinEditMaxNakedTuple.Value);
  mx := max(mx, Form1.SpinEditMaxFish.Value);
  repeat
  restart:
    Application.ProcessMessages;
    progress := n_cand_del;
    if Form1.CheckHiddenSingles.Checked then
    begin
      hidden_single_block;
      hidden_single_row;
      hidden_single_col;
      if n_cand_del > progress then
        goto restart;
    end;

    if Form1.CheckNakedSingles.Checked then
    begin
      naked_single;
      if n_cand_del > progress then
        goto restart;
    end;

    if Form1.CheckBlockLineInteraction.Checked then
    begin
      block_candidates_in_row;
      block_candidates_in_col;
      row_candidates_in_block;
      col_candidates_in_block;
      if n_cand_del > progress then
        goto restart;
    end;

    for i := 2 to mx do
    begin
      if Form1.CheckHiddenTuple.Checked and
        (i <= Form1.SpinEditMaxHiddenTuple.Value) then
      begin
        hidden_tuple_block(i);
        hidden_tuple_row(i);
        hidden_tuple_col(i);
      end;
      if Form1.CheckNakedTuple.Checked and
        (i <= Form1.SpinEditMaxNakedTuple.Value) then
      begin
        naked_tuple_block(i);
        naked_tuple_row(i);
        naked_tuple_col(i);
      end;
      if Form1.CheckBasicFish.Checked and (i <= Form1.SpinEditMaxFish.Value)
      then
      begin
        basicfish_tuple_row(i);
        basicfish_tuple_col(i);
      end;
      if n_cand_del > progress then
        goto restart;
    end;

    Application.ProcessMessages;
  until (n_cand_del = progress) or (n_cand_del = DIM3);

  Result := DIM2 - n_set; // number of unset cells
end;

function solveOnlySat(maxClauses: Integer; fullSolve: Boolean): Integer;
var
  clauses: TStringList;
  n_clauses: Integer;
Label xxx;
begin
  if not fullSolve then
    goto xxx;

  clauses := TStringList.Create;
  n_clauses := generate_cnf(clauses);
  if n_clauses > maxClauses then
  begin
    clauses.Free;
    Exit(n_clauses);
  end;
  clauses.SaveToFile('cnf.txt');
  clauses.Free;
xxx:
  output := TStringList.Create;
  // solution := TStringList.Create;
  solution.Clear;

  try
    errors := TStringList.Create;

    Form1.Memo1.Lines.Add('Invoking SAT-solver...');
    Application.ProcessMessages;
    satThread := TSATThread.Create(false);

    while not satThread.Terminated do
    begin
      Sleep(100);
      Application.ProcessMessages;
    end;

    decode_solution(output, solution);

  finally
    output.Free;
    errors.Free;
  end;

  Result := n_clauses; // value undefined if is_reduced=true!
end;

// Button "Solve" click
procedure TForm1.BSATSolverClick(Sender: TObject);
var
  clauses: TStringList;
  progress: Integer;
  i, mx, tme: Integer;
Label restart, xxx;
begin

  if BSATSolver.Caption = 'Abort' then
  begin
    stopComputation := true;
    BSATSolver.Caption := 'Solve puzzle'
  end
  else
  begin
    stopComputation := false;
    BSATSolver.Caption := 'Abort'
  end;

  if stopComputation then
  begin
    SATKilled := true;
    KillProcess(SATPID); // if no SAT is running this fails silently
    Exit;
  end;

  initBitArraysFromGivens;

  tme := getTickcount;

  if Sender = nil then
    goto xxx; // search for other solutions

  // try to reduce the number of candidates first
  if CheckVerbose.Checked then
  begin
    verbose := true;
    simpleCheck := true;
  end
  else
  begin
    verbose := false;
    simpleCheck := false;
  end;
  mx := max(Form1.SpinEditMaxHiddenTuple.Value,
    Form1.SpinEditMaxNakedTuple.Value);
  mx := max(mx, Form1.SpinEditMaxFish.Value);
  repeat
  restart:
    if stopComputation then
    begin
      Memo1.Lines.Add('');
      Memo1.Lines.Add('Solving process aborted!');
      Memo1.Lines.Add('');
      Exit;
    end;

    Application.ProcessMessages;
    progress := n_cand_del;

    if CheckHiddenSingles.Checked then
    begin
      hidden_single_block;
      if (n_cand_del > progress) and verbose then
        goto restart;
      hidden_single_row;
      if (n_cand_del > progress) and verbose then
        goto restart;
      hidden_single_col;
      if (n_cand_del > progress) and verbose then
        goto restart;
    end;

    if CheckNakedSingles.Checked then
      naked_single;

    if (n_cand_del > progress) then
      goto restart;

    if CheckBlockLineInteraction.Checked then
    begin
      block_candidates_in_row;
      if (n_cand_del > progress) and verbose then
        goto restart;
      block_candidates_in_col;
      if (n_cand_del > progress) and verbose then
        goto restart;
      row_candidates_in_block;
      if (n_cand_del > progress) and verbose then
        goto restart;
      col_candidates_in_block;
    end;

    if n_cand_del > progress then
      goto restart;

    for i := 2 to mx do
    begin
      if Form1.CheckHiddenTuple.Checked and
        (i <= Form1.SpinEditMaxHiddenTuple.Value) then
      begin
        hidden_tuple_block(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
        hidden_tuple_row(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
        hidden_tuple_col(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
      end;
      if Form1.CheckNakedTuple.Checked and
        (i <= Form1.SpinEditMaxNakedTuple.Value) then
      begin
        naked_tuple_block(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
        naked_tuple_row(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
        naked_tuple_col(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
      end;
      if Form1.CheckBasicFish.Checked and (i <= Form1.SpinEditMaxFish.Value)
      then
      begin
        basicfish_tuple_row(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
        basicfish_tuple_col(i);
        if (n_cand_del > progress) and verbose then
          goto restart;
      end;
      if n_cand_del > progress then
        goto restart;
    end;

  until (n_cand_del = progress) or (n_cand_del = DIM3);

  if CheckSATSolver.Checked and (n_cand_del < DIM3) then
  begin
    Memo1.Lines.Add('');
    Memo1.Lines.Add('Invoking SAT-solver to finish solving process...');
    Memo1.Lines.Add('');

    clauses := TStringList.Create;
    generate_cnf(clauses);
    clauses.SaveToFile('cnf.txt');
    clauses.Free;
  xxx:
    output := TStringList.Create;
    solution.Clear;

    try
      errors := TStringList.Create;

      SATKilled := false;
      satThread := TSATThread.Create(false);

      while not satThread.Terminated do
      begin
        Sleep(100);
        Application.ProcessMessages;
      end;

      decode_solution(output, solution);

      if (solution.Count > 0) then
      begin
        Memo1.Lines.Add('');
        PrintCurrentPuzzle;

        if SATKilled then
          Memo1.Lines.Add('SAT Solver aborted!')
        else if Sender = nil then
          Memo1.Lines.Add('This is a different solution! ')
        else
          Memo1.Lines.Add
            ('Puzzle solved! To check uniqueness use button "Find different solution".');

        BAddSolution.Enabled := true;
      end
      else
      begin
        Memo1.Lines.Add('');
        if Sender <> nil then
          Memo1.Lines.Add('Puzzle is unsolvable!')
        else // in this case Button "Find different solution" was pressed
          Memo1.Lines.Add('There is no other solution!')
      end;
      if satFailed then
      begin
        Memo1.Lines.Add('');
        Memo1.Lines.Add(satError)
      end;

    finally
      output.Free;
      errors.Free;
      // solution.free
    end;
    Memo1.Lines.Add('');
  end
  else
  begin
    Memo1.Lines.Add('');
    i := PrintCurrentPuzzle;
    Memo1.Lines.Add('');
    if i = 0 then
    begin
      if solutionValid then
        Memo1.Lines.Add('Puzzle solved - the solution is unique!')
      else
        Memo1.Lines.Add
          ('The unique solution is a valid Sudoku but an invalid SudokuX!')
    end
    else
    begin
      Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' +
        IntToStr(DIM3 - n_cand_del) + ' candidates(pencilmarks).');

    end;

    Memo1.Lines.Add('');
  end;
  BSATSolver.Caption := 'Solve puzzle';

  Memo1.Lines.Add(FloatToStr((getTickcount - tme) / 1000) + ' s total time.');
  Memo1.Lines.Add('');
end;

procedure TForm1.FormCreate(Sender: TObject);
begin

  SpinEditRow.MaxValue := N_MAXBOXLENGTH;
  SpinEditCol.MaxValue := N_MAXBOXLENGTH;

  B_ROW := SpinEditRow.Value;
  B_COL := SpinEditCol.Value;;
  DIM := B_ROW * B_COL; // Length of a row or column
  DIM2 := DIM * DIM; // Number of cells in puzzle
  DIM3 := DIM2 * DIM; // number of candidates

  SpinEditMaxHiddenTuple.MaxValue := DIM div 2;
  SpinEditMaxNakedTuple.MaxValue := DIM div 2;
  SpinEditMaxFish.MaxValue := DIM div 2;

  SetLength(rc_n, DIM2);
  SetLength(rn_c, DIM2);
  SetLength(cn_r, DIM2);
  SetLength(bn_k, DIM2);
  SetLength(pn_k, DIM2);
  SetLength(rc_set, DIM2);

  SetLength(rowmask, B_ROW);
  SetLength(rowmask2, B_ROW);
  SetLength(colmask, B_COL);
  SetLength(colmask2, B_COL);

  init_bitmasks;
  solution := TStringList.Create;
  randomize;
  firstLoad := true;
  // flag for FileOpenDialaog
  nochange := false; // for symmetries
  CheckSudokuX.Enabled := (B_ROW = B_COL);
end;

function makeDefString(sl: TStringList): String;
var
  snew, goodSet, badSet: TStringList;
  s_split: TArray<String>;
  i, j: Integer;
  test: Boolean;
  s: String;
begin
  snew := TStringList.Create;
  goodSet := TStringList.Create;
  badSet := TStringList.Create;

  if (DIM < 10) then
  begin
    Result := '';
    test := true;
    for i := 0 to sl.Count - 1 do
      if Length(sl[i]) > DIM + B_ROW + 3 then
      begin
        test := false;
        break;
      end;
    if test then // presumably multiline format without spaces
    begin
      for i := 0 to sl.Count - 1 do
      begin
        s := '';
        for j := 1 to sl[i].Length do // insert spaces
          s := s + sl[i][j] + ' ';
        sl[i] := s;
      end
    end
    else if (sl.Count = 1) and (Length(sl[0]) = DIM2) then
    // presumably one line format
    begin
      for i := 1 to DIM2 do
        Result := Result + sl[0][i] + ' ';
      snew.Free;
      goodSet.Free;
      badSet.Free;
      Exit(Result);
    end;
  end;

  // multi line format
  goodSet.Add('.'); // valid symbols in puzzle definition strings
  if DIM < 10 then
    goodSet.Add('_')
  else if DIM < 100 then
  begin
    goodSet.Add('__');
    goodSet.Add('00');
  end
  else if DIM < 1000 then
    goodSet.Add('___');
  for i := 0 to DIM do
    goodSet.Add(IntToStr(i));
  for i := 0 to DIM do
    goodSet.Add('0' + IntToStr(i));

  badSet.Add('experiment:'); // some testsuites have strange formats
  badSet.Add('number');
  badSet.Add('task:');
  badSet.Add('puzzle');

  for i := 0 to sl.Count - 1 do
  begin
    Result := '';
    s_split := custom_split(sl[i]);
    for j := 0 to Length(s_split) - 1 do
    begin
      if badSet.IndexOf(s_split[j]) <> -1 then
        break;
      if goodSet.IndexOf(s_split[j]) = -1 then
        continue;

      if s_split[j] = '' then
        continue;
      if pos('_', s_split[j]) > 0 then
        s_split[j] := '0';
      // used in some testsuites for empty position
      if s_split[j] = '00' then
        s_split[j] := '0';

      Result := Result + s_split[j] + ' ';
    end;
    if Result <> '' then
      snew.Add(Result);
  end;
  Result := '';
  for i := 0 to snew.Count - 1 do
    Result := Result + snew[i] + ' ';

  snew.Free;
  goodSet.Free;
  badSet.Free;
end;

//
procedure TForm1.SEMaxHiddenTupleChange(Sender: TObject);
begin
  BAddSolution.Enabled := false;
end;

// Change number of columns in "Select blocksize"
procedure TForm1.SpinEditColChange(Sender: TObject);
begin
  if (Sender as TSpinEdit).Value > N_MAXBOXLENGTH then
    (Sender as TSpinEdit).Value := N_MAXBOXLENGTH;
  // necessary if values are entered directly
  B_COL := (Sender as TSpinEdit).Value;
  DIM := B_ROW * B_COL;
  // Length of a row or column
  DIM2 := DIM * DIM; // Number of cells in puzzle
  DIM3 := DIM2 * DIM; // number of candidates

  SpinEditMaxHiddenTuple.MaxValue := DIM div 2;
  SpinEditMaxNakedTuple.MaxValue := DIM div 2;
  SpinEditMaxFish.MaxValue := DIM div 2;
  BSATSolver.Enabled := false;
  BAddSolution.Enabled := false;

  SetLength(rc_n, DIM2);
  SetLength(rn_c, DIM2);
  SetLength(cn_r, DIM2);
  SetLength(bn_k, DIM2);
  SetLength(pn_k, DIM2);
  SetLength(rc_set, DIM2);

  SetLength(rowmask, B_ROW);
  SetLength(rowmask2, B_ROW);
  SetLength(colmask, B_COL);
  SetLength(colmask2, B_COL);

  init_bitmasks;
  CheckSudokuX.Checked := false;
  CheckSudokuX.Enabled := (B_ROW = B_COL);
  if B_COL * B_ROW > 36 then
  begin
    CheckSATSolver.Caption := 'SAT Solver (eventually slow)';
    CheckSATSolver.Checked := false
  end
  else
    CheckSATSolver.Caption := 'SAT Solver';
end;

// Change number of rows in "Select blocksize"
procedure TForm1.SpinEditRowChange(Sender: TObject);
begin
  if (Sender as TSpinEdit).Value > N_MAXBOXLENGTH then
    (Sender as TSpinEdit).Value := N_MAXBOXLENGTH;
  // necessary if values are entered directly

  B_ROW := (Sender as TSpinEdit).Value;
  DIM := B_ROW * B_COL;
  DIM2 := DIM * DIM;
  DIM3 := DIM2 * DIM;

  SpinEditMaxHiddenTuple.MaxValue := DIM div 2;
  SpinEditMaxNakedTuple.MaxValue := DIM div 2;
  SpinEditMaxFish.MaxValue := DIM div 2;
  BSATSolver.Enabled := false;
  BReduceBasic.Enabled := false;
  BReduceSAT.Enabled := false;
  BAddSolution.Enabled := false;

  SetLength(rc_n, DIM2);
  SetLength(rn_c, DIM2);
  SetLength(cn_r, DIM2);
  SetLength(bn_k, DIM2);
  SetLength(pn_k, DIM2);
  SetLength(rc_set, DIM2);

  SetLength(rowmask, B_ROW);
  SetLength(rowmask2, B_ROW);
  SetLength(colmask, B_COL);
  SetLength(colmask2, B_COL);

  init_bitmasks;
  CheckSudokuX.Checked := false;
  CheckSudokuX.Enabled := (B_ROW = B_COL);
  if B_COL * B_ROW > 36 then
  begin
    CheckSATSolver.Caption := 'SAT Solver (eventually slow)';
    CheckSATSolver.Checked := false
  end
  else
    CheckSATSolver.Caption := 'SAT Solver';
end;

procedure addSolution;
var
  clauses: TStringList;
  line_split: TArray<String>;
  s: String;
var
  i, j, col: Integer;
begin
  clauses := TStringList.Create;
  clauses.LoadFromFile('cnf.txt');
  s := '';
  for i := 0 to solution.Count - 1 do
  begin
    col := 0;
    line_split := custom_split(solution.Strings[i]);
    for j := 0 to Length(line_split) - 1 do
    begin
      if line_split[j] = '' then
        continue;
      s := s + '-' + varname(i, col, StrToInt(line_split[j])) + ' ';
      Inc(col);
    end;
  end;
  clauses.Add(s + ' 0');

  s := clauses.Strings[2];
  line_split := custom_split(s);
  s := '';
  for j := 0 to Length(line_split) - 2 do
    s := s + line_split[j] + ' ';
  s := s + IntToStr(StrToInt(line_split[Length(line_split) - 1]) + 1);
  // Increment number of clauses
  clauses.Strings[2] := s;
  clauses.SaveToFile('cnf.txt');
  clauses.Free;
end;

// Button "Find different soluiton" click
procedure TForm1.BAddSolutionClick(Sender: TObject);
begin
  addSolution;
  Memo1.Lines.Add('Invoking SAT-solver to find a different solution...');
  Memo1.Lines.Add('');
  BSATSolverClick(nil);
  BSATSolver.Enabled := false;
end;

// count all numbers which do not occur exactly once in column c
function col_error(c: Integer): Integer;
var
  t: array of Integer;
  r, i: Integer;
begin
  Result := 0;
  SetLength(t, DIM);
  for r := 0 to DIM - 1 do
    Inc(t[rc_set[DIM * r + c]]);
  for i := 0 to DIM - 1 do
  begin
    if t[i] <> 1 then
      Inc(Result);
  end;
end;

function block_error(b: Integer): Integer;
var
  t: array of Integer;
  r, c, k, i: Integer;
begin
  Result := 0;
  SetLength(t, DIM);
  for k := 0 to DIM - 1 do
  begin
    r := bk_to_r(b, k);
    c := bk_to_c(b, k);
    Inc(t[rc_set[DIM * r + c]]);
  end;
  for i := 0 to DIM - 1 do
  begin
    if t[i] <> 1 then
      Inc(Result);
  end;
end;

// Set of same positions in blocks
function pSet_error(p: Integer): Integer;
var
  t: array of Integer;
  r, c, b, i: Integer;
begin
  Result := 0;
  SetLength(t, DIM);
  for b := 0 to DIM - 1 do
  begin
    r := bk_to_r(b, p);
    c := bk_to_c(b, p);
    Inc(t[rc_set[DIM * r + c]]);
  end;
  for i := 0 to DIM - 1 do
  begin
    if t[i] <> 1 then
      Inc(Result);
  end;
end;

function X_error(): Integer;
var
  t: array of Integer;
  x, i: Integer;
begin
  Result := 0;

  SetLength(t, DIM);
  for x := 0 to DIM - 1 do
  begin
    Inc(t[rc_set[DIM * x + x]]);
  end;
  for i := 0 to DIM - 1 do
  begin
    if t[i] <> 1 then
      Inc(Result);
  end;

  SetLength(t, 0);
  SetLength(t, DIM);
  for x := 0 to DIM - 1 do
  begin
    Inc(t[rc_set[DIM * x + (DIM - 1 - x)]]);
  end;
  for i := 0 to DIM - 1 do
  begin
    if t[i] <> 1 then
      Inc(Result);
  end;

  for i := 0 to DIM - 1 do
  begin
    if 2 * i = DIM - 1 then
      continue;
    if rc_set[DIM * i + i] = rc_set[DIM * (DIM - 1 - i) + i] then
      Inc(Result);
  end;

end;

// return number of misplaced cells
function n_error(): Integer;
var
  c, b, p: Integer;
begin
  Result := 0;

  for c := 0 to DIM - 1 do
    Inc(Result, col_error(c));

  for b := 0 to DIM - 1 do
    Inc(Result, block_error(b));

  if Form1.CheckSudokuP.Checked then
  begin
    for p := 0 to DIM - 1 do
      Inc(Result, pSet_error(p));
  end;

  if Form1.CheckSudokuX.Checked then
  begin
    Inc(Result, X_error());
  end;

end;

// Errors in blocks and columns, which are affected by swapping emtries (r,c1)
// and (r,c2)
function n_rcError(r, c1, c2: Integer): Integer;
{ TODO : für xsudoku anpassen }
var
  b1, b2, p1, p2: Integer;
begin
  if c1 = c2 then
    Result := col_error(c1)
  else
    Result := col_error(c1) + col_error(c2);
  // blocks of cells which are exchanged
  b1 := B_ROW * (r div B_ROW) + c1 div B_COL;
  b2 := B_ROW * (r div B_ROW) + c2 div B_COL;
  if b1 = b2 then
    Inc(Result, block_error(b1))
  else
    Inc(Result, block_error(b1) + block_error(b2));

  if Form1.CheckSudokuP.Checked then
  begin
    p1 := B_COL * (r mod B_ROW) + c1 mod B_COL;
    p2 := B_COL * (r mod B_ROW) + c2 mod B_COL;
    if p1 = p2 then
      Inc(Result, pSet_error(p1))
    else
      Inc(Result, pSet_error(p1) + pSet_error(p2));
  end;

  if Form1.CheckSudokuX.Checked then
  begin
    Inc(Result, X_error);
  end;
end;

// Button "Random grid" click
procedure TForm1.BCreateClick(Sender: TObject);
var
  a: array of Integer;
  i, j, r, e, eOld, eNew, tmp: Integer;
  cnt: UINT64;
  tm: Cardinal;
begin
  if CheckSudokuX.Checked or CheckSudokuP.Checked then
  begin
    Memo1.Lines.Add('');
    Memo1.Lines.Add
      ('Random Grid generation not implemented for SudokuX and SudokuP');
    Memo1.Lines.Add('');
    Exit;
  end;

  if BCreate.Caption = 'Abort' then
  begin
    stopComputation := true;
    BCreate.Caption := 'Random Grid'
  end
  else
  begin
    stopComputation := false;
    BCreate.Caption := 'Abort'
  end;

  if stopComputation then
    Exit;

  tm := getTickcount;
  SetLength(a, DIM);
  for i := 0 to DIM - 1 do
    a[i] := i;

  for i := 0 to DIM - 1 do
  begin
    permuteArray(a);
    for j := 0 to DIM - 1 do
      rc_set[DIM * i + j] := a[j];
  end;

  // each row now contains numbers 0..n-1 in random order
  Memo1.Lines.Add(IntToStr(n_error()));
  e := n_error();
  cnt := 0;
  while (e > 0) and not stopComputation do
  begin
    Inc(cnt);
    r := Random(DIM);
    // row

    i := Random(DIM); // places to swap in row
    if CheckSudokuX.Checked then
    begin
      if (r = i) or (r = DIM - 1 - i) then
        continue;
    end;

    j := Random(DIM);
    if CheckSudokuX.Checked then
    begin
      if (r = j) or (r = DIM - 1 - j) then
        continue;
    end;

    if i = j then
      continue;

    eOld := n_rcError(r, i, j);
    tmp := rc_set[DIM * r + i];
    rc_set[DIM * r + i] := rc_set[DIM * r + j];
    rc_set[DIM * r + j] := tmp;
    eNew := n_rcError(r, i, j);

    if eNew > eOld then // swap back
    begin
      tmp := rc_set[DIM * r + i];
      rc_set[DIM * r + i] := rc_set[DIM * r + j];
      rc_set[DIM * r + j] := tmp;
    end
    else
      e := e - eOld + eNew;
    if cnt mod 10000 = 0 then
    begin
      Memo1.Lines.Add(IntToStr(e));
      Application.ProcessMessages;
    end;
  end;
  for i := 0 to DIM2 - 1 do
  begin
    Inc(rc_set[i]); // make puzzle 1-based
  end;
  if not stopComputation then
  begin
    PrintCurrentPuzzle;
    initBitArraysFromGivens;
    BCreate.Caption := 'Random Grid';
  end
  else
  begin
    Memo1.Lines.Add('Grid generation aborted.');
    stopComputation := false;
  end;
  Memo1.Lines.Add(FloatToStr((getTickcount - tm) / 1000) + ' s total time.');
  BSATSolver.Enabled := true;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;
end;

// Button "Default grid" click
procedure TForm1.BDefaultClick(Sender: TObject);
var
  b, k: Integer;
  t1, t2: array of ByteArr;
begin
  if CheckSudokuX.Checked then
  begin
    Memo1.Lines.Add('');
    Memo1.Lines.Add('Default Grid not implemented for SudokuX');
    Memo1.Lines.Add('');
    Exit;
  end;
  for b := 0 to DIM - 1 do
    for k := 0 to DIM - 1 do
      rc_set[DIM * bk_to_r(b, k) + bk_to_c(b, k)] :=
        (k + B_COL * (b mod B_ROW) + (b div B_ROW)) mod DIM + 1;
  PrintCurrentPuzzle;
  initBitArraysFromGivens;

  BSATSolver.Enabled := true;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;
end;

// Button "Load" click
procedure TForm1.BLoadClick(Sender: TObject);
var
  sl: TStringList;
begin
  sl := TStringList.Create;
  OpenDialog1 := TOpenDialog.Create(self);

  // Set up the starting directory to be the current one
  if firstLoad then
  begin
    OpenDialog1.InitialDir := GetCurrentDir;
    firstLoad := false;
  end;
  // Only allow existing files to be selected
  OpenDialog1.Options := [ofFileMustExist];
  OpenDialog1.Filter := 'Text files|*.txt';
  OpenDialog1.FilterIndex := 1;

  // Display the open file dialog
  if OpenDialog1.Execute then
  begin
    sl.LoadFromFile(OpenDialog1.FileName);
    try
      curDefString := makeDefString(sl);
      initBitArraysFromString(curDefString);
    except
      Memo1.Lines.Add
        ('+-------------------------------------------------------+');
      Memo1.Lines.Add
        ('| Cannot paste puzzle! Wrong format for this boxsize. |');
      Memo1.Lines.Add
        ('+-------------------------------------------------------+');
      Memo1.Lines.Add('');
      sl.Free;
      OpenDialog1.Free;
      BSATSolver.Enabled := false;
      BReduceBasic.Enabled := false;
      BReduceSAT.Enabled := false;
      Exit;
    end;
    Memo1.Lines.Add(OpenDialog1.FileName + ':');
    Memo1.Lines.Add('');
    PrintCurrentPuzzle;
    Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del)
      + ' candidates(pencilmarks).');
    Memo1.Lines.Add('');
    BSATSolver.Enabled := true;
    BReduceBasic.Enabled := true;
    BReduceSAT.Enabled := true;
    BAddSolution.Enabled := false;
  end;
  sl.Free;
  OpenDialog1.Free;
end;

procedure TForm1.BLowClueGridClick(Sender: TObject);
var
  i, j, b, k: Integer;
  t1, t2: array of ByteArr;
  a: array of Integer;
  fillMode, statechange: Boolean;
begin
  if CheckSudokuX.Checked then
  begin
    Memo1.Lines.Add('');
    Memo1.Lines.Add('Default Grid not implemented for SudokuX');
    Memo1.Lines.Add('');
    Exit;
  end;
 for b := 0 to DIM - 1 do
    for k := 0 to DIM - 1 do
      rc_set[DIM * bk_to_r(b, k) + bk_to_c(b, k)] :=
        (k + B_COL * (b mod B_ROW) + (b div B_ROW)) mod DIM + 1;
  for k := 0 to DIM - 1 do // row
  begin
    if rc_set[DIM * k] < (DIM + 1) div 2 then
      fillMode := true
    else
      fillMode := false;
    statechange := false;
    for i := 0 to DIM - 1 do // col
    begin
      if (fillMode) and (rc_set[DIM * k + i] = (DIM + 1) div 2) and not statechange
      then
      begin
        fillMode := false;
        statechange := true;
      end;
      if (not fillMode) and (rc_set[DIM * k + i] = (DIM + 1) div 2) and
        not statechange and (i > 0) then
      begin
        fillMode := true;
        statechange := true;
      end;
      if not fillMode then
        rc_set[DIM * k + i] := 0;
    end;
  end;

  PrintCurrentPuzzle;
  initBitArraysFromGivens;
  Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
    ' candidates(pencilmarks).');
  Memo1.Lines.Add('');
  BSATSolver.Enabled := true;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;
end;

procedure TForm1.Paste1Click(Sender: TObject);
var
  sl: TStringList;
  s: String;
begin
  sl := TStringList.Create;
  s := Clipboard.AsText;
  sl.Text := s;
  try
    curDefString := makeDefString(sl);
    initBitArraysFromString(curDefString);
  except
    Memo1.Lines.Add
      ('+-------------------------------------------------------+');
    Memo1.Lines.Add('| Cannot paste puzzle! Wrong format for this boxsize. |');
    Memo1.Lines.Add
      ('+-------------------------------------------------------+');
    Memo1.Lines.Add('');
    sl.Free;
    BSATSolver.Enabled := false;
    BReduceBasic.Enabled := false;
    BReduceSAT.Enabled := false;
    Exit;
  end;
  Memo1.Lines.Add('');
  PrintCurrentPuzzle;
  Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
    ' candidates(pencilmarks).');
  Memo1.Lines.Add('');
  BSATSolver.Enabled := true;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;
  BAddSolution.Enabled := false;
  sl.Free;

end;

function seperatorLine(sz: Integer): String;
var
  i, j: Integer;
begin
  Result := ' +';
  for i := 0 to B_ROW - 1 do
  begin
    for j := 0 to B_COL - 1 do
      Result := Result + StringOfChar('-', sz);
    Result := Result + '-+';
  end;
end;

function TForm1.PrintCurrentPuzzle: Integer;
// returns number of unfilled cells
var
  r, c, sz: Integer;
  s, s2, form: String;
begin
  if CheckOutlineBoxes.Checked then
  begin
    Result := 0;
    for r := 0 to DIM - 1 do
    begin
      s := '';
      if DIM < 10 then
      begin
        form := '%2s';
        sz := 2;
      end
      else if DIM < 100 then
      begin
        form := '%3s';
        sz := 3;
      end
      else if DIM < 1000 then
      begin
        form := '%4s';
        sz := 4;
      end;
      if r mod B_ROW = 0 then
      begin
        Memo1.Lines.Add(seperatorLine(sz));
      end;
      for c := 0 to DIM - 1 do
      begin
        if rc_set[DIM * r + c] = 0 then
        begin
          s2 := '.';
          Inc(Result);
        end
        else
          s2 := IntToStr(rc_set[DIM * r + c]);
        if c mod B_COL = 0 then
          s2 := ' |' + Format(form, [s2])
        else
          s2 := Format(form, [s2]);
        s := s + s2;
      end;
      s := s + ' |';
      Memo1.Lines.Add(s);
    end;
    Memo1.Lines.Add(seperatorLine(sz));
    Memo1.Lines.Add('');
  end
  else
  begin
    Result := 0;
    for r := 0 to DIM - 1 do
    begin
      s := '';
      if DIM < 10 then
        form := '%2s'
      else if DIM < 100 then
        form := '%3s'
      else if DIM < 1000 then
        form := '%4s';
      for c := 0 to DIM - 1 do
      begin
        if rc_set[DIM * r + c] = 0 then
        begin
          s2 := '.';
          Inc(Result);
        end
        else
          s2 := IntToStr(rc_set[DIM * r + c]);
        s := s + Format(form, [s2]);
      end;
      Memo1.Lines.Add(s);
    end;
    Memo1.Lines.Add('');
  end;
  if DIM < 10 then // one line display
  begin
    s := '';
    for r := 0 to DIM - 1 do
      for c := 0 to DIM - 1 do
        if rc_set[DIM * r + c] = 0 then
          s := s + '.'
        else
          s := s + IntToStr(rc_set[DIM * r + c]);
    Memo1.Lines.Add(s);
    Memo1.Lines.Add('');
  end;

end;

procedure arrclear_sym(var a: ByteArr; s, n: Integer);
var
  r, c: Integer;
begin
  a[n] := 0;
  if s = 0 then
    Exit;

  r := n div DIM;
  c := n mod DIM;
  case s of
    1:
      a[r * DIM + (DIM - c - 1)] := 0;
    // vertical
    2:
      a[(DIM - r - 1) * DIM + c] := 0; // horizontal
    3:
      a[r + c * DIM] := 0; // diagonal
    4:
      a[(DIM - r - 1) * DIM + (DIM - c - 1)] := 0; // rot 2
    5:
      begin
        a[r * DIM + (DIM - c - 1)] := 0; // vertical, horizontal, rot 2
        a[(DIM - r - 1) * DIM + c] := 0;
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := 0;
      end;
    6:
      begin
        a[r + c * DIM] := 0; // diagonal, rot 2, antidiagonal
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := 0;
        a[(DIM - r - 1) + (DIM - c - 1) * DIM] := 0;

      end;
    7:
      begin
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := 0;
        // rot 2, rot 4, rot -4
        a[(DIM - r - 1) + c * DIM] := 0;
        a[r + (DIM - c - 1) * DIM] := 0;
      end;
    8:
      begin
        a[(DIM - r - 1) * DIM + c] := 0;
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := 0;
        a[r * DIM + (DIM - c - 1)] := 0;
        a[r + c * DIM] := 0;
        a[(DIM - r - 1) + c * DIM] := 0;
        a[(DIM - r - 1) + (DIM - c - 1) * DIM] := 0;
        a[r + (DIM - c - 1) * DIM] := 0;
      end;
  end;
end;

procedure fixcells(var a: array of Boolean; s, n: Integer);
var
  r, c: Integer;
begin
  a[n] := false;
  if s = 0 then
    Exit;
  r := n div DIM;
  c := n mod DIM;
  case s of
    1:
      a[r * DIM + (DIM - c - 1)] := false;
    2:
      a[(DIM - r - 1) * DIM + c] := false;
    3:
      a[r + c * DIM] := false;
    4:
      a[(DIM - r - 1) * DIM + (DIM - c - 1)] := false;
    5:
      begin
        a[r * DIM + (DIM - c - 1)] := false;
        // vertical, horizontal, rot 2
        a[(DIM - r - 1) * DIM + c] := false;
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := false;
      end;
    6:
      begin
        a[r + c * DIM] := false;
        // diagonal, rot 2, antidiagonal
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := false;
        a[(DIM - r - 1) + (DIM - c - 1) * DIM] := false;

      end;
    7:
      begin
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := false;
        // rot 2, rot 4, rot -4
        a[(DIM - r - 1) + c * DIM] := false;
        a[r + (DIM - c - 1) * DIM] := false;
      end;
    8:
      begin
        a[(DIM - r - 1) * DIM + c] := false;
        a[(DIM - r - 1) * DIM + (DIM - c - 1)] := false;
        a[r * DIM + (DIM - c - 1)] := false;
        a[r + c * DIM] := false;
        a[(DIM - r - 1) + c * DIM] := false;
        a[(DIM - r - 1) + (DIM - c - 1) * DIM] := false;
        a[r + (DIM - c - 1) * DIM] := false;
      end;
  end;
end;

procedure saveConfiguration(var n_cand_delx, n_setx: Integer;
  var rc_setx: ByteArr; var rc_nx, rn_cx, cn_rx, bn_kx, pn_kx: BigIntArr);
begin
  n_cand_delx := n_cand_del;
  n_setx := n_set;

  rc_setx := Copy(rc_set);
  rc_nx := Copy(rc_n);
  rn_cx := Copy(rn_c);
  cn_rx := Copy(cn_r);
  bn_kx := Copy(bn_k);
  pn_kx := Copy(pn_k);

end;

procedure loadConfiguration(var n_cand_delx, n_setx: Integer;
  var rc_setx: ByteArr; var rc_nx, rn_cx, cn_rx, bn_kx, pn_kx: BigIntArr);
begin
  n_cand_del := n_cand_delx;
  n_set := n_setx;

  rc_set := Copy(rc_setx);
  rc_n := Copy(rc_nx);
  rn_c := Copy(rn_cx);
  cn_r := Copy(cn_rx);
  bn_k := Copy(bn_kx);
  pn_k := Copy(pn_kx);

end;

// Button "Reduce givens" click
procedure TForm1.BReduceBasicClick(Sender: TObject);
var
  i, j, n, rnd, clauseLimit, deltalimit, givens: Integer;
  rc_setsave: ByteArr;
  randArr: array of Integer;
  removable: array of Boolean;
  alldone: Boolean;
  tme: Cardinal;
  n_cand_delOld, n_setOld, n_cand_delNew, n_setNew: Integer;
  rc_setOld, rc_setNew: ByteArr;
  rc_nOld, rn_cOld, cn_rOld, bn_kOld, pn_kOld, rc_nNew, rn_cNew, cn_rNew,
    bn_kNew, pn_kNew: BigIntArr;
begin

  SetLength(rc_setOld, DIM2);
  SetLength(rc_setNew, DIM2);
  SetLength(rc_nOld, DIM2);
  SetLength(rn_cOld, DIM2);
  SetLength(cn_rOld, DIM2);
  SetLength(bn_kOld, DIM2);
  SetLength(pn_kOld, DIM2);
  SetLength(rc_nNew, DIM2);
  SetLength(rn_cNew, DIM2);
  SetLength(cn_rNew, DIM2);
  SetLength(bn_kNew, DIM2);
  SetLength(pn_kNew, DIM2);

  // get symmetry
  if RadioOneFold.Checked then
  begin
    sym := 0; // no symmetry
    if CheckCenterLineVer.Checked then
      sym := 1;
    if CheckCenterLineHor.Checked then
      sym := 2;
    if CheckDiagonal.Checked then
      sym := 3;
  end
  else if RadioTwoFold.Checked then
  begin
    sym := 4;
    if CheckCenterLineVer.Checked then
      sym := 5;
    if CheckDiagonal.Checked then
      sym := 6;
  end
  else if RadioFourFold.Checked then
  begin
    sym := 7;
    if CheckCenterLineVer.Checked then
      sym := 8;
  end;

  stopComputation := false;
  BReduceBasic.Enabled := false;
  BReduceSAT.Enabled := false;
  simpleCheck := false;
  // slows down computation, only used for solve

  SetLength(rc_setsave, DIM2);
  SetLength(randArr, DIM2);
  SetLength(removable, DIM2);

  for i := 0 to DIM2 - 1 do
    randArr[i] := i;
  permuteArray(randArr); // generate random array

  for i := 0 to DIM2 - 1 do
  begin
    rc_setsave[i] := rc_set[i];
    removable[i] := true;
  end;
  deltalimit := 1000;

  initBitArraysFromGivens; // Grundinitialisierung

  // save current configuration
  saveConfiguration(n_cand_delOld, n_setOld, rc_setOld, rc_nOld, rn_cOld,
    cn_rOld, bn_kOld, pn_kOld);

  if CheckSATSolver.Checked then
    clauseLimit := MaxInt div 2
  else
    clauseLimit := 0;

  repeat
    for i := 0 to DIM2 - 1 do
    begin
      if stopComputation then
        break;

      Application.ProcessMessages;
      rnd := randArr[i];

      if (rc_set[rnd] = 0) or not removable[rnd] then
        continue;

      tme := getTickcount;

      arrclear_sym(rc_set, sym, rnd);
      // remove random elements from old rc_set

      // neue Konfiguration erzeugen und speichern
      // erzeugen.....

      for j := 0 to DIM2 - 1 do
      begin
        if rc_set[j] <> rc_setOld[j] then
        begin
          n := rc_setOld[j] - 1; // the removed number (zero based)
          deleteNumber(j div DIM, j mod DIM, n);
        end;
      end;

      // speichern
      saveConfiguration(n_cand_delNew, n_setNew, rc_setNew, rc_nNew, rn_cNew,
        cn_rNew, bn_kNew, pn_kNew);

      givens := n_set;
      if solveWithoutSat = 0 then // no free cells left
      begin

        // neue Konfiguration laden. Alte Konfig:= Neue Konfig

        loadConfiguration(n_cand_delNew, n_setNew, rc_setNew, rc_nNew, rn_cNew,
          cn_rNew, bn_kNew, pn_kNew);
        saveConfiguration(n_cand_delOld, n_setOld, rc_setOld, rc_nOld, rn_cOld,
          cn_rOld, bn_kOld, pn_kOld);

        Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
          IntToStr(givens) + ' givens left. (' + FloatToStr((getTickcount - tme)
          / 1000) + ' s)');

      end
      else
      begin
        // because cannot solve with given methods
        Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' is unremovable. (' +
          FloatToStr((getTickcount - tme) / 1000) + ' s)');

        // Alte Konfiguration laden
        loadConfiguration(n_cand_delOld, n_setOld, rc_setOld, rc_nOld, rn_cOld,
          cn_rOld, bn_kOld, pn_kOld);

      end;
      fixcells(removable, sym, rnd);

    end;

    clauseLimit := clauseLimit + deltalimit;
    alldone := true;
    for i := 0 to DIM2 - 1 do
      if removable[i] and (rc_set[i] <> 0) then
        alldone := false;
  until stopComputation or alldone;
  Memo1.Lines.Add('');
  initBitArraysFromGivens;
  PrintCurrentPuzzle;
  Memo1.Lines.Add('');
  Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
    ' candidates(pencilmarks).');
  if alldone then
    Memo1.Lines.Add
      ('Puzzle is minimal in relation to the chosen basic methods.');
  Memo1.Lines.Add('The SAT-method may eventually remove more givens. ');
  Memo1.Lines.Add('');
  stopComputation := false;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;

  SetLength(rc_setOld, 0);
  SetLength(rc_setNew, 0);
  SetLength(rc_nOld, 0);
  SetLength(rn_cOld, 0);
  SetLength(cn_rOld, 0);
  SetLength(bn_kOld, 0);
  SetLength(pn_kOld, 0);
  SetLength(rc_nNew, 0);
  SetLength(rn_cNew, 0);
  SetLength(cn_rNew, 0);
  SetLength(bn_kNew, 0);
  SetLength(pn_kNew, 0);

end;




// Button "Reduce givens" click (old version)
// procedure TForm1.BReduceClick(Sender: TObject);
// var
// i, j, rnd, clauseLimit, deltalimit, givens: Integer;
// rc_setsave: ByteArr;
// randArr: array of Integer;
// n_clauses: Integer;
// removable: array of Boolean;
// alldone: Boolean;
// tme: Cardinal;
// begin
// // get symmetry
// if RadioOneFold.Checked then
// begin
// sym := 0; // no symmetry
// if CheckCenterLineVer.Checked then
// sym := 1;
// if CheckCenterLineHor.Checked then
// sym := 2;
// if CheckDiagonal.Checked then
// sym := 3;
// end
// else if RadioTwoFold.Checked then
// begin
// sym := 4;
// if CheckCenterLineVer.Checked then
// sym := 5;
// if CheckDiagonal.Checked then
// sym := 6;
// end
// else if RadioFourFold.Checked then
// begin
// sym := 7;
// if CheckCenterLineVer.Checked then
// sym := 8;
// end;
//
// stopComputation := false;
// BReduce.Enabled := false;
// simpleCheck := false;
// // slows down computation, only used for solve
//
// SetLength(rc_setsave, DIM2);
// SetLength(randArr, DIM2);
// SetLength(removable, DIM2);
// for i := 0 to DIM2 - 1 do
// randArr[i] := i;
// permuteArray(randArr); // generate random array
//
// for i := 0 to DIM2 - 1 do
// begin
// rc_setsave[i] := rc_set[i];
// removable[i] := true;
// end;
// deltalimit := 1000;
// //////////////////////////////initBitArraysFromGivens;
// // get the number of the original clauses
//
// if CheckSATSolver.Checked then
// begin
// //////////////////  solveWithoutSat;
// // do this first to reduce cnf size
// clauseLimit := MaxInt div 2;
// // solveOnlySat(MaxInt, true) + 10000;//No restriction for first element
// ///////////////////////Memo1.Lines.Add('');
// end
// else
// clauseLimit := 0;
//
// //////////////////for i := 0 to DIM2 - 1 do // restore original unsolved state
// /////////////////  rc_set[i] := rc_setsave[i];
//
// repeat
// for i := 0 to DIM2 - 1 do
// begin
// if stopComputation then
// break;
//
// Application.ProcessMessages;
// rnd := randArr[i];
// if (rc_set[rnd] = 0) or not removable[rnd] then
// continue;
//
// tme := getTickcount;
//
// arrclear_sym(rc_set, sym, rnd); // Zufallselement(e) entfernen
//
// initBitArraysFromGivens;
// givens := n_set;
// if CheckSATSolver.Checked then
// begin
// if solveWithoutSat = 0 then
// // puzzle is solved withou SAT
// begin
//
// arrclear_sym(rc_setsave, sym, rnd);//store new valid configuration
//
// Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
// IntToStr(givens) + ' givens left. (' +
// FloatToStr((getTickcount - tme) / 1000) + ' s)');
// Memo1.Lines.Add('');
// if CheckSingleStep.Checked then
// stopComputation := true;
// // clauseLimit := n_clauses + deltalimit;
//
// end
// else
// begin // puzzle could not completely be solved without SAT
// SATKilled := false;
// n_clauses := solveOnlySat(clauseLimit, true);
// if (n_clauses <= clauseLimit) and not SATKilled then
// begin
// addSolution;
// Memo1.Lines.Add('Check SAT solution for uniqueness');
// Application.ProcessMessages;
// solveOnlySat(clauseLimit, false);
// // SATKilled can happen here again
// Application.ProcessMessages;
//
// if (solution.Count = 0) and not SATKilled then
// // still exactly one solution
// begin
// arrclear_sym(rc_setsave, sym, rnd); //store new valid configuration
//
// Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
// IntToStr(givens) + ' givens left. (' +
// FloatToStr((getTickcount - tme) / 1000) + ' s)');
// Memo1.Lines.Add('clauseLimit: ' + IntToStr(clauseLimit) +
// ', clauses: ' + IntToStr(n_clauses));
// Memo1.Lines.Add('');
// if CheckSingleStep.Checked then
// stopComputation := true;
// clauseLimit := n_clauses + deltalimit;
// end
//
// else // more than one solution
// begin
// if not SATKilled then
// begin
// Memo1.Lines.Add('Random cell ' + IntToStr(i) +
// ' is unremovable, ' + IntToStr(givens + 1) + ' givens left. ('
// + FloatToStr((getTickcount - tme) / 1000) + ' s)');
// Memo1.Lines.Add('')
// end;
// end;
// end;
// if SATKilled then
// begin
// Memo1.Lines.Add('SAT Solver aborted!');
// Memo1.Lines.Add('')
// end;
//
// fixcells(removable, sym, rnd);
// // egal ob Zellen(n) entfernt wurden oder nicht
// // sie werden als unremovable markiert
// end;
// end
// else // Simplify without SAT solver
// begin
// givens := n_set;
// if solveWithoutSat = 0 then
// begin
//
// arrclear_sym(rc_setsave, sym, rnd); //store new valid configuration
//
// Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
// IntToStr(givens) + ' givens left. (' +
// FloatToStr((getTickcount - tme) / 1000) + ' s)');
// end
// else
// begin
// // because cannot solve with given methods
// Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' is unremovable. (' +
// FloatToStr((getTickcount - tme) / 1000) + ' s)');
// end;
// fixcells(removable, sym, rnd);
// end;
// for j := 0 to DIM2 - 1 do
// rc_set[j] := rc_setsave[j]; //in case of success  rc_setsave holds the new
// //configuration. Else it holds the original configuration
// end;
//
// clauseLimit := clauseLimit + deltalimit;
// alldone := true;
// for i := 0 to DIM2 - 1 do
// if removable[i] and (rc_set[i] <> 0) then
// alldone := false;
// until stopComputation or alldone;
// Memo1.Lines.Add('');
// initBitArraysFromGivens;
// PrintCurrentPuzzle;
// Memo1.Lines.Add('');
// Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
// ' candidates(pencilmarks).');
// if alldone then
// Memo1.Lines.Add('Puzzle is minimal in relation to the chosen methods.');
// Memo1.Lines.Add('');
// stopComputation := false;
// BReduce.Enabled := true;
// end;

// Button "Stop reduce" click
procedure TForm1.BStopClick(Sender: TObject);
begin
  stopComputation := true;
  SATKilled := true;
  KillProcess(SATPID);
end;

procedure TForm1.BReduceSATClick(Sender: TObject);
var
  i, j, rnd, clauseLimit, deltalimit, givens: Integer;
  rc_setsave: ByteArr;
  randArr: array of Integer;
  n_clauses: Integer;
  removable: array of Boolean;
  alldone: Boolean;
  tme: Cardinal;
begin
  // get symmetry

  if RadioOneFold.Checked then
  begin
    sym := 0; // no symmetry
    if CheckCenterLineVer.Checked then
      sym := 1;
    if CheckCenterLineHor.Checked then
      sym := 2;
    if CheckDiagonal.Checked then
      sym := 3;
  end
  else if RadioTwoFold.Checked then
  begin
    sym := 4;
    if CheckCenterLineVer.Checked then
      sym := 5;
    if CheckDiagonal.Checked then
      sym := 6;
  end
  else if RadioFourFold.Checked then
  begin
    sym := 7;
    if CheckCenterLineVer.Checked then
      sym := 8;
  end;

  stopComputation := false;
  BReduceBasic.Enabled := false;
  BReduceSAT.Enabled := false;
  simpleCheck := false;
  // slows down computation, only used for solve

  SetLength(rc_setsave, DIM2);
  SetLength(randArr, DIM2);
  SetLength(removable, DIM2);
  for i := 0 to DIM2 - 1 do
    randArr[i] := i;
  permuteArray(randArr); // generate random array

  for i := 0 to DIM2 - 1 do
  begin
    rc_setsave[i] := rc_set[i];
    removable[i] := true;
  end;
  // deltalimit := 1000;

  clauseLimit := MaxInt div 2;

  repeat
    for i := 0 to DIM2 - 1 do
    begin
      if stopComputation then
        break;

      Application.ProcessMessages;
      rnd := randArr[i];
      if (rc_set[rnd] = 0) or not removable[rnd] then
        continue;

      tme := getTickcount;

      arrclear_sym(rc_set, sym, rnd); // Zufallselement(e) entfernen

      initBitArraysFromGivens;
      givens := n_set;

      if solveWithoutSat = 0 then
      // puzzle is solved withou SAT
      begin

        arrclear_sym(rc_setsave, sym, rnd); // store new valid configuration

        Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
          IntToStr(givens) + ' givens left. (' + FloatToStr((getTickcount - tme)
          / 1000) + ' s)');
        Memo1.Lines.Add('');
        if CheckSingleStep.Checked then
          stopComputation := true;
        // clauseLimit := n_clauses + deltalimit;

      end
      else
      begin // puzzle could not completely be solved without SAT
        SATKilled := false;
        n_clauses := solveOnlySat(clauseLimit, true);
        if satFailed then
        begin
          Memo1.Lines.Add('');
          Memo1.Lines.Add(satError);
          stopComputation := true;
        end;
        // if (n_clauses <= clauseLimit) and not SATKilled then
        if not SATKilled then
        begin
          addSolution;
          Memo1.Lines.Add('Check SAT solution for uniqueness');
          Application.ProcessMessages;
          solveOnlySat(clauseLimit, false);
          if satFailed then
          begin
            Memo1.Lines.Add('');
            Memo1.Lines.Add(satError);
            stopComputation := true;
          end;

          // SATKilled can happen here again
          Application.ProcessMessages;

          if (solution.Count = 0) and not SATKilled then
          // still exactly one solution
          begin
            arrclear_sym(rc_setsave, sym, rnd);
            // store new valid configuration

            Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' removed, ' +
              IntToStr(givens) + ' givens left. (' +
              FloatToStr((getTickcount - tme) / 1000) + ' s)');
            Memo1.Lines.Add('clauses: ' + IntToStr(n_clauses));
            Memo1.Lines.Add('');
            if CheckSingleStep.Checked then
              stopComputation := true;
            // clauseLimit := n_clauses + deltalimit;
          end

          else // more than one solution
          begin
            if not SATKilled then
            begin
              Memo1.Lines.Add('Random cell ' + IntToStr(i) + ' is unremovable, '
                + IntToStr(givens + 1) + ' givens left. (' +
                FloatToStr((getTickcount - tme) / 1000) + ' s)');
              Memo1.Lines.Add('')
            end;
          end;
        end;
        if SATKilled then
        begin
          Memo1.Lines.Add('SAT Solver aborted!');
          Memo1.Lines.Add('')
        end;

        fixcells(removable, sym, rnd);
        // egal ob Zellen(n) entfernt wurden oder nicht
        // sie werden als unremovable markiert
      end;

      for j := 0 to DIM2 - 1 do
        rc_set[j] := rc_setsave[j];
      // in case of success rc_setsave holds the new
      // configuration. Else it holds the original configuration
    end;

    // clauseLimit := clauseLimit + deltalimit;
    alldone := true;
    for i := 0 to DIM2 - 1 do
      if removable[i] and (rc_set[i] <> 0) then
        alldone := false;
  until stopComputation or alldone;
  Memo1.Lines.Add(' ');
  initBitArraysFromGivens;
  PrintCurrentPuzzle;
  Memo1.Lines.Add('');
  Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
    ' candidates(pencilmarks).');
  if alldone then
    Memo1.Lines.Add('Puzzle is minimal- no other givens can be removed.');
  Memo1.Lines.Add('');
  stopComputation := false;
  BReduceBasic.Enabled := true;
  BReduceSAT.Enabled := true;
end;

// Button "Check solution" click
procedure TForm1.BCheckSolutionClick(Sender: TObject);
var
  i: Integer;
begin
  for i := 0 to DIM2 - 1 do
    Dec(rc_set[i]);
  try
    if n_error = 0 then
      Memo1.Lines.Add('Solution is valid!')
    else
      Memo1.Lines.Add('Solution is invalid!');
  finally
    for i := 0 to DIM2 - 1 do
      Inc(rc_set[i]);
  end;
end;

procedure rndpermute_band(bnd: Integer);
var
  a: array of Integer;
  band: array of array of Integer;
  i, j: Integer;
begin
  SetLength(a, B_ROW);
  SetLength(band, B_ROW, DIM);
  for i := 0 to B_ROW - 1 do
    a[i] := i;
  permuteArray(a);
  for i := 0 to B_ROW - 1 do
    for j := 0 to DIM - 1 do
      band[a[i], j] := rc_set[DIM * (bnd * B_ROW + i) + j];

  for i := 0 to B_ROW - 1 do
  begin
    for j := 0 to DIM - 1 do
    begin
      rc_set[DIM * (bnd * B_ROW + i) + j] := band[i, j];
    end;
  end;
end;

procedure rndpermute_bands_synchron;
var
  a: array of Integer;
  band: array of array of Integer;
  i, j, bnd: Integer;
begin
  SetLength(a, B_ROW);
  SetLength(band, B_ROW, DIM);
  for i := 0 to B_ROW - 1 do
    a[i] := i;
  permuteArray(a);

  for bnd := 0 to B_COL - 1 do
  begin
    for i := 0 to B_ROW - 1 do
      for j := 0 to DIM - 1 do
        band[a[i], j] := rc_set[DIM * (bnd * B_ROW + i) + j];

    for i := 0 to B_ROW - 1 do
    begin
      for j := 0 to DIM - 1 do
      begin
        rc_set[DIM * (bnd * B_ROW + i) + j] := band[i, j];
      end;
    end;
  end;
end;

procedure rndpermute_stack(stk: Integer);
var
  a: array of Integer;
  stack: array of array of Integer;
  i, j: Integer;
begin
  SetLength(a, B_COL);
  SetLength(stack, DIM, B_COL);
  for i := 0 to B_COL - 1 do
    a[i] := i;
  permuteArray(a);
  for i := 0 to B_COL - 1 do
    for j := 0 to DIM - 1 do
      stack[j, a[i]] := rc_set[DIM * j + stk * B_COL + i];

  for i := 0 to B_COL - 1 do
  begin
    for j := 0 to DIM - 1 do
    begin
      rc_set[DIM * j + stk * B_COL + i] := stack[j, i];
    end;
  end;

end;

procedure rndpermute_stacks_synchron;
var
  a: array of Integer;
  stack: array of array of Integer;
  i, j, stk: Integer;
begin
  SetLength(a, B_COL);
  SetLength(stack, DIM, B_COL);
  for i := 0 to B_COL - 1 do
    a[i] := i;
  permuteArray(a);

  for stk := 0 to B_ROW - 1 do
  begin
    for i := 0 to B_COL - 1 do
      for j := 0 to DIM - 1 do
        stack[j, a[i]] := rc_set[DIM * j + stk * B_COL + i];

    for i := 0 to B_COL - 1 do
    begin
      for j := 0 to DIM - 1 do
      begin
        rc_set[DIM * j + stk * B_COL + i] := stack[j, i];
      end;
    end;
  end;

end;

procedure rndReflect();
var
  a: array of array of Integer;
  i: Integer;
begin
  if Random(2) = 0 then
    Exit;
  SetLength(a, DIM, DIM);
  for i := 0 to DIM2 - 1 do
    a[i div DIM, i mod DIM] := rc_set[i];
  for i := 0 to DIM2 - 1 do
    rc_set[i] := a[i mod DIM, i div DIM];
end;

procedure rndpermute_bands();
var
  a: array of Integer;
  b: array of array of Integer;
  i, j, k: Integer;
begin
  SetLength(a, B_COL);
  SetLength(b, DIM, DIM);
  for i := 0 to B_COL - 1 do
    a[i] := i;
  permuteArray(a);
  for i := 0 to B_COL - 1 do // bands
    for j := 0 to B_ROW - 1 do // rows within band
      for k := 0 to DIM - 1 do // elements of row
        b[B_ROW * a[i] + j, k] := rc_set[DIM * (B_ROW * i + j) + k];
  for i := 0 to B_COL - 1 do
    for j := 0 to B_ROW - 1 do
      for k := 0 to DIM - 1 do
        rc_set[DIM * (B_ROW * i + j) + k] := b[B_ROW * i + j, k]
end;

procedure rndpermute_stacks();
var
  a: array of Integer;
  b: array of array of Integer;
  i, j, k: Integer;
begin
  SetLength(a, B_ROW);
  SetLength(b, DIM, DIM);
  for i := 0 to B_ROW - 1 do
    a[i] := i;
  permuteArray(a);

  // for i := 0 to B_ROW - 1 do
  // a[i] := B_ROW - 1 - i;

  for i := 0 to B_ROW - 1 do // stacks
    for j := 0 to B_COL - 1 do // columns within stack
      for k := 0 to DIM - 1 do // elements of column
        b[k, B_COL * a[i] + j] := rc_set[DIM * k + B_COL * i + j];
  for i := 0 to B_ROW - 1 do
    for j := 0 to B_COL - 1 do
      for k := 0 to DIM - 1 do
        rc_set[DIM * k + B_COL * i + j] := b[k, B_COL * i + j]
end;

procedure rndrelable();
var
  a: array of Integer;
  i: Integer;
begin
  SetLength(a, DIM);
  for i := 0 to DIM - 1 do
    a[i] := i;
  permuteArray(a);
  for i := 0 to DIM2 - 1 do
    if rc_set[i] <> 0 then
      rc_set[i] := a[rc_set[i] - 1] + 1;
end;

// Button "Shuffle grid" click
procedure TForm1.BPermuteClick(Sender: TObject);
var
  i: Integer;
begin

  // rndpermute_stacks;
  // PrintCurrentPuzzle;
  // Exit;

  if not(CheckSudokuX.Checked or CheckSudokuP.Checked) then
  begin
    for i := 0 to B_COL - 1 do
      rndpermute_band(i);
    for i := 0 to B_ROW - 1 do
      rndpermute_stack(i);
    if B_ROW = B_COL then
      rndReflect();
    rndpermute_bands;
    rndpermute_stacks();

  end;

  if CheckSudokuP.Checked then
  begin
    rndpermute_bands_synchron;
    rndpermute_stacks_synchron;
    if B_ROW = B_COL then
      rndReflect();
    rndpermute_bands;
    rndpermute_stacks;
  end;
  // Only operation for sudokuX
  rndrelable();
  PrintCurrentPuzzle;
end;

// Button "Show active puzzle" click
procedure TForm1.BPrintPuzzleClick(Sender: TObject);
begin
  PrintCurrentPuzzle;
  Memo1.Lines.Add(IntToStr(n_set) + ' givens, ' + IntToStr(DIM3 - n_cand_del) +
    ' candidates(pencilmarks).');
  Memo1.Lines.Add('');
end;

procedure TForm1.RbSymClick(Sender: TObject);
begin
  nochange := true;
  CheckDiagonal.Checked := false;
  CheckCenterLineHor.Checked := false;
  CheckCenterLineVer.Checked := false;
  nochange := false;
end;

procedure TForm1.CheckDiagonalClick(Sender: TObject);
begin
  if nochange then
    Exit;
  nochange := true;
  if RadioOneFold.Checked then
  begin
    CheckCenterLineVer.Checked := false;
    CheckCenterLineHor.Checked := false;
  end
  else if RadioTwoFold.Checked then
  begin
    CheckCenterLineVer.Checked := false;
    CheckCenterLineHor.Checked := false;
  end
  else if RadioFourFold.Checked then
    if CheckDiagonal.Checked then
    begin
      CheckCenterLineHor.Checked := true;
      CheckCenterLineVer.Checked := true;
    end
    else
    begin
      CheckCenterLineHor.Checked := false;
      CheckCenterLineVer.Checked := false;
    end;

  nochange := false;
end;

procedure TForm1.CheckCenterLineHorClick(Sender: TObject);
begin
  if nochange then
    Exit;
  nochange := true;
  if RadioOneFold.Checked then
  begin
    CheckDiagonal.Checked := false;
    CheckCenterLineVer.Checked := false;
  end
  else if RadioTwoFold.Checked then
  begin
    if CheckCenterLineHor.Checked then
    begin
      CheckCenterLineVer.Checked := true;
      CheckDiagonal.Checked := false;
    end
    else
      CheckCenterLineVer.Checked := false;
  end
  else if RadioFourFold.Checked then
    if CheckCenterLineHor.Checked then
    begin
      CheckCenterLineVer.Checked := true;
      CheckDiagonal.Checked := true;
    end
    else
    begin
      CheckCenterLineVer.Checked := false;
      CheckDiagonal.Checked := false;
    end;
  nochange := false;
end;

procedure TForm1.CheckCenterLineVerClick(Sender: TObject);
begin
  if nochange then
    Exit;
  nochange := true;
  if RadioOneFold.Checked then
  begin
    CheckDiagonal.Checked := false;
    CheckCenterLineHor.Checked := false;
  end
  else if RadioTwoFold.Checked then
  begin
    if CheckCenterLineVer.Checked then
    begin
      CheckCenterLineHor.Checked := true;
      CheckDiagonal.Checked := false;
    end
    else
      CheckCenterLineHor.Checked := false;
  end
  else if RadioFourFold.Checked then
    if CheckCenterLineVer.Checked then
    begin
      CheckCenterLineHor.Checked := true;
      CheckDiagonal.Checked := true;
    end
    else
    begin
      CheckCenterLineHor.Checked := false;
      CheckDiagonal.Checked := false;
    end;
  nochange := false;
end;

end.
