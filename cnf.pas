// ******************************************************************************
// Code to generate the clauses for an n*m sudoku for use in a cnf-file
// ******************************************************************************

unit cnf;

interface

uses Classes;

var
  n_clauses_eff: Integer;

function generate_cnf(clauses: TStringList): Integer;

procedure decode_solution(output, solution: TStringList);
function varname(r, c, v: Integer): String;

implementation

uses SysUtils, StrUtils, main;

// the variable name for a candidate in row r, column c and value v
// r>=0,x>=0, v>=1 and hence varname>=1.
function varname(r, c, v: Integer): String;
begin
  result := IntToStr(r * DIM * DIM + c * DIM + v);
end;

procedure decode_solution(output, solution: TStringList);
var
  a: array of array of Integer;
  i, r, c, v, n: Integer;
  solution_raw, s: String;
  solution_split: TArray<String>;
begin
  Setlength(a, DIM, DIM);
  solution_raw := '';
  for i := 0 to output.Count - 1 do
  begin
    s := output.Strings[i];
    if s[1] = 's' then
    begin
      if ContainsText(s, 'UNSATISFIABLE') then
      begin
        // Form1.Memo1.Lines.Add('Puzzle is unsolvable.');
        Exit;
      end;
      // Form1.Memo1.Lines.Add(copy(s, 3, Length(s)) + ':');
    end;

    if (s[1] = 'c') and ContainsText(s, 'Total wall clock time') then
    begin
      solution_split := custom_split(s);
      Form1.Memo1.Lines.Add(copy(s, 3, Length(s)));
    end;

    if s[1] = 'v' then
      solution_raw := solution_raw + copy(s, 3, Length(s));
  end;
  solution_split := custom_split(solution_raw);
  for i := 0 to Length(solution_split) - 1 do
    try
      n := StrToInt(solution_split[i]);
      // if Abs(n) > DIM * DIM * DIM then // eventually commander variables
      // continue;
      if n > 0 then
      begin
        v := (n - 1) mod DIM + 1;
        n := (n - 1) div DIM;
        c := n mod DIM;
        r := n div DIM;
        a[r, c] := v;
        rc_set[DIM * r + c] := v; // update puzzle definition
      end;
    except
      on EConvertError do
    end;

  for r := 0 to DIM - 1 do
  begin
    s := '';
    for c := 0 to DIM - 1 do
      if DIM < 10 then
        s := s + Format('%2d', [a[r, c]])
      else if DIM < 100 then
        s := s + Format('%3d', [a[r, c]])
      else if DIM < 1000 then
        s := s + Format('%4d', [a[r, c]]);
    solution.Add(s) // in the current version we do not use solution any more
  end;
end;

procedure cell_clauses(clauses: TStringList);
var
  row, col, num, num2: Integer;
  s: String;
begin
  for row := 0 to DIM - 1 do
    for col := 0 to DIM - 1 do
    begin
      if rc_set[DIM * row + col] = 0 then // cell not occupied
      begin
        // each cell contains at least one number, dim^2 clauses
        s := '';
        for num := 1 to DIM do // iterate over numbers
          if rcQ(row, col, num - 1) then
            s := s + varname(row, col, num) + ' ';
        if s = '' then // cnf is unsolvable, no candidates for this cell
          s := varname(row, col, 1) + ' '; // add arbitrary candidate
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end
      else
      begin // clause for already set number
        clauses.Add(varname(row, col, rc_set[DIM * row + col]) + ' 0');
        Inc(n_clauses_eff);
      end;
      // never two different numbers in one cell, dim^2*Binomial(dim,2) clauses
      // but if the candidate (r,c,num) or (r,c,num2) are deleted, the clause is unnecessary
      for num := 1 to DIM - 1 do
        if rcQ(row, col, num - 1) or (rc_set[DIM * row + col] = num) then
          for num2 := num + 1 to DIM do
            if rcQ(row, col, num2 - 1) or (rc_set[DIM * row + col] = num2) then
            begin
              clauses.Add('-' + varname(row, col, num) + ' -' + varname(row,
                col, num2) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
end;

procedure row_clauses(clauses: TStringList);
var
  row, col, col2, num: Integer;
  s: String;
begin
  for row := 0 to DIM - 1 do
    for num := 1 to DIM do
    begin
      // each row contains each number at least once, dim^2 clauses
      s := '';
      for col := 0 to DIM - 1 do // iterate over columns of row
        if rcQ(row, col, num - 1) then
          s := s + varname(row, col, num) + ' ';
      if s <> '' then
      begin
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end;
      // never two same numbers in one row, dim^2*Binomial(dim,2) clauses
      for col := 0 to DIM - 2 do
        if rcQ(row, col, num - 1) or (rc_set[DIM * row + col] = num) then
          for col2 := col + 1 to DIM - 1 do
            if rcQ(row, col2, num - 1) or (rc_set[DIM * row + col2] = num) then
            begin
              clauses.Add('-' + varname(row, col, num) + ' -' + varname(row,
                col2, num) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
end;

procedure column_clauses(clauses: TStringList);
var
  row, row2, col, num: Integer;
  s: String;
begin
  for col := 0 to DIM - 1 do
    for num := 1 to DIM do
    begin
      // each column contains each number at least once, dim^2 clauses
      s := '';
      for row := 0 to DIM - 1 do // iterate over rows of column
        if rcQ(row, col, num - 1) then
          s := s + varname(row, col, num) + ' ';
      if s <> '' then
      begin
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end;
      // never two same numbers in one column, dim^2*Binomial(dim,2) clauses
      for row := 0 to DIM - 2 do
        if rcQ(row, col, num - 1) or (rc_set[DIM * row + col] = num) then
          for row2 := row + 1 to DIM - 1 do
            if rcQ(row2, col, num - 1) or (rc_set[DIM * row2 + col] = num) then
            begin
              clauses.Add('-' + varname(row, col, num) + ' -' + varname(row2,
                col, num) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
end;

procedure block_clauses(clauses: TStringList);
var
  blk, k, k2, num: Integer;
  s: String;
begin
  for blk := 0 to DIM - 1 do // block
  begin
    for num := 1 to DIM do
    begin
      // each block contains each number at least once, dim^2 clauses
      s := '';
      for k := 0 to DIM - 1 do // iterate over block elements
        if rcQ(bk_to_r(blk, k), bk_to_c(blk, k), num - 1) then
          s := s + varname(bk_to_r(blk, k), bk_to_c(blk, k), num) + ' ';
      if s <> '' then
      begin
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end;
      // never two same numbers in same block, dim^2*Binomial(dim,2) clauses
      for k := 0 to DIM - 2 do
        if rcQ(bk_to_r(blk, k), bk_to_c(blk, k), num - 1) or
          (rc_set[DIM * bk_to_r(blk, k) + bk_to_c(blk, k)] = num) then
          for k2 := k + 1 to DIM - 1 do
            if rcQ(bk_to_r(blk, k2), bk_to_c(blk, k2), num - 1) or
              (rc_set[DIM * bk_to_r(blk, k2) + bk_to_c(blk, k2)] = num) then
            begin
              clauses.Add('-' + varname(bk_to_r(blk, k), bk_to_c(blk, k), num) +
                ' -' + varname(bk_to_r(blk, k2), bk_to_c(blk, k2), num) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
  end;
end;

// Positionen
procedure pos_clauses(clauses: TStringList);
var
  pos, blk, blk2, num: Integer;
  s: String;
begin
  for pos := 0 to DIM - 1 do // positions
  begin
    for num := 1 to DIM do
    begin
      // each pos contains each number at least once, dim^2 clauses
      s := '';
      for blk := 0 to DIM - 1 do // iterate over blocks
        if rcQ(bk_to_r(blk, pos), bk_to_c(blk, pos), num - 1) then
          s := s + varname(bk_to_r(blk, pos), bk_to_c(blk, pos), num) + ' ';
      if s <> '' then
      begin
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end;
      // never two same numbers in same position, dim^2*Binomial(dim,2) clauses
      for blk := 0 to DIM - 2 do
        if rcQ(bk_to_r(blk, pos), bk_to_c(blk, pos), num - 1) or
          (rc_set[DIM * bk_to_r(blk, pos) + bk_to_c(blk, pos)] = num) then
          for blk2 := blk + 1 to DIM - 1 do
            if rcQ(bk_to_r(blk2, pos), bk_to_c(blk2, pos), num - 1) or
              (rc_set[DIM * bk_to_r(blk2, pos) + bk_to_c(blk2, pos)] = num) then
            begin
              clauses.Add('-' + varname(bk_to_r(blk, pos), bk_to_c(blk, pos),
                num) + ' -' + varname(bk_to_r(blk2, pos), bk_to_c(blk2, pos),
                num) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
  end;
end;

//clauses for Windoku
procedure window_clauses(clauses: TStringList);
var
  win, k, k2, num: Integer;
  s: String;
begin
  for win := 0 to DIMWIN - 1 do // Window
  begin
    for num := 1 to DIM do
    begin
      // each window contains each number at least once, dim*dimwin clauses
      s := '';
      for k := 0 to DIM - 1 do // iterate over window elements
        if rcQ(wk_to_r(win, k), wk_to_c(win, k), num - 1) then
          s := s + varname(wk_to_r(win, k), wk_to_c(win, k), num) + ' ';
      if s <> '' then
      begin
        clauses.Add(s + '0');
        Inc(n_clauses_eff);
      end;
      // never two same numbers in same window, dim*dimwin*Binomial(dim,2) clauses
      for k := 0 to DIM - 2 do
        if rcQ(wk_to_r(win, k), wk_to_c(win, k), num - 1) or
          (rc_set[DIM * wk_to_r(win, k) + wk_to_c(win, k)] = num) then
          for k2 := k + 1 to DIM - 1 do
            if rcQ(wk_to_r(win, k2), wk_to_c(win, k2), num - 1) or
              (rc_set[DIM * wk_to_r(win, k2) + wk_to_c(win, k2)] = num) then
            begin
              clauses.Add('-' + varname(wk_to_r(win, k), wk_to_c(win, k), num) +
                ' -' + varname(wk_to_r(win, k2), wk_to_c(win, k2), num) + ' 0');
              Inc(n_clauses_eff);
            end;
    end;
  end;
end;



procedure XSudoku_clauses(clauses: TStringList);
var
  k, k2, num: Integer;
  s: String;
begin
  for num := 1 to DIM do
  begin
    s := '';
    for k := 0 to DIM - 1 do // iterate over diagonal
      if rcQ(k, k, num - 1) then
        s := s + varname(k, k, num) + ' ';
    if s <> '' then
    begin
      clauses.Add(s + '0');
      Inc(n_clauses_eff);
    end;

    s := '';
    for k := 0 to DIM - 1 do // iterate over antidiagonal
      if rcQ(DIM - 1 - k, k, num - 1) then
        s := s + varname(DIM - 1 - k, k, num) + ' ';
    if s <> '' then
    begin
      clauses.Add(s + '0');
      Inc(n_clauses_eff);
    end;

    for k := 0 to DIM - 2 do
      if rcQ(k, k, num - 1) or (rc_set[DIM * k + k] = num) then
        for k2 := k + 1 to DIM - 1 do
          if rcQ(k2, k2, num - 1) or (rc_set[DIM * k2 + k2] = num) then
          begin
            clauses.Add('-' + varname(k, k, num) + ' -' + varname(k2, k2,
              num) + ' 0');
            Inc(n_clauses_eff);
          end;
    for k := 0 to DIM - 2 do
      if rcQ(DIM - 1 - k, k, num - 1) or (rc_set[DIM * (DIM - 1 - k) + k] = num)
      then
        for k2 := k + 1 to DIM - 1 do
          if rcQ(DIM - 1 - k2, k2, num - 1) or
            (rc_set[DIM * (DIM - 1 - k2) + k2] = num) then
          begin
            clauses.Add('-' + varname(DIM - 1 - k, k, num) + ' -' +
              varname(DIM - 1 - k2, k2, num) + ' 0');
            Inc(n_clauses_eff);
          end;
  end;
end;

// generate cnf file in DIMACS format
function generate_cnf(clauses: TStringList): Integer;
var
  DIM, n_variables: Integer;
  n_clauses: UInt64;
begin
  n_clauses_eff := 0;
  DIM := B_ROW * B_COL;
  n_clauses := UInt64(4) * DIM * DIM * (DIM * (DIM - 1) div 2 + 1);
  n_variables := DIM * DIM * DIM;
  clauses.Clear;
  clauses.Add('c CNF file in DIMACS format');
  clauses.Add('c Unreduced the problem could have up to ' + IntToStr(n_clauses)
    + ' clauses');
  clauses.Add('dummy'); // clauses.Strings[2]
  cell_clauses(clauses);
  row_clauses(clauses);
  column_clauses(clauses);
  block_clauses(clauses);
  if Form1.CheckSudokuX.Checked then
    XSudoku_clauses(clauses);
  if Form1.CheckSudokuP.Checked then
    pos_clauses(clauses);
  if Form1.CheckSudokuW.Checked then
    window_clauses(clauses);

  clauses.Strings[2] := 'p cnf ' + IntToStr(n_variables) + ' ' +
    IntToStr(n_clauses_eff);
  result := n_clauses_eff;
end;

end.
