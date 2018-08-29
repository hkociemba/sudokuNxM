object Form1: TForm1
  Left = 343
  Top = 300
  Anchors = []
  Caption = 'SATSudoku 0.95'
  ClientHeight = 741
  ClientWidth = 931
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -11
  Font.Name = 'Tahoma'
  Font.Style = []
  OldCreateOrder = False
  Position = poDesigned
  OnCreate = FormCreate
  DesignSize = (
    931
    741)
  PixelsPerInch = 96
  TextHeight = 13
  object Memo1: TMemo
    Left = 8
    Top = 0
    Width = 927
    Height = 540
    Anchors = [akLeft, akTop, akRight, akBottom]
    Font.Charset = DEFAULT_CHARSET
    Font.Color = clWindowText
    Font.Height = -11
    Font.Name = 'Fixedsys'
    Font.Style = []
    ParentFont = False
    PopupMenu = PopupMenu1
    ScrollBars = ssBoth
    TabOrder = 0
    WordWrap = False
  end
  object GroupBox1: TGroupBox
    Left = 321
    Top = 546
    Width = 203
    Height = 187
    Anchors = [akLeft, akBottom]
    Caption = 'Used methods'
    TabOrder = 1
    object Label3: TLabel
      Left = 154
      Top = 71
      Width = 41
      Height = 13
      Caption = 'Maxsize '
    end
    object Label4: TLabel
      Left = 154
      Top = 129
      Width = 38
      Height = 13
      Caption = 'Maxsize'
    end
    object Label5: TLabel
      Left = 154
      Top = 100
      Width = 41
      Height = 13
      Caption = 'Maxsize '
    end
    object Splitter2: TSplitter
      Left = 0
      Top = 154
      Width = 203
      Height = 3
      Align = alNone
      Beveled = True
    end
    object Splitter1: TSplitter
      Left = 0
      Top = 61
      Width = 203
      Height = 3
      Align = alNone
      Beveled = True
    end
    object CheckNakedSingles: TCheckBox
      Left = 114
      Top = 18
      Width = 97
      Height = 17
      Caption = 'Naked Singles'
      Checked = True
      State = cbChecked
      TabOrder = 0
    end
    object CheckHiddenSingles: TCheckBox
      Left = 16
      Top = 19
      Width = 97
      Height = 17
      Caption = 'Hidden Singles'
      Checked = True
      State = cbChecked
      TabOrder = 1
    end
    object CheckBlockLineInteraction: TCheckBox
      Left = 16
      Top = 40
      Width = 129
      Height = 17
      Caption = 'Box - Line Interaction'
      Checked = True
      State = cbChecked
      TabOrder = 2
    end
    object CheckNakedTuple: TCheckBox
      Left = 16
      Top = 99
      Width = 85
      Height = 17
      Caption = 'Naked Tuples'
      Checked = True
      State = cbChecked
      TabOrder = 3
    end
    object CheckHiddenTuple: TCheckBox
      Left = 16
      Top = 70
      Width = 97
      Height = 17
      Caption = 'Hidden Tuples'
      Checked = True
      State = cbChecked
      TabOrder = 4
    end
    object SpinEditMaxHiddenTuple: TSpinEdit
      Left = 107
      Top = 68
      Width = 41
      Height = 22
      MaxValue = 1000
      MinValue = 1
      PopupMenu = PopupMenu1
      TabOrder = 5
      Value = 3
    end
    object CheckSATSolver: TCheckBox
      Left = 16
      Top = 164
      Width = 184
      Height = 17
      Caption = 'SAT Solver'
      TabOrder = 6
    end
    object CheckBasicFish: TCheckBox
      Left = 16
      Top = 131
      Width = 97
      Height = 17
      Caption = 'Basic Fish'
      TabOrder = 7
    end
    object SpinEditMaxFish: TSpinEdit
      Left = 107
      Top = 126
      Width = 41
      Height = 22
      MaxValue = 1000
      MinValue = 1
      PopupMenu = PopupMenu1
      TabOrder = 8
      Value = 3
    end
    object SpinEditMaxNakedTuple: TSpinEdit
      Left = 107
      Top = 96
      Width = 41
      Height = 22
      MaxValue = 1000
      MinValue = 1
      PopupMenu = PopupMenu1
      TabOrder = 9
      Value = 3
      OnChange = SEMaxHiddenTupleChange
    end
  end
  object GroupBox2: TGroupBox
    Left = 10
    Top = 546
    Width = 137
    Height = 112
    Anchors = [akLeft, akBottom]
    Caption = 'Load from file'
    TabOrder = 2
    DesignSize = (
      137
      112)
    object Label2: TLabel
      Left = 65
      Top = 48
      Width = 6
      Height = 13
      Anchors = [akTop]
      Caption = 'x'
    end
    object Label1: TLabel
      Left = 37
      Top = 28
      Width = 68
      Height = 13
      Anchors = [akTop]
      Caption = 'Select boxsize'
    end
    object BLoad: TButton
      Left = 17
      Top = 76
      Width = 104
      Height = 25
      Anchors = [akTop]
      Caption = 'Load puzzle'
      TabOrder = 0
      OnClick = BLoadClick
    end
    object SpinEditRow: TSpinEdit
      Left = 18
      Top = 48
      Width = 41
      Height = 22
      Anchors = [akTop]
      MaxValue = 15
      MinValue = 1
      PopupMenu = PopupMenu1
      TabOrder = 1
      Value = 3
      OnChange = SpinEditRowChange
      OnEnter = SpinEditRowChange
    end
    object SpinEditCol: TSpinEdit
      Left = 77
      Top = 47
      Width = 41
      Height = 22
      Anchors = [akTop]
      MaxValue = 15
      MinValue = 1
      PopupMenu = PopupMenu1
      TabOrder = 2
      Value = 3
      OnChange = SpinEditColChange
      OnEnter = SpinEditColChange
    end
  end
  object GroupBox3: TGroupBox
    Left = 154
    Top = 546
    Width = 160
    Height = 187
    Anchors = [akLeft, akBottom]
    Caption = 'Solve'
    TabOrder = 3
    DesignSize = (
      160
      187)
    object BSATSolver: TButton
      Left = 17
      Top = 79
      Width = 123
      Height = 25
      Anchors = [akLeft, akBottom]
      Caption = 'Solve puzzle'
      Enabled = False
      TabOrder = 0
      OnClick = BSATSolverClick
    end
    object CheckVerbose: TCheckBox
      Left = 17
      Top = 19
      Width = 60
      Height = 15
      Caption = 'Verbose'
      TabOrder = 1
    end
    object CheckSudokuX: TCheckBox
      Left = 79
      Top = 19
      Width = 65
      Height = 15
      Anchors = [akLeft, akBottom]
      Caption = 'SudokuX'
      TabOrder = 2
    end
    object BCheckSolution: TButton
      Left = 17
      Top = 154
      Width = 123
      Height = 25
      Anchors = [akLeft, akBottom]
      Caption = 'Check Solution'
      TabOrder = 3
      OnClick = BCheckSolutionClick
    end
    object BAddSolution: TButton
      Left = 17
      Top = 110
      Width = 122
      Height = 25
      Anchors = [akLeft, akBottom]
      Caption = 'Find different solution'
      Enabled = False
      TabOrder = 4
      OnClick = BAddSolutionClick
    end
    object CheckSudokuP: TCheckBox
      Left = 79
      Top = 40
      Width = 97
      Height = 17
      Caption = 'SudokuP'
      TabOrder = 5
    end
  end
  object GroupBox4: TGroupBox
    Left = 530
    Top = 646
    Width = 239
    Height = 87
    Anchors = [akLeft, akBottom]
    Caption = 'Reduce puzzle'
    TabOrder = 4
    DesignSize = (
      239
      87)
    object BReduceBasic: TButton
      Left = 18
      Top = 25
      Width = 113
      Height = 25
      Anchors = [akLeft, akBottom]
      Caption = 'Use basic methods'
      Enabled = False
      TabOrder = 0
      OnClick = BReduceBasicClick
    end
    object BStop: TButton
      Left = 137
      Top = 25
      Width = 97
      Height = 25
      Anchors = [akLeft, akBottom]
      Caption = 'Stop Reduce'
      TabOrder = 1
      OnClick = BStopClick
    end
    object CheckSingleStep: TCheckBox
      Left = 143
      Top = 60
      Width = 74
      Height = 17
      Anchors = [akLeft, akBottom]
      Caption = 'Single step'
      TabOrder = 2
    end
    object BReduceSAT: TButton
      Left = 16
      Top = 56
      Width = 113
      Height = 25
      Caption = 'Use SAT method '
      Enabled = False
      TabOrder = 3
      OnClick = BReduceSATClick
    end
  end
  object GroupBox5: TGroupBox
    Left = 10
    Top = 662
    Width = 137
    Height = 71
    Anchors = [akLeft, akBottom]
    Caption = 'Miscellaneous '
    TabOrder = 5
    DesignSize = (
      137
      71)
    object BPrintPuzzle: TButton
      Left = 17
      Top = 40
      Width = 104
      Height = 26
      Anchors = [akLeft, akBottom]
      Caption = 'Show active puzzle'
      TabOrder = 0
      OnClick = BPrintPuzzleClick
    end
    object CheckOutlineBoxes: TCheckBox
      Left = 17
      Top = 20
      Width = 104
      Height = 14
      Anchors = [akLeft, akBottom]
      Caption = 'Outline Boxes'
      Checked = True
      State = cbChecked
      TabOrder = 1
    end
  end
  object GroupBox6: TGroupBox
    Left = 530
    Top = 546
    Width = 239
    Height = 102
    Anchors = [akLeft, akBottom]
    Caption = 'Symmetries'
    TabOrder = 6
    object CheckCenterLineHor: TCheckBox
      Left = 116
      Top = 21
      Width = 123
      Height = 17
      Caption = 'Center line horizontal '
      TabOrder = 0
      OnClick = CheckCenterLineHorClick
    end
    object CheckCenterLineVer: TCheckBox
      Left = 116
      Top = 44
      Width = 118
      Height = 17
      Caption = 'Center line vertical'
      TabOrder = 1
      OnClick = CheckCenterLineVerClick
    end
    object CheckDiagonal: TCheckBox
      Left = 116
      Top = 67
      Width = 123
      Height = 17
      Caption = 'Diagonal'
      TabOrder = 2
      OnClick = CheckDiagonalClick
    end
    object GroupBox7: TGroupBox
      Left = 8
      Top = 18
      Width = 91
      Height = 76
      Caption = 'Rotational'
      TabOrder = 3
      object RadioOneFold: TRadioButton
        Left = 9
        Top = 15
        Width = 113
        Height = 17
        Caption = '1-fold'
        Checked = True
        TabOrder = 0
        TabStop = True
        OnClick = RbSymClick
      end
      object RadioFourFold: TRadioButton
        Left = 9
        Top = 56
        Width = 113
        Height = 17
        Caption = '4-fold'
        TabOrder = 1
        OnClick = RbSymClick
      end
      object RadioTwoFold: TRadioButton
        Left = 9
        Top = 35
        Width = 113
        Height = 17
        Caption = '2-fold'
        TabOrder = 2
        OnClick = RbSymClick
      end
    end
  end
  object GroupBox8: TGroupBox
    Left = 775
    Top = 546
    Width = 149
    Height = 187
    Anchors = [akLeft, akBottom]
    Caption = 'Create Grid'
    TabOrder = 7
    object BCreate: TButton
      Left = 16
      Top = 48
      Width = 121
      Height = 25
      Caption = 'Random Grid'
      TabOrder = 0
      OnClick = BCreateClick
    end
    object BDefault: TButton
      Left = 16
      Top = 17
      Width = 121
      Height = 25
      Caption = 'Default Grid'
      TabOrder = 1
      OnClick = BDefaultClick
    end
    object BPermute: TButton
      Left = 16
      Top = 159
      Width = 113
      Height = 25
      Caption = 'Shuffle Grid'
      TabOrder = 2
      OnClick = BPermuteClick
    end
    object BLowClueGrid: TButton
      Left = 16
      Top = 95
      Width = 121
      Height = 25
      Caption = 'Few Clues Default Grid'
      TabOrder = 3
      OnClick = BLowClueGridClick
    end
  end
  object OpenDialog1: TOpenDialog
    Left = 160
    Top = 584
  end
  object PopupMenu1: TPopupMenu
    Left = 192
    Top = 584
    object Paste1: TMenuItem
      Caption = 'Paste'
      ShortCut = 16470
      OnClick = Paste1Click
    end
  end
end
