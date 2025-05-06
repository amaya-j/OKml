
%{
    open Exp
%}

%token PLUS TIMES MINUS DIV
%token EQ NEQ LT GT LEQ GEQ
%token AND OR NOT

%token <int>INT
%token <string> IDENT
%token <bool> BOOL 

%token LET IN REC FUN ARROW
%token IF THEN ELSE
%token MATCH WITH
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token CONS
%token COMMA BAR

%token UNIT
%token EOF

%start <ast>parse
%%

let parse :=
    | a=exp; EOF; { a }

let exp :=
  | LET; x=IDENT; EQ; e1=exp; IN; e2=exp; { BinOp(Let x, e1, e2) }
  | LET; REC; f=IDENT; x=IDENT; EQ; e1=exp; IN; e2=exp; { BinOp(LetRec(f, x), e1, e2) }
  | FUN; x=IDENT; ARROW; body=exp; { UnOp(Fun x, body) }
  | IF; e1=exp; THEN; e2=exp; ELSE; e3=exp; { TrinOp(Cond, e1, e2, e3) }
  | MATCH; e1=exp; WITH; LPAREN; x=IDENT; COMMA; y=IDENT; RPAREN; ARROW; e2=exp;  { BinOp(MatchP(x, y), e1, e2) }
  | MATCH; e1=exp; WITH; LBRACKET; RBRACKET; ARROW; e2=exp; BAR; x=IDENT; CONS; xs=IDENT; ARROW; e3=exp; { TrinOp(MatchL(x, xs), e1, e2, e3) }
  | a=exp0; { a }

let exp0 :=
  | a=exp0; EQ; b=exp1; { BinOp(Eq, a, b) }
  | a=exp0; NEQ; b=exp1; { BinOp(Neq, a, b) }
  | a=exp0; LT; b=exp1; { BinOp(Lt, a, b) }
  | a=exp0; GT; b=exp1; { BinOp(Gt, a, b) }
  | a=exp0; LEQ; b=exp1; { BinOp(Leq, a, b) }
  | a=exp0; GEQ; b=exp1; { BinOp(Geq, a, b) }
  | a=exp1; { a }

let exp1 :=
  | a=exp1; AND; b=exp2; { BinOp(And, a, b) }
  | a=exp1; OR; b=exp2; { BinOp(Or, a, b) }
  | a=exp2; { a }

let exp2 :=
  | a=exp2; PLUS; b=exp3; { BinOp(Add, a, b) }
  | a=exp2; MINUS; b=exp3; { BinOp(Sub, a, b) }
  | a=exp3; { a }

let exp3 :=
  | a=exp3; TIMES; b=exp4; { BinOp(Mul, a, b) }
  | a=exp3; DIV; b=exp4; { BinOp(Div, a, b) }
  | a=exp4; { a }

let exp4 :=
  | a=exp5; b=exp5; { BinOp(App, a, b) }
  | a=exp5; { a }

let exp5 :=
  | b=BOOL; { Base(Bool b) }
  | x=IDENT; { Base(Var x) }
  | n=INT; { Base(Int n) }
  | LPAREN; a=exp; RPAREN; { a }
  | UNIT; { Base(Unit) }
  | LBRACKET; RBRACKET; { Base(Nil) }
  | a=exp; CONS; b=exp5; { BinOp(Cons, a, b) }
  | LPAREN; a=exp; COMMA; b=exp; RPAREN; { BinOp(Pair, a, b) }
  | NOT; e=exp5; { UnOp(Not, e) }
  | MINUS; e=exp5; { UnOp(Neg, e) }

