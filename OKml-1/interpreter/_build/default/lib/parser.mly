%{
  open Exp
%}

%token PLUS MINUS TIMES DIV
%token EQ NEQ LT GT LEQ GEQ
%token AND OR NOT
%token <int> INT
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

%right UMINUS NOT
%right APP
%left TIMES DIV
%left PLUS MINUS
%nonassoc EQ NEQ LT GT LEQ GEQ
%right CONS

%start <ast> parse
%%

let cons_expr :=
  | hd=exp3; CONS; tl=cons_expr { BinOp (Cons, hd, tl) }
  | e=exp3 { e }

let parse := 
  | e=exp0; EOF; { e }

let exp0 :=  (* let, fun, match, if — lowest precedence *)
  | LET; f=IDENT; x=IDENT; EQ; e1=exp0; IN; e2=exp0; { BinOp (Let f, UnOp (Fun x, e1), e2) }
  | LET; x=IDENT; EQ; e1=exp0; IN; e2=exp0; { BinOp (Let x, e1, e2) }
  | LET; REC; f=IDENT; x=IDENT; EQ; e1=exp0; IN; e2=exp0; { BinOp (LetRec(f, x), e1, e2) }
  | FUN; x=IDENT; ARROW; body=exp0; { UnOp (Fun x, body) }
  | IF; c=exp1; THEN; t=exp0; ELSE; e=exp0; { TrinOp (Cond, c, t, e) }
  | MATCH; e1=exp1; WITH; LPAREN; x=IDENT; COMMA; y=IDENT; RPAREN; ARROW; e2=exp0; { BinOp (MatchP(x, y), e1, e2) }
  | MATCH; e1=exp1; WITH; LBRACKET; RBRACKET; ARROW; e2=exp0; BAR; x=IDENT; CONS; xs=IDENT; ARROW; e3=exp0; { TrinOp (MatchL(x, xs), e1, e2, e3) }
  | e=exp1; { e }

let exp1 :=
  | a=exp2; op=comparator; b=exp2; { BinOp (op, a, b) }
  | e=exp2; { e }

let comparator :=
  | EQ;  { Eq }
  | NEQ; { Neq }
  | LT;  { Lt }
  | GT;  { Gt }
  | LEQ; { Leq }
  | GEQ; { Geq }

let exp2 := 
  | a=exp3; rest=cons_tail { rest a }

let cons_tail :=
  | CONS; b=exp3; rest=cons_tail { fun a -> rest (BinOp (Cons, a, b)) }
  | { fun a -> a }

let exp3 :=  (* and, or *)
  | a=exp3; AND; b=exp4 { BinOp (And, a, b) }
  | a=exp3; OR; b=exp4  { BinOp (Or, a, b) }
  | e=exp4 { e }

let exp4 :=  (* addition, subtraction *)
  | a=exp4; PLUS; b=exp5  { BinOp (Add, a, b) }
  | a=exp4; MINUS; b=exp5 { BinOp (Sub, a, b) }
  | e=exp5 { e }

let exp5 :=  (* multiplication, division *)
  | a=exp5; TIMES; b=exp6 { BinOp (Mul, a, b) }
  | a=exp5; DIV; b=exp6   { BinOp (Div, a, b) }
  | e=exp6 { e }

let exp6 :=
  | MINUS; e=exp6 %prec UMINUS { UnOp (Neg, e) }
  | NOT; e=exp6 %prec NOT      { UnOp (Not, e) }
  | f=exp6; a=exp7 %prec APP   { BinOp (App, f, a) }
  | e=exp7 { e }

let exp7 :=
  | x=IDENT           { Base (Var x) }
  | n=INT             { Base (Int n) }
  | b=BOOL            { Base (Bool b) }
  | UNIT              { Base (Unit) }
  | LBRACKET; RBRACKET { Base (Nil) }
  | LPAREN; e=exp0; RPAREN            { e }
  | LPAREN; a=exp0; COMMA; b=exp0; RPAREN { BinOp (Pair, a, b) }