
(* The type of tokens. *)

type token = 
  | WITH
  | UNIT
  | TIMES
  | THEN
  | RPAREN
  | REC
  | RBRACKET
  | PLUS
  | OR
  | NOT
  | NEQ
  | MINUS
  | MATCH
  | LT
  | LPAREN
  | LET
  | LEQ
  | LBRACKET
  | INT of (int)
  | IN
  | IF
  | IDENT of (string)
  | GT
  | GEQ
  | FUN
  | EQ
  | EOF
  | ELSE
  | DIV
  | CONS
  | COMMA
  | BOOL of (bool)
  | BAR
  | ARROW
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val parse: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Exp.ast)
