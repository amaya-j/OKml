open Lexing
open Interpreter.Lexer
open Interpreter.Parser

let string_of_token = function
  | LET -> "LET"
  | IN -> "IN"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | REC -> "REC"
  | FUN -> "FUN"
  | MATCH -> "MATCH"
  | WITH -> "WITH"
  | BOOL true -> "BOOL(true)"
  | BOOL false -> "BOOL(false)"
  | UNIT -> "UNIT"
  | CONS -> "::"
  | ARROW -> "->"
  | NEQ -> "<>"
  | GEQ -> ">="
  | LEQ -> "<="
  | AND -> "&&"
  | OR -> "||"
  | EQ -> "="
  | PLUS -> "+"
  | MINUS -> "-"
  | TIMES -> "*"
  | DIV -> "/"
  | LT -> "<"
  | GT -> ">"
  | LPAREN -> "("
  | RPAREN -> ")"
  | LBRACKET -> "["
  | RBRACKET -> "]"
  | COMMA -> ","
  | BAR -> "|"
  | IDENT id -> "IDENT(" ^ id ^ ")"
  | INT n -> "INT(" ^ string_of_int n ^ ")"
  | EOF -> "EOF"

let rec lex_all lexbuf =
  let tok = Lexer.tokenize lexbuf in
  match tok with
  | EOF -> [EOF]
  | t -> t :: lex_all lexbuf

let () =
  let input = "let rec f x = match x with [] -> true | y::ys -> false" in
  let lexbuf = from_string input in
  let tokens = lex_all lexbuf in
  print_endline "Tokens:";
  List.iter (fun t -> print_endline (string_of_token t)) tokens