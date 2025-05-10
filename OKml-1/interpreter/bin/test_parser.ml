open Lexing
open Interpreter.Lexer
open Interpreter.Parser
open Interpreter.Exp  (* for string_of_ast *)

let parse_from_string s =
  let lexbuf = from_string s in
  try
    let ast = parse tokenize lexbuf in
    print_endline ("Parsed AST: " ^ string_of_ast ast)
  with
  | Error ->
      let curr = lexbuf.lex_curr_p in
      Printf.eprintf "Syntax error at line %d, column %d\n" curr.pos_lnum (curr.pos_cnum - curr.pos_bol)

let () =
  let inputs = [
    "let x = 3 + 4 in x * 2";
    "if x < 5 then true else false";
    "fun x -> x + 1";
    "match x with [] -> false | y::ys -> true";
    "not false";
    "x + y * 3";
    "(1, 2)";
    "match p with (a, b) -> a";
    "[ ]";
    "1 :: 2 :: []";
    "let rec fact x = if x = 0 then 1 else x * fact (x - 1) in fact 5";
    "let x = 5 in let y = x + 2 in y * y";
    "if (x = 0) then [] else x :: f (x - 1)";
  ] in

  let failing_inputs = [
    "not";
    "fun -> x";
    "let = 3 in 4";
    "let rec f x = x in in x";
    "match x with [] -> | y::ys -> y";
    "match x with (a b) -> a";
    "if x then y else";
    "1 + * 2";
    "(1, )";
    "true false";
    "[1; 2]";
  ] in

  List.iter (fun input ->
    print_endline ("Source: " ^ input);
    parse_from_string input;
    print_endline "----"
  ) inputs;

  List.iter (fun input ->
    print_endline ("Expect failure on: " ^ input);
    parse_from_string input;
    print_endline "----"
  ) failing_inputs