open Lexing
open Interpreter.Type
open Interpreter.Lexer
open Interpreter.Parser
open Interpreter.Exp
open Interpreter.Typechecker

let parse_from_string s =
  let lexbuf = from_string s in
  try parse tokenize lexbuf
  with _ ->
    let curr = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error at line %d, column %d"
                curr.pos_lnum (curr.pos_cnum - curr.pos_bol))

let print_ty = function
  | Some ty -> print_endline ("Inferred type: " ^ string_of_ty ty)
  | None    -> print_endline "Type error"

let () =
  let inputs = [
    "1 + 2 * 3";
    "1 - 2 - 3";
    "-1 + 2";
    "not true && false";
    "true || false && false";
    "1 :: 2 :: []";
    "1 + 2 :: 3 :: []";
    "(1 + 2) * (3 + 4)";
    "let f x = x + 1 in f 2 + 3";
    "let f x = x + 1 in - f 3";
    "let f x = x in f (f (f 1))";
    "let x = 1 in let f y = y * 2 in not (x + f 3 > 6) && false";
    "let rec fact x = if x = 0 then 1 else x * fact (x - 1) in fact";
    "let rec fact x = if x = 0 then 1 else x * fact (x - 1) in fact 5";
    "let rec bad x = if x = 0 then true else x * bad (x - 1) in bad";
    "let y = 42 in let rec f x = if x = 0 then 1 else x * f (x - 1) in f y";
    "let p = (1, true) in match p with (x, y) -> x";
    "match [] with [] -> 0 | x :: xs -> x";
    "let add x = fun y -> x + y in add 3 4";
    "(fun x -> x + 1) 10";
  ] in

  List.iter (fun input ->
    print_endline ("Source: " ^ input);
    let ast = parse_from_string input in
    print_endline ("Parsed AST: " ^ string_of_ast ast);
    print_ty (infer ast);
    print_endline "----"
  ) inputs