open Lexing
open Interpreter.Lexer
open Interpreter.Parser
open Interpreter.Exp
open Interpreter.Opt

let parse_from_string s =
  let lexbuf = from_string s in
  try parse tokenize lexbuf
  with _ ->
    let curr = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error at line %d, column %d"
                curr.pos_lnum (curr.pos_cnum - curr.pos_bol))

let show_ast ast =
  print_endline ("Optimized AST: " ^ string_of_ast ast)

let () = 
  let inputs = [
    (* Constant arithmetic folding *)
    "1 + 2";             (* → 3 *)
    "4 - 1";             (* → 3 *)
    "3 * 3";             (* → 9 *)
    "8 / 2";             (* → 4 *)
  
    (* Avoid division by zero *)
    "5 / 0";             (* → should not fold *)
  
    (* Partial folding should not happen *)
    "x + 1";             (* unchanged *)
    "1 + x";             (* unchanged *)
    "x * y";             (* unchanged *)
  
    (* Folding inside expressions *)
    "1 + 2 + x";         (* left subexpr folds: → 3 + x *)
    "x + 3 * 4";         (* right subexpr folds: → x + 12 *)
    "x + (1 + 2)";       (* parens should fold: → x + 3 *)
  
    (* Nesting *)
    "1 + 2 + 3";         (* → 6 *)
    "(1 + 2) * (3 + 4)"; (* → 3 * 7 → 21 *)
    ] in

  List.iter (fun input ->
    print_endline ("Source: " ^ input);
    let ast = parse_from_string input in
    let optimized = constProp ast in
    show_ast optimized;
    print_endline "----"
  ) inputs