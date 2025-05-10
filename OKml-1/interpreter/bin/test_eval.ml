open Lexing
open Interpreter.Exp
open Interpreter.Parser
open Interpreter.Lexer
open Interpreter.Opt
open Interpreter.Eval
open Interpreter.Typechecker  (* Make sure this module contains your 'infer' function *)
open Interpreter.Type       (* Assumes this contains your 'ty' type and 'to_string' *)

let parse_from_string s =
  let lexbuf = from_string s in
  try parse tokenize lexbuf
  with _ ->
    let curr = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error at line %d, column %d"
                curr.pos_lnum (curr.pos_cnum - curr.pos_bol))

let show_result v =
  print_endline ("Evaluated: " ^ string_of_ast v)

let () =
  let inputs = [
    "1 / 0";
    "(fun x -> x) = (fun y -> y)";
    "true || (1 / 0)";
    "false && (1 / 0)";
    "let p = (1, 2) in match p :: [] with [] -> 0 | x :: xs -> match x with (a, b) -> a + b";
    "if false && (1 / 0 = 1) then 1 else 0";
    "1 + 2 * 3";
    "let x = 3 in x + 4";
    "if true then 1 else 0";
    "let x = 2 in let y = 3 in x * y";
    "let f = fun x -> x + 1 in f 5";
    "let rec fact x = if x = 0 then 1 else x * fact (x - 1) in fact 5";
    "let rec id x = x in id 42";
    "match [] with [] -> 1 | x :: xs -> 2";
    "match (1 :: []) with [] -> 0 | x :: xs -> x";
    "match (1 :: 2 :: []) with [] -> 0 | x :: xs -> x + 10";
    "let p = (1, 2) in match p with (x, y) -> x + y";
    "match (3 + 1, 5) with (x, y) -> x * y";
    "let rec sum xs = match xs with [] -> 0 | x :: xt -> x + sum xt in sum (1 :: 2 :: 3 :: [])";
    "let f = fun p -> match p with (x, y) -> x * y in f (4, 5)";
    "if 3 < 5 then 1 else 0";
    "if 10 >= 10 then 42 else 0";
  ] in

  List.iter (fun input ->
    print_endline ("Source: " ^ input);
    let parsed = parse_from_string input in
    print_endline ("AST: " ^ string_of_ast parsed);
    let optimized = constProp parsed in
    print_endline ("Optimized: " ^ string_of_ast optimized);

    match infer optimized with
    | Some ty ->
        print_endline ("Inferred type: " ^ string_of_ty ty);  (* Optional *)
        begin
          try
            let result = eval optimized in
            show_result result
          with
          | Failure msg -> Printf.printf "Failure: %s\n" msg
          | exn -> Printf.printf "Runtime error: %s\n" (Printexc.to_string exn)
        end
    | None ->
        print_endline "Type error: program is not well-typed"

  ) inputs