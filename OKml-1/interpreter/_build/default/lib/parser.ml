
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
    | INT of (
# 8 "lib/parser.mly"
       (int)
# 33 "lib/parser.ml"
  )
    | IN
    | IF
    | IDENT of (
# 9 "lib/parser.mly"
       (string)
# 40 "lib/parser.ml"
  )
    | GT
    | GEQ
    | FUN
    | EQ
    | EOF
    | ELSE
    | DIV
    | CONS
    | COMMA
    | BOOL of (
# 10 "lib/parser.mly"
       (bool)
# 54 "lib/parser.ml"
  )
    | BAR
    | ARROW
    | AND
  
end

include MenhirBasics

# 1 "lib/parser.mly"
  
  open Exp

# 68 "lib/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_parse) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: parse. *)

  | MenhirState02 : (('s, _menhir_box_parse) _menhir_cell1_NOT, _menhir_box_parse) _menhir_state
    (** State 02.
        Stack shape : NOT.
        Start symbol: parse. *)

  | MenhirState03 : (('s, _menhir_box_parse) _menhir_cell1_MINUS, _menhir_box_parse) _menhir_state
    (** State 03.
        Stack shape : MINUS.
        Start symbol: parse. *)

  | MenhirState04 : (('s, _menhir_box_parse) _menhir_cell1_LPAREN, _menhir_box_parse) _menhir_state
    (** State 04.
        Stack shape : LPAREN.
        Start symbol: parse. *)

  | MenhirState05 : (('s, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_state
    (** State 05.
        Stack shape : MATCH.
        Start symbol: parse. *)

  | MenhirState12 : (('s, _menhir_box_parse) _menhir_cell1_exp6, _menhir_box_parse) _menhir_state
    (** State 12.
        Stack shape : exp6.
        Start symbol: parse. *)

  | MenhirState16 : (('s, _menhir_box_parse) _menhir_cell1_exp4, _menhir_box_parse) _menhir_state
    (** State 16.
        Stack shape : exp4.
        Start symbol: parse. *)

  | MenhirState18 : (('s, _menhir_box_parse) _menhir_cell1_exp4, _menhir_box_parse) _menhir_state
    (** State 18.
        Stack shape : exp4.
        Start symbol: parse. *)

  | MenhirState21 : (('s, _menhir_box_parse) _menhir_cell1_exp3, _menhir_box_parse) _menhir_state
    (** State 21.
        Stack shape : exp3.
        Start symbol: parse. *)

  | MenhirState23 : (('s, _menhir_box_parse) _menhir_cell1_exp3, _menhir_box_parse) _menhir_state
    (** State 23.
        Stack shape : exp3.
        Start symbol: parse. *)

  | MenhirState26 : (('s, _menhir_box_parse) _menhir_cell1_exp2, _menhir_box_parse) _menhir_state
    (** State 26.
        Stack shape : exp2.
        Start symbol: parse. *)

  | MenhirState34 : (('s, _menhir_box_parse) _menhir_cell1_exp2, _menhir_box_parse) _menhir_state
    (** State 34.
        Stack shape : exp2.
        Start symbol: parse. *)

  | MenhirState36 : (('s, _menhir_box_parse) _menhir_cell1_exp2, _menhir_box_parse) _menhir_state
    (** State 36.
        Stack shape : exp2.
        Start symbol: parse. *)

  | MenhirState38 : (('s, _menhir_box_parse) _menhir_cell1_exp2 _menhir_cell0_comparator, _menhir_box_parse) _menhir_state
    (** State 38.
        Stack shape : exp2 comparator.
        Start symbol: parse. *)

  | MenhirState47 : ((('s, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1 _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 47.
        Stack shape : MATCH exp1 IDENT IDENT.
        Start symbol: parse. *)

  | MenhirState52 : (('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 52.
        Stack shape : LET IDENT IDENT.
        Start symbol: parse. *)

  | MenhirState53 : (('s, _menhir_box_parse) _menhir_cell1_IF, _menhir_box_parse) _menhir_state
    (** State 53.
        Stack shape : IF.
        Start symbol: parse. *)

  | MenhirState55 : ((('s, _menhir_box_parse) _menhir_cell1_IF, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_state
    (** State 55.
        Stack shape : IF exp1.
        Start symbol: parse. *)

  | MenhirState58 : (('s, _menhir_box_parse) _menhir_cell1_FUN _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 58.
        Stack shape : FUN IDENT.
        Start symbol: parse. *)

  | MenhirState62 : (((('s, _menhir_box_parse) _menhir_cell1_IF, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_cell1_exp0, _menhir_box_parse) _menhir_state
    (** State 62.
        Stack shape : IF exp1 exp0.
        Start symbol: parse. *)

  | MenhirState65 : ((('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0, _menhir_box_parse) _menhir_state
    (** State 65.
        Stack shape : LET IDENT IDENT exp0.
        Start symbol: parse. *)

  | MenhirState69 : (('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 69.
        Stack shape : LET IDENT IDENT.
        Start symbol: parse. *)

  | MenhirState71 : ((('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0, _menhir_box_parse) _menhir_state
    (** State 71.
        Stack shape : LET IDENT IDENT exp0.
        Start symbol: parse. *)

  | MenhirState73 : (('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 73.
        Stack shape : LET IDENT.
        Start symbol: parse. *)

  | MenhirState75 : ((('s, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0, _menhir_box_parse) _menhir_state
    (** State 75.
        Stack shape : LET IDENT exp0.
        Start symbol: parse. *)

  | MenhirState80 : ((('s, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_state
    (** State 80.
        Stack shape : MATCH exp1.
        Start symbol: parse. *)

  | MenhirState86 : (((('s, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_cell1_exp0 _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_state
    (** State 86.
        Stack shape : MATCH exp1 exp0 IDENT IDENT.
        Start symbol: parse. *)

  | MenhirState90 : ((('s, _menhir_box_parse) _menhir_cell1_LPAREN, _menhir_box_parse) _menhir_cell1_exp0, _menhir_box_parse) _menhir_state
    (** State 90.
        Stack shape : LPAREN exp0.
        Start symbol: parse. *)


and 's _menhir_cell0_comparator = 
  | MenhirCell0_comparator of 's * (Exp.binOp)

and ('s, 'r) _menhir_cell1_exp0 = 
  | MenhirCell1_exp0 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_exp1 = 
  | MenhirCell1_exp1 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_exp2 = 
  | MenhirCell1_exp2 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_exp3 = 
  | MenhirCell1_exp3 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_exp4 = 
  | MenhirCell1_exp4 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_exp6 = 
  | MenhirCell1_exp6 of 's * ('s, 'r) _menhir_state * (Exp.ast)

and ('s, 'r) _menhir_cell1_FUN = 
  | MenhirCell1_FUN of 's * ('s, 'r) _menhir_state

and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * (
# 9 "lib/parser.mly"
       (string)
# 240 "lib/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MATCH = 
  | MenhirCell1_MATCH of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state

and _menhir_box_parse = 
  | MenhirBox_parse of (Exp.ast) [@@unboxed]

let _menhir_action_01 =
  fun _1 ->
    (
# 49 "lib/parser.mly"
         ( Eq )
# 269 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_02 =
  fun _1 ->
    (
# 50 "lib/parser.mly"
         ( Neq )
# 277 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_03 =
  fun _1 ->
    (
# 51 "lib/parser.mly"
         ( Lt )
# 285 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_04 =
  fun _1 ->
    (
# 52 "lib/parser.mly"
         ( Gt )
# 293 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_05 =
  fun _1 ->
    (
# 53 "lib/parser.mly"
         ( Leq )
# 301 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_06 =
  fun _1 ->
    (
# 54 "lib/parser.mly"
         ( Geq )
# 309 "lib/parser.ml"
     : (Exp.binOp))

let _menhir_action_07 =
  fun _1 _4 _6 e1 e2 f x ->
    (
# 35 "lib/parser.mly"
                                                     ( BinOp (Let f, UnOp (Fun x, e1), e2) )
# 317 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_08 =
  fun _1 _3 _5 e1 e2 x ->
    (
# 36 "lib/parser.mly"
                                            ( BinOp (Let x, e1, e2) )
# 325 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_09 =
  fun _1 _2 _5 _7 e1 e2 f x ->
    (
# 37 "lib/parser.mly"
                                                          ( BinOp (LetRec(f, x), e1, e2) )
# 333 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_10 =
  fun _1 _3 body x ->
    (
# 38 "lib/parser.mly"
                                    ( UnOp (Fun x, body) )
# 341 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_11 =
  fun _1 _3 _5 c e t ->
    (
# 39 "lib/parser.mly"
                                            ( TrinOp (Cond, c, t, e) )
# 349 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_12 =
  fun _1 _3 _4 _6 _8 _9 e1 e2 x y ->
    (
# 40 "lib/parser.mly"
                                                                                   ( BinOp (MatchP(x, y), e1, e2) )
# 357 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_13 =
  fun _1 _10 _12 _3 _4 _5 _6 _8 e1 e2 e3 x xs ->
    (
# 41 "lib/parser.mly"
                                                                                                            ( TrinOp (MatchL(x, xs), e1, e2, e3) )
# 365 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_14 =
  fun e ->
    (
# 42 "lib/parser.mly"
            ( e )
# 373 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_15 =
  fun a b op ->
    (
# 45 "lib/parser.mly"
                                   ( BinOp (op, a, b) )
# 381 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_16 =
  fun e ->
    (
# 46 "lib/parser.mly"
            ( e )
# 389 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_17 =
  fun _2 a b ->
    (
# 57 "lib/parser.mly"
                          ( BinOp (Cons, a, b) )
# 397 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_18 =
  fun _2 a b ->
    (
# 58 "lib/parser.mly"
                         ( BinOp (And, a, b) )
# 405 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_19 =
  fun _2 a b ->
    (
# 59 "lib/parser.mly"
                        ( BinOp (Or, a, b) )
# 413 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_20 =
  fun e ->
    (
# 60 "lib/parser.mly"
            ( e )
# 421 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_21 =
  fun _2 a b ->
    (
# 63 "lib/parser.mly"
                          ( BinOp (Add, a, b) )
# 429 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_22 =
  fun _2 a b ->
    (
# 64 "lib/parser.mly"
                           ( BinOp (Sub, a, b) )
# 437 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_23 =
  fun e ->
    (
# 65 "lib/parser.mly"
            ( e )
# 445 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_24 =
  fun _2 a b ->
    (
# 68 "lib/parser.mly"
                           ( BinOp (Mul, a, b) )
# 453 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_25 =
  fun _2 a b ->
    (
# 69 "lib/parser.mly"
                         ( BinOp (Div, a, b) )
# 461 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_26 =
  fun e ->
    (
# 70 "lib/parser.mly"
            ( e )
# 469 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_27 =
  fun _1 e ->
    (
# 73 "lib/parser.mly"
                                ( UnOp (Neg, e) )
# 477 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_28 =
  fun _1 e ->
    (
# 74 "lib/parser.mly"
                              ( UnOp (Not, e) )
# 485 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_29 =
  fun e ->
    (
# 75 "lib/parser.mly"
            ( e )
# 493 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_30 =
  fun a f ->
    (
# 78 "lib/parser.mly"
                              ( BinOp (App, f, a) )
# 501 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_31 =
  fun e ->
    (
# 79 "lib/parser.mly"
            ( e )
# 509 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_32 =
  fun x ->
    (
# 82 "lib/parser.mly"
             ( Base (Var x) )
# 517 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_33 =
  fun n ->
    (
# 83 "lib/parser.mly"
           ( Base (Int n) )
# 525 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_34 =
  fun b ->
    (
# 84 "lib/parser.mly"
            ( Base (Bool b) )
# 533 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_35 =
  fun _1 ->
    (
# 85 "lib/parser.mly"
          ( Base (Unit) )
# 541 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_36 =
  fun _1 _2 ->
    (
# 86 "lib/parser.mly"
                        ( Base (Nil) )
# 549 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_37 =
  fun _1 _3 a ->
    (
# 87 "lib/parser.mly"
                            ( a )
# 557 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_38 =
  fun _1 _3 _5 a b ->
    (
# 88 "lib/parser.mly"
                                           ( BinOp (Pair, a, b) )
# 565 "lib/parser.ml"
     : (Exp.ast))

let _menhir_action_39 =
  fun _2 e ->
    (
# 32 "lib/parser.mly"
                 ( e )
# 573 "lib/parser.ml"
     : (Exp.ast))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AND ->
        "AND"
    | ARROW ->
        "ARROW"
    | BAR ->
        "BAR"
    | BOOL _ ->
        "BOOL"
    | COMMA ->
        "COMMA"
    | CONS ->
        "CONS"
    | DIV ->
        "DIV"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | FUN ->
        "FUN"
    | GEQ ->
        "GEQ"
    | GT ->
        "GT"
    | IDENT _ ->
        "IDENT"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | INT _ ->
        "INT"
    | LBRACKET ->
        "LBRACKET"
    | LEQ ->
        "LEQ"
    | LET ->
        "LET"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MATCH ->
        "MATCH"
    | MINUS ->
        "MINUS"
    | NEQ ->
        "NEQ"
    | NOT ->
        "NOT"
    | OR ->
        "OR"
    | PLUS ->
        "PLUS"
    | RBRACKET ->
        "RBRACKET"
    | REC ->
        "REC"
    | RPAREN ->
        "RPAREN"
    | THEN ->
        "THEN"
    | TIMES ->
        "TIMES"
    | UNIT ->
        "UNIT"
    | WITH ->
        "WITH"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_96 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _v _tok ->
      match (_tok : MenhirBasics.token) with
      | EOF ->
          let (_2, e) = ((), _v) in
          let _v = _menhir_action_39 _2 e in
          MenhirBox_parse _v
      | _ ->
          _eRR ()
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = () in
      let _v = _menhir_action_35 _1 in
      _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_exp7 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState12 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState00 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState02 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState26 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState18 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState16 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_13 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp6 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp6 (_menhir_stack, _menhir_s, f) = _menhir_stack in
      let a = _v in
      let _v = _menhir_action_30 a f in
      _menhir_goto_exp6 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_exp6 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
      | LPAREN ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
      | INT _v_0 ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState12
      | IDENT _v_1 ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState12
      | BOOL _v_2 ->
          let _menhir_stack = MenhirCell1_exp6 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState12
      | AND | BAR | COMMA | CONS | DIV | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | THEN | TIMES | WITH ->
          let e = _v in
          let _v = _menhir_action_29 e in
          _menhir_goto_exp5 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState04 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUN ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState02 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState03 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_1, _2) = ((), ()) in
          let _v = _menhir_action_36 _1 _2 in
          _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let n = _v in
      let _v = _menhir_action_33 n in
      _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_09 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let x = _v in
      let _v = _menhir_action_32 x in
      _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_10 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let b = _v in
      let _v = _menhir_action_34 b in
      _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_05 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState05 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_48 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | REC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | EQ ->
                      let _menhir_s = MenhirState52 in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | UNIT ->
                          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | NOT ->
                          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | MINUS ->
                          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | MATCH ->
                          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LPAREN ->
                          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LET ->
                          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LBRACKET ->
                          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | INT _v ->
                          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | IF ->
                          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | IDENT _v ->
                          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | FUN ->
                          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | BOOL _v ->
                          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | EQ ->
                  let _menhir_s = MenhirState69 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | UNIT ->
                      _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | NOT ->
                      _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | MINUS ->
                      _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | MATCH ->
                      _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LPAREN ->
                      _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LET ->
                      _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LBRACKET ->
                      _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT _v ->
                      _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | IF ->
                      _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | IDENT _v ->
                      _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | FUN ->
                      _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BOOL _v ->
                      _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | EQ ->
              let _menhir_s = MenhirState73 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | NOT ->
                  _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LBRACKET ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT _v ->
                  _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FUN ->
                  _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_53 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState53 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_56 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _menhir_s = MenhirState58 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | NOT ->
                  _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LBRACKET ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT _v ->
                  _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FUN ->
                  _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_exp5 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState02 ->
          _menhir_run_94 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState03 ->
          _menhir_run_93 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState18 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState16 ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState00 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState26 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_94 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e) = ((), _v) in
      let _v = _menhir_action_28 _1 e in
      _menhir_goto_exp5 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_93 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_MINUS -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e) = ((), _v) in
      let _v = _menhir_action_27 _1 e in
      _menhir_goto_exp5 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_19 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp4 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp4 (_menhir_stack, _menhir_s, a) = _menhir_stack in
      let (b, _2) = (_v, ()) in
      let _v = _menhir_action_25 _2 a b in
      _menhir_goto_exp4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_exp4 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState23 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState26 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_24 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp3 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | THEN | WITH ->
          let MenhirCell1_exp3 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let (b, _2) = (_v, ()) in
          let _v = _menhir_action_22 _2 a b in
          _menhir_goto_exp3 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_16 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp4 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState16 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp4 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState18 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_exp3 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState36 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState26 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_37 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | NEQ | OR | RPAREN | THEN | WITH ->
          let MenhirCell1_exp2 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let (b, _2) = (_v, ()) in
          let _v = _menhir_action_18 _2 a b in
          _menhir_goto_exp2 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_21 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp3 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState21 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp3 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState23 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_exp2 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState38 ->
          _menhir_run_39 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_39 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 _menhir_cell0_comparator as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | CONS ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | IN | RPAREN | THEN | WITH ->
          let MenhirCell0_comparator (_menhir_stack, op) = _menhir_stack in
          let MenhirCell1_exp2 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let b = _v in
          let _v = _menhir_action_15 a b op in
          _menhir_goto_exp1 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState26 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_34 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState34 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_36 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState36 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_exp1 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState90 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState80 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState75 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState73 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState69 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState55 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_59 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_59 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_14 e in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_exp0 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_96 _menhir_stack _v _tok
      | MenhirState90 ->
          _menhir_run_91 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState04 ->
          _menhir_run_88 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_87 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState80 ->
          _menhir_run_81 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_77 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState75 ->
          _menhir_run_76 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState73 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState71 ->
          _menhir_run_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState69 ->
          _menhir_run_70 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_66 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState52 ->
          _menhir_run_64 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState62 ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState55 ->
          _menhir_run_61 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState58 ->
          _menhir_run_60 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_91 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LPAREN, _menhir_box_parse) _menhir_cell1_exp0 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_exp0 (_menhir_stack, _, a) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let (_1, b, _5, _3) = ((), _v, (), ()) in
          let _v = _menhir_action_38 _1 _3 _5 a b in
          _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_88 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let (_1, a, _3) = ((), _v, ()) in
          let _v = _menhir_action_37 _1 _3 a in
          _menhir_goto_exp7 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState90 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_87 : type  ttv_stack. (((ttv_stack, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_cell1_exp0 _menhir_cell0_IDENT _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_IDENT (_menhir_stack, xs) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_exp0 (_menhir_stack, _, e2) = _menhir_stack in
      let MenhirCell1_exp1 (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e3, _12, _10, _8, _6, _5, _4, _3) = ((), _v, (), (), (), (), (), (), ()) in
      let _v = _menhir_action_13 _1 _10 _12 _3 _4 _5 _6 _8 e1 e2 e3 x xs in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_81 : type  ttv_stack. (((ttv_stack, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | BAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | CONS ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | IDENT _v ->
                      let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | ARROW ->
                          let _menhir_s = MenhirState86 in
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | UNIT ->
                              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | NOT ->
                              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | MINUS ->
                              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | MATCH ->
                              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | LPAREN ->
                              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | LET ->
                              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | LBRACKET ->
                              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | INT _v ->
                              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                          | IF ->
                              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | IDENT _v ->
                              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                          | FUN ->
                              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                          | BOOL _v ->
                              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_77 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_MATCH, _menhir_box_parse) _menhir_cell1_exp1 _menhir_cell0_IDENT _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_IDENT (_menhir_stack, y) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_exp1 (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, _8, e2, _6, _4, _3, _9) = ((), (), _v, (), (), (), ()) in
      let _v = _menhir_action_12 _1 _3 _4 _6 _8 _9 e1 e2 x y in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_76 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp0 (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e2, _5, _3) = ((), _v, (), ()) in
      let _v = _menhir_action_08 _1 _3 _5 e1 e2 x in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_74 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _menhir_s = MenhirState75 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_72 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp0 (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, f) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e2, _6, _4) = ((), _v, (), ()) in
      let _v = _menhir_action_07 _1 _4 _6 e1 e2 f x in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_70 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _menhir_s = MenhirState71 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_66 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_parse) _menhir_cell1_exp0 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp0 (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, f) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, _2, e2, _5, _7) = ((), (), _v, (), ()) in
      let _v = _menhir_action_09 _1 _2 _5 _7 e1 e2 f x in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_64 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_LET _menhir_cell0_IDENT _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IN ->
          let _menhir_s = MenhirState65 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_63 : type  ttv_stack. (((ttv_stack, _menhir_box_parse) _menhir_cell1_IF, _menhir_box_parse) _menhir_cell1_exp1, _menhir_box_parse) _menhir_cell1_exp0 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp0 (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_exp1 (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, e, _5, _3) = ((), _v, (), ()) in
      let _v = _menhir_action_11 _1 _3 _5 c e t in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_61 : type  ttv_stack. (((ttv_stack, _menhir_box_parse) _menhir_cell1_IF, _menhir_box_parse) _menhir_cell1_exp1 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp0 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_s = MenhirState62 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_60 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_FUN _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_IDENT (_menhir_stack, x) = _menhir_stack in
      let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
      let (_1, _3, body) = ((), (), _v) in
      let _v = _menhir_action_10 _1 _3 body x in
      _menhir_goto_exp0 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_54 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp1 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _menhir_s = MenhirState55 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FUN ->
              _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_40 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp1 (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | COMMA ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | IDENT _v ->
                          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | RPAREN ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              (match (_tok : MenhirBasics.token) with
                              | ARROW ->
                                  let _menhir_s = MenhirState47 in
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  (match (_tok : MenhirBasics.token) with
                                  | UNIT ->
                                      _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | NOT ->
                                      _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | MINUS ->
                                      _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | MATCH ->
                                      _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | LPAREN ->
                                      _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | LET ->
                                      _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | LBRACKET ->
                                      _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | INT _v ->
                                      _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                                  | IF ->
                                      _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | IDENT _v ->
                                      _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                                  | FUN ->
                                      _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                                  | BOOL _v ->
                                      _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                                  | _ ->
                                      _eRR ())
                              | _ ->
                                  _eRR ())
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | LBRACKET ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACKET ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | ARROW ->
                      let _menhir_s = MenhirState80 in
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | UNIT ->
                          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | NOT ->
                          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | MINUS ->
                          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | MATCH ->
                          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LPAREN ->
                          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LET ->
                          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | LBRACKET ->
                          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | INT _v ->
                          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | IF ->
                          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | IDENT _v ->
                          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | FUN ->
                          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                      | BOOL _v ->
                          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_25 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_02 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LT ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_03 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LEQ ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_05 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | GT ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_04 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | GEQ ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_06 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | EQ ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = () in
          let _v = _menhir_action_01 _1 in
          _menhir_goto_comparator _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | CONS ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_exp2 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | IN | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_16 e in
          _menhir_goto_exp1 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_comparator : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_comparator (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | INT _v_0 ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState38
      | IDENT _v_1 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState38
      | BOOL _v_2 ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState38
      | _ ->
          _eRR ()
  
  and _menhir_run_35 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | NEQ | OR | RPAREN | THEN | WITH ->
          let MenhirCell1_exp2 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let (b, _2) = (_v, ()) in
          let _v = _menhir_action_17 _2 a b in
          _menhir_goto_exp2 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_27 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp2 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | NEQ | OR | RPAREN | THEN | WITH ->
          let MenhirCell1_exp2 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let (b, _2) = (_v, ()) in
          let _v = _menhir_action_19 _2 a b in
          _menhir_goto_exp2 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_exp3 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | NEQ | OR | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_20 e in
          _menhir_goto_exp2 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_22 : type  ttv_stack. ((ttv_stack, _menhir_box_parse) _menhir_cell1_exp3 as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | THEN | WITH ->
          let MenhirCell1_exp3 (_menhir_stack, _menhir_s, a) = _menhir_stack in
          let (b, _2) = (_v, ()) in
          let _v = _menhir_action_21 _2 a b in
          _menhir_goto_exp3 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_15 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_exp4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | CONS | ELSE | EOF | EQ | GEQ | GT | IN | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | THEN | WITH ->
          let e = _v in
          let _v = _menhir_action_23 e in
          _menhir_goto_exp3 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_17 : type  ttv_stack. (ttv_stack, _menhir_box_parse) _menhir_cell1_exp4 -> _ -> _ -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_exp4 (_menhir_stack, _menhir_s, a) = _menhir_stack in
      let (b, _2) = (_v, ()) in
      let _v = _menhir_action_24 _2 a b in
      _menhir_goto_exp4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_14 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_26 e in
      _menhir_goto_exp4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_11 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_parse) _menhir_state -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_31 e in
      _menhir_goto_exp6 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_parse =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUN ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
end

let parse =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_parse v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
