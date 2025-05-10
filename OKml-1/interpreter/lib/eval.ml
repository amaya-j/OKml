(* author: Evan*)

open Exp

let rec sub (x : string) (v : ast) (e : ast) : ast =
  match e with
  | Base(Var y) -> if x = y then v else e
  | Base _ -> e
  | UnOp(op, e1) -> UnOp(op, sub x v e1)
  | BinOp(op, e1, e2) -> BinOp(op, sub x v e1, sub x v e2)
  | TrinOp(op, e1, e2, e3) -> TrinOp(op, sub x v e1, sub x v e2, sub x v e3)


let rec is_value = function
  | Base(Int _) | Base(Bool _) | Base(Unit) | Base(Nil) -> true
  | UnOp(Fun _, _) | UnOp(RecFun _, _) -> true
  | BinOp(Cons, v1, v2) -> is_value v1 && is_value v2
  | BinOp(Pair, v1, v2) -> is_value v1 && is_value v2
  | _ -> false

let rec step (e : ast) : ast option =
  match e with

  (* not *)
  | UnOp(Not, Base(Bool b)) -> Some (Base(Bool(not b)))
  | UnOp(Not, e1) -> 
    (match step e1 with
    | Some e1' -> Some (UnOp(Not, e1'))
    | None -> None)

  (*    +, -, /, *    *)
  | BinOp(Add, Base(Int a), Base(Int b)) -> Some (Base(Int (a + b)))
  | BinOp(Add, e1, e2) when not (is_value e1) ->
    (match step e1 with
    | Some e1' -> Some (BinOp(Add, e1', e2))
    | None -> None)
  | BinOp(Add, v1, e2) when is_value v1 ->
    (match step e2 with
    | Some e2' -> Some (BinOp(Add, v1, e2'))
    | None -> None)

  | BinOp(Sub, Base(Int a), Base(Int b)) -> Some (Base(Int (a - b)))
  | BinOp(Sub, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Sub, e1', e2))
     | None -> None)
  | BinOp(Sub, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Sub, v1, e2'))
     | None -> None)

  | BinOp(Mul, Base(Int a), Base(Int b)) -> Some (Base(Int (a * b)))
  | BinOp(Mul, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Mul, e1', e2))
     | None -> None)
  | BinOp(Mul, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Mul, v1, e2'))
     | None -> None)

  | BinOp(Div, Base(Int a), Base(Int b)) when b <> 0 -> Some (Base(Int (a / b)))
  | BinOp(Div, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Div, e1', e2))
     | None -> None)
  | BinOp(Div, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Div, v1, e2'))
     | None -> None)
  | BinOp(Div, Base(Int _), Base(Int 0)) -> raise (Failure "Division by zero")

  (* let *)
  | BinOp(Let x, v, body) when is_value v ->
    Some (sub x v body)

  | BinOp(Let x, e1, e2) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Let x, e1', e2))
     | None -> None)

  | BinOp(LetRec (f, x), UnOp(Fun y, body), e2) when x = y ->
    let rec_fun = UnOp(RecFun(f, x), body) in
    Some (BinOp(Let f, rec_fun, e2))

  | BinOp(LetRec (f, x), e1, e2) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(LetRec (f, x), e1', e2))
     | None -> None)

    (* application *)
  | BinOp(App, e1, e2) when not (is_value e1) ->
    (match step e1 with
    | Some e1' -> Some (BinOp(App, e1', e2))
    | None -> None)

  | BinOp(App, v1, e2) when is_value v1 && not (is_value e2) ->
    (match step e2 with
    | Some e2' -> Some (BinOp(App, v1, e2'))
    | None -> None)

  | BinOp(App, UnOp(RecFun(f, x), body), arg) when is_value arg ->
    let rec_fun = UnOp(RecFun(f, x), body) in
    let body' = sub f rec_fun body in
    Some (sub x arg body')

  | BinOp(App, UnOp(Fun x, body), arg) when is_value arg ->
    Some (sub x arg body)

      (* and & or *)
  | BinOp(And, Base(Bool true), e2) -> Some e2
  | BinOp(And, Base(Bool false), _) -> Some (Base(Bool false))
  | BinOp(And, e1, e2) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(And, e1', e2))
     | None -> None)

  | BinOp(Or, Base(Bool true), _) -> Some (Base(Bool true))
  | BinOp(Or, Base(Bool false), e2) -> Some e2
  | BinOp(Or, e1, e2) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Or, e1', e2))
     | None -> None)


     (* comp *)
  | BinOp(Lt, Base(Int a), Base(Int b)) -> Some (Base(Bool (a < b)))
  | BinOp(Lt, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Lt, e1', e2))
     | None -> None)
  | BinOp(Lt, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Lt, v1, e2'))
     | None -> None)

  | BinOp(Gt, Base(Int a), Base(Int b)) -> Some (Base(Bool (a > b)))
  | BinOp(Gt, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Gt, e1', e2))
     | None -> None)
  | BinOp(Gt, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Gt, v1, e2'))
     | None -> None)

  | BinOp(Leq, Base(Int a), Base(Int b)) -> Some (Base(Bool (a <= b)))
  | BinOp(Leq, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Leq, e1', e2))
     | None -> None)
  | BinOp(Leq, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Leq, v1, e2'))
     | None -> None)

  | BinOp(Geq, Base(Int a), Base(Int b)) -> Some (Base(Bool (a >= b)))
  | BinOp(Geq, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Geq, e1', e2))
     | None -> None)
  | BinOp(Geq, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Geq, v1, e2'))
     | None -> None)

  | BinOp(Neq, Base(Int a), Base(Int b)) -> Some (Base(Bool (a <> b)))
  | BinOp(Neq, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Neq, e1', e2))
     | None -> None)
  | BinOp(Neq, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Neq, v1, e2'))
     | None -> None)  

     (* list *)
  | BinOp(Cons, v1, v2) when is_value v1 && is_value v2 ->
    Some (BinOp(Cons, v1, v2))  (* treat fully constructed cons as value *)

  | BinOp(Cons, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Cons, e1', e2))
     | None -> None)

  | BinOp(Cons, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Cons, v1, e2'))
     | None -> None)

     (* pair *)
  | BinOp(Pair, v1, v2) when is_value v1 && is_value v2 ->
    Some (BinOp(Pair, v1, v2))

  | BinOp(Pair, e1, e2) when not (is_value e1) ->
    (match step e1 with
     | Some e1' -> Some (BinOp(Pair, e1', e2))
     | None -> None)

  | BinOp(Pair, v1, e2) when is_value v1 ->
    (match step e2 with
     | Some e2' -> Some (BinOp(Pair, v1, e2'))
     | None -> None)

     (* matching*)
  | BinOp(MatchP (x, y), e1, e2) ->
    if not (is_value e1) then
      (match step e1 with
       | Some e1' -> Some (BinOp(MatchP (x, y), e1', e2))
       | None -> None)
    else (match e1 with
      | BinOp(Pair, v1, v2) when is_value v1 && is_value v2 ->
          Some (sub y v2 (sub x v1 e2))
      | _ -> None)

  | TrinOp(MatchL (x, xs), e1, e_nil, e_cons) ->
    if not (is_value e1) then
      (match step e1 with
       | Some e1' -> Some (TrinOp(MatchL (x, xs), e1', e_nil, e_cons))
       | None -> None)
    else (match e1 with
      | Base(Nil) -> Some e_nil
      | BinOp(Cons, vh, vt) when is_value vh && is_value vt ->
          Some (sub xs vt (sub x vh e_cons))
      | _ -> None)


  (* If-then-else *)
  | TrinOp(Cond, Base(Bool true), t, _) -> Some t
  | TrinOp(Cond, Base(Bool false), _, f) -> Some f
  | TrinOp(Cond, e1, t, f) ->
    (match step e1 with
     | Some e1' -> Some (TrinOp(Cond, e1', t, f))
     | None -> None)

  
  (* Nothing to do *)
  | _ -> None



(* This is what main.ml calls *)
let rec eval (e : ast) : ast =
  match step e with
  | Some e' -> eval e'  (* keep stepping *)
  | None -> e  