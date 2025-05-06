open Exp
open Type

exception TypeError of string

(* Type environment maps variables to types *)
type context = (string * ty) list

(* Lookup helper *)
let lookup (ctx : context) (x : string) : ty =
  try List.assoc x ctx
  with Not_found -> raise (TypeError ("Unbound variable: " ^ x))

(* Internal helper for inference with context *)
let rec infer_internal (ctx : context) (e : ast) : ty =
  match e with
  | Base(Int _) -> Int
  | Base(Bool _) -> Bool
  | Base(Unit) -> Unit
  | Base(Nil) -> 
      let a = Var 0 in
      List a
  | Base(Var x) -> lookup ctx x
  

  | UnOp(Not, e1) ->
      let t = infer_internal ctx e1 in
      if t = Bool then Bool else raise (TypeError "Expected bool for 'not'")

  | UnOp(Neg, e1) ->
      let t = infer_internal ctx e1 in
      if t = Int then Int else raise (TypeError "Expected int for unary '-'")

  | UnOp(Fun x, body) ->
      let a = Var 1 in
      let b = infer_internal ((x, a) :: ctx) body in
      Fun(a, b)

  | UnOp(RecFun (_f, _x), _body) ->
      raise (TypeError "Unexpected RecFun encountered at inference time")

  | BinOp(Add, e1, e2)
  | BinOp(Sub, e1, e2)
  | BinOp(Mul, e1, e2)
  | BinOp(Div, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      if t1 = Int && t2 = Int then Int
      else raise (TypeError "Expected int operands for arithmetic")

  | BinOp(And, e1, e2)
  | BinOp(Or, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      if t1 = Bool && t2 = Bool then Bool
      else raise (TypeError "Expected bool operands for logical operator")

  | BinOp(Eq, e1, e2)
  | BinOp(Neq, e1, e2)
  | BinOp(Gt, e1, e2)
  | BinOp(Lt, e1, e2)
  | BinOp(Geq, e1, e2)
  | BinOp(Leq, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      if t1 = t2 then Bool
      else raise (TypeError "Mismatched types in comparison")

  | BinOp(App, e1, e2) ->
      let tf = infer_internal ctx e1 in
      let tx = infer_internal ctx e2 in
      begin match tf with
      | Fun(arg_ty, ret_ty) ->
          if tx = arg_ty then ret_ty
          else raise (TypeError "Function argument type mismatch")
      | _ -> raise (TypeError "Attempted to apply a non-function")
      end

  | BinOp(Cons, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      begin match t2 with
      | List t_elem when t_elem = t1 -> t2
      | List _ -> raise (TypeError "Inconsistent list element types")
      | _ -> raise (TypeError "Second operand of :: must be a list")
      end

  | BinOp(Pair, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      Pair(t1, t2)

  | BinOp(Let x, e1, e2) ->
      let t1 = infer_internal ctx e1 in
      infer_internal ((x, t1) :: ctx) e2

  | BinOp(LetRec(f, x), e1, e2) ->
      let a = Var 2 in
      let b = Var 3 in
      let tf = Fun(a, b) in
      let ctx' = (f, tf) :: (x, a) :: ctx in
      let body_type = infer_internal ctx' e1 in
      if body_type = b then infer_internal ((f, tf) :: ctx) e2
      else raise (TypeError "Recursive function body does not match declared return type")

  | TrinOp(Cond, e1, e2, e3) ->
      let t1 = infer_internal ctx e1 in
      let t2 = infer_internal ctx e2 in
      let t3 = infer_internal ctx e3 in
      if t1 = Bool then
        if t2 = t3 then t2
        else raise (TypeError "Branches of if must have same type")
      else raise (TypeError "Condition of if must be boolean")

  | BinOp(MatchP(x, y), e1, e2) ->
      let t = infer_internal ctx e1 in
      begin match t with
      | Pair(t1, t2) -> infer_internal ((x, t1) :: (y, t2) :: ctx) e2
      | _ -> raise (TypeError "MatchP on non-pair value")
      end

  | TrinOp(MatchL(x, xs), e1, e2, e3) ->
      let t = infer_internal ctx e1 in
      begin match t with
      | List t_elem ->
          let t_nil = infer_internal ctx e2 in
          let t_cons = infer_internal ((x, t_elem) :: (xs, t) :: ctx) e3 in
          if t_nil = t_cons then t_nil
          else raise (TypeError "Branches of list match must have same type")
      | _ -> raise (TypeError "MatchL on non-list value")
      end

(* Public interface for infer, matches .mli *)
let infer (e : ast) : ty option =
  try Some (infer_internal [] e)
  with TypeError _ -> None

(* Actual unify implementation *)
let rec occurs_check v t =
  match t with
  | Var n -> n = v
  | List t' -> occurs_check v t'
  | Pair (t1, t2) | Fun (t1, t2) -> occurs_check v t1 || occurs_check v t2
  | _ -> false

let rec substitute (subs : (int * ty) list) (t : ty) : ty =
  match t with
  | Var v -> (try substitute subs (List.assoc v subs) with Not_found -> t)
  | List t' -> List (substitute subs t')
  | Pair (t1, t2) -> Pair (substitute subs t1, substitute subs t2)
  | Fun (t1, t2) -> Fun (substitute subs t1, substitute subs t2)
  | _ -> t

let rec unify_constraints (subs : (int * ty) list) (constraints : (ty * ty) list) : (int * ty) list option =
  match constraints with
  | [] -> Some subs
  | (t1, t2)::rest ->
    let t1 = substitute subs t1 in
    let t2 = substitute subs t2 in
    if t1 = t2 then unify_constraints subs rest
    else match (t1, t2) with
      | Var v, t | t, Var v ->
        if occurs_check v t then None
        else unify_constraints ((v, t) :: subs) rest
      | List a, List b ->
        unify_constraints subs ((a, b) :: rest)
      | Pair (a1, b1), Pair (a2, b2) ->
        unify_constraints subs ((a1, a2) :: (b1, b2) :: rest)
      | Fun (a1, b1), Fun (a2, b2) ->
        unify_constraints subs ((a1, a2) :: (b1, b2) :: rest)
      | _, _ -> None

let unify (constraints : (ty * ty) list) : (int * ty) list option =
  unify_constraints [] constraints