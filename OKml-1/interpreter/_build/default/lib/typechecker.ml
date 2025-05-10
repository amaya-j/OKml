open Exp

exception TypeError of string

let counter = ref 0
let new_var () = let v = !counter in incr counter; Type.Var v

let rec occurs v = function
  | Type.Var n -> n = v
  | Type.List t -> occurs v t
  | Type.Pair (a, b) | Type.Fun (a, b) -> occurs v a || occurs v b
  | _ -> false

let rec substitute subs t =
  match t with
  | Type.Var v -> (try substitute subs (List.assoc v subs) with Not_found -> t)
  | Type.List t1 -> Type.List (substitute subs t1)
  | Type.Pair (a, b) -> Type.Pair (substitute subs a, substitute subs b)
  | Type.Fun (a, b) -> Type.Fun (substitute subs a, substitute subs b)
  | _ -> t

let rec unifyH
  (subst : (int * Type.ty) list)
  (cs    : (Type.ty * Type.ty) list)
  : (int * Type.ty) list option =
  match cs with
  | [] -> Some subst
  | (t1, t2) :: rest ->
      (* apply *all* of subst *)
      let t1 = substitute subst t1 in
      let t2 = substitute subst t2 in

      if t1 = t2 then
        unifyH subst rest
      else match t1, t2 with
      | Type.Var v, t
      | t, Type.Var v ->
          if occurs v t then None else
          let subst' = (v, t) :: subst in
          let rest' =
            List.map (fun (a,b) ->
              (substitute [(v,t)] a, substitute [(v,t)] b)
            ) rest
          in
          unifyH subst' rest'
      | Type.List a1, Type.List a2 ->
          unifyH subst ((a1, a2) :: rest)
      | Type.Pair(a1,b1), Type.Pair(a2,b2)
      | Type.Fun (a1,b1),  Type.Fun (a2,b2) ->
          unifyH subst ((a1,a2) :: (b1,b2) :: rest)
      | _ ->
          None

let unify (cs : (Type.ty * Type.ty) list)
          : (int * Type.ty) list option =
  unifyH [] cs

let rec go ctx = function
  | Base (Int _) -> (Type.Int, [])
  | Base (Bool _) -> (Type.Bool, [])
  | Base Unit -> (Type.Unit, [])
  | Base Nil -> let v = new_var () in (Type.List v, [])
  | Base (Var x) ->
      (try (List.assoc x ctx, []) with Not_found -> raise (TypeError ("Unbound var: " ^ x)))

  | UnOp (Not, e) ->
      let t, c = go ctx e in (Type.Bool, (t, Type.Bool) :: c)

  | UnOp (Neg, e) ->
      let t, c = go ctx e in (Type.Int, (t, Type.Int) :: c)

  | UnOp (Fun x, body) ->
      let arg = new_var () in
      let ctx' = (x, arg) :: ctx in
      let res, c = go ctx' body in
      (Type.Fun (arg, res), c)
  
  | UnOp (RecFun (f, x), body) ->
    let a = new_var () in
    let b = new_var () in
    let ctx' = (f, Type.Fun (a, b)) :: (x, a) :: ctx in
    let t, c = go ctx' body in
    (Type.Fun (a, b), (t, b) :: c)

  | BinOp (Add, l, r) | BinOp (Sub, l, r) | BinOp (Mul, l, r) | BinOp (Div, l, r) ->
      let tl, cl = go ctx l in
      let tr, cr = go ctx r in
      (Type.Int, (tl, Type.Int) :: (tr, Type.Int) :: cl @ cr)

  | BinOp (And, l, r) | BinOp (Or, l, r) ->
      let tl, cl = go ctx l in
      let tr, cr = go ctx r in
      (Type.Bool, (tl, Type.Bool) :: (tr, Type.Bool) :: cl @ cr)

  | BinOp (Eq, l, r) | BinOp (Neq, l, r)
  | BinOp (Gt, l, r) | BinOp (Lt, l, r)
  | BinOp (Geq, l, r) | BinOp (Leq, l, r) ->
      let tl, cl = go ctx l in
      let tr, cr = go ctx r in
      (Type.Bool, (tl, tr) :: cl @ cr)

  | BinOp (App, f, x) ->
      let tf, cf = go ctx f in
      let tx, cx = go ctx x in
      let out = new_var () in
      (out, (tf, Type.Fun(tx, out)) :: cf @ cx)

  | BinOp (Let x, e1, e2) ->
      let t1, c1 = go ctx e1 in
      let t2, c2 = go ((x, t1) :: ctx) e2 in
      (t2, c1 @ c2)

  | BinOp (LetRec (f, x), e1, e2) ->
    let a = new_var () in
    let b = new_var () in
    let fun_ty = Type.Fun (a, b) in
    let ctx_fun = (f, fun_ty) :: (x, a) :: ctx in
    let body_ty, c1 = go ctx_fun e1 in
    let c = (body_ty, b) :: c1 in
    let t2, c2 = go ((f, fun_ty) :: ctx) e2 in
    (t2, c @ c2)

  | BinOp (Cons, h, t) ->
      let th, ch = go ctx h in
      let tt, ct = go ctx t in
      (tt, (tt, Type.List th) :: ch @ ct)

  | BinOp (Pair, a, b) ->
      let ta, ca = go ctx a in
      let tb, cb = go ctx b in
      (Type.Pair (ta, tb), ca @ cb)

  | BinOp (MatchP (x, y), e1, e2) ->
      let t, c1 = go ctx e1 in
      let a = new_var () in
      let b = new_var () in
      let ctx' = (x, a) :: (y, b) :: ctx in
      let t2, c2 = go ctx' e2 in
      (t2, (t, Type.Pair (a, b)) :: c1 @ c2)

  | TrinOp (MatchL (x, xs), e1, e2, e3) ->
      let tlist, c1 = go ctx e1 in
      let telem = new_var () in
      let ctx_cons = (x, telem) :: (xs, Type.List telem) :: ctx in
      let t2, c2 = go ctx e2 in
      let t3, c3 = go ctx_cons e3 in
      (t2, (tlist, Type.List telem) :: (t2, t3) :: c1 @ c2 @ c3)

  | TrinOp (Cond, e1, e2, e3) ->
      let t1, c1 = go ctx e1 in
      let t2, c2 = go ctx e2 in
      let t3, c3 = go ctx e3 in
      (t2, (t1, Type.Bool) :: (t2, t3) :: c1 @ c2 @ c3)

let infer e =
  try
    let t, cs = go [] e in
    match unifyH [] cs with
    | Some subs -> Some (substitute subs t)
    | None      -> None
  with TypeError _ -> None