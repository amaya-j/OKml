open Exp

let rec constProp (e : ast) : ast =
  match e with
  | Base _ -> e

  | UnOp(op, e1) ->
      UnOp(op, constProp e1)

  | TrinOp(op, e1, e2, e3) ->
      TrinOp(op, constProp e1, constProp e2, constProp e3)

  | BinOp(op, e1, e2) ->
      let e1' = constProp e1 in
      let e2' = constProp e2 in
      begin match op, e1', e2' with
      | Add, Base(Int a), Base(Int b) -> Base(Int (a + b))
      | Sub, Base(Int a), Base(Int b) -> Base(Int (a - b))
      | Mul, Base(Int a), Base(Int b) -> Base(Int (a * b))
      | Div, Base(Int a), Base(Int b) when b <> 0 -> Base(Int (a / b))
      | Let x, e1, e2 -> BinOp(Let x, e1, e2)
      | LetRec(f, x), e1, e2 -> BinOp(LetRec(f, x), e1, e2)
      | MatchP(x, y), e1, e2 -> BinOp(MatchP(x, y), e1, e2)
      | _ -> BinOp(op, e1', e2')
      end
