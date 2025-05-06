open Exp

exception RuntimeError of string

type value =
  | VInt of int
  | VBool of bool
  | VUnit
  | VClosure of string * ast * env
  | VRecClosure of string * string * ast * env
  | VNil
  | VPair of value * value

and env = (string * value) list

(* Convert value back to AST for display *)
let rec value_to_ast v =
  match v with
  | VInt n -> Base(Int n)
  | VBool b -> Base(Bool b)
  | VUnit -> Base(Unit)
  | VNil -> Base(Nil)
  | VPair (v1, v2) -> BinOp(Pair, value_to_ast v1, value_to_ast v2)
  | VClosure _ -> failwith "can't convert VClosure to ast"
  | VRecClosure _ -> failwith "can't convert VRecClosure to ast"


let rec eval_expr (env : env) (e : ast) : value =
  match e with
  | Base(Int n) -> VInt n
  | Base(Bool b) -> VBool b
  | Base(Unit) -> VUnit
  | Base(Nil) -> VNil
  | Base(Var x) -> List.assoc x env

  | UnOp(Fun x, body) -> VClosure (x, body, env)

  | UnOp(RecFun (f, x), body) -> VRecClosure (f, x, body, env)

  | BinOp(App, e1, e2) ->
    let func = eval_expr env e1 in
    let arg = eval_expr env e2 in
    begin match func with
    | VClosure (x, body, env') ->
        eval_expr ((x, arg) :: env') body
    | VRecClosure (f, x, body, env') ->
        let rec_env = (f, VRecClosure(f, x, body, env')) :: (x, arg) :: env' in
        eval_expr rec_env body
    | _ -> raise (RuntimeError "Attempted to apply non-function value")
    end

  | BinOp(Add, e1, e2) ->
      begin match eval_expr env e1, eval_expr env e2 with
      | VInt a, VInt b -> VInt (a + b)
      | _ -> raise (RuntimeError "Expected int values for addition")
      end
  
  | BinOp(Let x, e1, e2) ->
      let v1 = eval_expr env e1 in
      eval_expr ((x, v1) :: env) e2
  
  | BinOp(Pair, e1, e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    VPair (v1, v2)
    
  
  | _ -> raise (RuntimeError "unsupported expression in eval")
  

(* This is what main.ml calls *)
let eval (e : ast) : ast =
  value_to_ast (eval_expr [] e)

(* Stub for step *)
let step (_ : ast) : ast option =
  failwith "step not implemented yet"
