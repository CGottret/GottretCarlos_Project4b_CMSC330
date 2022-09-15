open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
let rec eval_expr env e = 
  match e with
    
    |Value value -> value

    |ID id -> (lookup env id)

    |Fun (str,body) -> Closure (env,str,body)

    |Binop (operation, exp1, exp2) -> eval_Binop env operation exp1 exp2

    |If (guard, branch1, branch2) -> eval_If env guard branch1 branch2

    |Let (str,bool,init,body) -> if bool then (eval_True_Let env str init body) else (eval_False_Let env str init body)

    |Not expr -> 
      let bool = (eval_expr env expr) in
      (match bool with
      | Bool x ->  (if x = true then Bool false else Bool true)
      | _ -> raise (TypeError("error")))

	  |FunctionCall (first,second) -> 
    let exp1, exp2 = (eval_expr env first), (eval_expr env second) in
    (match exp1 with
    | Closure (env,x,e) -> 
      let env2 = (extend env x exp2) 
      in
		  (eval_expr env2 e)

		|_ -> raise (TypeError("error")))

  and eval_If env guard branch1 branch2 = 
    let exp1 = eval_expr env guard in
    let t_branch = eval_expr env branch1 in
	  (match exp1 with
		|Bool bool -> if bool then t_branch else (eval_expr env branch2)
    |_ -> raise(TypeError("if")))

  and eval_True_Let env str init body = 
      let env2 = extend_tmp env str in
      update env2 str (eval_expr env2 init) ;
      eval_expr env2 body
  
  and eval_False_Let env str init body =
      let env2 = extend env str (eval_expr env init) in
      eval_expr env2 body 

  and eval_Additive env op n1 n2 = 
    let num1, num2 = (eval_expr env n1), (eval_expr env n2) in
      (match num1, num2 with
      | Int x, Int y -> 
        (match op with
        |Add -> Int(x+y)
        |Sub -> Int(x-y)
        |_ -> raise (TypeError("error")))
      | _ -> raise (TypeError("error")))

  and eval_Multipicative env op n1 n2 = 
    let num1, num2 = (eval_expr env n1), (eval_expr env n2) in
      (match num1, num2 with
      | Int x, Int y -> 
        (match op with
        |Mult -> Int(x*y)
        |Div -> if y!=0 then Int (x/y) else raise(DivByZeroError)
        |_ -> raise (TypeError("error")))
      | _ -> raise (TypeError("error")))

  and eval_Relative env op n1 n2 = 
    let num1, num2 = (eval_expr env n1), (eval_expr env n2) in
      (match num1, num2 with
      | Int x, Int y -> 
        (match op with
        |Less -> Bool(x<y)
        |Greater -> Bool(x>y)
        |_ -> raise (TypeError("error")))
      | _ -> raise (TypeError("error")))

  and eval_Equality env op n1 n2 = 
    let num1, num2 = (eval_expr env n1), (eval_expr env n2) in
      (match num1, num2 with
      |Int x, Int y -> 
        (match op with
        |Equal -> Bool(x=y)
        |NotEqual -> Bool(x<>y)
        |LessEqual -> Bool(x<=y)
        |GreaterEqual -> Bool(x>=y)
        |_ -> raise (TypeError("error")))
      |Bool x, Bool y -> 
        (match op with
        |Equal -> Bool(x=y)
        |NotEqual -> Bool(x<>y)
        |_ -> raise (TypeError("error")))
      |String x, String y -> 
        (match op with
        |Equal -> Bool(x=y)
        |NotEqual -> Bool(x<>y)
        |_ -> raise (TypeError("error")))
      | _ -> raise (TypeError("error")))

  and eval_Comparison env op n1 n2 = 
    let bool1, bool2 = (eval_expr env n1), (eval_expr env n2) in
      (match bool1, bool2 with
      |Bool x, Bool y -> 
        (match op with
        |Or -> Bool(x||y)
        |And -> Bool(x&&y)
        |_ -> raise (TypeError("error")))
      |_ -> raise (TypeError("error")))

  and eval_Concat env op n1 n2 = 
    let s1, s2 = (eval_expr env n1), (eval_expr env n2) in
      (match s1, s2 with
      |String x, String y -> String(x^y)
      |_ -> raise (TypeError("error")))

  and eval_Binop env op e1 e2 =
    match op with
	  |Add -> eval_Additive  env Add e1 e2
    |Sub -> eval_Additive  env Sub e1 e2
    |Mult -> eval_Multipicative env Mult e1 e2
    |Div -> eval_Multipicative env Div e1 e2
    |Less -> eval_Relative env Less e1 e2
    |Greater -> eval_Relative env Greater e1 e2
    |Equal -> eval_Equality env Equal e1 e2
    |NotEqual -> eval_Equality env NotEqual e1 e2                    
    |LessEqual -> eval_Equality env LessEqual e1 e2
    |GreaterEqual -> eval_Equality env GreaterEqual e1 e2
    |Or -> eval_Comparison env Or e1 e2
    |And -> eval_Comparison env And e1 e2
    |Concat -> eval_Concat env Concat e1 e2


(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
let eval_mutop env m = 
    match m with
    | Def (var, expr)-> 
        let env2 = extend_tmp env var in
        let v = (eval_expr env2 expr) in
        update env2 var v;
        (env2, Some v)
    | Expr expr -> 
        let e = eval_expr env expr in
        (env, Some e) 
    | NoOp -> ([], None)