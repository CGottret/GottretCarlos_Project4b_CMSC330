open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions - DO NOT MODIFY *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) = 
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) = 
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* Part 2: Parsing expressions *)

let rec parse_expr toks = 

  let head = lookahead toks in
  match head with 

  |Some Tok_Let -> 
   (let tok_match_let = match_token toks Tok_Let in
    let (tok_b4_let, expr_aftr_let) = 
      (let head = lookahead tok_match_let in
      match head with
      |Some Tok_Rec -> (match_token tok_match_let Tok_Rec, true)
      |_ -> (tok_match_let, false)) in
    let id = 
      (let head = lookahead tok_b4_let in
      match head with 
      | Some Tok_ID a -> a
      | _ -> failwith( "fail")) in
    let tok_match_ID = match_token tok_b4_let (Tok_ID id) in
    let tok_match_equal = match_token tok_match_ID Tok_Equal in
    let (tok_b4_equal, expr_aftr_equal) = parse_expr tok_match_equal in
    let tok_match_in = match_token tok_b4_equal Tok_In in
    let (tok_b4_in, expr_aftr_in) = parse_expr tok_match_in 
    in (*return *)   
    (tok_b4_in, Let (id, expr_aftr_let, expr_aftr_equal, expr_aftr_in)))

  |Some Tok_Fun -> 
   (let head = lookahead toks in
    match head with
    
    |Some Tok_Fun -> 
        (let tok_match_fun = match_token toks Tok_Fun in
        let head = lookahead tok_match_fun in
        match head with 

        |Some Tok_ID x -> 
        let tok_match_ID = match_token tok_match_fun (Tok_ID x) in
        let tok_match_arrow = match_token tok_match_ID Tok_Arrow in 
        let (tok_b4_arrow, exp_aftr_arrow) = parse_expr tok_match_arrow 
        in (*return*)
        (tok_b4_arrow, Fun(x, exp_aftr_arrow))

        |_ -> raise (InvalidInputException("function")) (*return*)) 

    |_ -> raise (InvalidInputException "function") (*return*))

  |Some Tok_If -> 
   (let head = lookahead toks in
    match head with 

    |Some Tok_If -> 
      let tok_match_if = match_token toks Tok_If in 
      let (tok_b4_if,exp_aftr_if) = parse_expr tok_match_if in 
      let tok_match_then = match_token tok_b4_if Tok_Then in 
      let (tok_b4_then,exp_aftr_then) = parse_expr tok_match_then in 
      let tok_match_else = match_token tok_b4_then Tok_Else in 
      let (tok_match_else,exp_aftr_else) = parse_expr tok_match_else 
      in (*return*)
      (tok_match_else, If(exp_aftr_if,exp_aftr_then,exp_aftr_else))

    |_ -> raise (InvalidInputException "if") (*error*))

  |_ -> 
  ( let (tok_b4_and, exp_aftr_and) = parse_And toks in
    let head = lookahead tok_b4_and in
    match head with
    
    |Some Tok_Or -> 
      let tok_match_or = match_token tok_b4_and Tok_Or in
      let (tok_b4_or, exp_aftr_or) = parse_Or tok_match_or 
      in (*return*)
      (tok_b4_or, Binop(Or, exp_aftr_and, exp_aftr_or))
    
    |_ -> (tok_b4_and, exp_aftr_and) (*or return*))

and parse_Or toks =
  let (tok_b4_and, exp_aftr_and) = parse_And toks in
  let head = lookahead tok_b4_and in
  match head with
  
  |Some Tok_Or -> 
    let tok_match_or = match_token tok_b4_and Tok_Or in
    let (tok_b4_or, exp_aftr_or) = parse_Or tok_match_or 
    in (*return*)
    (tok_b4_or, Binop(Or, exp_aftr_and, exp_aftr_or))
  
  |_ -> (tok_b4_and, exp_aftr_and) (*or return*)

and parse_And toks = 
  let (tok_b4_equal, exp_aftr_equal) = parse_Equal toks in
  let head = lookahead tok_b4_equal in
  match head with

  |Some Tok_And -> 
    let tok_match_and = match_token tok_b4_equal Tok_And in
    let (tok_b4_and, exp_aftr_and) = (parse_And tok_match_and) 
    in (*return*)
    (tok_b4_and, Binop(And, exp_aftr_equal, exp_aftr_and))
  
  |_ -> (tok_b4_equal, exp_aftr_equal) (*or return*)

and parse_Add_Sub toks =  
  let (tok_b4_mult, exp_aftr_mult) = parse_Multi_Div toks in
  let head = lookahead tok_b4_mult in
  match head with
  
  |Some Tok_Add -> 
    let tok_match_add = (match_token tok_b4_mult Tok_Add) in
    let (tok_b4_add, exp_aftr_add) = (parse_Add_Sub tok_match_add) 
    in (*return for addition*)
    (tok_b4_add, Binop(Add, exp_aftr_mult, exp_aftr_add))
  
  |Some Tok_Sub ->  
    let tok_match_sub = (match_token tok_b4_mult Tok_Sub) in
    let (tok_b4_sub, exp_aftr_sub) = (parse_Add_Sub tok_match_sub) 
    in (*return for subtraction*)
    (tok_b4_sub, Binop(Sub, exp_aftr_mult, exp_aftr_sub))
  
  |_ -> (tok_b4_mult, exp_aftr_mult)

and parse_Multi_Div toks =   
  let (tok_b4_concat, exp_aftr_concat) = parse_Concatenate toks in
  let head = lookahead tok_b4_concat in
  match head with 

  |Some Tok_Mult -> 
    let tok_match_mult = match_token tok_b4_concat Tok_Mult in 
    let (tok_b4_mult, exp_aftr_mult) = parse_Multi_Div tok_match_mult 
    in (*return for multiplication*)
    (tok_b4_mult, Binop (Mult, exp_aftr_concat, exp_aftr_mult))
  
  |Some Tok_Div -> 
    let tok_match_Div = match_token tok_b4_concat Tok_Div in 
    let (tok_b4_div, exp_aftr_div) = parse_Multi_Div tok_match_Div 
    in (*return for division*)
    (tok_b4_div, Binop (Div, exp_aftr_concat, exp_aftr_div))  
  |_ -> (tok_b4_concat, exp_aftr_concat)

and parse_Concatenate toks =
  let (tok_b4_unary_exp, exp_aftr_unary_exp) = parse_Unary toks in
  let head = lookahead tok_b4_unary_exp in
  match head with 

  |Some Tok_Concat -> 
    let tok_match_concat = match_token tok_b4_unary_exp Tok_Concat in
    let (tok_b4_concat, exp_aftr_concat) = parse_Concatenate tok_match_concat 
    in (*return *)
    (tok_b4_concat, Binop(Concat, exp_aftr_unary_exp, exp_aftr_concat))

  |_ -> (tok_b4_unary_exp, exp_aftr_unary_exp)

and parse_Equal toks = 
  let (tok_b4_relational_exp, exp_aftr_relational_exp) = parse_Relation toks in
  let head = lookahead tok_b4_relational_exp in
  match head with 

  |Some Tok_Equal -> 
    let tok_match_equal = match_token tok_b4_relational_exp Tok_Equal in
    let (tok_b4_equal, exp_aftr_equal) = (parse_Equal tok_match_equal) 
    in (*return*)
    (tok_b4_equal, Binop(Equal, exp_aftr_relational_exp, exp_aftr_equal))

  |Some Tok_NotEqual -> 
    let tok_match_not_equal = match_token tok_b4_relational_exp Tok_NotEqual in
    let(tok_b4_not_equal, exp_aftr_not_equal) = (parse_Equal tok_match_not_equal) 
    in (*return*)
    (tok_b4_not_equal, Binop(NotEqual, exp_aftr_relational_exp, exp_aftr_not_equal))

  |_ -> (tok_b4_relational_exp, exp_aftr_relational_exp)

and parse_Relation toks = 
  let (tok_b4_add, exp_aftr_add) = parse_Add_Sub toks in
  let head = lookahead tok_b4_add in
  match head with

  | Some Tok_Less -> 
    let tok_match_less = (match_token tok_b4_add Tok_Less) in
    let (tok_b4_less, exp_aftr_less) = (parse_Relation tok_match_less) 
    in (*return*)
    (tok_b4_less, Binop(Less, exp_aftr_add, exp_aftr_less))

  | Some Tok_Greater -> 
    let tok_match_greater = (match_token tok_b4_add Tok_Greater) in
    let (tok_b4_greater, exp_aftr_greater) = (parse_Relation tok_match_greater) 
    in (*return*)
    (tok_b4_greater, Binop(Greater, exp_aftr_add, exp_aftr_greater))
 
  | Some Tok_LessEqual -> 
    let tok_match_less_equal = (match_token tok_b4_add Tok_LessEqual) in
    let (tok_b4_less_equal, exp_aftr_less_equal) = (parse_Relation tok_match_less_equal) 
    in (*return*)
    (tok_b4_less_equal, Binop(LessEqual, exp_aftr_add, exp_aftr_less_equal))

  | Some Tok_GreaterEqual -> 
    let tok_match_greater_equal = (match_token tok_b4_add Tok_GreaterEqual) in
    let (tok_b4_greater_equal, exp_aftr_greater_equal) = (parse_Relation tok_match_greater_equal) 
    in (*return*)
    (tok_b4_greater_equal, Binop(Less, exp_aftr_add, exp_aftr_greater_equal))

  | _ -> (tok_b4_add, exp_aftr_add)

and parse_Unary toks = 
  let head = lookahead toks in
  match head with 

  | Some Tok_Not -> 
    let tok_match_not = match_token toks Tok_Not in 
    let (tok_b4_not, exp_aftr_not) = parse_Unary tok_match_not 
    in (*return*)
    (tok_b4_not, Not (exp_aftr_not))

  | _ -> parse_FunctionCall toks

and parse_FunctionCall toks =  
  let (tok_b4_prim, exp_aftr_prim) = parse_Primary toks in 
  let head = lookahead tok_b4_prim in
  match head with 

  | Some Tok_LParen -> 
    let (tok_b4_primm, exp_aftr_primm) = parse_Primary tok_b4_prim 
    in (*return*)
    (tok_b4_primm, FunctionCall(exp_aftr_prim, exp_aftr_primm))

  |Some Tok_Int i -> 
    let (tok_b4_primm, exp_aftr_primm) = parse_Primary tok_b4_prim 
    in (*return*)
    (tok_b4_primm, FunctionCall(exp_aftr_prim, exp_aftr_primm))

  |Some Tok_Bool bool -> 
    let (tok_b4_primm, exp_aftr_primm) = parse_Primary tok_b4_prim 
    in (*return*)
    (tok_b4_primm, FunctionCall(exp_aftr_prim, exp_aftr_primm))

  |Some Tok_ID id -> 
    let (tok_b4_primm, exp_aftr_primm) = parse_Primary tok_b4_prim 
    in (*return*)
    (tok_b4_primm, FunctionCall(exp_aftr_prim, exp_aftr_primm))

  |Some Tok_String str -> 
    let (tok_b4_primm, exp_aftr_primm) = parse_Primary tok_b4_prim 
    in (*return*)
    (tok_b4_primm, FunctionCall(exp_aftr_prim, exp_aftr_primm))

  |_ -> (tok_b4_prim, exp_aftr_prim)

and parse_Primary toks = 
  let head = lookahead toks in
  match head with

  |Some Tok_LParen -> 
    let tok_match_l_paren = match_token toks Tok_LParen in 
    let (tok_b4_l_paren, exp_aftr_l_paren) = parse_expr tok_match_l_paren in
    let tok_match_r_paren = match_token tok_b4_l_paren Tok_RParen 
    in (*return*)
    (tok_match_r_paren, exp_aftr_l_paren)

  |Some Tok_Int i -> 
    let tok_match_int = match_token toks (Tok_Int i) 
    in (*return*)
    (tok_match_int, Value(Int i)) 

  |Some Tok_Bool bool -> 
    let tok_match_bool = match_token toks (Tok_Bool bool) 
    in (*return*)
    (tok_match_bool, Value(Bool bool))

  |Some Tok_ID id -> 
    let tok_match_ID = match_token toks (Tok_ID id) 
    in (*return*)
    (tok_match_ID, ID id)

  |Some Tok_String str -> 
    let tok_match_string = match_token toks (Tok_String str) 
    in (*return*)
    (tok_match_string, Value(String str))

  | _ -> raise (InvalidInputException"primary") (*error*)

(* Part 3: Parsing mutop *)

let rec parse_mutop toks =
  let head = lookahead toks in
  match head with

  |Some Tok_Def ->
    let tok_match_def = match_token toks Tok_Def in
    let id = 
      (let head = lookahead tok_match_def in
      match head with
      |Some Tok_ID id -> id
      |_ -> raise (InvalidInputException"primary")) in
    let tok_match_ie = match_many tok_match_def [Tok_ID (id); Tok_Equal;] in
    let (tok_b4_ie, expr_aftr_ie) = parse_expr tok_match_ie in
    let tokens = match_token tok_b4_ie Tok_DoubleSemi 
    in (*return*)
    (tokens, Def (id, expr_aftr_ie))
  
  |Some Tok_DoubleSemi ->
    let tok_match_semi = match_token toks Tok_DoubleSemi 
    in (*return*)
    (tok_match_semi, NoOp)
  
  |_ ->
    let (tok_b4_parse, expr_aftr_parse) = parse_expr toks in
    let tok_match_semi = match_token tok_b4_parse Tok_DoubleSemi 
    in (*return*)
    (tok_match_semi, Expr (expr_aftr_parse))