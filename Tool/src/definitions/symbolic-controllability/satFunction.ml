open EnvResources
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Solver

(*open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult*)

(** function to convert an list of expressions in the form Ast.Expression.t into the Z3.Expr.expr required by the Z3 library  *)
let rec exp_list_to_z3 (c: Ast.Expression.t list) (a: Z3.Expr.expr list) (ctx: context) =
  let rec single_exp_to_z3 (e: Ast.Expression.t) (ctx: context) =
    (match e with
      | Ast.Expression.Identifier(x) -> (Expr.mk_const ctx (Symbol.mk_string ctx x.name) (Integer.mk_sort ctx))
      | Ast.Expression.Literal(x) -> (match x with
        | Ast.Literal.Int(n) -> (Integer.mk_numeral_i ctx n)
        | Ast.Literal.Bool(b) -> (
          match b with
            | true -> (Boolean.mk_true ctx)
            | false -> (Boolean.mk_false ctx)))
      | Ast.Expression.BinaryExp(x) ->
        (match x.operator with
          | Plus -> (Arithmetic.mk_add ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Minus -> (Arithmetic.mk_sub ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Mult -> (Arithmetic.mk_mul ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Div -> (Arithmetic.mk_div ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Leq -> (Arithmetic.mk_le ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Geq -> (Arithmetic.mk_ge ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Lt -> (Arithmetic.mk_lt ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Gt -> (Arithmetic.mk_gt ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Mod -> (Arithmetic.Integer.mk_mod ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Compare -> (Boolean.mk_eq ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | And -> (Boolean.mk_and ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Or -> (Boolean.mk_or ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)]))
      | Ast.Expression.UnaryExp(x) ->
        match x.operator with
        | Not -> (Boolean.mk_not ctx (single_exp_to_z3 x.arg ctx)))
  in match c with
    | [] -> (Boolean.mk_and ctx a)
    | e::es -> exp_list_to_z3 es (a @ [single_exp_to_z3 e ctx]) ctx

(* checks whether a list of expressions is satisfiable *)
let sat (c: Ast.Expression.t list): bool  =
  let cfg = [("model", "true")] in
    let ctx = (mk_context cfg) in
        let solver = (mk_solver ctx None) in
          let cndts = exp_list_to_z3 c [] ctx in
            (Solver.add solver [cndts]);
            (*print_endline(to_string solver);*) 
            if (check solver []) == SATISFIABLE
            then true
            else false


let rec print_subgoals (subgoals: Z3.Goal.goal list) = 
  match subgoals with
  | [] -> print_endline("finish")
  | g1::g2 -> 
    print_endline(Goal.to_string g1);
    print_subgoals g2

(*let sat (c: Ast.Expression.t list): bool  =
  let cfg = [("model", "true")] in 
    let ctx = (mk_context cfg) in
        let solver = (mk_solver ctx None) in
          let cndts = exp_list_to_z3 c [] ctx in
            
            let g = (mk_goal ctx true false false) in
            (Goal.add g [ cndts ]) ;
            print_endline("-------------------");
            print_endline(Goal.to_string g) ;

            (
              let result = (Tactic.apply (and_then ctx (mk_tactic ctx ("ctx-simplify")) (mk_tactic ctx "propagate-ineqs") []) g None) in
               (*if there is one subgoal and it is false, then unsat*)
                (if ((get_num_subgoals result) == 1 && ((is_decided_sat (get_subgoal result 0)) ||  (is_decided_unsat (get_subgoal result 0)))) 
                then
                  print_endline("unsat")
                else (*if there is more than one subgoal, then sat*)
                  print_endline("sat")
                );
                
                print_endline("subgoals are: ");
                print_subgoals (get_subgoals result)
            );

            print_endline("-------------------");
            if (check solver []) == SATISFIABLE
            then true
            else false
*)
(*(apply  (then qe ctx-solver-simplify propagate-ineqs))*)


