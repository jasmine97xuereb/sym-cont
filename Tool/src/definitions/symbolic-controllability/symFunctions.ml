open SymResources
open SymEventGenerator
open ExpressionEvaluator
open SatFunction
open SymTransitions
open PrettyPrint
open VisibilityLevel
open EnvFunctions
open EnvResources
open Queue

(* Reachable Conditions *)
let rec rc (ms: Ast.Monitor.t list) (sevt: Ast.SymbolicEvent.t) (cs: Ast.Expression.t list): Ast.Expression.t list =
  (* inner_rc generates the relevant conditions for a single monitor given an event *)
  let rec inner_rc (m: Ast.Monitor.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    match m with
      | Ast.Monitor.Verdict(_) -> []
      | Ast.Monitor.TVar(x) -> get_tvar_conditions x evt c
      | Ast.Monitor.Choice(x) -> (inner_rc x.left evt c) @ (inner_rc x.right evt c)
      (* inner_rc x.right evt (inner_rc x.left evt c)  *)
      | Ast.Monitor.ExpressionGuard(x) -> get_exp_guard_conditions x evt c
      | Ast.Monitor.QuantifiedGuard(x) -> get_quant_guard_conditions x evt c 
      | Ast.Monitor.Conditional(x) -> get_if_conditions x evt c
      | Ast.Monitor.Recurse(x) -> inner_rc x.consume evt c
      | Ast.Monitor.Evaluate(x) -> get_evaluate_conditions x evt c

  and get_tvar_conditions (tvar: Ast.TVar.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    match TVars.find_opt tvar.tvar !mapTVar with
    | Some m -> inner_rc m evt c
    | None -> []
   
  and get_exp_guard_conditions (m: Ast.Monitor.ExpressionGuard.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    if (compare_values (reduce_identifier m.label ) (reduce_identifier evt.label ))
    then
      (             
        let b = create_exp_identifier evt.payload.name in
          let op = Ast.Expression.BinaryExp.Compare in
            match (reduce_expression m.payload ) with
            | INT(x) ->
              (let a = Ast.Expression.Literal(Ast.Literal.Int(x)) in
                let cond = add_binary_condition a b op in
                  c @ [cond])
            | BOOL(x) ->
              (let a = Ast.Expression.Literal(Ast.Literal.Bool(x)) in
                let cond = add_binary_condition a b op in
                  c @ [cond]) 
            | STRING(x) ->
              (let a = create_exp_identifier x in
                let cond = add_binary_condition a b op in
                  c @ [cond]) 
            | ERR(x) -> (*it is an expression example <x+1>*) 
              (let a = m.payload in 
                let cond = add_binary_condition a b op in 
                  c @ [cond])
          ) 
      else c 

  and get_quant_guard_conditions (m: Ast.Monitor.QuantifiedGuard.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    if (compare_values (reduce_identifier m.label ) (reduce_identifier evt.label ))
    then [Ast.Expression.Literal(Bool(true))]
    else c

  and get_if_conditions (m: Ast.Monitor.Conditional.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    let a = m.condition in 
      let b_true = (inner_rc m.if_true evt c) in 
        let b_false = (inner_rc m.if_false evt c) in
          let op = Ast.Expression.BinaryExp.And in
            let rec add_all_conds (a: Ast.Expression.t) (b: Ast.Expression.t list) (c: Ast.Expression.t list): Ast.Expression.t list =
            match b with 
            | [] -> c 
            | b1::b2 ->
              add_all_conds a b2 (c @ [add_binary_condition a b1 op])  
          in
          match b_true, b_false with 
          | [], [] -> [a] @ [(add_unary_condition a)] @ c 
          | _ ->
            (match m.condition with
              | Ast.Expression.BinaryExp(x) -> 
                (add_all_conds a b_true c) @ (add_all_conds (add_unary_condition a) b_false c)
              | Ast.Expression.UnaryExp(x) ->
                (add_all_conds a b_true c) @ (add_all_conds (x.arg) b_false c)
              | _ -> c)

  and get_evaluate_conditions (m: Ast.Monitor.Evaluate.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    let rec sub_all_conds (var: Ast.Expression.t) (to_sub: Ast.Expression.t) (b: Ast.Expression.t list) (c: Ast.Expression.t list): Ast.Expression.t list =
      match b with 
      | [] -> c
      | b1::b2 -> sub_all_conds var to_sub b2 (c @ [substitute_expression b1 var to_sub])  
    in sub_all_conds m.var m.subst (inner_rc m.stmt evt c) c 

  in match ms with
    | [] -> []
    | mon::mons -> ((inner_rc mon sevt cs) @ (rc mons sevt cs))

(* * [Satisfiably Combinations] returns a list of satisfiable combinations *)
(* b stores the list of boolean conditions of the constrained-monitor set *)
(* cs stores the list of reachable boolean condition *)
(* returns a list of lists of boolean condition where each list represents boolean conditions added together usings ANDs *)
let rec sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list =
  (*create a list of consecutive numbers*)
  let rec create_list (n:int): int list =
    match n with 
      | 0 -> []
      | some_n -> some_n :: (create_list (n-1))  
    in let num_list = create_list ((List.length cs)) 

    in let rec filter_sat (condition_list: Ast.Expression.t list) = 
      let sat_result = sat condition_list
      in if (fst sat_result) 
      then snd sat_result
      else []

      in let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int) (result: Ast.Expression.t list): Ast.Expression.t list = 
        match cs with
        | [] -> result
        | x::xs -> 
          if element_exists_in_list indices counter
            then (create_one_combination xs indices (counter + 1)) (result @ [add_unary_condition x]) 
          else (create_one_combination xs indices (counter + 1)) (result @ [x])  
      
      in let rec create_all_combinations (indices_list: int list list): Ast.Expression.t list = 
        match indices_list with
        | [] -> filter_sat (b @ cs) (*then none of the conditions are negated*)
        | i::is -> 
          let combination = filter_sat (b @ (create_one_combination cs i 1 [])) 
          in (
            match combination with 
            | [] -> (create_all_combinations is)
            | _ -> combination  @ (create_all_combinations is)
          )
      in let rec combinations n = 
        match n with 
        | 0 -> filter_sat (b @ cs) (*in "n choose 0" none of the conditions are negated*)
        | n ->  (create_all_combinations (combnk n num_list)) @ (combinations (n-1))
      
        in combinations (List.length cs)            

(* checks whether some acceptance or rejection verdict has been reached *)
let rec verdict_reached (cms: Ast.Expression.t list * Ast.Monitor.t list): bool =
  match (snd cms) with (*match monitor list*)
    | [] -> false (*no verdict reached*)
    | elt::elts -> (
      match elt with 
      | Ast.Monitor.Verdict(x) -> (
        match x.verd with
          | ONE -> true
          | TWO -> true
          | _ -> verdict_reached (fst cms, elts))
      | _ ->  verdict_reached (fst cms, elts)
    ) 

(* A constrained monitor-set <b,M> symbolically potentially reaches a verdict spr(<b,M>,w) if the monitor set M can immediately reach a verdict without requiring tau transitions *)
let rec spr (cms: Ast.Expression.t list * Ast.Monitor.t list) (verdict_list: int list): bool =
  match (snd cms) with (*match monitor list*)
    | [] -> (match (List.length verdict_list) with (*if no monitors, check the list of potential verdicts*) 
      | 1 -> true (*one verdict reached*)
      | _ -> false 
    ) (*can only reach one verdict - either 1 or 2*) 

    | elt::elts -> (match elt with (*there are montiors left to analyse*)
      (* Check that the monitor is actually a verdict, and match the verdict.
          If the verdicts match then the monitor is can potentially reach a verdict, else it doesn't *)
      | Ast.Monitor.Verdict(x) -> (match x.verd with
          (* acceptance verdict *)
          | ONE -> 
            if (element_exists_in_list verdict_list 1)
            then spr (fst cms, elts) verdict_list (*verdict already expsts in verdict_list, check other monitors in M*)
            else spr (fst cms, elts) (verdict_list @ [1]) (*add verdict to verdict_list and check other monitors in M*)
          (*reject verdict*)
          | TWO -> 
            if (element_exists_in_list verdict_list 2)
            then spr (fst cms, elts) verdict_list
            else spr (fst cms, elts) (verdict_list @ [2])
          (*anything else - note that inconclusive verdicts are not externally observable*)
          | _ -> 
            if (element_exists_in_list verdict_list 0)
            then spr (fst cms, elts) verdict_list
            else spr (fst cms, elts) (verdict_list @ [0]))

      (* If the monitor is not a verdict, then the case holds trivially *)
      | _ -> 
        if (element_exists_in_list verdict_list 0)
        then spr (fst cms, elts) verdict_list
        else spr (fst cms, elts) (verdict_list @ [0])
    ) 

(*return a tuple made up of a boolean value and the simplified boolean condition *)
(*the second element of the tuple is always [] whenver spa is false *)
let rec spa (cms: Ast.Expression.t list * Ast.Monitor.t list) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t) (spa_list: int list): bool =
    let rec check_all_conds (mon_list:Ast.Monitor.t list) = 
      match mon_list with
      | [] -> false
      | m1::m2 ->  
        (*use simplified boolean condition returned by sat*)
        match sym_reduce m1 (fst cms) evt c  with 
          | REDUCED(x)::_ -> true (*if one monitor reduces it is enough*)
          | ERROR(x)::xs -> 
            (let rec check_remaining xs = 
              match xs with 
              | [] -> check_all_conds m2
              | REDUCED(y)::ys -> true
              | _::ys -> check_remaining ys  
            in check_remaining xs)  
            
    in check_all_conds (snd cms)

(*checks if there are any dependant variables*)
(*a variable may be dependent on another in two ways:*)
(*OPTION 1*)
(*it is part of some subcondition example y=x+1 where x is the variable to be kept*)
(*OPTION 2*)
(*it is part of some unary condition example !(x<5 && y>6) where x is the variable to be kept*)
let rec indirect_dependency (b: Ast.Expression.t list) (to_keep: Vars.t): Vars.t = 
  let rec inner_check (b: Ast.Expression.t list) (to_keep: Vars.t): Vars.t =
    match b with
    | [] -> to_keep
    | b1::bs ->
      (match b1 with 
      | Ast.Expression.BinaryExp(x)->
      (match x.operator with
        | Ast.Expression.BinaryExp.And -> 
          Vars.union (inner_check [x.arg_lt] to_keep) (inner_check [x.arg_rt] to_keep)
        | _ -> 
          if check_in_list (x.arg_rt) (Vars.elements to_keep)
          then Vars.union (fv ([x.arg_lt],[]) to_keep) (inner_check bs to_keep)
          else if check_in_list (x.arg_lt) (Vars.elements to_keep)
          then Vars.union (fv ([x.arg_rt],[]) to_keep) (inner_check bs to_keep)
          else inner_check bs to_keep
      )
      | Ast.Expression.UnaryExp(x) -> 
        if check_in_list x.arg (Vars.elements to_keep) (*if there is some var to be kept, then all those vars must also be kept*)
        then Vars.union to_keep (fv ([x.arg], []) Vars.empty)
        else (inner_check bs to_keep)
      | _ -> inner_check bs to_keep)
	in let new_to_keep = inner_check b to_keep in
	if Vars.diff to_keep new_to_keep != Vars.empty (*check if new ones have been added*)
  then indirect_dependency b new_to_keep (*new vars have been added - redo*)
	else new_to_keep 

(*cns returns the consolidated boolean condition*)
(*if there are no free variables in the monitor-set i.e. v=empty, then all the boolean conditions can be removed and b1 is empty*)
(*otherwise, call prt which returns b1 which is the list of boolean conditions to be kept*)
(*if there are no variables in the boolean condition, then all the conditions can be removed*)
(*otherwise, all the variables in the instersection of v and fv_b must be kept*)
(*also, the variables upon which those in the intersection depend must be kept*)
(*a variables is dependent on another either if there is some other subcondition that mentions a var in to_keep or it is part of a unary condition that contains a var in to_keep*)
(*after calculating the set of vars to be kept, check whether to_keep is a subset of v*)
(*if to_keep is not a subset of v, then the condition has been violated and no condition can be removed*)
let cns (b: Ast.Expression.t list) (mon_list: Ast.Monitor.t list): Ast.Expression.t list =
  let v = fv ([], mon_list) Vars.empty in (*V = fv(saft(M, B, $))*)
  print_all_messages("free V: ");
  List.iter (fun x -> print_all_messages (print_identifier_string x)) (Vars.elements v);

  let prt (b: Ast.Expression.t list) (v: Vars.t): Ast.Expression.t list = 
    let fv_b = (match List.length b with 
      | 0 -> Vars.empty
      | _ -> fv (b, []) Vars.empty) in 
    print_all_messages("free b: ");
    List.iter (fun x -> print_all_messages (print_identifier_string x)) (Vars.elements fv_b); 
    if Vars.is_empty v
    then []
    else( 
      let to_keep = Vars.inter fv_b v in 
      (*check if any of those to keep are dependent on any from the ones to be discarded*)
      (* let to_keep = indirect_dependency (List.hd b) to_keep  *)
      let to_keep = indirect_dependency b to_keep 
      in if Vars.subset to_keep v
      then filter_b b (Vars.elements to_keep)
      else b 
    )
  in if Vars.is_empty v 
  then []
  else prt b v 
	  
let rec osaft (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) (unseen_cms: (Ast.Expression.t list * Ast.Monitor.t list) Queue.t) =
  let rec saft_aux (m: Ast.Monitor.t list) (res: (Ast.Expression.t list * Ast.Monitor.t list)) =

    let rec new_monitors mon_list = 
      match mon_list with
      | [] -> []
      | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
      | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
    in 

    (match m with
    | [] -> 
        print_all_messages ("\nReturned by SAFT " ^ (pretty_print_monitor_list_string (snd res)));
        let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
        print_all_messages ("cond before was " ^ (pretty_print_evt_list (fst res)));
        print_all_messages ("cond after is " ^ (pretty_print_evt_list (fst optimized_res)));
        print_all_messages ("\nOptimized by OSAFT " ^ (pretty_print_monitor_list_string (snd optimized_res)));
        (Queue.push optimized_res unseen_cms)
    | ms::mss -> (
        let resulting_mons = sym_reduce ms (fst cm) evt c 
        in saft_aux mss ([c], (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)              
    ))
  in saft_aux (snd cm) ([],[])