open EnvFunctions
open EnvResources
open Queue
open SymResources
open SymEventGenerator
open ExpressionEvaluator
open SatFunction
open SymTransitions
open PrettyPrint
open VisibilityLevel

(* Queue of monitors we still need to exhibit (taking care of the aggregating constraints) *)
let unseen_cms = Queue.create ()

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

let rec combnk k lst =
  let rec inner result k lst =
    match k with
    | 0 -> [[]]
    | _ ->
      match lst with
      | []      -> result
      | x :: xs ->
        let rec innermost result f = function
          | []      -> result
          | x :: xs -> innermost ((f x) :: result) f xs
        in
          let new_result = innermost result (fun z -> x :: z) (inner [] (k - 1) xs)
          in inner new_result k xs
    in inner [] k lst     

(* let rec sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list list =
  (*create a list of consecutive numbers*)
  let rec create_list (n:int): int list =
    match n with 
      | 0 -> []
      | some_n -> some_n :: (create_list (n-1))  
    in let num_list = create_list (List.length cs) in

      let rec combinations n =
        match n with
         | 0 -> [[]]
         | n -> (combnk n num_list) @ combinations (n - 1)
      
        in let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int): Ast.Expression.t list = 
          match cs with
            | [] -> [Ast.Expression.Literal(Bool(true))]
            | x::[] -> 
              if element_exists_in_list indices counter
              then [add_unary_condition x] 
              else [x]  
            | x::xs -> 
              if element_exists_in_list indices counter
              then [add_unary_condition x] @ (create_one_combination xs indices (counter + 1))
              else [x] @ (create_one_combination xs indices (counter + 1))
        
            in let sc_list = 
              (let rec create_all_combinations (indices_list: int list list): Ast.Expression.t list list = 
                match indices_list with
                | [] -> (*none of the conditions are negated*)
                    let comb = b @ (create_one_combination cs [] 1)  
                    in if sat comb 
                    then [comb] 
                    else []
                | i::is -> 
                    let comb = b @ (create_one_combination cs i 1) 
                    in if sat comb 
                    then [comb] @ create_all_combinations is
                    else (create_all_combinations is)
              in create_all_combinations (combinations (List.length cs)); )

              in sc_list *)

(* [Satisfiably Combinations] returns a list of satisfiable combinations *)
(* b stores the list of boolean conditions of the constrained-monitor set *)
(* cs stores the list of reachable boolean condition *)
(* returns a list of lists of boolean condition where each list represents boolean conditions added together usings ANDs *)
let rec sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list list =
  (*create a list of consecutive numbers*)
  let rec create_list (n:int): int list =
    match n with 
      | 0 -> []
      | some_n -> some_n :: (create_list (n-1))  
    in let num_list = create_list ((List.length cs)) 

    in let rec filter_sat (condition_list: Ast.Expression.t list) = 
      if (sat condition_list) 
      then condition_list
      else []

      in let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int) (result: Ast.Expression.t list): Ast.Expression.t list = 
        match cs with
        | [] -> result
        | x::xs -> 
          if element_exists_in_list indices counter
            then (create_one_combination xs indices (counter + 1)) (result @ [add_unary_condition x]) 
          else (create_one_combination xs indices (counter + 1)) (result @ [x])  
      
      in let rec create_all_combinations (indices_list: int list list): Ast.Expression.t list list = 
        match indices_list with
        | [] -> 
          (match (filter_sat (b @ cs)) with  (*then none of the conditions are negated*)
          | [] -> []
          | x -> [x] )
        | i::is -> 
          let combination = filter_sat (b @ (create_one_combination cs i 1 [])) 
          in (
            match combination with 
            | [] -> (create_all_combinations is)
            | _ -> [combination]  @ (create_all_combinations is)
          )
      in let rec combinations (n:int): Ast.Expression.t list list = 
        match n with 
        | 0 -> 
          (match (filter_sat (b @ cs)) with (*in "n choose 0" none of the conditions are negated*)
          | [] -> []
          | x -> [x])
        | n ->  (create_all_combinations (combnk n num_list)) @ (combinations (n-1))
      
        in combinations (List.length cs)             

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

let rec spa (cms: Ast.Expression.t list * Ast.Monitor.t list) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (spa_list: int list): bool =
    let rec check_all_conds (mon_list:Ast.Monitor.t list) = 
      match mon_list with
      | [] -> false 
      | m1::m2 ->  
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

let rec print_all (a) = 
  match a with 
  | [] -> ()
  | x::xs -> 
    print_all xs; 
    print_all_messages (print_identifier_string x)

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
  print_all (Vars.elements v);

  let prt (b: Ast.Expression.t list) (v: Vars.t): Ast.Expression.t list = 
    let fv_b = (match List.length b with 
      | 0 -> Vars.empty
      | _ -> fv (b, []) Vars.empty) in 
    print_all_messages("free b: ");
    print_all (Vars.elements fv_b); 
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
	  
let rec osaft (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) =
  let rec saft_aux (m: Ast.Monitor.t list) (res: (Ast.Expression.t list * Ast.Monitor.t list)) =

    let rec new_monitors mon_list = 
      match mon_list with
      | [] -> []
      | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
      | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
    in 

    (match m with
    | [] -> 
        print_all_messages ("\nReturned by SAFT " ^ (pretty_print_evt_list (fst res)) ^ " ; "^ (pretty_print_monitor_list_string (snd res)));
        let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
        print_all_messages ("cond before was " ^ (pretty_print_evt_list (fst res)));
        print_all_messages ("cond after is " ^ (pretty_print_evt_list (fst optimized_res)));
        print_all_messages ("\nOptimized by OSAFT " ^ (pretty_print_monitor_list_string (snd optimized_res)));
        (Queue.push optimized_res unseen_cms)
    | ms::mss -> (
        let resulting_mons = sym_reduce ms (fst cm) evt c 
        in saft_aux mss (c, (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)              
        (* in saft_aux mss ([c], (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)               *)
    ))
  in saft_aux (snd cm) ([],[])

(*get the next tuple that is not already in the relation*)
let rec get_next_unseen (relation: (Ast.Expression.t list * Ast.Monitor.t list) list): (Ast.Expression.t list * Ast.Monitor.t list) = 
  if (Queue.is_empty unseen_cms) 
  then ([],[]) 
  else(
    let next_m = Queue.pop unseen_cms in
      if tuple_exists_in_relation next_m relation 
      then (
        print_all_messages ("it already exists in the relation");
        get_next_unseen relation
      )
      else (
        print_all_messages ("it does not exist");
        next_m
      )    
  ) 

(*check if the tuple is already in the relation, if not add it*)
let rec add_to_relation (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) (to_add: (Ast.Expression.t list * Ast.Monitor.t list)): (Ast.Expression.t list * Ast.Monitor.t list) list =
  print_all_messages ("adding " ^ (pretty_print_monitor_list_string (snd to_add)));
  if not (tuple_exists_in_relation to_add relation)
  then (
    print_all_messages ("not there"); 
    [to_add] @ relation)
  else (
    print_all_messages ("there"); 
    relation)

let isSymControllable (mon: Ast.Monitor.t list) =

  let rec computeSymRelation (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list): bool =

    let relation = add_to_relation relation cm in 
    print_all_messages ("RELATION IS " ^ pretty_print_relation relation ^ "\n---------------------");

    (*check symbolic potential reach*)
    if (spr cm []) 
    then(
        print_all_messages ("MONITOR TO EVAL IS " ^ pretty_print_monitor_list_string (snd cm));
		
        let frsh_v = fresh(fv cm (Vars.empty)) in
          let sym_events = generateSymEventsForMonitorList (snd cm) frsh_v [] in
            print_all_messages (pretty_print_sym_event sym_events);
            
            let rec exhibitSymEvents (sym_events: Ast.SymbolicEvent.t list): bool =
              match sym_events with
                |[] ->             
                  if (Queue.is_empty unseen_cms)
                  then( 
					          print_basic ("---------------------\nThe Witness Relation is " ^ pretty_print_relation relation);
                    true)
                  else 
                    (let next_m = get_next_unseen relation in 
                      match next_m with 
                      | ([],[]) -> (
                        print_basic ("---------------------\nThe Witness Relation is " ^ pretty_print_relation relation);
						            true)
                      | _-> computeSymRelation next_m relation
                    )
                |s::ss ->
                  print_all_messages ("Reachable Conditions (RC) for SymbolicEvent " ^ pretty_print_sym_event [s]);
                  (*List.sort_uniq drops all the duplicate elements in the list returned by rc*)
                  let c = List.sort_uniq compare (rc (snd cm) s []) in (
                    print_all_messages (pretty_print_evt_list c);
                    
                    let sat_cond = sc (fst cm) c [] in 
                      let rec print_sc (to_print) = 
                        match to_print with 
                        | [] -> ()
                        | x::xs -> 
                          print_all_messages (pretty_print_evt_list x);
                          print_sc xs
                      in print_all_messages ("\nSatisfiability Conditions (SC) ");
                      print_sc sat_cond;
                      (* print_all_messages ("\nSatisfiability Conditions (SC) " ^ (pretty_print_evt_list sat_cond)); *)

                      let rec spa_all_options (conds: Ast.Expression.t list list) = 
                        match conds with 
                         | [] -> print_all_messages ("there are no more conditions to analyse")
                         | sc1::sc2 -> 
							              let spa_result = spa cm s sc1 [] in 	
                              (* print_all_messages ("SPA For condition " ^ (pretty_print_evt_list [sc1]) ^ " is " ^ string_of_bool (spa_result));       *)
                              print_all_messages ("SPA For condition " ^ (pretty_print_evt_list sc1) ^ " is " ^ string_of_bool (spa_result));      
                              if spa_result (*if spa is true, then saft must also hold, otherwise go to the next condition*)
                              then (
                                osaft cm s sc1 relation;
                                spa_all_options sc2
                              )
                              else spa_all_options sc2
                        in spa_all_options sat_cond;  
                  );
                              
                  exhibitSymEvents ss;
            in exhibitSymEvents sym_events;
	) 
    else (
		false 
    )      
  in (computeSymRelation ([], mon) [([], mon)])
