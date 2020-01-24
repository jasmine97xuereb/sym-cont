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
open SymFunctions
open ViabilityChecking

(* Queue of monitors we still need to exhibit (taking care of the aggregating constraints) *)
let unseen_cms = Queue.create ()

let isSymControllable (mon: Ast.Monitor.t list) =

  if not (contains_visible_verdicts mon)
  then (
    print_endline("THE MONITOR SET DOES NOT CONTAIN ANY VISIBLE VERDICTS"); 
    true
  )
  else( print_endline ("THE MONITOR CONTAINS VERDICTS");

    if isViable(mon) == false
    then(
      print_basic("NOT VIABLE");
      true
    ) 
    else ( 
      print_basic("VIABLE");
      print_all_messages("-------------------------------------");

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
                        print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
                        true)
                      else 
                        (let next_m = get_next_unseen relation unseen_cms in 
                          match next_m with 
                          | ([],[]) -> (
                            print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
                            true)
                          | _-> computeSymRelation next_m relation
                        )
                    |s::ss ->
                      print_all_messages ("Reachable Conditions (RC) for SymbolicEvent " ^ pretty_print_sym_event [s]);
                      (*List.sort_uniq drops all the duplicate elements in the list returned by rc*)
                      let c = List.sort_uniq compare (rc (snd cm) s []) in (
                        print_all_messages (pretty_print_evt_list c);
                        
                        let sat_cond = sc (fst cm) c [] in 
                          print_all_messages ("\nSatisfiability Conditions (SC) " ^ (pretty_print_evt_list sat_cond));

                          let rec spa_all_options conds = 
                            match conds with 
                            | [] -> print_all_messages ("there are no more conditions to analyse")
                            | sc1::sc2 -> 
                                let spa_result = spa cm s sc1 [] in 	
                                  print_all_messages ("SPA For condition " ^ (pretty_print_evt_list [sc1]) ^ " is " ^ string_of_bool (spa_result));      
                                  if spa_result (*if spa is true, then saft must also hold, otherwise go to the next condition*)
                                  then (
                                    osaft cm s sc1 relation unseen_cms;
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
    )
  )
