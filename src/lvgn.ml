open Rule_abstraction

type linear_view_info = {
  view_parameters: bool list;
  poc: int;
  soc: int;
}

type linear_view_result = (linear_view_info, unit) result

type predicate_definition_linear_view_infos = linear_view_result PredicateMap.t

let merge_view_parameter_list (list: bool list list): bool list =
  List.fold_left (List.map2(||)) (List.hd list) (List.tl list)

let linear_view_result_of_rule_abstraction (view_name: string) (infos: predicate_definition_linear_view_infos) (rule: rule_abstraction): linear_view_result =
  let is_view_predicate = function
    | ImPred name -> name = view_name
    | ImDeltaInsert _ -> false
    | ImDeltaDelete _ -> false
  in

  let swap_view_parameter_result_list (list: (bool list, unit) result list): (bool list list, unit) result =
    List.fold_left (fun a b -> match (a, b) with
      | _, Result.Error () -> Result.error ()
      | Result.Error (), _ -> Result.error ()
      | Result.Ok xss, Result.Ok ys -> Result.ok (ys :: xss)
    ) (Result.ok []) list
  in

  let merge_view_parameter_result_list (list: (bool list, unit) result list): (bool list, unit) result =
    list |>
    swap_view_parameter_result_list |>
    Result.map merge_view_parameter_list
  in

  let process_bound_predicate (binder: named_var list) (predicate: intermediate_predicate) (arguments: intermediate_argument list): (bool list, unit) result  =
    let bound_pair =
      if is_view_predicate predicate then
        arguments |> List.map(fun a -> (a, true))
      else
        match PredicateMap.find_opt predicate infos with
          | Some (Result.Ok info) -> List.combine arguments info.view_parameters
          | Some (Result.Error _) -> arguments |> List.map(fun a -> (a, false)) (* TODO *)
          | None -> arguments |> List.map(fun a -> (a, false)) (* source or built-in predicate *)
    in

    let has_anonymous_view_patermeters =
      bound_pair |> 
      List.exists (function
        | ImAnonVarArg, true -> true
        | _ -> false
      )
    in

    let view_argument_names =
      bound_pair |> 
      List.filter_map (function
        | ImNamedVarArg named_var, true -> Some named_var
        | _ -> None
      )
    in
    
    if has_anonymous_view_patermeters then
      Result.error ()
    else
      binder |> List.map(fun v -> List.mem v view_argument_names) |> Result.ok
  in

  let process_intermediate_clause (binder: named_var list) (clause: intermediate_clause): (bool list, unit) result =
    match clause with
      | ImPositive (predicate, arguments) -> process_bound_predicate binder predicate arguments
      | ImNegative (predicate, arguments) -> process_bound_predicate binder predicate arguments
      | ImEquation    _ -> binder |> List.map(fun _ -> false) |> Result.ok
      | ImNonequation _ -> binder |> List.map(fun _ -> false) |> Result.ok
      | ImConstTerm   _ -> binder |> List.map(fun _ -> false) |> Result.ok
  in

  let process_rule_abstraction: (bool list, unit) result =
    rule.body |>
    List.map (process_intermediate_clause rule.binder) |>
    merge_view_parameter_result_list
  in

  let poc_of_predicate (predicate: intermediate_predicate): int =
    if is_view_predicate predicate then
      1
    else
      match PredicateMap.find_opt predicate infos with
        | Some(Result.Ok info) -> info.poc
        | Some(Result.Error _) -> 0 (* TODO *)
        | None -> 0
  in

  let poc_of_intermediate_clause (clause: intermediate_clause): int =
    match clause with
      | ImPositive (predicate, _) -> poc_of_predicate predicate
      | ImNegative (predicate, _) -> min (poc_of_predicate predicate) 1
      | ImEquation    _ -> 0
      | ImNonequation _ -> 0
      | ImConstTerm   _ -> 0
  in

  let poc_of_rule_abstraction: int =
    rule.body |>
    List.map poc_of_intermediate_clause |>
    List.fold_left max 0
  in
  
  let soc_of_intermediate_clause (clause: intermediate_clause): int =
    match clause with
      | ImPositive (predicate, _) -> min (poc_of_predicate predicate) 1
      | ImNegative (predicate, _) -> poc_of_predicate predicate
      | ImEquation    _ -> 0
      | ImNonequation _ -> 0
      | ImConstTerm   _ -> 0
  in

  let soc_of_rule_abstraction: int =
    rule.body |>
    List.map soc_of_intermediate_clause |>
    List.fold_left (+) 0
  in
  
  if soc_of_rule_abstraction <= 1 then
    Result.error ()
  else
    process_rule_abstraction |>
    Result.map (fun parameters -> { view_parameters = parameters; poc = poc_of_rule_abstraction; soc = soc_of_rule_abstraction;})
  
let merge_linear_view_result_for_predicate_definition (list: linear_view_result list): linear_view_result =
  List.fold_left (fun r s -> match (r, s) with
      | Result.Ok i, Result.Ok j -> 
        Result.ok {
          view_parameters = List.map2 (||) i.view_parameters j.view_parameters;
          poc = i.poc + j.poc;
          soc = max i.soc j.soc;
        }
      | _, _ -> Result.error ()
    ) (List.hd list) (List.tl list)
