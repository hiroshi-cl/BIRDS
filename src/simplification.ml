
open Expr
open Utils


let const_equal (c1 : const) (c2 : const) : bool =
  match (c1, c2) with
  | (Int n1, Int n2)       -> Int.equal n1 n2
  | (Real r1, Real r2)     -> Float.equal r1 r2 (* Not conform to IEEE754’s equality *)
  | (String s1, String s2) -> String.equal s1 s2
  | (Bool b1, Bool b2)     -> Bool.equal b1 b2
  | (Null, Null)           -> true
  | _                      -> false


type table_name = string

type var_name = string

type intermediate_predicate =
  | ImPred        of table_name
  | ImDeltaInsert of table_name
  | ImDeltaDelete of table_name

type intermediate_head_var =
  | ImHeadVar of var_name


let head_var_equal (ImHeadVar x1) (ImHeadVar x2) =
  String.equal x1 x2


type intermediate_body_var =
  | ImBodyNamedVar of var_name
  | ImBodyAnonVar


let body_var_compare (imbvar1 : intermediate_body_var) (imbvar2 : intermediate_body_var) : int =
  match (imbvar1, imbvar2) with
  | (ImBodyNamedVar x1, ImBodyNamedVar x2) -> String.compare x1 x2
  | (ImBodyNamedVar _, ImBodyAnonVar)      -> 1
  | (ImBodyAnonVar, ImBodyAnonVar)         -> 0
  | (ImBodyAnonVar, ImBodyNamedVar _)      -> -1


module Predicate = struct
  type t = intermediate_predicate

  let compare (impred1 : t) (impred2 : t) : int =
    match (impred1, impred2) with
    | (ImPred t1, ImPred t2)               -> String.compare t1 t2
    | (ImPred _, _)                        -> 1
    | (_, ImPred _)                        -> -1
    | (ImDeltaInsert t1, ImDeltaInsert t2) -> String.compare t1 t2
    | (ImDeltaInsert _, _)                 -> 1
    | (_, ImDeltaInsert _)                 -> -1
    | (ImDeltaDelete t1, ImDeltaDelete t2) -> String.compare t1 t2
end

module PredicateMap = Map.Make(Predicate)

module PredicateSet = Set.Make(Predicate)

module VariableMap = Map.Make(String)


type body_term_arguments = intermediate_body_var list


module BodyTermArguments = struct
  type t = body_term_arguments

  let compare =
    List.compare body_var_compare
end

module BodyTermArgumentsSet = Set.Make(BodyTermArguments)


type predicate_map = BodyTermArgumentsSet.t PredicateMap.t

type equation_map = const VariableMap.t

type intermediate_rule = {
  head_predicate : intermediate_predicate;
  head_arguments : intermediate_head_var list;
  positive_terms : predicate_map;
  negative_terms : predicate_map;
  equations      : equation_map;
}

type error =
  | UnexpectedHeadVarForm   of var
  | UnexpectedBodyVarForm   of var
  | UnsupportedEquation     of eterm
  | NonequalityNotSupported of eterm


let predicate_equal (impred1 : intermediate_predicate) (impred2 : intermediate_predicate) : bool =
  match (impred1, impred2) with
  | (ImPred t1, ImPred t2)               -> String.equal t1 t2
  | (ImDeltaInsert t1, ImDeltaInsert t2) -> String.equal t1 t2
  | (ImDeltaDelete t1, ImDeltaDelete t2) -> String.equal t1 t2
  | _                                    -> false


let predicate_map_equal : predicate_map -> predicate_map -> bool =
  PredicateMap.equal BodyTermArgumentsSet.equal


let rule_equal (imrule1 : intermediate_rule) (imrule2 : intermediate_rule) : bool =
  List.fold_left ( && ) true [
    predicate_equal imrule1.head_predicate imrule2.head_predicate;
    List.equal head_var_equal imrule1.head_arguments imrule2.head_arguments;
    predicate_map_equal imrule1.positive_terms imrule2.positive_terms;
    predicate_map_equal imrule1.negative_terms imrule2.negative_terms;
    VariableMap.equal const_equal imrule1.equations imrule2.equations;
  ]


let convert_head_var (var : var) : (intermediate_head_var, error) result =
  let open ResultMonad in
  match var with
  | NamedVar x -> return (ImHeadVar x)
  | _          -> err (UnexpectedHeadVarForm var)


let convert_body_var (var : var) : (intermediate_body_var, error) result =
  let open ResultMonad in
  match var with
  | NamedVar x -> return (ImBodyNamedVar x)
  | AnonVar    -> return ImBodyAnonVar
  | _          -> err (UnexpectedBodyVarForm var)


let separate_predicate_and_vars (rterm : rterm) : intermediate_predicate * var list =
  match rterm with
  | Pred (t, vars)        -> (ImPred t, vars)
  | Deltainsert (t, vars) -> (ImDeltaInsert t, vars)
  | Deltadelete (t, vars) -> (ImDeltaDelete t, vars)


let convert_head_rterm (rterm : rterm) : (intermediate_predicate * intermediate_head_var list, error) result =
  let open ResultMonad in
  let (impred, vars) = separate_predicate_and_vars rterm in
  vars |> mapM convert_head_var >>= fun imhvars ->
  return (impred, imhvars)


let convert_body_rterm (rterm : rterm) : (intermediate_predicate * intermediate_body_var list, error) result =
  let open ResultMonad in
  let (impred, vars) = separate_predicate_and_vars rterm in
  vars |> mapM convert_body_var >>= fun imbvars ->
  return (impred, imbvars)


let convert_eterm (eterm : eterm) : (var_name * const, error) result =
  let open ResultMonad in
  match eterm with
  | Equation("=", Var (NamedVar x), Const c)          -> return (x, c)
  | Equation("=", Var (NamedVar x), Var (ConstVar c)) -> return (x, c)
  | Equation("=", Const c, Var (NamedVar x))          -> return (x, c)
  | Equation("=", Var (ConstVar c), Var (NamedVar x)) -> return (x, c)
  | _                                                 -> err (UnsupportedEquation eterm)


let extend_predicate_map (impred : intermediate_predicate) (args : intermediate_body_var list) (predmap : predicate_map) : predicate_map =
  let argsset =
    match predmap |> PredicateMap.find_opt impred with
    | None          -> BodyTermArgumentsSet.empty
    | Some(argsset) -> argsset
  in
  predmap |> PredicateMap.add impred (argsset |> BodyTermArgumentsSet.add args)


let check_equation_map (x : var_name) (c : const) (eqnmap : equation_map) : equation_map option =
  match eqnmap |> VariableMap.find_opt x with
  | None ->
      Some (eqnmap |> VariableMap.add x c)

  | Some c0 ->
      if const_equal c0 c then
        Some eqnmap
      else
        None


(* Converts rules to intermediate ones.
   The application `convert_rule rule` returns:
   - `Error _` if `rule` is syntactically incorrect (or in unsupported form),
   - `Ok None` if it turns out that `rule` is syntactically correct but
     obviously unsatisfiable according to its equations, or
   - `Ok (Some imrule)` otherwise, i.e., if `rule` can be successfully converted to `imrule`. *)
let convert_rule (rule : rule) : (intermediate_rule option, error) result =
  let open ResultMonad in
  let (head, body) = rule in
  convert_head_rterm head >>= fun (impred_head, imhvars) ->
  body |> foldM (fun opt term ->
    match opt with
    | None ->
        return None

    | Some (predmap_pos, predmap_neg, eqnmap) ->
        begin
          match term with
          | Rel rterm ->
              convert_body_rterm rterm >>= fun (impred, imbvars) ->
              let predmap_pos = predmap_pos |> extend_predicate_map impred imbvars in
              return (Some (predmap_pos, predmap_neg, eqnmap))

          | Not rterm ->
              convert_body_rterm rterm >>= fun (impred, imbvars) ->
              let predmap_neg = predmap_neg |> extend_predicate_map impred imbvars in
              return (Some (predmap_pos, predmap_neg, eqnmap))

          | Equat eterm ->
              convert_eterm eterm >>= fun (x, c) ->
              begin
                match eqnmap |> check_equation_map x c with
                | None ->
                  (* If it turns out that the list of equations are unsatisfiable: *)
                    return None

                | Some eqnmap ->
                    return (Some (predmap_pos, predmap_neg, eqnmap))
              end

          | Noneq eterm ->
              err (NonequalityNotSupported eterm)
        end
  ) (Some (PredicateMap.empty, PredicateMap.empty, VariableMap.empty)) >>= fun opt ->
  return (opt |> Option.map (fun (predmap_pos, predmap_neg, eqnmap) ->
    {
      head_predicate = impred_head;
      head_arguments = imhvars;
      positive_terms = predmap_pos;
      negative_terms = predmap_neg;
      equations      = eqnmap;
    }))


type occurrence_count_map = int VariableMap.t


let increment_occurrence_count (x : var_name) (count_map : occurrence_count_map) : occurrence_count_map =
  match count_map |> VariableMap.find_opt x with
  | None       -> count_map |> VariableMap.add x 1
  | Some count -> count_map |> VariableMap.add x (count + 1)


let has_only_one_occurrence (count_map : occurrence_count_map) (x : var_name) : bool =
  match count_map |> VariableMap.find_opt x with
  | Some 1 -> true
  | _      -> false


let fold_predicate_map_for_counting (predmap : predicate_map) (count_map : occurrence_count_map) : occurrence_count_map =
  PredicateMap.fold (fun impred argsset count_map ->
    BodyTermArgumentsSet.fold (fun args count_map ->
      args |> List.fold_left (fun count_map arg ->
        match arg with
        | ImBodyNamedVar x -> count_map |> increment_occurrence_count x
        | ImBodyAnonVar    -> count_map
      ) count_map
    ) argsset count_map
  ) predmap count_map


let erase_sole_occurrences_in_predicate_map (count_map : occurrence_count_map) (predmap : predicate_map) : predicate_map =
  predmap |> PredicateMap.map (fun argsset ->
    argsset |> BodyTermArgumentsSet.map (fun args ->
      args |> List.map (fun arg ->
        match arg with
        | ImBodyNamedVar x ->
            if x |> has_only_one_occurrence count_map then
              ImBodyAnonVar
            else
              arg

      | ImBodyAnonVar ->
          arg
      )
    )
  )


let erase_sole_occurrences (imrule : intermediate_rule) : intermediate_rule =
  let { head_predicate; head_arguments; positive_terms; negative_terms; equations } = imrule in

  (* Counts occurrence of each variables: *)
  let count_map =
    VariableMap.empty
      |> fold_predicate_map_for_counting positive_terms
      |> fold_predicate_map_for_counting negative_terms
      |> VariableMap.fold (fun x _c count_map -> count_map |> increment_occurrence_count x) equations
  in

  (* Removes variables occurring in head arguments: *)
  let count_map =
    head_arguments |> List.fold_left (fun count_map (ImHeadVar x) ->
      count_map |> VariableMap.remove x
    ) count_map
  in

  (* Converts variables that have only one occurrence with the underscore: *)
  let positive_terms = positive_terms |> erase_sole_occurrences_in_predicate_map count_map in
  let negative_terms = negative_terms |> erase_sole_occurrences_in_predicate_map count_map in
  let equations =
    VariableMap.fold (fun x c equations_new ->
      if x |> has_only_one_occurrence count_map then
        equations_new
      else
        equations_new |> VariableMap.add x c
    ) equations VariableMap.empty
  in
  { head_predicate; head_arguments; positive_terms; negative_terms; equations }


let is_looser ~than:(args1 : body_term_arguments) (args2 : body_term_arguments) : bool =
  match List.combine args1 args2 with
  | exception Invalid_argument _ ->
      false

  | zipped ->
      zipped |> List.for_all (function
      | (_, ImBodyAnonVar)                     -> true
      | (ImBodyAnonVar, ImBodyNamedVar _)      -> false
      | (ImBodyNamedVar x1, ImBodyNamedVar x2) -> String.equal x1 x2
      )


let remove_looser_positive_terms (argsset : BodyTermArgumentsSet.t) : BodyTermArgumentsSet.t =
  let rec aux (acc : body_term_arguments list) ~(criterion : body_term_arguments) (targets : body_term_arguments list) =
    match targets |> List.filter (fun target -> not (is_looser ~than:criterion target)) with
    | [] ->
        BodyTermArgumentsSet.of_list acc

    | head :: tail ->
        aux (criterion :: acc) ~criterion:head tail
  in
  (* Sorted in descending lexicographical order as to variable name lists: *)
  let argss_sorted_desc = argsset |> BodyTermArgumentsSet.elements |> List.rev in
  match argss_sorted_desc with
  | [] ->
      argsset

  | head :: tail ->
      aux [] ~criterion:head tail


let remove_looser_negative_terms (argsset : BodyTermArgumentsSet.t) : BodyTermArgumentsSet.t =
  let rec aux (acc : body_term_arguments list) ~(criterion : body_term_arguments) (targets : body_term_arguments list) =
    match targets |> List.filter (fun target -> is_looser ~than:criterion target) with
    | [] ->
        BodyTermArgumentsSet.of_list acc

    | head :: tail ->
        aux (criterion :: acc) ~criterion:head tail
  in
  (* Sorted in ascending lexicographical order as to variable name lists: *)
  let argss_sorted_asc = argsset |> BodyTermArgumentsSet.elements in
  match argss_sorted_asc with
  | [] ->
      argsset

  | head :: tail ->
      aux [] ~criterion:head tail


let remove_looser_terms (imrule : intermediate_rule) : intermediate_rule =
  let { head_predicate; head_arguments; positive_terms; negative_terms; equations } = imrule in
  let positive_terms = positive_terms |> PredicateMap.map remove_looser_positive_terms in
  let negative_terms = negative_terms |> PredicateMap.map remove_looser_negative_terms in
  { head_predicate; head_arguments; positive_terms; negative_terms; equations }


let simplify_rule_step (imrule : intermediate_rule) : intermediate_rule =
  let imrule = erase_sole_occurrences imrule in
  remove_looser_terms imrule


let rec simplify_rule_recursively (imrule1 : intermediate_rule) : intermediate_rule =
  let imrule2 = simplify_rule_step imrule1 in
  if rule_equal imrule1 imrule2 then
  (* If the simplification reaches a fixpoint: *)
    imrule2
  else
    simplify_rule_recursively imrule2


let has_contradicting_body (imrule : intermediate_rule) : bool =
  let { positive_terms; negative_terms; _ } = imrule in
  let dom =
    PredicateSet.empty
      |> PredicateMap.fold (fun impred _ dom -> dom |> PredicateSet.add impred) positive_terms
      |> PredicateMap.fold (fun impred _ dom -> dom |> PredicateSet.add impred) negative_terms
  in
  PredicateSet.fold (fun impred found ->
    if found then
      true
    else
      match (positive_terms |> PredicateMap.find_opt impred, negative_terms |> PredicateMap.find_opt impred) with
      | (Some argsset_pos, Some argsset_neg) ->
          let argss_pos = BodyTermArgumentsSet.elements argsset_pos in
          let argss_neg = BodyTermArgumentsSet.elements argsset_neg in
          let posnegs =
            argss_pos |> List.map (fun args_pos ->
              argss_neg |> List.map (fun args_neg -> (args_pos, args_neg))
            ) |> List.concat
          in
          posnegs |> List.exists (fun (args_pos, args_neg) ->
            is_looser ~than:args_pos args_neg
          )

      | _ ->
          false
  ) dom false


let simplify (rules : rule list) =
  let open ResultMonad in

  (* Converts each rule to an intermediate rule (with unsatisfiable ones removed): *)
  rules |> foldM (fun imrule_acc rule ->
    convert_rule rule >>= function
    | None        -> return imrule_acc
    | Some imrule -> return (imrule :: imrule_acc)
  ) [] >>= fun imrule_acc ->
  let imrules = List.rev imrule_acc in

  (* Performs per-rule simplification: *)
  let imrules = imrules |> List.map simplify_rule_recursively in

  (* Remove rules that have a contradicting body: *)
  let _imrules = imrules |> List.filter (fun imrule -> not (has_contradicting_body imrule)) in

  failwith "TODO: simplify"
