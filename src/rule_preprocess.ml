(** 
Functions for preprocesing of IDB rules before
SQL generation.
 *)

open Expr;;
open Lib;;
open Utils;;

(****************************************************)
(*      Recursion check functions                   *)
(****************************************************)

(** Returns true if the provided term is a call to the predicate described
 by the provided key. If the recursive call is negative, an error is raised*)
let rec check_rec_term key = function
    | Rel rt ->
        let rt_key = symtkey_of_rterm rt in
        (key_comp key rt_key) = 0
    | Not rt ->
        if (check_rec_term key (Rel rt)) then
            raise (SemErr (
                "Predicate "^(string_of_symtkey key)^
                " is negatively recursive"
            ))
        else false
    | _ -> false

(** Returns true if the provided rule contains a call to itself.
 * If the recursive call is negative, then an error is raised.
 * If there is more than one recursive call to itself, an error is raised.*)
let is_rec_rule rule =
    let key = symtkey_of_rule rule in
    let body = rule_body rule in
    let rec_eval acc rule =
        if check_rec_term key rule then acc+1 else acc
    in
    let rec_count = List.fold_left rec_eval 0 body in
    if rec_count > 1 then
        raise (SemErr(
            "Predicate "^(string_of_symtkey key)^
            " has more than one recursive call"
        ))
    else
        rec_count = 1

(** Given a list of rules that define a predicate, checks that they satisfy the recursion conditions, which are:
  - There cannot be negative recursive calls.
  - A single rule cannot make more than one recursive call.
  - There is at most one recursive rule.
  - The predicate has a base-case.
 
  If the conditions are satisfied and there is a recursive rule,
  then this recursive rule is placed at the end of the list.
 *)
let check_rec_rule rule_lst =
    let rec_split rule (r_lst,nr_lst) =
        if is_rec_rule rule then (rule::r_lst, nr_lst)
        else (r_lst, rule::nr_lst)
    in
    (*Split the rules in recursive and not revursive*)
    let (r_lst, nr_lst) = List.fold_right rec_split rule_lst ([],[]) in
    (*Check existence of base-case*)
    let key = symtkey_of_rule (List.hd rule_lst) in
    if nr_lst = [] then
        raise (SemErr(
            "Recursive predicate "^(string_of_symtkey key)^
            " does not contain a base case"
        ))
    else
    (*Check that there is no more than one recursive rule
     * and return list with recursion at the end*)
    match r_lst with
        | _::_::_ ->
            raise (SemErr (
                "Predicate "^(string_of_symtkey key)^
                " contains more than one recursive definition"
            ))
        | _ -> nr_lst@r_lst

(****************************************************)
(*      Constant extraction functions               *)
(****************************************************)

(** Extracts constants in a rterm and replaces them with
  ad-hoc NumVars which numbers start from 'pos'. The function
  returns a tuple with the new rterm and a list of equalities
  that must be satisfied by the ad-hoc variables.
 *)
let extract_rterm_constants ?(pos = 0) rt = match rt with
    | Pred (x, vl) ->
        let extract var (v_lst,e_lst,i) = match var with 
            | ConstVar const -> 
                let nvar = NumberedVar i in
                let neq = Equal (Var nvar,Const const) in
                (nvar::v_lst, neq::e_lst,i+1) 
            | _ -> (var::v_lst, e_lst, i) in
        let (vars,eqs,_) = List.fold_right extract vl ([],[],pos) in 
        ( Pred (x,vars), eqs )
    | Deltainsert (x, vl) ->
        let extract var (v_lst,e_lst,i) = match var with 
            | ConstVar const -> 
                let nvar = NumberedVar i in
                let neq = Equal (Var nvar, Const const) in
                (nvar::v_lst, neq::e_lst,i+1) 
            | _ -> (var::v_lst, e_lst, i) in
        let (vars,eqs,_) = List.fold_right extract vl ([],[],pos) in 
        ( Deltainsert (x,vars), eqs )
    | Deltadelete (x, vl) ->
        let extract var (v_lst,e_lst,i) = match var with 
            | ConstVar const -> 
                let nvar = NumberedVar i in
                let neq = Equal (Var nvar, Const const) in
                (nvar::v_lst, neq::e_lst,i+1) 
            | _ -> (var::v_lst, e_lst, i) in
        let (vars,eqs,_) = List.fold_right extract vl ([],[],pos) in 
        ( Deltadelete (x,vars), eqs )

(** Given a rule, extracts all constants in its head and body rterms
  for replacing them with ad-hoc variables placed in the body.
  E.g. "Q(a,b,1) :- P(1,a,c) and R(b,3)." will be transformed to
  "Q(a,b,_0) :- P(_1,a,c) and R(b,_2) and _0 = 1 and _1 = 1 and _2 = 3."
 *)
let extract_rule_constants = function
    | Query _    -> invalid_arg "function extract_rule_constants called with a query"
    | Constraint _    -> invalid_arg "function extract_rule_constants called with a query"
    | Source _    -> invalid_arg "function extract_rule_constants called with a source schema"
    | View _ -> invalid_arg "function extract_rule_constants called with a view schema"
    | Rule(h, b) -> 
        let (h2, h2_e) = extract_rterm_constants h in
        let extract t (t_lst,e_lst,i) = match t with
            | Rel rt -> 
                let (rt2,rt2_e) = extract_rterm_constants ~pos:i rt in
                ((Rel rt2)::t_lst, rt2_e@e_lst, i+(List.length rt2_e) )
            | Not rt -> 
                let (rt2,rt2_e) = extract_rterm_constants ~pos:i rt in
                ((Not rt2)::t_lst, rt2_e@e_lst, i+(List.length rt2_e) )
            | _ -> (t::t_lst, e_lst, i) in
        let (b2,b2_e,_) = List.fold_right extract b ([],[],(List.length h2_e)) in
        Rule (h2,b2@h2_e@b2_e)
;;

let seperate_rules exp = match exp with 
    Expr.Prog lst -> List.partition (fun stt -> (match stt with Expr.Rule _ -> true | _ -> false) ) lst

(** Given a rule, replace AnonVar to a NamedVar*)
let anonvar2namedvar = function
    | Query _    -> invalid_arg "function anonvar2namedvar called with a query"
    | Constraint _    -> invalid_arg "function anonvar2namedvar called with a query"
    | Source _    -> invalid_arg "function anonvar2namedvar called with a source schema"
    | View _ -> invalid_arg "function anonvar2namedvar called with a view schema"
    | Rule(h, b) -> 
        let a2n_varlist lst ind = 
            List.fold_right (fun v (l,i)  -> if (is_anon v) then ((NamedVar ("DUMMY__ANON_"^string_of_int i))::l, i+1) else (v::l), i ) lst ([], ind) in
        let a2n_term t (lst, ind)  = match t with 
            | Rel rt -> (match rt with 
                        | Pred (name, varlst) -> 
                            let nvars, newind = a2n_varlist varlst ind in 
                            (Rel (Pred (name, nvars))::lst, newind)
                        | Deltainsert (name, varlst) -> 
                            let nvars, newind = a2n_varlist varlst ind in 
                            (Rel (Deltainsert (name, nvars))::lst, newind)
                        | Deltadelete (name, varlst) -> 
                            let nvars, newind = a2n_varlist varlst ind in 
                            (Rel (Deltadelete (name, nvars))::lst, newind)
                        )
            | Not rt -> (t::lst, ind)
            (* AnonVar in a negated predicate can not be converted to NamedVar because it make program unsafe *)
            | Equal _ -> (t::lst, ind)
            | Ineq _ -> (t::lst, ind) in
        let newb,_ = List.fold_right a2n_term b ([], 0) in 
        (* print_endline (string_of_stt (Rule(h,newb)));  *)
        Rule(h,newb)
;;

(****************************************************)
(*      Main function                               *)
(****************************************************)

(** Given a symtable, performs preprocess operations over the rules
  contained in it. This operations are:
   - Extraction of constants in predicates
   - Recursion checks (only one recursive rule,
                           only one recursive call in rules,
                           no negated recursions,
                           and base case existance)
                           
 *)
let preprocess_rules (st:symtable) =
    let rep_rule key rules =
        let rep_lst = List.map extract_rule_constants rules in
        let sorted_lst = check_rec_rule rep_lst in
        Hashtbl.replace st key sorted_lst in
    Hashtbl.iter rep_rule st

(** Given a symtable, replace AnonVar to a NamedVar*)
let anon2named_rules (st:symtable) =
    let rep_rule key rules =
        let named_lst = List.map anonvar2namedvar rules in
        Hashtbl.replace st key named_lst in
    Hashtbl.iter rep_rule st

(** Given a query, it returns a 'dummy' idb rule that calculates the desired output,
for example tracks2_prime(TRACK,0,RATING,ALBUM,QUANTITY) will be converted to _dummy_(TRACK,_0,RATING,ALBUM,QUANTITY):- ...
 *)
let rule_of_query query (idb:symtable) =
    let (q2,eqs) = extract_rterm_constants query in
    let dummy = Pred ("__dummy__", get_rterm_varlist q2) in
    Rule (dummy, (Rel q2)::eqs)

(** Takes a list of terms and splits them in positive rterms,
  negative terms, equalities, and inequalities*)
let split_terms terms =
    let rec split t (pos,neg,eq,inq) = match t with
        | Rel rt -> (rt::pos,neg,eq,inq)
        | Not rt -> (pos,rt::neg,eq,inq)
        | Equal _ -> (pos,neg,t::eq,inq) 
        | Ineq _ -> (pos,neg,eq,t::inq) in
    List.fold_right split terms ([],[],[],[])