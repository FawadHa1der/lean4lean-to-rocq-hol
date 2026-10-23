(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED. Theorem-producing evaluation infrastructure.
   See ../API646.txt. No native logical verdict, axiom or expected-answer input. *)
needs "compute.ml";;
needs "calc_num.ml";;

module Kernel_compute646 : sig
  type t
  exception Invalid_equations of string
  exception Undecided of string
  val create : ?conversions:(term * int * conv) list -> thm list -> t
  val numeral_step : thm list -> conv
  val boolean : t -> term -> bool * thm
  val numeral : t -> term -> term * thm
end = struct
  type t = { compset : Compute.compset }
  exception Invalid_equations of string
  exception Undecided of string

  type numeral_rule = {
    head : term;
    arity : int;
    positions : int list;
    equation : thm
  }

  let rec conjuncts th =
    if hyp th <> [] then raise (Invalid_equations "theorem has hypotheses");
    if is_forall (concl th) then conjuncts (SPEC_ALL th)
    else if is_conj (concl th) then
      conjuncts (CONJUNCT1 th) @ conjuncts (CONJUNCT2 th)
    else [th]

  (* Constructor distinctness may be supplied as a proved negation. These
     conversions derive equations; they do not assume their propositions. *)
  let equation th =
    let eq = if is_eq (concl th) then th
      else if is_neg (concl th) then EQF_INTRO th else EQT_INTRO th in
    let left,right = dest_eq (concl eq) in
    let head,_ = strip_comb left in
    if not (is_const head) then
      raise (Invalid_equations "left-hand side has no constant head");
    let variables = frees left in
    if not (List.for_all (fun v -> List.exists (aconv v) variables) (frees right))
    then raise (Invalid_equations "right-hand side has an unbound variable");
    eq

  let equations ths = List.map equation (List.concat (List.map conjuncts ths))

  let successor_variable tm =
    match strip_comb tm with
    | head,[n] when is_const head && fst (dest_const head) = "SUC" -> is_var n
    | _ -> false

  let numeral_rules eqs =
    List.fold_right (fun eq rest ->
      let head,args = strip_comb (lhs (concl eq)) in
      let positions = List.filter_map (fun (i,arg) ->
        if successor_variable arg then Some i else None)
        (List.mapi (fun i arg -> i,arg) args) in
      if positions = [] then rest else
        {head=head;arity=List.length args;positions=positions;equation=eq} :: rest)
      eqs []

  let rec argument_conversion arity index conversion =
    if index < 0 || index >= arity then failwith "numeral argument index";
    if index = arity - 1 then RAND_CONV conversion
    else RATOR_CONV (argument_conversion (arity - 1) index conversion)

  let expand_argument arity index tm =
    let _,args = strip_comb tm in
    let arg = List.nth args index in
    if is_numeral arg && not (aconv arg (mk_small_numeral 0)) then
      argument_conversion arity index num_CONV tm
    else REFL tm

  let apply_rule rule tm =
    let head,args = strip_comb tm in
    if not (is_const head) || fst (dest_const head) <> fst (dest_const rule.head)
       || List.length args <> rule.arity then failwith "numeral rule head/arity";
    let expanded = List.fold_left (fun th position ->
      TRANS th (expand_argument rule.arity position (rhs (concl th))))
      (REFL tm) rule.positions in
    (* Immediately consume SUC syntax with the genuine clause. A general
       arithmetic pass here would collapse it back to a binary numeral. *)
    let rewritten = REWR_CONV rule.equation (rhs (concl expanded)) in
    let before,after = dest_eq (concl rewritten) in
    if aconv before after then failwith "numeral clause is reflexive";
    let th = TRANS expanded rewritten in
    let left,right = dest_eq (concl th) in
    if hyp th <> [] || not (aconv left tm) || aconv left right then
      failwith "numeral rule produced no valid progress";
    th

  let rec try_rules rules tm = match rules with
    | [] -> failwith "no matching numeral recursion equation"
    | rule::rest ->
        try apply_rule rule tm with Failure _ -> try_rules rest tm

  let numeral_step ths = try_rules (numeral_rules (equations ths))

  let checked_conversion conversion tm =
    let th = conversion tm in
    if hyp th <> [] || not (is_eq (concl th)) then
      failwith "attached conversion did not return an unconditional equation";
    let left,right = dest_eq (concl th) in
    if not (aconv left tm) || aconv left right then
      failwith "attached conversion has wrong input or no progress";
    let variables = frees tm in
    if not (List.for_all (fun v -> List.exists (aconv v) variables) (frees right))
    then failwith "attached conversion introduced a free variable";
    th

  let create ?(conversions=[]) ths =
    let eqs = equations ths in
    let rules = numeral_rules eqs in
    let cs = Compute.basic_compset () in
    num_compute_add_convs cs;
    Compute.set_skip cs (parse_term "COND:bool->A->A->A") (Some 1);
    List.iter (fun (head,arity,conversion) ->
      if not (is_const head) || arity < 0 then
        raise (Invalid_equations "invalid conversion head or arity");
      Compute.add_conv (head,arity,checked_conversion conversion) cs) conversions;
    Compute.add_thms eqs cs;
    (* One conversion per exact head/arity; failed pattern matches leave the
       stock rewrite alternatives available. No global compset is changed. *)
    let keys = List.fold_left (fun keys rule ->
      if List.exists (fun (head,arity) -> head = rule.head && arity = rule.arity) keys
      then keys else (rule.head,rule.arity)::keys) [] rules in
    List.iter (fun (head,arity) ->
      let selected = List.filter (fun rule ->
        rule.head = head && rule.arity = arity) rules in
      Compute.add_conv (head,arity,try_rules selected) cs) keys;
    {compset=cs}

  let compute_closed state query =
    if frees query <> [] then raise (Undecided "query has free term variables");
    let th =
      try Compute.WEAK_CBV_CONV state.compset query
      with Failure message -> raise (Undecided ("conversion failed: " ^ message)) in
    if hyp th <> [] then raise (Undecided "result theorem has hypotheses");
    if frees (concl th) <> [] then raise (Undecided "result theorem is not closed");
    if not (is_eq (concl th)) then raise (Undecided "result is not an equation");
    let left,right = dest_eq (concl th) in
    if not (aconv query left) then raise (Undecided "result concerns another query");
    right,th

  let boolean state query =
    if type_of query <> parse_type "bool" then raise (Undecided "query is not boolean");
    let result,th = compute_closed state query in
    if aconv result (mk_const ("T",[])) then true,th
    else if aconv result (mk_const ("F",[])) then false,th
    else raise (Undecided "boolean computation did not reach a literal")

  let numeral state query =
    if type_of query <> parse_type "num" then raise (Undecided "query is not numeric");
    let result,th = compute_closed state query in
    if is_numeral result then result,th
    else raise (Undecided "numeric computation did not reach a numeral")
end;;
