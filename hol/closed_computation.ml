(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/closed_syntax.ml";;
needs "hol/closed_budget.ml";;

module L4_closed_computation : sig
  val convert : conv
  val scope : term -> thm option
  val guard_scope : term -> thm -> thm
  val guard_conversion : term -> term -> thm -> thm
  val clear : unit -> unit
  val stats : unit -> L4_closed_budget.stats
end = struct
  module Budget = L4_closed_budget.Make(struct
    type nonrec term = term
    type typ = hol_type
    let term_view tm =
      if is_var tm then let s,ty = dest_var tm in L4_closed_budget.Atom(s,ty)
      else if is_const tm then let s,ty = dest_const tm in L4_closed_budget.Atom(s,ty)
      else if is_comb tm then let a,b = dest_comb tm in L4_closed_budget.Branch(a,b)
      else let a,b = dest_abs tm in L4_closed_budget.Branch(a,b)
    let type_view ty =
      if is_vartype ty then L4_closed_budget.Type_var(dest_vartype ty)
      else let s,args = dest_type ty in L4_closed_budget.Type_app(s,args)
    let equal a b = a = b
  end)
  let bounded ts = match Budget.measure ts with
    | Some _ -> () | None -> failwith "closed computation size bound"
  let scope_term e = mk_comb(mk_comb(`l4_scoped`,e),`0`)
  let guard_scope e th =
    if hyp th <> [] then failwith "closed scope has hypotheses";
    bounded [e;concl th];
    if concl th <> scope_term e then failwith "closed scope mismatch";
    th
  let guard_conversion tm e th =
    if hyp th <> [] then failwith "closed conversion has hypotheses";
    bounded [tm;e;concl th];
    let l,r = dest_eq(concl th) in
    if l <> tm || r <> e then failwith "closed conversion mismatch";
    th
  let cache = Budget.create (fun th -> [concl th])
  let clear () = Budget.clear cache
  let stats () = Budget.stats cache
  type shape = Closed | Open | Unknown
  let shape e =
    (* This recognizer selects a proof attempt; it never supplies a theorem.
       Non-expression fields may be symbolic, including universe parameters. *)
    let todo = ref [e,0] and result = ref Closed in
    while !result <> Unknown && !todo <> [] do
      match !todo with
      | [] -> ()
      | (tm,depth)::rest ->
        todo := rest;
        let head,args = strip_comb tm in
        if not(is_const head) then result := Unknown else
        match fst(dest_const head),args with
        | "L4BVar",[i] ->
          (try if not(is_numeral i) then result := Unknown
               else if ge_num (dest_numeral i) (num depth) then result := Open
           with Failure _ -> result := Unknown)
        | "L4Sort",[_] | "L4Const",[_;_] | "L4NatLit",[_]
        | "L4StrLit",[_] -> ()
        | "L4App",[f;a] -> todo := (f,depth)::(a,depth)::!todo
        | "L4Lam",[_;a;b] | "L4Pi",[_;a;b] ->
          todo := (a,depth)::(b,depth+1)::!todo
        | "L4Let",[_;a;v;b] ->
          todo := (a,depth)::(v,depth)::(b,depth+1)::!todo
        | "L4Proj",[_;_;major] -> todo := (major,depth)::!todo
        | _ -> result := Unknown
    done;
    !result
  let scope e =
    try
      bounded [e];
      match Budget.find cache e with
      | L4_closed_budget.Positive th -> Some(guard_scope e th)
      | L4_closed_budget.Negative -> None
      | L4_closed_budget.Missing ->
        match shape e with
        | Unknown -> None
        | Open -> ignore(Budget.put cache e None); None
        | Closed ->
          let th = guard_scope e (EQT_ELIM
            ((REWRITE_CONV [l4_scoped] THENC NUM_REDUCE_CONV THENC
              REWRITE_CONV []) (scope_term e))) in
          ignore(Budget.put cache e (Some th)); Some th
    with Failure _ -> None
  let convert tm =
    bounded [tm];
    let head,args = strip_comb tm in
    if not(is_const head) then failwith "not a closed object computation";
    let e,derive = match fst(dest_const head),args with
      | "l4_lift",[e;d;k] -> e,(fun h -> SPECL [d;k]
          (MP (SPEC e l4_lift_closed) h))
      | "l4_subst",[e;k;s] -> e,(fun h -> SPECL [k;s]
          (MP (SPEC e l4_subst_closed) h))
      | "l4_inst",[s;e] -> e,(fun h -> SPEC s
          (MP (SPEC e l4_inst_closed) h))
      | _ -> failwith "not a closed object computation" in
    match scope e with
    | None -> failwith "closed scope unavailable"
    | Some h -> guard_conversion tm e (derive h)
end;;
