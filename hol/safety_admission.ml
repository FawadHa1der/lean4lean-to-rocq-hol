(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Restricted program declarations remain outside the safe logical environment. *)
needs "hol/safety_syntax.ml";;

module Lean4hol_safety : sig
  type safety = Safe | Partial | Unsafe
  type hint = No_hint | Opaque_hint | Abbrev_hint | Regular_hint of string
  type operation = Safe_step | Unsafe_single | Partial_single | Restricted_mutual
  type marked = {safety:safety; entry:Lean4hol_env.declaration; hint:hint;
    all:Lean4hol.name list}
  type state
  type references = Allowed of thm | Forbidden of thm
  type bridge = Exact | Generated of thm
  val quote_mark : marked -> term
  val quote_marks : marked list -> term
  val quote_operation : operation -> term
  val safe_environment : state -> Lean4hol_env.environment
  val registry : state -> marked list
  val certificate : state -> thm
  val history_term : state -> term
  val expected : state -> term
  val projection_certificate : state -> thm
  val authenticate : state -> thm -> (unit,Lean4hol.error) result
  val start : Lean4hol_env.environment -> (state,Lean4hol.error) result
  val view : state -> safety -> (Lean4hol_env.declaration list * thm,Lean4hol.error) result
  val check_references : state -> safety -> marked list -> (references,Lean4hol.error) result
  val check_fresh : state -> marked list -> (thm,Lean4hol.error) result
  val body_expected : state -> operation -> marked list -> marked -> term
  val authenticate_body : state -> operation -> marked list -> marked -> thm ->
    (unit,Lean4hol.error) result
  val admit_restricted : ?fuel:int -> state -> operation -> marked list ->
    (state,Lean4hol.error) result
  val append_safe : ?fuel:int -> state -> marked list -> Lean4hol_env.environment -> bridge ->
    (state,Lean4hol.error) result
end = struct
  open Lean4hol
  module Env = Lean4hol_env
  module Raw = Lean4hol_raw_ctor
  module Input_cert = Lean4hol_input_certificate
  type safety = Safe | Partial | Unsafe
  type hint = No_hint | Opaque_hint | Abbrev_hint | Regular_hint of string
  type operation = Safe_step | Unsafe_single | Partial_single | Restricted_mutual
  type marked = {safety:safety;entry:Env.declaration;hint:hint;all:name list}
  type state = {env:Env.environment;registry:marked list;history:term list;
    trace:thm;safe_blocks:Env.declaration list list;safe_trace:thm;projection:thm;proof:thm}
  type references = Allowed of thm | Forbidden of thm
  type bridge = Exact | Generated of thm
  let get = function Ok v -> v | Error e -> stop e.kind e.message
  let quote_safety = function Safe->`L4Safe` | Partial->`L4Partial` | Unsafe->`L4Unsafe`
  let quote_operation = function
    | Safe_step->`L4SafeStep` | Unsafe_single->`L4UnsafeSingle`
    | Partial_single->`L4PartialSingle` | Restricted_mutual->`L4RestrictedMutual`
  let quote_hint = function
    | No_hint->`L4NoHint` | Opaque_hint->`L4OpaqueHint` | Abbrev_hint->`L4AbbrevHint`
    | Regular_hint n->node "L4RegularHint" [natural n]
  let quote_names ns = mk_list(List.map quote_name ns,`:l4_name`)
  let quote_mark r = node "L4Mark"
    [quote_safety r.safety;Env.quote_decl r.entry;quote_hint r.hint;quote_names r.all]
  let quote_marks rs = mk_list(List.map quote_mark rs,`:l4_mark`)
  let quote_history hs = mk_list(hs,`:l4_safety_step`)
  let history_term s = quote_history s.history
  let safe_environment s = s.env
  let registry s = s.registry
  let certificate s = s.proof
  let projection_certificate s = s.projection
  let expected_values env registry history = node "l4_safety_full"
    [Env.quote_policy env;quote_marks registry;Env.quote_env env;quote_history history]
  let expected s = expected_values s.env s.registry s.history
  let trace_term env registry history = node "l4_safety_trace"
    [Env.quote_policy env;quote_marks registry;Env.quote_env env;quote_history history]
  let exact tm th =
    if hyp th<>[] || not(aconv(concl th)tm) then
      stop Proof_failure "safety certificate hypotheses or exact conclusion mismatch";
    th
  let equations = Raw.equations @
    [l4_scoped;l4_safety_visible;l4_safety_view;l4_safety_blocked;l4_safety_safe_entries;
     l4_protected_name;l4_primitive_names;l4_nat_name;l4_bool_name;
     l4_mark_safety;l4_mark_entry;l4_mark_hint;l4_mark_all;l4_mark_name;
     l4_safety_refs;l4_safety_rule_refs;l4_safety_role_refs;l4_safety_kind_refs;l4_safety_entry_refs;
     l4_safety_references;l4_safety_fresh;l4_safety_mode;l4_safety_placeholder;l4_safety_fragment;
     l4_safety_definition;l4_safety_shape;l4_safety_step_op;l4_safety_step_raw;
     l4_safety_step_registry;l4_safety_step_env;l4_safety_next_registry;l4_safety_next_env;
     l4_safety_raw_history;l4_safety_safe_history;ITLIST;FILTER;COND_CLAUSES;
     distinctness "l4_safety";distinctness "l4_operation";distinctness "l4_hint";
     injectivity "l4_mark";injectivity "l4_safety_step";injectivity "l4_hint"]
  let calc = REPEATC(CHANGED_CONV
    (computation THENC REWRITE_CONV equations THENC NUM_REDUCE_CONV))
  let assemble definitions tm proofs =
    exact tm (prove(tm,REWRITE_TAC definitions THEN CONV_TAC calc THEN
      REWRITE_TAC (List.map (CONV_RULE calc) proofs)))
  let require st tm message =
    tick st;
    let h=calc tm in
    if rhs(concl h)=`T` then exact tm (EQT_ELIM h)
    else if rhs(concl h)=`F` then
      (ignore(exact(mk_neg tm)(EQF_ELIM h)); stop Invalid_input message)
    else stop Proof_failure ("undecided safety side condition: "^message)
  let authenticate s th = run 100000 [] [] (fun _ -> ignore(exact(expected s)th))
  let authenticated s =
    ignore(exact(expected s)s.proof);
    ignore(exact(trace_term s.env s.registry s.history)s.trace);
    ignore(exact(Input_cert.trace s.env s.safe_blocks)s.safe_trace);
    ignore(exact(Input_cert.expected s.env s.safe_blocks)s.projection)
  let visible mode r = mode=Unsafe || r.safety=Safe || (mode=Partial && r.safety=Partial)
  let entries_view mode registry = List.filter_map(fun r->
    if visible mode r then Some r.entry else None)registry
  let view s mode = run 100000 [] [] (fun st ->
    authenticated s;
    let ds=entries_view mode s.registry in
    let tm=mk_eq(node "l4_safety_view" [quote_safety mode;quote_marks s.registry],Raw.entries ds) in
    ds,require st tm "mode view identity")
  let reference_term s mode raw = node "l4_safety_references"
    [quote_safety mode;quote_marks s.registry;quote_marks raw]
  let check_references s mode raw = run 100000 [] [] (fun st ->
    authenticated s; tick st;
    let tm=reference_term s mode raw in
    let h=calc tm in
    if rhs(concl h)=`T` then Allowed(exact tm(EQT_ELIM h))
    else if rhs(concl h)=`F` then Forbidden(exact(mk_neg tm)(EQF_ELIM h))
    else stop Proof_failure "undecided reference-safety proposition")
  let fresh_term s raw = node "l4_safety_fresh" [quote_marks s.registry;quote_marks raw]
  let check_fresh s raw = run 100000 [] [] (fun st ->
    authenticated s; require st (fresh_term s raw) "duplicate full-registry declaration name")
  let mode op raw = match op,raw with
    | (Safe_step|Partial_single),_ -> Safe
    | _,r::_ -> r.safety
    | _,[] -> stop Invalid_input "empty restricted declaration batch"
  let placeholder r = {r.entry with Env.kind=Env.Axiom;value=None}
  let fragment s op raw =
    let ds=entries_view(mode op raw)s.registry in
    if op=Partial_single then ds else List.map placeholder raw @ ds
  let body_term fragment r =
    let body=match r.entry.Env.value with Some b->b |None->stop Invalid_input "missing restricted body" in
    let qe=Raw.entries fragment in
    mk_conj(node "l4_econtext" [qe;quote_context []],
      node "l4_edef" [qe;quote_context [];quote_expr body;quote_expr body;quote_expr r.entry.Env.typ])
  let body_expected s op raw r = body_term (fragment s op raw) r
  let authenticate_body s op raw r th = run 100000 [] [] (fun _ ->
    authenticated s; ignore(exact(body_expected s op raw r)th))
  let full env registry history trace safe_blocks safe_trace =
    let projection=get(Input_cert.finish env safe_blocks safe_trace) in
    let tm=expected_values env registry history in
    let proof=assemble [l4_safety_full] tm [trace;projection] in
    {env;registry;history;trace;safe_blocks;safe_trace;projection;proof}
  let start env = run 100000 [] [] (fun _ ->
    if Env.declarations env<>[] then stop Unsupported "safety history must start with an empty certified environment";
    let trace=assemble [l4_safety_trace] (trace_term env [] []) [] in
    let safe_trace=Input_cert.start env in full env [] [] trace [] safe_trace)
  let extend_trace s step env registry history step_proof =
    let tm=trace_term env registry history in
    exact tm (prove(tm,GEN_REWRITE_TAC I [l4_safety_trace] THEN CONV_TAC calc THEN
      REWRITE_TAC (List.map(CONV_RULE calc)[s.trace;step_proof])))
  let step_term s op raw ds = node "L4SafetyStep"
    [quote_operation op;quote_marks raw;quote_marks s.registry;Env.quote_env s.env;Raw.entries ds]
  let prior_view s =
    let tm=mk_eq(node "l4_safety_view" [`L4Safe`;quote_marks s.registry],Env.quote_env s.env) in
    exact tm (CONJUNCT2(MP(SPECL [Env.quote_policy s.env;quote_marks s.registry;
      Env.quote_env s.env;history_term s] l4_safety_full_projection)s.proof))
  let admit_restricted ?(fuel=100000) s op raw = run fuel [] [] (fun st ->
    authenticated s;
    if List.exists(fun r->match r.entry.Env.kind with
      | Env.Axiom | Env.Opaque | Env.Generated _ -> true | _ -> false)raw
    then stop Unsupported "unsafe axiom/opaque/inductive admission remains outside this slice";
    let qo=quote_operation op and qr=quote_marks raw and qs=quote_marks s.registry in
    let shape=require st (node "l4_safety_shape" [qo;qr]) "restricted operation/scope/parameter shape" in
    let fresh=get(check_fresh s raw) in
    let refs=match get(check_references s (mode op raw) raw) with
      | Allowed h->h | Forbidden _->stop Invalid_input "forbidden reference in restricted declaration" in
    let prior,view_proof=get(view s (mode op raw)) in
    let headers=List.map(fun r->
      let u,h=get(Env.fragment_sort ~fuel:st.remaining prior [] r.entry.Env.typ) in
      let ex=mk_exists(`u:l4_level`,node "l4_raw_sort"
        [Raw.entries prior;quote_context [];quote_expr r.entry.Env.typ;`u:l4_level`]) in
      let exists=EXISTS(ex,quote_level u)h in
      let target=node "l4_safety_header" [Raw.entries prior;quote_mark r] in
      assemble [l4_safety_header] target [exists])raw in
    (* No placeholder is constructed or made visible before every header passes. *)
    let frag=fragment s op raw in
    let fragment_identity=require st (mk_eq(node "l4_safety_fragment" [qo;qs;qr],Raw.entries frag))
      "temporary fragment identity" in
    let bodies=List.map(fun r->
      let b=match r.entry.Env.value with Some b->b | None->stop Invalid_input "missing definition body" in
      let h=get(Env.fragment_check ~fuel:st.remaining frag [] b r.entry.Env.typ) in
      ignore(exact(body_term frag r)h);
      assemble [l4_safety_body] (node "l4_safety_body" [Raw.entries frag;quote_mark r]) [h])raw in
    let admitted=node "l4_safety_restricted" [qo;qs;qr] in
    let block=assemble [l4_safety_restricted] admitted
      (shape::fresh::refs::view_proof::fragment_identity::headers@bodies) in
    let step=step_term s op raw [] in
    let step_valid=node "l4_safety_step_valid" [Env.quote_policy s.env;step] in
    let hp=assemble [l4_safety_step_valid] step_valid [Env.certificate s.env;prior_view s;block] in
    let registry=raw@s.registry and history=step::s.history in
    let trace=extend_trace s step s.env registry history hp in
    full s.env registry history trace s.safe_blocks s.safe_trace)
  let append_safe ?(fuel=100000) s raw next bridge = run fuel [] [] (fun st ->
    authenticated s;
    let entries=List.map(fun r->r.entry)raw in
    let count=List.length(Env.declarations next)-List.length(Env.declarations s.env) in
    if count<0 then stop Proof_failure "safe environment shrank";
    let ds=List.filteri(fun i _->i<count)(Env.declarations next) in
    let canonical=List.map(fun d->{safety=Safe;entry=d;hint=No_hint;all=[]})ds in
    ignore(require st (mk_eq(Env.quote_env next,Raw.entries(ds@Env.declarations s.env))) "safe prefix identity");
    ignore(exact(node "l4_evalid" [Env.quote_policy s.env;Env.quote_env next])(Env.certificate next));
    let fresh=get(check_fresh s raw) and canonical_fresh=get(check_fresh s canonical) in
    let refs=match get(check_references s Safe raw) with
      | Allowed h->h |Forbidden _->stop Invalid_input "forbidden safe declaration reference" in
    let qr=quote_marks raw in
    let safe=require st (list_mk_comb(`ALL:(l4_mark->bool)->l4_mark list->bool`,
      [mk_abs(`r:l4_mark`,mk_eq(node "l4_mark_safety" [`r:l4_mark`],`L4Safe`));qr]))
      "unsafe entry cannot be a safe step" in
    let exact_meta=node "l4_metadata_matches" [Raw.entries entries;Raw.entries ds] in
    let generated=node "l4_raw_generated_admitted"
      [Env.quote_policy s.env;Env.quote_env s.env;Raw.entries entries;Raw.entries ds;Env.quote_env next] in
    let bridge_proof,safe_trace=match bridge with
      | Exact ->
        let h=require st exact_meta "raw/canonical safe metadata mismatch" in
        DISJ1 h generated,get(Input_cert.append_exact s.env next s.safe_blocks entries s.safe_trace)
      | Generated h ->
        let h=exact generated h in
        DISJ2 exact_meta h,get(Input_cert.append_generated s.env next s.safe_blocks entries ds s.safe_trace h) in
    let step=step_term s Safe_step raw ds in
    let hp=assemble [l4_safety_step_valid]
      (node "l4_safety_step_valid" [Env.quote_policy s.env;step])
      [Env.certificate s.env;prior_view s;safe;fresh;refs;canonical_fresh;Env.certificate next;bridge_proof] in
    let registry=canonical@s.registry and history=step::s.history in
    let trace=extend_trace s step next registry history hp in
    full next registry history trace (entries::s.safe_blocks) safe_trace)
end;;
