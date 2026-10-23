needs "hol/private_boot.ml";;
let indexed_control_trace_count=List.length(CONJUNCTS l4_input_trace_RULES);;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let module R=Lean4hol_raw_ctor in
  let module I=Lean4hol_raw_indexed in
  let module B=Lean4hol_ctor_bridge in
  let get=function Ok x->x|Error e->failwith e.H.message in
  let closed h=if hyp h<>[] || frees(concl h)<>[] then failwith "open control proof" in
  let group=Sys.getenv "COMPOSE_GROUP" in
  let prior=ref A.empty and claims=ref [] in
  List.iter(fun(_,d)->match d with
    | Hol_input.Definition(h,v) -> prior:=fst(get(A.admit !prior
      {A.kind=A.Definition;name=Hol_check.name h.Hol_input.name;
       params=List.map Hol_check.name h.Hol_input.params;typ=Hol_check.expr h.Hol_input.typ;
       value=Some(Hol_check.expr v)}))
    | Hol_input.Inductive cs -> claims:=List.map Hol_check.claim cs
    | _ -> failwith "unexpected prerequisite")
    (Hol_input.read_file "arena/corpus/tutorial/119_reduceCtorParamRefl.mk.ndjson");
  let prior= !prior and raw= !claims in
  let header=List.hd raw in
  let ctor=List.find(fun d->match d.A.kind with A.Generated(A.Constructor_role _)->true|_->false)raw in
  let parameter,u=match header.A.typ with H.Pi(n,a,H.Sort u)->(n,a),u
    | _->failwith "unexpected raw header" in
  let b={A.indexed_name=header.A.name;indexed_level_params=header.A.params;
    indexed_parameters=[parameter];indices=[];indexed_result_level=u;
    indexed_constructors=[{A.indexed_ctor_name=ctor.A.name;
      indexed_fields=[A.Index_function([H.Bvar 0],[])];result_indices=[]}];indexed_claims=[]} in
  let canonical=A.generate_indexed {H.remaining=100000} b ~large:true ~k:false in
  let b={b with A.indexed_claims=canonical} in
  let next,valid=get(A.admit_indexed_inductive prior b) in
  closed valid;
  let positive label next b claims =
    let proof=get(I.certify prior next claims b) in
    ignore(R.exact(I.expected prior next claims b.A.indexed_claims)proof);
    closed proof;Printf.printf "INDEXED_POSITIVE %s exact_closed\n%!" label in
  positive "authentic119_control" next b raw;
  let count=ref 0 in
  let decline label result=match result with
    | Error e when e.H.kind<>H.Resource ->
      incr count;Printf.printf "INDEXED_DECLINE %s %s\n%!" label e.H.message
    | Error _ -> failwith("resource exhaustion is not a negative control: "^label)
    | Ok _ -> failwith("negative control accepted: "^label) in
  let reject label claims=decline label(I.certify prior next claims b) in
  let replace_ctor d=List.map(fun old->if old.A.name=ctor.A.name then d else old)raw in
  let with_field f=replace_ctor {ctor with A.typ=match ctor.A.typ with
    | H.Pi(n,a,H.Pi(m,_,r))->H.Pi(n,a,H.Pi(m,f,r))
    | _->failwith "unexpected constructor"} in
  let family x=H.App(H.Const(header.A.name,List.map(fun p->H.Param p)header.A.params),x) in
  let arrow a body=H.Pi(H.Anonymous,a,body) in
  let beta x=H.App(H.Lam(H.Anonymous,H.Sort(H.Succ H.Zero),H.Bvar 0),x) in
  let canonical_ctor=List.find(fun d->d.A.name=ctor.A.name)canonical in
  let typed_entry claims =
    let d=List.find(fun d->d.A.name=ctor.A.name)claims in
    let _,formation=get(A.fragment_sort (header::A.declarations prior) [] d.A.typ) in
    closed formation;
    closed(get(H.run 100000 [] [] (fun st->B.entry st (ref "typed negative") next d canonical_ctor))) in
  (match group with
  | "positive" ->
    let let_field=arrow(H.Bvar 0)
      (H.Let(H.Anonymous,H.Sort(H.Succ H.Zero),family(H.Bvar 1),H.Bvar 0)) in
    positive "typed_let_body" next b (with_field let_field);
    let head_beta=arrow(H.Bvar 0)(beta(family(H.Bvar 1))) in
    positive "typed_beta_body" next b (with_field head_beta)
  | "domain-positive" ->
    let domain=beta(H.Bvar 0) in
    let c={A.indexed_ctor_name=ctor.A.name;
      indexed_fields=[A.Index_function([domain],[])];result_indices=[]} in
    let b2={b with A.indexed_constructors=[c];indexed_claims=[]} in
    let b2={b2 with A.indexed_claims=A.generate_indexed {H.remaining=100000} b2 ~large:true ~k:false} in
    let next2,_=get(A.admit_indexed_inductive prior b2) in
    let field=arrow domain(family(H.Bvar 1)) in
    decline "domain_change_without_matching_rhs" (I.certify prior next2 (with_field field) b2);
    let raw2=List.map(fun d->if d.A.name<>ctor.A.name then d else
      {d with A.typ=match ctor.A.typ with
       | H.Pi(n,a,H.Pi(m,_,r))->H.Pi(n,a,H.Pi(m,field,r))
       | _->failwith "unexpected domain control"})b2.A.indexed_claims in
    positive "unreduced_typed_domain_retained" next2 b2 raw2
  | "domain" ->
    let alias=H.Const(H.Str(H.Anonymous,"constType"),[]) in
    let hidden=H.App(H.App(alias,H.Bvar 0),family(H.Bvar 0)) in
    let claims=with_field(arrow hidden(family(H.Bvar 1))) in
    typed_entry claims;
    print_endline "INDEXED_TYPED_CONTROL hidden_domain_has_closed_formation_and_entry_bridge";
    reject "hidden_unreduced_domain_occurrence" claims;
    reject "negative_function_domain" (with_field(arrow(family(H.Bvar 0))(family(H.Bvar 1))));
    let claims=with_field(arrow(H.Bvar 0)(family(beta(H.Bvar 1)))) in
    typed_entry claims;
    print_endline "INDEXED_TYPED_CONTROL nonuniform_beta_has_closed_formation_and_entry_bridge";
    reject "nonuniform_beta_recursive_parameter" claims
  | "telescope" ->
    let c={A.indexed_ctor_name=ctor.A.name;
      indexed_fields=[A.Index_function([H.Bvar 0;H.Bvar 1],[])];result_indices=[]} in
    let b2={b with A.indexed_constructors=[c];indexed_claims=[]} in
    let canonical2=A.generate_indexed {H.remaining=100000} b2 ~large:true ~k:false in
    let b2={b2 with A.indexed_claims=canonical2} in
    let next2,_=get(A.admit_indexed_inductive prior b2) in
    let claims2 field=List.map(fun d->if d.A.name<>ctor.A.name then d else
      {d with A.typ=match ctor.A.typ with
       | H.Pi(n,a,H.Pi(m,_,r))->H.Pi(n,a,H.Pi(m,field,r))
       | _->failwith "unexpected telescope control"})canonical2 in
    let two domain body=arrow(H.Bvar 0)(arrow domain body) in
    let good=two(H.Bvar 1)
      (H.Let(H.Anonymous,H.Sort(H.Succ H.Zero),family(H.Bvar 2),H.Bvar 0)) in
    positive "two_binder_typed_let_telescope" next2 b2 (claims2 good);
    let typed2 claims=
      let d=List.find(fun d->d.A.name=ctor.A.name)claims in
      let can=List.find(fun d->d.A.name=ctor.A.name)canonical2 in
      closed(snd(get(A.fragment_sort(header::A.declarations prior)[] d.A.typ)));
      closed(get(H.run 100000 [] [] (fun st->B.entry st(ref "nested typed negative")next2 d can))) in
    let hidden=H.App(H.App(H.Const(H.Str(H.Anonymous,"constType"),[]),H.Bvar 1),family(H.Bvar 1)) in
    let claims=claims2(two hidden(family(H.Bvar 2))) in
    typed2 claims;
    print_endline "INDEXED_TYPED_CONTROL second_domain_has_closed_formation_and_entry_bridge";
    decline "hidden_second_domain_occurrence" (I.certify prior next2 claims b2);
    let claims=claims2(two(H.Bvar 1)(family(beta(H.Bvar 2)))) in
    typed2 claims;
    print_endline "INDEXED_TYPED_CONTROL nested_nonuniform_has_closed_formation_and_entry_bridge";
    decline "nonuniform_parameter_under_two_binders" (I.certify prior next2 claims b2)
  | "formation" ->
    let bad_parameter=H.App(H.Lam(H.Anonymous,H.Sort H.Zero,H.Sort(H.Succ H.Zero)),H.Sort H.Zero) in
    reject "reducible_illtyped_parameter" (replace_ctor {ctor with A.typ=match ctor.A.typ with
      | H.Pi(n,_,body)->H.Pi(n,bad_parameter,body)|_->failwith "parameter missing"});
    let badlet=arrow(H.Bvar 0)
      (H.Let(H.Anonymous,H.Sort H.Zero,H.Sort(H.Succ H.Zero),family(H.Bvar 2))) in
    reject "erased_illtyped_let_in_function_body" (with_field badlet);
    let wronglevel=H.App(H.Const(header.A.name,[H.Zero]),H.Bvar 1) in
    reject "wrong_recursive_universe_application" (with_field(arrow(H.Bvar 0)wronglevel))
  | "metadata" ->
    reject "constructor_numfields_tamper" (replace_ctor {ctor with A.kind=match ctor.A.kind with
      | A.Generated(A.Constructor_role c)->A.Generated(A.Constructor_role {c with A.num_fields=2})
      | _->failwith "not constructor"});
    reject "original_reflexive_flag_tamper" (List.map(fun d->if d.A.name<>header.A.name then d else
      {d with A.kind=match d.A.kind with
       | A.Generated(A.Inductive_role i)->A.Generated(A.Inductive_role {i with A.is_reflexive=false})
       | _->failwith "not header"})raw);
    decline "wrong_prior_anchor" (I.certify A.empty next raw b)
  | "rhs" ->
    let mutate f=List.map(fun d->match d.A.kind with
      | A.Generated(A.Recursor_role r)->{d with A.kind=A.Generated(A.Recursor_role
        {r with A.rules=List.map(fun (rule:A.rec_rule)->{rule with A.rhs=f rule.A.rhs})r.A.rules})}
      | _->d)raw in
    reject "rhs_computational_tamper" (mutate(fun _->H.Sort H.Zero));
    reject "rhs_erased_illtyped_annotation" (mutate(function
      | H.Lam(n,a,body)->H.Lam(n,H.Let(H.Anonymous,H.Sort H.Zero,H.Sort(H.Succ H.Zero),a),body)
      | _->failwith "raw RHS is not a lambda"));
    let wrong=List.map(fun d->if d.A.name=header.A.name then {d with A.params=[H.Anonymous]} else d)canonical in
    decline "wrong_canonical_anchor" (I.certify prior next raw {b with A.indexed_claims=wrong})
  | "result" ->
    let changed=replace_ctor {ctor with A.typ=match ctor.A.typ with
      | H.Pi(n,a,H.Pi(m,f,_))->H.Pi(n,a,H.Pi(m,f,family(beta(H.Bvar 1))))
      | _->failwith "unexpected result"} in
    let d=List.find(fun d->d.A.name=ctor.A.name)changed in
    closed(snd(get(A.fragment_sort(header::A.declarations prior)[] d.A.typ)));
    let ty,_=get(A.infer next [] d.A.typ) in
    closed(get(A.convert next [] d.A.typ canonical_ctor.A.typ ty));
    print_endline "INDEXED_TYPED_CONTROL result_beta_has_closed_formation_and_signature_conversion";
    reject "nonuniform_beta_constructor_result" changed;
    let forward=H.Let(H.Anonymous,ctor.A.typ,H.Const(ctor.A.name,[]),family(H.Bvar 2)) in
    reject "header_only_fragment_excludes_constructor" (with_field(arrow(H.Bvar 0)forward))
  | _ -> failwith "unknown indexed control group");
  let expected=match group with "positive"->0|"domain-positive"->1|"result"|"telescope"->2|_->3 in
  if !count<>expected then failwith "negative count mismatch";
  if private_native_rule_count<>29 || private_admission_rule_count<>11 || indexed_control_trace_count<>3 ||
     axioms()<>private_axioms then failwith "rule or axiom change";
  Printf.printf "PRIVATE_INDEXED_CONTROLS_DONE %s positive_gate %d_declines exact_closed unchanged_axioms\n%!" group !count;;
