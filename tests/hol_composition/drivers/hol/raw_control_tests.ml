needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let module R=Lean4hol_raw_ctor in
  let get=function Ok x->x | Error e->failwith e.H.message in
  let prior=ref A.empty and raw=ref [] in
  List.iter(fun(_,d)->match d with
    | Hol_input.Definition(h,v) -> prior:=fst(get(A.admit !prior
        {A.kind=A.Definition;name=Hol_check.name h.Hol_input.name;
         params=List.map Hol_check.name h.Hol_input.params;typ=Hol_check.expr h.Hol_input.typ;
         value=Some(Hol_check.expr v)}))
    | Hol_input.Inductive cs -> raw:=List.map Hol_check.claim cs
    | _ -> failwith "unexpected prerequisite")
    (Hol_input.read_file "arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson");
  let prior= !prior and raw= !raw in
  let b=get(Reducible_candidate.family prior raw) in
  let next,_=get(A.admit_inductive_family prior b) in
  let positive=get(R.certify prior next raw b) in
  ignore(R.exact(R.expected prior next raw b.A.family_claims)positive);
  print_endline "CONTROL positive_gate exact_closed_raw055";
  let count=ref 0 in
  let decline label candidate =
    match R.certify prior next candidate b with
    | Error e when e.H.kind<>H.Invalid_input ->
      incr count; print_endline("CONTROL decline "^label^" : "^e.H.message)
    | Error _ -> failwith(label^" malformed control")
    | Ok _ -> failwith(label^" accepted") in
  let ctor f=List.map(fun d->match d.A.kind with
    | A.Generated(A.Constructor_role _)->f d | _->d)raw in
  let domain e=ctor(fun d->match d.A.typ with
    | H.Pi(n,a,H.Pi(m,_,t))->{d with A.typ=H.Pi(n,a,H.Pi(m,e,t))}
    | _->failwith "unexpected constructor shape") in
  let beta=H.App(H.Lam(H.Anonymous,H.Sort(H.Succ H.Zero),H.Bvar 0),H.Bvar 0) in
  let nonuniform=H.App(H.Const(b.A.family_name,[]),beta) in
  let normal,proof=get(H.run 100000 [] [] (fun st->R.head st
    (List.hd raw::A.declarations prior) nonuniform)) in
  if normal<>nonuniform || hyp proof<>[] then failwith "argument was normalized";
  decline "nonuniform_beta_argument_old_bridge_counterexample" (domain nonuniform);
  decline "negative_recursive_domain" (domain
    (H.Pi(H.Anonymous,H.App(H.Const(b.A.family_name,[]),H.Bvar 0),H.Bvar 1)));
  decline "higher_order_direct_slice" (domain
    (H.Pi(H.Anonymous,H.Bvar 0,H.App(H.Const(b.A.family_name,[]),H.Bvar 1))));
  decline "free_field_variable" (domain(H.Bvar 9));
  decline "undeclared_field_universe" (domain(H.Sort(H.Param(H.Str(H.Anonymous,"undeclared")))));
  decline "field_universe_too_large" (domain(H.Sort(H.Succ H.Zero)));
  let ctor_name=match b.A.family_constructors with (n,_)::_->n | _->failwith "no ctor" in
  decline "constructor_forward_reference" (domain(H.Const(ctor_name,[])));
  decline "wrong_result_parameter" (ctor(fun d->match d.A.typ with
    | H.Pi(n,a,H.Pi(m,x,_))->{d with A.typ=H.Pi(n,a,H.Pi(m,x,
        H.App(H.Const(b.A.family_name,[]),H.Bvar 0)))}
    | _->failwith "constructor shape"));
  decline "wrong_parameter_domain" (ctor(fun d->match d.A.typ with
    | H.Pi(n,_,body)->{d with A.typ=H.Pi(n,H.Sort H.Zero,body)} | _->d));
  decline "wrong_constructor_metadata" (ctor(fun d->match d.A.kind with
    | A.Generated(A.Constructor_role r)->{d with A.kind=A.Generated(A.Constructor_role
        {r with A.num_fields=r.A.num_fields+1})} | _->d));
  decline "missing_recursor" (List.filter(fun d->match d.A.kind with
    | A.Generated(A.Recursor_role _)->false | _->true)raw);
  decline "duplicate_header_name" (ctor(fun d->{d with A.name=b.A.family_name}));
  decline "unformed_raw_header" (List.mapi(fun j d->if j=0 then
    {d with A.typ=H.Pi(H.Anonymous,H.Const(b.A.family_name,[]),H.Sort(H.Succ H.Zero))} else d)raw);
  decline "ill_typed_rhs_annotation" (List.map(fun d->match d.A.kind with
    | A.Generated(A.Recursor_role r)->
      let rules=List.map(fun rr->match rr.A.rhs with
        | H.Lam(n,_,body)->{rr with A.rhs=H.Lam(n,H.Sort H.Zero,body)}
        | _->failwith "RHS lambda")r.A.rules in
      {d with A.kind=A.Generated(A.Recursor_role {r with A.rules=rules})}
    | _->d)raw);
  decline "wrong_rhs_computation" (List.map(fun d->match d.A.kind with
    | A.Generated(A.Recursor_role r)->
      {d with A.kind=A.Generated(A.Recursor_role {r with A.rules=List.map
        (fun rr->{rr with A.rhs=H.Sort H.Zero})r.A.rules})}
    | _->d)raw);
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline(Printf.sprintf "PRIVATE_RAW_CONTROLS_DONE positive_gate %d_declines unchanged_axioms" !count);;
