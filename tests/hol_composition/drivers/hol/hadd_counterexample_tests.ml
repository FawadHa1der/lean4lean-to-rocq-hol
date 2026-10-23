needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
needs "frontend/reducible_candidate.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let get=function Ok x->x | Error e->failwith e.H.message in
  let env=ref A.empty and raw=ref [] in
  List.iter(fun(_,d)->match d with
    | Hol_input.Definition(h,v) -> env:=fst(get(A.admit !env
        {A.kind=A.Definition;name=Hol_check.name h.Hol_input.name;
         params=List.map Hol_check.name h.Hol_input.params;typ=Hol_check.expr h.Hol_input.typ;
         value=Some(Hol_check.expr v)}))
    | Hol_input.Inductive cs -> raw:=List.map Hol_check.claim cs
    | _ -> failwith "unexpected prerequisite")
    (Hol_input.read_file "arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson");
  let b=get(Reducible_candidate.family !env !raw) in
  let next,_=get(A.admit_inductive_family !env b) in
  let beta=H.App(H.Lam(H.Anonymous,H.Sort(H.Succ H.Zero),H.Bvar 0),H.Bvar 0) in
  let bad_field=H.App(H.Const(b.A.family_name,[]),beta) in
  let changed=List.map(fun d->match d.A.kind,d.A.typ with
    | A.Generated(A.Constructor_role _),H.Pi(n,a,H.Pi(m,_,t)) ->
      {d with A.typ=H.Pi(n,a,H.Pi(m,bad_field,t))}
    | _ -> d) !raw in
  let th=get(Lean4hol_ctor_bridge.certify next changed b.A.family_claims) in
  if hyp th<>[] || not(aconv(concl th)
    (Lean4hol_ctor_bridge.expected next changed b.A.family_claims)) then
    failwith "counterexample certificate mismatch";
  if beta=H.Bvar 0 then failwith "nonuniform parameter collapsed";
  (match Reducible_candidate.family !env changed with
   | Error e when e.H.kind=H.Unsupported -> ()
   | _ -> failwith "head-only candidate failed to expose counterexample");
  (match Lean4hol_raw_ctor.certify !env next changed b with
   | Error e when e.H.kind=H.Proof_failure || e.H.kind=H.Unsupported -> ()
   | _ -> failwith "new raw admission accepted old bridge counterexample");
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_COUNTEREXAMPLE_DONE old_bridge_accepts new_admission_declines exact_closed unchanged_axioms";;
