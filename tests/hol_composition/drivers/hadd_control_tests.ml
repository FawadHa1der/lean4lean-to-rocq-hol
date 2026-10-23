needs "hol/private_boot.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
needs "hadd_common.ml";;
let () =
  let module T=Hadd_test in
  let module H=T.H in
  let module A=T.A in
  let prior,_,_,cs,raw=T.setup() in
  let b,next=T.canonical prior cs in
  let ctor=T.ctor raw in
  let group=Sys.getenv "COMPOSE_GROUP" in
  let reject label changed=T.raw_reject label prior next changed b in
  let change_field f=T.map_ctor(fun d->{d with A.typ=T.nth_domain 3 f d.A.typ})raw in
  (match group with
  | "domain" ->
    let changed=change_field(function H.Pi(n,H.Bvar 2,H.Pi(m,H.Bvar 2,c))->
      H.Pi(n,H.Bvar 1,H.Pi(m,H.Bvar 3,c)) | _->failwith "unexpected field") in
    T.typed_ctors "altered_field_domain" prior changed;
    reject "altered_domain_fixed_anchor" changed;
    let proposed=T.get(Reducible_candidate.family prior changed) in
    let changed_env=fst(T.get(A.admit_inductive_family prior proposed)) in
    T.raw_reject "altered_domain_original_recursor" prior changed_env changed proposed
  | "universes" ->
    let levels=List.map(fun p->H.Param p)b.A.level_params in
    let swapped=match levels with [u;v;w]->[v;u;w]|_->failwith "expected u v w" in
    let changed=T.map_ctor(fun d->{d with A.typ=T.result(fun _->
      List.fold_left(fun f x->H.App(f,x))(H.Const(b.A.family_name,swapped))
        [H.Bvar 2;H.Bvar 3;H.Bvar 1])d.A.typ})raw in
    T.typed_ctors "swapped_result_universes_and_parameters" prior changed;
    reject "exact_result_universes" changed;
    T.decline "candidate_uniform_result" (Reducible_candidate.family prior changed);
    let low={b with A.result_level=H.Succ H.Zero} in
    let claims=T.get(H.run 100000 [] [] (fun st->A.generate_family st low ~large:true ~k:false)) in
    T.decline "polymorphic_field_universe_bound"
      (A.admit_inductive_family prior {low with A.family_claims=claims})
  | "metadata" ->
    T.typed_ctors "original_types_before_metadata_tamper" prior raw;
    let changed=T.map_ctor(fun d->{d with A.kind=match d.A.kind with
      | A.Generated(A.Constructor_role c)->A.Generated(A.Constructor_role {c with A.num_fields=c.A.num_fields+1})
      | _->failwith "not ctor"})raw in
    reject "wrong_field_count" changed;
    let changed=List.map(fun d->match d.A.kind with
      | A.Generated(A.Recursor_role _)->{d with A.params=List.rev d.A.params}
      | _->d)raw in
    reject "recursor_universe_parameter_order" changed
  | "rhs" ->
    let changed=List.map(fun d->match d.A.kind with
      | A.Generated(A.Recursor_role r)->
        let rules=List.map(fun rr->
          let ty,_=T.get(A.infer next [] rr.A.rhs) in
          let rhs=H.App(H.Lam(H.Anonymous,ty,H.Bvar 0),rr.A.rhs) in
          let _,th=T.get(A.infer next [] rhs) in T.closed th;
          T.closed(T.get(A.convert next [] rhs rr.A.rhs ty));
          Printf.printf "PRIVATE_TYPED rhs_beta_wrapper closed_inference_and_conversion\n%!";
          {rr with A.rhs})r.A.rules in
        {d with A.kind=A.Generated(A.Recursor_role {r with A.rules})}
      | _->d)raw in
    reject "typed_computational_rhs_shape" changed
  | "erased" ->
    let run label wrap =
      let changed=change_field wrap in
      let proposed=T.get(Reducible_candidate.family prior changed) in
      if proposed<>b then failwith "erasure changed canonical candidate";
      T.decline (label ^ "_formation")
        (A.fragment_sort (List.hd raw::A.declarations prior) [] (T.ctor changed).A.typ);
      reject label changed in
    run "illtyped_erased_beta" (fun field->
      H.App(H.Lam(H.Anonymous,H.Sort H.Zero,T.lift field 1),H.Sort H.Zero));
    run "illtyped_erased_let" (fun field->H.Let(H.Anonymous,H.Sort H.Zero,field,H.Bvar 0))
  | "forward" ->
    let changed=change_field(fun field->
      H.App(H.Lam(H.Anonymous,ctor.A.typ,T.lift field 1),
        H.Const(ctor.A.name,List.map(fun p->H.Param p)ctor.A.params))) in
    T.typed "forward_constructor_in_final_environment" (A.declarations next) (T.ctor changed).A.typ;
    let proposed=T.get(Reducible_candidate.family prior changed) in
    if proposed<>b then failwith "head erasure changed canonical candidate";
    T.decline "forward_header_only_formation"
      (A.fragment_sort (List.hd raw::A.declarations prior) [] (T.ctor changed).A.typ);
    T.decline "forward_bridge_guard" (Lean4hol_ctor_bridge.certify next changed b.A.family_claims);
    reject "forward_raw_admission" changed
  | _->failwith "unknown control group");
  T.native();
  Printf.printf "PRIVATE_CONTROL_DONE %s no_resource_negatives unchanged_axioms\n%!" group;;
