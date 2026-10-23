(* Focused repaired-main prepared API tests. All positive dependencies pass
   ordinary checked admission. No policy grant is used for a positive gate. *)
needs "hol/reflected_condition.ml";;
needs "tests/hol_reflection/reflection_boolean_fixtures.ml";;

module Lean4hol_prepared_bool_tests = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Fix=Lean4hol_reflection_fixture
  module Syn=Lean4hol_reflection_syntax
  module Cond=Lean4hol_reflected_condition
  let initial_axioms=axioms()
  let count=ref 0
  let test label value =
    if not value then failwith label;
    incr count;Printf.printf "UNIFIED_CHECK %d %s\n%!" !count label
  let get label = function Ok x -> x | Error e -> raise(Stop {e with message=label^": "^e.message})
  let error label kind = function
    | Error e -> test (label^" exact error kind") (e.kind=kind)
    | Ok _ -> failwith(label^": unexpectedly certified")
  let exact label a b = test label
    (hyp b=[] && frees(concl b)=[] && aconv (concl a) (concl b))
  let same label a b =
    let compare kind xs ys =
      test (label^kind^" count") (List.length xs=List.length ys);
      List.iter2 (exact (label^kind^" closed exact")) xs ys in
    compare " checked" (Cond.theorems a) (Cond.theorems b);
    compare " raw" (Cond.raw_theorems a) (Cond.raw_theorems b)
  let env=ref Env.empty
  let quotes=ref None
  let base=ref None and ite=ref None
  let demand = function Some x -> x | None -> failwith "missing completed preparation"
  let p,d=Syn.bool_condition()
  let condition=Cond.Boolean(p,d)
  let bh ()=List.hd(Cond.theorems(demand !base))
  let ih ()=List.nth(Cond.theorems(demand !ite)) 1
  let invariant () =
    let e,pol=demand !quotes in
    test "exact final environment" (aconv e (Env.quote_env !env));
    test "exact final empty policy" (aconv pol (Env.quote_policy !env) && Env.permissions !env=[]);
    test "unchanged HOL axioms" (axioms()=initial_axioms);
    test "exact 29 native / 11 admission" (List.length(CONJUNCTS l4_edef_RULES)=29 &&
      List.length(CONJUNCTS(SPEC pol l4_evalid_RULES))=11)
  let admit () =
    env:=Lean4hol_reflection_boolean_fixture.add(Fix.base());
    quotes:=Some(Env.quote_env !env,Env.quote_policy !env);
    test "13 genuine fixture admissions" (!(Fix.admissions)=13);
    invariant()
  let make_base () =
    base:=Some(get "canonical Bool base" (Cond.check !env condition));
    test "base checked/raw singleton" (List.length(Cond.theorems(demand !base))=1 &&
      List.length(Cond.raw_theorems(demand !base))=1)
  let make_ite () =
    ite:=Some(get "canonical Bool ITE" (Cond.check ~ite:true !env condition));
    let c=demand !ite in
    test "whole base+ITE checked/raw pair" (List.length(Cond.theorems c)=2 &&
      List.length(Cond.raw_theorems c)=2);
    exact "ITE base equals independently checked base" (bh()) (List.hd(Cond.theorems c));
    exact "ITE raw base equals independently checked base" (List.hd(Cond.raw_theorems(demand !base)))
      (List.hd(Cond.raw_theorems c))
  let default i d =
    let r=Cond.check ~ite:i ~dite:d !env condition in
    if d then error "default Bool DITE" Unsupported r else
      same "default bundle" (demand (if i then !ite else !base)) (get "default flag" r)
  let prepared_flags () =
    List.iter (fun (i,d) ->
      let r=Cond.check_prepared ~ite:i ~dite:d ~ite_proof:(ih()) !env condition (bh()) in
      if d then error "prepared Bool DITE" Unsupported r else
        same "prepared bundle" (demand(if i then !ite else !base)) (get "prepared flag" r))
      [false,false;true,false;false,true;true,true];
    same "prepared no optional ITE" (demand !base)
      (get "prepared base" (Cond.check_prepared !env condition (bh())));
    List.iter (fun flag ->
      error "Bool supplied DITE always unsupported" Unsupported
        (Cond.check_prepared ~dite:flag ~dite_proof:TRUTH !env condition (bh()))) [false;true]
  let typed_sources () =
    let open Fix.Quote in
    let wrong=run(lam bb (fun _ -> con ["Nat";"zero"] [])) in
    let _,h=get "typed altered source" (Env.infer !env [] wrong) in
    test "altered source genuinely typed" (hyp h=[] && frees(concl h)=[]);
    error "typed altered decision" Proof_failure
      (Cond.check_prepared !env (Cond.Boolean(p,wrong)) (bh()));
    error "typed altered proposition" Proof_failure
      (Cond.check_prepared !env (Cond.Boolean(wrong,d)) (bh()))
  let controls () =
    let consume ?ite_proof h=Cond.check_prepared ?ite_proof !env condition h in
    error "unrelated base theorem" Proof_failure (consume TRUTH);
    error "wrong base contract" Proof_failure (consume (ih()));
    error "raw is not checked base" Proof_failure (consume(List.hd(Cond.raw_theorems(demand !base))));
    error "hypothesis-bearing base" Proof_failure (consume(ASSUME(concl(bh()))));
    error "hypothesis-bearing optional" Proof_failure
      (consume ~ite_proof:(ASSUME(concl(ih()))) (bh()));
    error "wrong optional despite false flag" Proof_failure (consume ~ite_proof:TRUTH (bh()));
    error "wrong optional contract" Proof_failure (consume ~ite_proof:(bh()) (bh()));
    error "missing requested ITE" Proof_failure (Cond.check_prepared ~ite:true !env condition (bh()));
    error "missing dependency / stale environment" Proof_failure
      (Cond.check_prepared ~ite_proof:(ih()) Env.empty condition (bh()));
    let stale=Fix.def !env ["PreparedUnused"] [] (Sort(Succ Zero)) (Sort Zero) in
    error "later genuinely admitted environment" Proof_failure
      (Cond.check_prepared ~ite_proof:(ih()) stale condition (bh()));
    let other=get "negative-only policy environment" (Env.with_axioms
      [{Env.axiom_name=Fix.name ["UnusedPermission"];axiom_params=[];axiom_type=Sort Zero}]) in
    error "different policy environment" Proof_failure
      (Cond.check_prepared ~ite_proof:(ih()) other condition (bh()));
    let _,args=strip_comb(concl(bh())) in
    let altered=node "l4_bool_condition_base_contract"
      (node "l4_checked" [Env.quote_policy other;Env.quote_env !env]::List.tl args) in
    test "policy-only target bound with same entries" (not(aconv altered (concl(bh()))));
    error "unbound input" Proof_failure
      (Cond.check_prepared !env (Cond.Boolean(p,Bvar 0)) (bh()));
    error "malformed negative index" Invalid_input
      (Cond.check_prepared !env (Cond.Boolean(p,Bvar (-1))) (bh()));
    error "zero fuel" Resource (Cond.check_prepared ~fuel:0 ~ite:true ~ite_proof:(ih()) !env condition (bh()));
    invariant()
  let run phase =
    let before= !count in
    Printf.printf "\nUNIFIED_WORK_START %s\n%!" phase;
    try
      (match phase with
      | "admit" -> admit() | "base" -> make_base() | "ite" -> make_ite()
      | "default-0-0" -> default false false | "default-1-0" -> default true false
      | "default-0-1" -> default false true | "default-1-1" -> default true true
      | "prepared-flags" -> prepared_flags() | "typed-sources" -> typed_sources()
      | "controls" -> controls() | "invariants" -> invariant()
      | _ -> failwith "unknown focused phase");
      Printf.printf "\nUNIFIED_WORK_PASS %s %d\n%!" phase (!count-before)
    with e -> Printf.printf "\nUNIFIED_WORK_FAIL %s %s\n%!" phase (Printexc.to_string e)
end;;
Printf.printf "\nUNIFIED_SETUP_READY\n%!";;
