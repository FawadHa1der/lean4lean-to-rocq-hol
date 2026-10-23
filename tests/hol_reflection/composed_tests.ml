(* Private composition tests. Fixtures use existing checked admission only. *)
let composed_initial_axioms = axioms();;
needs "hol/reflected_condition.ml";;
needs "tests/hol_reflection/reflection_boolean_fixtures.ml";;

module Lean4hol_composed_tests = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Fix=Lean4hol_reflection_fixture
  module Syn=Lean4hol_reflection_syntax
  module Ref=Lean4hol_reflection
  module Cond=Lean4hol_reflected_condition
  let get=Fix.get
  let count=ref 0
  let test label b = if not b then failwith label else
    (incr count; Printf.printf "COMPOSED_CHECK %d %s\n%!" !count label)
  let exact label target h =
    test (label^" closed/exact") (hyp h=[] && frees(concl h)=[] && aconv target (concl h))
  let decline label = function
    | Error {kind=Resource;message} -> failwith(label^": resource-only failure: "^message)
    | Error e -> Printf.printf "COMPOSED_NEGATIVE %s: %s\n%!" label e.message; test label true
    | Ok _ -> failwith(label^": unexpectedly certified")
  let env=Lean4hol_reflection_boolean_fixture.add(Fix.base())
  let env_quote=Env.quote_env env and policy_quote=Env.quote_policy env
  let ite_proofs=ref [] and dite_proofs=ref []
  let obligations id args =
    let j=node "l4_checked" [policy_quote;env_quote] in
    let v=genvar(type_of j) in
    let h=INST [j,v] (Syn.calc(node id (v::args))) in
    conjuncts(rhs(concl h))
  let ite_goals r=obligations "l4_reflection_ite_contract"
    (List.map quote_expr [r.Syn.typ;r.Syn.to_dec])
  let dite_goals r=obligations "l4_reflection_dite_contract"
    (List.map quote_expr [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec])
  let prepare dependent indices =
    let r=Syn.reflection false in
    let goals=if dependent then dite_goals r else ite_goals r in
    let output=if dependent then dite_proofs else ite_proofs in
    List.iter (fun i ->
      let target=List.nth goals i in
      let h=match List.find_opt (fun h -> aconv target (concl h)) (!ite_proofs @ !dite_proofs) with
        | Some h -> Printf.printf "COMPOSED_PROOF_REUSED %b %d\n%!" dependent i;h
        | None ->
          let head,xs=strip_comb target in
          match fst(dest_const head),xs with
          | "l4_checked",[policy;entries;g;e;e';a] when aconv policy policy_quote &&
              aconv entries env_quote && aconv g (quote_context []) ->
            let e=Syn.decode e and e'=Syn.decode e' and a=Syn.decode a in
            let fuel=if dependent && i=6 then 200000 else 100000 in
            Printf.printf "COMPOSED_PROOF_NATIVE_START %b %d fuel=%d\n%!" dependent i fuel;
            get "prepared actual checker obligation" (if e=e' then Env.check ~fuel env [] e a
              else Env.convert ~fuel env [] e e' a)
          | _ -> failwith "unexpected preparation judgment" in
      exact "prepared native proof" target h;
      output:=h::!output;
      Printf.printf "COMPOSED_PROOF_READY %b %d\n%!" dependent i) indices
  let check_invariants () =
    test "empty fixture policy" (Env.permissions env=[]);
    test "exact environment unchanged" (aconv env_quote (Env.quote_env env));
    test "exact policy unchanged" (aconv policy_quote (Env.quote_policy env));
    test "no axioms added since before module load" (axioms()=composed_initial_axioms);
    test "Bool base reuse theorem closed"
      (hyp l4_bool_condition_ite_implies_base=[] && frees(concl l4_bool_condition_ite_implies_base)=[]);
    test "native/admission rules unchanged"
      (List.length(CONJUNCTS l4_edef_RULES)=29 &&
       List.length(CONJUNCTS(SPEC policy_quote l4_evalid_RULES))=11)
  let cert label id args c =
    exact (label^" checked") (node id (node "l4_checked" [policy_quote;env_quote]::args))
      (Ref.theorem c);
    exact (label^" raw") (node id (node "l4_edef" [env_quote]::args)) (Ref.raw_theorem c)
  let bool_positive () =
    let p,d=Syn.bool_condition() in
    let c=get "full canonical Bool ITE" (Cond.check ~ite:true env (Cond.Boolean(p,d))) in
    let checked=Cond.theorems c and raw=Cond.raw_theorems c in
    test "one complete base plus ITE return" (List.length checked=2 && List.length raw=2);
    let _,xs=strip_comb(concl(List.nth checked 1)) in
    let dt=List.nth xs 3 in
    let args=[quote_expr p;quote_expr d;dt] in
    List.iteri (fun i id ->
      exact (id^" checked") (node id (node "l4_checked" [policy_quote;env_quote]::args))
        (List.nth checked i);
      exact (id^" raw") (node id (node "l4_edef" [env_quote]::args)) (List.nth raw i))
      ["l4_bool_condition_base_contract";"l4_bool_condition_ite_contract"];
    test "Bool certificate source bound" (not(aconv (concl(List.nth checked 1))
      (node "l4_bool_condition_ite_contract"
        [node "l4_checked" [policy_quote;env_quote];quote_expr d;quote_expr p;dt])));
    check_invariants()
  let one_ite () =
    let r=Syn.reflection false in
    test "four actual ITE proofs prepared" (List.length !ite_proofs=4);
    let c=get "full canonical defn1 ITE" (Ref.check_ite_using !ite_proofs env r) in
    cert "defn1 ITE" "l4_reflection_ite_contract" (List.map quote_expr [r.Syn.typ;r.Syn.to_dec]) c;
    test "certificate environment bound" (not(aconv (concl(Ref.theorem c))
      (node "l4_reflection_ite_contract" [node "l4_checked" [policy_quote;Env.quote_env Env.empty];
        quote_expr r.Syn.typ;quote_expr r.Syn.to_dec])));
    check_invariants()
  let one_dite () =
    let r=Syn.reflection false in
    test "seven actual DITE proofs prepared" (List.length !dite_proofs=7);
    let c=get "full canonical defn1 NatDITE" (Ref.check_nat_dite_using !dite_proofs env r) in
    cert "defn1 NatDITE" "l4_reflection_dite_contract"
      (List.map quote_expr [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec]) c;
    let other=get "negative policy fixture" (Env.with_axioms
      [{Env.axiom_name=Fix.name ["Unused"];axiom_params=[];axiom_type=Sort Zero}]) in
    test "certificate policy bound" (not(aconv (concl(Ref.theorem c))
      (node "l4_reflection_dite_contract" (node "l4_checked" [Env.quote_policy other;env_quote]::
        List.map quote_expr [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec]))));
    check_invariants()
  let proof_negatives () =
    let r=Syn.reflection false in
    let target=List.hd(ite_goals r) in
    decline "assumed obligation is not a closed proof" (Ref.check_ite_using [ASSUME target] env r);
    decline "unrelated proved theorem" (Ref.check_ite_using [TRUTH] env r);
    decline "proof source mismatch" (Ref.check_ite_using !ite_proofs env {r with Syn.to_dec=r.Syn.of_true});
    let p=List.hd !ite_proofs in
    decline "proof environment mismatch" (Ref.check_ite_using [p] Env.empty r);
    let other=get "different exact policy" (Env.with_axioms
      [{Env.axiom_name=Fix.name ["Unused"];axiom_params=[];axiom_type=Sort Zero}]) in
    decline "proof policy mismatch" (Ref.check_ite_using [p] other r);
    let g=List.hd(ite_goals r) in
    let left=rhs(concl(Syn.calc(node "l4_reflection_type_contract"
      [node "l4_checked" [policy_quote;env_quote];quote_expr r.Syn.typ]))) in
    test "source expected obligation agrees" (aconv g left);
    test "prepared proof zero fuel still Resource" (match Ref.check_ite_using ~fuel:0 !ite_proofs env r with
      Error {kind=Resource;_}->true|_->false);
    check_invariants()
  let negatives () =
    let r=Syn.reflection false in
    ignore(get "true helper independently typed" (Env.infer env [] r.Syn.of_true));
    ignore(get "false helper independently typed" (Env.infer env [] r.Syn.of_false));
    decline "typed poisoned true helper" (Ref.check_nat_dite env {r with Syn.of_true=r.Syn.of_false});
    decline "typed poisoned false helper" (Ref.check_nat_dite env {r with Syn.of_false=r.Syn.of_true});
    let p,d=Syn.bool_condition() in
    let open Fix.Quote in
    let bad=run(lam bb (fun _ -> con ["Nat";"zero"] [])) in
    ignore(get "wrong decision independently typed" (Env.infer env [] bad));
    decline "typed wrong Bool decision" (Cond.check ~ite:true env (Cond.Boolean(p,bad)));
    decline "typed wrong Bool proposition" (Cond.check ~ite:true env (Cond.Boolean(bad,d)));
    decline "unbound decision" (Ref.check_ite env {r with Syn.to_dec=Bvar 0});
    decline "missing dependencies" (Ref.check_type Env.empty r);
    test "zero fuel is Resource" (match Ref.check_ite ~fuel:0 env r with Error {kind=Resource;_}->true|_->false);
    test "Bool DITE stays explicitly unsupported" (match Cond.check ~dite:true env (Cond.Boolean(p,d)) with
      Error {kind=Unsupported;_}->true|_->false);
    check_invariants()
  let run phase =
    let before= !count in
    Printf.printf "\nCOMPOSED_WORK_START %s\n%!" phase;
    try
      (match phase with
       | "bool" -> bool_positive()
       | "one-ite" -> one_ite()
       | "one-dite" -> one_dite()
       | "ite-types" -> prepare false [0;1]
       | "ite-true-proof" -> prepare false [2]
       | "ite-false-proof" -> prepare false [3]
       | "dite-types" -> prepare true [0;1;2;3;4]
       | "dite-true-proof" -> prepare true [5]
       | "dite-false-proof" -> prepare true [6]
       | "proof-negatives" -> proof_negatives()
       | "negatives" -> negatives()
       | _ -> failwith "unknown composed phase");
      Printf.printf "\nCOMPOSED_WORK_PASS %s %d\n%!" phase (!count-before)
    with e -> Printf.printf "\nCOMPOSED_WORK_FAIL %s %s\n%!" phase (Printexc.to_string e)
end;;
Lean4hol_composed_tests.check_invariants();;
Printf.printf "\nCOMPOSED_SETUP_READY\n%!";;
