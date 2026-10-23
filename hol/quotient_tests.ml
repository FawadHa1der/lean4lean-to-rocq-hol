(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_quotient_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Qmodel=Lean4hol_quotient_model in
  let count=ref 0 and before=axioms() in
  let test label ok = if not ok then failwith("quotient regression: "^label);
    incr count; print_endline("quotient check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let closed label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let admit label result =
    let env,h=get label result in
    closed label (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h; env in
  let nm s=Str(Anonymous,s) and one=Succ Zero in
  let child p s=Str(p,s) and app=Env.apps in
  let lam a b=Lam(Anonymous,a,b) in
  let u=nm "u" and v=nm "v" and eq=nm "Eq" and nat=nm "Nat" in
  let qt kind =
    let ps=if kind=Qmodel.Qlift then [u;v] else [u] in
    {Env.kind=Env.Quotient kind;name=Qmodel.name kind;params=ps;
      typ=Qmodel.signature {remaining=100000} kind (Param u) (Param v);value=None} in
  decline "missing equality prerequisite" (Env.admit_quotient Env.empty (qt Qmodel.Qtype));
  let eq_permission={Env.axiom_name=eq;axiom_params=[u];
    axiom_type=Qmodel.equality_type {remaining=100000} (Param u)} in
  let fakeeq=get "equality axiom policy" (Env.with_axioms [eq_permission]) in
  let fakeeq=admit "ordinary Eq-named axiom" (Env.admit fakeeq
    {Env.kind=Env.Axiom;name=eq;params=[u];typ=eq_permission.Env.axiom_type;value=None}) in
  decline "axiom cannot impersonate equality family"
    (Env.admit_quotient fakeeq (qt Qmodel.Qtype));
  let eb={Env.indexed_name=eq;indexed_level_params=[u];
    indexed_parameters=[nm "A",Sort(Param u);nm "a",Bvar 0];indices=[nm "b",Bvar 1];
    indexed_result_level=Zero;
    indexed_constructors=[{Env.indexed_ctor_name=child eq "refl";indexed_fields=[];result_indices=[Bvar 0]}];
    indexed_claims=[]} in
  let eb={eb with Env.indexed_claims=Env.generate_indexed {remaining=100000} eb ~large:true ~k:true} in
  let eqenv=admit "canonical Eq" (Env.admit_indexed_inductive Env.empty eb) in
  let bad_eq={eb with Env.indexed_constructors=[{Env.indexed_ctor_name=child eq "refl";
    indexed_fields=[Env.Index_data(Bvar 1)];result_indices=[Bvar 0]}];indexed_claims=[]} in
  let bad_eq={bad_eq with Env.indexed_claims=Env.generate_indexed {remaining=100000} bad_eq ~large:true ~k:false} in
  let bad_eq_env=admit "well-formed noncanonical Eq constructor"
    (Env.admit_indexed_inductive Env.empty bad_eq) in
  decline "noncanonical Eq cannot initialize quotient"
    (Env.admit_quotient bad_eq_env (qt Qmodel.Qtype));
  let renamed=nm "quotient_level" in
  ignore(admit "renamed quotient universe" (Env.admit_quotient eqenv
    {(qt Qmodel.Qtype) with Env.params=[renamed];
      typ=Qmodel.signature {remaining=100000} Qmodel.Qtype (Param renamed) Zero}));
  let named_type=match (qt Qmodel.Qtype).Env.typ with
    | Pi(_,a,b) -> Pi(nm "displayName",a,b) | _ -> failwith "quotient telescope absent" in
  ignore(admit "binder display name is irrelevant" (Env.admit_quotient eqenv
    {(qt Qmodel.Qtype) with Env.typ=named_type}));
  decline "missing quotient type dependency" (Env.admit_quotient eqenv (qt Qmodel.Qctor));
  let typeenv=admit "Quot type" (Env.admit_quotient eqenv (qt Qmodel.Qtype)) in
  decline "quotient kind cannot bypass specialized admission" (Env.admit eqenv (qt Qmodel.Qtype));
  decline "duplicate quotient name" (Env.admit_quotient typeenv (qt Qmodel.Qtype));
  decline "incorrect quotient name" (Env.admit_quotient eqenv {(qt Qmodel.Qtype) with Env.name=nm "Quot.fake"});
  decline "incorrect quotient signature" (Env.admit_quotient eqenv {(qt Qmodel.Qtype) with Env.typ=Sort Zero});
  decline "incorrect quotient universe count" (Env.admit_quotient eqenv {(qt Qmodel.Qtype) with Env.params=[u;v]});
  decline "quotient metadata kind mismatch" (Env.admit_quotient eqenv {(qt Qmodel.Qtype) with Env.kind=Env.Quotient Qmodel.Qctor});
  test "quotient body is malformed" (match Env.admit_quotient eqenv
    {(qt Qmodel.Qtype) with Env.value=Some(Sort Zero)} with
    | Error {kind=Invalid_input;_} -> true | _ -> false);
  test "zero fuel is a resource decline" (match Env.admit_quotient ~fuel:0 eqenv (qt Qmodel.Qtype) with
    | Error {kind=Resource;_} -> true | _ -> false);
  let env=admit "Quot constructor" (Env.admit_quotient typeenv (qt Qmodel.Qctor)) in
  let env=admit "Quot lift" (Env.admit_quotient env (qt Qmodel.Qlift)) in
  let env=admit "Quot induction" (Env.admit_quotient env (qt Qmodel.Qind)) in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000} nb} in
  let env=admit "Nat" (Env.admit_inductive env nb) in
  let nt=Const(nat,[]) and zero=Const(child nat "zero",[]) in
  let r=App(Const(eq,[one]),nt) in
  let eqt x y=app r [x;y] in
  let refl x=app (Const(child eq "refl",[one])) [nt;x] in
  let quotient=app (Const(Qmodel.name Qmodel.Qtype,[one])) [nt;r] in
  let mk x=app (Const(Qmodel.name Qmodel.Qctor,[one])) [nt;r;x] in
  let ident=lam nt (Bvar 0) in
  let sanity=lam nt (lam nt (lam (eqt (Bvar 1) (Bvar 0)) (Bvar 0))) in
  let lift major=app (Const(Qmodel.name Qmodel.Qlift,[one;one])) [nt;r;nt;ident;sanity;major] in
  let motive=lam quotient (eqt zero zero) and branch=lam nt (refl zero) in
  let ind major=app (Const(Qmodel.name Qmodel.Qind,[one])) [nt;r;motive;branch;major] in
  let normalize label g term expected =
    let result,typ,h=get label (Env.normalize env g term) in
    test (label^" expected normal form") (result=expected);
    closed label (node "l4_checked" [Env.quote_policy env;Env.quote_env env;
      quote_context g;quote_expr term;quote_expr result;quote_expr typ]) h in
  normalize "lift constructor iota" [] (lift(mk zero)) zero;
  normalize "induction constructor iota" [] (ind(mk zero)) (refl zero);
  normalize "lift beta major" [] (lift(App(lam quotient (Bvar 0),mk zero))) zero;
  normalize "induction zeta major" []
    (ind(Let(Anonymous,quotient,mk zero,Bvar 0))) (refl zero);
  normalize "neutral quotient lift is stuck" [quotient] (lift(Bvar 0)) (lift(Bvar 0));
  normalize "neutral quotient induction is stuck" [quotient] (ind(Bvar 0)) (ind(Bvar 0));
  let arrow=Pi(Anonymous,nt,nt) in
  let function_refl=app (Const(child eq "refl",[one])) [arrow;ident] in
  let function_sanity=lam nt (lam nt (lam (eqt (Bvar 1) (Bvar 0)) function_refl)) in
  let lifted_function=app (Const(Qmodel.name Qmodel.Qlift,[one;one]))
    [nt;r;arrow;lam nt ident;function_sanity;mk zero] in
  normalize "extra lift argument" [] (App(lifted_function,zero)) zero;
  let proof_function=Pi(Anonymous,nt,eqt zero zero) in
  let inducted_function=app (Const(Qmodel.name Qmodel.Qind,[one]))
    [nt;r;lam quotient proof_function;lam nt (lam nt (refl zero));mk zero] in
  normalize "extra induction argument" [] (App(inducted_function,zero)) (refl zero);
  decline "ill-typed major cannot reduce" (Env.normalize env [] (lift zero));
  decline "missing quotient universe argument" (Env.infer env [] (Const(Qmodel.base,[])));
  let ctor=qt Qmodel.Qctor in
  let fake_ctor_policy=get "quotient constructor axiom policy" (Env.with_axioms
    [{Env.axiom_name=ctor.Env.name;axiom_params=ctor.Env.params;axiom_type=ctor.Env.typ}]) in
  let fake=admit "fake-constructor Eq gate" (Env.admit_indexed_inductive fake_ctor_policy eb) in
  let fake=admit "fake-constructor Quot gate" (Env.admit_quotient fake (qt Qmodel.Qtype)) in
  let fake=admit "ordinary Quot.mk-named axiom" (Env.admit fake {ctor with Env.kind=Env.Axiom}) in
  let fake=admit "fake-constructor lift gate" (Env.admit_quotient fake (qt Qmodel.Qlift)) in
  let fake=admit "fake-constructor Nat gate" (Env.admit_inductive fake nb) in
  let term=lift(mk zero) in
  let result,typ,h=get "fake constructor does not reduce" (Env.normalize fake [] term) in
  test "name-only constructor never triggers iota" (result=term);
  closed "fake constructor neutral certificate"
    (node "l4_checked" [Env.quote_policy fake;Env.quote_env fake;quote_context [];
      quote_expr term;quote_expr result;quote_expr typ]) h;
  decline "fake constructor cannot prove lift equation" (Env.convert fake [] term zero nt);
  decline "fake constructor cannot satisfy induction prerequisite"
    (Env.admit_quotient fake (qt Qmodel.Qind));
  test "no new HOL axioms" (axioms()=before);
  print_endline("HOL_QUOTIENT_TESTS_PASSED "^string_of_int !count);;

l4_quotient_tests ();;
