needs "hol/private_boot.ml";;
needs "hol/instantiation_certificates.ml";;
let run_instantiation_cases () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let assertions=ref 0 in
  let test label ok=incr assertions;if not ok then failwith label in
  let get=function Ok x->x | Error e->failwith e.message in
  let failure f=try ignore(f());false with Failure _->true in
  List.iter(fun(label,proof,expected)->
    test (label^" exact theorem") (aconv(concl proof) expected);
    test (label^" closed theorem") (hyp proof=[] && frees(concl proof)=[])) [
    "pure",l4_defeq_instantiation,
      `!g a u e f t v. l4_defeq g a a (L4Sort u) /\
        l4_defeq (CONS a g) e f t /\ l4_defeq g v v a ==>
        l4_defeq g (l4_inst v e) (l4_inst v f) (l4_inst v t)`;
    "native",l4_edef_instantiation,
      `!env g a u e f t v. l4_edef env g a a (L4Sort u) /\
        l4_edef env (CONS a g) e f t /\ l4_edef env g v v a ==>
        l4_edef env g (l4_inst v e) (l4_inst v f) (l4_inst v t)`;
    "checked",l4_checked_instantiation,
      `!policy env g a u e f t v. l4_checked policy env g a a (L4Sort u) /\
        l4_checked policy env (CONS a g) e f t /\ l4_checked policy env g v v a ==>
        l4_checked policy env g (l4_inst v e) (l4_inst v f) (l4_inst v t)`];
  let a=Sort(Succ Zero) and z=Sort Zero and an=Anonymous in
  let cases=[
    "variable",[],a,Succ(Succ Zero),Bvar 0,Bvar 0,a,z,z,z,a;
    "beta",[],a,Succ(Succ Zero),App(Lam(an,a,Bvar 0),Bvar 0),Bvar 0,a,z,
      App(Lam(an,a,Bvar 0),z),z,a;
    "dependent_context",[Bvar 0;a],Bvar 1,Succ Zero,Bvar 0,Bvar 0,Bvar 2,Bvar 0,
      Bvar 0,Bvar 0,Bvar 1;
    "capture",[a],a,Succ(Succ Zero),Lam(an,Bvar 0,Bvar 0),Lam(an,Bvar 0,Bvar 0),
      Pi(an,Bvar 0,Bvar 1),Bvar 0,Lam(an,Bvar 0,Bvar 0),Lam(an,Bvar 0,Bvar 0),
      Pi(an,Bvar 0,Bvar 1);
    "universe",[],a,Succ(Succ Zero),z,Sort(Max(Zero,Zero)),a,z,
      z,Sort(Max(Zero,Zero)),a;
    "let",[],a,Succ(Succ Zero),Let(an,a,Bvar 0,Bvar 0),Bvar 0,a,z,
      Let(an,a,z,Bvar 0),z,a] in
  List.iter(fun(label,g,domain,u,e,f,t,v,expected_e,expected_f,expected_t)->
    let fields=[quote_context g;quote_expr domain;quote_level u;
      quote_expr e;quote_expr f;quote_expr t;quote_expr v] in
    let pure=[get(check g domain (Sort u));get(convert (domain::g) e f t);
      get(check g v domain)] in
    let concrete=SPECL fields l4_defeq_instantiation in
    let proof=CONV_RULE computation (MP concrete (end_itlist CONJ pure)) in
    test (label^" pure exact") (aconv(concl proof)
      (node "l4_defeq" [quote_context g;quote_expr expected_e;quote_expr expected_f;quote_expr expected_t]));
    test (label^" pure closed") (hyp proof=[] && frees(concl proof)=[]);
    let native=[get(Env.check Env.empty g domain (Sort u));
      get(Env.convert Env.empty (domain::g) e f t);get(Env.check Env.empty g v domain)] in
    let checked=SPECL (Env.quote_policy Env.empty::Env.quote_env Env.empty::fields)
      l4_checked_instantiation in
    let certified=CONV_RULE computation (MP checked (end_itlist CONJ native)) in
    test (label^" checked exact") (aconv(concl certified)
      (node "l4_checked" [Env.quote_policy Env.empty;Env.quote_env Env.empty;quote_context g;
       quote_expr expected_e;quote_expr expected_f;quote_expr expected_t]));
    test (label^" checked closed") (hyp certified=[] && frees(concl certified)=[]);
    let body=List.nth pure 1 and value=List.nth pure 2 in
    test (label^" wrong domain certificate")
      (failure(fun()->MP concrete (end_itlist CONJ [value;body;value])));
    test (label^" missing body certificate")
      (failure(fun()->MP concrete (CONJ (List.hd pure) value)));
    let wrong_fields=[quote_context g;quote_expr domain;quote_level u;
      quote_expr e;quote_expr f;quote_expr t;quote_expr(Sort(Succ(Succ Zero)))] in
    test (label^" changed substitution value") (failure(fun()->
      MP (SPECL wrong_fields l4_defeq_instantiation) (end_itlist CONJ pure)));
    let assumed=MP concrete (ASSUME(fst(dest_imp(concl concrete)))) in
    test (label^" conditional premises remain conditional") (hyp assumed<>[])
  ) cases;
  let declared_name=Str(Anonymous,"InstantiationWitness") in
  let decl={Env.kind=Env.Definition;name=declared_name;params=[];typ=a;value=Some z} in
  let env,_=get(Env.admit Env.empty decl) in
  let value=Const(declared_name,[]) in
  let fields=[quote_context [];quote_expr a;quote_level(Succ(Succ Zero));
    quote_expr(Bvar 0);quote_expr(Bvar 0);quote_expr a;quote_expr value] in
  let premises=[get(Env.check env [] a (Sort(Succ(Succ Zero))));
    get(Env.check env [a] (Bvar 0) a);get(Env.check env [] value a)] in
  let specialize target=SPECL (Env.quote_policy target::Env.quote_env target::fields)
    l4_checked_instantiation in
  let h=CONV_RULE computation (MP (specialize env) (end_itlist CONJ premises)) in
  test "nonempty environment exact" (aconv(concl h)
    (node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context [];
     quote_expr value;quote_expr value;quote_expr a]));
  test "nonempty environment closed" (hyp h=[] && frees(concl h)=[]);
  test "changed environment fails" (failure(fun()->MP (specialize Env.empty)
    (end_itlist CONJ premises)));
  let policy=get(Env.with_axioms [{Env.axiom_name=Str(Anonymous,"UnusedPermission");
    axiom_params=[];axiom_type=a}]) in
  let other,_=get(Env.admit policy decl) in
  test "policy control has identical declarations" (Env.declarations env=Env.declarations other);
  test "policy control changes policy" (not(aconv(Env.quote_policy env)(Env.quote_policy other)));
  test "changed policy fails" (failure(fun()->MP (specialize other)
    (end_itlist CONJ premises)));
  test "pure rule count unchanged" (List.length(CONJUNCTS l4_defeq_RULES)=13);
  test "native rule count unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission rule count unchanged" (private_admission_rule_count=11);
  test "no new HOL axioms" (axioms()=private_axioms);
  Printf.printf "PRIVATE_INSTANTIATION_CASES_DONE %d_assertions seven_cases unchanged_rules unchanged_axioms\n%!" !assertions;;
run_instantiation_cases ();;
exit 0;;
