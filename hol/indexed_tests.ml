(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_indexed_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 and before=axioms() in
  let test label ok = if not ok then failwith("indexed regression: "^label);
    incr count; print_endline("indexed check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} | Error {kind=Resource;_} -> test label true
    | Error _ -> failwith(label^": malformed-input classification")
    | Ok _ -> failwith("accepted: "^label) in
  let nm s=Str(Anonymous,s) and n=Anonymous in
  let child i s=Str(i,s) in
  let one=Succ Zero in
  let pi a b=Pi(n,a,b) and lam a b=Lam(n,a,b) and app=Env.apps in
  let names ns=mk_list(List.map quote_name ns,`:l4_name`) in
  let levels us=mk_list(List.map quote_level us,`:l4_level`) in
  let pars ps=mk_list(List.map (fun (n,a) -> mk_pair(quote_name n,quote_expr a)) ps,`:l4_name#l4_expr`) in
  let entries ds=mk_list(List.map Env.quote_decl ds,`:l4_entry`) in
  let specs cs=mk_list(List.map (fun c -> node "L4IndexCtor" [quote_name c.Env.indexed_ctor_name;
    mk_list(List.map (function Env.Index_data a -> node "L4IndexData" [quote_expr a]
      | Env.Index_recursive xs -> node "L4IndexRecursive" [quote_context xs]
      | Env.Index_function(ds,xs) -> node "L4IndexFunction" [quote_context ds;quote_context xs]) c.Env.indexed_fields,`:l4_index_field`);
    quote_context c.Env.result_indices]) cs,`:l4_index_ctor`) in
  let bool b=if b then `T` else `F` in
  let closed label tm h=test (label^" closed") (hyp h=[]);test (label^" exact") (aconv(concl h) tm) in
  let ctor name fields result={Env.indexed_ctor_name=name;indexed_fields=fields;result_indices=result} in
  let candidate i ps parameters indices u cs large k =
    let b={Env.indexed_name=i;indexed_level_params=ps;indexed_parameters=parameters;indices;
      indexed_result_level=u;indexed_constructors=cs;indexed_claims=[]} in
    {b with Env.indexed_claims=Env.generate_indexed {remaining=100000} b ~large ~k} in
  let admit label env b vss large k =
    let after,h=get label (Env.admit_indexed_inductive env b) in
    closed (label^" admission") (node "l4_evalid" [Env.quote_policy after;Env.quote_env after]) h;
    let args=[Env.quote_policy env;Env.quote_env env;quote_name b.Env.indexed_name;names b.Env.indexed_level_params;
      pars b.Env.indexed_parameters;pars b.Env.indices;quote_level b.Env.indexed_result_level;
      specs b.Env.indexed_constructors;mk_list(List.map levels vss,`:l4_level list`);
      bool large;bool k;entries b.Env.indexed_claims] in
    let detail=get label (Env.inductive_certificate after b.Env.indexed_name) in
    closed (label^" detail") (node "l4_index_checked" args) detail;
    closed (label^" metadata") (node "l4_metadata_matches" [entries b.Env.indexed_claims;
      node "l4_index_generated" [quote_name b.Env.indexed_name;names b.Env.indexed_level_params;
        pars b.Env.indexed_parameters;pars b.Env.indices;quote_level b.Env.indexed_result_level;
        specs b.Env.indexed_constructors;bool large;bool k]])
      (MATCH_MP (SPECL args l4_index_checked_metadata) detail);
    closed (label^" elimination") (mk_conj(mk_eq(bool large,node "l4_index_large"
      [quote_level b.Env.indexed_result_level;specs b.Env.indexed_constructors;mk_list(List.map levels vss,`:l4_level list`)]),
      mk_eq(bool k,node "l4_index_k" [quote_level b.Env.indexed_result_level;specs b.Env.indexed_constructors])))
      (MATCH_MP (SPECL args l4_index_checked_elimination) detail);
    after in
  let stmt env g a b ty=node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
    quote_expr a;quote_expr b;quote_expr ty] in
  let check label env g a ty=closed label (stmt env g a a ty) (get label (Env.check env g a ty)) in
  let equal label env g a b ty=closed label (stmt env g a b ty) (get label (Env.convert env g a b ty)) in
  let nat=nm "Nat" in let nt=Const(nat,[]) in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000} nb} in
  let env,_=get "Nat base" (Env.admit_inductive Env.empty nb) in
  let eq=nm "Eq" and u=nm "u" and a=nm "A" in
  let rfl=child eq "refl" in
  let eqt us x y z=app (Const(eq,us)) [x;y;z] in
  let eb=candidate eq [u] [a,Sort(Param u);nm "a",Bvar 0] [nm "b",Bvar 1] Zero
    [ctor rfl [] [Bvar 0]] true true in
  test "independent Eq constructor type" ((List.nth eb.Env.indexed_claims 1).Env.typ=
    pi (Sort(Param u)) (pi (Bvar 0) (eqt [Param u] (Bvar 1) (Bvar 0) (Bvar 0))));
  let motive=pi (Bvar 1) (pi (eqt [Param u] (Bvar 2) (Bvar 1) (Bvar 0)) (Sort(Param(nm "u_1")))) in
  let minor=app (Bvar 0) [Bvar 1;app (Const(rfl,[Param u])) [Bvar 2;Bvar 1]] in
  let expected=pi (Sort(Param u)) (pi (Bvar 0) (pi motive (pi minor
    (pi (Bvar 3) (pi (eqt [Param u] (Bvar 4) (Bvar 3) (Bvar 0))
      (app (Bvar 3) [Bvar 1;Bvar 0])))))) in
  test "independent Eq recursor type" ((List.nth eb.Env.indexed_claims 2).Env.typ=expected);
  let env=admit "polymorphic Eq" env eb [[]] true true in
  let refl=app (Const(rfl,[one])) [nt;Natlit "0"] in
  check "Eq refl" env [] refl (eqt [one] nt (Natlit "0") (Natlit "0"));
  let mot=lam nt (lam (eqt [one] nt (Natlit "0") (Bvar 0)) nt) in
  let reduce major=app (Const(child eq "rec",[one;one])) [nt;Natlit "0";mot;Natlit "2";Natlit "0";major] in
  equal "Eq constructor iota" env [] (reduce refl) (Natlit "2") nt;
  equal "neutral Eq K reduction" env [eqt [one] nt (Natlit "0") (Natlit "0")]
    (reduce(Bvar 0)) (Natlit "2") nt;
  let mismatched=app (Const(child eq "rec",[one;one]))
    [nt;Natlit "0";mot;Natlit "2";Natlit "1";Bvar 0] in
  test "neutral K cannot change Eq indices" (match Env.convert env
    [eqt [one] nt (Natlit "0") (Natlit "1")] mismatched (Natlit "2") nt with
    Error {kind=Proof_failure;_} -> true | _ -> false);
  test "neutral K resource classification" (match Env.convert ~fuel:0 env
    [eqt [one] nt (Natlit "0") (Natlit "0")] (reduce(Bvar 0)) (Natlit "2") nt with
    Error {kind=Resource;_} -> true | _ -> false);
  let p=nm "KProofProp" and intro=nm "KProofIntro" in
  let pb={Env.family_name=p;level_params=[];parameters=[];result_level=Zero;
    family_constructors=[intro,[]];family_claims=[]} in
  let pb={pb with Env.family_claims=Env.generate_family {remaining=100000} pb ~large:true ~k:true} in
  let proofenv,_=get "Prop for Eq universe-zero K" (Env.admit_inductive_family env pb) in
  let pt=Const(p,[]) and proofintro=Const(intro,[]) in
  let eqp x=eqt [Zero] pt proofintro x in
  let proofmot=lam pt (lam (eqp(Bvar 0)) nt) in
  let proofrec=app (Const(child eq "rec",[one;Zero]))
    [pt;proofintro;proofmot;Natlit "3";proofintro;Bvar 0] in
  equal "neutral Eq K instantiates constructor universes" proofenv [eqp proofintro] proofrec (Natlit "3") nt;
  let sigma=nm "DependentPair" in
  let sb=candidate sigma [u] [a,Sort(Succ(Param u));nm "B",pi (Bvar 0) (Sort(Succ(Param u)))] [] (Succ(Param u))
    [ctor (child sigma "mk") [Env.Index_data(Bvar 1);Env.Index_data(App(Bvar 1,Bvar 0))] []] true false in
  let env=admit "dependent constructor fields" env sb [[Succ(Param u);Succ(Param u)]] true false in
  let family=lam nt nt in
  let st=app (Const(sigma,[Zero])) [nt;family] in
  let pair=app (Const(child sigma "mk",[Zero])) [nt;family;Natlit "2";Natlit "3"] in
  check "dependent pair constructor" env [] pair st;
  equal "dependent pair iota" env []
    (app (Const(child sigma "rec",[one;Zero])) [nt;family;lam st nt;lam nt (lam nt (Bvar 0));pair]) (Natlit "3") nt;
  let witness=nm "IndexedWitness" in
  let wb=candidate witness [u] [a,Sort(Param u)] [nm "x",Bvar 0] Zero
    [ctor (child witness "mk") [Env.Index_data(Bvar 0)] [Bvar 0]] true false in
  let env=admit "large elimination field retained as index" env wb [[Param u]] true false in
  let wm=App(Const(child witness "mk",[one]),nt) in
  let wt x=app (Const(witness,[one])) [nt;x] in
  equal "indexed data field iota" env []
    (app (Const(child witness "rec",[one;one])) [nt;lam nt (lam (wt(Bvar 0)) nt);
      lam nt (Bvar 0);Natlit "3";App(wm,Natlit "3")]) (Natlit "3") nt;
  let seq=nm "IndexedSeq" in
  let nil=child seq "nil" and step=child seq "step" in
  let suc x=App(Const(child nat "succ",[]),x) in
  let qb=candidate seq [] [] [nm "n",nt] one
    [ctor nil [] [Natlit "0"];
     ctor step [Env.Index_data nt;Env.Index_recursive [Bvar 0]] [suc(Bvar 1)]] true false in
  let env=admit "indexed direct recursion" env qb [[];[one;one]] true false in
  let qt x=App(Const(seq,[]),x) in
  let qnil=Const(nil,[]) in
  let qone=app (Const(step,[])) [Natlit "0";qnil] in
  let qmot=lam nt (lam (qt(Bvar 0)) nt) in
  let qstep=lam nt (lam (qt(Bvar 0)) (lam nt (suc(Bvar 0)))) in
  equal "indexed recursive iota" env []
    (app (Const(child seq "rec",[one])) [qmot;Natlit "0";qstep;Natlit "1";qone]) (Natlit "1") nt;
  let dependent=nm "DependentIndices" in
  let db=candidate dependent [] [] [a,Sort one;nm "x",Bvar 0] Zero
    [ctor (child dependent "mk") [Env.Index_data(Sort one);Env.Index_data(Bvar 0)] [Bvar 1;Bvar 0]] true false in
  let env=admit "dependent index telescope" env db [[Succ one;one]] true false in
  check "dependent indexed constructor" env []
    (app (Const(child dependent "mk",[])) [nt;Natlit "2"])
    (app (Const(dependent,[])) [nt;Natlit "2"]);
  ignore(admit "permuted indexed claims" Env.empty {eb with Env.indexed_claims=List.rev eb.Env.indexed_claims} [[]] true true);
  let bad_return={eb with Env.indexed_constructors=[ctor rfl [] [Bvar 1]]} in
  decline "ill-typed constructor return index" (Env.admit_indexed_inductive Env.empty
    {bad_return with Env.indexed_claims=Env.generate_indexed {remaining=100000} bad_return ~large:true ~k:true});
  let bad_arity={eb with Env.indexed_constructors=[ctor rfl [] []]} in
  decline "constructor index arity" (Env.admit_indexed_inductive Env.empty bad_arity);
  let hidden=candidate (nm "HiddenData") [u] [a,Sort(Param u);nm "a",Bvar 0] [nm "b",Bvar 1] Zero
    [ctor (nm "HiddenDataMk") [Env.Index_data(Bvar 1)] [Bvar 1]] true false in
  decline "large elimination cannot erase non-Prop field" (Env.admit_indexed_inductive Env.empty hidden);
  let self=nm "NegativeIndexed" in
  decline "negative indexed recursion" (Env.admit_indexed_inductive Env.empty
    (candidate self [] [] [] one
      [ctor (nm "NegativeMk") [Env.Index_data(pi (Const(self,[])) (Const(self,[])))] []] true false));
  let forward=nm "ForwardIndexed" in
  decline "constructor forward reference" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [] one [ctor (nm "ForwardMk") [Env.Index_data(Const(nm "LaterMk",[]))] [];
      ctor (nm "LaterMk") [] []] true false));
  decline "recursor forward reference" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [] one [ctor (nm "ForwardMk") [Env.Index_data(Const(child forward "rec",[]))] []] true false));
  decline "header forward reference" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [n,Const(forward,[])] one [] true false));
  decline "field forward bound variable" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [] one [ctor (nm "ForwardMk") [Env.Index_data(Bvar 0)] []] true false));
  decline "recursive index contains family" (Env.admit_indexed_inductive env
    (candidate forward [] [] [n,Sort one] one
      [ctor (nm "ForwardMk") [Env.Index_recursive [App(Const(forward,[]),nt)]] [nt]] true false));
  decline "result index contains family" (Env.admit_indexed_inductive env
    (candidate forward [] [] [n,Sort one] one [ctor (nm "ForwardMk") [] [App(Const(forward,[]),nt)]] true false));
  decline "indexed field universe bound" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [] one [ctor (nm "ForwardMk") [Env.Index_data(Sort one)] []] true false));
  decline "undeclared indexed universe" (Env.admit_indexed_inductive Env.empty
    (candidate forward [] [] [n,Sort(Param u)] one [] true false));
  let bad_metadata=List.map (fun d -> match d.Env.kind with
    | Env.Generated(Env.Recursor_role r) -> {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.num_indices=0})}
    | _ -> d) eb.Env.indexed_claims in
  decline "recursor index-count metadata" (Env.admit_indexed_inductive Env.empty
    {eb with Env.indexed_claims=bad_metadata});
  let bad_rule=List.map (fun d -> match d.Env.kind with
    | Env.Generated(Env.Recursor_role r) -> {d with Env.kind=Env.Generated(Env.Recursor_role
        {r with Env.rules=List.map (fun rule -> {rule with Env.rhs=Sort Zero}) r.Env.rules})}
    | _ -> d) eb.Env.indexed_claims in
  decline "indexed recursor RHS authentication" (Env.admit_indexed_inductive Env.empty
    {eb with Env.indexed_claims=bad_rule});
  let permissions=MATCH_MP (SPECL [Env.quote_policy env;Env.quote_env env] l4_evalid_permissions)
    (Env.certificate env) in
  test "indexed permission invariant" (hyp permissions=[]);
  let unique=MATCH_MP (SPECL [Env.quote_policy env;Env.quote_env env] l4_evalid_unique)
    (Env.certificate env) in
  test "indexed uniqueness invariant" (hyp unique=[]);
  let qe=entries(List.init 128 (fun _ -> List.nth eb.Env.indexed_claims 2)) in
  let rule=List.hd(CONJUNCTS l4_edef_RULES) in
  let args=[quote_context [Sort Zero];`0`] in
  let timed f = let start=Sys.time() in let result=ref TRUTH in
    for j=1 to 5 do result:=f() done; !result,Sys.time()-.start in
  let old,old_time=timed(fun () -> CONV_RULE computation (SPECL (qe::args) rule)) in
  let newer,new_time=timed(fun () -> let ev=genvar(type_of qe) in
    INST [qe,ev] (CONV_RULE computation (SPECL (ev::args) rule))) in
  test "symbolic environment specialization exact" (aconv(concl old)(concl newer));
  test "symbolic environment specialization closed" (hyp old=[] && hyp newer=[]);
  Printf.printf "HOL_RULE_SPECIALIZATION_BENCH old=%.6fs symbolic=%.6fs runs=5 entries=128\n%!" old_time new_time;
  decline "indexed protected primitive" (Env.admit_indexed_inductive Env.empty
    (candidate nat [] [] [n,Sort Zero] one [] true false));
  let duplicate={eb with Env.indexed_claims=List.hd eb.Env.indexed_claims::List.tl(List.rev eb.Env.indexed_claims)} in
  decline "duplicate indexed claims" (Env.admit_indexed_inductive Env.empty duplicate);
  test "indexed resource classification" (match Env.admit_indexed_inductive ~fuel:0 env eb with
    Error {kind=Resource;_} -> true | _ -> false);
  test "no new HOL axioms" (axioms()=before);
  print_endline("HOL_INDEXED_TESTS_PASSED "^string_of_int !count);;

l4_indexed_tests ();;
