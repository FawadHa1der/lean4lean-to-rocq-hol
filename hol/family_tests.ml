(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_family_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let count=ref 0 in
  let test label ok = if not ok then failwith("family regression: "^label);
    incr count; print_endline("family check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} | Error {kind=Resource;_} -> test label true
    | Error _ -> failwith(label^": malformed-input classification")
    | Ok _ -> failwith("accepted: "^label) in
  let nm s=Str(Anonymous,s) and n=Anonymous in
  let child i s=Str(i,s) in
  let level=Succ Zero in
  let pi a b=Pi(n,a,b) and lam a b=Lam(n,a,b) in
  let app=Env.apps in
  let names ns=mk_list(List.map quote_name ns,`:l4_name`) in
  let levels us=mk_list(List.map quote_level us,`:l4_level`) in
  let entries ds=mk_list(List.map Env.quote_decl ds,`:l4_entry`) in
  let params ps=mk_list(List.map (fun (n,a) -> mk_pair(quote_name n,quote_expr a)) ps,`:l4_name#l4_expr`) in
  let specs cs=mk_list(List.map (fun (c,fs) -> node "L4CtorSpec" [quote_name c;
    mk_list(List.map (function Env.Data a -> node "L4Data" [quote_expr a]
      | Env.Recursive -> `L4Recursive`) fs,`:l4_field`)]) cs,`:l4_ctor_spec`) in
  let bool b=if b then `T` else `F` in
  let closed label target h =
    test (label^" closed") (hyp h=[]); test (label^" exact") (aconv (concl h) target) in
  let candidate i ps pars u cs large k =
    let b={Env.family_name=i;level_params=ps;parameters=pars;result_level=u;
      family_constructors=cs;family_claims=[]} in
    {b with Env.family_claims=Env.generate_family {remaining=100000} b ~large ~k} in
  let admit label env b vss large k =
    let after,h=get label (Env.admit_inductive_family env b) in
    closed (label^" admission") (node "l4_evalid" [Env.quote_policy after;Env.quote_env after]) h;
    let args=[Env.quote_policy env;Env.quote_env env;quote_name b.Env.family_name;names b.Env.level_params;
      params b.Env.parameters;quote_level b.Env.result_level;specs b.Env.family_constructors;
      mk_list(List.map levels vss,`:l4_level list`);bool large;bool k;entries b.Env.family_claims] in
    let detail=get label (Env.inductive_certificate after b.Env.family_name) in
    closed (label^" detail") (node "l4_family_checked" args) detail;
    let metadata=MATCH_MP (SPECL args l4_family_checked_metadata) detail in
    closed (label^" metadata") (node "l4_metadata_matches" [entries b.Env.family_claims;
      node "l4_family_generated" [quote_name b.Env.family_name;names b.Env.level_params;
        params b.Env.parameters;quote_level b.Env.result_level;specs b.Env.family_constructors;bool large;bool k]]) metadata;
    let elimination=MATCH_MP (SPECL args l4_family_checked_elimination) detail in
    closed (label^" elimination") (mk_conj(mk_eq(bool large,node "l4_family_large"
      [quote_level b.Env.result_level;specs b.Env.family_constructors;mk_list(List.map levels vss,`:l4_level list`)]),
      mk_eq(bool k,node "l4_family_k" [quote_level b.Env.result_level;specs b.Env.family_constructors]))) elimination;
    after in
  let stmt env g e e' ty=node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr e;quote_expr e';quote_expr ty] in
  let chk label env g e ty = closed label (stmt env g e e ty) (get label (Env.check env g e ty)) in
  let eq label env g e e' ty = closed label (stmt env g e e' ty) (get label (Env.convert env g e e' ty)) in
  let nat=nm "Nat" in
  let z=child nat "zero" and s=child nat "succ" and nt=Const(nat,[]) in
  let nb=candidate nat [] [] level [z,[];s,[Env.Recursive]] true false in
  let env=admit "canonical Nat family" Env.empty nb [[];[level]] true false in
  chk "Nat literal after family admission" env [] (Natlit "2") nt;
  let u=nm "u" and a=nm "A" in
  let wrap=nm "Wrap" in
  let mk=child wrap "mk" in
  let wu=Succ(Param u) in
  let wb=candidate wrap [u] [a,Sort wu] wu [mk,[Env.Data(Bvar 0)]] true false in
  let expected_ctor=pi (Sort wu) (pi (Bvar 0) (App(Const(wrap,[Param u]),Bvar 1))) in
  test "independent parameter constructor type" ((List.nth wb.Env.family_claims 1).Env.typ=expected_ctor);
  let motive=pi (App(Const(wrap,[Param u]),Bvar 0)) (Sort(Param(nm "u_1"))) in
  let minor=pi (Bvar 1) (App(Bvar 1,app (Const(mk,[Param u])) [Bvar 2;Bvar 0])) in
  let expected_rec=pi (Sort wu) (pi motive (pi minor
    (pi (App(Const(wrap,[Param u]),Bvar 2)) (App(Bvar 2,Bvar 0))))) in
  test "independent parameter recursor type" ((List.nth wb.Env.family_claims 2).Env.typ=expected_rec);
  let expected_rhs=lam (Sort wu) (lam motive (lam minor (lam (Bvar 2) (App(Bvar 1,Bvar 0))))) in
  (match (List.nth wb.Env.family_claims 2).Env.kind with Env.Generated(Env.Recursor_role r) ->
    test "independent parameter recursor RHS" ((List.hd r.Env.rules).Env.rhs=expected_rhs)
   | _ -> failwith "missing family recursor");
  let env=admit "polymorphic Wrap" env wb [[wu]] true false in
  ignore(admit "permuted family claim table" Env.empty
    {wb with Env.family_claims=List.rev wb.Env.family_claims} [[wu]] true false);
  let wt=App(Const(wrap,[Zero]),nt) in
  let wrapped=app (Const(mk,[Zero])) [nt;Natlit "2"] in
  chk "parameter constructor" env [] wrapped wt;
  let unwrap=app (Const(child wrap "rec",[level;Zero]))
    [nt;lam wt nt;lam nt (Bvar 0);wrapped] in
  eq "parameter iota" env [] unwrap (Natlit "2") nt;
  let pointed=nm "Pointed" in
  let pm=child pointed "mk" in
  let point=candidate pointed [] [a,Sort level;nm "point",Bvar 0] level
    [pm,[Env.Data(Bvar 1)]] true false in
  let env=admit "dependent parameter telescope" env point [[level]] true false in
  chk "dependent parameter constructor" env []
    (app (Const(pm,[])) [nt;Natlit "1";Natlit "2"])
    (app (Const(pointed,[])) [nt;Natlit "1"]);
  let list=nm "Sequence" in
  let nil=child list "nil" and cons=child list "cons" in
  let lb=candidate list [u] [a,Sort wu] wu
    [nil,[];cons,[Env.Data(Bvar 0);Env.Recursive]] true false in
  let env=admit "parameterized direct recursion" env lb [[];[wu;wu]] true false in
  let lt=App(Const(list,[Zero]),nt) in
  let empty=App(Const(nil,[Zero]),nt) in
  let singleton=app (Const(cons,[Zero])) [nt;Natlit "2";empty] in
  let fold=app (Const(child list "rec",[level;Zero]))
    [nt;lam lt nt;Natlit "0";lam nt (lam lt (lam nt (Bvar 2)));singleton] in
  eq "parameterized recursive iota" env [] fold (Natlit "2") nt;
  let phantom=nm "PolyNullary" in
  let phb=candidate phantom [u] [] (Param u) [nm "PolyNullaryMk",[]] true false in
  let env=admit "possibly Prop universe nullary elimination" env phb [[]] true false in
  let imax=nm "ImaxProp" in
  let ib=candidate imax [u] [] (Imax(Param u,Zero)) [nm "ImaxPropMk",[]] true true in
  let env=admit "symbolic always-zero K eligibility" env ib [[]] true true in
  let many=nm "FreshMany" in
  let manyps=u::List.init 10 (fun j -> nm("u_"^string_of_int(j+1))) in
  let mb=candidate many manyps [] level [] true false in
  test "fresh universe decimal suffix" ((List.nth mb.Env.family_claims 1).Env.params=nm "u_11"::manyps);
  let env=admit "fresh universe search past ten" env mb [] true false in
  let falsep=nm "FalseP" in
  let fb=candidate falsep [] [] Zero [] true false in
  let env=admit "empty Prop large elimination" env fb [] true false in
  let truep=nm "TrueP" and intro=nm "TrueIntro" in
  let tb=candidate truep [] [] Zero [intro,[]] true true in
  let env=admit "nullary Prop K metadata" env tb [[]] true true in
  let tp=Const(truep,[]) and ti=Const(intro,[]) in
  let tr major=app (Const(child truep "rec",[level])) [lam tp nt;Natlit "3";major] in
  eq "exposed K constructor iota" env [] (tr ti) (Natlit "3") nt;
  eq "neutral nullary Prop K reduction" env [tp] (tr(Bvar 0)) (Natlit "3") nt;
  let nested_major=Let(n,tp,Bvar 0,Bvar 0) in
  eq "zeta then neutral K reduction" env [tp] (tr nested_major) (Natlit "3") nt;
  eq "beta then neutral K reduction" env [tp]
    (tr(App(lam tp (Bvar 0),Bvar 0))) (Natlit "3") nt;
  let choice=nm "PropChoice" in
  let cb=candidate choice [] [] Zero [nm "ChoiceLeft",[];nm "ChoiceRight",[]] false false in
  let env=admit "multiple Prop constructors small elimination" env cb [[];[]] false false in
  let badlarge={cb with Env.family_claims=Env.generate_family {remaining=100000} cb ~large:true ~k:false} in
  decline "forged large Prop elimination" (Env.admit_inductive_family Env.empty badlarge);
  let boxed=nm "ProofBox" and p=nm "P" in
  let pb=candidate boxed [] [p,Sort Zero] Zero [nm "ProofBoxMk",[Env.Data(Bvar 0)]] true false in
  let env=admit "proof-only singleton large elimination" env pb [[Zero]] true false in
  let pbt=App(Const(boxed,[]),tp) in
  let pbmajor=app (Const(nm "ProofBoxMk",[])) [tp;ti] in
  let pbreduce=app (Const(child boxed "rec",[level])) [tp;lam pbt nt;lam tp (Natlit "4");pbmajor] in
  eq "proof-only singleton large iota" env [] pbreduce (Natlit "4") nt;
  let packed=nm "DataProp" in
  let db=candidate packed [u] [a,Sort wu] Zero [nm "DataPropMk",[Env.Data(Bvar 0)]] false false in
  let env=admit "data-bearing singleton small elimination" env db [[wu]] false false in
  let dt=App(Const(packed,[Zero]),nt) in
  let dmajor=app (Const(nm "DataPropMk",[Zero])) [nt;Natlit "2"] in
  chk "small recursor usable in Prop" env []
    (app (Const(child packed "rec",[Zero])) [nt;lam dt tp;lam nt ti;dmajor]) tp;
  let unsound={db with Env.family_claims=Env.generate_family {remaining=100000} db ~large:true ~k:false} in
  decline "data-bearing Prop cannot eliminate large" (Env.admit_inductive_family Env.empty unsound);
  let badk={pb with Env.family_claims=Env.generate_family {remaining=100000} pb ~large:true ~k:true} in
  decline "proof field prevents K metadata" (Env.admit_inductive_family Env.empty badk);
  decline "duplicate family universe parameters" (Env.admit_inductive_family Env.empty
    (candidate wrap [u;u] [a,Sort wu] wu [mk,[Env.Data(Bvar 0)]] true false));
  decline "undeclared family universe" (Env.admit_inductive_family Env.empty
    (candidate wrap [] [a,Sort wu] wu [mk,[Env.Data(Bvar 0)]] true false));
  decline "out of scope parameter" (Env.admit_inductive_family Env.empty
    (candidate wrap [] [a,Bvar 0] level [] true false));
  decline "out of scope field" (Env.admit_inductive_family Env.empty
    (candidate wrap [] [a,Sort level] level [mk,[Env.Data(Bvar 1)]] true false));
  decline "family field universe bound" (Env.admit_inductive_family Env.empty
    (candidate wrap [] [] level [mk,[Env.Data(Sort level)]] true false));
  decline "polymorphic primitive impersonation" (Env.admit_inductive_family Env.empty
    (candidate nat [u] [] level [z,[];s,[Env.Recursive]] true false));
  let nested=child (nm "_nested") "Family" in
  let nestedb=candidate nested [u] [] level [] true false in
  let nested_env=admit "empty reserved-prefix family" Env.empty nestedb [] true false in
  decline "reserved-prefix family result reference" (Env.admit_inductive_family Env.empty
    (candidate nested [u] [] level [nm "NestedFamilyMk",[]] true false));
  decline "prior reserved-prefix family field" (Env.admit_inductive_family nested_env
    (candidate wrap [u] [] level [mk,[Env.Data(Const(nested,[Param u]))]] true false));
  decline "negative family recursion" (Env.admit_inductive_family Env.empty
    (candidate wrap [u] [a,Sort wu] wu
      [mk,[Env.Data(pi (App(Const(wrap,[Param u]),Bvar 0)) (Sort Zero))]] true false));
  let forged=List.mapi (fun j d -> if j=2 then {d with Env.params=[nm "other";u]} else d) wb.Env.family_claims in
  decline "wrong generated elimination universe" (Env.admit_inductive_family Env.empty
    {wb with Env.family_claims=forged});
  test "family resource classification" (match Env.admit_inductive_family ~fuel:0 Env.empty wb with
    Error {kind=Resource;_} -> true | _ -> false);
  let permissions=MATCH_MP (SPECL [Env.quote_policy env;Env.quote_env env] l4_evalid_permissions)
    (Env.certificate env) in
  test "family permission invariant" (hyp permissions=[]);
  test "no new HOL axioms" (axioms()=l4_axioms_before);
  print_endline("HOL_FAMILY_TESTS_PASSED "^string_of_int !count);;

l4_family_tests ();;
