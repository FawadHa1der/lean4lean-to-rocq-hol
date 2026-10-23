(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_structure_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 and before=axioms() in
  let test label ok = if not ok then failwith("structure regression: "^label);
    incr count; print_endline("structure check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_} -> test label true
    | Error e -> failwith(label^": wrong decline class: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let nm s=Str(Anonymous,s) and n=Anonymous in
  let child i s=Str(i,s) in
  let one=Succ Zero and two=Succ(Succ Zero) in
  let pi a b=Pi(n,a,b) and app=Env.apps in
  let closed label tm h=test (label^" closed") (hyp h=[]);test (label^" exact") (aconv(concl h) tm) in
  let stmt env g a b ty=node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
    quote_expr a;quote_expr b;quote_expr ty] in
  let equal label env g a b ty=closed label (stmt env g a b ty) (get label (Env.convert env g a b ty)) in
  let admit label result =
    let env,h=get label result in
    closed label (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h; env in
  let block i u cs =
    let b={Env.inductive_name=i;inductive_level=u;constructors=cs;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  let family i ps parameters u cs large =
    let b={Env.family_name=i;level_params=ps;parameters;result_level=u;
      family_constructors=cs;family_claims=[]} in
    {b with Env.family_claims=Env.generate_family {remaining=100000} b ~large ~k:false} in
  let ctor name fields result={Env.indexed_ctor_name=name;indexed_fields=fields;result_indices=result} in
  let indexed i indices u cs =
    let b={Env.indexed_name=i;indexed_level_params=[];indexed_parameters=[];indices;
      indexed_result_level=u;indexed_constructors=cs;indexed_claims=[]} in
    {b with Env.indexed_claims=Env.generate_indexed {remaining=100000} b ~large:true ~k:false} in
  let nat=nm "Nat" in let nt=Const(nat,[]) in
  let env=admit "Nat" (Env.admit_inductive Env.empty
    (block nat one [child nat "zero",[];child nat "succ",[Env.Recursive]])) in
  let unit=nm "EtaUnit" in let ut=Const(unit,[]) and ui=Const(child unit "mk",[]) in
  let env=admit "unit" (Env.admit_inductive env (block unit one [child unit "mk",[]])) in
  equal "unit-like neutrals" env [ut;ut] (Bvar 0) (Bvar 1) ut;
  equal "unit-like constructor" env [ut] (Bvar 0) ui ut;
  equal "unit-like symmetry" env [ut] ui (Bvar 0) ut;
  let pair=nm "EtaPair" in let pt=Const(pair,[]) and mk=Const(child pair "mk",[]) in
  let env=admit "pair" (Env.admit_inductive env
    (block pair one [child pair "mk",[Env.Data nt;Env.Data nt]])) in
  let expanded=app mk [Proj(pair,0,Bvar 0);Proj(pair,1,Bvar 0)] in
  equal "structure eta" env [pt] (Bvar 0) expanded pt;
  equal "structure eta symmetry" env [pt] expanded (Bvar 0) pt;
  decline "eta does not replace a field" (Env.convert env [pt] (Bvar 0)
    (app mk [Natlit "0";Proj(pair,1,Bvar 0)]) pt);
  decline "different fields are not convertible" (Env.convert env [pt]
    (Proj(pair,0,Bvar 0)) (Proj(pair,1,Bvar 0)) nt);
  test "two neutral non-unit structures decline without eta loops"
    (match Env.convert ~fuel:1200 env [pt;pt] (Bvar 0) (Bvar 1) pt with
     Error {kind=Proof_failure;_} -> true | _ -> false);
  test "unequal constructor fields decline without repeated eta"
    (match Env.convert ~fuel:2500 env [] (app mk [Natlit "0";Natlit "1"])
      (app mk [Natlit "1";Natlit "1"]) pt with
     Error {kind=Proof_failure;_} -> true | _ -> false);
  let g=[ut;ut;pi ut pt] in
  let m1=App(Bvar 2,Bvar 1) and m2=App(Bvar 2,Bvar 0) in
  equal "neutral projection congruence" env g (Proj(pair,0,m1)) (Proj(pair,0,m2)) nt;
  let outer=nm "EtaOuter" in let ot=Const(outer,[]) in
  let env=admit "outer record" (Env.admit_inductive env
    (block outer one [child outer "mk",[Env.Data pt]])) in
  let nested major=Proj(pair,1,Proj(outer,0,major)) in
  equal "nested projection congruence" env [ut;ut;pi ut ot] (nested m1) (nested m2) nt;
  let dep=nm "EtaDependent" in let dt=Const(dep,[]) in
  let db=indexed dep [] two [ctor (child dep "mk")
    [Env.Index_data(Sort one);Env.Index_data(Bvar 0)] []] in
  let env=admit "dependent structure" (Env.admit_indexed_inductive env db) in
  let dexp=app (Const(child dep "mk",[])) [Proj(dep,0,Bvar 0);Proj(dep,1,Bvar 0)] in
  equal "dependent structure eta" env [dt] (Bvar 0) dexp dt;
  equal "dependent projection congruence transports field type" env [ut;ut;pi ut dt]
    (Proj(dep,1,m1)) (Proj(dep,1,m2)) (Proj(dep,0,m1));
  let u=nm "u" and box=nm "EtaBox" in
  let bb=family box [u] [nm "A",Sort(Param u)] (Param u)
    [child box "mk",[Env.Data(Bvar 0)]] false in
  let env=admit "parameterized structure" (Env.admit_inductive_family env bb) in
  let bt=App(Const(box,[one]),nt) in
  equal "polymorphic parameterized eta" env [bt] (Bvar 0)
    (app (Const(child box "mk",[one])) [nt;Proj(box,0,Bvar 0)]) bt;
  let phantom=nm "EtaPhantom" in
  let ph=family phantom [u] [nm "A",Sort(Param u)] one [child phantom "mk",[]] true in
  let env=admit "parameterized unit" (Env.admit_inductive_family env ph) in
  let pht a=App(Const(phantom,[one]),a) in
  equal "unit-like same parameters" env [pht nt;pht nt] (Bvar 0) (Bvar 1) (pht nt);
  decline "unit-like different parameters" (Env.convert env [pht nt;pht ut] (Bvar 0) (Bvar 1) (pht nt));
  decline "unit-like different owners" (Env.convert env [ut;pht nt] (Bvar 0) (Bvar 1) ut);
  let recursive=nm "EtaRecursive" in let rt=Const(recursive,[]) in
  let env=admit "recursive singleton" (Env.admit_inductive env
    (block recursive one [child recursive "mk",[Env.Recursive]])) in
  decline "recursive singleton has no structure eta" (Env.convert env [rt] (Bvar 0)
    (App(Const(child recursive "mk",[]),Proj(recursive,0,Bvar 0))) rt);
  let ix=nm "EtaIndexedUnit" in
  let ib=indexed ix [nm "n",nt] one [ctor (child ix "mk") [] [Natlit "0"]] in
  let env=admit "indexed nullary constructor" (Env.admit_indexed_inductive env ib) in
  let it=App(Const(ix,[]),Natlit "0") in
  decline "indexed singleton has no unit eta" (Env.convert env [it;it] (Bvar 0) (Bvar 1) it);
  let enumeration=nm "EtaEnum" in let et=Const(enumeration,[]) in
  let env=admit "multiple constructors" (Env.admit_inductive env
    (block enumeration one [child enumeration "left",[];child enumeration "right",[]])) in
  decline "multiple constructors have no unit eta" (Env.convert env [et;et] (Bvar 0) (Bvar 1) et);
  let boxedunit=App(Const(box,[one]),ut) in
  test "a structure of unit fields is not a zero-field unit"
    (match Env.convert ~fuel:1200 env [boxedunit;boxedunit] (Bvar 0) (Bvar 1) boxedunit with
     Error {kind=Proof_failure;_} -> true | _ -> false);
  test "structure eta resource classification" (match Env.convert ~fuel:0 env [pt] (Bvar 0) expanded pt with
    Error {kind=Resource;_} -> true | _ -> false);
  test "projection congruence resource classification"
    (match Env.convert ~fuel:0 env g (Proj(pair,0,m1)) (Proj(pair,0,m2)) nt with
     Error {kind=Resource;_} -> true | _ -> false);
  let role ni recursive ctors = node "L4InductiveRole" [number 0;number ni;
    mk_list([quote_name pair],`:l4_name`);mk_list(List.map quote_name ctors,`:l4_name`);
    number 0;(if recursive then `T` else `F`);`F`;`F`] in
  let c=child pair "mk" in
  let guard label role expected =
    let tm=node "l4_eta_ind_meta" [role;quote_name c;number 0] in
    let h=(REWRITE_CONV [l4_eta_ind_meta;distinctness "list";injectivity "list"] THENC NUM_REDUCE_CONV) tm in
    closed label (mk_eq(tm,expected)) h in
  guard "HOL positive eta metadata" (role 0 false [c]) `T`;
  guard "HOL rejects recursive metadata" (role 0 true [c]) `F`;
  guard "HOL rejects indexed metadata" (role 1 false [c]) `F`;
  guard "HOL rejects empty constructor metadata" (role 0 false []) `F`;
  guard "HOL rejects multiple constructor metadata" (role 0 false [c;c]) `F`;
  let rules=CONJUNCTS l4_edef_RULES in
  test "native and admission rules include guarded quotient extensions"
    (List.length rules=29 && List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no added HOL axioms" (axioms()=before);
  print_endline("HOL_STRUCTURE_TESTS_PASSED "^string_of_int !count);;

l4_structure_tests ();;
