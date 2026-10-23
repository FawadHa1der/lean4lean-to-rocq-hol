(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_structure_major_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let before=axioms() and count=ref 0 in
  let test label ok = if not ok then failwith("major regression: "^label);
    incr count; print_endline("major check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_} -> test label true
    | Error e -> failwith(label^": wrong error class: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let n=Anonymous and nm s=Str(Anonymous,s) in
  let child i s=Str(i,s) in
  let one=Succ Zero and two=Succ(Succ Zero) in
  let lam a b=Lam(n,a,b) and pi a b=Pi(n,a,b) and app=Env.apps in
  let closed label tm h=test (label^" closed") (hyp h=[]);test (label^" exact") (aconv(concl h) tm) in
  let equal label env g a b ty =
    let h=get label (Env.convert env g a b ty) in
    closed label (node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
      quote_expr a;quote_expr b;quote_expr ty]) h in
  let admit label result = let env,h=get label result in
    closed label (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h; env in
  let block i u cs = let b={Env.inductive_name=i;inductive_level=u;constructors=cs;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  let family i ps parameters u cs large k =
    let b={Env.family_name=i;level_params=ps;parameters;result_level=u;family_constructors=cs;family_claims=[]} in
    {b with Env.family_claims=Env.generate_family {remaining=100000} b ~large ~k} in
  let ctor name fields result={Env.indexed_ctor_name=name;indexed_fields=fields;result_indices=result} in
  let indexed i inds u cs =
    let b={Env.indexed_name=i;indexed_level_params=[];indexed_parameters=[];indices=inds;
      indexed_result_level=u;indexed_constructors=cs;indexed_claims=[]} in
    {b with Env.indexed_claims=Env.generate_indexed {remaining=100000} b ~large:true ~k:false} in
  let nat=nm "Nat" in let nt=Const(nat,[]) in
  let env=admit "Nat" (Env.admit_inductive Env.empty
    (block nat one [child nat "zero",[];child nat "succ",[Env.Recursive]])) in
  let pair=nm "MajorPair" in let pt=Const(pair,[]) in
  let env=admit "pair" (Env.admit_inductive env
    (block pair one [child pair "mk",[Env.Data nt;Env.Data nt]])) in
  let select major=app (Const(child pair "rec",[one]))
    [lam pt nt;lam nt (lam nt (Bvar 1));major] in
  equal "neutral structure recursor" env [pt] (select(Bvar 0)) (Proj(pair,0,Bvar 0)) nt;
  equal "normalized beta major" env [pt] (select(App(lam pt (Bvar 0),Bvar 0))) (Proj(pair,0,Bvar 0)) nt;
  equal "normalized zeta major" env [pt] (select(Let(n,pt,Bvar 0,Bvar 0))) (Proj(pair,0,Bvar 0)) nt;
  equal "exposed constructor still reduces" env []
    (select(app (Const(child pair "mk",[])) [Natlit "3";Natlit "4"])) (Natlit "3") nt;
  let fnrec=app (Const(child pair "rec",[one]))
    [lam pt (pi nt nt);lam nt (lam nt (lam nt (Bvar 2)));Bvar 0] in
  equal "overapplication" env [pt] (App(fnrec,Natlit "7")) (Proj(pair,0,Bvar 0)) nt;
  let dep=nm "MajorDependent" in let dt=Const(dep,[]) in
  let env=admit "dependent record" (Env.admit_indexed_inductive env
    (indexed dep [] two [ctor (child dep "mk") [Env.Index_data(Sort one);Env.Index_data(Bvar 0)] []])) in
  let dependent_rec=app (Const(child dep "rec",[one]))
    [lam dt (Proj(dep,0,Bvar 0));lam (Sort one) (lam (Bvar 0) (Bvar 0));Bvar 0] in
  equal "dependent motive transport" env [dt] dependent_rec (Proj(dep,1,Bvar 0)) (Proj(dep,0,Bvar 0));
  let u=nm "u" and box=nm "MajorBox" in
  let bb=family box [u] [nm "A",Sort(Succ(Param u))] (Succ(Param u))
    [child box "mk",[Env.Data(Bvar 0)]] true false in
  let env=admit "polymorphic box" (Env.admit_inductive_family env bb) in
  let bx=App(Const(box,[Param u]),Bvar 0) in
  let bt=App(Const(box,[Param u]),Bvar 1) in
  let boxedrec=app (Const(child box "rec",[Succ(Param u);Param u]))
    [Bvar 1;lam bt (Bvar 2);lam (Bvar 1) (Bvar 0);Bvar 0] in
  equal "symbolic successor nonzero guard" env [bx;Sort(Succ(Param u))]
    boxedrec (Proj(box,0,Bvar 0)) (Bvar 1);
  let unit=nm "MajorUnit" in let ut=Const(unit,[Param u]) in
  let ub=family unit [u] [] (Succ(Param u)) [child unit "mk",[]] true false in
  let env=admit "polymorphic unit" (Env.admit_inductive_family env ub) in
  let unitrec=app (Const(child unit "rec",[one;Param u])) [lam ut nt;Natlit "2";Bvar 0] in
  equal "zero-field Type recursor" env [ut] unitrec (Natlit "2") nt;
  let truth=nm "MajorTruth" in let tp=Const(truth,[]) in
  let env=admit "truth" (Env.admit_inductive_family env
    (family truth [] [] Zero [child truth "intro",[]] true true)) in
  let proofbox=nm "MajorPropBox" in let pbt=Const(proofbox,[]) in
  let env=admit "proof record" (Env.admit_inductive_family env
    (family proofbox [] [] Zero [child proofbox "mk",[Env.Data tp]] true false)) in
  let prop_rec=app (Const(child proofbox "rec",[one])) [lam pbt nt;lam tp (Natlit "2");Bvar 0] in
  decline "Prop structure cannot use nonzero major expansion" (Env.convert env [pbt] prop_rec (Natlit "2") nt);
  let recursive=nm "MajorRecursive" in let rt=Const(recursive,[]) in
  let env=admit "recursive singleton" (Env.admit_inductive env
    (block recursive one [child recursive "mk",[Env.Recursive]])) in
  let recursive_rec=app (Const(child recursive "rec",[one]))
    [lam rt nt;lam rt (lam nt (Natlit "2"));Bvar 0] in
  decline "recursive singleton cannot expand" (Env.convert env [rt] recursive_rec (Natlit "2") nt);
  let ix=nm "MajorIndexed" in let it x=App(Const(ix,[]),x) in
  let env=admit "indexed singleton" (Env.admit_indexed_inductive env
    (indexed ix [nm "index",nt] one [ctor (child ix "mk") [] [Natlit "0"]])) in
  let indexed_rec=app (Const(child ix "rec",[one]))
    [lam nt (lam (it(Bvar 0)) nt);Natlit "2";Natlit "0";Bvar 0] in
  decline "indexed singleton cannot expand" (Env.convert env [it(Natlit "0")] indexed_rec (Natlit "2") nt);
  let en=nm "MajorEnum" in let et=Const(en,[]) in
  let env=admit "enum" (Env.admit_inductive env
    (block en one [child en "left",[];child en "right",[]])) in
  let enum_rec=app (Const(child en "rec",[one])) [lam et nt;Natlit "2";Natlit "3";Bvar 0] in
  decline "multiple constructors cannot expand" (Env.convert env [et] enum_rec (Natlit "2") nt);
  decline "wrong major owner" (Env.convert env [et] (select(Bvar 0)) (Natlit "2") nt);
  test "resource decline" (match Env.convert ~fuel:0 env [pt] (select(Bvar 0)) (Proj(pair,0,Bvar 0)) nt with
    Error {kind=Resource;_} -> true | _ -> false);
  let expected_nonzero=`!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
    l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u ==>
    l4_level_nonzero u` in
  closed "certificate entails nonzero sort" expected_nonzero l4_struct_major_nonzero;
  let expected_shape=`!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
    l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u ==>
    l4_eta_meta ind ctor owner us pars nf` in
  closed "certificate entails authenticated structure" expected_shape l4_struct_major_structure;
  let vars,_=strip_forall(concl l4_struct_major_nonzero) in
  let args=List.rev(List.tl(List.rev vars)) in
  List.iter (fun (label,u) ->
    let qu=quote_level u in
    let nonzero=node "l4_level_nonzero" [qu] in
    let neg=prove(mk_neg nonzero,REWRITE_TAC [l4_level_nonzero;NOT_FORALL_THM] THEN
      EXISTS_TAC `\n:l4_name. 0` THEN REWRITE_TAC [l4_eval_level] THEN CONV_TAC NUM_REDUCE_CONV) in
    let implication=SPECL (args@[qu]) l4_struct_major_nonzero in
    let impossible=MATCH_MP (TAUT `(p ==> q) ==> ~q ==> ~p`) implication in
    let impossible=MP impossible neg in
    closed label (mk_neg(node "l4_struct_major" (args@[qu]))) impossible)
    ["Prop certificate impossible",Zero;
     "symbolic possibly-zero certificate impossible",Param u;
     "imax always-zero certificate impossible",Imax(Param u,Zero)];
  test "indexed mutual clauses appended after structure rules" (List.length(CONJUNCTS l4_edef_RULES)=29 &&
    List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=before);
  print_endline("HOL_STRUCTURE_MAJOR_TESTS_PASSED "^string_of_int !count);;

l4_structure_major_tests ();;
