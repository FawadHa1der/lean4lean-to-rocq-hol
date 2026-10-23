(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_projection_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 and before=axioms() in
  let test label ok = if not ok then failwith("projection regression: "^label);
    incr count; print_endline("projection check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": wrong decline class: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let nm s=Str(Anonymous,s) and n=Anonymous in
  let child i s=Str(i,s) in
  let one=Succ Zero and two=Succ(Succ Zero) in
  let pi a b=Pi(n,a,b) and lam a b=Lam(n,a,b) and app=Env.apps in
  let closed label tm h=test (label^" closed") (hyp h=[]);test (label^" exact") (aconv(concl h) tm) in
  let stmt env g a b ty=node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
    quote_expr a;quote_expr b;quote_expr ty] in
  let check label env g a ty=closed label (stmt env g a a ty) (get label (Env.check env g a ty)) in
  let equal label env g a b ty=closed label (stmt env g a b ty) (get label (Env.convert env g a b ty)) in
  let admit label result =
    let env,h=get label result in
    closed label (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h; env in
  let block i u cs =
    let b={Env.inductive_name=i;inductive_level=u;constructors=cs;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  let family i ps parameters u cs large k =
    let b={Env.family_name=i;level_params=ps;parameters;result_level=u;
      family_constructors=cs;family_claims=[]} in
    {b with Env.family_claims=Env.generate_family {remaining=100000} b ~large ~k} in
  let ctor name fields result={Env.indexed_ctor_name=name;indexed_fields=fields;result_indices=result} in
  let indexed i indices u cs large =
    let b={Env.indexed_name=i;indexed_level_params=[];indexed_parameters=[];indices;
      indexed_result_level=u;indexed_constructors=cs;indexed_claims=[]} in
    {b with Env.indexed_claims=Env.generate_indexed {remaining=100000} b ~large ~k:false} in
  let nat=nm "Nat" in let nt=Const(nat,[]) in
  let env=admit "Nat" (Env.admit_inductive Env.empty
    (block nat one [child nat "zero",[];child nat "succ",[Env.Recursive]])) in
  let pair=nm "ProjectionPair" in let mk=child pair "mk" in
  let pt=Const(pair,[]) in
  let env=admit "pair" (Env.admit_inductive env (block pair one [mk,[Env.Data nt;Env.Data nt]])) in
  let value=app (Const(mk,[])) [Natlit "2";Natlit "3"] in
  check "first field type" env [] (Proj(pair,0,value)) nt;
  check "last field type" env [] (Proj(pair,1,value)) nt;
  equal "first field reduction" env [] (Proj(pair,0,value)) (Natlit "2") nt;
  equal "last field reduction" env [] (Proj(pair,1,value)) (Natlit "3") nt;
  check "neutral major typing" env [pt] (Proj(pair,1,Bvar 0)) nt;
  equal "beta major reduction" env [] (Proj(pair,1,App(lam pt (Bvar 0),value))) (Natlit "3") nt;
  equal "zeta major reduction" env [] (Proj(pair,0,Let(n,pt,value,Bvar 0))) (Natlit "2") nt;
  let open_value=app (Const(mk,[])) [Bvar 0;Bvar 0] in
  equal "ambient bound variables survive telescope removal" env [nt]
    (Proj(pair,1,open_value)) (Bvar 0) nt;
  decline "out of bounds" (Env.infer env [] (Proj(pair,2,value)));
  decline "wrong owner" (Env.infer env [] (Proj(nat,0,value)));
  decline "multiple constructors" (Env.infer env [] (Proj(nat,0,Natlit "2")));
  decline "unknown owner" (Env.infer env [] (Proj(nm "UnknownProjection",0,value)));
  test "negative index is malformed" (match Env.infer env [] (Proj(pair,-1,value)) with
    Error {kind=Invalid_input;_} -> true | _ -> false);
  test "fuel exhaustion is a resource decline" (match Env.infer ~fuel:0 env [] (Proj(pair,0,value)) with
    Error {kind=Resource;_} -> true | _ -> false);
  decline "pure projection typing remains unsupported" (infer [] (Proj(pair,0,value)));
  let u=nm "u" and box=nm "ProjectionBox" in
  let boxb=family box [u] [nm "A",Sort(Param u)] (Param u)
    [child box "mk",[Env.Data(Bvar 0)]] false false in
  let env=admit "universe-polymorphic box" (Env.admit_inductive_family env boxb) in
  let bv=app (Const(child box "mk",[one])) [nt;Natlit "4"] in
  equal "universe and parameter instantiation" env [] (Proj(box,0,bv)) (Natlit "4") nt;
  let btype=App(Const(box,[Param u]),Bvar 0) in
  decline "possibly Prop with unknown field universe"
    (Env.infer env [btype;Sort(Param u)] (Proj(box,0,Bvar 0)));
  let dep=nm "ProjectionDependent" in
  let db=indexed dep [] two [ctor (child dep "mk")
    [Env.Index_data(Sort one);Env.Index_data(Bvar 0)] []] true in
  let env=admit "dependent fields" (Env.admit_indexed_inductive env db) in
  let dv=app (Const(child dep "mk",[])) [nt;Natlit "5"] in
  check "dependent projection type retains preceding projection" env [Const(dep,[])]
    (Proj(dep,1,Bvar 0)) (Proj(dep,0,Bvar 0));
  equal "dependent first field" env [] (Proj(dep,0,dv)) nt (Sort one);
  equal "dependent second field reduces at converted type" env [] (Proj(dep,1,dv)) (Natlit "5") nt;
  let wrap=nm "ProjectionIndexed" in
  let wb=indexed wrap [nm "index",nt] one [ctor (child wrap "mk")
    [Env.Index_data nt;Env.Index_data nt] [Bvar 1]] true in
  let env=admit "indexed owner" (Env.admit_indexed_inductive env wb) in
  let wv=app (Const(child wrap "mk",[])) [Natlit "6";Natlit "7"] in
  equal "indexed constructor projection" env [] (Proj(wrap,1,wv)) (Natlit "7") nt;
  check "indexed neutral projection" env [App(Const(wrap,[]),Natlit "6")]
    (Proj(wrap,0,Bvar 0)) nt;
  let truth=nm "ProjectionTruth" in
  let tb=family truth [] [] Zero [child truth "intro",[]] true true in
  let env=admit "truth" (Env.admit_inductive_family env tb) in
  let tp=Const(truth,[]) and ti=Const(child truth "intro",[]) in
  let proofbox=nm "ProjectionProofBox" in
  let pb=family proofbox [] [] Zero [child proofbox "mk",[Env.Data tp]] true false in
  let env=admit "proof record" (Env.admit_inductive_family env pb) in
  equal "Prop selected proof field" env [] (Proj(proofbox,0,App(Const(child proofbox "mk",[]),ti))) ti tp;
  let bb=app (Const(child box "mk",[Zero])) [tp;ti] in
  equal "possibly Prop specialized to Prop" env [] (Proj(box,0,bb)) ti tp;
  let data=nm "ProjectionDataProp" in
  let data_b=family data [] [] Zero [child data "mk",[Env.Data nt;Env.Data tp]] false false in
  let env=admit "data and proof in Prop" (Env.admit_inductive_family env data_b) in
  let data_v=app (Const(child data "mk",[])) [Natlit "8";ti] in
  decline "Prop cannot project non-Prop selected field" (Env.infer env [] (Proj(data,0,data_v)));
  equal "unused non-Prop preceding field may be skipped" env [] (Proj(data,1,data_v)) ti tp;
  let dp=nm "ProjectionDependentProp" in
  let dpb=indexed dp [] Zero [ctor (child dp "mk")
    [Env.Index_data(Sort Zero);Env.Index_data(Bvar 0)] []] false in
  let env=admit "dependent Prop record" (Env.admit_indexed_inductive env dpb) in
  let dpv=app (Const(child dp "mk",[])) [tp;ti] in
  decline "used non-Prop preceding field is forbidden" (Env.infer env [] (Proj(dp,1,dpv)));
  let dn=nm "ProjectionDefinition" in
  let env=admit "projection body declaration" (Env.admit env
    {Env.kind=Env.Definition;name=dn;params=[];typ=nt;value=Some(Proj(pair,1,value))}) in
  equal "delta through projection body" env [] (Const(dn,[])) (Natlit "3") nt;
  let sample=Proj(pair,1,Lam(n,Sort(Param u),Bvar 0)) in
  let qs=quote_expr sample in
  let calc=REWRITE_CONV [l4_expr_lsubst;l4_level_lsubst;l4_lparam;l4_anon;l4_no_nested_aux;
    l4_nested_name;l4_params_expr;l4_params_level;l4_without_const;l4_uses_bound;
    HD;TL;MEM;distinctness "l4_name";injectivity "l4_name";distinctness "list";injectivity "list"]
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let computations=[
    "projection universe substitution",node "l4_expr_lsubst"
      [qs;mk_list([quote_name u],`:l4_name`);mk_list([quote_level one],`:l4_level`)],
      quote_expr(Proj(pair,1,Lam(n,Sort one,Bvar 0)));
    "binder erasure traverses projection",node "l4_anon" [quote_expr(Proj(pair,0,Lam(nm "x",nt,Bvar 0)))],
      quote_expr(Proj(pair,0,Lam(n,nt,Bvar 0)));
    "nested projection owner guard",node "l4_no_nested_aux" [quote_expr(Proj(child (nm "_nested") "T",0,Bvar 0))],`F`;
    "nested projection major guard",node "l4_no_nested_aux"
      [quote_expr(Proj(pair,0,Const(child (nm "_nested") "T",[])))],`F`;
    "universe scope traverses projection",node "l4_params_expr" [qs;`[]:l4_name list`],`F`;
    "positivity traverses projection",node "l4_without_const" [quote_name dep;quote_expr(Proj(pair,0,Const(dep,[])))],`F`;
    "bound occurrence under projection",node "l4_uses_bound" [quote_expr(Proj(pair,0,Bvar 1));number 1],`T`;
    "ambient variable is not removed field",node "l4_uses_bound" [quote_expr(pi nt (Bvar 2));number 0],`F`;
    "removed field below binder",node "l4_uses_bound" [quote_expr(pi nt (Bvar 1));number 0],`T`] in
  List.iter (fun (label,tm,result) -> closed label (mk_eq(tm,result)) (calc tm)) computations;
  let expand=List.nth(CONJUNCTS l4_expand_RULES) 8 in
  let bv=quote_expr(Bvar 0) in
  let hexpand=MP (SPECL [`[]:l4_decl list`;quote_name pair;number 1;bv;bv] expand)
    (SPECL [`[]:l4_decl list`;number 0] (CONJUNCT1 l4_expand_RULES)) in
  closed "macro traversal projection"
    (node "l4_expand" [`[]:l4_decl list`;quote_expr(Proj(pair,1,Bvar 0));quote_expr(Proj(pair,1,Bvar 0))]) hexpand;
  test "29 native rules and 11 admission rules"
    (List.length(CONJUNCTS l4_edef_RULES)=29 &&
      List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no added HOL axioms" (axioms()=before);
  print_endline("HOL_PROJECTION_TESTS_PASSED "^string_of_int !count);;

l4_projection_tests ();;
