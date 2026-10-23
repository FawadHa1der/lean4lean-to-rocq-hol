(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_environment_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let n = Anonymous and count = ref 0 in
  let nm s = Str(Anonymous,s) in
  let c s = Const(nm s,[]) in
  let prop = Sort Zero and typ = Sort(Succ Zero) in
  let test label b = if not b then failwith("environment regression: "^label); incr count in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function Error _ -> test label true | Ok _ -> failwith("accepted: "^label) in
  let expected env g e e' a = node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr e;quote_expr e';quote_expr a] in
  let eq env g e e' a =
    let th = get "conversion" (Env.convert env g e e' a) in
    test "closed conversion" (hyp th=[]);
    test "exact conversion" (aconv (concl th) (expected env g e e' a)) in
  let chk env g e a =
    let th = get "typing" (Env.check env g e a) in
    test "closed typing" (hyp th=[]);
    test "exact typing" (aconv (concl th) (expected env g e e a)) in
  let admit env d =
    let env',th = get "admission" (Env.admit env d) in
    test "closed environment" (hyp th=[]);
    test "exact environment" (aconv (concl th)
      (node "l4_evalid" [Env.quote_policy env';Env.quote_env env'])); env' in
  let ax s a = {Env.kind=Env.Axiom;name=nm s;params=[];typ=a;value=None} in
  let axa = ax "A" typ and axx = ax "x" (c "A") and axy = ax "y" (c "A") in
  let axs = [axa;axx;axy;ax "P" prop;ax "h" (c "P");ax "h2" (c "P")] in
  let permits = List.map (fun d ->
    {Env.axiom_name=d.Env.name;axiom_params=d.Env.params;axiom_type=d.Env.typ}) axs in
  chk Env.empty [] prop typ;
  decline "default axiom denial" (Env.admit Env.empty axa);
  let env = get "policy" (Env.with_axioms permits) in
  decline "changed permitted type" (Env.admit env {axa with Env.typ=prop});
  decline "forward type dependency" (Env.admit env axx);
  let env = List.fold_left admit env axs in
  chk env [] (c "x") (c "A");
  eq env [] (c "h") (c "h2") (c "P");
  decline "not all constants proof irrelevant" (Env.convert env [] (c "x") (c "y") (c "A"));
  let mk k s a v = {Env.kind=k;name=nm s;params=[];typ=a;value=Some v} in
  let env = admit env (mk Env.Definition "id" (Pi(n,c "A",c "A")) (Lam(n,c "A",Bvar 0))) in
  eq env [] (App(c "id",c "x")) (c "x") (c "A");
  let env = admit env (mk Env.Opaque "o" (c "A") (c "x")) in
  chk env [] (c "o") (c "A");
  decline "opaque must not unfold" (Env.convert env [] (c "o") (c "x") (c "A"));
  decline "opaque bad body" (Env.admit env (mk Env.Opaque "bad" (c "A") typ));
  let env = admit env (mk Env.Opaque "o2" (c "A") (c "x")) in
  decline "equal bodies do not equate opaques" (Env.convert env [] (c "o") (c "o2") (c "A"));
  let env = admit env (mk Env.Opaque "ofun" (Pi(n,c "A",c "A")) (c "id")) in
  decline "opaque application not beta" (Env.convert env [] (App(c "ofun",c "x")) (c "x") (c "A"));
  eq env [] (Lam(n,c "A",App(c "ofun",Bvar 0))) (c "ofun") (Pi(n,c "A",c "A"));
  let env = admit env (mk Env.Opaque "oproof" (c "P") (c "h")) in
  eq env [] (c "oproof") (c "h2") (c "P");
  let env = admit env (mk Env.Definition "alias" (c "A") (c "o")) in
  eq env [] (c "alias") (c "o") (c "A");
  decline "alias preserves opacity" (Env.convert env [] (c "alias") (c "x") (c "A"));
  decline "opaque self reference" (Env.admit env (mk Env.Opaque "self" (c "A") (c "self")));
  decline "theorem requires proposition" (Env.admit env (mk Env.Theorem "badthm" (c "A") (c "x")));
  let env = admit env (mk Env.Theorem "thm" (c "P") (c "h")) in
  eq env [] (c "thm") (c "h") (c "P");
  chk env [c "A"] (App(c "id",Bvar 0)) (c "A");
  eq env [] (Lam(n,c "A",App(c "id",Bvar 0))) (c "id") (Pi(n,c "A",c "A"));
  let u = nm "u" in
  let poly = {Env.kind=Env.Opaque;name=nm "poly";params=[u];
    typ=Pi(n,Sort(Param u),Pi(n,Bvar 0,Bvar 1));
    value=Some(Lam(n,Sort(Param u),Lam(n,Bvar 0,Bvar 0)))} in
  let env = admit env poly in
  chk env [] (Const(nm "poly",[Succ Zero])) (Pi(n,typ,Pi(n,Bvar 0,Bvar 1)));
  eq env [] (Const(nm "poly",[Max(Zero,Succ Zero)])) (Const(nm "poly",[Succ Zero]))
    (Pi(n,typ,Pi(n,Bvar 0,Bvar 1)));
  decline "opaque polymorphic unfolding" (Env.convert env [] (Const(nm "poly",[Succ Zero]))
    (Lam(n,typ,Lam(n,Bvar 0,Bvar 0))) (Pi(n,typ,Pi(n,Bvar 0,Bvar 1))));
  decline "constant arity" (Env.infer env [] (Const(nm "poly",[])));
  decline "duplicate admission" (Env.admit env axa);
  decline "undeclared universe" (Env.admit env {poly with Env.name=nm "badpoly";params=[]});
  decline "body required" (Env.admit env {poly with Env.name=nm "empty";value=None});
  decline "axiom has no body" (Env.admit env {axa with Env.name=nm "bodyax";value=Some prop});
  decline "resource" (Env.check ~fuel:0 env [] (c "x") (c "A"));
  decline "policy resource" (Env.with_axioms ~fuel:0 permits);
  let permission_proof = MATCH_MP
    (SPECL [Env.quote_policy env;Env.quote_env env] l4_evalid_permissions) (Env.certificate env) in
  let permission_term = vsubst [Env.quote_policy env,`policy:l4_entry list`;Env.quote_env env,`env:l4_entry list`]
    `ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) env` in
  test "permission theorem closed" (hyp permission_proof=[]);
  test "permission theorem conclusion" (aconv (concl permission_proof) permission_term);
  let unique = MATCH_MP (SPECL [Env.quote_policy env;Env.quote_env env] l4_evalid_unique) (Env.certificate env) in
  test "unique environment theorem closed" (hyp unique=[]);
  let u1 = nm "u1" and u2 = nm "u2" in
  let axpoly = {Env.kind=Env.Axiom;name=nm "axpoly";params=[u1;u2];typ=Sort(Param u1);value=None} in
  let polyperm = {Env.axiom_name=axpoly.Env.name;axiom_params=axpoly.Env.params;axiom_type=axpoly.Env.typ} in
  let polyenv = get "polymorphic policy" (Env.with_axioms [polyperm]) in
  decline "permission parameter order" (Env.admit polyenv {axpoly with Env.params=[u2;u1]});
  let polyenv = admit polyenv axpoly in
  chk polyenv [] (Const(nm "axpoly",[Succ Zero;Zero])) typ;
  let badgrant = {Env.axiom_name=nm "nontype";axiom_params=[];axiom_type=c "x"} in
  let env2 = get "nontype policy" (Env.with_axioms (badgrant::permits)) in
  let env2 = List.fold_left admit env2 axs in
  decline "permitted axiom still needs type formation" (Env.admit env2 (ax "nontype" (c "x")));
  test "no new HOL axioms" (axioms () = l4_axioms_before);
  print_endline("HOL_ENVIRONMENT_TESTS_PASSED "^string_of_int !count);;

l4_environment_tests ();;
