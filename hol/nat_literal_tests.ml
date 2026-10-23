(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_nat_literal_axioms_before = axioms ();;
needs "hol/environment.ml";;
needs "hol/admission.ml";;

let l4_nat_literal_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let count = ref 0 in
  let test label ok =
    if not ok then failwith("natural literal regression: "^label);
    incr count; print_endline("literal check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} | Error {kind=Resource;_} -> test label true
    | Error _ -> failwith(label^": malformed-input classification for a well-formed test")
    | Ok _ -> failwith("accepted: "^label) in
  let name s = Str(Anonymous,s) in
  let nat = name "Nat" in
  let zero = Str(nat,"zero") and succ = Str(nat,"succ") in
  let nt = Const(nat,[]) and z = Const(zero,[]) in
  let s e = App(Const(succ,[]),e) in
  let level = Succ Zero in
  let pi a b = Pi(Anonymous,a,b) and lam a b = Lam(Anonymous,a,b) in
  let stmt env g a b ty = node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr a;quote_expr b;quote_expr ty] in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let chk label env g e ty =
    assert_th label (stmt env g e e ty) (get label (Env.check env g e ty)) in
  let eq label env g e e' ty =
    assert_th label (stmt env g e e' ty) (get label (Env.convert env g e e' ty)) in
  let admitted label before b =
    let after,h = get label (Env.admit_inductive before b) in
    assert_th label (node "l4_evalid" [Env.quote_policy after;Env.quote_env after]) h; after in
  let ordinary label before d =
    let after,h = get label (Env.admit before d) in
    assert_th label (node "l4_evalid" [Env.quote_policy after;Env.quote_env after]) h; after in
  let block i cs =
    let b={Env.inductive_name=i;inductive_level=level;constructors=cs;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  decline "literal without Nat" (Env.infer Env.empty [] (Natlit "0"));
  let env=admitted "canonical Nat" Env.empty (block nat [zero,[];succ,[Env.Recursive]]) in
  chk "zero literal" env [] (Natlit "0") nt;
  chk "positive literal" env [] (Natlit "7") nt;
  chk "literal in context" env [nt] (Natlit "7") nt;
  let huge="12345678901234567890123456789012345678901234567890" in
  let predecessor="12345678901234567890123456789012345678901234567889" in
  chk "exact arbitrary precision literal" env [] (Natlit huge) nt;
  eq "zero constructor view" env [] (Natlit "0") z nt;
  eq "successor constructor view" env [] (Natlit "7") (s(Natlit "6")) nt;
  eq "huge single constructor step" env [] (Natlit huge) (s(Natlit predecessor)) nt;
  eq "reverse constructor view" env [] (s(Natlit "6")) (Natlit "7") nt;
  eq "two constructor steps" env [] (Natlit "2") (s(s z)) nt;
  eq "literal beta" env [] (App(lam nt (Bvar 0),Natlit "7")) (Natlit "7") nt;
  eq "literal zeta" env [] (Let(Anonymous,nt,Natlit "7",Bvar 0)) (Natlit "7") nt;
  decline "unequal literals" (Env.convert env [] (Natlit "2") (Natlit "3") nt);
  test "large unequal literals decline without unary expansion"
    (match Env.convert ~fuel:1000 env []
      (Natlit "115792089237316195423570985008687907853269984665640564039457584007913129639935")
      (Natlit "115792089237316195423570985008687907853269984665640564039457584007913129639934") nt with
     | Error {kind=Proof_failure;_} -> true | _ -> false);
  decline "literal is not a type" (Env.check env [] (Natlit "0") (Sort level));
  decline "zero is not successor" (Env.convert env [] (Natlit "0") (s z) nt);
  test "literal resource decline"
    (match Env.infer ~fuel:0 env [] (Natlit huge) with Error {kind=Resource;_} -> true | _ -> false);
  test "noncanonical literal classification"
    (match Env.infer env [] (Natlit "00") with Error {kind=Invalid_input;_} -> true | _ -> false);
  let recursor=Const(Str(nat,"rec"),[level]) in
  let copy n=Env.apps recursor [lam nt nt;Natlit "0";lam nt (lam nt (s(Bvar 0)));n] in
  eq "literal recursor zero" env [] (copy(Natlit "0")) (Natlit "0") nt;
  eq "literal recursor successor" env [] (copy(Natlit "2")) (Natlit "2") nt;
  let constant=name "LargeNat" and u=name "u" in
  let env=ordinary "literal definition" env
    {Env.kind=Env.Definition;name=constant;params=[u];typ=nt;value=Some(Natlit huge)} in
  eq "literal universe substitution and delta" env [] (Const(constant,[level])) (Natlit huge) nt;
  let opaque=name "OpaqueNat" in
  let env=ordinary "literal opaque body" env
    {Env.kind=Env.Opaque;name=opaque;params=[];typ=nt;value=Some(Natlit "7")} in
  decline "literal opaque body stays opaque" (Env.convert env [] (Const(opaque,[])) (Natlit "7") nt);
  let pred=name "NatFamily" in
  let env=ordinary "literal type family" env
    {Env.kind=Env.Definition;name=pred;params=[];typ=pi nt (Sort level);value=Some(lam nt nt)} in
  let box=name "LiteralField" and mk=name "LiteralFieldMk" in
  let field=App(Const(pred,[]),Natlit "0") in
  let env=admitted "literal inside generated signatures" env (block box [mk,[Env.Data field]]) in
  chk "literal constructor argument" env [] (App(Const(mk,[]),Natlit "2")) (Const(box,[]));
  let literal=quote_expr(Natlit huge) in
  let computations=[
    "HOL literal lift",node "l4_lift" [literal;number 9;number 3],literal;
    "HOL literal substitution",node "l4_subst" [literal;number 0;quote_expr nt],literal;
    "HOL literal universe substitution",node "l4_expr_lsubst"
      [literal;mk_list([quote_name u],`:l4_name`);mk_list([quote_level level],`:l4_level`)],literal;
    "HOL literal binder erasure",node "l4_anon" [literal],literal;
    "HOL literal nested traversal",node "l4_no_nested_aux" [literal],`T`;
    "HOL literal universe scope",node "l4_params_expr" [literal;`[]:l4_name list`],`T`] in
  List.iter (fun (label,tm,result) ->
    let h=REWRITE_CONV [l4_lift;l4_subst;l4_expr_lsubst;l4_anon;l4_no_nested_aux;l4_params_expr] tm in
    assert_th label (mk_eq(tm,result)) h) computations;
  decline "macro layer cannot certify literal typing"
    (Lean4hol_admit.check Lean4hol_admit.empty (Natlit "0") (Sort Zero));
  let native_rules=CONJUNCTS l4_edef_RULES in
  let literal_heads j =
    let _,body=strip_forall(concl(List.nth native_rules j)) in
    let _,args=strip_comb(snd(dest_imp body)) in
    let head e=fst(dest_const(fst(strip_comb e))) in
    head(List.nth args 2),head(List.nth args 3) in
  test "native rule indices preserved" (List.length native_rules=29 &&
    List.map literal_heads [16;17;18]=
      ["L4NatLit","L4NatLit";"L4NatLit","L4Const";"L4NatLit","L4App"]);
  test "no new HOL axioms" (axioms()=l4_nat_literal_axioms_before);
  print_endline("HOL_NAT_LITERAL_TESTS_PASSED "^string_of_int !count);;

l4_nat_literal_tests ();;
