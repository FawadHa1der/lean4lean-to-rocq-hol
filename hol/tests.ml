(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_axioms_before = axioms ();;
needs "hol/core.ml";;

let l4_test_count = ref 0;;
let l4_test label b =
  if not b then failwith ("HOL core regression: " ^ label);
  incr l4_test_count;;

let l4_tests () =
  let open Lean4hol in
  let n = Anonymous in
  let prop = Sort Zero in
  let typ = Sort (Succ Zero) in
  let id = Lam(n,prop,Bvar 0) in
  let idty = Pi(n,prop,prop) in
  let expect label g e a =
    match check g e a with
    | Error err -> failwith (label ^ ": " ^ err.message)
    | Ok th ->
      l4_test (label ^ " closed") (hyp th = []);
      l4_test (label ^ " conclusion")
        (aconv (concl th) (list_mk_comb (`l4_defeq`,
          [quote_context g;quote_expr e;quote_expr e;quote_expr a]))) in
  let equal label g a b ty =
    match convert g a b ty with
    | Error err -> failwith (label ^ ": " ^ err.message)
    | Ok th ->
      l4_test (label ^ " closed") (hyp th = []);
      l4_test (label ^ " conclusion")
        (aconv (concl th) (list_mk_comb (`l4_defeq`,
          [quote_context g;quote_expr a;quote_expr b;quote_expr ty]))) in
  let decline label r = match r with
    | Error _ -> l4_test label true
    | Ok _ -> failwith (label ^ ": incorrectly accepted") in
  expect "sort" [] prop typ;
  expect "identity" [] id idty;
  expect "dependent identity" []
    (Lam(n,typ,Lam(n,Bvar 0,Bvar 0)))
    (Pi(n,typ,Pi(n,Bvar 0,Bvar 1)));
  expect "dependent application" [prop] (App(id,Bvar 0)) prop;
  equal "beta" [prop] (App(id,Bvar 0)) (Bvar 0) prop;
  equal "zeta" [prop] (Let(n,prop,Bvar 0,Bvar 0)) (Bvar 0) prop;
  equal "binder alpha" [] id (Lam(Str(n,"x"),prop,Bvar 0)) idty;
  expect "imax zero" [] (Pi(n,prop,Bvar 0)) prop;
  expect "max universe" [] (Sort(Max(Zero,Succ Zero))) (Sort(Succ(Succ Zero)));
  let u = Param(Str(n,"u")) in
  equal "symbolic max" [] (Sort(Max(u,Zero))) (Sort u) (Sort(Succ u));
  equal "symbolic imax zero" [] (Sort(Imax(u,Zero))) prop typ;
  let v = Param(Num(Str(n,"universe"),"98765432109876543210")) in
  equal "max commutativity" [] (Sort(Max(u,v))) (Sort(Max(v,u))) (Sort(Succ(Max(u,v))));
  equal "zero imax symbolic" [] (Sort(Imax(Zero,u))) (Sort u) (Sort(Succ u));
  equal "imax self" [] (Sort(Imax(u,u))) (Sort u) (Sort(Succ u));
  equal "imax positive" [] (Sort(Imax(u,Succ v))) (Sort(Max(u,Succ v)))
    (Sort(Succ(Max(u,Succ v))));
  List.iter (fun (a,b) ->
    let expected=node "l4_level_equiv" [quote_level a;quote_level b] in
    List.iter (fun _ ->
      let h=level_proof {remaining=10000} a b in
      l4_test "cached level proof closed" (hyp h=[]);
      l4_test "cached level proof conclusion" (aconv(concl h)expected)) [0;1;2])
    [u,u;Max(u,v),Max(v,u);Imax(u,Zero),Zero];
  l4_test "cached level proof still consumes fuel"
    (try ignore(level_proof {remaining=0} (Max(u,v)) (Max(v,u))); false
     with Stop {kind=Resource;_} -> true | _ -> false);
  l4_test "nearby false universe equality is not cached"
    (try ignore(level_proof {remaining=10000} (Max(u,v)) (Succ(Max(v,u)))); false
     with Failure _ | Stop {kind=Proof_failure;_} -> true | _ -> false);
  equal "proof irrelevance" [Bvar 1;Bvar 0;prop] (Bvar 0) (Bvar 1) (Bvar 2);
  equal "function eta" [idty]
    (Lam(n,prop,App(Bvar 1,Bvar 0))) (Bvar 0) idty;
  equal "capture avoiding beta" [prop]
    (App(Lam(n,prop,Lam(n,prop,Bvar 1)),Bvar 0))
    (Lam(n,prop,Bvar 1)) idty;
  equal "beta under lambda" [] (Lam(n,prop,App(id,Bvar 0))) id idty;
  expect "beta in binder type" []
    (Lam(n,App(Lam(n,typ,Bvar 0),prop),Bvar 0)) idty;
  expect "dependent let" [] (Let(n,typ,prop,Lam(n,Bvar 0,Bvar 0))) idty;
  equal "dependent eta" [Pi(n,Bvar 0,prop);typ]
    (Lam(n,Bvar 1,App(Bvar 1,Bvar 0))) (Bvar 0) (Pi(n,Bvar 1,prop));
  equal "dependent beta application" [prop]
    (App(App(Lam(n,typ,Lam(n,Bvar 0,Bvar 0)),prop),Bvar 0)) (Bvar 0) prop;
  decline "sort not its own type" (check [] prop prop);
  decline "out of scope" (infer [] (Bvar 0));
  decline "bad domain" (infer [] (Lam(n,id,Bvar 0)));
  decline "bad argument" (infer [] (App(id,typ)));
  decline "ill typed let value" (infer [] (Let(n,prop,typ,Bvar 0)));
  decline "invalid context" (infer [Bvar 0] (Bvar 0));
  decline "type inhabitants not proof irrelevant"
    (convert [typ;typ] (Bvar 0) (Bvar 1) typ);
  decline "unknown constant" (infer [] (Const(Str(n,"Nat"),[])));
  decline "pure literal lacks Nat environment" (infer [] (Natlit "0"));
  l4_test "malformed literal rejected"
    (match infer [] (Natlit "01") with Error {kind=Invalid_input;_} -> true | _ -> false);
  l4_test "negative literal rejected"
    (match infer [] (Natlit "-1") with Error {kind=Invalid_input;_} -> true | _ -> false);
  l4_test "exact large literal quoted"
    (aconv (quote_expr(Natlit "123456789012345678901234567890"))
      (node "L4NatLit" [mk_numeral(num_of_string "123456789012345678901234567890")]));
  l4_test "literal lift is constant"
    (lift {remaining=10} 7 2 (Natlit "123") = Natlit "123");
  l4_test "literal substitution is constant"
    (subst {remaining=10} 0 prop (Natlit "123") = Natlit "123");
  l4_test "literal universe substitution is constant"
    (instantiate_levels {remaining=10} [n] [Zero] (Natlit "123") = Natlit "123");
  decline "resource" (check ~fuel:0 [] prop typ);
  decline "negative index" (infer [] (Bvar (-1)));
  decline "different universe parameters" (convert [] (Sort u) (Sort v) (Sort(Succ u)));
  l4_test "resource classification"
    (match check ~fuel:0 [] prop typ with Error {kind=Resource;_} -> true | _ -> false);
  l4_test "unsupported classification"
    (match infer [] (Const(n,[])) with Error {kind=Unsupported;_} -> true | _ -> false);
  l4_test "malformed name classification"
    (match infer [] (Sort(Param(Num(n,"01")))) with
     | Error {kind=Invalid_input;_} -> true | _ -> false);
  l4_test "structured names do not collide"
    (not (aconv (quote_name (Str(n,"a.b")))
                (quote_name (Str(Str(n,"a"),"b")))));
  l4_test "numeric names do not collide"
    (not (aconv (quote_name (Num(n,"12"))) (quote_name (Str(n,"12")))));
  l4_test "big numeric segment"
    (type_of (quote_name (Num(n,"123456789012345678901234567890"))) = `:l4_name`);
  l4_test "no new HOL axioms" (axioms () = l4_axioms_before);
  print_endline ("HOL_CORE_TESTS_PASSED " ^ string_of_int !l4_test_count);;

l4_tests ();;
needs "hol/admission_tests.ml";;
needs "hol/environment_tests.ml";;
needs "hol/inductive_tests.ml";;
