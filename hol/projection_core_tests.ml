(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_projection_core_axioms_before = axioms ();;
needs "hol/core.ml";;

let l4_projection_core_tests () =
  let open Lean4hol in
  let count = ref 0 in
  let test label ok =
    if not ok then failwith ("projection core regression: " ^ label);
    incr count in
  let fresh () = {remaining=100000} in
  let owner = Str(Str(Anonymous,"Example"),"Pair") in
  let u = Str(Anonymous,"u") in
  let p = Sort Zero in
  let seeds = [Bvar 0;Bvar 1;Bvar 2;p;Sort(Param u);
    Const(owner,[Param u]);Natlit "12345678901234567890"] in
  let expressions = List.flatten(List.map(fun e ->
    [Proj(owner,0,e);Proj(owner,2,Proj(owner,1,e));
     Lam(Anonymous,p,Proj(owner,1,e));
     Pi(Anonymous,Proj(owner,0,e),Proj(owner,1,App(e,Bvar 0)));
     Let(Anonymous,p,e,Proj(owner,1,Lam(Anonymous,p,e)))]) seeds) in
  let certificate label left right =
    let expected = mk_eq(left,quote_expr right) in
    let th = prove(expected,
      CONV_TAC (TOP_DEPTH_CONV (CHANGED_CONV compute_object))) in
    test (label ^ " closed") (hyp th=[] && frees(concl th)=[]);
    test (label ^ " exact") (aconv (concl th) expected) in
  List.iter (fun e ->
    List.iter (fun (d,k) ->
      certificate "lift agrees with HOL recursion"
        (node "l4_lift" [quote_expr e;number d;number k])
        (lift (fresh()) d k e)) [0,0;1,0;2,1;3,2];
    List.iter (fun (k,s) ->
      certificate "substitution agrees with HOL recursion"
        (node "l4_subst" [quote_expr e;number k;quote_expr s])
        (subst (fresh()) k s e))
      [0,p;0,Bvar 0;1,Bvar 1;2,Proj(owner,0,Bvar 0)]) expressions;
  test "quoted projection retains all fields"
    (aconv (quote_expr(Proj(owner,2,Bvar 1)))
      (node "L4Proj" [quote_name owner;number 2;quote_expr(Bvar 1)]));
  test "lift crosses projection and protects lambda variable"
    (lift (fresh()) 2 0 (Lam(Anonymous,p,Proj(owner,0,App(Bvar 0,Bvar 1)))) =
      Lam(Anonymous,p,Proj(owner,0,App(Bvar 0,Bvar 3))));
  test "substitution lifts replacement through binder"
    (subst (fresh()) 0 (Bvar 0) (Lam(Anonymous,p,Proj(owner,0,Bvar 1))) =
      Lam(Anonymous,p,Proj(owner,0,Bvar 1)));
  test "universe substitution descends through projection"
    (instantiate_levels (fresh()) [u] [Succ Zero]
      (Proj(owner,0,Const(owner,[Param u]))) =
        Proj(owner,0,Const(owner,[Succ Zero])));
  test "negative projection index rejected"
    (match infer [] (Proj(owner,-1,p)) with Error {kind=Invalid_input;_} -> true | _ -> false);
  test "pure engine cannot invent structure metadata"
    (match infer [] (Proj(owner,0,p)) with Error {kind=Unsupported;_} -> true | _ -> false);
  test "projection validation consumes fuel"
    (match infer ~fuel:0 [] (Proj(owner,0,p)) with Error {kind=Resource;_} -> true | _ -> false);
  test "projection major syntax is validated"
    (match infer [] (Proj(owner,0,Bvar(-1))) with Error {kind=Invalid_input;_} -> true | _ -> false);
  test "no new HOL axioms" (axioms()=l4_projection_core_axioms_before);
  print_endline("HOL_PROJECTION_CORE_TESTS_PASSED " ^ string_of_int !count);;

l4_projection_core_tests ();;
