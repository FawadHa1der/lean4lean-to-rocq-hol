(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/admission.ml";;

let l4_admission_tests () =
  let open Lean4hol in
  let module Adm = Lean4hol_admit in
  let n = Anonymous in
  let name s = Str(n,s) in
  let prop = Sort Zero and typ = Sort(Succ Zero) in
  let count = ref 0 in
  let test label b = if not b then failwith("admission regression: "^label); incr count in
  let admission env d = match Adm.admit env d with
    | Error e -> failwith("admission: " ^ e.message)
    | Ok(env',th) ->
      test "admission hypotheses" (hyp th=[]);
      test "admission conclusion" (aconv (concl th) (node "l4_admitted" [Adm.quote_env env']));
      env' in
  let check env e a = match Adm.check env e a with
    | Error e -> failwith("environment check: " ^ e.message)
    | Ok th ->
      test "check hypotheses" (hyp th=[]);
      test "check conclusion" (aconv (concl th)
        (node "l4_env_has_type" [Adm.quote_env env;quote_expr e;quote_expr a])) in
  let decline label = function
    | Error _ -> test label true
    | Ok _ -> failwith("admission incorrectly accepted: "^label) in
  let d = {Adm.kind=Adm.Definition;name=name "P";params=[];typ;value=prop} in
  let env = admission Adm.empty d in
  check env (Const(name "P",[])) typ;
  let p = Const(name "P",[]) in
  let identity = {Adm.kind=Adm.Definition;name=name "idP";params=[];
    typ=Pi(n,p,p);value=Lam(n,p,Bvar 0)} in
  let env = admission env identity in
  check env (Const(name "idP",[])) (Pi(n,prop,prop));
  let u = name "u" in
  let polymorphic = {Adm.kind=Adm.Definition;name=name "id";params=[u];
    typ=Pi(n,Sort(Param u),Pi(n,Bvar 0,Bvar 1));
    value=Lam(n,Sort(Param u),Lam(n,Bvar 0,Bvar 0))} in
  let env = admission env polymorphic in
  check env (Const(name "id",[Succ Zero])) (Pi(n,typ,Pi(n,Bvar 0,Bvar 1)));
  let theorem = {Adm.kind=Adm.Theorem;name=name "idProof";params=[];
    typ=Pi(n,prop,Pi(n,Bvar 0,Bvar 1));value=Const(name "id",[Zero])} in
  let env = admission env theorem in
  check env (Const(name "idProof",[])) theorem.Adm.typ;
  check env (App(App(Const(name "idProof",[]),theorem.Adm.typ),Const(name "idProof",[]))) theorem.Adm.typ;
  decline "duplicate" (Adm.admit env d);
  decline "undefined" (Adm.check env (Const(name "absent",[])) prop);
  decline "wrong level count" (Adm.check env (Const(name "id",[])) polymorphic.Adm.typ);
  decline "bad body" (Adm.admit env {d with Adm.name=name "bad";value=typ});
  decline "undeclared parameter" (Adm.admit env {polymorphic with Adm.name=name "badU";params=[]});
  decline "duplicate parameter" (Adm.admit env {polymorphic with Adm.name=name "dupU";params=[u;u]});
  decline "self reference" (Adm.admit env {d with Adm.name=name "self";value=Const(name "self",[])});
  decline "resource" (Adm.admit ~fuel:0 env d);
  decline "theorem requires proposition" (Adm.admit env
    {d with Adm.kind=Adm.Theorem;name=name "badTheorem"});
  decline "universe mismatch" (Adm.check env (Const(name "id",[Zero]))
    (Pi(n,typ,Pi(n,Bvar 0,Bvar 1))));
  let env = admission env {d with Adm.name=Str(n,"a.b")} in
  let env = admission env {d with Adm.name=Str(Str(n,"a"),"b")} in
  let env = admission env {d with Adm.name=Num(n,"123456789012345678901234567890")} in
  check env (Const(Num(n,"123456789012345678901234567890"),[])) typ;
  test "persistent environment after declines" (List.length(Adm.declarations env)=7);
  test "no new axioms" (axioms () = l4_axioms_before);
  print_endline("HOL_ADMISSION_TESTS_PASSED " ^ string_of_int !count);;

l4_admission_tests ();;
