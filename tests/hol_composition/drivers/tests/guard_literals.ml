needs "tests/common.ml";;
needs "hol/text_validation.ml";;
let run_guard_literals () =
  let open Lean4hol in
  let open Early_test in
  let module Env=Lean4hol_env in
  let module Text=Lean4hol_text in
  let name s=Str(Anonymous,s) in
  let child s t=Str(name s,t) in
  let nat=Const(name "Nat",[]) and char=Const(name "Char",[]) in
  let text=Const(name "String",[]) and one=Succ Zero in
  let pi a b=Pi(n,a,b) and lam a b=Lam(n,a,b) in
  let def ?(params=[]) name typ value={Env.kind=Env.Definition;name;params;typ;value=Some value} in
  let install env d=fst(get "ordinary admission" (Env.admit env d)) in
  let primitive env d=
    let certificate=get "typed text contract" (Text.check_definition env d) in
    fst(get "typed text admission" (Env.admit_text_primitive env d(Text.raw_theorem certificate))) in
  let block={Env.inductive_name=name "Nat";inductive_level=one;
    constructors=[child "Nat" "zero",[];child "Nat" "succ",[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env=fst(get "certified Nat admission" (Env.admit_inductive Env.empty block)) in
  let env=install env(def(name "Char")(Sort one)nat) in
  let env=install env(def(name "String")prop p) in
  let u=name "u" in
  let at=Sort(Succ(Param u)) in
  let list e=App(Const(name "List",[Param u]),e) in
  let env=install env(def ~params:[u](name "List")(pi at(Sort one))(lam at nat)) in
  let env=install env(def ~params:[u](child "List" "nil")
    (pi at(list(Bvar 0)))(lam at(Natlit "0"))) in
  let env=install env(def ~params:[u](child "List" "cons")
    (pi at(pi(Bvar 0)(pi(list(Bvar 1))(list(Bvar 2)))))
    (lam at(lam(Bvar 0)(lam(list(Bvar 1))(Bvar 0))))) in
  let env=primitive env(def(child "Char" "ofNat")(pi nat char)(lam nat(Natlit "0"))) in
  let list_char=App(Const(name "List",[Zero]),char) in
  let env=primitive env(def(child "String" "ofList")(pi list_char text)(lam list_char hp)) in
  checked env [] text text prop (get "String genuinely has Prop type" (Env.check env [] text prop));
  let strings=ref 0 and successes=ref 0 and skips=ref 0 in
  test_schedule_expr := (fun tag left _ ->
    if tag="early.enter" && left=Strlit "x" then incr strings);
  test_schedule_mark := (fun tag -> if tag="early.success" then incr successes
    else if tag="skip.successor" then incr skips);
  let result=Env.convert env [] (Strlit "x") hp text in
  test_schedule_expr := (fun _ _ _ -> ());
  test_schedule_mark := (fun _ -> ());
  checked env [] (Strlit "x") hp text (get "Strlit remains eligible as proof" result);
  test "Strlit reached optional branch" (!strings>0);
  test "actual typed early success exists" (!successes>0);
  let successor_skips=ref 0 in
  test_schedule_mark := (fun tag -> if tag="skip.successor" then incr successor_skips);
  let result=Env.convert env [] (Natlit "0") (Const(child "Nat" "zero",[])) nat in
  test_schedule_mark := (fun _ -> ());
  checked env [] (Natlit "0") (Const(child "Nat" "zero",[])) nat (get "Nat literal ordinary fallback" result);
  test "Nat uses certified successor-level scheduling" (!successor_skips>0);
  refusal "missing text interface still refused" (Env.convert Env.empty [] (Strlit "x") hp p);
  test "malformed string still Invalid" (match Env.infer env [] (Strlit "\128") with
    | Error {kind=Invalid_input;_} -> true | _ -> false);
  test "string zero fuel remains Resource" (match Env.convert ~fuel:0 env [] (Strlit "x") hp text with
    | Error {kind=Resource;_} -> true | _ -> false);
  Printf.printf "GUARD_LITERAL string_early=%d successes=%d nat_successor_skips=%d\n%!"
    !strings !successes !successor_skips;
  finish "guards-literals";;
