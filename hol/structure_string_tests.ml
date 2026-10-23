(* Private integration regression: no verdict oracle or new object rule. *)
needs "hol/text_validation.ml";;

let l4_structure_string_exclusion_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Text=Lean4hol_text in
  let before=axioms() and count=ref 0 in
  let test label b=if not b then failwith("structure/string: "^label);
    incr count; print_endline("structure/string check "^string_of_int !count^": "^label) in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let n s=Str(Anonymous,s) and one=Succ Zero in
  let child n s=Str(n,s) in
  let pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) in
  let nat=Const(n "Nat",[]) and char=Const(n "Char",[]) and text=Const(n "String",[]) in
  let exact label env input output ty h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv(concl h)
      (node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context [];
        quote_expr input;quote_expr output;quote_expr ty])) in
  let normalize label env input expected =
    let ty,_=get (label^" infer") (Env.infer env [] input) in
    let output,actual,h=get label (Env.normalize env [] input) in
    test (label^" result") (output=expected && actual=ty);
    exact label env input expected ty h in
  let def ?(params=[]) name typ value=
    {Env.kind=Env.Definition;name;params;typ;value=Some value} in
  let install env d=fst(get "ordinary declaration" (Env.admit env d)) in
  let primitive env d=
    let c=get "text interface factory" (Text.check_definition env d) in
    fst(get "text interface admission" (Env.admit_text_primitive env d (Text.raw_theorem c))) in
  let block owner constructors=
    let b={Env.inductive_name=owner;inductive_level=one;constructors;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  let env=fst(get "Nat" (Env.admit_inductive Env.empty
    (block (n "Nat") [child(n "Nat")"zero",[];child(n "Nat")"succ",[Env.Recursive]]))) in
  let env=install env (def(n "Char")(Sort one)nat) in
  let env=fst(get "String structure" (Env.admit_inductive env
    (block(n "String")[child(n "String")"mk",[Env.Data nat]]))) in
  let u=n "u" in
  let at=Sort(Succ(Param u)) and list a=App(Const(n "List",[Param u]),a) in
  let env=install env (def ~params:[u](n "List")(pi at(Sort one))(lam at nat)) in
  let env=install env (def ~params:[u](child(n "List")"nil")
    (pi at(list(Bvar 0)))(lam at(Natlit "0"))) in
  let env=install env (def ~params:[u](child(n "List")"cons")
    (pi at(pi(Bvar 0)(pi(list(Bvar 1))(list(Bvar 2)))))
    (lam at(lam(Bvar 0)(lam(list(Bvar 1))(Bvar 0))))) in
  let env=primitive env (def(child(n "Char")"ofNat")(pi nat char)(lam nat(Natlit "0"))) in
  let lc=App(Const(n "List",[Zero]),char) and mk=Const(child(n "String")"mk",[]) in
  let recursor=Const(child(n "String")"rec",[one]) in
  let fold major=Env.apps recursor [lam text nat;lam nat(Bvar 0);major] in
  let hidden=n "neutralStringMajor" in
  let env=install env {Env.kind=Env.Opaque;name=hidden;params=[];
    typ=text;value=Some(App(mk,Natlit "7"))} in
  let neutral=Const(hidden,[]) in
  let neutral_env=primitive env (def(child(n "String")"ofList")
    (pi lc text)(lam lc neutral)) in
  let projected=Proj(n "String",0,neutral) in
  normalize "ordinary nonliteral structure expands" neutral_env (fold neutral) projected;
  normalize "literal expansion stays in literal branch" neutral_env
    (fold(Strlit "abc")) (fold neutral);
  normalize "beta exposes literal before branch selection" neutral_env
    (fold(App(lam text(Bvar 0),Strlit "abc"))) (fold neutral);
  normalize "zeta exposes literal before branch selection" neutral_env
    (fold(Let(Anonymous,text,Strlit "abc",Bvar 0))) (fold neutral);
  let alias=n "stringMajorAlias" in
  let alias_env=install neutral_env (def alias text (Strlit "abc")) in
  normalize "delta exposes literal before branch selection" alias_env
    (fold(Const(alias,[]))) (fold neutral);
  normalize "ordinary literal WHNF remains neutral" neutral_env (Strlit "abc") (Strlit "abc");
  let ctor_env=primitive env (def(child(n "String")"ofList")
    (pi lc text)(lam lc(App(mk,Natlit "7")))) in
  let input=fold(Strlit "abc") in
  let h=get "constructor literal iota" (Env.convert ctor_env [] input (Natlit "7") nat) in
  exact "constructor literal still reduces" ctor_env input (Natlit "7") nat h;
  test "resource remains classified" (match Env.normalize ~fuel:0 neutral_env [] input with
    | Error {kind=Resource;_}->true | _->false);
  test "indexed mutual clauses appended after literal exclusion rules" (List.length(CONJUNCTS l4_edef_RULES)=29 &&
    List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=before);
  print_endline("HOL_STRUCTURE_STRING_EXCLUSION_TESTS_PASSED "^string_of_int !count);;

l4_structure_string_exclusion_tests ();;
