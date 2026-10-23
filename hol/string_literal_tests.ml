let string_literal_axioms_before = axioms();;
needs "hol/text_validation.ml";;

let string_literal_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Text=Lean4hol_text in
  let count=ref 0 in
  let test label p=if not p then failwith("string literal: "^label) else incr count in
  let get label=function Ok x->x|Error e->failwith(label^": "^e.message) in
  let n s=Str(Anonymous,s) in
  let child n s=Str(n,s) in
  let pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) in
  let one=Succ Zero and u=n "u" in
  let nat=Const(n "Nat",[]) and char=Const(n "Char",[]) and text=Const(n "String",[]) in
  let exact label env g a b ty h = test label
    (hyp h=[] && frees(concl h)=[] && aconv(concl h)
      (node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
        quote_expr a;quote_expr b;quote_expr ty])) in
  let chk label env g e ty = exact label env g e e ty (get label(Env.check env g e ty)) in
  let eq label env g a b ty = exact label env g a b ty (get label(Env.convert env g a b ty)) in
  let decline label = function
    | Error {kind=(Unsupported|Proof_failure);_}->test label true
    | Error e->failwith(label^": wrong decline classification: "^e.message)
    | Ok _->failwith(label^": unexpectedly accepted") in
  let def ?(params=[]) name typ value = {Env.kind=Env.Definition;name;params;typ;value=Some value} in
  let install env d=fst(get "install ordinary"(Env.admit env d)) in
  let primitive env d =
    let c=get "text factory" (Text.check_definition env d) in
    fst(get "text admission"(Env.admit_text_primitive env d(Text.raw_theorem c))) in
  let block owner constructors =
    let b={Env.inductive_name=owner;inductive_level=one;constructors;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  let nat_block=block(n "Nat") [child(n "Nat")"zero",[];child(n "Nat")"succ",[Env.Recursive]] in
  decline "empty environment cannot type literal" (Env.infer Env.empty [] (Strlit ""));
  let env=fst(get "Nat admission"(Env.admit_inductive Env.empty nat_block)) in
  let env=install env(def(n "Char")(Sort one)nat) in
  let string_block=block(n "String")[child(n "String")"mk",[Env.Data nat]] in
  let env=fst(get "String admission"(Env.admit_inductive env string_block)) in
  let at=Sort(Succ(Param u)) in
  let list e=App(Const(n "List",[Param u]),e) in
  let env=install env(def ~params:[u](n "List")(pi at(Sort one))(lam at nat)) in
  let env=install env(def ~params:[u](child(n "List")"nil")
    (pi at(list(Bvar 0)))(lam at(Natlit "0"))) in
  let env=install env(def ~params:[u](child(n "List")"cons")
    (pi at(pi(Bvar 0)(pi(list(Bvar 1))(list(Bvar 2)))))
    (lam at(lam(Bvar 0)(lam(list(Bvar 1))(Bvar 0))))) in
  decline "mere String type is insufficient" (Env.infer env [] (Strlit "abc"));
  let char_decl=def(child(n "Char")"ofNat")(pi nat char)(lam nat(Natlit "0")) in
  let env=primitive env char_decl in
  decline "missing String.ofList" (Env.infer env [] (Strlit "abc"));
  let lc=App(Const(n "List",[Zero]),char) in
  let mk=Const(child(n "String")"mk",[]) in
  let string_decl=def(child(n "String")"ofList")(pi lc text)(lam lc(App(mk,Natlit "7"))) in
  let env=primitive env string_decl in
  let samples=["";"\000";"abc";"\194\128";"\224\160\128";
    "\237\159\191";"\238\128\128";"\240\144\128\128";"\244\143\191\191"] in
  List.iter(fun s->
    chk "literal exact type" env [] (Strlit s) text;
    chk "literal in context" env [nat] (Strlit s) text;
    eq "literal reflexivity" env [] (Strlit s)(Strlit s)text;
    let r,ty,h=get "literal stays neutral"(Env.normalize env [] (Strlit s)) in
    test "ordinary WHNF does not eagerly expand" (r=Strlit s && ty=text);
    exact "neutral WHNF certificate" env [] (Strlit s)(Strlit s)text h) samples;
  List.iter(fun(a,b)->decline "distinct literals despite constant constructor bodies"
    (Env.convert env [] (Strlit a)(Strlit b)text))
    ["","\000";"a","b";"ab","ba";"\195\169","e\204\129"];
  decline "literal is not Nat" (Env.check env [] (Strlit "")nat);
  decline "literal is not a type" (Env.check env [] (Strlit "")(Sort one));
  decline "bad projection index" (Env.infer env [] (Proj(n "String",1,Strlit "")));
  decline "wrong projection owner" (Env.infer env [] (Proj(n "Nat",0,Strlit "")));
  List.iter(fun s->
    eq "constructor expansion drives projection" env [] (Proj(n "String",0,Strlit s))(Natlit "7")nat)
    ["";"a";"\240\144\128\128"];
  let recursor=Const(child(n "String")"rec",[one]) in
  let fold major=Env.apps recursor [lam text nat;lam nat(Bvar 0);major] in
  eq "constructor expansion drives recursor" env [] (fold(Strlit ""))(Natlit "7")nat;
  eq "unicode constructor expansion drives recursor" env [] (fold(Strlit "\194\128"))(Natlit "7")nat;
  eq "zeta before string major" env []
    (fold(Let(Anonymous,text,Strlit "a",Bvar 0)))(Natlit "7")nat;
  eq "beta wrapped literal" env [] (App(lam text(Bvar 0),Strlit "abc"))(Strlit "abc")text;
  let env=install env(def ~params:[u](n "literalAlias")text(Strlit "abc")) in
  eq "delta and universe substitution retain literal" env []
    (Const(n "literalAlias",[one]))(Strlit "abc")text;
  let opaque={Env.kind=Env.Opaque;name=n "hiddenLiteral";params=[];typ=text;value=Some(Strlit "abc")} in
  let env=install env opaque in
  decline "opaque literal remains opaque" (Env.convert env [] (Const(n "hiddenLiteral",[]))(Strlit "abc")text);
  test "zero fuel is resource" (match Env.infer ~fuel:0 env [] (Strlit "") with
    |Error {kind=Resource;_}->true|_->false);
  List.iter(fun s->test "malformed UTF-8 remains invalid" (match Env.infer env [] (Strlit s) with
    |Error {kind=Invalid_input;_}->true|_->false)) ["\128";"\192\128";"\237\160\128";"\244\144\128\128"];
  test "native rule count" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "environment rule count" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=string_literal_axioms_before);
  Printf.printf "HOL_STRING_LITERAL_TESTS_PASSED %d\n%!" !count;;
string_literal_tests();;
