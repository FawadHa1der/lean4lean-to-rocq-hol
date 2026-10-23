let text_axioms_before = axioms();;
needs "hol/text_validation.ml";;

let text_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Text = Lean4hol_text in
  let count = ref 0 in
  let test label p = if not p then failwith("text primitive: "^label) else incr count in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let n s = Str(Anonymous,s) in
  let nt = Const(n "Nat",[]) and char = Const(n "Char",[]) and text = Const(n "String",[]) in
  let one = Succ Zero and u = n "u" in
  let pi a b = Pi(Anonymous,a,b) and lam a b = Lam(Anonymous,a,b) in
  let raw env d b = node "l4_text_definition_contract"
    [node "l4_edef" [Env.quote_env env];quote_name d.Env.name;
     mk_list(List.map quote_name d.Env.params,`:l4_name`);quote_expr d.Env.typ;quote_expr b] in
  let definition ?(params=[]) name typ body =
    {Env.kind=Env.Definition;name;params;typ;value=Some body} in
  let expected env d b = node "l4_text_definition_contract"
    [node "l4_checked" [Env.quote_policy env;Env.quote_env env];quote_name d.Env.name;
     mk_list(List.map quote_name d.Env.params,`:l4_name`);quote_expr d.Env.typ;quote_expr b] in
  let cert label env d =
    let c = get label (Text.check_definition env d) in
    let b = match d.Env.value with Some b -> b | None -> failwith "test body" in
    let h = Text.theorem c and r = Text.raw_theorem c in
    test (label^" retained input") (Text.declaration c=d);
    test (label^" exact checked") (hyp h=[] && frees(concl h)=[] && aconv(concl h)(expected env d b));
    test (label^" exact raw") (hyp r=[] && frees(concl r)=[] && aconv(concl r)(raw env d b));
    c in
  let decline label env d = match Text.check_definition env d with
    | Error {kind=(Unsupported|Proof_failure);_} -> test label true
    | Error e -> failwith(label^": unexpected classification: "^e.message)
    | Ok _ -> failwith(label^": incorrectly certified") in
  let install env d = let env,h = get "install" (Env.admit env d) in
    test "ordinary input certificate" (hyp h=[] && frees(concl h)=[] &&
      aconv(concl h)(node "l4_evalid"[Env.quote_policy env;Env.quote_env env])); env in
  let nat_block = {Env.inductive_name=n "Nat";inductive_level=one;
    constructors=[Str(n "Nat","zero"),[];Str(n "Nat","succ"),[Env.Recursive]];claims=[]} in
  let nat_block = {nat_block with Env.claims=Env.generate {remaining=100000} nat_block} in
  let nat env = fst(get "canonical Nat"(Env.admit_inductive env nat_block)) in
  let char_decl = definition (Str(n "Char","ofNat")) (pi nt char) (lam nt(Bvar 0)) in
  decline "no Nat or Char" Env.empty char_decl;
  let env = nat Env.empty in
  decline "missing Char" env char_decl;
  let env = install env (definition (n "Char") (Sort one) nt) in
  ignore(cert "identity Char.ofNat" env char_decl);
  ignore(cert "arbitrary well-typed Char.ofNat body is allowed by upstream interface" env
    {char_decl with Env.value=Some(lam nt(Natlit "0"))});
  ignore(cert "beta wrapped Char.ofNat" env
    {char_decl with Env.value=Some(App(lam(pi nt char)(Bvar 0),lam nt(Bvar 0)))});
  List.iter (fun (label,d) -> decline label env d)
    ["wrong Char header",{char_decl with Env.typ=pi nt(Sort Zero)};
     "wrong Char body",{char_decl with Env.value=Some(Sort Zero)};
     "extra universe parameter",{char_decl with Env.params=[u]};
     "dotted single name",{char_decl with Env.name=n "Char.ofNat"};
     "not a text name",{char_decl with Env.name=n "Other"};
     "theorem kind",{char_decl with Env.kind=Env.Theorem};
     "opaque kind",{char_decl with Env.kind=Env.Opaque};
     "axiom kind",{char_decl with Env.kind=Env.Axiom}];
  test "missing body malformed" (match Text.check_definition env {char_decl with Env.value=None} with
    | Error {kind=Invalid_input;_}->true|_->false);
  test "negative variable malformed" (match Text.check_definition env {char_decl with Env.value=Some(Bvar(-1))} with
    | Error {kind=Invalid_input;_}->true|_->false);
  test "zero fuel resource" (match Text.check_definition ~fuel:0 env char_decl with
    | Error {kind=Resource;_}->true|_->false);
  let env = install env (definition (n "String") (Sort one) nt) in
  let at = Sort(Succ(Param u)) in
  let list e = App(Const(n "List",[Param u]),e) in
  let env = install env (definition ~params:[u] (n "List") (pi at(Sort one)) (lam at nt)) in
  let lc = App(Const(n "List",[Zero]),char) in
  let string_decl = definition (Str(n "String","ofList")) (pi lc text) (lam lc(Natlit "0")) in
  decline "missing List.nil" env string_decl;
  let bad_nil = install env (definition (Str(n "List","nil")) nt (Natlit "0")) in
  decline "wrong List.nil interface despite admitted dependency" bad_nil string_decl;
  let env = install env (definition ~params:[u] (Str(n "List","nil"))
    (pi at(list(Bvar 0))) (lam at(Natlit "0"))) in
  decline "missing List.cons" env string_decl;
  let bad_cons = install env (definition (Str(n "List","cons")) nt (Natlit "0")) in
  decline "wrong List.cons interface despite admitted dependency" bad_cons string_decl;
  let env = install env (definition ~params:[u] (Str(n "List","cons"))
    (pi at(pi(Bvar 0)(pi(list(Bvar 1))(list(Bvar 2)))))
    (lam at(lam(Bvar 0)(lam(list(Bvar 1))(Bvar 0))))) in
  ignore(cert "String.ofList" env string_decl);
  ignore(cert "arbitrary well-typed String.ofList body is allowed by upstream interface" env
    {string_decl with Env.value=Some(lam lc(Bvar 0))});
  ignore(cert "binder display name is irrelevant" env
    {string_decl with Env.typ=Pi(n "characters",lc,text)});
  decline "wrong String.ofList header" env {string_decl with Env.typ=pi nt(Sort Zero)};
  decline "wrong String.ofList body" env {string_decl with Env.value=Some(Sort Zero)};
  let high = Sort(Succ one) in
  let seed = n "charSeed" in
  let perms = [{Env.axiom_name=n "Char";axiom_params=[];axiom_type=high};
    {Env.axiom_name=seed;axiom_params=[];axiom_type=pi nt char}] in
  let high_env = nat(get "higher universe policy"(Env.with_axioms perms)) in
  let high_env = install high_env {Env.kind=Env.Axiom;name=n "Char";params=[];typ=high;value=None} in
  let high_env = install high_env {Env.kind=Env.Axiom;name=seed;params=[];typ=pi nt char;value=None} in
  ignore(cert "Char type universe is not hardcoded" high_env {char_decl with Env.value=Some(Const(seed,[]))});
  let raw_char = Text.raw_theorem(get "admission Char factory" (Text.check_definition env char_decl)) in
  let admit label env d h =
    let result,proof = get label (Env.admit_text_primitive env d h) in
    test (label^" exact environment certificate")
      (hyp proof=[] && frees(concl proof)=[] &&
       aconv(concl proof)(node "l4_evalid"[Env.quote_policy result;Env.quote_env result]));
    test (label^" exact source retained") (Env.declarations result=d::Env.declarations env);
    test (label^" unchanged permissions") (Env.permissions result=Env.permissions env);
    result in
  let no_admit label env d h = match Env.admit_text_primitive env d h with
    | Error {kind=(Unsupported|Proof_failure);_} -> test label true
    | Error e -> failwith(label^": unexpected admission classification: "^e.message)
    | Ok _ -> failwith(label^": incorrectly admitted") in
  let after_char = admit "Char.ofNat admission" env char_decl raw_char in
  no_admit "old certificate in extended environment" after_char char_decl raw_char;
  let duplicate = Text.raw_theorem(get "duplicate factory"(Text.check_definition after_char char_decl)) in
  no_admit "duplicate with matching new certificate" after_char char_decl duplicate;
  no_admit "wrong body" env {char_decl with Env.value=Some(lam nt(Natlit "0"))} raw_char;
  no_admit "wrong name" env {char_decl with Env.name=n "ordinary"} raw_char;
  no_admit "wrong kind" env {char_decl with Env.kind=Env.Opaque} raw_char;
  no_admit "wrong signature" env {char_decl with Env.typ=Sort one} raw_char;
  no_admit "wrong params" env {char_decl with Env.params=[u]} raw_char;
  no_admit "nonempty hypotheses" env char_decl (ADD_ASSUM `T` raw_char);
  no_admit "unrelated theorem" env char_decl TRUTH;
  no_admit "checked is not raw" env char_decl
    (Text.theorem(get "checked certificate" (Text.check_definition env char_decl)));
  test "zero admission fuel" (match Env.admit_text_primitive ~fuel:0 env char_decl raw_char with
    | Error {kind=Resource;_}->true|_->false);
  test "ordinary protected admission remains closed" (match Env.admit env char_decl with
    | Error {kind=(Unsupported|Proof_failure);_}->true|_->false);
  let string_certificate = get "String factory after Char" (Text.check_definition after_char string_decl) in
  let after_text = admit "String.ofList admission" after_char string_decl (Text.raw_theorem string_certificate) in
  let converted = get "admitted text body is transparent" (Env.convert after_text []
    (App(Const(Str(n "String","ofList"),[]),Natlit "7")) (Natlit "0") nt) in
  test "admitted text computation closed" (hyp converted=[] && frees(concl converted)=[]);
  let permissions = MATCH_MP (SPEC (Env.quote_policy after_text) l4_evalid_permissions) (Env.certificate after_text) in
  test "axiom-policy invariant remains proved" (hyp permissions=[] && frees(concl permissions)=[]);
  test "no new HOL axioms" (axioms()=text_axioms_before);
  Printf.printf "HOL_TEXT_PRIMITIVE_TESTS_PASSED %d\n%!" !count;;
text_tests();;
