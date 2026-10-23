(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let string_quotient_axioms_before = axioms();;
needs "hol/text_validation.ml";;

let string_quotient_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Text=Lean4hol_text in
  let module Qmodel=Lean4hol_quotient_model in
  let count=ref 0 in
  let test label p=if not p then failwith("string quotient: "^label) else
    (incr count; print_endline("string quotient check: "^label)) in
  let get label=function Ok x->x|Error e->failwith(label^": "^e.message) in
  let n s=Str(Anonymous,s) and one=Succ Zero in
  let child p s=Str(p,s) and app=Env.apps in
  let pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) in
  let u=n "u" and v=n "v" and eq=n "Eq" and nat=n "Nat" in
  let exact label env g a b ty h = test label
    (hyp h=[] && frees(concl h)=[] && aconv(concl h)
      (node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
        quote_expr a;quote_expr b;quote_expr ty])) in
  let admit label result =
    let env,h=get label result in
    test label (hyp h=[] && frees(concl h)=[] && aconv(concl h)
      (node "l4_evalid" [Env.quote_policy env;Env.quote_env env])); env in
  let eb={Env.indexed_name=eq;indexed_level_params=[u];
    indexed_parameters=[n "A",Sort(Param u);n "a",Bvar 0];indices=[n "b",Bvar 1];
    indexed_result_level=Zero;
    indexed_constructors=[{Env.indexed_ctor_name=child eq "refl";indexed_fields=[];
      result_indices=[Bvar 0]}];indexed_claims=[]} in
  let eb={eb with Env.indexed_claims=Env.generate_indexed {remaining=100000} eb ~large:true ~k:true} in
  let env=admit "canonical Eq gate" (Env.admit_indexed_inductive Env.empty eb) in
  let env=List.fold_left(fun env kind ->
    let d={Env.kind=Env.Quotient kind;name=Qmodel.name kind;
      params=(if kind=Qmodel.Qlift then [u;v] else [u]);
      typ=Qmodel.signature {remaining=100000} kind (Param u)(Param v);value=None} in
    admit "canonical quotient gate" (Env.admit_quotient env d)) env
    [Qmodel.Qtype;Qmodel.Qctor;Qmodel.Qlift;Qmodel.Qind] in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000} nb} in
  let env=admit "canonical Nat gate" (Env.admit_inductive env nb) in
  let nt=Const(nat,[]) and char=Const(n "Char",[]) and text=Const(n "String",[]) in
  let r=App(Const(eq,[one]),nt) in
  let eqt x y=app r[x;y] in
  let refl x=app(Const(child eq "refl",[one]))[nt;x] in
  let quotient=app(Const(Qmodel.name Qmodel.Qtype,[one]))[nt;r] in
  let mk x=app(Const(Qmodel.name Qmodel.Qctor,[one]))[nt;r;x] in
  let def ?(params=[]) name typ value={Env.kind=Env.Definition;name;params;typ;value=Some value} in
  let install env d=admit "ordinary text interface gate" (Env.admit env d) in
  let primitive env d =
    let c=get "text factory gate" (Text.check_definition env d) in
    admit "text primitive admission gate" (Env.admit_text_primitive env d(Text.raw_theorem c)) in
  let env=install env(def(n "Char")(Sort one)nt) in
  let env=install env(def(n "String")(Sort one)quotient) in
  let at=Sort(Succ(Param u)) in
  let list e=App(Const(n "List",[Param u]),e) in
  let env=install env(def ~params:[u](n "List")(pi at(Sort one))(lam at nt)) in
  let env=install env(def ~params:[u](child(n "List")"nil")
    (pi at(list(Bvar 0)))(lam at(Natlit "0"))) in
  let env=install env(def ~params:[u](child(n "List")"cons")
    (pi at(pi(Bvar 0)(pi(list(Bvar 1))(list(Bvar 2)))))
    (lam at(lam(Bvar 0)(lam(list(Bvar 1))(Bvar 0))))) in
  let env=primitive env(def(child(n "Char")"ofNat")(pi nt char)(lam nt(Bvar 0))) in
  let lc=App(Const(n "List",[Zero]),char) in
  let env=primitive env(def(child(n "String")"ofList")(pi lc text)(lam lc(mk(Natlit "0")))) in
  let literal=Strlit "" in
  exact "literal typing gate" env [] literal literal text
    (get "literal typing"(Env.check env [] literal text));
  let seven=Natlit "7" in
  let f=lam nt seven in
  let h=lam nt(lam nt(lam(eqt(Bvar 1)(Bvar 0))(refl seven))) in
  let lift major=app(Const(Qmodel.name Qmodel.Qlift,[one;one]))[nt;r;nt;f;h;major] in
  let normalize label env term expected =
    let result,ty,h=get label(Env.normalize env [] term) in
    if result<>expected then begin
      print_endline("actual normal form: "^string_of_term(quote_expr result));
      print_endline("expected normal form: "^string_of_term(quote_expr expected))
    end;
    test (label^" normal form") (result=expected);
    exact (label^" certificate") env [] term result ty h in
  normalize "explicit constructor control" env (lift(mk(Natlit "0")))
    (App(Const(child nat "succ",[]),Natlit "6"));
  let alias=n "stringQuotientAlias" in
  let env=install env(def alias text literal) in
  List.iter(fun(label,major)->
    let term=lift major in
    exact (label^" typing gate") env [] term term nt
      (get label(Env.check env [] term nt));
    normalize label env term (lift literal);
    test (label^" conversion does not expand quotient major")
      (match Env.convert env [] term seven nt with
       | Error {kind=(Unsupported|Proof_failure);_}->true
       | Error e->failwith(label^": unexpected error: "^e.message)
       | Ok _->false))
    ["literal",literal;"delta alias",Const(alias,[]);
     "beta wrapper",App(lam text(Bvar 0),literal);
     "zeta wrapper",Let(Anonymous,text,literal,Bvar 0)];
  test "no new HOL axioms" (axioms()=string_quotient_axioms_before);
  Printf.printf "HOL_STRING_QUOTIENT_TESTS_PASSED %d\n%!" !count;;
string_quotient_tests();;
