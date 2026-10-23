(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_primitive_admission_axioms_before = axioms ();;
needs "hol/primitive_validation.ml";;

let l4_primitive_admission_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive admission regression: "^label);
    incr count; print_endline("primitive admission check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let constant_type label name expected =
    let actual=type_of(mk_const(name,[])) in
    print_string(name^" : "); print_type actual; print_newline();
    test label (actual=expected) in
  constant_type "header parameter type is l4_name list" "l4_prim_definition_header"
    `:l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`;
  constant_type "contract parameter type is l4_name list" "l4_prim_definition_contract"
    `:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) ->
       l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`;
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and z=Const(Str(nat,"zero"),[]) in
  let level=Succ Zero in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let named s=Const(Str(nat,s),[]) in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt nt;base;lam nt(lam nt step);n] in
  let add=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let pred=lam nt(recnat z (Bvar 1) (Bvar 0)) in
  let sub=lam nt(lam nt(recnat (Bvar 1) (App(named "pred",Bvar 0)) (Bvar 0))) in
  let mul=lam nt(lam nt(recnat z (app2 (named "add") (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let declaration suffix ty value={Env.kind=Env.Definition;name=Str(nat,suffix);
    params=[];typ=ty;value=Some value} in
  let ad=declaration "add" binary add and pd=declaration "pred" unary pred in
  let sd=declaration "sub" binary sub and md=declaration "mul" binary mul in
  let block={Env.inductive_name=nat;inductive_level=level;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env0,h0=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  let valid env=node "l4_evalid" [Env.quote_policy env;Env.quote_env env] in
  assert_th "Nat admission" (valid env0) h0;
  let fields d=match d.Env.value with
    | Some b -> [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b]
    | None -> failwith "fixture has no body" in
  let certify label env d =
    let c=get (label^" factory") (Prim.check_definition env d) in
    let h=Prim.definition_raw_theorem c in
    assert_th (label^" raw factory")
      (node "l4_prim_definition_contract" (node "l4_edef" [Env.quote_env env]::fields d)) h;
    test (label^" factory retains exact declaration") (Prim.definition_declaration c=d);
    h in
  let admit label env d h =
    let after,proof=get label (Env.admit_primitive env d h) in
    assert_th (label^" environment") (valid after) proof;
    test (label^" exact source body and Definition kind retained")
      (Env.declarations after=d::Env.declarations env);
    test (label^" policy retained") (aconv (Env.quote_policy after) (Env.quote_policy env));
    after in
  let ah=certify "add" env0 ad in
  let env1=admit "add" env0 ad ah in
  let ph=certify "pred" env1 pd in
  let env2=admit "pred" env1 pd ph in
  print_endline "HOL_PRIMITIVE_ADMISSION_ADD_PRED_PASSED";
  let bad_body=lam nt(lam nt(Bvar 1)) in
  let judgment env g a b ty=node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr a;quote_expr b;quote_expr ty] in
  assert_th "mutated body typing positive gate" (judgment env0 [] bad_body bad_body binary)
    (get "mutated body typing" (Env.check env0 [] bad_body binary));
  List.iter (fun (label,d) -> decline label (Env.admit_primitive env0 d ah))
    ["wrong body",{ad with Env.value=Some bad_body};
     "wrong primitive name",{ad with Env.name=Str(nat,"mul")};
     "wrong ordinary name",{ad with Env.name=Str(Anonymous,"OrdinaryAdd")};
     "wrong universe parameters",{ad with Env.params=[Str(Anonymous,"u")]};
     "wrong signature",{ad with Env.typ=unary};
     "wrong opaque kind",{ad with Env.kind=Env.Opaque};
     "wrong theorem kind",{ad with Env.kind=Env.Theorem};
     "wrong axiom kind",{ad with Env.kind=Env.Axiom}];
  let aux={Env.kind=Env.Definition;name=Str(Anonymous,"AdmissionEnvironmentMismatch");
    params=[];typ=unary;value=Some(lam nt(Bvar 0))} in
  let env_other,_=get "ordinary environment extension" (Env.admit env0 aux) in
  decline "certificate from different environment" (Env.admit_primitive env_other ad ah);
  decline "replay old environment certificate" (Env.admit_primitive env1 ad ah);
  let duplicate=certify "duplicate name fresh certificate" env1 ad in
  decline "duplicate name even with matching fresh certificate"
    (Env.admit_primitive env1 ad duplicate);
  let assumed=ADD_ASSUM `T` ah in
  test "hypothesis mutation keeps the exact conclusion"
    (hyp assumed<>[] && aconv (concl assumed) (concl ah));
  decline "nonempty theorem hypotheses" (Env.admit_primitive env0 ad assumed);
  decline "forged TRUTH certificate" (Env.admit_primitive env0 ad TRUTH);
  let checked=get "checked instead of raw factory" (Prim.check_definition env0 ad) in
  decline "checked judgment is not the required raw judgment"
    (Env.admit_primitive env0 ad (Prim.definition_theorem checked));
  test "zero-fuel admission" (match Env.admit_primitive ~fuel:0 env0 ad ah with
    | Error {kind=Resource;_} -> true | _ -> false);
  decline "ordinary protected-name admission stays closed" (Env.admit env0 ad);
  print_endline "HOL_PRIMITIVE_ADMISSION_GUARDS_PASSED";
  let sh=certify "sub with canonical pred" env2 sd in
  let env3=admit "sub" env2 sd sh in
  let mh=certify "mul with canonical add" env3 md in
  let env4=admit "mul" env3 md mh in
  print_endline "HOL_PRIMITIVE_ADMISSION_FOUR_PASSED";
  let eq label g a b=assert_th label (judgment env4 g a b nt)
    (get label (Env.convert env4 g a b nt)) in
  eq "admitted add symbolic equation" [nt;nt]
    (app2 (named "add") (Bvar 1) (succ(Bvar 0)))
    (succ(app2 (named "add") (Bvar 1) (Bvar 0)));
  eq "admitted pred symbolic equation" [nt]
    (App(named "pred",succ(Bvar 0))) (Bvar 0);
  eq "admitted sub symbolic equation" [nt;nt]
    (app2 (named "sub") (Bvar 1) (succ(Bvar 0)))
    (App(named "pred",app2 (named "sub") (Bvar 1) (Bvar 0)));
  eq "admitted mul symbolic equation" [nt;nt]
    (app2 (named "mul") (Bvar 1) (succ(Bvar 0)))
    (app2 (named "add") (app2 (named "mul") (Bvar 1) (Bvar 0)) (Bvar 1));
  test "no new HOL axioms" (axioms()=l4_primitive_admission_axioms_before);
  print_endline("HOL_PRIMITIVE_ADMISSION_TESTS_PASSED "^string_of_int !count);;

l4_primitive_admission_tests ();;
