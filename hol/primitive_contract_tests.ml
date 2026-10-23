(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_primitive_axioms_before = axioms ();;
needs "hol/primitive_validation.ml";;

let l4_primitive_contract_tests ?(projections=false) () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive contract regression: "^label);
    incr count; print_endline("primitive check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and z=Const(Str(nat,"zero"),[]) in
  let level=Succ Zero in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt nt;base;lam nt(lam nt step);n] in
  let add=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let pred=lam nt(recnat z (Bvar 1) (Bvar 0)) in
  let sub p=lam nt(lam nt(recnat (Bvar 1) (App(p,Bvar 0)) (Bvar 0))) in
  let mul a=lam nt(lam nt(recnat z (app2 a (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let block={Env.inductive_name=nat;inductive_level=level;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,h=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  assert_th "canonical Nat environment"
    (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h;
  let original_env=Env.quote_env env and original_policy=Env.quote_policy env in
  let judgment env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let contract env name bodies=node name (judgment env::List.map quote_expr bodies) in
  let checked env g a b ty=list_mk_comb(judgment env,
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]) in
  let typed label body ty=assert_th (label^" well typed")
    (checked env [] body body ty) (get label (Env.check env [] body ty)) in
  let eq label g a b=assert_th label (checked env g a b nt)
    (get label (Env.convert env g a b nt)) in
  let ac=get "add" (Prim.check_add env add) in
  assert_th "add contract" (contract env "l4_prim_add_contract" [add]) (Prim.add_theorem ac);
  test "add body retained" (Prim.add_body ac=add);
  let pc=get "pred" (Prim.check_pred env pred) in
  assert_th "pred contract" (contract env "l4_prim_pred_contract" [pred]) (Prim.pred_theorem pc);
  test "pred body retained" (Prim.pred_body pc=pred);
  let notation=[l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_prim_unary;
    l4_prim_binary;l4_nat_name] in
  let add_parts=CONJUNCTS(REWRITE_RULE (l4_prim_add_contract::notation) (Prim.add_theorem ac)) in
  assert_th "add arbitrary x,y equation"
    (checked env [nt;nt] (app2 add (Bvar 1) (succ(Bvar 0)))
      (succ(app2 add (Bvar 1) (Bvar 0))) nt) (List.nth add_parts 2);
  let pred_parts=CONJUNCTS(REWRITE_RULE (l4_prim_pred_contract::notation) (Prim.pred_theorem pc)) in
  assert_th "pred arbitrary x equation"
    (checked env [nt] (App(pred,succ(Bvar 0))) (Bvar 0) nt) (List.nth pred_parts 2);
  let add_bad_base=lam nt(lam nt(recnat z (succ(Bvar 0)) (Bvar 0))) in
  let add_bad_step=lam nt(lam nt(recnat (Bvar 1) (Bvar 0) (Bvar 0))) in
  let add_finite=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 3)) (Bvar 0))) in
  List.iter (fun (label,b) -> typed label b binary; decline label (Prim.check_add env b))
    ["add wrong base",add_bad_base;"add ignores successor",add_bad_step;
     "add finite impostor",add_finite];
  eq "add impostor passes y=0 for arbitrary x" [nt] (app2 add_finite (Bvar 0) z) (Bvar 0);
  eq "add impostor passes y=1 for arbitrary x" [nt]
    (app2 add_finite (Bvar 0) (succ z)) (succ(Bvar 0));
  let pred_bad_base=lam nt(recnat (succ z) (Bvar 1) (Bvar 0)) in
  let pred_finite=lam nt(recnat z z (Bvar 0)) in
  List.iter (fun (label,b) -> typed label b unary; decline label (Prim.check_pred env b))
    ["pred wrong base",pred_bad_base;"pred identity",lam nt(Bvar 0);
     "pred finite impostor",pred_finite];
  eq "pred impostor passes zero" [] (App(pred_finite,z)) z;
  eq "pred impostor passes one" [] (App(pred_finite,succ z)) z;
  let add_wrapped=Let(Anonymous,binary,add,Bvar 0) in
  let pred_wrapped=App(lam unary(Bvar 0),pred) in
  let aw=get "zeta add" (Prim.check_add env add_wrapped) in
  let pw=get "beta pred" (Prim.check_pred env pred_wrapped) in
  assert_th "zeta add" (contract env "l4_prim_add_contract" [add_wrapped]) (Prim.add_theorem aw);
  assert_th "beta pred" (contract env "l4_prim_pred_contract" [pred_wrapped]) (Prim.pred_theorem pw);
  print_endline "HOL_PRIMITIVE_ADD_PRED_PASSED";
  let sb=sub(Prim.pred_body pc) and mb=mul(Prim.add_body ac) in
  let sc=get "sub" (Prim.check_sub env pc sb) in
  let mc=get "mul" (Prim.check_mul env ac mb) in
  assert_th "sub contract" (contract env "l4_prim_sub_contract" [pred;sb]) (Prim.sub_theorem sc);
  assert_th "mul contract" (contract env "l4_prim_mul_contract" [add;mb]) (Prim.mul_theorem mc);
  test "sub body retained" (Prim.sub_body sc=sb);
  test "mul body retained" (Prim.mul_body mc=mb);
  assert_th "sub carries pred certificate" (contract env "l4_prim_pred_contract" [pred])
    (MATCH_MP (SPECL [judgment env;quote_expr pred;quote_expr sb] l4_prim_sub_dependency)
      (Prim.sub_theorem sc));
  assert_th "mul carries add certificate" (contract env "l4_prim_add_contract" [add])
    (MATCH_MP (SPECL [judgment env;quote_expr add;quote_expr mb] l4_prim_mul_dependency)
      (Prim.mul_theorem mc));
  let sub_parts=CONJUNCTS(REWRITE_RULE (l4_prim_sub_contract::notation) (Prim.sub_theorem sc)) in
  let mul_parts=CONJUNCTS(REWRITE_RULE (l4_prim_mul_contract::notation) (Prim.mul_theorem mc)) in
  assert_th "sub arbitrary x,y equation"
    (checked env [nt;nt] (app2 sb (Bvar 1) (succ(Bvar 0)))
      (App(pred,app2 sb (Bvar 1) (Bvar 0))) nt) (List.nth sub_parts 3);
  assert_th "mul arbitrary x,y equation"
    (checked env [nt;nt] (app2 mb (Bvar 1) (succ(Bvar 0)))
      (app2 add (app2 mb (Bvar 1) (Bvar 0)) (Bvar 1)) nt) (List.nth mul_parts 3);
  let sub_bad=lam nt(lam nt(recnat (Bvar 1) (App(pred,Bvar 3)) (Bvar 0))) in
  let sub_bad_base=lam nt(lam nt(recnat z (App(pred,Bvar 0)) (Bvar 0))) in
  let mul_bad=lam nt(lam nt(recnat z (app2 add (Bvar 0) (Bvar 1)) (Bvar 0))) in
  List.iter (fun (label,b) -> typed label b binary; decline label (Prim.check_sub env pc b))
    ["sub identity step",add_bad_step;"sub ignores recursive result",sub_bad;
     "sub poisoned pred",sub pred_finite;"sub wrong base",sub_bad_base];
  List.iter (fun (label,b) -> typed label b binary; decline label (Prim.check_mul env ac b))
    ["mul wrong base",add;"mul wrong variable",mul_bad;"mul poisoned add",mul add_bad_step];
  let sw=get "sub convertible dependency" (Prim.check_sub env pw sb) in
  let mw=get "mul convertible dependency" (Prim.check_mul env aw mb) in
  assert_th "sub exact wrapped dependency" (contract env "l4_prim_sub_contract" [pred_wrapped;sb])
    (Prim.sub_theorem sw);
  assert_th "mul exact wrapped dependency" (contract env "l4_prim_mul_contract" [add_wrapped;mb])
    (Prim.mul_theorem mw);
  decline "add missing Nat" (Prim.check_add Env.empty add);
  decline "pred missing Nat" (Prim.check_pred Env.empty pred);
  decline "add wrong signature" (Prim.check_add env pred);
  decline "pred wrong signature" (Prim.check_pred env add);
  decline "open candidate" (Prim.check_pred env (Bvar 0));
  decline "dangling variable inside candidate" (Prim.check_pred env (lam nt(Bvar 1)));
  test "malformed variable" (match Prim.check_pred env (Bvar (-1)) with
    | Error {kind=Invalid_input;_} -> true | _ -> false);
  test "zero fuel" (match Prim.check_add ~fuel:0 env add with
    | Error {kind=Resource;_} -> true | _ -> false);
  let aux=Str(Anonymous,"PrimitiveAuditAux") in
  let env2,_=get "ordinary source dependency" (Env.admit env
    {Env.kind=Env.Definition;name=aux;params=[];typ=unary;value=Some pred}) in
  let refpred=Const(aux,[]) in
  let refpc=get "certified ordinary source" (Prim.check_pred env2 refpred) in
  let refs=sub refpred in
  let refsc=get "sub ordinary source" (Prim.check_sub env2 refpc refs) in
  assert_th "sub ordinary source contract" (contract env2 "l4_prim_sub_contract" [refpred;refs])
    (Prim.sub_theorem refsc);
  let auxadd=Str(Anonymous,"PrimitiveAuditAdd") in
  let env3,_=get "ordinary add dependency" (Env.admit env
    {Env.kind=Env.Definition;name=auxadd;params=[];typ=binary;value=Some add}) in
  let refadd=Const(auxadd,[]) in
  let refac=get "certified ordinary add" (Prim.check_add env3 refadd) in
  let refm=mul refadd in
  let refmc=get "mul ordinary source" (Prim.check_mul env3 refac refm) in
  assert_th "mul ordinary source contract" (contract env3 "l4_prim_mul_contract" [refadd;refm])
    (Prim.mul_theorem refmc);
  decline "dependency environment replay" (Prim.check_sub env2 pc sb);
  decline "dependency environment replay mul" (Prim.check_mul env2 ac mb);
  let policy=get "unused policy" (Env.with_axioms
    [{Env.axiom_name=Str(Anonymous,"UnusedPrimitivePolicy");axiom_params=[];axiom_type=nt}]) in
  let env_policy,_=get "Nat under different policy" (Env.admit_inductive policy block) in
  test "policy replay has identical entries" (aconv (Env.quote_env env_policy) (Env.quote_env env));
  decline "dependency policy replay" (Prim.check_sub env_policy pc sb);
  decline "dependency policy replay mul" (Prim.check_mul env_policy ac mb);
  List.iter (fun (suffix,ty,b) -> decline ("protected ordinary admission "^suffix)
    (Env.admit env {Env.kind=Env.Definition;name=Str(nat,suffix);params=[];typ=ty;value=Some b}))
    ["add",binary,add;"pred",unary,pred;"sub",binary,sb;"mul",binary,mb];
  if projections then begin
  let raw_j=node "l4_edef" [Env.quote_env env] in
  let pointwise=SPECL [Env.quote_policy env;Env.quote_env env] l4_checked_typing in
  let project label lemma name args h =
    let quoted=List.map quote_expr args in
    let raw=MP (MP (SPECL (judgment env::raw_j::quoted) lemma) pointwise) h in
    assert_th label (node name (raw_j::quoted)) raw in
  project "add raw equation contract" l4_prim_add_mono "l4_prim_add_contract" [add]
    (Prim.add_theorem ac);
  project "pred raw equation contract" l4_prim_pred_mono "l4_prim_pred_contract" [pred]
    (Prim.pred_theorem pc);
  project "sub raw equation contract" l4_prim_sub_mono "l4_prim_sub_contract" [pred;sb]
    (Prim.sub_theorem sc);
  project "mul raw equation contract" l4_prim_mul_mono "l4_prim_mul_contract" [add;mb]
    (Prim.mul_theorem mc)
  end;
  test "environment unchanged" (aconv (Env.quote_env env) original_env);
  test "policy unchanged" (aconv (Env.quote_policy env) original_policy);
  test "no new HOL axioms" (axioms()=l4_primitive_axioms_before);
  print_endline("HOL_PRIMITIVE_CONTRACT_TESTS_PASSED "^string_of_int !count);;

(* Factory tests run first and independently of the body-regression suite. *)
let l4_primitive_factory_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive factory regression: "^label);
    incr count; print_endline("factory check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let header_type=type_of(mk_const("l4_prim_definition_header",[])) in
  print_string "l4_prim_definition_header : "; print_type header_type; print_newline();
  test "header parameter type is l4_name list"
    (header_type=`:l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  test "contract parameter type is l4_name list"
    (type_of(mk_const("l4_prim_definition_contract",[]))=
      `:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) ->
         l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and z=Const(Str(nat,"zero"),[]) in
  let level=Succ Zero in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt nt;base;lam nt(lam nt step);n] in
  let add=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let pred=lam nt(recnat z (Bvar 1) (Bvar 0)) in
  let add_bad_step=lam nt(lam nt(recnat (Bvar 1) (Bvar 0) (Bvar 0))) in
  let pred_bad=lam nt(Bvar 0) in
  let add_wrapped=Let(Anonymous,binary,add,Bvar 0) in
  let sb=lam nt(lam nt(recnat (Bvar 1) (App(pred,Bvar 0)) (Bvar 0))) in
  let mb=lam nt(lam nt(recnat z (app2 add (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let block={Env.inductive_name=nat;inductive_level=level;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,h=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  assert_th "canonical Nat environment"
    (node "l4_evalid" [Env.quote_policy env;Env.quote_env env]) h;
  let original_env=Env.quote_env env and original_policy=Env.quote_policy env in
  let judgment env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let checked env g a b ty=list_mk_comb(judgment env,
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]) in
  let typed label body ty=assert_th (label^" well typed")
    (checked env [] body body ty) (get label (Env.check env [] body ty)) in
  let declaration suffix ty b={Env.kind=Env.Definition;name=Str(nat,suffix);
    params=[];typ=ty;value=Some b} in
  let ad=declaration "add" binary add and pd=declaration "pred" unary pred in
  let fields d=match d.Env.value with
    | Some b -> [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b]
    | None -> failwith "test declaration requires a body" in
  let definition_stmt env d=node "l4_prim_definition_contract" (judgment env::fields d) in
  let definition label env d =
    let c=get label (Prim.check_definition env d) in
    assert_th (label^" checked fields") (definition_stmt env d) (Prim.definition_theorem c);
    assert_th (label^" raw fields")
      (node "l4_prim_definition_contract" (node "l4_edef" [Env.quote_env env]::fields d))
      (Prim.definition_raw_theorem c);
    test (label^" original declaration retained") (Prim.definition_declaration c=d); c in
  let adc=definition "add declaration" env ad in
  let pdc=definition "pred declaration" env pd in
  let xname=Str(Anonymous,"x") and yname=Str(Anonymous,"y") in
  let named={ad with Env.typ=Pi(xname,nt,Pi(yname,nt,nt))} in
  let raw=Prim.definition_raw_theorem adc in
  assert_th "raw declaration body typing"
    (node "l4_edef" [Env.quote_env env;quote_context [];quote_expr add;quote_expr add;quote_expr binary])
    (MATCH_MP l4_prim_definition_body_typed raw);
  assert_th "raw declaration type formation"
    (node "l4_edef" [Env.quote_env env;quote_context [];quote_expr binary;quote_expr binary;
      quote_expr(Sort level)]) (MATCH_MP l4_prim_definition_type_formed raw);
  assert_th "declaration header obligation"
    (node "l4_prim_definition_header" (fields ad)) (MATCH_MP l4_prim_definition_header_required raw);
  typed "add mutation positive typing gate" add_bad_step binary;
  typed "pred mutation positive typing gate" pred_bad unary;
  List.iter (fun (label,d) -> decline label (Prim.check_definition env d))
    ["nonprimitive definition",{ad with Env.name=Str(Anonymous,"UnrelatedAdd")};
     "unimplemented primitive definition",{ad with Env.name=Str(nat,"gcd")};
     "theorem cannot impersonate primitive definition",{ad with Env.kind=Env.Theorem};
     "opaque cannot impersonate primitive definition",{ad with Env.kind=Env.Opaque};
     "axiom cannot impersonate primitive definition",{ad with Env.kind=Env.Axiom};
     "nonempty universe parameters",{ad with Env.params=[xname]};
     "wrong declared signature",{ad with Env.typ=unary};
     "typed body substitution attack",{ad with Env.value=Some add_bad_step};
     "typed pred body substitution attack",{pd with Env.value=Some pred_bad};
     "sub requires canonical admitted pred",declaration "sub" binary sb;
     "mul requires canonical admitted add",declaration "mul" binary mb];
  decline "add factory without Nat environment" (Prim.check_definition Env.empty ad);
  decline "pred factory without Nat environment" (Prim.check_definition Env.empty pd);
  test "certificate binds original body"
    (not(aconv (concl(Prim.definition_theorem adc))
      (definition_stmt env {ad with Env.value=Some add_bad_step})));
  test "certificate binds original type"
    (not(aconv (concl(Prim.definition_theorem adc)) (definition_stmt env named)));
  let aux=Str(Anonymous,"PrimitiveFactoryAux") in
  let env2,_=get "ordinary source environment extension" (Env.admit env
    {Env.kind=Env.Definition;name=aux;params=[];typ=unary;value=Some pred}) in
  test "certificate binds original environment"
    (not(aconv (concl(Prim.definition_theorem adc)) (definition_stmt env2 ad)));
  test "pred certificate binds original environment"
    (not(aconv (concl(Prim.definition_theorem pdc)) (definition_stmt env2 pd)));
  let policy=get "unused policy" (Env.with_axioms
    [{Env.axiom_name=Str(Anonymous,"UnusedFactoryPolicy");axiom_params=[];axiom_type=nt}]) in
  let env_policy,_=get "Nat under different policy" (Env.admit_inductive policy block) in
  test "policy mismatch has identical entries" (aconv (Env.quote_env env_policy) (Env.quote_env env));
  test "certificate binds original policy"
    (not(aconv (concl(Prim.definition_theorem adc)) (definition_stmt env_policy ad)));
  print_endline "HOL_PRIMITIVE_FACTORY_REQUIRED_PASSED";
  ignore(definition "named signature binders" env named);
  ignore(definition "unmodified wrapped body" env {ad with Env.value=Some add_wrapped});
  let ua=Param xname in
  let escaped=Let(Anonymous,Sort(Succ ua),Sort ua,add) in
  typed "undeclared universe parameter body" escaped binary;
  decline "header rejects undeclared body universe" (Prim.check_definition env {ad with Env.value=Some escaped});
  let alias=Str(Anonymous,"PrimitiveSignatureAlias") in
  let env_alias,_=get "ordinary type alias" (Env.admit env
    {Env.kind=Env.Definition;name=alias;params=[];typ=Sort level;value=Some binary}) in
  let alias_type=Const(alias,[]) in
  assert_th "type alias positive typing gate" (checked env_alias [] add add alias_type)
    (get "type alias positive typing gate" (Env.check env_alias [] add alias_type));
  decline "type alias is not canonical signature"
    (Prim.check_definition env_alias {ad with Env.typ=alias_type});
  test "definition body required" (match Prim.check_definition env {ad with Env.value=None} with
    | Error {kind=Invalid_input;_} -> true | _ -> false);
  test "definition zero fuel" (match Prim.check_definition ~fuel:0 env ad with
    | Error {kind=Resource;_} -> true | _ -> false);
  test "environment unchanged" (aconv (Env.quote_env env) original_env);
  test "policy unchanged" (aconv (Env.quote_policy env) original_policy);
  test "no new HOL axioms" (axioms()=l4_primitive_axioms_before);
  print_endline("HOL_PRIMITIVE_FACTORY_TESTS_PASSED "^string_of_int !count);;

let l4_primitive_bool_tests suffix =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let phase=match Sys.getenv_opt "HOL_PRIMITIVE_BOOL_PHASE" with
    | None -> "all"
    | Some ("all" | "body" | "factory" | "bases" | "diagonal" as p) -> p
    | Some _ -> failwith "HOL_PRIMITIVE_BOOL_PHASE must be all, body, factory, bases, or diagonal" in
  let selected p=phase="all" || phase=p in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive "^suffix^" regression: "^label);
    incr count; print_endline(suffix^" check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  let jty=`:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) -> l4_expr -> bool` in
  List.iter (fun n -> test (n^" monomorphic type") (type_of(mk_const(n,[]))=jty))
    ["l4_prim_beq_contract";"l4_prim_ble_contract"];
  test "header type unchanged" (type_of(mk_const("l4_prim_definition_header",[]))=
    `:l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  test "definition contract type unchanged" (type_of(mk_const("l4_prim_definition_contract",[]))=
    `:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) ->
       l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  let nat=Str(Anonymous,"Nat") and bool=Str(Anonymous,"Bool") in
  let nt=Const(nat,[]) and bt=Const(bool,[]) in
  let z=Const(Str(nat,"zero"),[]) in
  let fal=Const(Str(bool,"false"),[]) and tru=Const(Str(bool,"true"),[]) in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt bt in
  let signature=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let level=Succ Zero in
  let recnat ty base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt ty;base;step;n] in
  let body b00 b0s bs0 diag =
    let base=lam nt(recnat bt b00 (lam nt(lam bt b0s)) (Bvar 0)) in
    (* At the inner successor: [innerIH; yPred; y; outerIH; xPred; x]. *)
    let step=lam nt(lam unary(lam nt
      (recnat bt bs0 (lam nt(lam bt diag)) (Bvar 0)))) in
    lam nt(recnat unary base step (Bvar 0)) in
  let b0s=if suffix="beq" then fal else tru in
  let opposite=if suffix="beq" then tru else fal in
  let diag=App(Bvar 3,Bvar 1) in
  let candidate=body tru b0s fal diag in
  let block n cs={Env.inductive_name=n;inductive_level=level;constructors=cs;claims=[]} in
  let admit_block env b =
    let b={b with Env.claims=Env.generate {remaining=100000} b} in
    let env',h=get "canonical inductive" (Env.admit_inductive env b) in
    assert_th "canonical inductive environment"
      (node "l4_evalid" [Env.quote_policy env';Env.quote_env env']) h; env' in
  let nat_env=admit_block Env.empty
    (block nat [Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]]) in
  let env=admit_block nat_env (block bool [Str(bool,"false"),[];Str(bool,"true"),[]]) in
  let original=Env.quote_env env in
  let judgment env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let checked env g a b ty=list_mk_comb(judgment env,
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]) in
  let certify env b = if suffix="beq" then
      match Prim.check_beq env b with Error e -> Error e
        | Ok c -> Ok(Prim.beq_body c,Prim.beq_theorem c)
    else match Prim.check_ble env b with Error e -> Error e
        | Ok c -> Ok(Prim.ble_body c,Prim.ble_theorem c) in
  if selected "body" then begin
  let retained,h=get "symbolic body certificate" (certify env candidate) in
  test "body certificate retains original body" (retained=candidate);
  assert_th "body contract" (node ("l4_prim_"^suffix^"_contract")
    [judgment env;quote_expr candidate]) h;
  let equations=CONJUNCTS(REWRITE_RULE
    [l4_prim_beq_contract;l4_prim_ble_contract;l4_prim_bool_cases_contract;
     l4_prim_bool_binary;l4_prim_bool;l4_prim_true;l4_prim_false;
     l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_bool_name;l4_nat_name] h) in
  List.iteri (fun i (g,a,b,ty) -> assert_th ("contract conjunct "^string_of_int i)
    (checked env g a b ty) (List.nth equations i))
    [[],candidate,candidate,signature;
     [],app2 candidate z z,tru,bt;
     [nt],app2 candidate z (succ(Bvar 0)),b0s,bt;
     [nt],app2 candidate (succ(Bvar 0)) z,fal,bt;
     [nt;nt],app2 candidate (succ(Bvar 1)) (succ(Bvar 0)),
       app2 candidate (Bvar 1) (Bvar 0),bt];
  end;
  let d={Env.kind=Env.Definition;name=Str(nat,suffix);params=[];
    typ=signature;value=Some candidate} in
  if selected "factory" then begin
  let c=get "definition factory" (Prim.check_definition env d) in
  let fields=[quote_name d.Env.name;mk_list([],`:l4_name`);quote_expr signature;quote_expr candidate] in
  assert_th "checked factory contract"
    (node "l4_prim_definition_contract" (judgment env::fields)) (Prim.definition_theorem c);
  let raw=Prim.definition_raw_theorem c in
  assert_th "raw factory contract"
    (node "l4_prim_definition_contract" (node "l4_edef" [Env.quote_env env]::fields)) raw;
  test "factory retains exact declaration" (Prim.definition_declaration c=d);
  let admitted,eh=get "guarded primitive admission" (Env.admit_primitive env d raw) in
  assert_th "admitted environment" (node "l4_evalid"
    [Env.quote_policy admitted;Env.quote_env admitted]) eh;
  test "admission retains Definition source body" (Env.declarations admitted=d::Env.declarations env);
  let named=Const(d.Env.name,[]) in
  assert_th "admitted arbitrary diagonal"
    (checked admitted [nt;nt] (app2 named (succ(Bvar 1)) (succ(Bvar 0)))
      (app2 named (Bvar 1) (Bvar 0)) bt)
    (get "admitted diagonal" (Env.convert admitted [nt;nt]
      (app2 named (succ(Bvar 1)) (succ(Bvar 0))) (app2 named (Bvar 1) (Bvar 0)) bt));
  print_endline("HOL_PRIMITIVE_"^String.uppercase_ascii suffix^"_POSITIVE_PASSED");
  let bad=lam nt(lam nt fal) in
  assert_th "factory mutant typing" (checked env [] bad bad signature)
    (get "factory mutant typing" (Env.check env [] bad signature));
  decline "typed factory body mutation" (Prim.check_definition env {d with Env.value=Some bad});
  decline "consumer body mismatch" (Env.admit_primitive env {d with Env.value=Some bad} raw);
  decline "missing Bool dependency" (Prim.check_definition nat_env d);
  decline "missing Nat and Bool dependencies" (Prim.check_definition Env.empty d);
  decline "consumer swapped operation name" (Env.admit_primitive env
    {d with Env.name=Str(nat,if suffix="beq" then "ble" else "beq")} raw);
  decline "wrong Nat-result signature" (Prim.check_definition env {d with Env.typ=pi nt(pi nt nt)});
  decline "nonempty universe parameters" (Prim.check_definition env
    {d with Env.params=[Str(Anonymous,"u")]});
  decline "different-environment replay" (Env.admit_primitive admitted d raw);
  decline "unproved consumer certificate" (Env.admit_primitive env d TRUTH);
  decline "ordinary protected admission" (Env.admit env d);
  test "factory zero fuel" (match Prim.check_definition ~fuel:0 env d with
    | Error {kind=Resource;_} -> true | _ -> false);
  end;
  let mutants=["zero zero",body fal b0s fal diag;
    "zero successor",body tru opposite fal diag;
    "successor zero",body tru b0s tru diag;
    "wrong recursive argument",body tru b0s fal (App(Bvar 3,succ(Bvar 1)))] in
  List.iteri (fun i (label,b) -> if selected (if i=3 then "diagonal" else "bases") then begin
    assert_th (label^" mutant typing") (checked env [] b b signature)
      (get (label^" typing") (Env.check env [] b signature));
    decline (label^" symbolic rejection") (certify env b) end) mutants;
  if selected "diagonal" then begin
  let decoy=body tru b0s fal tru in
  assert_th "example-only decoy typing" (checked env [] decoy decoy signature)
    (get "decoy typing" (Env.check env [] decoy signature));
  List.iter (fun n -> assert_th "decoy finite positive gate" (checked env [] (app2 decoy n n) tru bt)
    (get "decoy finite gate" (Env.convert env [] (app2 decoy n n) tru bt))) [z;succ z];
  decline "finite examples do not establish symbolic diagonal" (certify env decoy);
  end;
  test "original environment unchanged" (aconv (Env.quote_env env) original);
  test "no new HOL axioms" (axioms()=l4_primitive_axioms_before);
  print_endline("HOL_PRIMITIVE_"^String.uppercase_ascii suffix^"_"^
    String.uppercase_ascii phase^"_TESTS_PASSED "^string_of_int !count);;

let l4_primitive_pow_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let phase=match Sys.getenv_opt "HOL_PRIMITIVE_POW_PHASE" with
    | None -> "factory"
    | Some ("factory" | "body" | "base" | "step" | "order" | "dependencies" |
            "poison" | "replay" | "missing" as p) -> p
    | Some _ -> failwith "unknown HOL_PRIMITIVE_POW_PHASE" in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive pow regression: "^label);
    incr count; print_endline("pow "^phase^" check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  test "pow contract monomorphic type" (type_of(mk_const("l4_prim_pow_contract",[]))=
    `:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) ->
      l4_expr -> l4_expr -> l4_expr -> bool`);
  test "header type unchanged" (type_of(mk_const("l4_prim_definition_header",[]))=
    `:l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and z=Const(Str(nat,"zero"),[]) in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let one=succ z in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let named s=Const(Str(nat,s),[]) in
  let level=Succ Zero in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt nt;base;lam nt(lam nt step);n] in
  let add=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let mul=lam nt(lam nt(recnat z (app2 (named "add") (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let pow base step=lam nt(lam nt(recnat base step (Bvar 0))) in
  let candidate=pow one (app2 (named "mul") (Bvar 0) (Bvar 3)) in
  let declaration suffix value={Env.kind=Env.Definition;name=Str(nat,suffix);
    params=[];typ=binary;value=Some value} in
  let d=declaration "pow" candidate in
  let block={Env.inductive_name=nat;inductive_level=level;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env0,h0=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  let valid env=node "l4_evalid" [Env.quote_policy env;Env.quote_env env] in
  let j env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let checked env g a b ty=list_mk_comb(j env,
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]) in
  assert_th "canonical Nat environment" (valid env0) h0;
  let fields d=match d.Env.value with
    | Some b -> [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b]
    | None -> failwith "test declaration requires a body" in
  let certify env d =
    let c=get "definition factory" (Prim.check_definition env d) in
    assert_th "raw definition contract" (node "l4_prim_definition_contract"
      (node "l4_edef" [Env.quote_env env]::fields d)) (Prim.definition_raw_theorem c);
    test "factory retains exact declaration" (Prim.definition_declaration c=d); c in
  let admit env d c =
    let env',h=get "primitive admission" (Env.admit_primitive env d (Prim.definition_raw_theorem c)) in
    assert_th "primitive environment" (valid env') h;
    test "admission retains exact Definition" (Env.declarations env'=d::Env.declarations env);
    test "admission retains policy" (aconv (Env.quote_policy env') (Env.quote_policy env)); env' in
  let ad=declaration "add" add in
  let env1=admit env0 ad (certify env0 ad) in
  let md=declaration "mul" mul in
  let env=admit env1 md (certify env1 md) in
  print_endline "HOL_PRIMITIVE_POW_CANONICAL_DEPENDENCIES_PASSED";
  let original=Env.quote_env env in
  if phase="factory" then begin
    let c=certify env d in
    assert_th "checked pow declaration" (node "l4_prim_definition_contract" (j env::fields d))
      (Prim.definition_theorem c);
    let env'=admit env d c in
    let eq label g a b=assert_th label (checked env' g a b nt)
      (get label (Env.convert env' g a b nt)) in
    eq "admitted symbolic zero equation" [nt] (app2 (named "pow") (Bvar 0) z) one;
    eq "admitted symbolic successor equation" [nt;nt]
      (app2 (named "pow") (Bvar 1) (succ(Bvar 0)))
      (app2 (named "mul") (app2 (named "pow") (Bvar 1) (Bvar 0)) (Bvar 1));
    let bad=lam nt(lam nt z) in
    assert_th "factory mutant typing" (checked env [] bad bad binary)
      (get "factory mutant typing" (Env.check env [] bad binary));
    decline "typed wrong-body factory" (Prim.check_definition env {d with Env.value=Some bad});
    decline "consumer body substitution" (Env.admit_primitive env {d with Env.value=Some bad}
      (Prim.definition_raw_theorem c));
    decline "wrong name" (Prim.check_definition env {d with Env.name=Str(nat,"gcd")});
    decline "wrong parameters" (Prim.check_definition env {d with Env.params=[Str(Anonymous,"u")]});
    decline "wrong signature" (Prim.check_definition env {d with Env.typ=unary});
    decline "quotient cannot impersonate a definition" (Prim.check_definition env
      {d with Env.kind=Env.Quotient Lean4hol_quotient_model.Qtype});
    decline "consumer quotient kind mismatch" (Env.admit_primitive env
      {d with Env.kind=Env.Quotient Lean4hol_quotient_model.Qtype} (Prim.definition_raw_theorem c));
    decline "ordinary protected admission" (Env.admit env d);
    decline "raw certificate environment replay" (Env.admit_primitive env' d (Prim.definition_raw_theorem c));
    decline "unproved consumer certificate" (Env.admit_primitive env d TRUTH);
    test "factory zero fuel" (match Prim.check_definition ~fuel:0 env d with
      | Error {kind=Resource;_} -> true | _ -> false)
  end else if phase="missing" then begin
    decline "missing canonical add and mul" (Prim.check_definition env0 d);
    decline "missing canonical mul" (Prim.check_definition env1 d)
  end else begin
    let ac=get "canonical add recertification" (Prim.check_add env (named "add")) in
    let mc=get "canonical mul recertification" (Prim.check_mul env ac (named "mul")) in
    assert_th "mul dependency includes add" (node "l4_prim_mul_contract"
      [j env;quote_expr(named "add");quote_expr(named "mul")]) (Prim.mul_theorem mc);
    if phase="body" then begin
      let pc=get "pow symbolic body certificate" (Prim.check_pow env mc candidate) in
      let h=Prim.pow_theorem pc in
      test "pow body retained" (Prim.pow_body pc=candidate);
      assert_th "pow contract" (node "l4_prim_pow_contract"
        [j env;quote_expr(named "add");quote_expr(named "mul");quote_expr candidate]) h;
      let mh=MATCH_MP l4_prim_pow_dependency h in
      assert_th "pow carries mul" (concl(Prim.mul_theorem mc)) mh;
      assert_th "pow transitively carries add" (concl(Prim.add_theorem ac))
        (MATCH_MP l4_prim_mul_dependency mh);
      let parts=CONJUNCTS(REWRITE_RULE
        [l4_prim_pow_contract;l4_prim_binary;l4_prim_unary;l4_prim_nat;
         l4_prim_one;l4_prim_succ;l4_prim_zero;l4_nat_name] h) in
      assert_th "pow canonical typing" (checked env [] candidate candidate binary) (List.nth parts 1);
      assert_th "pow arbitrary zero equation" (checked env [nt] (app2 candidate (Bvar 0) z) one nt)
        (List.nth parts 2);
      assert_th "pow arbitrary successor equation"
        (checked env [nt;nt] (app2 candidate (Bvar 1) (succ(Bvar 0)))
          (app2 (named "mul") (app2 candidate (Bvar 1) (Bvar 0)) (Bvar 1)) nt) (List.nth parts 3);
      test "body zero fuel" (match Prim.check_pow ~fuel:0 env mc candidate with
        | Error {kind=Resource;_} -> true | _ -> false)
    end else if phase="dependencies" || phase="poison" || phase="replay" then begin
      if phase<>"poison" then begin
        let pc=get "positive pow dependency gate" (Prim.check_pow env mc candidate) in
        test "positive dependency gate closed"
          (hyp(Prim.pow_theorem pc)=[] && frees(concl(Prim.pow_theorem pc))=[])
      end;
      if phase<>"replay" then begin
        let bad=lam nt(lam nt z) in
        assert_th "poisoned mul typing" (checked env [] bad bad binary)
          (get "poisoned mul typing" (Env.check env [] bad binary));
        decline "poisoned mul cannot produce dependency certificate" (Prim.check_mul env ac bad);
        let bad_add=lam nt(lam nt(Bvar 1)) in
        assert_th "poisoned add typing" (checked env [] bad_add bad_add binary)
          (get "poisoned add typing" (Env.check env [] bad_add binary));
        decline "poisoned transitive add cannot produce dependency certificate" (Prim.check_add env bad_add)
      end;
      if phase<>"poison" then begin
        let aux={Env.kind=Env.Definition;name=Str(Anonymous,"PowDependencyReplay");
          params=[];typ=unary;value=Some(lam nt(Bvar 0))} in
        let env',_=get "valid environment extension" (Env.admit env aux) in
        decline "mul certificate environment replay" (Prim.check_pow env' mc candidate);
        decline "transitive add certificate environment replay" (Prim.check_mul env' ac (named "mul"))
      end;
      if phase="dependencies" then begin
        decline "missing canonical add and mul" (Prim.check_definition env0 d);
        decline "missing canonical mul" (Prim.check_definition env1 d)
      end
    end else begin
      let bad=if phase="base" then pow z (app2 (named "mul") (Bvar 0) (Bvar 3))
        else if phase="step" then pow one (Bvar 0)
        else pow one (app2 (named "mul") (Bvar 3) (Bvar 0)) in
      assert_th "mutant typing positive gate" (checked env [] bad bad binary)
        (get "mutant typing" (Env.check env [] bad binary));
      if phase<>"base" then begin
        assert_th "mutant zero equation positive gate"
          (checked env [nt] (app2 bad (Bvar 0) z) one nt)
          (get "mutant zero equation" (Env.convert env [nt] (app2 bad (Bvar 0) z) one nt))
      end;
      decline "symbolic pow mutation" (Prim.check_pow env mc bad)
    end
  end;
  test "original environment unchanged" (aconv (Env.quote_env env) original);
  test "no new HOL axioms" (axioms()=l4_primitive_axioms_before);
  print_endline("HOL_PRIMITIVE_POW_"^String.uppercase_ascii phase^"_TESTS_PASSED "^string_of_int !count);;

let l4_primitive_shift_left_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let module Prim = Lean4hol_primitive in
  let phase=match Sys.getenv_opt "HOL_PRIMITIVE_SHIFT_LEFT_PHASE" with
    | None -> "body"
    | Some ("body" | "factory" | "named" | "base" | "step" | "order" |
            "output" | "replay" | "missing" | "checks" | "equations" as p) -> p
    | Some _ -> failwith "unknown HOL_PRIMITIVE_SHIFT_LEFT_PHASE" in
  let count=ref 0 in
  let test label ok =
    if not ok then failwith("primitive shiftLeft regression: "^label);
    incr count; print_endline("shiftLeft "^phase^" check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function
    | Error {kind=Unsupported;_} | Error {kind=Proof_failure;_} -> test label true
    | Error e -> failwith(label^": unexpected error classification: "^e.message)
    | Ok _ -> failwith("accepted: "^label) in
  let assert_th label tm h =
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv (concl h) tm) in
  test "shiftLeft contract monomorphic type" (type_of(mk_const("l4_prim_shift_left_contract",[]))=
    `:(l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool) ->
      l4_expr -> l4_expr -> l4_expr -> bool`);
  test "header type unchanged" (type_of(mk_const("l4_prim_definition_header",[]))=
    `:l4_name -> l4_name list -> l4_expr -> l4_expr -> bool`);
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and z=Const(Str(nat,"zero"),[]) in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let two=succ(succ z) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let app2 f x y=App(App(f,x),y) in
  let named s=Const(Str(nat,s),[]) in
  let level=Succ Zero in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt nt;base;lam nt(lam nt step);n] in
  let add=lam nt(lam nt(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let mul=lam nt(lam nt(recnat z (app2 (named "add") (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let shift base step=lam nt(lam nt(App(Env.apps (Const(Str(nat,"rec"),[level]))
    [lam nt unary;base;lam nt(lam unary(lam nt step));Bvar 0],Bvar 1))) in
  let identity=lam nt(Bvar 0) in
  let changed_input=App(Bvar 1,app2 (named "mul") two (Bvar 0)) in
  let candidate=shift identity changed_input in
  let declaration suffix value={Env.kind=Env.Definition;name=Str(nat,suffix);
    params=[];typ=binary;value=Some value} in
  let d=declaration "shiftLeft" candidate in
  let block={Env.inductive_name=nat;inductive_level=level;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env0,h0=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  let valid env=node "l4_evalid" [Env.quote_policy env;Env.quote_env env] in
  let j env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let checked env g a b ty=list_mk_comb(j env,
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]) in
  assert_th "canonical Nat environment" (valid env0) h0;
  let fields d=match d.Env.value with
    | Some b -> [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b]
    | None -> failwith "test declaration requires a body" in
  let certify env d =
    let c=get "definition factory" (Prim.check_definition env d) in
    assert_th "raw definition contract" (node "l4_prim_definition_contract"
      (node "l4_edef" [Env.quote_env env]::fields d)) (Prim.definition_raw_theorem c);
    test "factory retains exact declaration" (Prim.definition_declaration c=d); c in
  let admit env d c =
    let env',h=get "primitive admission" (Env.admit_primitive env d (Prim.definition_raw_theorem c)) in
    assert_th "primitive environment" (valid env') h;
    test "admission retains exact Definition" (Env.declarations env'=d::Env.declarations env);
    test "admission retains policy" (aconv (Env.quote_policy env') (Env.quote_policy env)); env' in
  let ad=declaration "add" add in
  let env1=admit env0 ad (certify env0 ad) in
  let md=declaration "mul" mul in
  let env=admit env1 md (certify env1 md) in
  print_endline "HOL_PRIMITIVE_SHIFT_LEFT_CANONICAL_DEPENDENCIES_PASSED";
  let original=Env.quote_env env in
  let eq label env g a b=assert_th label (checked env g a b nt)
    (get label (Env.convert env g a b nt)) in
  if phase="factory" || phase="named" || phase="checks" || phase="equations" then begin
    let d=if phase="named" then
        {d with Env.typ=Pi(Str(Anonymous,"x"),nt,Pi(Str(Anonymous,"n"),nt,nt))}
      else d in
    let c=certify env d in
    let raw=Prim.definition_raw_theorem c in
    assert_th "checked shiftLeft declaration" (node "l4_prim_definition_contract" (j env::fields d))
      (Prim.definition_theorem c);
    let env'=admit env d c in
    if phase="named" then begin
      test "named binders preserved in admission" ((List.hd(Env.declarations env')).Env.typ=d.Env.typ);
      decline "raw certificate cannot substitute anonymous header" (Env.admit_primitive env
        {d with Env.typ=binary} raw)
    end else begin
      if phase<>"checks" then begin
      eq "admitted symbolic zero equation" env' [nt] (app2 (named "shiftLeft") (Bvar 0) z) (Bvar 0);
      eq "admitted symbolic changed-input equation" env' [nt;nt]
        (app2 (named "shiftLeft") (Bvar 1) (succ(Bvar 0)))
        (app2 (named "shiftLeft") (app2 (named "mul") two (Bvar 1)) (Bvar 0));
      end;
      if phase<>"equations" then begin
      let bad=lam nt(lam nt z) in
      assert_th "consumer mutant typing" (checked env [] bad bad binary)
        (get "consumer mutant typing" (Env.check env [] bad binary));
      decline "consumer body substitution" (Env.admit_primitive env {d with Env.value=Some bad} raw);
      List.iter (fun (label,wrong) ->
        decline ("factory "^label) (Prim.check_definition env wrong);
        decline ("consumer "^label) (Env.admit_primitive env wrong raw))
        ["wrong name",{d with Env.name=Str(nat,"gcd")};
         "wrong parameters",{d with Env.params=[Str(Anonymous,"u")]};
         "wrong signature",{d with Env.typ=unary};
         "wrong kind",{d with Env.kind=Env.Quotient Lean4hol_quotient_model.Qtype}];
      decline "ordinary protected admission" (Env.admit env d);
      decline "raw certificate environment replay" (Env.admit_primitive env' d raw);
      let with_hyp=ADD_ASSUM `F` raw in
      test "hypothesis mutant keeps exact conclusion" (aconv (concl with_hyp) (concl raw));
      decline "nonempty theorem hypotheses" (Env.admit_primitive env d with_hyp);
      decline "unproved consumer certificate" (Env.admit_primitive env d TRUTH);
      test "factory zero fuel" (match Prim.check_definition ~fuel:0 env d with
        | Error {kind=Resource;_} -> true | _ -> false);
      test "consumer zero fuel" (match Env.admit_primitive ~fuel:0 env d raw with
        | Error {kind=Resource;_} -> true | _ -> false)
      end
    end
  end else if phase="missing" then begin
    decline "missing canonical add and mul" (Prim.check_definition env0 d);
    decline "missing canonical mul" (Prim.check_definition env1 d)
  end else begin
    let ac=get "canonical add recertification" (Prim.check_add env (named "add")) in
    let mc=get "canonical mul recertification" (Prim.check_mul env ac (named "mul")) in
    assert_th "mul dependency includes add" (node "l4_prim_mul_contract"
      [j env;quote_expr(named "add");quote_expr(named "mul")]) (Prim.mul_theorem mc);
    if phase="body" || phase="replay" then begin
      let sc=get "shiftLeft symbolic body certificate" (Prim.check_shift_left env mc candidate) in
      let h=Prim.shift_left_theorem sc in
      test "shiftLeft body retained" (Prim.shift_left_body sc=candidate);
      assert_th "shiftLeft contract" (node "l4_prim_shift_left_contract"
        [j env;quote_expr(named "add");quote_expr(named "mul");quote_expr candidate]) h;
      if phase="body" then begin
        let mh=MATCH_MP l4_prim_shift_left_dependency h in
        assert_th "shiftLeft carries mul" (concl(Prim.mul_theorem mc)) mh;
        assert_th "shiftLeft transitively carries add" (concl(Prim.add_theorem ac))
          (MATCH_MP l4_prim_mul_dependency mh);
        let parts=CONJUNCTS(REWRITE_RULE
          [l4_prim_shift_left_contract;l4_prim_binary;l4_prim_unary;l4_prim_nat;
           l4_prim_two;l4_prim_one;l4_prim_succ;l4_prim_zero;l4_nat_name] h) in
        assert_th "shiftLeft canonical typing" (checked env [] candidate candidate binary) (List.nth parts 1);
        assert_th "shiftLeft arbitrary zero equation"
          (checked env [nt] (app2 candidate (Bvar 0) z) (Bvar 0) nt) (List.nth parts 2);
        assert_th "shiftLeft arbitrary changed-input equation"
          (checked env [nt;nt] (app2 candidate (Bvar 1) (succ(Bvar 0)))
            (app2 candidate (app2 (named "mul") two (Bvar 1)) (Bvar 0)) nt) (List.nth parts 3);
        test "body zero fuel" (match Prim.check_shift_left ~fuel:0 env mc candidate with
          | Error {kind=Resource;_} -> true | _ -> false)
      end else begin
        let aux={Env.kind=Env.Definition;name=Str(Anonymous,"ShiftLeftDependencyReplay");
          params=[];typ=unary;value=Some identity} in
        let env',h'=get "valid environment extension" (Env.admit env aux) in
        assert_th "valid replay target" (valid env') h';
        decline "mul certificate environment replay" (Prim.check_shift_left env' mc candidate);
        decline "transitive add certificate environment replay" (Prim.check_mul env' ac (named "mul"))
      end
    end else begin
      let bad=if phase="base" then shift (lam nt z) changed_input
        else if phase="step" then shift identity (App(Bvar 1,Bvar 0))
        else if phase="order" then shift identity (App(Bvar 1,app2 (named "mul") (Bvar 0) two))
        else shift identity (app2 (named "mul") two (App(Bvar 1,Bvar 0))) in
      assert_th "mutant typing positive gate" (checked env [] bad bad binary)
        (get "mutant typing" (Env.check env [] bad binary));
      if phase<>"base" then
        eq "mutant zero equation positive gate" env [nt] (app2 bad (Bvar 0) z) (Bvar 0);
      decline "symbolic shiftLeft mutation" (Prim.check_shift_left env mc bad)
    end
  end;
  test "original environment unchanged" (aconv (Env.quote_env env) original);
  test "no new HOL axioms" (axioms()=l4_primitive_axioms_before);
  print_endline("HOL_PRIMITIVE_SHIFT_LEFT_"^String.uppercase_ascii phase^
    "_TESTS_PASSED "^string_of_int !count);;

match Sys.getenv_opt "HOL_PRIMITIVE_SUITE" with
| None | Some "factory" -> l4_primitive_factory_tests ()
| Some "body" -> l4_primitive_contract_tests ()
| Some "body-projections" -> l4_primitive_contract_tests ~projections:true ()
| Some "beq" -> l4_primitive_bool_tests "beq"
| Some "ble" -> l4_primitive_bool_tests "ble"
| Some "pow" -> l4_primitive_pow_tests ()
| Some "shift-left" -> l4_primitive_shift_left_tests ()
| Some _ -> failwith "unknown HOL_PRIMITIVE_SUITE";;
