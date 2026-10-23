(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let add_body_axioms_before=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/primitive_validation.ml";;
needs "hol/add_body_probe.ml";;
needs "hol/add_body_baseline.ml";;

let add_body_tests phase =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Prim=Lean4hol_primitive in
  let module Probe=Add_body_probe in
  let module Old=Add_body_baseline in
  let count=ref 0 in
  let test label yes=if not yes then failwith("add-body: "^label) else
    (incr count; Printf.printf "ADD_BODY_ASSERT %s %s\n%!" phase label) in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let exact label expected h=
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv(concl h) expected) in
  let decline label=function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_}->test label true
    | Error e->failwith(label^": unexpected error "^e.message)
    | Ok _->failwith(label^": accepted") in
  let refuses label f=try ignore(f());failwith(label^": accepted") with
    | Stop {kind=Proof_failure;_}->test label true in
  let nat=Str(Anonymous,"Nat") in
  let nt=Const(nat,[]) and zero=Const(Str(nat,"zero"),[]) in
  let lam e=Lam(Anonymous,nt,e) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nt nt in
  let binary=pi nt unary in
  let succ e=App(Const(Str(nat,"succ"),[]),e) in
  let app2 b x y=App(App(b,x),y) in
  let recnat base step n=Env.apps (Const(Str(nat,"rec"),[Succ Zero]))
    [lam nt;base;lam(lam step);n] in
  let add=lam(lam(recnat (Bvar 1) (succ(Bvar 0)) (Bvar 0))) in
  let bad_base=lam(lam(recnat zero (succ(Bvar 0)) (Bvar 0))) in
  let bad_step=lam(lam(recnat (Bvar 1) (Bvar 0) (Bvar 0))) in
  let pred=lam(recnat zero (Bvar 1) (Bvar 0)) in
  let block={Env.inductive_name=nat;inductive_level=Succ Zero;
    constructors=[Str(nat,"zero"),[];Str(nat,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,hvalid=get "Nat admission" (Env.admit_inductive Env.empty block) in
  let initial_env=Env.quote_env env and initial_policy=Env.quote_policy env in
  exact "Nat environment" (node "l4_evalid" [initial_policy;initial_env]) hvalid;
  let checked env g a b ty=node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr a;quote_expr b;quote_expr ty] in
  let contract env b=node "l4_prim_add_contract"
    [node "l4_checked" [Env.quote_policy env;Env.quote_env env];quote_expr b] in
  let decl ty b={Env.kind=Env.Definition;name=Str(nat,"add");params=[];typ=ty;value=Some b} in
  let fields d=match d.Env.value with Some b->
    [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
     quote_expr d.Env.typ;quote_expr b] | None->failwith "missing test body" in
  let definition env d=node "l4_prim_definition_contract"
    (node "l4_checked" [Env.quote_policy env;Env.quote_env env]::fields d) in
  let raw_definition env d=node "l4_prim_definition_contract"
    (node "l4_edef" [Env.quote_env env]::fields d) in
  let named=Pi(Str(Anonymous,"x"),nt,Pi(Str(Anonymous,"y"),nt,nt)) in
  let reset ()=add_body_probe_checks:=[];add_body_probe_converts:=[];
    add_body_probe_conversion_override:=None in
  let factory label env d=
    let c=get label (Prim.check_definition env d) in
    exact (label^" checked") (definition env d) (Prim.definition_theorem c);
    exact (label^" raw") (raw_definition env d) (Prim.definition_raw_theorem c);
    test (label^" original declaration") (Prim.definition_declaration c=d); c in
  (match phase with
  | "guards" ->
    let ac=get "authenticated add" (Prim.check_add env add) in
    let hop=Prim.add_theorem ac in
    exact "full authenticated contract" (contract env add) hop;
    reset();
    exact "reuse body theorem" (checked env [] add add binary)
      (Probe.add_body_typing 100000 env add binary hop);
    test "canonical reuse performs no check or conversion"
      (!add_body_probe_checks=[] && !add_body_probe_converts=[]);
    exact "canonical reuse needs no additional fuel" (checked env [] add add binary)
      (Probe.add_body_typing 0 env add binary hop);
    let body=REWRITE_RULE [l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_nat_name]
      (CONJUNCT1(REWRITE_RULE [l4_prim_add_contract] hop)) in
    refuses "body typing alone is not full contract"
      (fun()->Probe.add_body_typing 100000 env add binary body);
    refuses "wrong contract body"
      (fun()->Probe.add_body_typing 100000 env bad_step binary hop);
    refuses "contract with added assumption"
      (fun()->Probe.add_body_typing 100000 env add binary (ADD_ASSUM `T` hop));
    refuses "exact assumed contract"
      (fun()->Probe.add_body_typing 100000 env add binary (ASSUME(concl hop)));
    refuses "free variables even in hypothesis-free theorem"
      (fun()->Probe.add_body_typing 100000 env add binary (REFL `open_term:bool`));
    refuses "unrelated closed theorem"
      (fun()->Probe.add_body_typing 100000 env add binary TRUTH);
    let aux={Env.kind=Env.Definition;name=Str(Anonymous,"AuxAddBody");params=[];
      typ=unary;value=Some pred} in
    let extended,_=get "ordinary extension" (Env.admit env aux) in
    refuses "changed environment"
      (fun()->Probe.add_body_typing 100000 extended add binary hop);
    refuses "missing Nat environment"
      (fun()->Probe.add_body_typing 100000 Env.empty add binary hop);
    let policy=get "different policy" (Env.with_axioms
      [{Env.axiom_name=Str(Anonymous,"UnusedAddBodyGrant");axiom_params=[];axiom_type=nt}]) in
    let policy_env,_=get "Nat under different policy" (Env.admit_inductive policy block) in
    test "different policy same entries" (aconv(Env.quote_env policy_env) initial_env);
    refuses "changed policy"
      (fun()->Probe.add_body_typing 100000 policy_env add binary hop);
    reset();
    exact "named type conversion" (checked env [] add add named)
      (Probe.add_body_typing 100000 env add named hop);
    test "named reuse has no redundant body check" (!add_body_probe_checks=[]);
    test "named reuse converts binary to exact declared type"
      (!add_body_probe_converts=[([],binary,named,Sort(Succ Zero),Some 100000)]);
    test "conversion fuel exhaustion is retained" (try
      ignore(Probe.add_body_typing 0 env add named hop);false with Stop {kind=Resource;_}->true);
    reset();
    let wrong=get "wrong target positive formation" (Env.check env [] unary (Sort(Succ Zero))) in
    exact "wrong signature independently formed" (checked env [] unary unary (Sort(Succ Zero))) wrong;
    refuses "well formed incompatible type"
      (fun()->Probe.add_body_typing 100000 env add unary hop);
    let genuine=get "genuine named conversion"
      (Env.convert env [] binary named (Sort(Succ Zero))) in
    let assumption=ADD_ASSUM `T` genuine in
    List.iter(fun(label,h)->add_body_probe_conversion_override:=Some h;
      refuses label (fun()->Probe.add_body_typing 100000 env add named hop))
      ["conversion conclusion must match",wrong;
       "conversion hypotheses forbidden",assumption;
       "body typing cannot impersonate conversion",body];
    reset()
  | "canonical" | "named" ->
    let signature=if phase="canonical" then binary else named in
    let d=decl signature add in
    let c=factory "production factory" env d in
    let old=get "baseline factory" (Old.check_definition env d) in
    exact "baseline checked theorem" (definition env d) (Old.definition_theorem old);
    exact "baseline raw theorem" (raw_definition env d) (Old.definition_raw_theorem old);
    test "old and new exact checked conclusion"
      (aconv(concl(Prim.definition_theorem c))(concl(Old.definition_theorem old)));
    test "old and new exact raw conclusion"
      (aconv(concl(Prim.definition_raw_theorem c))(concl(Old.definition_raw_theorem old)));
    reset();
    let pc=get "observed candidate factory" (Probe.check_definition env d) in
    exact "observed candidate checked" (definition env d) (Probe.definition_theorem pc);
    test "one full body check during authentication only"
      (List.filter(fun(g,b,t)->g=[] && b=add && t=binary) !add_body_probe_checks=[([],add,binary)]);
    test "type formation still checked"
      (List.mem([],signature,Sort(Succ Zero)) !add_body_probe_checks);
    test "no other checker call from factory"
      (List.length !add_body_probe_checks=2);
    test "base authentication still required"
      (List.mem([nt],app2 add (Bvar 0) zero,Bvar 0,nt,Some 100000) !add_body_probe_converts);
    test "step authentication still required"
      (List.mem([nt;nt],app2 add (Bvar 1) (succ(Bvar 0)),
        succ(app2 add (Bvar 1) (Bvar 0)),nt,Some 100000) !add_body_probe_converts);
    test "only named signatures add a type-conversion search"
      (List.length !add_body_probe_converts=(if phase="canonical" then 2 else 3));
    if phase="canonical" then begin
      let pd={d with Env.name=Str(nat,"pred");typ=unary;value=Some pred} in
      let fresh=factory "non-add pred production" env pd in
      let prior=get "non-add pred baseline" (Old.check_definition env pd) in
      test "non-add raw theorem preserved" (aconv
        (concl(Prim.definition_raw_theorem fresh))(concl(Old.definition_raw_theorem prior)))
    end else begin
      let bodyname=Str(Anonymous,"NamedSourceAdd") in
      let named_env,_=get "ordinary named body" (Env.admit env
        {d with Env.name=bodyname;typ=binary}) in
      ignore(factory "named body and named binders" named_env (decl named (Const(bodyname,[]))));
      ignore(factory "let wrapper body" env (decl named (Let(Anonymous,binary,add,Bvar 0))))
    end
  | "authentication" ->
    let d=decl binary add in
    ignore(factory "positive authentication gate" env d);
    List.iter(fun(label,b)->
      exact (label^" independent typing") (checked env [] b b binary)
        (get label (Env.check env [] b binary));
      decline (label^" full contract refused") (Prim.check_add env b);
      decline (label^" factory refused") (Prim.check_definition env {d with Env.value=Some b}))
      ["wrong base",bad_base;"wrong step",bad_step];
    exact "wrong-step body still satisfies base law"
      (checked env [nt] (app2 bad_step (Bvar 0) zero) (Bvar 0) nt)
      (get "wrong-step base positive gate"
        (Env.convert env [nt] (app2 bad_step (Bvar 0) zero) (Bvar 0) nt));
    decline "independent wrong-step law refusal" (Env.convert env [nt;nt]
      (app2 bad_step (Bvar 1) (succ(Bvar 0)))
      (succ(app2 bad_step (Bvar 1) (Bvar 0))) nt);
    exact "wrong-base body still satisfies step law"
      (checked env [nt;nt] (app2 bad_base (Bvar 1) (succ(Bvar 0)))
        (succ(app2 bad_base (Bvar 1) (Bvar 0))) nt)
      (get "wrong-base step positive gate" (Env.convert env [nt;nt]
        (app2 bad_base (Bvar 1) (succ(Bvar 0)))
        (succ(app2 bad_base (Bvar 1) (Bvar 0))) nt));
    decline "independent wrong-base law refusal"
      (Env.convert env [nt] (app2 bad_base (Bvar 0) zero) (Bvar 0) nt);
    List.iter(fun(label,wrong)->decline label (Prim.check_definition env wrong))
      ["wrong primitive name",{d with Env.name=Str(nat,"gcd")};
       "nonempty parameters",{d with Env.params=[Str(Anonymous,"u")]};
       "wrong signature",{d with Env.typ=unary};
       "wrong definition kind",{d with Env.kind=Env.Theorem};
       "erased illtyped body",{d with Env.value=Some(Let(Anonymous,nt,Sort Zero,add))}];
    decline "missing primitive environment" (Prim.check_definition Env.empty d);
    let alias=Str(Anonymous,"BinaryAlias") in
    let alias_env,_=get "type alias admission" (Env.admit env
      {Env.kind=Env.Definition;name=alias;params=[];typ=Sort(Succ Zero);value=Some binary}) in
    let alias_ty=Const(alias,[]) in
    exact "definition alias independently types body" (checked alias_env [] add add alias_ty)
      (get "alias positive typing" (Env.check alias_env [] add alias_ty));
    decline "header still requires canonical signature"
      (Prim.check_definition alias_env (decl alias_ty add));
    test "missing body classified invalid input" (match Prim.check_definition env {d with Env.value=None} with
      Error {kind=Invalid_input;_}->true | _->false);
    test "public zero fuel stays resource" (match Prim.check_definition ~fuel:0 env d with
      Error {kind=Resource;_}->true | _->false)
  | "admission" ->
    let d=decl binary add in
    let c=factory "admission factory gate" env d in
    let raw=Prim.definition_raw_theorem c in
    let admitted,valid=get "primitive admission" (Env.admit_primitive env d raw) in
    exact "admitted environment" (node "l4_evalid"
      [Env.quote_policy admitted;Env.quote_env admitted]) valid;
    exact "retained full definition contract" (raw_definition env d) raw;
    let actual=Const(d.Env.name,[]) in
    exact "admitted body ordinary typing" (checked admitted [] actual actual binary)
      (get "admitted ordinary typing" (Env.check admitted [] actual binary));
    exact "admitted small computation"
      (checked admitted [] (app2 actual (Natlit "2") (Natlit "1")) (Natlit "3") nt)
      (get "admitted small computation" (Env.convert admitted []
        (app2 actual (Natlit "2") (Natlit "1")) (Natlit "3") nt));
    List.iter(fun(label,wrong)->decline label (Env.admit_primitive env wrong raw))
      ["admission body binding",{d with Env.value=Some bad_step};
       "admission exact type binding",{d with Env.typ=named};
       "admission name binding",{d with Env.name=Str(nat,"mul")};
       "admission kind restriction",{d with Env.kind=Env.Opaque};
       "admission parameters binding",{d with Env.params=[Str(Anonymous,"u")]}];
    decline "admission raw versus checked contract" (Env.admit_primitive env d (Prim.definition_theorem c));
    decline "admission rejects conditional exact contract" (Env.admit_primitive env d (ADD_ASSUM `T` raw));
    decline "admission wrong environment" (Env.admit_primitive Env.empty d raw);
    decline "admission stale environment" (Env.admit_primitive admitted d raw);
    let at_current=factory "recertified current environment" admitted d in
    decline "admission freshness remains required"
      (Env.admit_primitive admitted d (Prim.definition_raw_theorem at_current));
    let named_d=decl named add in
    let named_c=factory "named admission gate" env named_d in
    let named_env,named_valid=get "named primitive admission"
      (Env.admit_primitive env named_d (Prim.definition_raw_theorem named_c)) in
    exact "named admitted environment"
      (node "l4_evalid" [Env.quote_policy named_env;Env.quote_env named_env]) named_valid
  | _->failwith "unknown add body phase");
  test "original environment unchanged" (aconv(Env.quote_env env) initial_env);
  test "original policy unchanged" (aconv(Env.quote_policy env) initial_policy);
  test "29 native clauses unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "11 admission clauses unchanged"
    (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=add_body_axioms_before);
  Printf.printf "ADD_BODY_TESTS_PASSED %s %d\n%!" phase !count;;

add_body_tests(Sys.getenv "ADD_BODY_PHASE");;
