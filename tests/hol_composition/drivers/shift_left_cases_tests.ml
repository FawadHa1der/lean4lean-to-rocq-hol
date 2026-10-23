(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let shift_left_axioms_before=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/derived_shift_left.ml";;
needs "hol/primitive_validation.ml";;
needs "hol/shift_left_evaluation_probe.ml";;

let run_shift_left_cases phase =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Shift=Lean4hol_derived_shift_left in
  let module Prim=Lean4hol_primitive in
  let count=ref 0 in
  let test label yes=if not yes then failwith("shiftLeft "^phase^": "^label) else
    (incr count;Printf.printf "SHIFT_LEFT_ASSERT %s %s\n%!" phase label) in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let decline label=function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_}->test label true
    | Error e->failwith(label^": unexpected error "^e.message)
    | Ok _->failwith(label^": accepted") in
  let exact label expected h=
    test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" exact") (aconv(concl h) expected) in
  let nn=Str(Anonymous,"Nat") in
  let nat=Const(nn,[]) and zero=Const(Str(nn,"zero"),[])
  and successor=Const(Str(nn,"succ"),[]) in
  let unary=Pi(Anonymous,nat,nat) in
  let binary=Pi(Anonymous,nat,unary) in
  let lam a b=Lam(Anonymous,a,b) in
  let succ x=App(successor,x) in
  let app2 b x y=App(App(b,x),y) in
  let recnat base step n=Env.apps(Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat nat;base;lam nat(lam nat step);n] in
  let add=lam nat(lam nat(recnat(Bvar 1)(succ(Bvar 0))(Bvar 0))) in
  let mul=lam nat(lam nat(recnat zero(app2 add(Bvar 0)(Bvar 3))(Bvar 0))) in
  let identity=lam nat(Bvar 0) in
  let shift base step=lam nat(lam nat(App(Env.apps(Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat unary;base;lam nat(lam unary(lam nat step));Bvar 0],Bvar 1))) in
  let body=shift identity(App(Bvar 1,app2 mul(succ(succ zero))(Bvar 0))) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,valid=get "canonical Nat" (Env.admit_inductive Env.empty block) in
  let before_env=Env.quote_env env and before_policy=Env.quote_policy env in
  let judgment env=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
  let checked env g e f ty=list_mk_comb(judgment env,
    [quote_context g;quote_expr e;quote_expr f;quote_expr ty]) in
  exact "canonical environment" (node "l4_evalid" [before_policy;before_env]) valid;
  let prepare env g a m b=get "ordinary contextual preparation" (Shift.prepare env g ~add:a ~mul:m b) in
  let relative env g=
    let delta=`delta:l4_expr list` in
    mk_abs(delta,node "l4_checked" [Env.quote_policy env;Env.quote_env env;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;quote_context g])]) in
  let law env g a m b=node "l4_prim_shift_left_contract"
    [relative env g;quote_expr a;quote_expr m;quote_expr b] in
  let evaluate env g b cert left shift answer=
    let result,h=get "derived evaluation" (Shift.evaluate cert left shift) in
    test "literal answer" (result=Natlit answer);
    exact "literal checked equality" (checked env g(app2 b(Natlit left)(Natlit shift)) result nat) h;
    test "tampered output not certified" (not(aconv(concl h)
      (checked env g(app2 b(Natlit left)(Natlit shift))(succ result) nat)));
    h in
  (match phase with
  | "empty" | "nat-context" | "dependent-context" ->
    let g=if phase="empty" then [] else if phase="nat-context" then [nat]
      else [Bvar 0;Sort(Succ Zero)] in
    let cert=prepare env g add mul body in
    test "exact body retained" (Shift.body cert=body);
    test "exact context retained" (Shift.context cert=g);
    exact "full contextual checked contract" (law env g add mul body)(Shift.contract cert);
    List.iter(fun(left,n,answer)->ignore(evaluate env g body cert left n answer))
      ["0","0","0";"3","0","3";"3","1","6";"13","7","1664";
       "1","128","340282366920938463463374607431768211456"];
    let raw_law=MATCH_MP(SPECL [Env.quote_policy env;Env.quote_env env;quote_context g;
      quote_expr add;quote_expr mul;quote_expr body] l4_shift_left_context_checked_raw)(Shift.contract cert) in
    let raw h=List.nth(CONJUNCTS(REWRITE_RULE[l4_checked]h))2 in
    let scope e=prove(node "l4_scoped" [quote_expr e;`0`],REWRITE_TAC[l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    let typing gamma e ty=raw(get "typed theorem premise" (Env.check env gamma e ty)) in
    let premises=[scope add;scope mul;scope body;raw_law;
      typing g nat(Sort(Succ Zero));typing(nat::g)nat(Sort(Succ Zero));
      typing g zero nat;typing g successor unary] in
    let theorem=REWRITE_RULE[l4_nat_name](SPECL [Env.quote_env env;quote_context g;
      quote_expr add;quote_expr mul;quote_expr body]l4_edef_shift_left_evaluation_in_context) in
    let all=MP theorem(end_itlist CONJ premises) in
    test "specialized contextual theorem closed" (hyp all=[] && frees(concl all)=[]);
    List.iteri(fun omitted _->test "every exact typed or scope premise required"
      (try ignore(MP theorem(end_itlist CONJ(List.filteri(fun i _->i<>omitted)premises)));false
       with Failure _->true))premises;
    test "assumed full premise remains conditional"
      (hyp(MP theorem(ASSUME(fst(dest_imp(concl theorem)))))<>[]);
    let replay=REWRITE_RULE[l4_nat_name](SPECL [Env.quote_env env;quote_context(nat::g);
      quote_expr add;quote_expr mul;quote_expr body]l4_edef_shift_left_evaluation_in_context) in
    test "no arbitrary weakening of contextual contract"
      (try ignore(MP replay(end_itlist CONJ premises));false with Failure _->true);
    let symbolic=List.nth(CONJUNCTS(REWRITE_RULE
      [l4_prim_shift_left_contract;APPEND;l4_prim_nat;l4_prim_binary;l4_prim_unary;
       l4_prim_two;l4_prim_one;l4_prim_zero;l4_prim_succ;l4_nat_name]raw_law))3 in
    let _,args=strip_comb(concl symbolic) in
    let e,f,ty=match args with [_;_;e;f;ty]->e,f,ty|_->failwith "symbolic step shape" in
    let value=quote_expr(Natlit "3") in
    let inst=SPECL [Env.quote_env env;quote_context(nat::g);quote_expr nat;`L4Succ L4Zero`;
      e;f;ty;value] l4_edef_instantiation in
    let domain=List.nth premises 5 in
    let hv=typing(nat::g)(Natlit "3")nat in
    let instantiated=MP inst(CONJ domain(CONJ symbolic hv)) in
    exact "typed substitution in the nonempty suffix context"
      (node "l4_edef" [Env.quote_env env;quote_context(nat::g);
        node "l4_inst" [value;e];node "l4_inst" [value;f];node "l4_inst" [value;ty]]) instantiated;
    List.iter(fun(label,hd,he,hvalue)->test label
      (try ignore(MP inst(CONJ hd(CONJ he hvalue)));false with Failure _->true))
      ["substitution needs domain typing in exact suffix",List.nth premises 4,symbolic,hv;
       "substitution needs a typed Nat argument",domain,symbolic,domain;
       "substitution binds exact argument",domain,symbolic,typing(nat::g)(Natlit "0")nat;
       "substitution needs symbolic equality, not just formation",domain,domain,hv]
  | "large-and-budget" ->
    let cert=prepare env [] add mul body in
    List.iter(fun(left,n,answer)->ignore(evaluate env [] body cert left n answer))
      ["1","256","115792089237316195423570985008687907853269984665640564039457584007913129639936";
       "9876543210987654321098765432109876543210","0","9876543210987654321098765432109876543210";
       "9876543210987654321098765432109876543210","64",
       "182190064946022818019751609161975160916179297085125149327360";
       "0","9999999999999999999999999999999999999999","0"];
    test "huge positive shift is resource decline before exponent allocation"
      (match Shift.evaluate cert "1" (String.make 100 '9') with Error {kind=Resource;_}->true|_->false);
    test "explicit small output budget enforced"
      (match Shift.evaluate ~max_output_bits:64 cert "1" "100" with Error {kind=Resource;_}->true|_->false);
    test "invalid budget refused" (match Shift.evaluate ~max_output_bits:max_int cert "1" "1" with
      Error {kind=Invalid_input;_}->true|_->false);
    List.iter(fun s->test "malformed input refused"
      (match Shift.evaluate cert s "1" with Error {kind=Invalid_input;_}->true|_->false))
      ["";"00";"-1";"1.2";"1x"];
    test "zero fuel explicit" (match Shift.evaluate ~fuel:0 cert "1" "1" with
      Error {kind=Resource;_}->true|_->false);
    let proof=get "checked claimed result" (Shift.check_result cert "13" "7" "1664") in
    exact "claimed output theorem" (checked env [] (app2 body(Natlit "13")(Natlit "7"))(Natlit "1664") nat) proof;
    decline "tampered literal output" (Shift.check_result cert "13" "7" "1665");
    test "malformed claimed output" (match Shift.check_result cert "13" "7" "01664" with
      Error {kind=Invalid_input;_}->true|_->false)
  | "contract-guards" ->
    let cert=prepare env [] add mul body in
    let h=Shift.contract cert in
    ignore(get "exact authenticated contract accepted" (Shift.prepare_from_contract env [] ~add ~mul body h));
    List.iter(fun(label,wrong)->decline label (Shift.prepare_from_contract env [] ~add ~mul body wrong))
      ["hypothesis on exact conclusion",ADD_ASSUM `T` h;
       "assumed contract",ASSUME(concl h);
       "free variable theorem",REFL `open_evidence:bool`;
       "unrelated closed theorem",TRUTH;
       "body typing is not full contract",MATCH_MP l4_prim_shift_left_body_typed h;
       "dependency is not full contract",MATCH_MP l4_prim_shift_left_dependency h];
    let raw=MATCH_MP(SPECL [Env.quote_policy env;Env.quote_env env;quote_context [];
      quote_expr add;quote_expr mul;quote_expr body]l4_shift_left_context_checked_raw)h in
    decline "raw contract cannot impersonate checked contract"
      (Shift.prepare_from_contract env [] ~add ~mul body raw);
    decline "wrong add dependency" (Shift.prepare_from_contract env [] ~add:body ~mul body h);
    decline "wrong mul dependency" (Shift.prepare_from_contract env [] ~add ~mul:add body h);
    decline "wrong body" (Shift.prepare_from_contract env [] ~add ~mul add h);
    decline "wrong context" (Shift.prepare_from_contract env [nat] ~add ~mul body h);
    let later,_=get "environment extension" (Env.admit env {Env.kind=Env.Definition;
      name=Str(Anonymous,"ShiftExtra");params=[];typ=nat;value=Some zero}) in
    decline "wrong environment" (Shift.prepare_from_contract later [] ~add ~mul body h);
    let policy=get "unused policy" (Env.with_axioms
      [{Env.axiom_name=Str(Anonymous,"ShiftGrant");axiom_params=[];axiom_type=nat}]) in
    let changed_policy,_=get "same Nat different policy" (Env.admit_inductive policy block) in
    test "policy control same entries" (aconv(Env.quote_env changed_policy)(Env.quote_env env));
    decline "wrong policy" (Shift.prepare_from_contract changed_policy [] ~add ~mul body h)
  | "allocation-controls" ->
    let module Probe=Shift_left_evaluation_probe in
    let module Budget=Lean4hol_shift_left_budget in
    let cert=prepare env [] add mul body in
    let pc=get "observed evaluator prepared from full checked contract"
      (Probe.prepare_from_contract env [] ~add ~mul body(Shift.contract cert)) in
    let reset ()=shift_left_probe_numeric_inputs:=[];
      shift_left_probe_require_zero:=false;shift_left_probe_forbid_numeric:=false in
    let enormous=String.make 1000 '9' in
    reset();shift_left_probe_require_zero:=true;
    let result,h=get "zero with enormous shift at one-bit cap"
      (Probe.evaluate ~max_output_bits:1 pc "0" enormous) in
    test "zero result even for enormous exponent" (result=Natlit "0");
    exact "huge exponent retained in exact source, not exponentiated"
      (checked env [] (app2 body(Natlit "0")(Natlit enormous))(Natlit "0")nat) h;
    test "numeric converter sees only zero, never EXP"
      (!shift_left_probe_numeric_inputs=[`0`]);
    reset();shift_left_probe_forbid_numeric:=true;
    let no_arithmetic label kind outcome=
      test label (match outcome with Error e->e.kind=kind | Ok _->false);
      test (label^" no numeral evaluation") (!shift_left_probe_numeric_inputs=[]) in
    no_arithmetic "nonzero huge exponent resource decline" Resource
      (Probe.evaluate pc "1" enormous);
    no_arithmetic "actual result fits but conservative bound declines" Resource
      (Probe.evaluate ~max_output_bits:4 pc "1" "1");
    no_arithmetic "one-bit true result conservatively declined" Resource
      (Probe.evaluate ~max_output_bits:1 pc "1" "0");
    List.iter(fun bad->
      no_arithmetic "malformed left is invalid, not exhausted" Invalid_input(Probe.evaluate pc bad "0");
      no_arithmetic "malformed shift is invalid, not exhausted" Invalid_input(Probe.evaluate pc "1" bad);
      no_arithmetic "zero does not bypass malformed shift" Invalid_input(Probe.evaluate pc "0" bad))
      ["";"00";"01";"-0";"-1";"+1";" 1";"1 ";"1\n";"1.0";"1e3";"0x10";"1x"];
    no_arithmetic "invalid cap distinct from resource decline" Invalid_input
      (Probe.evaluate ~max_output_bits:0 pc "1" "1");
    no_arithmetic "oversized input text bounded before decimal processing" Resource
      (Probe.evaluate pc "0" (String.make 16385 '9'));
    reset();
    let result,h=get "same small result within larger conservative bound"
      (Probe.evaluate ~max_output_bits:5 pc "1" "1") in
    test "canonical decimal positive result" (result=Natlit "2");
    exact "positive result still needs a proof"
      (checked env [] (app2 body(Natlit "1")(Natlit "1"))(Natlit "2")nat) h;
    test "allocation permission is not a claimed-result verdict"
      (Budget.check ~max_output_bits:4096 "13" "7"=Budget.Allowed);
    decline "allowed allocation cannot certify a tampered answer"
      (Probe.check_result pc "13" "7" "1665");
    ignore(get "correct answer still certified"(Probe.check_result pc "13" "7" "1664"));
    reset()
  | "primitive-import" ->
    let ac=get "existing add authentication" (Prim.check_add env add) in
    let mc=get "existing mul authentication" (Prim.check_mul env ac mul) in
    let sc=get "existing shiftLeft authentication" (Prim.check_shift_left env mc body) in
    let target=law env [] add mul body in
    let equation=REWRITE_CONV [APPEND_NIL;ETA_AX] target in
    let h=EQ_MP(SYM equation)(Prim.shift_left_theorem sc) in
    exact "imported full primitive contract" target h;
    let cert=get "prepare from existing authenticated contract"
      (Shift.prepare_from_contract env [] ~add ~mul body h) in
    ignore(evaluate env [] body cert "7" "3" "56")
  | "authentication" ->
    let bad=shift identity(App(Bvar 1,Bvar 0)) in
    exact "wrong-step body independently typed" (checked env [] bad bad binary)
      (get "wrong body positive typing" (Env.check env [] bad binary));
    decline "typed wrong-step shift refused" (Shift.prepare env [] ~add ~mul bad);
    let bad_add=lam nat(lam nat(recnat zero(succ(Bvar 0))(Bvar 0))) in
    decline "poisoned addition dependency refused" (Shift.prepare env [] ~add:bad_add ~mul body);
    decline "poisoned multiplication dependency refused" (Shift.prepare env [] ~add ~mul:add body);
    let g=[binary] in
    exact "open candidate independently typed" (checked env g(Bvar 0)(Bvar 0)binary)
      (get "open positive typing" (Env.check env g(Bvar 0)binary));
    decline "scopedness cannot be dropped" (Shift.prepare env g ~add ~mul(Bvar 0));
    decline "missing environment" (Shift.prepare Env.empty [] ~add ~mul body);
    test "preparation zero fuel explicit" (match Shift.prepare ~fuel:0 env [] ~add ~mul body with
      Error {kind=Resource;_}->true|_->false)
  | "wrappers" ->
    let name=Str(Anonymous,"DerivedShift") in
    let named_env,_=get "ordinary named shift" (Env.admit env
      {Env.kind=Env.Definition;name;params=[];typ=binary;value=Some body}) in
    let named=Const(name,[]) in
    let g=[Bvar 0;Sort(Succ Zero)] in
    List.iter(fun source->
      let cert=prepare named_env g add mul source in
      test "named or wrapped source retained" (Shift.body cert=source);
      ignore(evaluate named_env g source cert "5" "2" "20"))
      [named;Let(Anonymous,binary,named,Bvar 0)];
    decline "named body missing in earlier environment" (Shift.prepare env [] ~add ~mul named)
  | _->failwith "unknown shiftLeft test phase");
  test "original environment unchanged" (aconv(Env.quote_env env)before_env);
  test "original policy unchanged" (aconv(Env.quote_policy env)before_policy);
  test "29 native clauses unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "11 admission clauses unchanged"
    (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=shift_left_axioms_before);
  Printf.printf "SHIFT_LEFT_DERIVED_PASSED %s %d\n%!" phase !count;;

run_shift_left_cases(Sys.getenv "SHIFT_LEFT_PHASE");;
