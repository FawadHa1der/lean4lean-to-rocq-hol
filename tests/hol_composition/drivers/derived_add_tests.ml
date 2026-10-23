let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/derived_add.ml";;
let run_derived_add_service_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Add=Lean4hol_derived_add in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let nonresource label=function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_}->test label true
    | _->failwith(label^": not a nonresource decline") in
  let nn=Str(Anonymous,"Nat") in
  let nat=Const(nn,[]) and zero=Const(Str(nn,"zero"),[])
  and successor=Const(Str(nn,"succ"),[]) in
  let lam x=Lam(Anonymous,nat,x) in
  let recnat base step n=Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat;base;lam(lam step);n] in
  let body=lam(lam(recnat (Bvar 1) (App(successor,Bvar 0)) (Bvar 0))) in
  let bad=lam(lam(recnat zero (App(successor,Bvar 0)) (Bvar 0))) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,_=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let env_later,_=get "different valid environment" (Env.admit env
    {Env.kind=Env.Definition;name=Str(Anonymous,"Extra");params=[];typ=nat;value=Some(Natlit "0")}) in
  let environment_before=Env.quote_env env in
  let stmt environment gamma e result=node "l4_checked"
    [Env.quote_policy environment;Env.quote_env environment;quote_context gamma;
     quote_expr e;quote_expr result;quote_expr nat] in
  List.iter(fun gamma->
    let cert=get "prepare actual contextual addition" (Add.prepare env gamma body) in
    test "body retained" (Add.body cert=body);
    test "context retained" (Add.context cert=gamma);
    test "universal checked theorem closed" (hyp(Add.theorem cert)=[] && frees(concl(Add.theorem cert))=[]);
    List.iter(fun (left,right,answer)->
      let start=Sys.time() in
      let result,h=get "derived literal evaluation" (Add.evaluate cert left right) in
      let elapsed=Sys.time()-.start in
      let call=App(App(body,Natlit left),Natlit right) in
      test "exact literal answer" (result=Natlit answer);
      test "exact closed checked judgment" (hyp h=[] && aconv(concl h)(stmt env gamma call result));
      test "different environment not silently substituted" (not(aconv(concl h)(stmt env_later gamma call result)));
      test "different context not silently substituted" (not(aconv(concl h)(stmt env (nat::gamma) call result)));
      Printf.printf "DERIVED_ADD_MEASUREMENT digits=%d+%d context=%d cpu=%.6f\n%!"
        (String.length left) (String.length right) (List.length gamma) elapsed
    )["0","0","0";"2","3","5";
      "99999999999999999999999999999999999999999999999999","1",
      "100000000000000000000000000000000000000000000000000"];
    List.iter(fun bad->
      test "malformed numeral classified" (match Add.evaluate cert bad "1" with
        | Error {kind=Invalid_input;_}->true | _->false)
    )["";"00";"-1";"1.0";"1x"];
    test "evaluation zero fuel explicit" (match Add.evaluate ~fuel:0 cert "1" "2" with
      | Error {kind=Resource;_}->true | _->false)
  )[[];[Bvar 0;Sort(Succ Zero)]];
  ignore(get "bad-base body independently typed" (Env.check env [] bad (Pi(Anonymous,nat,Pi(Anonymous,nat,nat)))));
  nonresource "typed wrong-base body declined" (Add.prepare env [] bad);
  nonresource "missing Nat environment declined" (Add.prepare Env.empty [] body);
  test "preparation zero fuel explicit" (match Add.prepare ~fuel:0 env [] body with
    | Error {kind=Resource;_}->true | _->false);
  let unary=Pi(Anonymous,nat,nat) in
  let open_gamma=[Pi(Anonymous,nat,unary)] in
  ignore(get "open candidate independently typed" (Env.check env open_gamma (Bvar 0) (Pi(Anonymous,nat,unary))));
  nonresource "open body cannot bypass scopedness" (Add.prepare env open_gamma (Bvar 0));
  test "environment unchanged" (aconv(Env.quote_env env) environment_before);
  test "native rule count unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission count unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "PRIVATE_NAT_EVALUATION_DONE %d_derived_service_assertions unchanged_axioms\n%!" !count;;
run_derived_add_service_tests ();;
exit 0;;
