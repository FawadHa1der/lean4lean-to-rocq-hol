let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/derived_add.ml";;
let run_derived_add_wrapper_tests () =
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
  let binary=Pi(Anonymous,nat,Pi(Anonymous,nat,nat)) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,_=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let add_name=Str(Anonymous,"Test.add") and bad_name=Str(Anonymous,"Test.bad") in
  let declare env name value=get "typed named definition" (Env.admit env
    {Env.kind=Env.Definition;name;params=[];typ=binary;value=Some value}) in
  let named_env,_=declare env add_name body in
  let named_env,_=declare named_env bad_name bad in
  let named=Const(add_name,[]) and bad_named=Const(bad_name,[]) in
  let wrapped=Let(Anonymous,binary,named,Bvar 0) in
  let gamma=[Bvar 0;Sort(Succ Zero)] in
  let expected source result=node "l4_checked"
    [Env.quote_policy named_env;Env.quote_env named_env;quote_context gamma;
     quote_expr(App(App(source,Natlit "8"),Natlit "13"));quote_expr result;quote_expr nat] in
  List.iter(fun source->
    let cert=get "prepare named or let-wrapped definition" (Add.prepare named_env gamma source) in
    let result,h=get "evaluate named or let-wrapped definition" (Add.evaluate cert "8" "13") in
    test "wrapper retained exactly" (Add.body cert=source);
    test "dependent context retained" (Add.context cert=gamma);
    test "exact answer" (result=Natlit "21");
    test "exact closed checked judgment" (hyp h=[] && aconv(concl h)(expected source result));
    test "different syntactic source not silently substituted"
      (not(aconv(concl h)(expected body result)))
  )[named;wrapped];
  nonresource "typed named wrong-base definition declined" (Add.prepare named_env gamma bad_named);
  nonresource "typed let-wrapped wrong-base definition declined"
    (Add.prepare named_env gamma (Let(Anonymous,binary,bad_named,Bvar 0)));
  nonresource "named definition missing from environment declined" (Add.prepare env [] named);
  test "native rule count unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission count unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "PRIVATE_NAT_EVALUATION_DONE %d_derived_wrapper_assertions unchanged_axioms\n%!" !count;;
run_derived_add_wrapper_tests ();;
exit 0;;
