let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/pred_context_evaluation.ml";;
needs "hol/environment.ml";;
let run_pred_cases () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2 in
  let nn=Str(Anonymous,"Nat") in
  let nat=Const(nn,[]) and zero=Const(Str(nn,"zero"),[])
  and successor=Const(Str(nn,"succ"),[]) in
  let unary=Pi(Anonymous,nat,nat) and lam x=Lam(Anonymous,nat,x) in
  let body=lam(Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat;zero;lam(lam(Bvar 1));Bvar 0]) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,valid=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let notation=[APPEND;l4_prim_unary;l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_nat_name] in
  let certify env g body =
    let qe=Env.quote_env env and qg=quote_context g and qb=quote_expr body in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,node "l4_edef" [qe;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;qg])]) in
    let scope=prove(node "l4_scoped" [qb;`0`],
      REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    let typed=get "pred body typed in actual context" (Env.check env g body unary) in
    let base=get "pred zero equation" (Env.convert env g (App(body,zero)) zero nat) in
    let step=get "pred symbolic successor equation" (Env.convert env (nat::g)
      (App(body,App(successor,Bvar 0))) (Bvar 0) nat) in
    let law=REWRITE_RULE notation(SPECL [relative;qb] l4_prim_pred_contract) in
    let contract=EQ_MP(SYM law)(end_itlist CONJ [raw typed;raw base;raw step]) in
    let hn=get "Nat typed in actual context" (Env.check env g nat (Sort(Succ Zero))) in
    let hz=get "zero typed in actual context" (Env.check env g zero nat) in
    let hs=get "successor typed in actual context" (Env.check env g successor unary) in
    let premises=[scope;contract;raw hn;raw hz;raw hs] in
    let theorem=REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qb] l4_edef_pred_evaluation_in_context) in
    let all=MP theorem(end_itlist CONJ premises) in
    all,theorem,premises,hn in
  let refuses theorem premises=try ignore(MP theorem(end_itlist CONJ premises));false with Failure _->true in
  List.iter(fun g->
    let all,theorem,premises,hn=certify env g body in
    test "closed contextual universal predecessor" (hyp all=[] && frees(concl all)=[]);
    let qe=Env.quote_env env and qp=Env.quote_policy env and qg=quote_context g in
    let context=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] hn)) 1 in
    List.iter(fun text->
      let n=natural text in
      let output=rhs(concl(NUM_REDUCE_CONV(mk_comb(`PRE`,n)))) in
      let call=node "L4App" [quote_expr body;node "L4NatLit" [n]] in
      let result=node "L4NatLit" [output] in
      let expected=node "l4_edef" [qe;qg;call;result;quote_expr nat] in
      let proof=CONV_RULE NUM_REDUCE_CONV(SPEC n all) in
      test "exact raw predecessor result" (aconv(concl proof) expected && hyp proof=[]);
      let expected=node "l4_checked" [qp;qe;qg;call;result;quote_expr nat] in
      let checked=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
        (CONJ valid(CONJ context proof)) in
      test "exact checked predecessor result" (aconv(concl checked) expected && hyp checked=[])
    )["0";"1";"2";"19";"123456789012345678901234567890123456789012345678901234567890"];
    List.iteri(fun omitted _->test "every premise is required"
      (refuses theorem(List.filteri(fun i _->i<>omitted) premises))) premises;
    List.iter(fun (qe,qg,qb)->
      let wrong=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;qg;qb] l4_edef_pred_evaluation_in_context) in
      test "different environment/context/body cannot reuse premises" (refuses wrong premises))
      [`[]:l4_entry list`,qg,quote_expr body;
       qe,quote_context(nat::g),quote_expr body;
       qe,qg,quote_expr(lam zero)];
    let assumed=MP theorem(ASSUME(fst(dest_imp(concl theorem)))) in
    test "assumed law never becomes closed" (hyp assumed<>[])
  )[[];[nat];[Bvar 0;Sort(Succ Zero)]];
  List.iter(fun wrapped->
    let all,_,_,_=certify env [] wrapped in
    test "beta/let wrappers retain actual source" (hyp all=[] && frees(concl all)=[]);
    let checked=get "small result independent ordinary checker" (Env.convert env []
      (App(wrapped,Natlit "4")) (Natlit "3") nat) in
    test "ordinary wrapped result is closed" (hyp checked=[]))
    [App(Lam(Anonymous,unary,Bvar 0),body);Let(Anonymous,unary,body,Bvar 0)];
  let alias=Str(Anonymous,"localPred") in
  let env2,_=get "ordinary named predecessor" (Env.admit env
    {Env.kind=Env.Definition;name=alias;params=[];typ=unary;value=Some body}) in
  let all,_,_,_=certify env2 [nat] (Const(alias,[])) in
  test "named predecessor in extended exact environment" (hyp all=[] && frees(concl all)=[]);
  List.iter(fun bad->
    ignore(get "mutant independently well typed" (Env.check env [] bad unary));
    let outcome=Env.convert env [nat] (App(bad,App(successor,Bvar 0))) (Bvar 0) nat in
    test "typed wrong successor law is nonresource decline" (match outcome with
      | Error {kind=Proof_failure;_}->true | _->false)) [lam zero;lam(Bvar 0)];
  ignore(get "open function independently well typed" (Env.check env [unary] (Bvar 0) unary));
  let closed_false=try ignore(prove(node "l4_scoped" [quote_expr(Bvar 0);`0`],
    REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV));false with Failure _->true in
  test "open function is not silently closed" closed_false;
  test "unchanged native clauses" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "unchanged admission clauses" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new axioms" (axioms()=before_axioms);
  Printf.printf "COMPOSED_WORK_PASS pred-cases %d\n%!" !count;;
run_pred_cases ();;
