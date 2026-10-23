let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/sub_context_evaluation.ml";;
needs "hol/environment.ml";;
let run_sub_cases () =
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
  let binary=Pi(Anonymous,nat,unary) in
  let recnat z step major=Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat;z;lam(lam step);major] in
  let pred=lam(recnat zero (Bvar 1) (Bvar 0)) in
  let subtraction p=lam(lam(recnat (Bvar 1) (App(p,Bvar 0)) (Bvar 0))) in
  let body=subtraction pred in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,_=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_nat_name] in
  let app2 f a b=App(App(f,a),b) in
  let certify env g pred body =
    let qe=Env.quote_env env and qg=quote_context g
    and qp=quote_expr pred and qb=quote_expr body in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,node "l4_edef" [qe;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;qg])]) in
    let closed q=prove(node "l4_scoped" [q;`0`],
      REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    let hp=get "predecessor type" (Env.check env g pred unary) in
    let pbase=get "predecessor zero" (Env.convert env g (App(pred,zero)) zero nat) in
    let pstep=get "predecessor successor" (Env.convert env (nat::g)
      (App(pred,App(successor,Bvar 0))) (Bvar 0) nat) in
    let plaw=REWRITE_RULE notation(SPECL [relative;qp] l4_prim_pred_contract) in
    let plaw=EQ_MP(SYM plaw)(end_itlist CONJ [raw hp;raw pbase;raw pstep]) in
    let typed=get "subtraction type" (Env.check env g body binary) in
    let base=get "subtraction base" (Env.convert env (nat::g)
      (app2 body (Bvar 0) zero) (Bvar 0) nat) in
    let step=get "subtraction step" (Env.convert env (nat::nat::g)
      (app2 body (Bvar 1) (App(successor,Bvar 0)))
      (App(pred,app2 body (Bvar 1) (Bvar 0))) nat) in
    let law=REWRITE_RULE notation(SPECL [relative;qp;qb] l4_prim_sub_contract) in
    let contract=EQ_MP(SYM law)(end_itlist CONJ [plaw;raw typed;raw base;raw step]) in
    let hn=get "Nat typed" (Env.check env g nat (Sort(Succ Zero))) in
    let hn1=get "Nat typed above context" (Env.check env (nat::g) nat (Sort(Succ Zero))) in
    let hz=get "zero typed" (Env.check env g zero nat) in
    let hs=get "successor typed" (Env.check env g successor unary) in
    let premises=[closed qp;closed qb;contract;raw hn;raw hn1;raw hz;raw hs] in
    let theorem=REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qp;qb] l4_edef_sub_evaluation_in_context) in
    MP theorem(end_itlist CONJ premises),theorem,premises,hn in
  let refuses theorem premises=try ignore(MP theorem(end_itlist CONJ premises));false with Failure _->true in
  List.iter(fun g->
    let all,theorem,premises,hn=certify env g pred body in
    test "closed contextual universal subtraction" (hyp all=[] && frees(concl all)=[]);
    let qe=Env.quote_env env and policy=Env.quote_policy env and qg=quote_context g in
    let valid=Env.certificate env and context=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] hn)) 1 in
    List.iter(fun (left,right)->
      let m=natural left and n=natural right in
      let output=rhs(concl(NUM_REDUCE_CONV(node "-" [m;n]))) in
      let call=quote_expr(app2 body (Natlit left) (Natlit right)) in
      let result=node "L4NatLit" [output] in
      let expected=node "l4_edef" [qe;qg;call;result;quote_expr nat] in
      let proof=CONV_RULE NUM_REDUCE_CONV(SPECL [m;n] all) in
      test "exact truncated subtraction" (aconv(concl proof) expected && hyp proof=[]);
      let expected=node "l4_checked" [policy;qe;qg;call;result;quote_expr nat] in
      let checked=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
        (CONJ valid(CONJ context proof)) in
      test "exact checked subtraction" (aconv(concl checked) expected && hyp checked=[]))
      ["0","0";"0","10";"10","0";"8","3";"3","8";"17","17";
       "9876543210987654321098765432109876543210","123456789012345678901234567890";
       "123456789012345678901234567890","9876543210987654321098765432109876543210"];
    List.iteri(fun omitted _->test "every premise required"
      (refuses theorem(List.filteri(fun i _->i<>omitted) premises))) premises;
    List.iter(fun (qe,qg,qp,qb)->
      let wrong=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;qg;qp;qb] l4_edef_sub_evaluation_in_context) in
      test "exact environment context dependency and body binding" (refuses wrong premises))
      [`[]:l4_entry list`,qg,quote_expr pred,quote_expr body;
       qe,quote_context(nat::g),quote_expr pred,quote_expr body;
       qe,qg,quote_expr(lam zero),quote_expr body;
       qe,qg,quote_expr pred,quote_expr(lam(lam(Bvar 1)))];
    let assumed=MP theorem(ASSUME(fst(dest_imp(concl theorem)))) in
    test "assumed contract remains conditional" (hyp assumed<>[])
  )[[];[nat];[Bvar 0;Sort(Succ Zero)]];
  List.iter(fun wrapped->
    let all,_,_,_=certify env [] pred wrapped in
    test "beta and let source retained" (hyp all=[] && frees(concl all)=[]);
    let h=get "ordinary small subtraction" (Env.convert env []
      (app2 wrapped (Natlit "5") (Natlit "2")) (Natlit "3") nat) in
    test "independent ordinary result is closed" (hyp h=[]))
    [App(Lam(Anonymous,binary,Bvar 0),body);Let(Anonymous,binary,body,Bvar 0)];
  let pn=Str(Anonymous,"localPred") and sn=Str(Anonymous,"localSub") in
  let env2,_=get "ordinary named dependency" (Env.admit env
    {Env.kind=Env.Definition;name=pn;params=[];typ=unary;value=Some pred}) in
  let p=Const(pn,[]) in
  let env3,_=get "ordinary named subtraction" (Env.admit env2
    {Env.kind=Env.Definition;name=sn;params=[];typ=binary;value=Some(subtraction p)}) in
  let all,_,_,_=certify env3 [nat] p (Const(sn,[])) in
  test "named dependency and source in exact extended environment" (hyp all=[] && frees(concl all)=[]);
  let bad=lam(lam(Bvar 1)) in
  ignore(get "wrong subtraction independently typed" (Env.check env [] bad binary));
  ignore(get "wrong subtraction zero law passes" (Env.convert env [nat]
    (app2 bad (Bvar 0) zero) (Bvar 0) nat));
  test "typed projection impostor fails symbolic successor" (match Env.convert env [nat;nat]
    (app2 bad (Bvar 1) (App(successor,Bvar 0)))
    (App(pred,app2 bad (Bvar 1) (Bvar 0))) nat with
    | Error {kind=Proof_failure;_}->true | _->false);
  ignore(get "false predecessor independently typed" (Env.check env [] (lam zero) unary));
  test "typed dependency impostor fails symbolic successor" (match Env.convert env [nat]
    (App(lam zero,App(successor,Bvar 0))) (Bvar 0) nat with
    | Error {kind=Proof_failure;_}->true | _->false);
  test "unchanged native clauses" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "unchanged admission clauses" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new axioms" (axioms()=before_axioms);
  Printf.printf "COMPOSED_WORK_PASS sub-cases %d\n%!" !count;;
run_sub_cases ();;
