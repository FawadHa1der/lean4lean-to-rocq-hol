let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/add_context_evaluation.ml";;
needs "hol/primitive_validation.ml";;
let run_context_add_cases () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2 in
  let nn=Str(Anonymous,"Nat") in
  let nat=Const(nn,[]) and zero=Const(Str(nn,"zero"),[])
  and successor=Const(Str(nn,"succ"),[]) in
  let lam x=Lam(Anonymous,nat,x) in
  let body=lam(lam(Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat;Bvar 1;lam(lam(App(successor,Bvar 0)));Bvar 0])) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,valid=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let qe=Env.quote_env env and qp=Env.quote_policy env and qb=quote_expr body in
  let jr=node "l4_edef" [qe] and jc=node "l4_checked" [qp;qe] in
  let scope=prove(node "l4_scoped" [qb;`0`],
    REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;
    l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_nat_name] in
  let unary=Pi(Anonymous,nat,nat) in
  List.iter(fun g->
    let qg=quote_context g in
    let delta=`delta:l4_expr list` in
    let append=list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;qg]) in
    let relative=mk_abs(delta,mk_comb(jr,append)) in
    let typed=get "body typed in actual context" (Env.check env g body (Pi(Anonymous,nat,unary))) in
    let base=get "base equation above actual context" (Env.convert env (nat::g)
      (App(App(body,Bvar 0),zero)) (Bvar 0) nat) in
    let step=get "step equation above actual context" (Env.convert env (nat::nat::g)
      (App(App(body,Bvar 1),App(successor,Bvar 0)))
      (App(successor,App(App(body,Bvar 1),Bvar 0))) nat) in
    let contract_equation=REWRITE_RULE notation(SPECL [relative;qb] l4_prim_add_contract) in
    let contract=EQ_MP(SYM contract_equation)(end_itlist CONJ [raw typed;raw base;raw step]) in
    test "context-relative symbolic contract closed" (hyp contract=[] && frees(concl contract)=[]);
    test "context-relative contract exact" (aconv(concl contract)
      (node "l4_prim_add_contract" [relative;qb]));
    let hn=get "Nat typed in actual context" (Env.check env g nat (Sort(Succ Zero))) in
    let hn1=get "Nat typed above actual context" (Env.check env (nat::g) nat (Sort(Succ Zero))) in
    let hz=get "zero typed in actual context" (Env.check env g zero nat) in
    let hs=get "successor typed in actual context" (Env.check env g successor unary) in
    let premises=[scope;contract;raw hn;raw hn1;raw hz;raw hs] in
    let theorem=REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qb] l4_edef_add_evaluation_in_context) in
    let all=MP theorem(end_itlist CONJ premises) in
    test "all pairs in actual context closed" (hyp all=[] && frees(concl all)=[]);
    let context=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] hn)) 1 in
    List.iter(fun (left,right)->
      let m=natural left and n=natural right in
      let sum=rhs(concl(NUM_REDUCE_CONV(node "+" [m;n]))) in
      let call=node "L4App" [node "L4App" [qb;node "L4NatLit" [m]];node "L4NatLit" [n]] in
      let output=node "L4NatLit" [sum] and ty=quote_expr nat in
      let expected=list_mk_comb(jr,[qg;call;output;ty]) in
      let h=CONV_RULE NUM_REDUCE_CONV(SPECL [m;n] all) in
      test "exact contextual native result" (aconv(concl h) expected && hyp h=[]);
      let expected_checked=list_mk_comb(jc,[qg;call;output;ty]) in
      let ch=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected_checked))
        (CONJ valid(CONJ context h)) in
      test "exact contextual checked result" (aconv(concl ch) expected_checked && hyp ch=[])
    )["0","0";"2","3";"123456789012345678901234567890","987654321098765432109876543210"];
    let refuses th ps=try ignore(MP th(end_itlist CONJ ps));false with Failure _->true in
    List.iteri(fun omitted _->
      test "all contextual premises required" (refuses theorem(List.filteri(fun i _->i<>omitted) premises))
    ) premises;
    let wrong=REWRITE_RULE [l4_nat_name]
      (SPECL [qe;quote_context(nat::g);qb] l4_edef_add_evaluation_in_context) in
    test "different context cannot reuse contract" (refuses wrong premises);
    let wrong=REWRITE_RULE [l4_nat_name]
      (SPECL [`[]:l4_entry list`;qg;qb] l4_edef_add_evaluation_in_context) in
    test "different environment cannot reuse contract" (refuses wrong premises);
    let assumed=MP theorem(ASSUME(fst(dest_imp(concl theorem)))) in
    test "assumed recurrence does not become closed" (hyp assumed<>[])
  )[[];[nat];[Bvar 0;Sort(Succ Zero)]];
  test "no new native clauses" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "no new admission clauses" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new axioms" (axioms()=before_axioms);
  Printf.printf "PRIVATE_NAT_EVALUATION_DONE %d_context_concrete_assertions unchanged_axioms\n%!" !count;;
run_context_add_cases ();;
exit 0;;
