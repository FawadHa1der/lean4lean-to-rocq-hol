let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/pow_context_evaluation.ml";;
needs "hol/environment.ml";;
let run_pow_cases group =
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
  let app2 f a b=App(App(f,a),b) in
  let recnat z step major=Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat;z;lam(lam step);major] in
  let add=lam(lam(recnat (Bvar 1) (App(successor,Bvar 0)) (Bvar 0))) in
  let multiplication a=lam(lam(recnat zero (app2 a (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let mul=multiplication add in
  let power p=lam(lam(recnat (App(successor,zero)) (app2 p (Bvar 0) (Bvar 3)) (Bvar 0))) in
  let body=power mul in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,_=get "canonical Nat admission" (Env.admit_inductive Env.empty block) in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_prim_one;l4_prim_zero;l4_prim_succ;l4_nat_name] in
  let certify env g add mul body =
    let qe=Env.quote_env env and qg=quote_context g
    and qa=quote_expr add and qm=quote_expr mul and qb=quote_expr body in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,node "l4_edef" [qe;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;qg])]) in
    let closed q=prove(node "l4_scoped" [q;`0`],
      REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    let check label b=get label(Env.check env g b binary) in
    let base label b z=get label(Env.convert env (nat::g) (app2 b (Bvar 0) zero) z nat) in
    let step label b s=get label(Env.convert env (nat::nat::g)
      (app2 b (Bvar 1) (App(successor,Bvar 0))) s nat) in
    let ha=check "addition type" add in
    let az=base "addition zero" add (Bvar 0) in
    let astep=step "addition successor" add (App(successor,app2 add (Bvar 1) (Bvar 0))) in
    let aequation=REWRITE_RULE notation(SPECL [relative;qa] l4_prim_add_contract) in
    let alaw=EQ_MP(SYM aequation)(end_itlist CONJ [raw ha;raw az;raw astep]) in
    let hm=check "multiplication type" mul in
    let mz=base "multiplication zero" mul zero in
    let mstep=step "multiplication successor" mul (app2 add (app2 mul (Bvar 1) (Bvar 0)) (Bvar 1)) in
    let mequation=REWRITE_RULE notation(SPECL [relative;qa;qm] l4_prim_mul_contract) in
    let mlaw=EQ_MP(SYM mequation)(end_itlist CONJ [alaw;raw hm;raw mz;raw mstep]) in
    let hb=check "power type" body in
    let bz=base "power zero" body (App(successor,zero)) in
    let bstep=step "power successor" body (app2 mul (app2 body (Bvar 1) (Bvar 0)) (Bvar 1)) in
    let statement=node "l4_prim_pow_contract" [relative;qa;qm;qb] in
    let equation=REWRITE_RULE notation(REWR_CONV l4_prim_pow_contract statement) in
    let contract=EQ_MP(SYM equation)(end_itlist CONJ [mlaw;raw hb;raw bz;raw bstep]) in
    let hn=get "Nat typed" (Env.check env g nat (Sort(Succ Zero))) in
    let hn1=get "Nat typed above context" (Env.check env (nat::g) nat (Sort(Succ Zero))) in
    let hz=get "zero typed" (Env.check env g zero nat) in
    let hs=get "successor typed" (Env.check env g successor unary) in
    let premises=[closed qa;closed qm;closed qb;contract;raw hn;raw hn1;raw hz;raw hs] in
    let theorem=REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qa;qm;qb] l4_edef_pow_evaluation_in_context) in
    MP theorem(end_itlist CONJ premises),theorem,premises,hn in
  let refuses theorem premises=try ignore(MP theorem(end_itlist CONJ premises));false with Failure _->true in
  let context_cases g =
    let all,theorem,premises,hn=certify env g add mul body in
    test "closed contextual universal exponentiation" (hyp all=[] && frees(concl all)=[]);
    let qe=Env.quote_env env and policy=Env.quote_policy env and qg=quote_context g in
    let valid=Env.certificate env and context=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] hn)) 1 in
    List.iter(fun (left,right)->
      let m=natural left and n=natural right in
      let output=rhs(concl(NUM_REDUCE_CONV(node "EXP" [m;n]))) in
      let call=quote_expr(app2 body (Natlit left) (Natlit right)) in
      let result=node "L4NatLit" [output] in
      let expected=node "l4_edef" [qe;qg;call;result;quote_expr nat] in
      let proof=CONV_RULE NUM_REDUCE_CONV(SPECL [m;n] all) in
      test "exact exponentiation" (aconv(concl proof) expected && hyp proof=[]);
      let expected=node "l4_checked" [policy;qe;qg;call;result;quote_expr nat] in
      let checked=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
        (CONJ valid(CONJ context proof)) in
      test "exact checked exponentiation" (aconv(concl checked) expected && hyp checked=[]))
      ["0","0";"0","7";"10","0";"1","120";"2","100";"3","7";
       "9876543210987654321098765432109876543210","3"];
    List.iteri(fun omitted _->test "every premise required"
      (refuses theorem(List.filteri(fun i _->i<>omitted) premises))) premises;
    List.iter(fun (qe,qg,qa,qm,qb)->
      let wrong=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;qg;qa;qm;qb] l4_edef_pow_evaluation_in_context) in
      test "exact environment context dependencies and body binding" (refuses wrong premises))
      [`[]:l4_entry list`,qg,quote_expr add,quote_expr mul,quote_expr body;
       qe,quote_context(nat::g),quote_expr add,quote_expr mul,quote_expr body;
       qe,qg,quote_expr(lam(lam(Bvar 1))),quote_expr mul,quote_expr body;
       qe,qg,quote_expr add,quote_expr(lam(lam zero)),quote_expr body;
       qe,qg,quote_expr add,quote_expr mul,quote_expr(lam(lam(App(successor,zero))))];
    let assumed=MP theorem(ASSUME(fst(dest_imp(concl theorem)))) in
    test "assumed contract remains conditional" (hyp assumed<>[]) in
  (match group with
   | "empty" ->
      context_cases [];
      let bad=lam(lam(App(successor,zero))) in
      ignore(get "wrong power independently typed" (Env.check env [] bad binary));
      ignore(get "wrong power zero law passes" (Env.convert env [nat]
        (app2 bad (Bvar 0) zero) (App(successor,zero)) nat));
      test "typed constant-one impostor fails symbolic successor" (match Env.convert env [nat;nat]
        (app2 bad (Bvar 1) (App(successor,Bvar 0)))
        (app2 mul (app2 bad (Bvar 1) (Bvar 0)) (Bvar 1)) nat with
        | Error {kind=Proof_failure;_}->true | _->false)
   | "contexts" -> List.iter context_cases [[nat];[Bvar 0;Sort(Succ Zero)]]
   | "wrappers" ->
      List.iter(fun wrapped->
        let all,_,_,_=certify env [] add mul wrapped in
        test "beta and let source retained" (hyp all=[] && frees(concl all)=[]);
        let h=get "ordinary small power" (Env.convert env []
          (app2 wrapped (Natlit "2") (Natlit "1")) (Natlit "2") nat) in
        test "independent ordinary result is closed" (hyp h=[]))
        [App(Lam(Anonymous,binary,Bvar 0),body);Let(Anonymous,binary,body,Bvar 0)];
      let an=Str(Anonymous,"localAdd") and mn=Str(Anonymous,"localMul") and pn=Str(Anonymous,"localPow") in
      let declare env name b=get "ordinary named definition" (Env.admit env
        {Env.kind=Env.Definition;name;params=[];typ=binary;value=Some b}) in
      let env2,_=declare env an add in
      let a=Const(an,[]) in
      let env3,_=declare env2 mn (multiplication a) in
      let m=Const(mn,[]) in
      let env4,_=declare env3 pn (power m) in
      let all,_,_,_=certify env4 [nat] a m (Const(pn,[])) in
      test "named dependency chain and source in extended environment" (hyp all=[] && frees(concl all)=[])
   | _ -> failwith "unknown power test group");
  test "unchanged native clauses" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "unchanged admission clauses" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new axioms" (axioms()=before_axioms);
  Printf.printf "\nCOMPOSED_WORK_PASS pow-%s %d\n%!" group !count;;
