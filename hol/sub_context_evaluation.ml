(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Truncated subtraction derived from authenticated predecessor and body laws. *)
needs "hol/pred_context_evaluation.ml";;

let l4_edef_sub_evaluation_in_context =
  let env=`env:l4_entry list` and context=`g:l4_expr list`
  and pred=`pred:l4_expr` and body=`body:l4_expr` and m=`m:num` and n=`n:num` in
  let nat=`L4Const l4_nat_name []`
  and zero=`L4Const (L4String l4_nat_name [122;101;114;111]) []`
  and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []`
  and level=`L4Succ L4Zero` in
  let unary=list_mk_comb(`L4Pi`,[`L4Anonymous`;nat;nat]) in
  let one=list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[nat;context]) in
  let app f x=list_mk_comb(`L4App`,[f;x]) in
  let lit k=mk_comb(`L4NatLit`,k) in
  let sub a b=list_mk_comb(`(-):num->num->num`,[a;b]) in
  let j g x y a=list_mk_comb(`l4_edef`,[env;g;x;y;a]) in
  let typed_nat g=j g nat nat(mk_comb(`L4Sort`,level)) in
  let delta=`delta:l4_expr list` in
  let relative=mk_abs(delta,list_mk_comb(`l4_edef`,[env;
    list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])])) in
  let contract=list_mk_comb(`l4_prim_sub_contract`,[relative;pred;body]) in
  let premise=list_mk_conj [list_mk_comb(`l4_scoped`,[pred;`0`]);
    list_mk_comb(`l4_scoped`,[body;`0`]);contract;typed_nat context;typed_nat one;
    j context zero zero nat;j context succ succ unary] in
  let pscope,scope,law,hn0,hn1,hz,hs=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d;e;f;h]->a,b,c,d,e,f,h | _->failwith "sub evaluation premise arity" in
  let plaw,hb,hbase,hstep=match CONJUNCTS(REWRITE_RULE [l4_prim_sub_contract] law) with
    | [a;b;c;d]->a,b,c,d | _->failwith "sub contract arity" in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_prim_zero;l4_prim_succ] in
  let hb=REWRITE_RULE notation hb and hbase=REWRITE_RULE notation hbase
  and hstep=REWRITE_RULE notation hstep in
  let hp=CONJUNCT1(REWRITE_RULE(l4_prim_pred_contract::notation) plaw) in
  let peval=MP(SPECL [env;context;pred] l4_edef_pred_evaluation_in_context)
    (end_itlist CONJ [pscope;plaw;hn0;hz;hs]) in
  let body_subst=MP(SPEC body l4_subst_closed) scope
  and body_lift=MP(SPEC body l4_lift_closed) scope
  and pred_subst=MP(SPEC pred l4_subst_closed) pscope
  and pred_lift=MP(SPEC pred l4_lift_closed) pscope in
  let simplify=REWRITE_CONV [l4_inst;l4_subst;l4_lift;body_subst;body_lift;pred_subst;pred_lift]
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let rules=CONJUNCTS l4_edef_RULES in
  let use g i args proofs =
    let th=CONV_RULE simplify(SPECL(env::g::args)(List.nth rules i)) in
    MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
  let literal g k ht=use g 16 [k] [ht] in
  let instantiate g value hx hd hv =
    let _,args=strip_comb(concl hx) in
    let x,y,a=match args with [_;_;x;y;a]->x,y,a | _->failwith "sub instantiation arity" in
    CONV_RULE simplify(MP(SPECL [env;g;nat;level;x;y;a;value] l4_edef_instantiation)
      (CONJ hd(CONJ hx hv))) in
  let lm=lit m and ln=lit n in
  let hm=literal context m hn0 in
  let fn=app body lm in
  let hf=use context 2 [body;body;lm;lm;`L4Anonymous`;nat;unary] [hb;hm] in
  let congr f h x y hxy=use context 2 [f;f;x;y;`L4Anonymous`;nat;nat] [h;hxy] in
  let trans x y z h k=use context 7 [x;y;z;nat] [h;k] in
  let base=instantiate context lm hbase hn0 hm in
  let literal_zero=use context 17 [] [hz] in
  let base=trans (app fn(lit `0`)) (app fn zero) lm
    (congr fn hf (lit `0`) zero literal_zero) base in
  let symbolic=instantiate context lm
    (instantiate one ln hstep hn1(literal one n hn1)) hn0 hm in
  let goal k=j context (app fn(lit k)) (lit(sub m k)) nat in
  let next=lit(mk_comb(`SUC`,n)) in
  let first=congr fn hf next (app succ ln)(use context 18 [n] [hs]) in
  let step=trans (app fn next) (app fn(app succ ln)) (app pred(app fn ln)) first symbolic in
  let step=trans (app fn next) (app pred(app fn ln)) (app pred(lit(sub m n))) step
    (congr pred hp (app fn ln) (lit(sub m n)) (ASSUME(goal n))) in
  let step=trans (app fn next) (app pred(lit(sub m n))) (lit(mk_comb(`PRE`,sub m n))) step
    (SPEC (sub m n) peval) in
  let induction=REWRITE_RULE [SUB]
    (BETA_RULE(SPEC (mk_abs(n,goal n)) num_INDUCTION)) in
  let all=MP induction(CONJ base(GEN n(DISCH(goal n) step))) in
  let theorem=GENL [env;context;pred;body](DISCH premise(GEN m all)) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then failwith "open contextual subtraction theorem";
  theorem;;

let l4_edef_sub_evaluation_context_empty =
  let env=`env:l4_entry list` and pred=`pred:l4_expr` and body=`body:l4_expr` in
  GENL [env;pred;body](REWRITE_RULE [APPEND_NIL;ETA_AX]
    (SPECL [env;`[]:l4_expr list`;pred;body] l4_edef_sub_evaluation_in_context));;
