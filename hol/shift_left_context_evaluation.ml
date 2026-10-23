(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Changed-input recursion, with induction generalized over the first operand. *)
needs "hol/pow_context_evaluation.ml";;

let l4_edef_shift_left_evaluation_in_context =
  let env=`env:l4_entry list` and context=`g:l4_expr list`
  and add=`add:l4_expr` and mul=`mul:l4_expr` and body=`body:l4_expr`
  and m=`m:num` and n=`n:num` in
  let nat=`L4Const l4_nat_name []`
  and zero=`L4Const (L4String l4_nat_name [122;101;114;111]) []`
  and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []`
  and level=`L4Succ L4Zero` in
  let unary=list_mk_comb(`L4Pi`,[`L4Anonymous`;nat;nat]) in
  let one=list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[nat;context]) in
  let app f x=list_mk_comb(`L4App`,[f;x]) in
  let app2 f x y=app(app f x)y in
  let lit k=mk_comb(`L4NatLit`,k) in
  let product x y=list_mk_comb(`(*):num->num->num`,[x;y]) in
  let power k=list_mk_comb(`(EXP):num->num->num`,[`2`;k]) in
  let j g x y a=list_mk_comb(`l4_edef`,[env;g;x;y;a]) in
  let typed_nat g=j g nat nat(mk_comb(`L4Sort`,level)) in
  let delta=`delta:l4_expr list` in
  let relative=mk_abs(delta,list_mk_comb(`l4_edef`,[env;
    list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])])) in
  let contract=list_mk_comb(`l4_prim_shift_left_contract`,[relative;add;mul;body]) in
  let scoped b=list_mk_comb(`l4_scoped`,[b;`0`]) in
  let premise=list_mk_conj [scoped add;scoped mul;scoped body;contract;
    typed_nat context;typed_nat one;j context zero zero nat;j context succ succ unary] in
  let ascope,mscope,scope,law,hn0,hn1,hz,hs=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d;e;f;h;i]->a,b,c,d,e,f,h,i | _->failwith "shiftLeft premise arity" in
  let mlaw,hb,hbase,hstep=match CONJUNCTS(REWRITE_RULE [l4_prim_shift_left_contract] law) with
    | [a;b;c;d]->a,b,c,d | _->failwith "shiftLeft contract arity" in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;
    l4_prim_two;l4_prim_one;l4_prim_zero;l4_prim_succ] in
  let hb=REWRITE_RULE notation hb and hbase=REWRITE_RULE notation hbase
  and hstep=REWRITE_RULE notation hstep in
  let hmul=List.nth(CONJUNCTS(REWRITE_RULE(l4_prim_mul_contract::notation) mlaw)) 1 in
  let meval=MP(SPECL [env;context;add;mul] l4_edef_mul_evaluation_in_context)
    (end_itlist CONJ [ascope;mscope;mlaw;hn0;hn1;hz;hs]) in
  let closed_rules=List.concat(List.map(fun(b,h)->
    [MP(SPEC b l4_subst_closed) h;MP(SPEC b l4_lift_closed) h])
    [body,scope;mul,mscope;add,ascope]) in
  let simplify=REWRITE_CONV(l4_inst::l4_subst::l4_lift::closed_rules)
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let rules=CONJUNCTS l4_edef_RULES in
  let use g i args proofs=
    let th=CONV_RULE simplify(SPECL(env::g::args)(List.nth rules i)) in
    MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
  let literal g k ht=use g 16 [k] [ht] in
  let instantiate g value hx hd hv=
    let _,args=strip_comb(concl hx) in
    let x,y,a=match args with [_;_;x;y;a]->x,y,a | _->failwith "shiftLeft instantiation arity" in
    CONV_RULE simplify(MP(SPECL [env;g;nat;level;x;y;a;value] l4_edef_instantiation)
      (CONJ hd(CONJ hx hv))) in
  let lm=lit m and ln=lit n in
  let hm=literal context m hn0 and hn=literal context n hn0 in
  let fn=app body lm in
  let hf=use context 2 [body;body;lm;lm;`L4Anonymous`;nat;unary] [hb;hm] in
  let congr f h x y hxy=use context 2 [f;f;x;y;`L4Anonymous`;nat;nat] [h;hxy] in
  let trans x y z h k=use context 7 [x;y;z;nat] [h;k] in
  let sym x y h=use context 6 [x;y;nat] [h] in
  let literal_zero=use context 17 [] [hz] in
  let literal_one=trans (lit `1`) (app succ(lit `0`)) (app succ zero)
    (use context 18 [`0`] [hs]) (congr succ hs (lit `0`) zero literal_zero) in
  let two=app succ(app succ zero) in
  let literal_two=trans (lit `2`) (app succ(lit `1`)) two
    (use context 18 [`1`] [hs]) (congr succ hs (lit `1`) (app succ zero) literal_one) in
  let base=trans (app fn(lit `0`)) (app fn zero) lm
    (congr fn hf (lit `0`) zero literal_zero) (instantiate context lm hbase hn0 hm) in
  let symbolic=instantiate context lm
    (instantiate one ln hstep hn1(literal one n hn1)) hn0 hm in
  let next=lit(mk_comb(`SUC`,n)) in
  let changed=app2 mul two lm and doubled=product `2` m in
  let first=congr fn hf next (app succ ln)(use context 18 [n] [hs]) in
  let step=trans (app fn next) (app fn(app succ ln)) (app2 body changed ln) first symbolic in
  let hmul2=use context 2 [mul;mul;two;lit `2`;`L4Anonymous`;nat;unary]
    [hmul;sym (lit `2`) two literal_two] in
  let hmularg=use context 2 [app mul two;app mul(lit `2`);lm;lm;`L4Anonymous`;nat;nat]
    [hmul2;hm] in
  let hdouble=trans changed (app2 mul(lit `2`) lm) (lit doubled)
    hmularg (SPECL [`2`;m] meval) in
  let hbody=use context 2 [body;body;changed;lit doubled;`L4Anonymous`;nat;unary]
    [hb;hdouble] in
  let harg=use context 2 [app body changed;app body(lit doubled);ln;ln;`L4Anonymous`;nat;nat]
    [hbody;hn] in
  let step=trans (app fn next) (app2 body changed ln) (app2 body(lit doubled) ln) step harg in
  let goal x k=j context (app2 body(lit x)(lit k)) (lit(product x(power k))) nat in
  let induction_goal k=mk_forall(m,goal m k) in
  let ih=ASSUME(induction_goal n) in
  let step=trans (app fn next) (app2 body(lit doubled) ln) (lit(product doubled(power n)))
    step (SPEC doubled ih) in
  let arithmetic=prove(`!m n. (2*m)*2 EXP n = m*2 EXP (SUC n)`,
    REPEAT GEN_TAC THEN REWRITE_TAC [EXP;AC MULT_AC `(2*m)*p = m*(2*p)`]) in
  let step=REWRITE_RULE [arithmetic] step in
  let induction=REWRITE_RULE [CONJUNCT1 EXP;MULT_CLAUSES]
    (BETA_RULE(SPEC(mk_abs(n,induction_goal n)) num_INDUCTION)) in
  let alln=MP induction(CONJ(GEN m base)(GEN n(DISCH(induction_goal n)(GEN m step)))) in
  let all=GENL [m;n](SPECL [n;m] alln) in
  let theorem=GENL [env;context;add;mul;body](DISCH premise all) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then failwith "open contextual shiftLeft theorem";
  theorem;;

let l4_edef_shift_left_evaluation_context_empty =
  let env=`env:l4_entry list` and add=`add:l4_expr` and mul=`mul:l4_expr` and body=`body:l4_expr` in
  GENL [env;add;mul;body](REWRITE_RULE [APPEND_NIL;ETA_AX]
    (SPECL [env;`[]:l4_expr list`;add;mul;body] l4_edef_shift_left_evaluation_in_context));;

let l4_shift_left_context_checked_raw = prove
 (`!policy env g add mul body.
    l4_prim_shift_left_contract (\delta. l4_checked policy env (APPEND delta g)) add mul body ==>
    l4_prim_shift_left_contract (\delta. l4_edef env (APPEND delta g)) add mul body`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC l4_prim_shift_left_mono THEN
  REWRITE_TAC [l4_checked] THEN MESON_TAC []);;
