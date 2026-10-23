(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Natural exponentiation from exact multiplication and addition contracts. *)
needs "hol/mul_context_evaluation.ml";;

let l4_edef_pow_evaluation_in_context =
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
  let lit k=mk_comb(`L4NatLit`,k) in
  let pow a b=list_mk_comb(`(EXP):num->num->num`,[a;b]) in
  let j g x y a=list_mk_comb(`l4_edef`,[env;g;x;y;a]) in
  let typed_nat g=j g nat nat(mk_comb(`L4Sort`,level)) in
  let delta=`delta:l4_expr list` in
  let relative=mk_abs(delta,list_mk_comb(`l4_edef`,[env;
    list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])])) in
  let contract=list_mk_comb(`l4_prim_pow_contract`,[relative;add;mul;body]) in
  let scoped b=list_mk_comb(`l4_scoped`,[b;`0`]) in
  let premise=list_mk_conj [scoped add;scoped mul;scoped body;contract;
    typed_nat context;typed_nat one;j context zero zero nat;j context succ succ unary] in
  let ascope,mscope,scope,law,hn0,hn1,hz,hs=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d;e;f;h;i]->a,b,c,d,e,f,h,i | _->failwith "pow evaluation premise arity" in
  let mlaw,hb,hbase,hstep=match CONJUNCTS(REWRITE_RULE [l4_prim_pow_contract] law) with
    | [a;b;c;d]->a,b,c,d | _->failwith "pow contract arity" in
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_prim_one;l4_prim_zero;l4_prim_succ] in
  let hb=REWRITE_RULE notation hb and hbase=REWRITE_RULE notation hbase
  and hstep=REWRITE_RULE notation hstep in
  let hmul=List.nth(CONJUNCTS(REWRITE_RULE(l4_prim_mul_contract::notation) mlaw)) 1 in
  let meval=MP(SPECL [env;context;add;mul] l4_edef_mul_evaluation_in_context)
    (end_itlist CONJ [ascope;mscope;mlaw;hn0;hn1;hz;hs]) in
  let closed_rules=List.concat(List.map(fun (b,h)->
    [MP(SPEC b l4_subst_closed) h;MP(SPEC b l4_lift_closed) h])
    [body,scope;mul,mscope;add,ascope]) in
  let simplify=REWRITE_CONV(l4_inst::l4_subst::l4_lift::closed_rules)
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let rules=CONJUNCTS l4_edef_RULES in
  let use g i args proofs =
    let th=CONV_RULE simplify(SPECL(env::g::args)(List.nth rules i)) in
    MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
  let literal g k ht=use g 16 [k] [ht] in
  let instantiate g value hx hd hv =
    let _,args=strip_comb(concl hx) in
    let x,y,a=match args with [_;_;x;y;a]->x,y,a | _->failwith "pow instantiation arity" in
    CONV_RULE simplify(MP(SPECL [env;g;nat;level;x;y;a;value] l4_edef_instantiation)
      (CONJ hd(CONJ hx hv))) in
  let lm=lit m and ln=lit n in
  let hm=literal context m hn0 in
  let fn=app body lm in
  let hf=use context 2 [body;body;lm;lm;`L4Anonymous`;nat;unary] [hb;hm] in
  let congr f h x y hxy=use context 2 [f;f;x;y;`L4Anonymous`;nat;nat] [h;hxy] in
  let trans x y z h k=use context 7 [x;y;z;nat] [h;k] in
  let literal_zero=use context 17 [] [hz] in
  let literal_one=trans (lit `1`) (app succ(lit `0`)) (app succ zero)
    (use context 18 [`0`] [hs]) (congr succ hs (lit `0`) zero literal_zero) in
  let base=trans (app fn(lit `0`)) (app fn zero) (app succ zero)
    (congr fn hf (lit `0`) zero literal_zero) (instantiate context lm hbase hn0 hm) in
  let base=trans (app fn(lit `0`)) (app succ zero) (lit `1`) base
    (use context 6 [lit `1`;app succ zero;nat] [literal_one]) in
  let symbolic=instantiate context lm
    (instantiate one ln hstep hn1(literal one n hn1)) hn0 hm in
  let goal k=j context (app fn(lit k)) (lit(pow m k)) nat in
  let next=lit(mk_comb(`SUC`,n)) and previous=app fn ln in
  let first=congr fn hf next (app succ ln)(use context 18 [n] [hs]) in
  let step=trans (app fn next) (app fn(app succ ln)) (app(app mul previous) lm) first symbolic in
  let hpartial=use context 2 [mul;mul;previous;lit(pow m n);`L4Anonymous`;nat;unary]
    [hmul;ASSUME(goal n)] in
  let expanded=app(app mul(lit(pow m n))) lm in
  let hproduct=use context 2 [app mul previous;app mul(lit(pow m n));lm;lm;`L4Anonymous`;nat;nat]
    [hpartial;hm] in
  let step=trans (app fn next) (app(app mul previous) lm) expanded step hproduct in
  let product=list_mk_comb(`(*):num->num->num`,[pow m n;m]) in
  let step=trans (app fn next) expanded (lit product) step (SPECL [pow m n;m] meval) in
  let arithmetic=TRANS(SPECL [m;n](CONJUNCT2 EXP))(SPECL [m;pow m n] MULT_SYM) in
  let induction=REWRITE_RULE [CONJUNCT1 EXP;arithmetic]
    (BETA_RULE(SPEC (mk_abs(n,goal n)) num_INDUCTION)) in
  let all=MP induction(CONJ base(GEN n(DISCH(goal n) step))) in
  let theorem=GENL [env;context;add;mul;body](DISCH premise(GEN m all)) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then failwith "open contextual exponentiation theorem";
  theorem;;

let l4_edef_pow_evaluation_context_empty =
  let env=`env:l4_entry list` and add=`add:l4_expr` and mul=`mul:l4_expr` and body=`body:l4_expr` in
  GENL [env;add;mul;body](REWRITE_RULE [APPEND_NIL;ETA_AX]
    (SPECL [env;`[]:l4_expr list`;add;mul;body] l4_edef_pow_evaluation_in_context));;
