(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Context-relative addition from authenticated body equations, without a new rule. *)
needs "hol/nat_evaluation.ml";;
needs "hol/instantiation_certificates.ml";;
needs "hol/closed_syntax.ml";;

let l4_edef_add_evaluation_in_context =
  let env=`env:l4_entry list` and context=`g:l4_expr list` and body=`body:l4_expr`
  and m=`m:num` and n=`n:num` in
  let nat=`L4Const l4_nat_name []`
  and zero=`L4Const (L4String l4_nat_name [122;101;114;111]) []`
  and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []`
  and level=`L4Succ L4Zero` in
  let unary=list_mk_comb(`L4Pi`,[`L4Anonymous`;nat;nat]) in
  let one=list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[nat;context]) in
  let app f x=list_mk_comb(`L4App`,[f;x]) in
  let lit k=mk_comb(`L4NatLit`,k) in
  let j g x y a=list_mk_comb(`l4_edef`,[env;g;x;y;a]) in
  let nat_typed g=j g nat nat (mk_comb(`L4Sort`,level)) in
  let delta=`delta:l4_expr list` in
  let shifted=list_mk_comb(`l4_edef`,[env;list_mk_comb
    (`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])]) in
  let contract=list_mk_comb(`l4_prim_add_contract`,[mk_abs(delta,shifted);body]) in
  let premise=list_mk_conj [list_mk_comb(`l4_scoped`,[body;`0`]);contract;
    nat_typed context;nat_typed one;j context zero zero nat;j context succ succ unary] in
  let scope,law,hn0,hn1,hz,hs=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d;e;f]->a,b,c,d,e,f | _->failwith "add evaluation premise arity" in
  let hb,hbase,hstep=match CONJUNCTS(REWRITE_RULE
    [APPEND;l4_prim_add_contract;l4_prim_binary;l4_prim_unary;l4_prim_nat;l4_prim_zero;l4_prim_succ] law) with
    | [a;b;c]->a,b,c | _->failwith "add contract arity" in
  let closed_subst=MP(SPEC body l4_subst_closed) scope
  and closed_lift=MP(SPEC body l4_lift_closed) scope in
  let simplify=REWRITE_CONV [l4_inst;l4_subst;l4_lift;closed_subst;closed_lift]
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let rules=CONJUNCTS l4_edef_RULES in
  let use g i args proofs =
    let th=CONV_RULE simplify(SPECL(env::g::args)(List.nth rules i)) in
    MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
  let literal g k ht=use g 16 [k] [ht] in
  let instantiate g value hx hd hv =
    let _,args=strip_comb(concl hx) in
    let x,y,a=match args with [_;_;x;y;a]->x,y,a | _->failwith "typed equality arity" in
    CONV_RULE simplify (MP(SPECL [env;g;nat;level;x;y;a;value] l4_edef_instantiation)
      (CONJ hd(CONJ hx hv))) in
  let lm=lit m and ln=lit n in
  let hm=literal context m hn0 in
  let fn=app body lm in
  let hfn=use context 2 [body;body;lm;lm;`L4Anonymous`;nat;unary] [hb;hm] in
  let base=instantiate context lm hbase hn0 hm in
  let literal_zero=use context 17 [] [hz] in
  let first=use context 2 [fn;fn;lit `0`;zero;`L4Anonymous`;nat;nat] [hfn;literal_zero] in
  let base=use context 7 [app fn(lit `0`);app fn zero;lm;nat] [first;base] in
  let step_y=instantiate one ln hstep hn1 (literal one n hn1) in
  let step=instantiate context lm step_y hn0 hm in
  let recurrence=SPECL [env;context;fn;m] l4_edef_nat_recurrence in
  let result=MP recurrence(end_itlist CONJ [hfn;hs;base;GEN n step]) in
  let theorem=GENL [env;context;body] (DISCH premise(GEN m result)) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then
    failwith "open add evaluation theorem";
  theorem;;

let l4_edef_add_evaluation_context_empty =
  let env=`env:l4_entry list` and body=`body:l4_expr` in
  GENL [env;body] (REWRITE_RULE [APPEND_NIL;ETA_AX]
    (SPECL [env;`[]:l4_expr list`;body] l4_edef_add_evaluation_in_context));;
