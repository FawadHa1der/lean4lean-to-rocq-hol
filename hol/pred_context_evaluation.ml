(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Literal predecessor follows from the existing typed symbolic contract. *)
needs "hol/instantiation_certificates.ml";;
needs "hol/closed_syntax.ml";;

let l4_edef_pred_evaluation_in_context =
  let env=`env:l4_entry list` and context=`g:l4_expr list` and body=`body:l4_expr`
  and n=`n:num` in
  let nat=`L4Const l4_nat_name []`
  and zero=`L4Const (L4String l4_nat_name [122;101;114;111]) []`
  and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []`
  and level=`L4Succ L4Zero` in
  let unary=list_mk_comb(`L4Pi`,[`L4Anonymous`;nat;nat]) in
  let app f x=list_mk_comb(`L4App`,[f;x]) in
  let lit k=mk_comb(`L4NatLit`,k) in
  let j x y a=list_mk_comb(`l4_edef`,[env;context;x;y;a]) in
  let delta=`delta:l4_expr list` in
  let relative=mk_abs(delta,list_mk_comb(`l4_edef`,[env;
    list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])])) in
  let contract=list_mk_comb(`l4_prim_pred_contract`,[relative;body]) in
  let premise=list_mk_conj [list_mk_comb(`l4_scoped`,[body;`0`]);contract;
    j nat nat (mk_comb(`L4Sort`,level));j zero zero nat;j succ succ unary] in
  let scope,law,hn,hz,hs=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d;e]->a,b,c,d,e | _->failwith "pred evaluation premise arity" in
  let hb,hbase,hstep=match CONJUNCTS(REWRITE_RULE
    [APPEND;l4_prim_pred_contract;l4_prim_unary;l4_prim_nat;l4_prim_zero;l4_prim_succ] law) with
    | [a;b;c]->a,b,c | _->failwith "pred contract arity" in
  let closed_subst=MP(SPEC body l4_subst_closed) scope
  and closed_lift=MP(SPEC body l4_lift_closed) scope in
  let simplify=REWRITE_CONV [l4_inst;l4_subst;l4_lift;closed_subst;closed_lift]
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  let rules=CONJUNCTS l4_edef_RULES in
  let use i args proofs =
    let th=CONV_RULE simplify(SPECL(env::context::args)(List.nth rules i)) in
    MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
  let congr x y h=use 2 [body;body;x;y;`L4Anonymous`;nat;nat] [hb;h] in
  let trans x y z h k=use 7 [x;y;z;nat] [h;k] in
  let literal_zero=use 17 [] [hz] in
  let zero_back=use 6 [lit `0`;zero;nat] [literal_zero] in
  let base=trans (app body(lit `0`)) (app body zero) zero
    (congr (lit `0`) zero literal_zero) hbase in
  let base=trans (app body(lit `0`)) zero (lit `0`) base zero_back in
  let ln=lit n in
  let hn_lit=use 16 [n] [hn] in
  let _,step_args=strip_comb(concl hstep) in
  let x,y,a=match step_args with [_;_;x;y;a]->x,y,a | _->failwith "pred step judgment arity" in
  let step=CONV_RULE simplify(MP(SPECL [env;context;nat;level;x;y;a;ln]
    l4_edef_instantiation)(CONJ hn(CONJ hstep hn_lit))) in
  let successor_literal=use 18 [n] [hs] in
  let next=lit(mk_comb(`SUC`,n)) in
  let step=trans (app body next) (app body(app succ ln)) ln
    (congr next (app succ ln) successor_literal) step in
  let goal k=j (app body(lit k)) (lit(mk_comb(`PRE`,k))) nat in
  let induction=REWRITE_RULE [PRE]
    (BETA_RULE(SPEC (mk_abs(n,goal n)) num_INDUCTION)) in
  let all=MP induction(CONJ base(GEN n(DISCH(goal n) step))) in
  let theorem=GENL [env;context;body](DISCH premise all) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then
    failwith "open contextual predecessor theorem";
  theorem;;

let l4_edef_pred_evaluation_context_empty =
  let env=`env:l4_entry list` and body=`body:l4_expr` in
  GENL [env;body](REWRITE_RULE [APPEND_NIL;ETA_AX]
    (SPECL [env;`[]:l4_expr list`;body] l4_edef_pred_evaluation_in_context));;
