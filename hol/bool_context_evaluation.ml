(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Two-dimensional numeral comparison from the existing four symbolic laws.
   This is a theorem derivation, not a new object-language reduction rule. *)
needs "hol/instantiation_certificates.ml";;
needs "hol/closed_syntax.ml";;

let l4_edef_beq_evaluation_in_context,l4_edef_ble_evaluation_in_context =
  let derive contract_definition predicate =
    let env=`env:l4_entry list` and context=`g:l4_expr list`
    and body=`body:l4_expr` and m=`m:num` and n=`n:num` in
    let nat=`L4Const l4_nat_name []` and bool=`L4Const l4_bool_name []`
    and zero=`L4Const (L4String l4_nat_name [122;101;114;111]) []`
    and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []`
    and tru=`L4Const (L4String l4_bool_name [116;114;117;101]) []`
    and fal=`L4Const (L4String l4_bool_name [102;97;108;115;101]) []`
    and level=`L4Succ L4Zero` in
    let pi a b=list_mk_comb(`L4Pi`,[`L4Anonymous`;a;b]) in
    let one=list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[nat;context]) in
    let app f x=list_mk_comb(`L4App`,[f;x]) in
    let app2 f x y=app(app f x)y in
    let lit k=mk_comb(`L4NatLit`,k) and suc k=mk_comb(`SUC`,k) in
    let j g x y a=list_mk_comb(`l4_edef`,[env;g;x;y;a]) in
    let typed g a=j g a a(mk_comb(`L4Sort`,level)) in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,list_mk_comb(`l4_edef`,[env;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;context])])) in
    let contract=lhs(concl(SPECL [relative;body] contract_definition)) in
    let premise=list_mk_conj [list_mk_comb(`l4_scoped`,[body;`0`]);contract;
      typed context nat;typed one nat;j context zero zero nat;
      j context succ succ(pi nat nat);typed context bool;
      j context tru tru bool;j context fal fal bool] in
    let scope,law,hn0,hn1,hz,hs=match CONJUNCTS(ASSUME premise) with
      | [a;b;c;d;e;f;_;_;_]->a,b,c,d,e,f
      | _->failwith "comparison evaluation premise arity" in
    let notation=[APPEND;contract_definition;l4_prim_bool_cases_contract;
      l4_prim_bool_binary;l4_prim_bool;l4_prim_nat;l4_prim_zero;l4_prim_succ;
      l4_prim_true;l4_prim_false] in
    let hb,h00,h0s,hs0,hss=match CONJUNCTS(REWRITE_RULE notation law) with
      | [a;b;c;d;e]->a,b,c,d,e | _->failwith "comparison contract arity" in
    let body_subst=MP(SPEC body l4_subst_closed) scope
    and body_lift=MP(SPEC body l4_lift_closed) scope in
    let simplify=REWRITE_CONV [l4_inst;l4_subst;l4_lift;body_subst;body_lift]
      THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
    let rules=CONJUNCTS l4_edef_RULES in
    let use g i args proofs =
      let th=CONV_RULE simplify(SPECL(env::g::args)(List.nth rules i)) in
      MP th(if List.length proofs=1 then List.hd proofs else end_itlist CONJ proofs) in
    let literal g k ht=use g 16 [k] [ht] in
    let instantiate g value hx hd hv =
      let _,args=strip_comb(concl hx) in
      let x,y,a=match args with [_;_;x;y;a]->x,y,a
        | _->failwith "comparison instantiation arity" in
      CONV_RULE simplify(MP(SPECL [env;g;nat;level;x;y;a;value] l4_edef_instantiation)
        (CONJ hd(CONJ hx hv))) in
    let congr x x' y y' hx hy =
      let hf=use context 2 [body;body;x;x';`L4Anonymous`;nat;pi nat bool] [hb;hx] in
      use context 2 [app body x;app body x';y;y';`L4Anonymous`;nat;bool] [hf;hy] in
    let trans x y z h k=use context 7 [x;y;z;bool] [h;k] in
    let lm=lit m and ln=lit n in
    let literal_zero=use context 17 [] [hz] in
    let sm=app succ lm and sn=app succ ln in
    let nextm=lit(suc m) and nextn=lit(suc n) in
    let literal_sm=use context 18 [m] [hs]
    and literal_sn=use context 18 [n] [hs] in
    let base00=trans (app2 body(lit `0`)(lit `0`)) (app2 body zero zero) tru
      (congr (lit `0`) zero (lit `0`) zero literal_zero literal_zero) h00 in
    let base0s=instantiate context ln h0s hn0(literal context n hn0) in
    let _,args=strip_comb(concl base0s) in
    let out0s=List.nth args 3 in
    let base0s=trans (app2 body(lit `0`)nextn) (app2 body zero sn) out0s
      (congr (lit `0`) zero nextn sn literal_zero literal_sn) base0s in
    let bases0=instantiate context lm hs0 hn0(literal context m hn0) in
    let bases0=trans (app2 body nextm(lit `0`)) (app2 body sm zero) fal
      (congr nextm sm (lit `0`) zero literal_sm literal_zero) bases0 in
    let diagonal=instantiate context lm
      (instantiate one ln hss hn1(literal one n hn1)) hn0(literal context m hn0) in
    let diagonal=trans (app2 body nextm nextn) (app2 body sm sn) (app2 body lm ln)
      (congr nextm sm nextn sn literal_sm literal_sn) diagonal in
    let result a b=mk_cond(list_mk_comb(predicate,[a;b]),tru,fal) in
    let goal a b=j context(app2 body(lit a)(lit b))(result a b) bool in
    let arithmetic=[CONJUNCT1 LE;LE_0;LE_SUC;NOT_SUC;GSYM NOT_SUC;SUC_INJ] in
    let align tm th=EQ_MP(SYM(REWRITE_CONV arithmetic tm)) th in
    (* The inner induction is repeated for zero and successor outer arguments.
       The diagonal uses the outer hypothesis at n, not finite examples. *)
    let induct var property base step =
      MP(BETA_RULE(SPEC(mk_abs(var,property)) num_INDUCTION))
        (CONJ base(GEN var(DISCH property step))) in
    let at_zero=induct n (goal `0` n) (align(goal `0` `0`) base00)
      (align(goal `0`(suc n)) base0s) in
    let outer=mk_forall(n,goal m n) in
    let step=trans (app2 body nextm nextn) (app2 body lm ln) (result m n)
      diagonal(SPEC n(ASSUME outer)) in
    let at_successor=induct n (goal(suc m)n) (align(goal(suc m)`0`) bases0)
      (align(goal(suc m)(suc n)) step) in
    let all=induct m outer at_zero at_successor in
    let theorem=GENL [env;context;body](DISCH premise all) in
    if hyp theorem<>[] || frees(concl theorem)<>[] then
      failwith "open contextual Boolean comparison theorem";
    theorem in
  derive l4_prim_beq_contract `(=):num->num->bool`,
  derive l4_prim_ble_contract `(<=):num->num->bool`;;

let l4_edef_beq_evaluation_context_empty,l4_edef_ble_evaluation_context_empty =
  let empty theorem =
    let env=`env:l4_entry list` and body=`body:l4_expr` in
    GENL [env;body](REWRITE_RULE [APPEND_NIL;ETA_AX]
      (SPECL [env;`[]:l4_expr list`;body] theorem)) in
  empty l4_edef_beq_evaluation_in_context,empty l4_edef_ble_evaluation_in_context;;

let l4_checked_beq_evaluation_in_context,l4_checked_ble_evaluation_in_context =
  let checked theorem =
    let policy=`policy:l4_entry list` and env=`env:l4_entry list`
    and g=`g:l4_expr list` and body=`body:l4_expr`
    and m=`m:num` and n=`n:num` in
    let raw=SPECL [env;g;body] theorem in
    let premise,_=dest_imp(concl raw) in
    let valid=list_mk_comb(`l4_evalid`,[policy;env])
    and context=list_mk_comb(`l4_econtext`,[env;g]) in
    let whole=list_mk_conj [valid;context;premise] in
    let hv,hc,hp=match CONJUNCTS(ASSUME whole) with
      | hv::hc::rest->hv,hc,end_itlist CONJ rest
      | _->failwith "checked comparison premises" in
    let evaluation=SPECL [m;n](MP raw hp) in
    let _,args=strip_comb(concl evaluation) in
    let term=list_mk_comb(`l4_checked`,policy::args) in
    let proof=EQ_MP(SYM(REWRITE_CONV [l4_checked] term))
      (CONJ hv(CONJ hc evaluation)) in
    let result=GENL [policy;env;g;body](DISCH whole(GENL [m;n] proof)) in
    if hyp result<>[] || frees(concl result)<>[] then failwith "open checked comparison theorem";
    result in
  checked l4_edef_beq_evaluation_in_context,checked l4_edef_ble_evaluation_in_context;;
