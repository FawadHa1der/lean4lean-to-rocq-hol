(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Conditional literal evaluation, derived from existing typed rules. *)
needs "hol/environment_rules.ml";;

let l4_edef_nat_recurrence =
  let env=`env:l4_entry list` and g=`g:l4_expr list`
  and f=`f:l4_expr` and m=`m:num` and n=`n:num` in
  let nat=`L4Const l4_nat_name []`
  and succ=`L4Const (L4String l4_nat_name [115;117;99;99]) []` in
  let app x y=list_mk_comb(`L4App`,[x;y]) in
  let lit x=mk_comb(`L4NatLit`,x) in
  let sum x y=list_mk_comb(`(+):num->num->num`,[x;y]) in
  let unary=list_mk_comb(`L4Pi`,[`L4Anonymous`;nat;nat]) in
  let judgment x y ty=list_mk_comb(`l4_edef`,[env;g;x;y;ty]) in
  let goal k=judgment (app f (lit k)) (lit(sum m k)) nat in
  let premise=list_mk_conj [judgment f f unary;judgment succ succ unary;
    judgment (app f (lit `0`)) (lit m) nat;
    mk_forall(n,judgment (app f (app succ (lit n)))
      (app succ (app f (lit n))) nat)] in
  let hf,hs,hzero,hrec=match CONJUNCTS(ASSUME premise) with
    | [a;b;c;d]->a,b,c,d | _->failwith "Nat recurrence premise arity" in
  let rules=CONJUNCTS l4_edef_RULES in
  let use i arguments premises =
    let th=REWRITE_RULE [l4_inst;l4_subst] (SPECL (env::g::arguments) (List.nth rules i)) in
    MP th (if List.length premises=1 then List.hd premises else end_itlist CONJ premises) in
  let congr x y a b hx hab=use 2 [x;y;a;b;`L4Anonymous`;nat;nat] [hx;hab] in
  let trans x y z hxy hyz=use 7 [x;y;z;nat] [hxy;hyz] in
  let sym x y h=use 6 [x;y;nat] [h] in
  let numeral_step k=use 18 [k] [hs] in
  let h1=congr f f (lit(mk_comb(`SUC`,n))) (app succ(lit n)) hf (numeral_step n) in
  let h2=SPEC n hrec in
  let h3=congr succ succ (app f(lit n)) (lit(sum m n)) hs (ASSUME(goal n)) in
  let h4=sym (lit(mk_comb(`SUC`,sum m n))) (app succ(lit(sum m n))) (numeral_step(sum m n)) in
  let first=trans (app f(lit(mk_comb(`SUC`,n))))
    (app f(app succ(lit n))) (app succ(app f(lit n))) h1 h2 in
  let second=trans (app f(lit(mk_comb(`SUC`,n))))
    (app succ(app f(lit n))) (app succ(lit(sum m n))) first h3 in
  let step=trans (app f(lit(mk_comb(`SUC`,n))))
    (app succ(lit(sum m n))) (lit(mk_comb(`SUC`,sum m n))) second h4 in
  let induction=REWRITE_RULE [ADD_CLAUSES]
    (BETA_RULE(SPEC (mk_abs(n,goal n)) num_INDUCTION)) in
  let result=MP induction (CONJ hzero (GEN n (DISCH (goal n) step))) in
  let theorem=GENL [env;g;f;m] (DISCH premise result) in
  if hyp theorem<>[] || frees(concl theorem)<>[] then
    failwith "open Nat recurrence theorem";
  theorem;;
