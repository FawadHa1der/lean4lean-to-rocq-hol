(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Typed substitution derived from existing lambda, application and beta rules.
   No new object-language rule or HOL axiom is introduced. *)
needs "hol/judgments.ml";;
needs "hol/environment_rules.ml";;

let l4_defeq_instantiation,l4_edef_instantiation =
  let derive prefix judgment rules =
    let g=`g:l4_expr list` and n=`L4Anonymous` and a=`a:l4_expr`
    and u=`u:l4_level` and e=`e:l4_expr` and f=`f:l4_expr`
    and t=`t:l4_expr` and v=`v:l4_expr` in
    let j gamma x y ty = list_mk_comb(judgment,[gamma;x;y;ty]) in
    let bind=list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[a;g]) in
    let sort=mk_comb(`L4Sort`,u) in
    let lam x=list_mk_comb(`L4Lam`,[n;a;x]) in
    let app x=mk_comb(mk_comb(`L4App`,lam x),v) in
    let inst x=mk_comb(mk_comb(`l4_inst`,v),x) in
    let premise=list_mk_conj [j g a a sort;j bind e f t;j g v v a] in
    let ha,hef,hv=match CONJUNCTS(ASSUME premise) with
      | [ha;hef;hv] -> ha,hef,hv
      | _ -> failwith "instantiation premise arity" in
    let use i args hypotheses =
      MP (SPECL (prefix@args) (List.nth rules i))
         (if List.length hypotheses=1 then List.hd hypotheses else end_itlist CONJ hypotheses) in
    let sym gamma x y ty h=use 6 [gamma;x;y;ty] [h] in
    let trans gamma x y z ty h k=use 7 [gamma;x;y;z;ty] [h;k] in
    let hfe=sym bind e f t hef in
    let he=trans bind e f e t hef hfe and hf=trans bind f e f t hfe hef in
    let hl=use 3 [g;n;n;a;a;e;f;t;u] [ha;hef] in
    let happ=use 2 [g;lam e;lam f;v;v;n;a;t] [hl;hv] in
    let hb1=use 8 [g;n;a;e;t;v] [he;hv]
    and hb2=use 8 [g;n;a;f;t;v] [hf;hv] in
    let first=trans g (inst e) (app e) (app f) (inst t)
      (sym g (app e) (inst e) (inst t) hb1) happ in
    let result=trans g (inst e) (app f) (inst f) (inst t) first hb2 in
    let theorem=GENL (prefix@[g;a;u;e;f;t;v]) (DISCH premise result) in
    if hyp theorem<>[] || frees(concl theorem)<>[] then
      failwith "open typed-instantiation certificate";
    theorem in
  derive [] `l4_defeq` (CONJUNCTS l4_defeq_RULES),
  derive [`env:l4_entry list`] (mk_comb(`l4_edef`,`env:l4_entry list`))
    (CONJUNCTS l4_edef_RULES);;

let l4_checked_instantiation = prove
 (`!policy env g a u e f t v.
    l4_checked policy env g a a (L4Sort u) /\
    l4_checked policy env (CONS a g) e f t /\
    l4_checked policy env g v v a ==>
    l4_checked policy env g (l4_inst v e) (l4_inst v f) (l4_inst v t)`,
  REWRITE_TAC [l4_checked] THEN MESON_TAC [l4_edef_instantiation]);;
