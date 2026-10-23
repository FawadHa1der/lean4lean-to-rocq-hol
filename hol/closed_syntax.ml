(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Syntactic binder scope only: this predicate does not assert typing. *)
needs "hol/syntax.ml";;

let l4_scoped = new_recursive_definition l4_expr_RECURSION
 `(l4_scoped (L4BVar i) k <=> i < k) /\
  (l4_scoped (L4Sort u) k <=> T) /\
  (l4_scoped (L4Const n us) k <=> T) /\
  (l4_scoped (L4App f a) k <=> l4_scoped f k /\ l4_scoped a k) /\
  (l4_scoped (L4Lam n a b) k <=> l4_scoped a k /\ l4_scoped b (SUC k)) /\
  (l4_scoped (L4Pi n a b) k <=> l4_scoped a k /\ l4_scoped b (SUC k)) /\
  (l4_scoped (L4Let n a v b) k <=>
    l4_scoped a k /\ l4_scoped v k /\ l4_scoped b (SUC k)) /\
  (l4_scoped (L4NatLit lit) k <=> T) /\
  (l4_scoped (L4Proj n i e) k <=> l4_scoped e k) /\
  (l4_scoped (L4StrLit chars) k <=> T)`;;

let l4_lift_scoped = prove
 (`!e. !k. l4_scoped e k ==> !d. l4_lift e d k = e`,
  MATCH_MP_TAC l4_expr_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_scoped;l4_lift] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;

let l4_subst_scoped = prove
 (`!e. !k. l4_scoped e k ==> !s. l4_subst e k s = e`,
  MATCH_MP_TAC l4_expr_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_scoped;l4_subst] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;

let l4_scoped_mono = prove
 (`!e. !k. l4_scoped e k ==> !j. k <= j ==> l4_scoped e j`,
  MATCH_MP_TAC l4_expr_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_scoped] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC [ARITH_RULE `i < k /\ k <= j ==> i < j`;
                 ARITH_RULE `k <= j ==> SUC k <= SUC j`]);;

let l4_lift_closed = prove
 (`!e. l4_scoped e 0 ==> !d k. l4_lift e d k = e`,
  MESON_TAC [l4_lift_scoped;l4_scoped_mono;LE_0]);;

let l4_subst_closed = prove
 (`!e. l4_scoped e 0 ==> !k s. l4_subst e k s = e`,
  MESON_TAC [l4_subst_scoped;l4_scoped_mono;LE_0]);;

let l4_inst_closed = prove
 (`!e. l4_scoped e 0 ==> !s. l4_inst s e = e`,
  REWRITE_TAC [l4_inst] THEN MESON_TAC [l4_subst_scoped]);;
