(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of:
   1. Untyped parallel-reduction confluence (Takahashi complete development,
      triangle, diamond, strip, and Church-Rosser theorems on l4_vpar_red961 /
      l4_vpar_red_star961) and deterministic syntax-directed typing uniqueness
      (l4_vsyn_has_type_unique968, using l4_venv_wf_lookup_unique966), closing
      the gap between declarative_typing961.ml and rocq/DeclarativeTyping.v.
   2. Lean4Lean/Theory/LevelSat.lean: coNP-hardness of semantic universe level
      equivalence (l4_vlevel_equiv961) and inequality (l4_vlevel_le961) via a
      linear-size dual-rail reduction from CNF unsatisfiability.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/typing_lemmas966.ml";;

(* ========================================================================= *)
(* 1. Takahashi Complete Development & Untyped Beta Church-Rosser            *)
(* ========================================================================= *)

let l4_vpar_red_bvar968,
    l4_vpar_red_sort968,
    l4_vpar_red_const968,
    l4_vpar_red_app968,
    l4_vpar_red_lam968,
    l4_vpar_red_forall968,
    l4_vpar_red_beta968 =
  match CONJUNCTS l4_vpar_red_RULES961 with
  | [c1;c2;c3;c4;c5;c6;c7] -> (c1,c2,c3,c4,c5,c6,c7)
  | _ -> failwith "l4_vpar_red_RULES961: unexpected arity";;

let l4_vpar_red_lam_inv968 = prove
 (`!dom body e.
   l4_vpar_red961 (L4VLam961 dom body) e <=>
   ?dom' body'. e = L4VLam961 dom' body' /\
                l4_vpar_red961 dom dom' /\ l4_vpar_red961 body body'`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_CASES961] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vpar_red_vliftN_ind968 = prove
 (`!e1 e2.
   l4_vpar_red961 e1 e2 ==>
   (!n k. l4_vpar_red961 (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vpar_red_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
  [REWRITE_TAC [l4_vpar_red_bvar968];
   REWRITE_TAC [l4_vpar_red_sort968];
   REWRITE_TAC [l4_vpar_red_const968];
   MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vpar_red_lam968 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vpar_red_forall968 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vpar_red_beta968 THEN ASM_REWRITE_TAC []]);;

let l4_vpar_red_vliftN968 = prove
 (`!e1 e2 n k.
   l4_vpar_red961 e1 e2 ==>
   l4_vpar_red961 (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_vpar_red_vliftN_ind968]);;

let l4_vpar_red_vinst_ind968 = prove
 (`!e1 e2.
   l4_vpar_red961 e1 e2 ==>
   (!v1 v2 k.
      l4_vpar_red961 v1 v2 ==>
      l4_vpar_red961 (l4_vinst961 e1 v1 k) (l4_vinst961 e2 v2 k))`,
  MATCH_MP_TAC l4_vpar_red_INDUCT961 THEN
  REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
  REPEAT CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`i:num`;`v1:l4_vexpr961`;`v2:l4_vexpr961`;`k:num`] THEN
   DISCH_TAC THEN REWRITE_TAC [l4_vinst_var961] THEN
   ASM_CASES_TAC `i < k` THEN ASM_REWRITE_TAC [l4_vpar_red_bvar968] THEN
   ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC [l4_vpar_red_bvar968] THEN
   MATCH_MP_TAC l4_vpar_red_vliftN968 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vpar_red_sort968];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vpar_red_const968];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpar_red_lam968 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpar_red_forall968 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpar_red_beta968 THEN ASM_MESON_TAC []]);;

let l4_vpar_red_vinst968 = prove
 (`!e1 e2 v1 v2 k.
   l4_vpar_red961 e1 e2 /\ l4_vpar_red961 v1 v2 ==>
   l4_vpar_red961 (l4_vinst961 e1 v1 k) (l4_vinst961 e2 v2 k)`,
  MESON_TAC [l4_vpar_red_vinst_ind968]);;

let l4_vpar_red_vinst0968 = prove
 (`!b1 b2 a1 a2.
   l4_vpar_red961 b1 b2 /\ l4_vpar_red961 a1 a2 ==>
   l4_vpar_red961 (l4_vinst0961 b1 a1) (l4_vinst0961 b2 a2)`,
  REWRITE_TAC [l4_vinst0961] THEN MESON_TAC [l4_vpar_red_vinst968]);;

let l4_vis_vlam968 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vis_vlam968 (L4VBVar961 i) <=> F) /\
  (l4_vis_vlam968 (L4VSort961 u) <=> F) /\
  (l4_vis_vlam968 (L4VConst961 c ls) <=> F) /\
  (l4_vis_vlam968 (L4VApp961 f a) <=> F) /\
  (l4_vis_vlam968 (L4VLam961 dom body) <=> T) /\
  (l4_vis_vlam968 (L4VForallE961 dom cod) <=> F)`;;

let l4_vlam_body968 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vlam_body968 (L4VBVar961 i) = L4VBVar961 i) /\
  (l4_vlam_body968 (L4VSort961 u) = L4VSort961 u) /\
  (l4_vlam_body968 (L4VConst961 c ls) = L4VConst961 c ls) /\
  (l4_vlam_body968 (L4VApp961 f a) = L4VApp961 f a) /\
  (l4_vlam_body968 (L4VLam961 dom body) = body) /\
  (l4_vlam_body968 (L4VForallE961 dom cod) = cod)`;;

let l4_vcomplete_dev968 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vcomplete_dev968 (L4VBVar961 i) = L4VBVar961 i) /\
  (l4_vcomplete_dev968 (L4VSort961 u) = L4VSort961 u) /\
  (l4_vcomplete_dev968 (L4VConst961 c ls) = L4VConst961 c ls) /\
  (l4_vcomplete_dev968 (L4VApp961 f a) =
    if l4_vis_vlam968 f
    then l4_vinst0961 (l4_vlam_body968 (l4_vcomplete_dev968 f)) (l4_vcomplete_dev968 a)
    else L4VApp961 (l4_vcomplete_dev968 f) (l4_vcomplete_dev968 a)) /\
  (l4_vcomplete_dev968 (L4VLam961 dom body) =
    L4VLam961 (l4_vcomplete_dev968 dom) (l4_vcomplete_dev968 body)) /\
  (l4_vcomplete_dev968 (L4VForallE961 dom cod) =
    L4VForallE961 (l4_vcomplete_dev968 dom) (l4_vcomplete_dev968 cod))`;;

let l4_vpar_red_self_dev968 = prove
 (`!e. l4_vpar_red961 e (l4_vcomplete_dev968 e)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_bvar968];
   GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_sort968];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_const968];
   MAP_EVERY X_GEN_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `f:l4_vexpr961` (cases "l4_vexpr961")) THENL
   [STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vcomplete_dev968;l4_vis_vlam968;l4_vlam_body968;
                 l4_vpar_red_lam_inv968;injectivity "l4_vexpr961"] THEN
    STRIP_TAC THEN MATCH_MP_TAC l4_vpar_red_beta968 THEN ASM_MESON_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vcomplete_dev968] THEN
   MATCH_MP_TAC l4_vpar_red_lam968 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vcomplete_dev968] THEN
   MATCH_MP_TAC l4_vpar_red_forall968 THEN ASM_REWRITE_TAC []]);;

let l4_vpar_red_STRONG_INDUCT968 =
  derive_strong_induction (l4_vpar_red_RULES961, l4_vpar_red_INDUCT961);;

let l4_vpar_red_triangle968 = prove
 (`!e1 e2. l4_vpar_red961 e1 e2 ==> l4_vpar_red961 e2 (l4_vcomplete_dev968 e1)`,
  MATCH_MP_TAC l4_vpar_red_STRONG_INDUCT968 THEN
  REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_bvar968];
   GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_sort968];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vpar_red_const968];
   MAP_EVERY X_GEN_TAC [`f:l4_vexpr961`;`f':l4_vexpr961`;`a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `f:l4_vexpr961` (cases "l4_vexpr961")) THENL
   [STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vcomplete_dev968;l4_vis_vlam968;l4_vlam_body968;l4_vpar_red_lam_inv968] THEN
    STRIP_TAC THEN l4_subst_vars_tac966 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpar_red_lam_inv968;injectivity "l4_vexpr961"]) THEN
    MATCH_MP_TAC l4_vpar_red_beta968 THEN ASM_MESON_TAC [];
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [l4_vcomplete_dev968] THEN
    REWRITE_TAC [l4_vis_vlam968] THEN MATCH_MP_TAC l4_vpar_red_app968 THEN ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vcomplete_dev968] THEN
   MATCH_MP_TAC l4_vpar_red_lam968 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vcomplete_dev968] THEN
   MATCH_MP_TAC l4_vpar_red_forall968 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vcomplete_dev968;l4_vis_vlam968;l4_vlam_body968] THEN
   MATCH_MP_TAC l4_vpar_red_vinst0968 THEN ASM_REWRITE_TAC []]);;

let l4_vpar_red_diamond968 = prove
 (`!e e1 e2.
   l4_vpar_red961 e e1 /\ l4_vpar_red961 e e2 ==>
   ?e3. l4_vpar_red961 e1 e3 /\ l4_vpar_red961 e2 e3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `l4_vcomplete_dev968 e` THEN
  ASM_SIMP_TAC [l4_vpar_red_triangle968]);;

let l4_vpar_red_strip_ind968 = prove
 (`!e e2.
   l4_vpar_red_star961 e e2 ==>
   (!e1. l4_vpar_red961 e e1 ==>
     ?e3. l4_vpar_red_star961 e1 e3 /\ l4_vpar_red961 e2 e3)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN CONJ_TAC THENL
  [MESON_TAC [l4_vpar_red_star_refl961];
   MAP_EVERY X_GEN_TAC [`e:l4_vexpr961`;`a:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRIP_TAC THEN X_GEN_TAC `e1:l4_vexpr961` THEN DISCH_TAC THEN
   MP_TAC (SPECL [`e:l4_vexpr961`;`a:l4_vexpr961`;`e1:l4_vexpr961`] l4_vpar_red_diamond968) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `b:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `b:l4_vexpr961`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e3:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `e3:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vpar_red_star_RULES961]]);;

let l4_vpar_red_strip968 = prove
 (`!e e1 e2.
   l4_vpar_red961 e e1 /\ l4_vpar_red_star961 e e2 ==>
   ?e3. l4_vpar_red_star961 e1 e3 /\ l4_vpar_red961 e2 e3`,
  MESON_TAC [l4_vpar_red_strip_ind968]);;

let l4_vpar_red_star_cr_ind968 = prove
 (`!e e1.
   l4_vpar_red_star961 e e1 ==>
   (!e2. l4_vpar_red_star961 e e2 ==>
     ?e3. l4_vpar_red_star961 e1 e3 /\ l4_vpar_red_star961 e2 e3)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN CONJ_TAC THENL
  [MESON_TAC [l4_vpar_red_star_refl961];
   MAP_EVERY X_GEN_TAC [`e:l4_vexpr961`;`a:l4_vexpr961`;`e1:l4_vexpr961`] THEN
   STRIP_TAC THEN X_GEN_TAC `e2:l4_vexpr961` THEN DISCH_TAC THEN
   MP_TAC (SPECL [`e:l4_vexpr961`;`a:l4_vexpr961`;`e2:l4_vexpr961`] l4_vpar_red_strip968) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `b:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `b:l4_vexpr961`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e3:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `e3:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vpar_red_star_RULES961]]);;

let l4_vpar_red_star_church_rosser968 = prove
 (`!e e1 e2.
   l4_vpar_red_star961 e e1 /\ l4_vpar_red_star961 e e2 ==>
   ?e3. l4_vpar_red_star961 e1 e3 /\ l4_vpar_red_star961 e2 e3`,
  MESON_TAC [l4_vpar_red_star_cr_ind968]);;

(* ========================================================================= *)
(* 2. Syntax-Directed Bidirectional Typing Uniqueness                        *)
(* ========================================================================= *)

let l4_vlookup_deterministic_ind968 = prove
 (`!g i ty1.
   l4_vlookup961 g i ty1 ==>
   (!ty2. l4_vlookup961 g i ty2 ==> ty1 = ty2)`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num"] THEN MESON_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN AP_TERM_TAC THEN ASM_MESON_TAC []]);;

let l4_vlookup_deterministic968 = prove
 (`!g i ty1 ty2.
   l4_vlookup961 g i ty1 /\ l4_vlookup961 g i ty2 ==> ty1 = ty2`,
  MESON_TAC [l4_vlookup_deterministic_ind968]);;

let l4_vsyn_has_type_RULES968,l4_vsyn_has_type_INDUCT968,l4_vsyn_has_type_CASES968 =
  new_inductive_definition
 `(!env uvars g i ty.
     l4_vlookup961 g i ty ==>
     l4_vsyn_has_type968 env uvars g (L4VBVar961 i) ty) /\
  (!env uvars g u.
     l4_vlevel_wf961 uvars u ==>
     l4_vsyn_has_type968 env uvars g (L4VSort961 u) (L4VSort961 (L4VLSucc961 u))) /\
  (!env uvars g c ci ls.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vc_uvars961 ci ==>
     l4_vsyn_has_type968 env uvars g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci))) /\
  (!env uvars g f a dom cod.
     l4_vsyn_has_type968 env uvars g f (L4VForallE961 dom cod) /\
     l4_vsyn_has_type968 env uvars g a dom ==>
     l4_vsyn_has_type968 env uvars g (L4VApp961 f a) (l4_vinst0961 cod a)) /\
  (!env uvars g dom body u cod.
     l4_vsyn_has_type968 env uvars g dom (L4VSort961 u) /\
     l4_vsyn_has_type968 env uvars (CONS dom g) body cod ==>
     l4_vsyn_has_type968 env uvars g (L4VLam961 dom body) (L4VForallE961 dom cod)) /\
  (!env uvars g dom cod u v.
     l4_vsyn_has_type968 env uvars g dom (L4VSort961 u) /\
     l4_vsyn_has_type968 env uvars (CONS dom g) cod (L4VSort961 v) ==>
     l4_vsyn_has_type968 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)))`;;

let l4_all2_vlevel_equiv_refl968 = prove
 (`!ls. ALL2 l4_vlevel_equiv961 ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]);;

let l4_vsyn_has_type_sound968 = prove
 (`!env uvars g e ty.
   l4_vsyn_has_type968 env uvars g e ty ==> l4_vhas_type961 env uvars g e ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vsyn_has_type_INDUCT968 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_bvar961];
   MESON_TAC [l4_vis_defeq_sort961;l4_vlevel_equiv_refl961];
   MESON_TAC [l4_vis_defeq_const961;l4_all2_vlevel_equiv_refl968];
   MESON_TAC [l4_vis_defeq_app961];
   MESON_TAC [l4_vis_defeq_lam961];
   MESON_TAC [l4_vis_defeq_forall961]]);;

let l4_vsyn_has_type_unique_ind968 = prove
 (`!env uvars g e ty1.
   l4_vsyn_has_type968 env uvars g e ty1 ==>
   (!ty2.
      l4_venv_wf966 env /\ l4_vsyn_has_type968 env uvars g e ty2 ==>
      ty1 = ty2)`,
  MATCH_MP_TAC l4_vsyn_has_type_INDUCT968 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   ASM_MESON_TAC [l4_vlookup_deterministic968];
   (* sort *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   MESON_TAC [];
   (* const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   ASM_MESON_TAC [l4_venv_wf_lookup_unique966];
   (* app *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [injectivity "l4_vexpr961"];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN AP_TERM_TAC THEN ASM_MESON_TAC [];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsyn_has_type_CASES968] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN
   REWRITE_TAC [injectivity "l4_vexpr961";injectivity "l4_vlevel961"] THEN
   ASM_MESON_TAC [injectivity "l4_vexpr961"]]);;

let l4_vsyn_has_type_unique968 = prove
 (`!env uvars g e ty1 ty2.
   l4_venv_wf966 env /\
   l4_vsyn_has_type968 env uvars g e ty1 /\
   l4_vsyn_has_type968 env uvars g e ty2 ==>
   ty1 = ty2`,
  MESON_TAC [l4_vsyn_has_type_unique_ind968]);;

(* ========================================================================= *)
(* 3. Lean4Lean/Theory/LevelSat.lean: CNF Formulas & Dual-Rail Levels        *)
(* ========================================================================= *)

let l4_lit_INDUCT968,l4_lit_RECURSION968 = define_type
 "l4_lit968 = L4Lit968 num bool";;

let l4_lit_var968 = new_recursive_definition l4_lit_RECURSION968
 `l4_lit_var968 (L4Lit968 i pol) = i`;;

let l4_lit_pol968 = new_recursive_definition l4_lit_RECURSION968
 `l4_lit_pol968 (L4Lit968 i pol) = pol`;;

let l4_lit_wf968 = new_definition
 `l4_lit_wf968 n l <=> l4_lit_var968 l < n`;;

let l4_cnf_wf968 = new_definition
 `l4_cnf_wf968 n (phi:(l4_lit968 list) list) <=> ALL (ALL (l4_lit_wf968 n)) phi`;;

let l4_clause_sat968 = new_definition
 `l4_clause_sat968 (a:num->bool) (c:l4_lit968 list) <=>
   ?l. MEM l c /\ (a (l4_lit_var968 l) <=> l4_lit_pol968 l)`;;

let l4_cnf_sat968 = new_definition
 `l4_cnf_sat968 (phi:(l4_lit968 list) list) <=>
   ?a:num->bool. !c. MEM c phi ==> l4_clause_sat968 a c`;;

let l4_lvl_yes968 = new_definition
 `l4_lvl_yes968 (i:num) = 2 * i`;;

let l4_lvl_no968 = new_definition
 `l4_lvl_no968 (i:num) = 2 * i + 1`;;

let l4_lvl_rail968 = new_definition
 `l4_lvl_rail968 l =
   if l4_lit_pol968 l then l4_lvl_yes968 (l4_lit_var968 l)
   else l4_lvl_no968 (l4_lit_var968 l)`;;

let l4_lvl_rail_lt968 = prove
 (`!n l. l4_lit_wf968 n l ==> l4_lvl_rail968 l < 2 * n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_lit_wf968;l4_lvl_rail968;l4_lvl_yes968;l4_lvl_no968] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let l4_lvl_two968 = new_definition
 `l4_lvl_two968 = L4VLSucc961 (L4VLSucc961 L4VLZero961)`;;

let l4_clause_lvl968 = new_recursive_definition list_RECURSION
 `(l4_clause_lvl968 [] = L4VLZero961) /\
  (l4_clause_lvl968 (CONS l c) =
    L4VLMax961 (L4VLParam961 (l4_lvl_rail968 l)) (l4_clause_lvl968 c))`;;

let l4_foldl_imax968 = new_recursive_definition list_RECURSION
 `(l4_foldl_imax968 [] b = b) /\
  (l4_foldl_imax968 (CONS g gs) b = l4_foldl_imax968 gs (L4VLIMax961 b g))`;;

let l4_lvl_gates968 = new_definition
 `l4_lvl_gates968 phi = l4_foldl_imax968 (MAP l4_clause_lvl968 phi) l4_lvl_two968`;;

let l4_lvl_var968 = new_definition
 `l4_lvl_var968 i =
   L4VLMax961 (L4VLParam961 (l4_lvl_yes968 i))
     (L4VLIMax961 (L4VLIMax961 l4_lvl_two968 (L4VLParam961 (l4_lvl_yes968 i)))
                  (L4VLParam961 (l4_lvl_no968 i)))`;;

let l4_lvl_small968 = new_recursive_definition num_RECURSION
 `(l4_lvl_small968 0 = L4VLZero961) /\
  (l4_lvl_small968 (SUC i) = L4VLMax961 (l4_lvl_small968 i) (l4_lvl_var968 i))`;;

let l4_lvl_big968 = new_definition
 `l4_lvl_big968 n phi = L4VLMax961 (l4_lvl_small968 n) (l4_lvl_gates968 phi)`;;

(* ========================================================================= *)
(* 4. LevelSat Evaluation & Gate Lemmas                                      *)
(* ========================================================================= *)

let l4_eval_two968 = prove
 (`!ls. l4_vlevel_eval961 ls l4_lvl_two968 = 2`,
  GEN_TAC THEN REWRITE_TAC [l4_lvl_two968;l4_vlevel_eval961] THEN ARITH_TAC);;

let l4_eval_clause_lvl_le968 = prove
 (`!c ls bound.
   (!l. MEM l c ==> l4_vnth_nat961 ls (l4_lvl_rail968 l) <= bound) ==>
   l4_vlevel_eval961 ls (l4_clause_lvl968 c) <= bound`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_clause_lvl968;l4_vlevel_eval961;MEM;LE_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `l4_vnth_nat961 ls (l4_lvl_rail968 h) <= bound` ASSUME_TAC THENL
  [ASM_MESON_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vlevel_eval961 ls (l4_clause_lvl968 t) <= bound` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [];
   ASM_ARITH_TAC]);;

let l4_eval_clause_lvl_ne_zero968 = prove
 (`!c ls.
   ~(l4_vlevel_eval961 ls (l4_clause_lvl968 c) = 0) <=>
   (?l. MEM l c /\ ~(l4_vnth_nat961 ls (l4_lvl_rail968 l) = 0))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC [l4_clause_lvl968;l4_vlevel_eval961;MEM] THEN
  ASM_REWRITE_TAC [ARITH_RULE `~(MAX a b = 0) <=> ~(a = 0) \/ ~(b = 0)`] THEN
  MESON_TAC []);;

let l4_eval_foldl_imax_le968 = prove
 (`!gs ls bound b.
   (!g. MEM g gs ==> l4_vlevel_eval961 ls g <= bound) ==>
   l4_vlevel_eval961 ls (l4_foldl_imax968 gs b) <=
     MAX (l4_vlevel_eval961 ls b) bound`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_foldl_imax968;MEM] THENL
  [ARITH_TAC;
   DISCH_TAC THEN
   SUBGOAL_THEN `l4_vlevel_eval961 ls (l4_foldl_imax968 t (L4VLIMax961 b h)) <=
                 MAX (l4_vlevel_eval961 ls (L4VLIMax961 b h)) bound` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_eval961 ls h <= bound` MP_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_vlevel_eval961;l4_vlevel_imax_nat961] THEN
   COND_CASES_TAC THEN ARITH_TAC]);;

let l4_eval_foldl_imax_le_of_zero968 = prove
 (`!gs ls bound b.
   (!g. MEM g gs ==> l4_vlevel_eval961 ls g <= bound) /\
   (?g. MEM g gs /\ l4_vlevel_eval961 ls g = 0) ==>
   l4_vlevel_eval961 ls (l4_foldl_imax968 gs b) <= bound`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_foldl_imax968;MEM] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g0:l4_vlevel961` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ASM_CASES_TAC `l4_vlevel_eval961 ls h = 0` THENL
  [MP_TAC (SPECL [`t:l4_vlevel961 list`;`ls:num list`;`bound:num`;
                  `L4VLIMax961 b h`] l4_eval_foldl_imax_le968) THEN
   ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [l4_vlevel_eval961;l4_vlevel_imax_nat961] THEN ARITH_TAC];
   UNDISCH_TAC `g0:l4_vlevel961 = h \/ MEM g0 t` THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [UNDISCH_TAC `~(l4_vlevel_eval961 ls h = 0)` THEN ASM_SIMP_TAC [];
    FIRST_X_ASSUM (MP_TAC o SPECL [`ls:num list`;`bound:num`;`L4VLIMax961 b h`]) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
      EXISTS_TAC `g0:l4_vlevel961` THEN ASM_REWRITE_TAC []];
     SIMP_TAC []]]]);;

let l4_le_eval_foldl_imax968 = prove
 (`!gs ls b.
   (!g. MEM g gs ==> ~(l4_vlevel_eval961 ls g = 0)) ==>
   l4_vlevel_eval961 ls b <= l4_vlevel_eval961 ls (l4_foldl_imax968 gs b)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_foldl_imax968;MEM;LE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(l4_vlevel_eval961 ls h = 0)` ASSUME_TAC THENL
  [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vlevel_eval961 ls (L4VLIMax961 b h) <=
                l4_vlevel_eval961 ls (l4_foldl_imax968 t (L4VLIMax961 b h))` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC [l4_vlevel_eval961;l4_vlevel_imax_nat961] THEN ARITH_TAC);;

let l4_eval_var_eq968 = prove
 (`!i ls.
   l4_vlevel_eval961 ls (l4_lvl_var968 i) =
     if l4_vnth_nat961 ls (l4_lvl_no968 i) = 0 then l4_vnth_nat961 ls (l4_lvl_yes968 i)
     else if l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0 then l4_vnth_nat961 ls (l4_lvl_no968 i)
     else MAX 2 (MAX (l4_vnth_nat961 ls (l4_lvl_yes968 i))
                     (l4_vnth_nat961 ls (l4_lvl_no968 i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_lvl_var968;l4_vlevel_eval961;l4_vlevel_imax_nat961;l4_eval_two968] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let l4_yes_le_eval_var968 = prove
 (`!i ls. l4_vnth_nat961 ls (l4_lvl_yes968 i) <= l4_vlevel_eval961 ls (l4_lvl_var968 i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_eval_var_eq968] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let l4_no_le_eval_var968 = prove
 (`!i ls. l4_vnth_nat961 ls (l4_lvl_no968 i) <= l4_vlevel_eval961 ls (l4_lvl_var968 i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_eval_var_eq968] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let l4_two_le_eval_var968 = prove
 (`!i ls.
   ~(l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0) /\
   ~(l4_vnth_nat961 ls (l4_lvl_no968 i) = 0) ==>
   2 <= l4_vlevel_eval961 ls (l4_lvl_var968 i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [l4_eval_var_eq968] THEN
  ARITH_TAC);;

let l4_eval_var_le_one968 = prove
 (`!i ls.
   (l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0 \/
    l4_vnth_nat961 ls (l4_lvl_no968 i) = 0) /\
   l4_vnth_nat961 ls (l4_lvl_yes968 i) <= 1 /\
   l4_vnth_nat961 ls (l4_lvl_no968 i) <= 1 ==>
   l4_vlevel_eval961 ls (l4_lvl_var968 i) <= 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_eval_var_eq968] THEN
  STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let l4_le_eval_small968 = prove
 (`!n j ls. j < 2 * n ==> l4_vnth_nat961 ls j <= l4_vlevel_eval961 ls (l4_lvl_small968 n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [ARITH_TAC;
   REWRITE_TAC [l4_lvl_small968;l4_vlevel_eval961] THEN DISCH_TAC THEN
   ASM_CASES_TAC `j < 2 * n` THENL
   [FIRST_X_ASSUM (MP_TAC o SPECL [`j:num`;`ls:num list`]) THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC;
    SUBGOAL_THEN `j = l4_lvl_yes968 n \/ j = l4_lvl_no968 n` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC [l4_lvl_yes968;l4_lvl_no968] THEN ASM_ARITH_TAC;
     ASM_REWRITE_TAC [] THEN MP_TAC (SPECL [`n:num`;`ls:num list`] l4_yes_le_eval_var968) THEN ARITH_TAC;
     ASM_REWRITE_TAC [] THEN MP_TAC (SPECL [`n:num`;`ls:num list`] l4_no_le_eval_var968) THEN ARITH_TAC]]]);;

let l4_two_le_eval_small968 = prove
 (`!n i ls.
   i < n /\
   ~(l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0) /\
   ~(l4_vnth_nat961 ls (l4_lvl_no968 i) = 0) ==>
   2 <= l4_vlevel_eval961 ls (l4_lvl_small968 n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [ARITH_TAC;
   REWRITE_TAC [l4_lvl_small968;l4_vlevel_eval961] THEN STRIP_TAC THEN
   ASM_CASES_TAC `i < n` THENL
   [FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`ls:num list`]) THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC;
    SUBGOAL_THEN `i:num = n` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC (SPECL [`n:num`;`ls:num list`] l4_two_le_eval_var968) THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC]]);;

let l4_eval_small_le_one968 = prove
 (`!n ls.
   (!i. i < n ==>
     l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0 \/
     l4_vnth_nat961 ls (l4_lvl_no968 i) = 0) /\
   (!j. j < 2 * n ==> l4_vnth_nat961 ls j <= 1) ==>
   l4_vlevel_eval961 ls (l4_lvl_small968 n) <= 1`,
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC [l4_lvl_small968;l4_vlevel_eval961;LE_0] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l4_vlevel_eval961 ls (l4_lvl_small968 n) <= 1` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vlevel_eval961 ls (l4_lvl_var968 n) <= 1` MP_TAC THENL
  [MATCH_MP_TAC l4_eval_var_le_one968 THEN REPEAT CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [l4_lvl_yes968;l4_lvl_no968] THEN ARITH_TAC;
   ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* 5. Dual-Rail Assignment List & Main coNP-Hardness Reduction               *)
(* ========================================================================= *)

let l4_rail_list_from968 = new_recursive_definition num_RECURSION
 `(l4_rail_list_from968 (a:num->bool) base 0 = []) /\
  (l4_rail_list_from968 a base (SUC k) =
    CONS (if a base then 1 else 0)
      (CONS (if a base then 0 else 1)
        (l4_rail_list_from968 a (SUC base) k)))`;;

let l4_rail_list968 = new_definition
 `l4_rail_list968 n a = l4_rail_list_from968 a 0 n`;;

let l4_vnth_rail_list_from_le968 = prove
 (`!k a base j. l4_vnth_nat961 (l4_rail_list_from968 a base k) j <= 1`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_rail_list_from968;l4_vnth_nat961;LE_0] THEN
  COND_CASES_TAC THENL
  [COND_CASES_TAC THEN ARITH_TAC;
   COND_CASES_TAC THENL
   [COND_CASES_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC []]]);;

let l4_vnth_rail_list_le968 = prove
 (`!n a j. l4_vnth_nat961 (l4_rail_list968 n a) j <= 1`,
  REWRITE_TAC [l4_rail_list968;l4_vnth_rail_list_from_le968]);;

let l4_vnth_rail_list_from_pair968 = prove
 (`!m k a base.
   m < k ==>
   l4_vnth_nat961 (l4_rail_list_from968 a base k) (2 * m) =
     (if a (base + m) then 1 else 0) /\
   l4_vnth_nat961 (l4_rail_list_from968 a base k) (2 * m + 1) =
     (if a (base + m) then 0 else 1)`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN REPEAT GEN_TAC THEN TRY ARITH_TAC THENL
  [DISCH_TAC THEN
   REWRITE_TAC [ARITH_RULE `2 * 0 = 0 /\ 2 * 0 + 1 = 1 /\ 1 - 1 = 0 /\ ~(1 = 0)`;
                ADD_CLAUSES;l4_rail_list_from968;l4_vnth_nat961];
   DISCH_TAC THEN
   REWRITE_TAC [l4_rail_list_from968;
                ARITH_RULE `~(2 * SUC m = 0) /\ ~(2 * SUC m - 1 = 0) /\
                            (2 * SUC m - 1) - 1 = 2 * m /\
                            ~(2 * SUC m + 1 = 0) /\ ~((2 * SUC m + 1) - 1 = 0) /\
                            ((2 * SUC m + 1) - 1) - 1 = 2 * m + 1`;
                l4_vnth_nat961] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`a:num->bool`;`SUC base`]) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ADD_CLAUSES]]]);;

let l4_vnth_rail_list_yes968 = prove
 (`!n a i.
   i < n ==>
   l4_vnth_nat961 (l4_rail_list968 n a) (l4_lvl_yes968 i) =
     (if a i then 1 else 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_rail_list968;l4_lvl_yes968] THEN
  MP_TAC (SPECL [`i:num`;`n:num`;`a:num->bool`;`0`] l4_vnth_rail_list_from_pair968) THEN
  ASM_SIMP_TAC [ADD_CLAUSES]);;

let l4_vnth_rail_list_no968 = prove
 (`!n a i.
   i < n ==>
   l4_vnth_nat961 (l4_rail_list968 n a) (l4_lvl_no968 i) =
     (if a i then 0 else 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_rail_list968;l4_lvl_no968] THEN
  MP_TAC (SPECL [`i:num`;`n:num`;`a:num->bool`;`0`] l4_vnth_rail_list_from_pair968) THEN
  ASM_SIMP_TAC [ADD_CLAUSES]);;

let l4_vnth_rail_list_rail968 = prove
 (`!n a l.
   l4_lit_wf968 n l ==>
   l4_vnth_nat961 (l4_rail_list968 n a) (l4_lvl_rail968 l) =
     (if (a (l4_lit_var968 l) <=> l4_lit_pol968 l) then 1 else 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_lit_wf968;l4_lvl_rail968] THEN DISCH_TAC THEN
  ASM_CASES_TAC `l4_lit_pol968 l` THEN
  ASM_SIMP_TAC [l4_vnth_rail_list_yes968;l4_vnth_rail_list_no968] THEN
  COND_CASES_TAC THEN REWRITE_TAC []);;

let l4_small_le_big968 = prove
 (`!n phi. l4_vlevel_le961 (l4_lvl_small968 n) (l4_lvl_big968 n phi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlevel_le961;l4_lvl_big968;l4_vlevel_eval961] THEN
  GEN_TAC THEN ARITH_TAC);;

let l4_all_mem968 = prove
 (`!P (xs:A list). ALL P xs <=> (!x. MEM x xs ==> P x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL;MEM] THEN MESON_TAC []);;

let l4_big_equiv_small_iff_unsat968 = prove
 (`!n phi.
   l4_cnf_wf968 n phi ==>
   (l4_vlevel_equiv961 (l4_lvl_big968 n phi) (l4_lvl_small968 n) <=>
    ~l4_cnf_sat968 phi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_cnf_wf968;l4_all_mem968] THEN DISCH_TAC THEN
  EQ_TAC THENL
  [(* ==> *)
   REWRITE_TAC [l4_vlevel_equiv961;l4_cnf_sat968] THEN
   DISCH_TAC THEN DISCH_THEN (X_CHOOSE_TAC `a:num->bool`) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `l4_rail_list968 n a`) THEN
   SUBGOAL_THEN `l4_vlevel_eval961 (l4_rail_list968 n a) (l4_lvl_small968 n) <= 1`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_eval_small_le_one968 THEN
    REWRITE_TAC [l4_vnth_rail_list_le968] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC [l4_vnth_rail_list_yes968;l4_vnth_rail_list_no968] THEN
    COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `2 <= l4_vlevel_eval961 (l4_rail_list968 n a) (l4_lvl_gates968 phi)`
     MP_TAC THENL
   [REWRITE_TAC [l4_lvl_gates968] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM (SPEC `l4_rail_list968 n a` l4_eval_two968)] THEN
    MATCH_MP_TAC l4_le_eval_foldl_imax968 THEN
    REWRITE_TAC [MEM_MAP] THEN X_GEN_TAC `g:l4_vlevel961` THEN
    DISCH_THEN (X_CHOOSE_THEN `c:l4_lit968 list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [l4_eval_clause_lvl_ne_zero968] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `c:l4_lit968 list`) THEN ASM_REWRITE_TAC [l4_clause_sat968] THEN
    DISCH_THEN (X_CHOOSE_THEN `l:l4_lit968` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:l4_lit968` THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `l4_lit_wf968 n l` ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [l4_vnth_rail_list_rail968] THEN ARITH_TAC;
    REWRITE_TAC [l4_lvl_big968;l4_vlevel_eval961] THEN ASM_ARITH_TAC];
   (* <== *)
   REWRITE_TAC [l4_vlevel_equiv961] THEN DISCH_TAC THEN X_GEN_TAC `ls:num list` THEN
   ASM_CASES_TAC `l4_vlevel_eval961 ls (l4_lvl_big968 n phi) =
                  l4_vlevel_eval961 ls (l4_lvl_small968 n)` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `l4_cnf_sat968 phi` (fun th -> ASM_MESON_TAC [th]) THEN
   REWRITE_TAC [l4_cnf_sat968] THEN
   EXISTS_TAC `\i:num. ~(l4_vnth_nat961 ls (l4_lvl_yes968 i) = 0)` THEN
   SUBGOAL_THEN `!c. MEM c phi ==>
                     l4_vlevel_eval961 ls (l4_clause_lvl968 c) <=
                     l4_vlevel_eval961 ls (l4_lvl_small968 n)` ASSUME_TAC THENL
   [X_GEN_TAC `c:l4_lit968 list` THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_eval_clause_lvl_le968 THEN
    X_GEN_TAC `l:l4_lit968` THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_le_eval_small968 THEN
    MATCH_MP_TAC l4_lvl_rail_lt968 THEN ASM_MESON_TAC [];
    ALL_TAC] THEN
   X_GEN_TAC `c:l4_lit968 list` THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(l4_vlevel_eval961 ls (l4_clause_lvl968 c) = 0)` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC (SPECL [`MAP l4_clause_lvl968 phi`;`ls:num list`;
                   `l4_vlevel_eval961 ls (l4_lvl_small968 n)`;`l4_lvl_two968`]
      l4_eval_foldl_imax_le_of_zero968) THEN
    ANTS_TAC THENL
    [REWRITE_TAC [MEM_MAP] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN (X_CHOOSE_THEN `c0:l4_lit968 list` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC [];
      EXISTS_TAC `l4_clause_lvl968 c` THEN ASM_REWRITE_TAC [] THEN
      EXISTS_TAC `c:l4_lit968 list` THEN ASM_REWRITE_TAC []];
     UNDISCH_TAC `~(l4_vlevel_eval961 ls (l4_lvl_big968 n phi) =
                    l4_vlevel_eval961 ls (l4_lvl_small968 n))` THEN
     REWRITE_TAC [l4_lvl_big968;l4_lvl_gates968;l4_vlevel_eval961] THEN
     ARITH_TAC];
    REWRITE_TAC [l4_eval_clause_lvl_ne_zero968;l4_clause_sat968] THEN
    DISCH_THEN (X_CHOOSE_THEN `l:l4_lit968` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:l4_lit968` THEN BETA_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `l4_lit_pol968 l` THENL
    [UNDISCH_TAC `~(l4_vnth_nat961 ls (l4_lvl_rail968 l) = 0)` THEN
     ASM_SIMP_TAC [l4_lvl_rail968];
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC (TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     SUBGOAL_THEN `~(l4_vnth_nat961 ls (l4_lvl_no968 (l4_lit_var968 l)) = 0)`
       ASSUME_TAC THENL
     [ASM_MESON_TAC [l4_lvl_rail968]; ALL_TAC] THEN
     SUBGOAL_THEN `l4_lit_var968 l < n` ASSUME_TAC THENL
     [REWRITE_TAC [GSYM l4_lit_wf968] THEN ASM_MESON_TAC []; ALL_TAC] THEN
     MP_TAC (SPECL [`n:num`;`l4_lit_var968 l`;`ls:num list`] l4_two_le_eval_small968) THEN
     ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
     MP_TAC (SPECL [`MAP l4_clause_lvl968 phi`;`ls:num list`;
                    `l4_vlevel_eval961 ls (l4_lvl_small968 n)`;`l4_lvl_two968`]
       l4_eval_foldl_imax_le968) THEN
     ANTS_TAC THENL
     [REWRITE_TAC [MEM_MAP] THEN GEN_TAC THEN
      DISCH_THEN (X_CHOOSE_THEN `c0:l4_lit968 list` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC [];
      ALL_TAC] THEN
     REWRITE_TAC [l4_eval_two968] THEN
     UNDISCH_TAC `~(l4_vlevel_eval961 ls (l4_lvl_big968 n phi) =
                    l4_vlevel_eval961 ls (l4_lvl_small968 n))` THEN
     REWRITE_TAC [l4_lvl_big968;l4_lvl_gates968;l4_vlevel_eval961] THEN
     ASM_ARITH_TAC]]]);;

let l4_level_equiv_iff_unsat968 = prove
 (`!n phi.
   l4_cnf_wf968 n phi ==>
   (l4_vlevel_equiv961 (l4_lvl_small968 n) (l4_lvl_big968 n phi) <=>
    ~l4_cnf_sat968 phi)`,
  MESON_TAC [l4_big_equiv_small_iff_unsat968;l4_vlevel_equiv_symm961]);;

let l4_vlevel_le_antisymm_iff968 = prove
 (`!u v. l4_vlevel_equiv961 u v <=> l4_vlevel_le961 u v /\ l4_vlevel_le961 v u`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_le961] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [LE_REFL];
   STRIP_TAC THEN GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ls:num list`) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ls:num list`) THEN ARITH_TAC]);;

let l4_level_le_iff_unsat968 = prove
 (`!n phi.
   l4_cnf_wf968 n phi ==>
   (l4_vlevel_le961 (l4_lvl_big968 n phi) (l4_lvl_small968 n) <=>
    ~l4_cnf_sat968 phi)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`n:num`;`phi:(l4_lit968 list) list`] l4_big_equiv_small_iff_unsat968) THEN
  ASM_SIMP_TAC [l4_vlevel_le_antisymm_iff968;l4_small_le_big968]);;

(* Unconditional variable bound wrapper for arbitrary untyped CNF formulas *)
let l4_clause_num_vars968 = new_recursive_definition list_RECURSION
 `(l4_clause_num_vars968 [] = 0) /\
  (l4_clause_num_vars968 (CONS l c) =
    MAX (SUC (l4_lit_var968 l)) (l4_clause_num_vars968 c))`;;

let l4_cnf_num_vars968 = new_recursive_definition list_RECURSION
 `(l4_cnf_num_vars968 [] = 0) /\
  (l4_cnf_num_vars968 (CONS c phi) =
    MAX (l4_clause_num_vars968 c) (l4_cnf_num_vars968 phi))`;;

let l4_clause_wf_mono968 = prove
 (`!c n1 n2. n1 <= n2 /\ ALL (l4_lit_wf968 n1) c ==> ALL (l4_lit_wf968 n2) c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [ALL;l4_lit_wf968;FORALL_SIMP] THEN
  REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC []]);;

let l4_clause_num_vars_wf968 = prove
 (`!c. ALL (l4_lit_wf968 (l4_clause_num_vars968 c)) c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_clause_num_vars968;ALL;l4_lit_wf968] THEN
  CONJ_TAC THENL
  [ARITH_TAC;
   MATCH_MP_TAC l4_clause_wf_mono968 THEN
   EXISTS_TAC `l4_clause_num_vars968 t` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]);;

let l4_cnf_wf_mono968 = prove
 (`!phi n1 n2. n1 <= n2 /\ l4_cnf_wf968 n1 phi ==> l4_cnf_wf968 n2 phi`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_cnf_wf968;ALL;FORALL_SIMP] THEN
  REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC [l4_clause_wf_mono968];
   RULE_ASSUM_TAC (REWRITE_RULE [l4_cnf_wf968]) THEN ASM_MESON_TAC []]);;

let l4_cnf_num_vars_wf968 = prove
 (`!phi. l4_cnf_wf968 (l4_cnf_num_vars968 phi) phi`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_cnf_wf968;l4_cnf_num_vars968;ALL] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC l4_clause_wf_mono968 THEN
   EXISTS_TAC `l4_clause_num_vars968 h` THEN
   REWRITE_TAC [l4_clause_num_vars_wf968] THEN ARITH_TAC;
   REWRITE_TAC [GSYM l4_cnf_wf968] THEN
   MATCH_MP_TAC l4_cnf_wf_mono968 THEN
   EXISTS_TAC `l4_cnf_num_vars968 t` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]);;

let l4_level_equiv_iff_unsat_uncond968 = prove
 (`!phi.
   l4_vlevel_equiv961
     (l4_lvl_small968 (l4_cnf_num_vars968 phi))
     (l4_lvl_big968 (l4_cnf_num_vars968 phi) phi) <=>
   ~l4_cnf_sat968 phi`,
  GEN_TAC THEN MATCH_MP_TAC l4_level_equiv_iff_unsat968 THEN
  REWRITE_TAC [l4_cnf_num_vars_wf968]);;

(* ========================================================================= *)
(* 6. Linear Size Bounds & Worked Self-Contradiction Instance                *)
(* ========================================================================= *)

let l4_vlevel_size968 = new_recursive_definition l4_vlevel_RECURSION961
 `(l4_vlevel_size968 L4VLZero961 = 1) /\
  (l4_vlevel_size968 (L4VLParam961 i) = 1) /\
  (l4_vlevel_size968 (L4VLSucc961 l) = l4_vlevel_size968 l + 1) /\
  (l4_vlevel_size968 (L4VLMax961 a b) = l4_vlevel_size968 a + l4_vlevel_size968 b + 1) /\
  (l4_vlevel_size968 (L4VLIMax961 a b) = l4_vlevel_size968 a + l4_vlevel_size968 b + 1)`;;

let l4_list_sum968 = new_recursive_definition list_RECURSION
 `(l4_list_sum968 [] = 0) /\
  (l4_list_sum968 (CONS x xs) = x + l4_list_sum968 xs)`;;

let l4_cnf_size968 = new_definition
 `l4_cnf_size968 (phi:(l4_lit968 list) list) =
   l4_list_sum968 (MAP (\c. LENGTH c + 1) phi)`;;

let l4_size_two968 = prove
 (`l4_vlevel_size968 l4_lvl_two968 = 3`,
  REWRITE_TAC [l4_lvl_two968;l4_vlevel_size968] THEN ARITH_TAC);;

let l4_size_clause_lvl968 = prove
 (`!c. l4_vlevel_size968 (l4_clause_lvl968 c) = 2 * LENGTH c + 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_clause_lvl968;l4_vlevel_size968;LENGTH] THEN
  ASM_ARITH_TAC);;

let l4_size_foldl_imax968 = prove
 (`!gs b.
   l4_vlevel_size968 (l4_foldl_imax968 gs b) =
   l4_vlevel_size968 b + l4_list_sum968 (MAP (\g. l4_vlevel_size968 g + 1) gs)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC [l4_foldl_imax968;MAP;l4_list_sum968] THEN BETA_TAC THENL
  [ARITH_TAC;
   ASM_REWRITE_TAC [l4_vlevel_size968] THEN ARITH_TAC]);;

let l4_size_gates_sum968 = prove
 (`!phi.
   l4_list_sum968 (MAP (\g. l4_vlevel_size968 g + 1) (MAP l4_clause_lvl968 phi)) =
   2 * l4_cnf_size968 phi`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_cnf_size968;MAP;l4_list_sum968] THEN BETA_TAC THEN
  REWRITE_TAC [l4_size_clause_lvl968] THENL
  [ARITH_TAC;
   RULE_ASSUM_TAC (REWRITE_RULE [l4_cnf_size968]) THEN ASM_ARITH_TAC]);;

let l4_size_gates968 = prove
 (`!phi. l4_vlevel_size968 (l4_lvl_gates968 phi) = 2 * l4_cnf_size968 phi + 3`,
  GEN_TAC THEN
  REWRITE_TAC [l4_lvl_gates968;l4_size_foldl_imax968;l4_size_two968;l4_size_gates_sum968] THEN
  ARITH_TAC);;

let l4_size_var968 = prove
 (`!i. l4_vlevel_size968 (l4_lvl_var968 i) = 9`,
  GEN_TAC THEN REWRITE_TAC [l4_lvl_var968;l4_vlevel_size968;l4_size_two968] THEN
  ARITH_TAC);;

let l4_size_small968 = prove
 (`!n. l4_vlevel_size968 (l4_lvl_small968 n) = 10 * n + 1`,
  INDUCT_TAC THEN REWRITE_TAC [l4_lvl_small968;l4_vlevel_size968;l4_size_var968] THEN
  ASM_ARITH_TAC);;

let l4_size_big968 = prove
 (`!n phi.
   l4_vlevel_size968 (l4_lvl_big968 n phi) = 10 * n + 2 * l4_cnf_size968 phi + 5`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_lvl_big968;l4_vlevel_size968;l4_size_small968;l4_size_gates968] THEN
  ARITH_TAC);;

let l4_self_contradiction968 = new_definition
 `l4_self_contradiction968 = [[L4Lit968 0 T]; [L4Lit968 0 F]]`;;

let l4_self_contradiction_wf968 = prove
 (`l4_cnf_wf968 1 l4_self_contradiction968`,
  REWRITE_TAC [l4_self_contradiction968;l4_cnf_wf968;ALL;l4_lit_wf968;l4_lit_var968] THEN
  ARITH_TAC);;

let l4_not_sat_self_contradiction968 = prove
 (`~l4_cnf_sat968 l4_self_contradiction968`,
  REWRITE_TAC [l4_self_contradiction968;l4_cnf_sat968] THEN
  DISCH_THEN (X_CHOOSE_TAC `a:num->bool`) THEN
  FIRST_X_ASSUM (fun th ->
    MP_TAC (SPEC `[L4Lit968 0 T]` th) THEN
    MP_TAC (SPEC `[L4Lit968 0 F]` th)) THEN
  REWRITE_TAC [MEM;l4_clause_sat968] THEN
  DISCH_THEN (X_CHOOSE_THEN `l1:l4_lit968` (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  DISCH_THEN (fun h1 -> DISCH_THEN (fun e1 ->
    ASSUME_TAC (REWRITE_RULE [e1;l4_lit_var968;l4_lit_pol968] h1))) THEN
  DISCH_THEN (X_CHOOSE_THEN `l2:l4_lit968` (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  DISCH_THEN (fun h2 -> DISCH_THEN (fun e2 ->
    ASSUME_TAC (REWRITE_RULE [e2;l4_lit_var968;l4_lit_pol968] h2))) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_equiv_self_contradiction968 = prove
 (`l4_vlevel_equiv961
   (l4_lvl_small968 1)
   (l4_lvl_big968 1 l4_self_contradiction968)`,
  MP_TAC (SPECL [`1`;`l4_self_contradiction968`] l4_level_equiv_iff_unsat968) THEN
  SIMP_TAC [l4_self_contradiction_wf968;l4_not_sat_self_contradiction968]);;

let l4_single_pos_sat968 = prove
 (`l4_cnf_sat968 [[L4Lit968 0 T]]`,
  REWRITE_TAC [l4_cnf_sat968] THEN EXISTS_TAC `\i:num. T` THEN
  GEN_TAC THEN REWRITE_TAC [MEM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [l4_clause_sat968] THEN EXISTS_TAC `L4Lit968 0 T` THEN
  BETA_TAC THEN REWRITE_TAC [MEM;l4_lit_pol968]);;

let l4_not_equiv_single_pos968 = prove
 (`~l4_vlevel_equiv961 (l4_lvl_small968 1) (l4_lvl_big968 1 [[L4Lit968 0 T]])`,
  MP_TAC (SPECL [`1`;`[[L4Lit968 0 T]]`] l4_level_equiv_iff_unsat968) THEN
  ANTS_TAC THENL
  [REWRITE_TAC [l4_cnf_wf968;ALL;l4_lit_wf968;l4_lit_var968] THEN ARITH_TAC;
   SIMP_TAC [l4_single_pos_sat968]]);;
