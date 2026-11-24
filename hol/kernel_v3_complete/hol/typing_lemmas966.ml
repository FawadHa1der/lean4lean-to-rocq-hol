(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of Lean4Lean/Theory/VExpr.lean (de Bruijn lifting and
   instantiation commutation algebra) and Lean4Lean/Theory/Typing/Lemmas.lean
   (universe instantiation instL, closedness closedN, level well-formedness
   levelWF, context slice weakening weakN / weak0, VEnvWF invariants,
   const0 / extra0, cut / substitution instN / inst0, context conversion
   defeqDF_l / defeqDFC, Sort / Pi inversion, regularity isType, and
   congruence instDF) over declarative_typing961.ml.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/declarative_typing961.ml";;

(* ========================================================================= *)
(* 1. Universe Level Evaluation, Instantiation, WF & Composition             *)
(* ========================================================================= *)

let l4_vnth_nat_map_eval966 = prove
 (`!ks ls i.
   l4_vnth_nat961 (MAP (l4_vlevel_eval961 ls) ks) i =
   l4_vlevel_eval961 ls (l4_vnth_level961 ks i)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC [MAP;l4_vnth_nat961;l4_vnth_level961;l4_vlevel_eval961] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlevel_eval_inst966 = prove
 (`!u ks ls.
   l4_vlevel_eval961 ls (l4_vlevel_inst961 ks u) =
   l4_vlevel_eval961 (MAP (l4_vlevel_eval961 ls) ks) u`,
  MATCH_MP_TAC l4_vlevel_INDUCT961 THEN
  REWRITE_TAC [l4_vlevel_inst961;l4_vlevel_eval961;l4_vnth_nat_map_eval966] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlevel_inst_equiv966 = prove
 (`!ks u1 u2.
   l4_vlevel_equiv961 u1 u2 ==>
   l4_vlevel_equiv961 (l4_vlevel_inst961 ks u1) (l4_vlevel_inst961 ks u2)`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval_inst966] THEN MESON_TAC []);;

let l4_all2_vlevel_inst_equiv966 = prove
 (`!ls1 ls2 ks.
   ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
   ALL2 l4_vlevel_equiv961
     (MAP (l4_vlevel_inst961 ks) ls1)
     (MAP (l4_vlevel_inst961 ks) ls2)`,
  LIST_INDUCT_TAC THENL
  [GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ls2:l4_vlevel961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;MAP];
   GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ls2:l4_vlevel961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;MAP] THEN STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vlevel_inst_equiv966]]);;

let l4_vnth_level_wf966 = prove
 (`!ks uvars i.
   ALL (l4_vlevel_wf961 uvars) ks ==>
   l4_vlevel_wf961 uvars (l4_vnth_level961 ks i)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL;l4_vnth_level961;l4_vlevel_wf961] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC []);;

let l4_vlevel_inst_wf_any966 = prove
 (`!u ks uvars.
   ALL (l4_vlevel_wf961 uvars) ks ==>
   l4_vlevel_wf961 uvars (l4_vlevel_inst961 ks u)`,
  MATCH_MP_TAC l4_vlevel_INDUCT961 THEN
  REWRITE_TAC [l4_vlevel_inst961;l4_vlevel_wf961] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vnth_level_wf966]);;

let l4_all_vlevel_inst_wf966 = prove
 (`!ls ks uvars.
   ALL (l4_vlevel_wf961 uvars) ks ==>
   ALL (l4_vlevel_wf961 uvars) (MAP (l4_vlevel_inst961 ks) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;ALL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vlevel_inst_wf_any966]);;

let l4_vnth_level_map_inst966 = prove
 (`!ks2 ks1 i.
   l4_vnth_level961 (MAP (l4_vlevel_inst961 ks1) ks2) i =
   l4_vlevel_inst961 ks1 (l4_vnth_level961 ks2 i)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [MAP;l4_vnth_level961;l4_vlevel_inst961] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlevel_inst_inst966 = prove
 (`!u ks1 ks2.
   l4_vlevel_inst961 ks1 (l4_vlevel_inst961 ks2 u) =
   l4_vlevel_inst961 (MAP (l4_vlevel_inst961 ks1) ks2) u`,
  MATCH_MP_TAC l4_vlevel_INDUCT961 THEN
  REWRITE_TAC [l4_vlevel_inst961;l4_vnth_level_map_inst966] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_map_vlevel_inst_inst966 = prove
 (`!us ks1 ks2.
   MAP (l4_vlevel_inst961 ks1) (MAP (l4_vlevel_inst961 ks2) us) =
   MAP (l4_vlevel_inst961 (MAP (l4_vlevel_inst961 ks1) ks2)) us`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_vlevel_inst_inst966] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlevel_params_from966 = new_recursive_definition num_RECURSION
 `(l4_vlevel_params_from966 k 0 = []) /\
  (l4_vlevel_params_from966 k (SUC n) =
    CONS (L4VLParam961 k) (l4_vlevel_params_from966 (SUC k) n))`;;

let l4_vlevel_params966 = new_definition
 `l4_vlevel_params966 n = l4_vlevel_params_from966 0 n`;;

let l4_vlevel_params_from_length966 = prove
 (`!n k. LENGTH (l4_vlevel_params_from966 k n) = n`,
  INDUCT_TAC THEN REWRITE_TAC [l4_vlevel_params_from966;LENGTH] THEN
  ASM_REWRITE_TAC []);;

let l4_vlevel_params_length966 = prove
 (`!n. LENGTH (l4_vlevel_params966 n) = n`,
  REWRITE_TAC [l4_vlevel_params966;l4_vlevel_params_from_length966]);;

let l4_vlevel_params_from_wf966 = prove
 (`!n k uvars. k + n <= uvars ==>
   ALL (l4_vlevel_wf961 uvars) (l4_vlevel_params_from966 k n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlevel_params_from966;ALL;l4_vlevel_wf961] THEN
  DISCH_TAC THEN CONJ_TAC THENL
  [ASM_ARITH_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_vlevel_params_wf966 = prove
 (`!uvars. ALL (l4_vlevel_wf961 uvars) (l4_vlevel_params966 uvars)`,
  GEN_TAC THEN REWRITE_TAC [l4_vlevel_params966] THEN
  MATCH_MP_TAC l4_vlevel_params_from_wf966 THEN ARITH_TAC);;

let l4_vnth_params_from966 = prove
 (`!n k i. i < n ==>
   l4_vnth_level961 (l4_vlevel_params_from966 k n) i = L4VLParam961 (k + i)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [ARITH_TAC;
   REWRITE_TAC [l4_vlevel_params_from966;l4_vnth_level961] THEN
   DISCH_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [ADD_CLAUSES];
    SUBGOAL_THEN `i - 1 < n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC `SUC k` o MATCH_MP (ASSUME
      `!k i. i < n ==> l4_vnth_level961 (l4_vlevel_params_from966 k n) i =
        L4VLParam961 (k + i)`)) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

let l4_vlevel_inst_params966 = prove
 (`!u uvars.
   l4_vlevel_wf961 uvars u ==>
   l4_vlevel_inst961 (l4_vlevel_params966 uvars) u = u`,
  MATCH_MP_TAC l4_vlevel_INDUCT961 THEN
  REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_inst961;l4_vlevel_params966] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vnth_params_from966;ADD_CLAUSES]);;

let l4_map_vlevel_inst_params966 = prove
 (`!us uvars.
   ALL (l4_vlevel_wf961 uvars) us ==>
   MAP (l4_vlevel_inst961 (l4_vlevel_params966 uvars)) us = us`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [ALL;MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vlevel_inst_params966]);;

(* ========================================================================= *)
(* 2. De Bruijn Lifting, Substitution, Scope & Level-Substitution Algebra    *)
(* ========================================================================= *)

let l4_forall_t966 = prove (`(!x:A. T) <=> T`, MESON_TAC []);;

let l4_vliftN_vliftN966 = prove
 (`!e n m k1 k2.
   k1 <= k2 /\ k2 <= n + k1 ==>
   l4_vliftN961 (l4_vliftN961 e n k1) m k2 = l4_vliftN961 e (m + n) k1`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vlift_var961;injectivity "l4_vexpr961";l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_vliftN_comp966 = prove
 (`!e n m k.
   l4_vliftN961 (l4_vliftN961 e n k) m k = l4_vliftN961 e (m + n) k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC l4_vliftN_vliftN966 THEN ARITH_TAC);;

let l4_vliftN_comm966 = prove
 (`!e n1 n2 k1 k2.
   k2 <= k1 ==>
   l4_vliftN961 (l4_vliftN961 e n2 k2) n1 (n2 + k1) =
   l4_vliftN961 (l4_vliftN961 e n1 k1) n2 k2`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vlift_var961;injectivity "l4_vexpr961";l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `SUC (n2 + k1) = n2 + SUC k1` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let l4_vinst_vliftN_gen966 = prove
 (`!e v n k0 k.
   k0 <= k /\ k <= n + k0 ==>
   l4_vinst961 (l4_vliftN961 e (SUC n) k0) v k = l4_vliftN961 e n k0`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinst961;l4_vlift_var961;l4_vinst_var961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN
   CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN
   CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN
   CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_vinst0_vlift966 = prove
 (`!e v. l4_vinst0961 (l4_vlift961 e) v = e`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vinst0961;l4_vlift961;ONE] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`v:l4_vexpr961`;`0`;`0`;`0`] l4_vinst_vliftN_gen966) THEN
  REWRITE_TAC [LE_REFL;ADD_CLAUSES;l4_vliftN_zero961]);;

let l4_vliftN_vinst_hi966 = prove
 (`!e v n k j.
   j <= k ==>
   l4_vliftN961 (l4_vinst961 e v j) n k =
   l4_vinst961 (l4_vliftN961 e n (SUC k)) (l4_vliftN961 v n (k - j)) j`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinst961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [l4_vinst_var961;l4_vlift_var961] THEN
   ASM_CASES_TAC `a < j` THEN ASM_REWRITE_TAC [] THENL
   [SUBGOAL_THEN `a < SUC k` (fun th -> REWRITE_TAC [th;l4_vliftN961;l4_vlift_var961;l4_vinst_var961]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
    ASM_CASES_TAC `a:num = j` THEN ASM_REWRITE_TAC [] THENL
    [SUBGOAL_THEN `j < SUC k` (fun th -> REWRITE_TAC [th;l4_vinst961;l4_vinst_var961;LT_REFL]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
     MP_TAC (SPECL [`v:l4_vexpr961`;`n:num`;`j:num`;`k - j`;`0`] l4_vliftN_comm966) THEN
     SUBGOAL_THEN `j + (k - j) = k` (fun th -> SIMP_TAC [LE_0;th]) THEN ASM_ARITH_TAC;
     ASM_CASES_TAC `a < SUC k` THEN ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961;l4_vinst961;l4_vinst_var961] THEN
     REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `k - j = SUC k - SUC j` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `k - j = SUC k - SUC j` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let l4_vliftN_vinst0966 = prove
 (`!e v n k.
   l4_vliftN961 (l4_vinst0961 e v) n k =
   l4_vinst0961 (l4_vliftN961 e n (SUC k)) (l4_vliftN961 v n k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`v:l4_vexpr961`;`n:num`;`k:num`;`0`] l4_vliftN_vinst_hi966) THEN
  REWRITE_TAC [LE_0;SUB_0]);;

let l4_vliftN_vinst_lo966 = prove
 (`!e v n k j.
   k <= j ==>
   l4_vliftN961 (l4_vinst961 e v j) n k =
   l4_vinst961 (l4_vliftN961 e n k) v (n + j)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinst961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [l4_vinst_var961;l4_vlift_var961] THEN
   ASM_CASES_TAC `a < j` THEN ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961] THENL
   [ASM_CASES_TAC `a < k` THEN ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(a < k)` (fun th -> REWRITE_TAC [th;l4_vinst961;l4_vinst_var961]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `a:num = j` THEN ASM_REWRITE_TAC [LT_REFL] THENL
    [MATCH_MP_TAC l4_vliftN_vliftN966 THEN ASM_ARITH_TAC;
     REPEAT COND_CASES_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vlift_var961;injectivity "l4_vexpr961"] THEN
     REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `SUC (n + j) = n + SUC j` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `SUC (n + j) = n + SUC j` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let l4_vinst_vinst_hi966 = prove
 (`!e u v k j.
   l4_vinst961 (l4_vinst961 e u k) v (j + k) =
   l4_vinst961 (l4_vinst961 e v (SUC (j + k))) (l4_vinst961 u v j) k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinst961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_vinst_var961] THEN
   ASM_CASES_TAC `a < k` THEN ASM_REWRITE_TAC [] THENL
   [SUBGOAL_THEN `a < SUC (j + k) /\ a < j + k` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961]];
    ASM_CASES_TAC `a:num = k` THEN ASM_REWRITE_TAC [] THENL
    [SUBGOAL_THEN `k < SUC (j + k)` (fun th -> REWRITE_TAC [th;l4_vinst961;l4_vinst_var961;LT_REFL]) THENL
     [ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `j + k = k + j` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC (GSYM l4_vliftN_vinst_lo966) THEN ARITH_TAC;
     ASM_CASES_TAC `a < SUC (j + k)` THEN ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961] THENL
     [REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC;
      ASM_CASES_TAC `a = SUC (j + k)` THEN ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961] THENL
      [SUBGOAL_THEN `SUC (j + k) - 1 = j + k` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC [LT_REFL] THEN
       MATCH_MP_TAC (GSYM l4_vinst_vliftN_gen966) THEN ARITH_TAC;
       REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC]]]];
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [injectivity "l4_vexpr961"];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [];
    SUBGOAL_THEN `SUC (j + k) = j + SUC k` SUBST1_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC []]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [];
    SUBGOAL_THEN `SUC (j + k) = j + SUC k` SUBST1_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC []]]]);;

let l4_vinst0_vinst_hi966 = prove
 (`!e u v j.
   l4_vinst961 (l4_vinst0961 e u) v j =
   l4_vinst0961 (l4_vinst961 e v (SUC j)) (l4_vinst961 u v j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`u:l4_vexpr961`;`v:l4_vexpr961`;`0`;`j:num`] l4_vinst_vinst_hi966) THEN
  REWRITE_TAC [ADD_CLAUSES]);;

let l4_vinstL_vliftN966 = prove
 (`!e ks n k.
   l4_vinstL961 ks (l4_vliftN961 e n k) = l4_vliftN961 (l4_vinstL961 ks e) n k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinstL961] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vinstL_vlift966 = prove
 (`!ks e. l4_vinstL961 ks (l4_vlift961 e) = l4_vlift961 (l4_vinstL961 ks e)`,
  REWRITE_TAC [l4_vlift961;l4_vinstL_vliftN966]);;

let l4_vinstL_vinst966 = prove
 (`!e ks v k.
   l4_vinstL961 ks (l4_vinst961 e v k) =
   l4_vinst961 (l4_vinstL961 ks e) (l4_vinstL961 ks v) k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinst961;l4_vinstL961;l4_vinst_var961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
   REWRITE_TAC [l4_vinstL961;l4_vinstL_vliftN966];
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_vinstL_vinst0966 = prove
 (`!ks e v.
   l4_vinstL961 ks (l4_vinst0961 e v) =
   l4_vinst0961 (l4_vinstL961 ks e) (l4_vinstL961 ks v)`,
  REWRITE_TAC [l4_vinst0961;l4_vinstL_vinst966]);;

let l4_vinstL_vinstL966 = prove
 (`!e ks1 ks2.
   l4_vinstL961 ks1 (l4_vinstL961 ks2 e) =
   l4_vinstL961 (MAP (l4_vlevel_inst961 ks1) ks2) e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinstL961;l4_vlevel_inst_inst966;l4_map_vlevel_inst_inst966] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(* Closedness & levelWF preservation *)
let l4_vclosedN_mono966 = prove
 (`!e k1 k2. k1 <= k2 /\ l4_vclosedN961 e k1 ==> l4_vclosedN961 e k2`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vclosedN961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [ARITH_TAC;
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THENL
   [EXISTS_TAC `k1:num` THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `k1:num` THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `k1:num` THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `SUC k1` THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]]);;

let l4_vclosedN_vliftN_eq966 = prove
 (`!e n k. l4_vclosedN961 e k ==> l4_vliftN961 e n k = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vclosedN961;l4_vliftN961;l4_vlift_var961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC []]);;

let l4_vclosedN_vinst_eq966 = prove
 (`!e v k. l4_vclosedN961 e k ==> l4_vinst961 e v k = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vclosedN961;l4_vinst961;l4_vinst_var961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC []]);;

let l4_vliftN_preserves_vclosedN966 = prove
 (`!e n k d. k <= d /\ l4_vclosedN961 e d ==> l4_vclosedN961 (l4_vliftN961 e n k) (n + d)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vclosedN961;l4_vliftN961;l4_vlift_var961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC [l4_vclosedN961] THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [];
    SUBGOAL_THEN `SUC (n + d) = n + SUC d` SUBST1_TAC THENL
    [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]]]);;

let l4_vinst_preserves_vclosedN966 = prove
 (`!e v k d.
   k <= d /\ l4_vclosedN961 e (SUC d) /\ l4_vclosedN961 v (d - k) ==>
   l4_vclosedN961 (l4_vinst961 e v k) d`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vclosedN961;l4_vinst961;l4_vinst_var961;l4_forall_t966] THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   ASM_CASES_TAC `a < k` THEN ASM_REWRITE_TAC [l4_vclosedN961] THENL
   [ASM_ARITH_TAC;
    ASM_CASES_TAC `a:num = k` THEN ASM_REWRITE_TAC [l4_vclosedN961] THENL
    [SUBGOAL_THEN `d = k + (d - k)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC l4_vliftN_preserves_vclosedN966 THEN ASM_REWRITE_TAC [LE_0];
     ASM_ARITH_TAC]];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [SUB_SUC] THEN ASM_ARITH_TAC]]);;

let l4_vinst0_preserves_vclosedN966 = prove
 (`!e v d.
   l4_vclosedN961 e (SUC d) /\ l4_vclosedN961 v d ==>
   l4_vclosedN961 (l4_vinst0961 e v) d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  MATCH_MP_TAC l4_vinst_preserves_vclosedN966 THEN
  ASM_REWRITE_TAC [LE_0;SUB_0]);;

let l4_vinstL_preserves_vclosedN966 = prove
 (`!e ks k. l4_vclosedN961 (l4_vinstL961 ks e) k <=> l4_vclosedN961 e k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinstL961;l4_vclosedN961] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vexpr_level_wf966 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vexpr_level_wf966 uvars (L4VBVar961 i) <=> T) /\
  (l4_vexpr_level_wf966 uvars (L4VSort961 u) <=> l4_vlevel_wf961 uvars u) /\
  (l4_vexpr_level_wf966 uvars (L4VConst961 c us) <=> ALL (l4_vlevel_wf961 uvars) us) /\
  (l4_vexpr_level_wf966 uvars (L4VApp961 f a) <=>
    l4_vexpr_level_wf966 uvars f /\ l4_vexpr_level_wf966 uvars a) /\
  (l4_vexpr_level_wf966 uvars (L4VLam961 dom body) <=>
    l4_vexpr_level_wf966 uvars dom /\ l4_vexpr_level_wf966 uvars body) /\
  (l4_vexpr_level_wf966 uvars (L4VForallE961 dom cod) <=>
    l4_vexpr_level_wf966 uvars dom /\ l4_vexpr_level_wf966 uvars cod)`;;

let l4_vexpr_level_wf_vliftN966 = prove
 (`!e uvars n k. l4_vexpr_level_wf966 uvars (l4_vliftN961 e n k) <=> l4_vexpr_level_wf966 uvars e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vexpr_level_wf966] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vexpr_level_wf_vinst966 = prove
 (`!e uvars v k.
   l4_vexpr_level_wf966 uvars e /\ l4_vexpr_level_wf966 uvars v ==>
   l4_vexpr_level_wf966 uvars (l4_vinst961 e v k)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinst961;l4_vexpr_level_wf966;l4_vinst_var961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
   ASM_REWRITE_TAC [l4_vexpr_level_wf966;l4_vexpr_level_wf_vliftN966];
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC []]);;

let l4_vexpr_level_wf_vinstL_any966 = prove
 (`!e ks uvars.
   ALL (l4_vlevel_wf961 uvars) ks ==>
   l4_vexpr_level_wf966 uvars (l4_vinstL961 ks e)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinstL961;l4_vexpr_level_wf966] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_all_vlevel_inst_wf966]);;

let l4_vinstL_params966 = prove
 (`!e uvars.
   l4_vexpr_level_wf966 uvars e ==>
   l4_vinstL961 (l4_vlevel_params966 uvars) e = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vexpr_level_wf966;l4_vinstL961] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [l4_vlevel_inst_params966;l4_map_vlevel_inst_params966]);;

(* ========================================================================= *)
(* 3. Universe Instantiation of Judgments (IsDefEq.instL)                    *)
(* ========================================================================= *)

let l4_vlookup_instL966 = prove
 (`!g i ty.
   l4_vlookup961 g i ty ==>
   (!ks. l4_vlookup961 (MAP (l4_vinstL961 ks) g) i (l4_vinstL961 ks ty))`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC [MAP;l4_vinstL_vlift966] THENL
  [REWRITE_TAC [l4_vlookup_RULES961];
   STRIP_TAC THEN GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN
   ASM_REWRITE_TAC []]);;

let l4_vis_defeq_instL_ind966 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   (!uvars' ks.
      ALL (l4_vlevel_wf961 uvars') ks ==>
      l4_vis_defeq961 env uvars'
        (MAP (l4_vinstL961 ks) g)
        (l4_vinstL961 ks e1)
        (l4_vinstL961 ks e2)
        (l4_vinstL961 ks ty))`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_vis_defeq_bvar961 THEN ASM_SIMP_TAC [l4_vlookup_instL966];
   (* symm *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_SIMP_TAC [];
   (* trans *)
   MESON_TAC [l4_vis_defeq_trans961];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vlevel_inst961] THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vlevel_inst_equiv966];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinstL966] THEN
   MATCH_MP_TAC l4_vis_defeq_const961 THEN
   ASM_SIMP_TAC [LENGTH_MAP;l4_all_vlevel_inst_wf966;l4_all2_vlevel_inst_equiv966];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `l4_vinstL961 ks dom` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961]) THEN ASM_SIMP_TAC [];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN
   EXISTS_TAC `l4_vlevel_inst961 ks u` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961;MAP]) THEN ASM_SIMP_TAC [];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vlevel_inst961] THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961;MAP]) THEN ASM_SIMP_TAC [];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 ks ty1`;`l4_vlevel_inst961 ks u`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961]) THEN ASM_SIMP_TAC [];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_beta961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP]) THEN ASM_SIMP_TAC [];
   (* eta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vlift966] THEN
   MATCH_MP_TAC l4_vis_defeq_eta961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961]) THEN ASM_SIMP_TAC [];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_proof_irrel961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961;l4_vlevel_inst961]) THEN ASM_SIMP_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL_vinstL966] THEN
   MATCH_MP_TAC l4_vis_defeq_extra961 THEN
   ASM_SIMP_TAC [LENGTH_MAP;l4_all_vlevel_inst_wf966]]);;

let l4_vis_defeq_instL966 = prove
 (`!env uvars uvars' ks g e1 e2 ty.
   ALL (l4_vlevel_wf961 uvars') ks /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars'
     (MAP (l4_vinstL961 ks) g)
     (l4_vinstL961 ks e1)
     (l4_vinstL961 ks e2)
     (l4_vinstL961 ks ty)`,
  MESON_TAC [l4_vis_defeq_instL_ind966]);;

let l4_vhas_type_instL966 = prove
 (`!env uvars uvars' ks g e ty.
   ALL (l4_vlevel_wf961 uvars') ks /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vhas_type961 env uvars'
     (MAP (l4_vinstL961 ks) g)
     (l4_vinstL961 ks e)
     (l4_vinstL961 ks ty)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_instL966]);;

let l4_vis_type_instL966 = prove
 (`!env uvars uvars' ks g ty.
   ALL (l4_vlevel_wf961 uvars') ks /\
   l4_vis_type961 env uvars g ty ==>
   l4_vis_type961 env uvars' (MAP (l4_vinstL961 ks) g) (l4_vinstL961 ks ty)`,
  REWRITE_TAC [l4_vis_type961] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `l4_vlevel_inst961 ks u` THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`uvars':num`;`ks:l4_vlevel961 list`;
                 `g:l4_vexpr961 list`;`ty:l4_vexpr961`;`L4VSort961 u`] l4_vhas_type_instL966) THEN
  ASM_REWRITE_TAC [l4_vinstL961]);;

(* ========================================================================= *)
(* 4. Closedness, Level WF & Environment Well-Formedness                     *)
(* ========================================================================= *)

let l4_vctx_closed966 = new_recursive_definition list_RECURSION
 `(l4_vctx_closed966 [] <=> T) /\
  (l4_vctx_closed966 (CONS a g) <=> l4_vctx_closed966 g /\ l4_vclosedN961 a (LENGTH g))`;;

let l4_vlookup_length_lt966 = prove
 (`!g i ty. l4_vlookup961 g i ty ==> i < LENGTH g`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN REWRITE_TAC [LENGTH] THEN ARITH_TAC);;

let l4_vlookup_closed966 = prove
 (`!g i ty. l4_vlookup961 g i ty ==> l4_vctx_closed966 g ==> l4_vclosedN961 ty (LENGTH g)`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN REWRITE_TAC [l4_vctx_closed966;LENGTH;l4_vlift961] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUC (LENGTH (g:l4_vexpr961 list)) = 1 + LENGTH g` SUBST1_TAC THENL
  [ARITH_TAC;
   MATCH_MP_TAC l4_vliftN_preserves_vclosedN966 THEN ASM_REWRITE_TAC [LE_0];
   ARITH_TAC;
   MATCH_MP_TAC l4_vliftN_preserves_vclosedN966 THEN ASM_SIMP_TAC [LE_0]]);;

let l4_venv_closed966 = new_definition
 `l4_venv_closed966 env <=>
   (!c ci. l4_venv_lookup_const961 env c ci ==> l4_vclosedN961 (l4_vc_type961 ci) 0) /\
   (!df. l4_venv_has_defeq961 env df ==>
     l4_vclosedN961 (l4_vdf_lhs961 df) 0 /\
     l4_vclosedN961 (l4_vdf_rhs961 df) 0 /\
     l4_vclosedN961 (l4_vdf_type961 df) 0)`;;

let l4_closed_inst_const966 = prove
 (`!env c ci ls k.
   l4_venv_closed966 env /\ l4_venv_lookup_const961 env c ci ==>
   l4_vclosedN961 (l4_vinstL961 ls (l4_vc_type961 ci)) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_closed966;l4_vinstL_preserves_vclosedN966] THEN
  STRIP_TAC THEN MATCH_MP_TAC l4_vclosedN_mono966 THEN
  EXISTS_TAC `0` THEN ASM_MESON_TAC [LE_0]);;

let l4_closed_inst_defeq966 = prove
 (`!env df ls k.
   l4_venv_closed966 env /\ l4_venv_has_defeq961 env df ==>
   l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_lhs961 df)) k /\
   l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_rhs961 df)) k /\
   l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_type961 df)) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_closed966;l4_vinstL_preserves_vclosedN966] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `df:l4_vdefeq961`) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC l4_vclosedN_mono966 THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC [LE_0]);;

let l4_vis_defeq_closedN_ind966 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_venv_closed966 env /\ l4_vctx_closed966 g ==>
   l4_vclosedN961 e1 (LENGTH g) /\
   l4_vclosedN961 e2 (LENGTH g) /\
   l4_vclosedN961 ty (LENGTH g)`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vclosedN961] THEN
   ASM_MESON_TAC [l4_vlookup_length_lt966;l4_vlookup_closed966];
   MESON_TAC [];
   MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vclosedN961];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vclosedN961] THEN
   ASM_MESON_TAC [l4_closed_inst_const966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vclosedN961] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vclosedN961]) THEN
   ASM_MESON_TAC [l4_vinst0_preserves_vclosedN966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vclosedN961] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_closed966;LENGTH]) THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vclosedN961] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_closed966;LENGTH]) THEN ASM_MESON_TAC [];
   MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vclosedN961] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_closed966;LENGTH]) THEN
   ASM_MESON_TAC [l4_vinst0_preserves_vclosedN966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC [l4_vclosedN961] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vclosedN961;ARITH_RULE `0 < SUC n`;l4_vlift961] THEN
   SUBGOAL_THEN `SUC (LENGTH (g:l4_vexpr961 list)) = 1 + LENGTH g` SUBST1_TAC THENL
   [ARITH_TAC; MATCH_MP_TAC l4_vliftN_preserves_vclosedN966 THEN ASM_REWRITE_TAC [LE_0]];
   MESON_TAC [];
   MESON_TAC [l4_closed_inst_defeq966]]);;

let l4_vis_defeq_closedN966 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_closed966 env /\ l4_vctx_closed966 g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vclosedN961 e1 (LENGTH g) /\
   l4_vclosedN961 e2 (LENGTH g) /\
   l4_vclosedN961 ty (LENGTH g)`,
  MESON_TAC [l4_vis_defeq_closedN_ind966]);;

let l4_vctx_level_wf966 = new_recursive_definition list_RECURSION
 `(l4_vctx_level_wf966 uvars [] <=> T) /\
  (l4_vctx_level_wf966 uvars (CONS a g) <=>
    l4_vctx_level_wf966 uvars g /\ l4_vexpr_level_wf966 uvars a)`;;

let l4_vlookup_level_wf966 = prove
 (`!g i ty.
   l4_vlookup961 g i ty ==>
   (!uvars. l4_vctx_level_wf966 uvars g ==> l4_vexpr_level_wf966 uvars ty)`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN
  REWRITE_TAC [l4_vctx_level_wf966;l4_vlift961;l4_vexpr_level_wf_vliftN966] THEN
  MESON_TAC []);;

let l4_vis_defeq_level_wf966 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vctx_level_wf966 uvars g ==>
   l4_vexpr_level_wf966 uvars e1 /\
   l4_vexpr_level_wf966 uvars e2 /\
   l4_vexpr_level_wf966 uvars ty`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vexpr_level_wf966] THEN MESON_TAC [l4_vlookup_level_wf966];
   MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vlevel_wf961] THEN MESON_TAC [];
   REWRITE_TAC [l4_vexpr_level_wf966] THEN MESON_TAC [l4_vexpr_level_wf_vinstL_any966];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vinst0961] THEN MESON_TAC [l4_vexpr_level_wf_vinst966];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vctx_level_wf966] THEN MESON_TAC [];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vlevel_wf961;l4_vctx_level_wf966] THEN MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vctx_level_wf966;l4_vinst0961] THEN
   MESON_TAC [l4_vexpr_level_wf_vinst966];
   REWRITE_TAC [l4_vexpr_level_wf966;l4_vlift961;l4_vexpr_level_wf_vliftN966] THEN MESON_TAC [];
   MESON_TAC [];
   MESON_TAC [l4_vexpr_level_wf_vinstL_any966]]);;

(* ========================================================================= *)
(* 5. Context Slice Weakening (VCtxLiftN, IsDefEq.weakN, IsDefEq.weak0)      *)
(* ========================================================================= *)

let l4_vctx_liftN_RULES966,l4_vctx_liftN_INDUCT966,l4_vctx_liftN_CASES966 =
  new_inductive_definition
 `(!n g prefix. LENGTH prefix = n ==> l4_vctx_liftN966 n 0 g (APPEND prefix g)) /\
  (!n k g g' a. l4_vctx_liftN966 n k g g' ==>
    l4_vctx_liftN966 n (SUC k) (CONS a g) (CONS (l4_vliftN961 a n k) g'))`;;

let [l4_vctx_liftN_zero966; l4_vctx_liftN_succ966] = CONJUNCTS l4_vctx_liftN_RULES966;;

let l4_vlookup_append_prefix966 = prove
 (`!prefix g i ty.
   l4_vlookup961 g i ty ==>
   l4_vlookup961 (APPEND prefix g) (LENGTH prefix + i) (l4_vliftN961 ty (LENGTH prefix) 0)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [APPEND;LENGTH;ADD_CLAUSES] THENL
  [REWRITE_TAC [l4_vliftN_zero961];
   DISCH_TAC THEN
   SUBGOAL_THEN `l4_vliftN961 ty (SUC (LENGTH (t:l4_vexpr961 list))) 0 =
                 l4_vlift961 (l4_vliftN961 ty (LENGTH t) 0)` SUBST1_TAC THENL
   [REWRITE_TAC [l4_vlift961;l4_vliftN_comp966;ARITH_RULE `1 + n = SUC n`];
    MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_SIMP_TAC []]]);;

let l4_subst_vars_tac966 =
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o
    check (fun th -> is_eq (concl th) && is_var (lhs (concl th)))));;

let l4_vliftN_vlift966 = prove
 (`!e n k. l4_vliftN961 (l4_vlift961 e) n (SUC k) = l4_vlift961 (l4_vliftN961 e n k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift961] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`n:num`;`1`;`k:num`;`0`] l4_vliftN_comm966) THEN
  REWRITE_TAC [LE_0;ARITH_RULE `1 + k = SUC k`]);;

let l4_vlift_var_succ966 = prove
 (`!n i k. l4_vlift_var961 n (SUC i) (SUC k) = SUC (l4_vlift_var961 n i k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift_var961;LT_SUC;ADD_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC []);;

let l4_vctx_liftN_lookup966 = prove
 (`!n k g g'.
   l4_vctx_liftN966 n k g g' ==>
   (!i ty. l4_vlookup961 g i ty ==>
     l4_vlookup961 g' (l4_vlift_var961 n i k) (l4_vliftN961 ty n k))`,
  MATCH_MP_TAC l4_vctx_liftN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_var961;LT] THEN
   MATCH_MP_TAC l4_vlookup_append_prefix966 THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THENL
   [REWRITE_TAC [l4_vlift_var961;ARITH_RULE `0 < SUC k`;l4_vliftN_vlift966;l4_vlookup_RULES961];
    REWRITE_TAC [l4_vlift_var_succ966;l4_vliftN_vlift966] THEN
    MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_SIMP_TAC []]]);;

let l4_vlookup_weakN966 = prove
 (`!g i ty n k g'.
   l4_vlookup961 g i ty /\ l4_vctx_liftN966 n k g g' ==>
   l4_vlookup961 g' (l4_vlift_var961 n i k) (l4_vliftN961 ty n k)`,
  MESON_TAC [l4_vctx_liftN_lookup966]);;

let l4_vis_defeq_weakN_ind966 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   (!n k g'.
      l4_venv_closed966 env /\ l4_vctx_liftN966 n k g g' ==>
      l4_vis_defeq961 env uvars g'
        (l4_vliftN961 e1 n k)
        (l4_vliftN961 e2 n k)
        (l4_vliftN961 ty n k))`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_bvar961 THEN ASM_MESON_TAC [l4_vlookup_weakN966];
   (* symm *)
   MESON_TAC [l4_vis_defeq_symm961];
   (* trans *)
   MESON_TAC [l4_vis_defeq_trans961];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   SUBGOAL_THEN `l4_vliftN961 (l4_vinstL961 ls1 (l4_vc_type961 cinfo)) n k =
                 l4_vinstL961 ls1 (l4_vc_type961 cinfo)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_vclosedN_vliftN_eq966 THEN ASM_MESON_TAC [l4_closed_inst_const966];
    MATCH_MP_TAC l4_vis_defeq_const961 THEN ASM_REWRITE_TAC []];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `l4_vliftN961 dom n k` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_SIMP_TAC [];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
   ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
   ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 ty1 n k`;`u:l4_vlevel961`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_SIMP_TAC [];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_beta961 THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   (* eta *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961;ARITH_RULE `0 < SUC k`] THEN
   SUBGOAL_THEN `l4_vliftN961 (l4_vlift961 e) n (SUC k) = l4_vlift961 (l4_vliftN961 e n k)`
     SUBST1_TAC THENL
   [REWRITE_TAC [l4_vlift961] THEN
    MP_TAC (SPECL [`e:l4_vexpr961`;`n:num`;`1`;`k:num`;`0`] l4_vliftN_comm966) THEN
    REWRITE_TAC [LE_0;ARITH_RULE `1 + k = SUC k`];
    MATCH_MP_TAC l4_vis_defeq_eta961 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_SIMP_TAC []];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_proof_irrel961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_SIMP_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`;`k:num`]
     l4_closed_inst_defeq966) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966;l4_vis_defeq_extra961]]);;

let l4_vis_defeq_weakN966 = prove
 (`!env uvars g e1 e2 ty n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g'
     (l4_vliftN961 e1 n k)
     (l4_vliftN961 e2 n k)
     (l4_vliftN961 ty n k)`,
  MESON_TAC [l4_vis_defeq_weakN_ind966]);;

let l4_vctx_liftN_one966 = prove
 (`!a g. l4_vctx_liftN966 1 0 g (CONS a g)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `CONS (a:l4_vexpr961) g = APPEND [a] g` SUBST1_TAC THENL
  [REWRITE_TAC [APPEND];
   MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REWRITE_TAC [LENGTH;ONE]]);;

let l4_vis_defeq_weak966 = prove
 (`!env uvars g b e1 e2 ty.
   l4_venv_closed966 env /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars (CONS b g)
     (l4_vlift961 e1) (l4_vlift961 e2) (l4_vlift961 ty)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift961] THEN
  MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
  EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vctx_liftN_one966]);;

let l4_vis_type_weakN966 = prove
 (`!env uvars g ty n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_type961 env uvars g ty ==>
   l4_vis_type961 env uvars g' (l4_vliftN961 ty n k)`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `u:l4_vlevel961` THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `ty:l4_vexpr961`;`ty:l4_vexpr961`;`L4VSort961 u`;
                 `n:num`;`k:num`;`g':l4_vexpr961 list`] l4_vis_defeq_weakN966) THEN
  ASM_REWRITE_TAC [l4_vliftN961]);;

let l4_vis_defeq_weak0966 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_closed966 env /\
   l4_vis_defeq961 env uvars [] e1 e2 ty ==>
   l4_vis_defeq961 env uvars g e1 e2 ty`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
    l4_vis_defeq_closedN966) THEN
  ASM_REWRITE_TAC [l4_vctx_closed966;LENGTH] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`;
                 `LENGTH (g:l4_vexpr961 list)`;`0`;`APPEND (g:l4_vexpr961 list) []`]
    l4_vis_defeq_weakN966) THEN
  ASM_SIMP_TAC [l4_vctx_liftN_zero966;APPEND_NIL;l4_vclosedN_vliftN_eq966]);;

(* ========================================================================= *)
(* 6. Substitution / Cut Rule (VCtxInstN, IsDefEq.instN, IsDefEq.inst0)      *)
(* ========================================================================= *)

let l4_vctx_instN_RULES966,l4_vctx_instN_INDUCT966,l4_vctx_instN_CASES966 =
  new_inductive_definition
 `(!g0 e0 a0. l4_vctx_instN966 g0 e0 a0 0 (CONS a0 g0) g0) /\
  (!g0 e0 a0 k g1 g a. l4_vctx_instN966 g0 e0 a0 k g1 g ==>
    l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS a g1) (CONS (l4_vinst961 a e0 k) g))`;;

let [l4_vctx_instN_zero966; l4_vctx_instN_succ966] = CONJUNCTS l4_vctx_instN_RULES966;;

let l4_vinst_vlift_succ966 = prove
 (`!e v k. l4_vinst961 (l4_vlift961 e) v (SUC k) = l4_vlift961 (l4_vinst961 e v k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift961] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`v:l4_vexpr961`;`1`;`0`;`k:num`] l4_vliftN_vinst_lo966) THEN
  REWRITE_TAC [LE_0;ARITH_RULE `1 + k = SUC k`] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let l4_vinst_var_succ966 = prove
 (`!j v k. l4_vinst_var961 (SUC j) v (SUC k) = l4_vlift961 (l4_vinst_var961 j v k)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`L4VBVar961 j`;`v:l4_vexpr961`;`1`;`0`;`k:num`] l4_vliftN_vinst_lo966) THEN
  REWRITE_TAC [LE_0;l4_vinst961;l4_vliftN961;l4_vlift_var961;LT;ARITH_RULE `1 + x = SUC x`;l4_vlift961] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let l4_vctx_instN_lookup966 = prove
 (`!g0 e0 a0 k g1 g.
   l4_vctx_instN966 g0 e0 a0 k g1 g ==>
   (!env uvars i ty.
      l4_venv_closed966 env /\
      l4_vhas_type961 env uvars g0 e0 a0 /\
      l4_vlookup961 g1 i ty ==>
      l4_vhas_type961 env uvars g (l4_vinst_var961 i e0 k) (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THENL
   [l4_subst_vars_tac966 THEN
    ASM_REWRITE_TAC [l4_vinst_var961;LT_REFL;l4_vliftN_zero961;GSYM l4_vinst0961;l4_vinst0_vlift966];
    l4_subst_vars_tac966 THEN
    ASM_REWRITE_TAC [l4_vinst_var961;LT;distinctness "num";SUC_SUB1;
                     GSYM l4_vinst0961;l4_vinst0_vlift966;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN ASM_REWRITE_TAC []];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THENL
   [l4_subst_vars_tac966 THEN
    ASM_REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;l4_vinst_vlift_succ966;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961];
    l4_subst_vars_tac966 THEN
    ASM_REWRITE_TAC [l4_vinst_var_succ966;l4_vinst_vlift_succ966;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    ASM_MESON_TAC []]]);;

let l4_vis_defeq_instN_ind966 = prove
 (`!env uvars g1 e1 e2 ty.
   l4_vis_defeq961 env uvars g1 e1 e2 ty ==>
   (!g0 e0 a0 k g.
      l4_venv_closed966 env /\
      l4_vhas_type961 env uvars g0 e0 a0 /\
      l4_vctx_instN966 g0 e0 a0 k g1 g ==>
      l4_vis_defeq961 env uvars g
        (l4_vinst961 e1 e0 k)
        (l4_vinst961 e2 e0 k)
        (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;GSYM l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vctx_instN_lookup966];
   (* symm *)
   MESON_TAC [l4_vis_defeq_symm961];
   (* trans *)
   MESON_TAC [l4_vis_defeq_trans961];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_vinst961 (l4_vinstL961 ls1 (l4_vc_type961 cinfo)) e0 k =
                 l4_vinstL961 ls1 (l4_vc_type961 cinfo)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_vclosedN_vinst_eq966 THEN ASM_MESON_TAC [l4_closed_inst_const966];
    MATCH_MP_TAC l4_vis_defeq_const961 THEN ASM_REWRITE_TAC []];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `l4_vinst961 dom e0 k` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN
   ASM_MESON_TAC [l4_vctx_instN_succ966];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN
   ASM_MESON_TAC [l4_vctx_instN_succ966];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 ty1 e0 k`;`u:l4_vlevel961`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   MATCH_MP_TAC l4_vis_defeq_beta961 THEN ASM_MESON_TAC [l4_vctx_instN_succ966];
   (* eta *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vinst961;l4_vinst_var961;ARITH_RULE `0 < SUC k`;l4_vinst_vlift_succ966] THEN
   MATCH_MP_TAC l4_vis_defeq_eta961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_proof_irrel961 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`;`k:num`]
     l4_closed_inst_defeq966) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vclosedN_vinst_eq966;l4_vis_defeq_extra961]]);;

let l4_vis_defeq_instN966 = prove
 (`!env uvars g0 e0 a0 g1 e1 e2 ty k g.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_defeq961 env uvars g1 e1 e2 ty ==>
   l4_vis_defeq961 env uvars g
     (l4_vinst961 e1 e0 k)
     (l4_vinst961 e2 e0 k)
     (l4_vinst961 ty e0 k)`,
  MESON_TAC [l4_vis_defeq_instN_ind966]);;

let l4_vis_type_instN966 = prove
 (`!env uvars g0 e0 a0 g1 ty k g.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_type961 env uvars g1 ty ==>
   l4_vis_type961 env uvars g (l4_vinst961 ty e0 k)`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `u:l4_vlevel961` THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                 `e0:l4_vexpr961`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`;
                 `ty:l4_vexpr961`;`ty:l4_vexpr961`;`L4VSort961 u`;
                 `k:num`;`g:l4_vexpr961 list`] l4_vis_defeq_instN966) THEN
  ASM_REWRITE_TAC [l4_vinst961;l4_vhas_type961]);;

let l4_vis_defeq_inst0966 = prove
 (`!env uvars g a e1 e2 b v.
   l4_venv_closed966 env /\
   l4_vis_defeq961 env uvars (CONS a g) e1 e2 b /\
   l4_vhas_type961 env uvars g v a ==>
   l4_vis_defeq961 env uvars g
     (l4_vinst0961 e1 v) (l4_vinst0961 e2 v) (l4_vinst0961 b v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  MATCH_MP_TAC l4_vis_defeq_instN966 THEN
  MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`a:l4_vexpr961`;`CONS (a:l4_vexpr961) g`] THEN
  ASM_REWRITE_TAC [l4_vctx_instN_zero966]);;

(* ========================================================================= *)
(* 7. Context Conversion (defeqDF_l', IsDefEqCtx, defeqDFC)                  *)
(* ========================================================================= *)

let l4_vinst_vliftN_bvar0966 = prove
 (`!e k. l4_vinst961 (l4_vliftN961 e 1 (SUC k)) (L4VBVar961 0) k = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinst961;l4_forall_t966] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift_var961] THEN
   ASM_CASES_TAC `a < SUC k` THEN ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961] THENL
   [ASM_CASES_TAC `a < k` THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `a:num = k` THEN ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961;LT;ADD_CLAUSES] THEN
    ASM_ARITH_TAC;
    REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC];
   REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_defeqDF_l_ctx_pair966 = prove
 (`!d g a a'.
   ?g'. l4_vctx_liftN966 1 (SUC (LENGTH d)) (APPEND d (CONS a g)) g' /\
        l4_vctx_instN966 (CONS a' g) (L4VBVar961 0) (l4_vlift961 a) (LENGTH d) g'
          (APPEND d (CONS a' g))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [APPEND;LENGTH] THENL
  [EXISTS_TAC `CONS (l4_vlift961 a) (CONS a' g)` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vlift961] THEN MATCH_MP_TAC l4_vctx_liftN_succ966 THEN
    REWRITE_TAC [l4_vctx_liftN_one966];
    REWRITE_TAC [l4_vctx_instN_zero966]];
   FIRST_X_ASSUM (X_CHOOSE_THEN `g':l4_vexpr961 list` STRIP_ASSUME_TAC o
     SPECL [`g:l4_vexpr961 list`;`a:l4_vexpr961`;`a':l4_vexpr961`]) THEN
   EXISTS_TAC `CONS (l4_vliftN961 h 1 (SUC (LENGTH (t:l4_vexpr961 list)))) g'` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vctx_liftN_succ966 THEN ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`CONS (a':l4_vexpr961) g`;`L4VBVar961 0`;`l4_vlift961 a`;
                   `LENGTH (t:l4_vexpr961 list)`;`g':l4_vexpr961 list`;
                   `APPEND t (CONS (a':l4_vexpr961) g)`;
                   `l4_vliftN961 h 1 (SUC (LENGTH (t:l4_vexpr961 list)))`]
      l4_vctx_instN_succ966) THEN
    ASM_REWRITE_TAC [l4_vinst_vliftN_bvar0966]]]);;

let l4_vis_defeq_defeqDF_l'966 = prove
 (`!env uvars g a a' u d e1 e2 b.
   l4_venv_closed966 env /\
   l4_vis_defeq961 env uvars g a a' (L4VSort961 u) /\
   l4_vis_defeq961 env uvars (APPEND d (CONS a g)) e1 e2 b ==>
   l4_vis_defeq961 env uvars (APPEND d (CONS a' g)) e1 e2 b`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `g':l4_vexpr961 list` STRIP_ASSUME_TAC
    (SPECL [`d:l4_vexpr961 list`;`g:l4_vexpr961 list`;`a:l4_vexpr961`;`a':l4_vexpr961`]
      l4_defeqDF_l_ctx_pair966) THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS a' g) (L4VBVar961 0) (l4_vlift961 a)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift961 a'`;`u:l4_vlevel961`] THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`a':l4_vexpr961`;
                   `a':l4_vexpr961`;`a:l4_vexpr961`;`L4VSort961 u`] l4_vis_defeq_weak966) THEN
    ASM_SIMP_TAC [l4_vlift961;l4_vliftN961;l4_vis_defeq_symm961] THEN
    MESON_TAC [l4_vis_defeq_weak966;l4_vis_defeq_symm961;l4_vlift961;l4_vliftN961];
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961]];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`APPEND d (CONS (a:l4_vexpr961) g)`;
                  `e1:l4_vexpr961`;`e2:l4_vexpr961`;`b:l4_vexpr961`;
                  `1`;`SUC (LENGTH (d:l4_vexpr961 list))`;`g':l4_vexpr961 list`]
     l4_vis_defeq_weakN966) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (a':l4_vexpr961) g`;
                  `L4VBVar961 0`;`l4_vlift961 a`;`g':l4_vexpr961 list`;
                  `l4_vliftN961 e1 1 (SUC (LENGTH (d:l4_vexpr961 list)))`;
                  `l4_vliftN961 e2 1 (SUC (LENGTH (d:l4_vexpr961 list)))`;
                  `l4_vliftN961 b 1 (SUC (LENGTH (d:l4_vexpr961 list)))`;
                  `LENGTH (d:l4_vexpr961 list)`;`APPEND d (CONS (a':l4_vexpr961) g)`]
     l4_vis_defeq_instN966) THEN
   ASM_REWRITE_TAC [l4_vinst_vliftN_bvar0966]]);;

let l4_vis_defeq_defeqDF_l966 = prove
 (`!env uvars g a a' u e1 e2 b.
   l4_venv_closed966 env /\
   l4_vis_defeq961 env uvars g a a' (L4VSort961 u) /\
   l4_vis_defeq961 env uvars (CONS a g) e1 e2 b ==>
   l4_vis_defeq961 env uvars (CONS a' g) e1 e2 b`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `a:l4_vexpr961`;`a':l4_vexpr961`;`u:l4_vlevel961`;
                 `[]:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;`b:l4_vexpr961`]
    l4_vis_defeq_defeqDF_l'966) THEN
  ASM_REWRITE_TAC [APPEND]);;

let l4_vis_defeq_ctx_RULES966,l4_vis_defeq_ctx_INDUCT966,l4_vis_defeq_ctx_CASES966 =
  new_inductive_definition
 `(!env uvars g0. l4_vis_defeq_ctx966 env uvars g0 g0 g0) /\
  (!env uvars g0 g1 g2 ty1 ty2 u.
     l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
     l4_vis_defeq961 env uvars g1 ty1 ty2 (L4VSort961 u) ==>
     l4_vis_defeq_ctx966 env uvars g0 (CONS ty1 g1) (CONS ty2 g2))`;;

let [l4_vis_defeq_ctx_zero966; l4_vis_defeq_ctx_succ966] =
  CONJUNCTS l4_vis_defeq_ctx_RULES966;;

let l4_vis_defeq_ctx_STRONG_INDUCT966 =
  derive_strong_induction (l4_vis_defeq_ctx_RULES966, l4_vis_defeq_ctx_INDUCT966);;

let l4_vis_defeq_defeqDFC'966 = prove
 (`!env uvars g0 g1 g2.
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
   (!d e1 e2 b.
      l4_venv_closed966 env /\
      l4_vis_defeq961 env uvars (APPEND d g1) e1 e2 b ==>
      l4_vis_defeq961 env uvars (APPEND d g2) e1 e2 b)`,
  MATCH_MP_TAC l4_vis_defeq_ctx_INDUCT966 THEN CONJ_TAC THENL
  [SIMP_TAC [];
   MAP_EVERY X_GEN_TAC
     [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
      `g1:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
      `ty1:l4_vexpr961`;`ty2:l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`d:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;`b:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `ty1:l4_vexpr961`;`ty2:l4_vexpr961`;`u:l4_vlevel961`;
                  `d:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;`b:l4_vexpr961`]
     l4_vis_defeq_defeqDF_l'966) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN `APPEND d (CONS (ty2:l4_vexpr961) g2) = APPEND (APPEND d [ty2]) g2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM APPEND_ASSOC;APPEND]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [GSYM APPEND_ASSOC;APPEND]]);;

let l4_vis_defeq_defeqDFC966 = prove
 (`!env uvars g0 g1 g2 e1 e2 b.
   l4_venv_closed966 env /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vis_defeq961 env uvars g1 e1 e2 b ==>
   l4_vis_defeq961 env uvars g2 e1 e2 b`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                 `g1:l4_vexpr961 list`;`g2:l4_vexpr961 list`]
    l4_vis_defeq_defeqDFC'966) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`[]:l4_vexpr961 list`;`e1:l4_vexpr961`;
                              `e2:l4_vexpr961`;`b:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [APPEND]);;

let l4_vis_type_defeqDFC966 = prove
 (`!env uvars g0 g1 g2 b.
   l4_venv_closed966 env /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vis_type961 env uvars g1 b ==>
   l4_vis_type961 env uvars g2 b`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_defeqDFC966]);;

let l4_vis_defeq_ctx_symm966 = prove
 (`!env uvars g0 g1 g2.
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
   l4_venv_closed966 env ==>
   l4_vis_defeq_ctx966 env uvars g0 g2 g1`,
  MATCH_MP_TAC l4_vis_defeq_ctx_STRONG_INDUCT966 THEN CONJ_TAC THENL
  [SIMP_TAC [l4_vis_defeq_ctx_zero966];
   MAP_EVERY X_GEN_TAC
     [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
      `g1:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
      `ty1:l4_vexpr961`;`ty2:l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_MESON_TAC [l4_vis_defeq_symm961]]]);;

(* ========================================================================= *)
(* 8. Well-Formed Environments, Sort/Pi Inversion & Regularity (isType)      *)
(* ========================================================================= *)

let l4_vconstant_wf966 = new_definition
 `l4_vconstant_wf966 env ci <=>
   l4_vis_type961 env (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) /\
   l4_vclosedN961 (l4_vc_type961 ci) 0`;;

let l4_vdefeq_wf966 = new_definition
 `l4_vdefeq_wf966 env df <=>
   l4_vhas_type961 env (l4_vdf_uvars961 df) [] (l4_vdf_lhs961 df) (l4_vdf_type961 df) /\
   l4_vhas_type961 env (l4_vdf_uvars961 df) [] (l4_vdf_rhs961 df) (l4_vdf_type961 df) /\
   l4_vclosedN961 (l4_vdf_lhs961 df) 0 /\
   l4_vclosedN961 (l4_vdf_rhs961 df) 0 /\
   l4_vclosedN961 (l4_vdf_type961 df) 0`;;

let l4_venv_empty961 = new_definition
 `l4_venv_empty961 = L4VEnv961 [] []`;;

let l4_venv_wf_RULES966,l4_venv_wf_INDUCT966,l4_venv_wf_CASES966 =
  new_inductive_definition
 `(l4_venv_wf966 (L4VEnv961 [] [])) /\
  (!cs dfs n ci.
     l4_venv_wf966 (L4VEnv961 cs dfs) /\
     ~(?ci0. l4_venv_lookup_const961 (L4VEnv961 cs dfs) n ci0) /\
     l4_vconstant_wf966 (L4VEnv961 cs dfs) ci ==>
     l4_venv_wf966 (L4VEnv961 (CONS (n,ci) cs) dfs)) /\
  (!cs dfs df.
     l4_venv_wf966 (L4VEnv961 cs dfs) /\
     l4_vdefeq_wf966 (L4VEnv961 cs dfs) df ==>
     l4_venv_wf966 (L4VEnv961 cs (CONS df dfs)))`;;

let [l4_venv_wf_empty966; l4_venv_wf_const966; l4_venv_wf_defeq966] =
  CONJUNCTS l4_venv_wf_RULES966;;

let l4_venv_empty_wf966 = prove
 (`l4_venv_wf966 l4_venv_empty961`,
  REWRITE_TAC [l4_venv_empty961;l4_venv_wf_empty966]);;

let l4_venv_wf_lookup_unique_ind966 = prove
 (`!env. l4_venv_wf966 env ==>
   (!n c1 c2.
      l4_venv_lookup_const961 env n c1 /\
      l4_venv_lookup_const961 env n c2 ==>
      c1 = c2)`,
  MATCH_MP_TAC l4_venv_wf_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;PAIR_EQ] THEN
   MESON_TAC [];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961] THEN
   MESON_TAC []]);;

let l4_venv_wf_lookup_unique966 = prove
 (`!env n c1 c2.
   l4_venv_wf966 env /\
   l4_venv_lookup_const961 env n c1 /\
   l4_venv_lookup_const961 env n c2 ==>
   c1 = c2`,
  MESON_TAC [l4_venv_wf_lookup_unique_ind966]);;

let l4_venv_cons_const_ordered966 = prove
 (`!cs dfs n ci.
   l4_venv_ordered961 (L4VEnv961 cs dfs) (L4VEnv961 (CONS (n,ci) cs) dfs)`,
  REWRITE_TAC [l4_venv_ordered961;l4_venv_lookup_const961;l4_venv_has_defeq961;
               l4_venv_consts_list961;l4_venv_defeqs_list961;MEM] THEN
  MESON_TAC []);;

let l4_venv_cons_defeq_ordered966 = prove
 (`!cs dfs df.
   l4_venv_ordered961 (L4VEnv961 cs dfs) (L4VEnv961 cs (CONS df dfs))`,
  REWRITE_TAC [l4_venv_ordered961;l4_venv_lookup_const961;l4_venv_has_defeq961;
               l4_venv_consts_list961;l4_venv_defeqs_list961;MEM] THEN
  MESON_TAC []);;

let l4_venv_ordered_preserve_vis_type966 = prove
 (`!env1 env2 uvars g ty.
   l4_venv_ordered961 env1 env2 /\ l4_vis_type961 env1 uvars g ty ==>
   l4_vis_type961 env2 uvars g ty`,
  REWRITE_TAC [l4_vis_type961] THEN MESON_TAC [l4_venv_ordered_preserve_vhas_type961]);;

let l4_venv_wf_closed966 = prove
 (`!env. l4_venv_wf966 env ==> l4_venv_closed966 env`,
  MATCH_MP_TAC l4_venv_wf_INDUCT966 THEN
  REWRITE_TAC [l4_venv_closed966;l4_venv_lookup_const961;l4_venv_has_defeq961;
               l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;
               l4_vconstant_wf966;l4_vdefeq_wf966;PAIR_EQ] THEN
  MESON_TAC []);;

let l4_venv_wf_const_wf966 = prove
 (`!env. l4_venv_wf966 env ==>
   (!c ci. l4_venv_lookup_const961 env c ci ==> l4_vconstant_wf966 env ci)`,
  MATCH_MP_TAC l4_venv_wf_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;PAIR_EQ] THEN
   STRIP_TAC THENL
   [l4_subst_vars_tac966 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vconstant_wf966]) THEN
    REWRITE_TAC [l4_vconstant_wf966] THEN
    ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_ordered_preserve_vis_type966];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vconstant_wf966;l4_venv_lookup_const961;l4_venv_consts_list961]) THEN
    REWRITE_TAC [l4_vconstant_wf966] THEN
    ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_ordered_preserve_vis_type966]];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vconstant_wf966;l4_venv_lookup_const961;l4_venv_consts_list961]) THEN
   REWRITE_TAC [l4_vconstant_wf966] THEN
   ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vis_type966]]);;

let l4_venv_wf_defeq_wf966 = prove
 (`!env. l4_venv_wf966 env ==>
   (!df. l4_venv_has_defeq961 env df ==> l4_vdefeq_wf966 env df)`,
  MATCH_MP_TAC l4_venv_wf_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
   REWRITE_TAC [l4_vdefeq_wf966] THEN
   ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_ordered_preserve_vhas_type961];
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM] THEN STRIP_TAC THENL
   [l4_subst_vars_tac966 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966]) THEN
    REWRITE_TAC [l4_vdefeq_wf966] THEN
    ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vhas_type961];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
    REWRITE_TAC [l4_vdefeq_wf966] THEN
    ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vhas_type961]]]);;

let l4_vhas_type_const0966 = prove
 (`!env c ci.
   l4_venv_wf966 env /\ l4_venv_lookup_const961 env c ci ==>
   l4_vhas_type961 env (l4_vc_uvars961 ci) []
     (L4VConst961 c (l4_vlevel_params966 (l4_vc_uvars961 ci)))
     (l4_vc_type961 ci)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c:l4_name`;`ci:l4_vconstant961`]
    (MATCH_MP l4_venv_wf_const_wf966 (ASSUME `l4_venv_wf966 env`))) THEN
  ASM_REWRITE_TAC [l4_vconstant_wf966;l4_vis_type961;l4_vhas_type961] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`l4_vc_uvars961 ci`;`[]:l4_vexpr961 list`;
                 `l4_vc_type961 ci`;`l4_vc_type961 ci`;`L4VSort961 u`]
    l4_vis_defeq_level_wf966) THEN
  ASM_REWRITE_TAC [l4_vctx_level_wf966] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vc_type961 ci =
                l4_vinstL961 (l4_vlevel_params966 (l4_vc_uvars961 ci)) (l4_vc_type961 ci)`
    SUBST1_TAC THENL
  [ASM_SIMP_TAC [l4_vinstL_params966];
   MATCH_MP_TAC l4_vis_defeq_const961 THEN
   ASM_REWRITE_TAC [l4_vlevel_params_wf966;l4_vlevel_params_length966] THEN
   SUBGOAL_THEN `!ls:l4_vlevel961 list. ALL2 l4_vlevel_equiv961 ls ls`
     (fun th -> REWRITE_TAC [th]) THEN
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]]);;

let l4_vis_defeq_extra0966 = prove
 (`!env df.
   l4_venv_wf966 env /\ l4_venv_has_defeq961 env df ==>
   l4_vis_defeq961 env (l4_vdf_uvars961 df) []
     (l4_vdf_lhs961 df) (l4_vdf_rhs961 df) (l4_vdf_type961 df)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `df:l4_vdefeq961`
    (MATCH_MP l4_venv_wf_defeq_wf966 (ASSUME `l4_venv_wf966 env`))) THEN
  ASM_REWRITE_TAC [l4_vdefeq_wf966;l4_vhas_type961] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`[]:l4_vexpr961 list`;
                 `l4_vdf_lhs961 df`;`l4_vdf_lhs961 df`;`l4_vdf_type961 df`]
    l4_vis_defeq_level_wf966) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`[]:l4_vexpr961 list`;
                 `l4_vdf_rhs961 df`;`l4_vdf_rhs961 df`;`l4_vdf_type961 df`]
    l4_vis_defeq_level_wf966) THEN
  ASM_REWRITE_TAC [l4_vctx_level_wf966] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`[]:l4_vexpr961 list`;
                 `df:l4_vdefeq961`;`l4_vlevel_params966 (l4_vdf_uvars961 df)`]
    l4_vis_defeq_extra961) THEN
  ASM_SIMP_TAC [l4_vlevel_params_wf966;l4_vlevel_params_length966;l4_vinstL_params966]);;

(* Well-formed contexts & lookup *)
let l4_vctx_wf966 = new_recursive_definition list_RECURSION
 `(l4_vctx_wf966 env uvars [] <=> T) /\
  (l4_vctx_wf966 env uvars (CONS a g) <=>
    l4_vctx_wf966 env uvars g /\ l4_vis_type961 env uvars g a)`;;

let l4_vis_type_lookup966 = prove
 (`!g i ty.
   l4_vlookup961 g i ty ==>
   (!env uvars.
      l4_venv_closed966 env /\ l4_vctx_wf966 env uvars g ==>
      l4_vis_type961 env uvars g ty)`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN
  REWRITE_TAC [l4_vctx_wf966;l4_vlift961] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_type_weakN966 THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vctx_liftN_one966];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_type_weakN966 THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_vctx_liftN_one966]]);;

(* Sort & Pi inversion *)
let l4_vinst0_eq_sort966 = prove
 (`!e a u.
   l4_vinst0961 e a = L4VSort961 u ==>
   e = L4VSort961 u \/ (e = L4VBVar961 0 /\ a = L4VSort961 u)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REWRITE_TAC [l4_vinst0961;l4_vinst961;l4_vinst_var961;LT;distinctness "l4_vexpr961"] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_vliftN_zero961;distinctness "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vinst0_eq_forall966 = prove
 (`!e a dom cod.
   l4_vinst0961 e a = L4VForallE961 dom cod ==>
   (e = L4VBVar961 0 /\ a = L4VForallE961 dom cod) \/
   (?dom0 cod0. e = L4VForallE961 dom0 cod0 /\
                dom = l4_vinst961 dom0 a 0 /\
                cod = l4_vinst961 cod0 a 1)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REWRITE_TAC [l4_vinst0961;l4_vinst961;l4_vinst_var961;LT;
               distinctness "l4_vexpr961";injectivity "l4_vexpr961";ONE] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_vliftN_zero961;distinctness "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vinstL_eq_sort966 = prove
 (`!ls e u.
   l4_vinstL961 ls e = L4VSort961 u ==>
   ?u0. e = L4VSort961 u0 /\ u = l4_vlevel_inst961 ls u0`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REWRITE_TAC [l4_vinstL961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vis_defeq_sort_inv'966 = prove
 (`!env uvars g e1 e2 v.
   l4_vis_defeq961 env uvars g e1 e2 v ==>
   (!u. (e1 = L4VSort961 u \/ e2 = L4VSort961 u) ==> l4_vlevel_wf961 uvars u)`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [injectivity "l4_vexpr961"] THEN MESON_TAC [];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   MESON_TAC [];
   REWRITE_TAC [distinctness "l4_vexpr961"] THEN MESON_TAC [l4_vinst0_eq_sort966];
   REWRITE_TAC [distinctness "l4_vexpr961"] THEN MESON_TAC [];
   MESON_TAC [];
   MESON_TAC [l4_vinstL_eq_sort966;l4_vlevel_inst_wf_any966]]);;

let l4_vis_type_sort_inv966 = prove
 (`!env uvars g u.
   l4_vis_type961 env uvars g (L4VSort961 u) ==> l4_vlevel_wf961 uvars u`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_sort_inv'966]);;

let l4_vdefeqs_forall_inv966 = new_definition
 `l4_vdefeqs_forall_inv966 env <=>
   !df dom cod.
     l4_venv_has_defeq961 env df /\
     (l4_vdf_lhs961 df = L4VForallE961 dom cod \/
      l4_vdf_rhs961 df = L4VForallE961 dom cod) ==>
     l4_vis_type961 env (l4_vdf_uvars961 df) [] dom /\
     l4_vis_type961 env (l4_vdf_uvars961 df) [dom] cod`;;

let l4_forall_inv_instL966 = prove
 (`!env uvars uvars0 g ls e dom cod.
   l4_venv_closed966 env /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   l4_vinstL961 ls e = L4VForallE961 dom cod /\
   (!dom0 cod0. e = L4VForallE961 dom0 cod0 ==>
     l4_vis_type961 env uvars0 [] dom0 /\
     l4_vis_type961 env uvars0 [dom0] cod0) ==>
   l4_vis_type961 env uvars g dom /\
   l4_vis_type961 env uvars (CONS dom g) cod`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REWRITE_TAC [l4_vinstL961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`a0:l4_vexpr961`;`a1:l4_vexpr961`]) THEN
  REWRITE_TAC [] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars0:num`;`uvars:num`;`ls:l4_vlevel961 list`;
                 `[]:l4_vexpr961 list`;`a0:l4_vexpr961`] l4_vis_type_instL966) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars0:num`;`uvars:num`;`ls:l4_vlevel961 list`;
                 `[a0:l4_vexpr961]`;`a1:l4_vexpr961`] l4_vis_type_instL966) THEN
  ASM_REWRITE_TAC [MAP;l4_vis_type961;l4_vhas_type961] THEN
  DISCH_THEN (X_CHOOSE_TAC `v:l4_vlevel961`) THEN
  DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961`) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `dom:l4_vexpr961`;`dom:l4_vexpr961`;`L4VSort961 u`] l4_vis_defeq_closedN966) THEN
  ASM_REWRITE_TAC [l4_vctx_closed966;LENGTH] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[dom:l4_vexpr961]`;
                 `cod:l4_vexpr961`;`cod:l4_vexpr961`;`L4VSort961 v`] l4_vis_defeq_closedN966) THEN
  ASM_REWRITE_TAC [l4_vctx_closed966;LENGTH;ONE] THEN STRIP_TAC THEN CONJ_TAC THENL
  [EXISTS_TAC `u:l4_vlevel961` THEN MATCH_MP_TAC l4_vis_defeq_weak0966 THEN ASM_REWRITE_TAC [];
   EXISTS_TAC `v:l4_vlevel961` THEN
   SUBGOAL_THEN `l4_vctx_liftN966 (LENGTH (g:l4_vexpr961 list)) (SUC 0) [dom] (CONS dom g)`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `CONS (dom:l4_vexpr961) g =
                  CONS (l4_vliftN961 dom (LENGTH g) 0) (APPEND g [])` SUBST1_TAC THENL
    [ASM_SIMP_TAC [APPEND_NIL;l4_vclosedN_vliftN_eq966];
     MATCH_MP_TAC l4_vctx_liftN_succ966 THEN
     MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REWRITE_TAC []];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[dom:l4_vexpr961]`;
                   `cod:l4_vexpr961`;`cod:l4_vexpr961`;`L4VSort961 v`;
                   `LENGTH (g:l4_vexpr961 list)`;`SUC 0`;
                   `CONS (dom:l4_vexpr961) g`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966;l4_vliftN961]]]);;

let l4_vis_defeq_STRONG_INDUCT966 =
  derive_strong_induction (l4_vis_defeq_RULES961, l4_vis_defeq_INDUCT961);;

let l4_venv_wf_STRONG_INDUCT966 =
  derive_strong_induction (l4_venv_wf_RULES966, l4_venv_wf_INDUCT966);;

let l4_vis_defeq_forall_inv_ind966 = prove
 (`!env uvars g e1 e2 v.
   l4_vis_defeq961 env uvars g e1 e2 v ==>
   (!dom cod.
      l4_venv_closed966 env /\ l4_vdefeqs_forall_inv966 env /\
      (e1 = L4VForallE961 dom cod \/ e2 = L4VForallE961 dom cod) ==>
      l4_vis_type961 env uvars g dom /\
      l4_vis_type961 env uvars (CONS dom g) cod)`,
  MATCH_MP_TAC l4_vis_defeq_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [injectivity "l4_vexpr961"] THEN STRIP_TAC THENL
   [l4_subst_vars_tac966 THEN
    REWRITE_TAC [l4_vis_type961] THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961];
    l4_subst_vars_tac966 THEN
    REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961];
     EXISTS_TAC `v:l4_vlevel961` THEN
     MATCH_MP_TAC l4_vis_defeq_defeqDF_l966 THEN
     MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961]]];
   (* conv *)
   MESON_TAC [];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`dom_q:l4_vexpr961`;`cod_q:l4_vexpr961`] THEN
   REWRITE_TAC [distinctness "l4_vexpr961"] THEN STRIP_TAC THEN
   MP_TAC (SPECL [`body:l4_vexpr961`;`arg:l4_vexpr961`;`dom_q:l4_vexpr961`;`cod_q:l4_vexpr961`]
     l4_vinst0_eq_forall966) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
   [ASM_MESON_TAC [];
    SUBGOAL_THEN `l4_vis_type961 env uvars (CONS dom g) dom0 /\
                  l4_vis_type961 env uvars (CONS dom0 (CONS dom g)) cod0` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [];
     ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vis_type_instN966 THENL
     [MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
      ASM_REWRITE_TAC [l4_vhas_type961;l4_vctx_instN_zero966];
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                            `CONS (dom0:l4_vexpr961) (CONS dom g)`] THEN
      ASM_REWRITE_TAC [l4_vhas_type961;ONE] THEN
      MATCH_MP_TAC l4_vctx_instN_succ966 THEN REWRITE_TAC [l4_vctx_instN_zero966]]]];
   (* eta *)
   REWRITE_TAC [distinctness "l4_vexpr961"] THEN MESON_TAC [];
   (* proofIrrel *)
   MESON_TAC [];
   (* extra *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC l4_forall_inv_instL966 THEN
    MAP_EVERY EXISTS_TAC [`l4_vdf_uvars961 df`;`ls:l4_vlevel961 list`;`l4_vdf_lhs961 df`] THEN
    ASM_REWRITE_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeqs_forall_inv966]) THEN
    ASM_MESON_TAC [];
    MATCH_MP_TAC l4_forall_inv_instL966 THEN
    MAP_EVERY EXISTS_TAC [`l4_vdf_uvars961 df`;`ls:l4_vlevel961 list`;`l4_vdf_rhs961 df`] THEN
    ASM_REWRITE_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeqs_forall_inv966]) THEN
    ASM_MESON_TAC []]]);;

let l4_venv_wf_forall_inv966 = prove
 (`!env. l4_venv_wf966 env ==> l4_vdefeqs_forall_inv966 env`,
  MATCH_MP_TAC l4_venv_wf_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vdefeqs_forall_inv966;l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vdefeqs_forall_inv966] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeqs_forall_inv966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
   ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_ordered_preserve_vis_type966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC (SPEC `L4VEnv961 cs dfs` l4_venv_wf_closed966) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   REWRITE_TAC [l4_vdefeqs_forall_inv966] THEN
   MAP_EVERY X_GEN_TAC [`df_q:l4_vdefeq961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM] THEN
   DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
   [l4_subst_vars_tac966 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966;l4_vhas_type961]) THEN
    SUBGOAL_THEN `l4_vis_type961 (L4VEnv961 cs dfs) (l4_vdf_uvars961 df) [] dom /\
                  l4_vis_type961 (L4VEnv961 cs dfs) (l4_vdf_uvars961 df) [dom] cod`
      MP_TAC THENL
    [ASM_MESON_TAC [l4_vis_defeq_forall_inv_ind966];
     MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vis_type966]];
    SUBGOAL_THEN `l4_vis_type961 (L4VEnv961 cs dfs) (l4_vdf_uvars961 df_q) [] dom /\
                  l4_vis_type961 (L4VEnv961 cs dfs) (l4_vdf_uvars961 df_q) [dom] cod`
      MP_TAC THENL
    [RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeqs_forall_inv966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
     ASM_MESON_TAC [];
     MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vis_type966]]]]);;

let l4_vis_type_forall_inv966 = prove
 (`!env uvars g dom cod.
   l4_venv_wf966 env /\
   l4_vis_type961 env uvars g (L4VForallE961 dom cod) ==>
   l4_vis_type961 env uvars g dom /\
   l4_vis_type961 env uvars (CONS dom g) cod`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `u:l4_vlevel961` o REWRITE_RULE [l4_vis_type961;l4_vhas_type961])) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `L4VForallE961 dom cod`;`L4VForallE961 dom cod`;`L4VSort961 u`]
    l4_vis_defeq_forall_inv_ind966) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [];
   DISCH_THEN (MP_TAC o SPECL [`dom:l4_vexpr961`;`cod:l4_vexpr961`]) THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;l4_venv_wf_forall_inv966]]);;

(* Regularity: IsDefEq.isType *)
let l4_venv_types_wf966 = new_definition
 `l4_venv_types_wf966 env <=>
   (!c ci. l4_venv_lookup_const961 env c ci ==>
      l4_vis_type961 env (l4_vc_uvars961 ci) [] (l4_vc_type961 ci)) /\
   (!df. l4_venv_has_defeq961 env df ==>
      l4_vis_type961 env (l4_vdf_uvars961 df) [] (l4_vdf_type961 df))`;;

let l4_vis_defeq_is_type_ind966 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_venv_closed966 env /\
   l4_vdefeqs_forall_inv966 env /\
   l4_venv_types_wf966 env /\
   l4_vctx_wf966 env uvars g ==>
   l4_vis_type961 env uvars g ty`,
  MATCH_MP_TAC l4_vis_defeq_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MESON_TAC [l4_vis_type_lookup966];
   (* symm *)
   MESON_TAC [];
   (* trans *)
   MESON_TAC [];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   EXISTS_TAC `L4VLSucc961 (L4VLSucc961 l1)` THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   (* const *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_venv_types_wf966 env` THEN REWRITE_TAC [l4_venv_types_wf966] THEN
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`c:l4_name`;`cinfo:l4_vconstant961`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`l4_vc_uvars961 cinfo`;`uvars:num`;`ls1:l4_vlevel961 list`;
                  `[]:l4_vexpr961 list`;`l4_vc_type961 cinfo`] l4_vis_type_instL966) THEN
   ASM_REWRITE_TAC [MAP;l4_vis_type961;l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_weak0966];
   (* app *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars g (L4VForallE961 dom cod)` MP_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_TAC `w:l4_vlevel961` o REWRITE_RULE [l4_vis_type961;l4_vhas_type961]) THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars (CONS dom g) cod` MP_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_forall_inv_ind966]; ALL_TAC] THEN
   DISCH_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
   MATCH_MP_TAC l4_vis_type_instN966 THEN
   MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
   ASM_MESON_TAC [l4_vctx_instN_zero966;l4_vis_defeq_refl_l961];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars g dom1` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars (CONS dom1 g) cod` MP_TAC THENL
   [ASM_SIMP_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   DISCH_THEN (X_CHOOSE_TAC `v:l4_vlevel961`) THEN
   EXISTS_TAC `L4VLIMax961 u v` THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN
   ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars g (L4VSort961 u)` MP_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   DISCH_THEN (ASSUME_TAC o MATCH_MP l4_vis_type_sort_inv966) THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars g dom1` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars (CONS dom1 g) (L4VSort961 v)` MP_TAC THENL
   [ASM_SIMP_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   DISCH_THEN (ASSUME_TAC o MATCH_MP l4_vis_type_sort_inv966) THEN
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   EXISTS_TAC `L4VLSucc961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   (* conv *)
   REWRITE_TAC [l4_vis_type961] THEN MESON_TAC [l4_vis_defeq_refl_r961];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars g dom` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 env uvars (CONS dom g) cod` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vis_type_instN966 THEN
   MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
   ASM_REWRITE_TAC [l4_vhas_type961;l4_vctx_instN_zero966];
   (* eta *)
   MESON_TAC [];
   (* proofIrrel *)
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN MESON_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_venv_types_wf966 env` THEN REWRITE_TAC [l4_venv_types_wf966] THEN
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `df:l4_vdefeq961`) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`uvars:num`;`ls:l4_vlevel961 list`;
                  `[]:l4_vexpr961 list`;`l4_vdf_type961 df`] l4_vis_type_instL966) THEN
   ASM_REWRITE_TAC [MAP;l4_vis_type961;l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_weak0966]]);;

let l4_venv_wf_types966 = prove
 (`!env. l4_venv_wf966 env ==> l4_venv_types_wf966 env`,
  MATCH_MP_TAC l4_venv_wf_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_venv_types_wf966;l4_venv_lookup_const961;l4_venv_has_defeq961;
                l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 (L4VEnv961 (CONS (n,ci) cs) dfs)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_wf_const966]; ALL_TAC] THEN
   REWRITE_TAC [l4_venv_types_wf966] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_venv_wf_const_wf966;l4_vconstant_wf966];
    GEN_TAC THEN REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_types_wf966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
    ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_ordered_preserve_vis_type966]];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 (L4VEnv961 cs (CONS df dfs))` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_defeq966]; ALL_TAC] THEN
   REWRITE_TAC [l4_venv_types_wf966] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_venv_wf_const_wf966;l4_vconstant_wf966];
    GEN_TAC THEN REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM] THEN
    STRIP_TAC THENL
    [l4_subst_vars_tac966 THEN
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966;l4_vhas_type961]) THEN
     SUBGOAL_THEN `l4_vis_type961 (L4VEnv961 cs dfs) (l4_vdf_uvars961 df) [] (l4_vdf_type961 df)`
       MP_TAC THENL
     [MP_TAC (SPECL [`L4VEnv961 cs dfs`;`l4_vdf_uvars961 df`;`[]:l4_vexpr961 list`;
                     `l4_vdf_lhs961 df`;`l4_vdf_lhs961 df`;`l4_vdf_type961 df`]
        l4_vis_defeq_is_type_ind966) THEN
      ASM_SIMP_TAC [l4_venv_wf_closed966;l4_venv_wf_forall_inv966;l4_vctx_wf966];
      ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vis_type966]];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_types_wf966;l4_venv_has_defeq961;l4_venv_defeqs_list961]) THEN
     ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_ordered_preserve_vis_type966]]]]);;

let l4_vis_defeq_is_type966 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_type961 env uvars g ty`,
  MESON_TAC [l4_vis_defeq_is_type_ind966;l4_venv_wf_closed966;
             l4_venv_wf_forall_inv966;l4_venv_wf_types966]);;

let l4_vis_defeq_sort_r966 = prove
 (`!env uvars g e1 e2 u.
   l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 (L4VSort961 u) ==>
   l4_vlevel_wf961 uvars u`,
  MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type_sort_inv966]);;

(* Congruence of single substitution: IsDefEq.instDF *)
let l4_vis_defeq_instDF_aux966 = prove
 (`!env uvars g a f f' b x x' v.
   l4_vis_defeq961 env uvars g a a (L4VSort961 v) /\
   l4_vis_defeq961 env uvars (CONS a g) f f' b /\
   l4_vis_defeq961 env uvars g x x' a /\
   (?w. l4_vis_defeq961 env uvars g (l4_vinst0961 b x) (l4_vinst0961 b x') (L4VSort961 w)) ==>
   l4_vis_defeq961 env uvars g (l4_vinst0961 f x) (l4_vinst0961 f' x') (l4_vinst0961 b x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g
    (l4_vinst0961 f x) (L4VApp961 (L4VLam961 a f) x) (l4_vinst0961 b x)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_beta961 THEN
   ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g
    (L4VApp961 (L4VLam961 a f) x) (L4VApp961 (L4VLam961 a f') x') (l4_vinst0961 b x)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `a:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
   EXISTS_TAC `v:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g
    (L4VApp961 (L4VLam961 a f') x') (l4_vinst0961 f' x') (l4_vinst0961 b x)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst0961 b x'`;`w:l4_vlevel961`] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_symm961];
    MATCH_MP_TAC l4_vis_defeq_beta961 THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961]]; ALL_TAC] THEN
  ASM_MESON_TAC [l4_vis_defeq_trans961]);;

let l4_vis_defeq_instDF966 = prove
 (`!env uvars g a f f' b x x'.
   l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars (CONS a g) f f' b /\
   l4_vis_defeq961 env uvars g x x' a ==>
   l4_vis_defeq961 env uvars g (l4_vinst0961 f x) (l4_vinst0961 f' x') (l4_vinst0961 b x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_type961 env uvars g a` MP_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type966]; ALL_TAC] THEN
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961`) THEN
  SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS a g)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC [l4_vctx_wf966;l4_vis_type961;l4_vhas_type961] THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_type961 env uvars (CONS a g) b` MP_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type966]; ALL_TAC] THEN
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  DISCH_THEN (X_CHOOSE_TAC `w:l4_vlevel961`) THEN
  SUBGOAL_THEN `l4_vlevel_wf961 uvars w` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_sort_r966]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g (l4_vinst0961 b x) (l4_vinst0961 b x') (L4VSort961 w)`
    ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`a:l4_vexpr961`;
                  `b:l4_vexpr961`;`b:l4_vexpr961`;`L4VSort961 w`;`x:l4_vexpr961`;
                  `x':l4_vexpr961`;`u:l4_vlevel961`] l4_vis_defeq_instDF_aux966) THEN
   ASM_REWRITE_TAC [l4_vinst0961;l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `L4VLSucc961 w` THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   MATCH_MP_TAC l4_vis_defeq_instDF_aux966 THEN
   MAP_EVERY EXISTS_TAC [`a:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_MESON_TAC []]);;
