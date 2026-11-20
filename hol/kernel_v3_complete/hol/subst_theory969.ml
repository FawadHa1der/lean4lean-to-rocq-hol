(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of remaining Lean4Lean/Theory/VExpr.lean and
   Lean4Lean/Theory/Typing/Lemmas.lean substitution & renaming theory:
   1. Unlifting, skipping predicates, liftN injectivity, and liftN/instL
      commutation inversions (of_liftN_eq_liftN, of_liftN_eq_instL).
   2. Structured renamings l4_vlift_op969, l4_vlift_prime969, l4_vctx_lift_prime969,
      equivalence with l4_vliftN961 / l4_vctx_liftN966, lookup inversion, and
      structured-renaming weakening for declarative typing.
   3. Simultaneous substitutions (:num -> l4_vexpr961): identity, head/tail/cons,
      lifting, left/right lift composition, substitution composition, closedness
      invariance, and interaction with l4_vinst961 / l4_vinst0961 / l4_vinstL961.
   4. Pointwise substitution typing & definitional equality l4_vctx_subst_eq969
      with left, lookup, skip, lift, lift_at, wf, and id theorems.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/typing_lemmas966.ml";;

let l4_subst_vars_tac969 =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if is_eq c && lhs c <> rhs c then
      if is_var (lhs c) && not (vfree_in (lhs c) (rhs c)) then
        SUBST_ALL_TAC th
      else if is_var (rhs c) && not (vfree_in (rhs c) (lhs c)) then
        SUBST_ALL_TAC (SYM th)
      else failwith "l4_subst_vars_tac969"
    else failwith "l4_subst_vars_tac969"));;

(* ========================================================================= *)
(* 1. Unlifting, Skipping, and Lift Injectivity (VExpr.lean:360-481)         *)
(* ========================================================================= *)

let l4_vexpr_default969 = new_definition
 `l4_vexpr_default969 = L4VSort961 L4VLZero961`;;

let l4_vliftN_default969 = prove
 (`!n k. l4_vliftN961 l4_vexpr_default969 n k = l4_vexpr_default969`,
  REWRITE_TAC [l4_vexpr_default969;l4_vliftN961]);;

let l4_vinst_default969 = prove
 (`!v k. l4_vinst961 l4_vexpr_default969 v k = l4_vexpr_default969`,
  REWRITE_TAC [l4_vexpr_default969;l4_vinst961]);;

let l4_vinstL_default969 = prove
 (`!ls. l4_vinstL961 ls l4_vexpr_default969 = l4_vexpr_default969`,
  REWRITE_TAC [l4_vexpr_default969;l4_vinstL961;l4_vlevel_inst961]);;

let l4_vclosedN_default969 = prove
 (`!k. l4_vclosedN961 l4_vexpr_default969 k`,
  REWRITE_TAC [l4_vexpr_default969;l4_vclosedN961]);;

let l4_vunliftN969 = new_recursive_definition num_RECURSION
 `(l4_vunliftN969 e 0 k = e) /\
  (l4_vunliftN969 e (SUC n) k =
    l4_vunliftN969 (l4_vinst961 e l4_vexpr_default969 k) n k)`;;

let l4_vinst_vliftN_same969 = prove
 (`!e v n k. l4_vinst961 (l4_vliftN961 e (SUC n) k) v k = l4_vliftN961 e n k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC l4_vinst_vliftN_gen966 THEN ARITH_TAC);;

let l4_vunliftN_vliftN969 = prove
 (`!n e k. l4_vunliftN969 (l4_vliftN961 e n k) n k = e`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vunliftN969;l4_vliftN_zero961];
   ASM_REWRITE_TAC [l4_vunliftN969;l4_vinst_vliftN_same969]]);;

let l4_vliftN_inj969 = prove
 (`!e1 e2 n k. l4_vliftN961 e1 n k = l4_vliftN961 e2 n k <=> e1 = e2`,
  MESON_TAC [l4_vunliftN_vliftN969]);;

let l4_vlift_var_inj969 = prove
 (`!n i1 i2 k. l4_vlift_var961 n i1 k = l4_vlift_var961 n i2 k <=> i1 = i2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`L4VBVar961 i1`;`L4VBVar961 i2`;`n:num`;`k:num`] l4_vliftN_inj969) THEN
  REWRITE_TAC [l4_vliftN961;injectivity "l4_vexpr961"]);;

let l4_vliftN_vunliftN_hi969 = prove
 (`!n2 e n1 k1 k2.
   k2 <= k1 ==>
   l4_vliftN961 (l4_vunliftN969 e n2 k2) n1 k1 =
   l4_vunliftN969 (l4_vliftN961 e n1 (k1 + n2)) n2 k2`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vunliftN969;ADD_CLAUSES];
   DISCH_TAC THEN REWRITE_TAC [l4_vunliftN969] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`l4_vinst961 e l4_vexpr_default969 k2`;
                                  `n1:num`;`k1:num`;`k2:num`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`e:l4_vexpr961`;`l4_vexpr_default969`;`n1:num`;
                  `k1 + n2`;`k2:num`] l4_vliftN_vinst_hi966) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC [l4_vliftN_default969;ARITH_RULE `SUC (k1 + n2) = k1 + SUC n2`]]);;

let l4_vskips969 = new_definition
 `l4_vskips969 e n k <=> l4_vliftN961 (l4_vunliftN969 e n k) n k = e`;;

let l4_vskips_vliftN969 = prove
 (`!e n k. l4_vskips969 (l4_vliftN961 e n k) n k`,
  REWRITE_TAC [l4_vskips969;l4_vunliftN_vliftN969]);;

let l4_vskips_iff_exists969 = prove
 (`!e n k. l4_vskips969 e n k <=> ?e'. e = l4_vliftN961 e' n k`,
  MESON_TAC [l4_vskips969;l4_vskips_vliftN969]);;

let l4_vskips_of_vliftN_hi969 = prove
 (`!e n1 k1 n2 k2.
   n2 + k2 <= k1 /\ l4_vskips969 (l4_vliftN961 e n1 k1) n2 k2 ==>
   l4_vskips969 e n2 k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vskips969] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM (SPECL [`l4_vliftN961 (l4_vunliftN969 e n2 k2) n2 k2`;
                                  `e:l4_vexpr961`;`n1:num`;`k1:num`] l4_vliftN_inj969)] THEN
  SUBGOAL_THEN `k1 = n2 + ((k1 - (n2 + k2)) + k2)` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`l4_vunliftN969 e n2 k2`;`n1:num`;`n2:num`;
                 `(k1 - (n2 + k2)) + k2`;`k2:num`] l4_vliftN_comm966) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC (SPECL [`n2:num`;`e:l4_vexpr961`;`n1:num`;
                 `(k1 - (n2 + k2)) + k2`;`k2:num`] l4_vliftN_vunliftN_hi969) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `((k1 - (n2 + k2)) + k2) + n2 = k1 /\
                n2 + ((k1 - (n2 + k2)) + k2) = k1` (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_ARITH_TAC; ASM_REWRITE_TAC []]);;

let l4_of_vliftN_eq_vliftN969 = prove
 (`!e1 e2 n1 n2 k1 k2.
   l4_vliftN961 e1 n1 ((k1 + n2) + k2) = l4_vliftN961 e2 n2 k2 ==>
   ?e'. e1 = l4_vliftN961 e' n2 k2 /\ e2 = l4_vliftN961 e' n1 (k1 + k2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`e1:l4_vexpr961`;`n1:num`;`(k1 + n2) + k2`;`n2:num`;`k2:num`]
    l4_vskips_of_vliftN_hi969) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_vskips_vliftN969] THEN ARITH_TAC;
   REWRITE_TAC [l4_vskips_iff_exists969] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` SUBST_ALL_TAC) THEN
   EXISTS_TAC `e':l4_vexpr961` THEN REWRITE_TAC [] THEN
   GEN_REWRITE_TAC I [GSYM (SPECL [`e2:l4_vexpr961`;
                                   `l4_vliftN961 e' n1 (k1 + k2)`;
                                   `n2:num`;`k2:num`] l4_vliftN_inj969)] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`e':l4_vexpr961`;`n1:num`;`n2:num`;`k1 + k2`;`k2:num`] l4_vliftN_comm966) THEN
   ANTS_TAC THENL
   [ARITH_TAC;
    SUBGOAL_THEN `n2 + (k1 + k2) = (k1 + n2) + k2` SUBST1_TAC THENL
    [ARITH_TAC; DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC]]]);;

let l4_vskips_prime969 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vskips_prime969 (L4VBVar961 i) n k <=> (i < k + n ==> i < k)) /\
  (l4_vskips_prime969 (L4VSort961 u) n k <=> T) /\
  (l4_vskips_prime969 (L4VConst961 c us) n k <=> T) /\
  (l4_vskips_prime969 (L4VApp961 f a) n k <=>
    l4_vskips_prime969 f n k /\ l4_vskips_prime969 a n k) /\
  (l4_vskips_prime969 (L4VLam961 dom body) n k <=>
    l4_vskips_prime969 dom n k /\ l4_vskips_prime969 body n (SUC k)) /\
  (l4_vskips_prime969 (L4VForallE961 dom cod) n k <=>
    l4_vskips_prime969 dom n k /\ l4_vskips_prime969 cod n (SUC k))`;;

let l4_vskips_prime_iff_exists969 = prove
 (`!e n k. l4_vskips_prime969 e n k <=> (?e'. e = l4_vliftN961 e' n k)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`i:num`;`n:num`;`k:num`] THEN
   REWRITE_TAC [l4_vskips_prime969] THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `i < k` THENL
    [EXISTS_TAC `L4VBVar961 i` THEN ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961];
     EXISTS_TAC `L4VBVar961 (i - n)` THEN
     REWRITE_TAC [l4_vliftN961;l4_vlift_var961;injectivity "l4_vexpr961"] THEN
     COND_CASES_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` MP_TAC) THEN
    STRUCT_CASES_TAC (SPEC `e':l4_vexpr961` (cases "l4_vexpr961")) THEN
    REWRITE_TAC [l4_vliftN961;l4_vlift_var961;
                 distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_vskips_prime969] THEN
   EXISTS_TAC `L4VSort961 a` THEN REWRITE_TAC [l4_vliftN961];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_vskips_prime969] THEN
   EXISTS_TAC `L4VConst961 a0 a1` THEN REWRITE_TAC [l4_vliftN961];
   MAP_EVERY X_GEN_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`] THEN
   ASM_REWRITE_TAC [l4_vskips_prime969] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `L4VApp961 e' e''` THEN ASM_REWRITE_TAC [l4_vliftN961];
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` MP_TAC) THEN
    STRUCT_CASES_TAC (SPEC `e':l4_vexpr961` (cases "l4_vexpr961")) THEN
    REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    MESON_TAC []];
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`] THEN
   ASM_REWRITE_TAC [l4_vskips_prime969] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `L4VLam961 e' e''` THEN ASM_REWRITE_TAC [l4_vliftN961];
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` MP_TAC) THEN
    STRUCT_CASES_TAC (SPEC `e':l4_vexpr961` (cases "l4_vexpr961")) THEN
    REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    MESON_TAC []];
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`] THEN
   ASM_REWRITE_TAC [l4_vskips_prime969] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `L4VForallE961 e' e''` THEN ASM_REWRITE_TAC [l4_vliftN961];
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` MP_TAC) THEN
    STRUCT_CASES_TAC (SPEC `e':l4_vexpr961` (cases "l4_vexpr961")) THEN
    REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    MESON_TAC []]]);;

let l4_vskips_iff969 = prove
 (`!e n k. l4_vskips969 e n k <=> l4_vskips_prime969 e n k`,
  REWRITE_TAC [l4_vskips_iff_exists969;l4_vskips_prime_iff_exists969]);;

let l4_vskips_prime_vinstL969 = prove
 (`!e ls n k. l4_vskips_prime969 (l4_vinstL961 ls e) n k <=> l4_vskips_prime969 e n k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinstL961;l4_vskips_prime969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_of_vliftN_eq_vinstL969 = prove
 (`!e1 e2 ls n k.
   l4_vliftN961 e1 n k = l4_vinstL961 ls e2 ==>
   ?e'. e1 = l4_vinstL961 ls e' /\ e2 = l4_vliftN961 e' n k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_vskips_prime969 e2 n k` MP_TAC THENL
  [SUBST1_TAC (SYM (SPECL [`e2:l4_vexpr961`;`ls:l4_vlevel961 list`;`n:num`;`k:num`]
                 l4_vskips_prime_vinstL969)) THEN
   REWRITE_TAC [GSYM l4_vskips_iff969] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_vskips_vliftN969];
   REWRITE_TAC [l4_vskips_prime_iff_exists969] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` SUBST_ALL_TAC) THEN
   EXISTS_TAC `e':l4_vexpr961` THEN REWRITE_TAC [] THEN
   UNDISCH_TAC `l4_vliftN961 e1 n k = l4_vinstL961 ls (l4_vliftN961 e' n k)` THEN
   SIMP_TAC [l4_vinstL_vliftN966;l4_vliftN_inj969]]);;

(* ========================================================================= *)
(* 2. Structured Renamings: l4_vlift_op969, l4_vlift_prime969, Ctx.Lift'     *)
(* ========================================================================= *)

let l4_vlift_op_INDUCT969,l4_vlift_op_RECURSION969 = define_type
 "l4_vlift_op969 = L4VLRefl969
                 | L4VLSkip969 l4_vlift_op969
                 | L4VLCons969 l4_vlift_op969";;

let l4_vlift_op_skip_n969 = new_recursive_definition num_RECURSION
 `(l4_vlift_op_skip_n969 l 0 = l) /\
  (l4_vlift_op_skip_n969 l (SUC n) = L4VLSkip969 (l4_vlift_op_skip_n969 l n))`;;

let l4_vlift_op_skip_n_add969 = prove
 (`!k l n. l4_vlift_op_skip_n969 (l4_vlift_op_skip_n969 l n) k =
           l4_vlift_op_skip_n969 l (n + k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC [l4_vlift_op_skip_n969;ADD_CLAUSES]);;

let l4_vlift_op_cons_n969 = new_recursive_definition num_RECURSION
 `(l4_vlift_op_cons_n969 l 0 = l) /\
  (l4_vlift_op_cons_n969 l (SUC k) = L4VLCons969 (l4_vlift_op_cons_n969 l k))`;;

let l4_vlift_op_cons_n_add969 = prove
 (`!b l a. l4_vlift_op_cons_n969 (l4_vlift_op_cons_n969 l a) b =
           l4_vlift_op_cons_n969 l (a + b)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC [l4_vlift_op_cons_n969;ADD_CLAUSES]);;

let l4_vlift_op_cons_step969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_cons_step969 f l2 L4VLRefl969 = L4VLCons969 l2) /\
  (l4_vlift_op_cons_step969 f l2 (L4VLSkip969 l1) = L4VLSkip969 (f l1)) /\
  (l4_vlift_op_cons_step969 f l2 (L4VLCons969 l1) = L4VLCons969 (f l1))`;;

let l4_vlift_op_comp_aux969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_comp_aux969 L4VLRefl969 l1 = l1) /\
  (l4_vlift_op_comp_aux969 (L4VLSkip969 l2) l1 =
    L4VLSkip969 (l4_vlift_op_comp_aux969 l2 l1)) /\
  (l4_vlift_op_comp_aux969 (L4VLCons969 l2) l1 =
    l4_vlift_op_cons_step969 (l4_vlift_op_comp_aux969 l2) l2 l1)`;;

let l4_vlift_op_comp969 = new_definition
 `l4_vlift_op_comp969 l1 l2 = l4_vlift_op_comp_aux969 l2 l1`;;

let l4_vlift_op_comp_clauses969 = prove
 (`(!l1. l4_vlift_op_comp969 l1 L4VLRefl969 = l1) /\
   (!l1 l2. l4_vlift_op_comp969 l1 (L4VLSkip969 l2) =
            L4VLSkip969 (l4_vlift_op_comp969 l1 l2)) /\
   (!l2. l4_vlift_op_comp969 L4VLRefl969 (L4VLCons969 l2) = L4VLCons969 l2) /\
   (!l1 l2. l4_vlift_op_comp969 (L4VLSkip969 l1) (L4VLCons969 l2) =
            L4VLSkip969 (l4_vlift_op_comp969 l1 l2)) /\
   (!l1 l2. l4_vlift_op_comp969 (L4VLCons969 l1) (L4VLCons969 l2) =
            L4VLCons969 (l4_vlift_op_comp969 l1 l2))`,
  REWRITE_TAC [l4_vlift_op_comp969;l4_vlift_op_comp_aux969;l4_vlift_op_cons_step969]);;

let l4_vlift_op_refl_comp969 = prove
 (`!l. l4_vlift_op_comp969 L4VLRefl969 l = l`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN
  REWRITE_TAC [l4_vlift_op_comp_clauses969] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let l4_vlift_op_cons_n_comp969 = prove
 (`!n l1 l2.
   l4_vlift_op_cons_n969 (l4_vlift_op_comp969 l1 l2) n =
   l4_vlift_op_comp969 (l4_vlift_op_cons_n969 l1 n) (l4_vlift_op_cons_n969 l2 n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC [l4_vlift_op_cons_n969;l4_vlift_op_comp_clauses969]);;

let l4_vlift_op_dom969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_dom969 L4VLRefl969 = 0) /\
  (l4_vlift_op_dom969 (L4VLSkip969 l) = l4_vlift_op_dom969 l) /\
  (l4_vlift_op_dom969 (L4VLCons969 l) = SUC (l4_vlift_op_dom969 l))`;;

let l4_vlift_op_size969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_size969 L4VLRefl969 = 0) /\
  (l4_vlift_op_size969 (L4VLSkip969 l) = SUC (l4_vlift_op_size969 l)) /\
  (l4_vlift_op_size969 (L4VLCons969 l) = SUC (l4_vlift_op_size969 l))`;;

let l4_vlift_op_depth969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_depth969 L4VLRefl969 = 0) /\
  (l4_vlift_op_depth969 (L4VLSkip969 l) = SUC (l4_vlift_op_depth969 l)) /\
  (l4_vlift_op_depth969 (L4VLCons969 l) = l4_vlift_op_depth969 l)`;;

let l4_vlift_op_dom_add_depth969 = prove
 (`!l. l4_vlift_op_dom969 l + l4_vlift_op_depth969 l = l4_vlift_op_size969 l`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN
  REWRITE_TAC [l4_vlift_op_dom969;l4_vlift_op_depth969;l4_vlift_op_size969] THEN
  ARITH_TAC);;

let l4_vlift_op_depth_comp969 = prove
 (`!l2 l1.
   l4_vlift_op_depth969 (l4_vlift_op_comp969 l1 l2) =
   l4_vlift_op_depth969 l1 + l4_vlift_op_depth969 l2`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_depth969;ADD_CLAUSES];
   MAP_EVERY X_GEN_TAC [`l2:l4_vlift_op969`] THEN DISCH_TAC THEN GEN_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_depth969;ADD_CLAUSES];
   X_GEN_TAC `l2:l4_vlift_op969` THEN DISCH_TAC THEN X_GEN_TAC `l1:l4_vlift_op969` THEN
   STRUCT_CASES_TAC (SPEC `l1:l4_vlift_op969` (cases "l4_vlift_op969")) THEN
   ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_depth969;ADD_CLAUSES]]);;

let l4_vlift_op_depth_cons_n969 = prove
 (`!n l. l4_vlift_op_depth969 (l4_vlift_op_cons_n969 l n) = l4_vlift_op_depth969 l`,
  INDUCT_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [l4_vlift_op_cons_n969;l4_vlift_op_depth969]);;

let l4_vlift_op_depth_skip_n969 = prove
 (`!n l. l4_vlift_op_depth969 (l4_vlift_op_skip_n969 l n) = l4_vlift_op_depth969 l + n`,
  INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC [l4_vlift_op_skip_n969;l4_vlift_op_depth969;ADD_CLAUSES]);;

let l4_vlift_op_cons_n_skip_eq969 = prove
 (`!l k.
   l4_vlift_op_cons_n969 (L4VLSkip969 l) k =
   l4_vlift_op_comp969
     (l4_vlift_op_cons_n969 l k)
     (l4_vlift_op_cons_n969 (L4VLSkip969 L4VLRefl969) k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_op_cons_n_comp969;l4_vlift_op_comp_clauses969]);;

let l4_vlift_op_depth_succ969 = prove
 (`!l n.
   l4_vlift_op_depth969 l = SUC n ==>
   ?l' k. l4_vlift_op_depth969 l' = n /\
          l = l4_vlift_op_cons_n969 (L4VLSkip969 l') k`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vlift_op_depth969;NOT_SUC];
   MAP_EVERY X_GEN_TAC [`l:l4_vlift_op969`] THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
   REWRITE_TAC [l4_vlift_op_depth969;SUC_INJ] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`l:l4_vlift_op969`;`0`] THEN
   ASM_REWRITE_TAC [l4_vlift_op_cons_n969];
   X_GEN_TAC `l:l4_vlift_op969` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
   REWRITE_TAC [l4_vlift_op_depth969] THEN DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `l':l4_vlift_op969` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`l':l4_vlift_op969`;`SUC k`] THEN
   ASM_REWRITE_TAC [l4_vlift_op_cons_n969]]);;

let l4_vlift_op_lift_var969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_lift_var969 L4VLRefl969 i = i) /\
  (l4_vlift_op_lift_var969 (L4VLSkip969 l) i = SUC (l4_vlift_op_lift_var969 l i)) /\
  (l4_vlift_op_lift_var969 (L4VLCons969 l) i =
    if i = 0 then 0 else SUC (l4_vlift_op_lift_var969 l (i - 1)))`;;

let l4_vlift_op_lift_var_clauses969 = prove
 (`(!i. l4_vlift_op_lift_var969 L4VLRefl969 i = i) /\
   (!l i. l4_vlift_op_lift_var969 (L4VLSkip969 l) i = SUC (l4_vlift_op_lift_var969 l i)) /\
   (!l. l4_vlift_op_lift_var969 (L4VLCons969 l) 0 = 0) /\
   (!l i. l4_vlift_op_lift_var969 (L4VLCons969 l) (SUC i) =
          SUC (l4_vlift_op_lift_var969 l i))`,
  REWRITE_TAC [l4_vlift_op_lift_var969;NOT_SUC;SUC_SUB1]);;

let l4_vlift_op_lift_var_comp969 = prove
 (`!l2 l1 i.
   l4_vlift_op_lift_var969 (l4_vlift_op_comp969 l1 l2) i =
   l4_vlift_op_lift_var969 l2 (l4_vlift_op_lift_var969 l1 i)`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_lift_var_clauses969];
   X_GEN_TAC `l2:l4_vlift_op969` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_lift_var_clauses969];
   X_GEN_TAC `l2:l4_vlift_op969` THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`l1:l4_vlift_op969`;`i:num`] THEN
   STRUCT_CASES_TAC (SPEC `l1:l4_vlift_op969` (cases "l4_vlift_op969")) THENL
   [REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_lift_var_clauses969];
    ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_lift_var_clauses969];
    STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
    ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969;l4_vlift_op_lift_var_clauses969]]]);;

let l4_vlift_op_lift_var_skip_n969 = prove
 (`!n l i.
   l4_vlift_op_lift_var969 (l4_vlift_op_skip_n969 l n) i =
   l4_vlift_op_lift_var969 l i + n`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC [l4_vlift_op_skip_n969;l4_vlift_op_lift_var_clauses969;ADD_CLAUSES]);;

let l4_vlift_op_lift_var_cons_n_skip_n969 = prove
 (`!k n i.
   l4_vlift_op_lift_var969
     (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) i =
   l4_vlift_var961 n i k`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vlift_op_cons_n969;l4_vlift_op_lift_var_skip_n969;
                l4_vlift_op_lift_var_clauses969;l4_vlift_var961;LT] THEN ARITH_TAC;
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_vlift_op_cons_n969;l4_vlift_op_lift_var_clauses969;
                 l4_vlift_var961;ARITH_RULE `0 < SUC k`];
    ASM_REWRITE_TAC [l4_vlift_op_cons_n969;l4_vlift_op_lift_var_clauses969;
                     l4_vlift_var_succ966]]]);;

let l4_vlift_op_lift_var_depth_zero969 = prove
 (`!l i. l4_vlift_op_depth969 l = 0 ==> l4_vlift_op_lift_var969 l i = i`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vlift_op_lift_var_clauses969];
   REWRITE_TAC [l4_vlift_op_depth969;NOT_SUC];
   X_GEN_TAC `l:l4_vlift_op969` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
   REWRITE_TAC [l4_vlift_op_depth969] THEN DISCH_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
   REWRITE_TAC [l4_vlift_op_lift_var_clauses969] THEN AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_vlift_op_fixes_step969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_fixes_step969 rec L4VLRefl969 <=> T) /\
  (l4_vlift_op_fixes_step969 rec (L4VLSkip969 l) <=> F) /\
  (l4_vlift_op_fixes_step969 rec (L4VLCons969 l) <=> rec l)`;;

let l4_vlift_op_fixes969 = new_recursive_definition num_RECURSION
 `(l4_vlift_op_fixes969 0 rho <=> T) /\
  (l4_vlift_op_fixes969 (SUC k) rho <=>
    l4_vlift_op_fixes_step969 (l4_vlift_op_fixes969 k) rho)`;;

let l4_vlift_op_fixes_clauses969 = prove
 (`(!rho. l4_vlift_op_fixes969 0 rho <=> T) /\
   (!k. l4_vlift_op_fixes969 (SUC k) L4VLRefl969 <=> T) /\
   (!k l. l4_vlift_op_fixes969 (SUC k) (L4VLSkip969 l) <=> F) /\
   (!k l. l4_vlift_op_fixes969 (SUC k) (L4VLCons969 l) <=> l4_vlift_op_fixes969 k l)`,
  REWRITE_TAC [l4_vlift_op_fixes969;l4_vlift_op_fixes_step969]);;

let l4_vlift_op_fixes_lift_var_eq969 = prove
 (`!rho k i.
   l4_vlift_op_fixes969 k rho /\ i < k ==>
   l4_vlift_op_lift_var969 rho i = i`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vlift_op_lift_var_clauses969];
   X_GEN_TAC `rho:l4_vlift_op969` THEN DISCH_TAC THEN
   X_GEN_TAC `k:num` THEN STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
   REWRITE_TAC [FORALL_SIMP;LT;l4_vlift_op_fixes_clauses969];
   X_GEN_TAC `rho:l4_vlift_op969` THEN DISCH_TAC THEN
   X_GEN_TAC `k:num` THEN STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THENL
   [REWRITE_TAC [FORALL_SIMP;LT];
    REWRITE_TAC [l4_vlift_op_fixes_clauses969] THEN
    X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
    REWRITE_TAC [l4_vlift_op_lift_var_clauses969;LT_SUC] THEN
    ASM_MESON_TAC []]]);;

let l4_vlift_prime969 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vlift_prime969 (L4VBVar961 i) rho = L4VBVar961 (l4_vlift_op_lift_var969 rho i)) /\
  (l4_vlift_prime969 (L4VSort961 u) rho = L4VSort961 u) /\
  (l4_vlift_prime969 (L4VConst961 c us) rho = L4VConst961 c us) /\
  (l4_vlift_prime969 (L4VApp961 f a) rho =
    L4VApp961 (l4_vlift_prime969 f rho) (l4_vlift_prime969 a rho)) /\
  (l4_vlift_prime969 (L4VLam961 dom body) rho =
    L4VLam961 (l4_vlift_prime969 dom rho) (l4_vlift_prime969 body (L4VLCons969 rho))) /\
  (l4_vlift_prime969 (L4VForallE961 dom cod) rho =
    L4VForallE961 (l4_vlift_prime969 dom rho) (l4_vlift_prime969 cod (L4VLCons969 rho)))`;;

let l4_vlift_prime_cons_n_skip_n969 = prove
 (`!e n k.
   l4_vlift_prime969 e (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) =
   l4_vliftN961 e n k`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vlift_prime969;l4_vliftN961;
               l4_vlift_op_lift_var_cons_n_skip_n969;
               GSYM l4_vlift_op_cons_n969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlift_prime_comp969 = prove
 (`!e l1 l2.
   l4_vlift_prime969 e (l4_vlift_op_comp969 l1 l2) =
   l4_vlift_prime969 (l4_vlift_prime969 e l1) l2`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vlift_prime969;l4_vlift_op_lift_var_comp969;
               GSYM l4_vlift_op_comp_clauses969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlift_prime_depth_zero969 = prove
 (`!e l. l4_vlift_op_depth969 l = 0 ==> l4_vlift_prime969 e l = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [FORALL_SIMP;l4_vlift_prime969] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC l4_vlift_op_lift_var_depth_zero969 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_vlift_op_depth969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_vlift_op_depth969]]);;

let l4_vlift_prime_refl969 = prove
 (`!e. l4_vlift_prime969 e L4VLRefl969 = e`,
  GEN_TAC THEN MATCH_MP_TAC l4_vlift_prime_depth_zero969 THEN
  REWRITE_TAC [l4_vlift_op_depth969]);;

let l4_vlift_eq_vlift_prime969 = prove
 (`!e. l4_vlift961 e = l4_vlift_prime969 e (L4VLSkip969 L4VLRefl969)`,
  GEN_TAC THEN
  REWRITE_TAC [l4_vlift961;GSYM l4_vlift_prime_cons_n_skip_n969;
               ONE;l4_vlift_op_skip_n969;l4_vlift_op_cons_n969]);;

let l4_vlift_vlift_prime969 = prove
 (`!e l. l4_vlift961 (l4_vlift_prime969 e l) = l4_vlift_prime969 e (L4VLSkip969 l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlift_eq_vlift_prime969;GSYM l4_vlift_prime_comp969;
               l4_vlift_op_comp_clauses969]);;

let l4_vlift_prime_cons_vlift969 = prove
 (`!e l. l4_vlift_prime969 (l4_vlift961 e) (L4VLCons969 l) =
         l4_vlift_prime969 e (L4VLSkip969 l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlift_eq_vlift_prime969;GSYM l4_vlift_prime_comp969;
               l4_vlift_op_comp_clauses969;l4_vlift_op_refl_comp969]);;

let l4_vinstL_vlift_prime969 = prove
 (`!e ls rho.
   l4_vinstL961 ls (l4_vlift_prime969 e rho) =
   l4_vlift_prime969 (l4_vinstL961 ls e) rho`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vlift_prime969;l4_vinstL961] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vclosed_n_vlift_prime_eq969 = prove
 (`!e k rho.
   l4_vclosedN961 e k /\ l4_vlift_op_fixes969 k rho ==>
   l4_vlift_prime969 e rho = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [FORALL_SIMP;l4_vclosedN961;l4_vlift_prime969] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC l4_vlift_op_fixes_lift_var_eq969 THEN
   EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `SUC k` THEN
    ASM_REWRITE_TAC [l4_vlift_op_fixes_clauses969]];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `SUC k` THEN
    ASM_REWRITE_TAC [l4_vlift_op_fixes_clauses969]]]);;

(* Structured context lifting: Ctx.Lift' *)
let l4_vctx_lift_prime_RULES969,l4_vctx_lift_prime_INDUCT969,l4_vctx_lift_prime_CASES969 =
  new_inductive_definition
 `(!g. l4_vctx_lift_prime969 L4VLRefl969 g g) /\
  (!l g g' a.
     l4_vctx_lift_prime969 l g g' ==>
     l4_vctx_lift_prime969 (L4VLSkip969 l) g (CONS a g')) /\
  (!l g g' a.
     l4_vctx_lift_prime969 l g g' ==>
     l4_vctx_lift_prime969 (L4VLCons969 l) (CONS a g) (CONS (l4_vlift_prime969 a l) g'))`;;

let l4_vctx_lift_prime_refl969,
    l4_vctx_lift_prime_skip969,
    l4_vctx_lift_prime_cons969 =
  match CONJUNCTS l4_vctx_lift_prime_RULES969 with
  | [c1;c2;c3] -> (c1,c2,c3)
  | _ -> failwith "l4_vctx_lift_prime_RULES969: unexpected arity";;

let l4_vctx_lift_prime_append_skip_n969 = prove
 (`!prefix g.
   l4_vctx_lift_prime969
     (l4_vlift_op_skip_n969 L4VLRefl969 (LENGTH prefix)) g (APPEND prefix g)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC [LENGTH;APPEND;l4_vlift_op_skip_n969;l4_vctx_lift_prime_refl969] THEN
  MATCH_MP_TAC l4_vctx_lift_prime_skip969 THEN ASM_REWRITE_TAC []);;

let l4_vctx_liftN_to_lift_prime_ind969 = prove
 (`!n k g g'.
   l4_vctx_liftN966 n k g g' ==>
   l4_vctx_lift_prime969
     (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) g g'`,
  MATCH_MP_TAC l4_vctx_liftN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_vlift_op_cons_n969;l4_vctx_lift_prime_append_skip_n969];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vlift_op_cons_n969;GSYM l4_vlift_prime_cons_n_skip_n969] THEN
   MATCH_MP_TAC l4_vctx_lift_prime_cons969 THEN ASM_REWRITE_TAC []]);;

let l4_vctx_lift_prime_skip_n_inv969 = prove
 (`!n g g'.
   l4_vctx_lift_prime969 (l4_vlift_op_skip_n969 L4VLRefl969 n) g g' ==>
   ?prefix. LENGTH prefix = n /\ g' = APPEND prefix g`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vlift_op_skip_n969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [distinctness "l4_vlift_op969"] THEN STRIP_TAC THEN
   EXISTS_TAC `[]:l4_vexpr961 list` THEN ASM_REWRITE_TAC [LENGTH;APPEND];
   REWRITE_TAC [l4_vlift_op_skip_n969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [distinctness "l4_vlift_op969";injectivity "l4_vlift_op969"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`g:l4_vexpr961 list`;`g'':l4_vexpr961 list`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `prefix0:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `CONS (a:l4_vexpr961) prefix0` THEN ASM_REWRITE_TAC [LENGTH;APPEND]]);;

let l4_vctx_lift_prime_to_liftN_ind969 = prove
 (`!k n g g'.
   l4_vctx_lift_prime969
     (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) g g' ==>
   l4_vctx_liftN966 n k g g'`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vlift_op_cons_n969] THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vctx_lift_prime_skip_n_inv969) THEN
   DISCH_THEN (X_CHOOSE_THEN `prefix:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vctx_liftN_zero966 THEN ASM_REWRITE_TAC [];
   REWRITE_TAC [l4_vlift_op_cons_n969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [distinctness "l4_vlift_op969";injectivity "l4_vlift_op969"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THEN
   REWRITE_TAC [l4_vlift_prime_cons_n_skip_n969] THEN
   MATCH_MP_TAC l4_vctx_liftN_succ966 THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_vctx_liftN_iff_lift_prime969 = prove
 (`!n k g g'.
   l4_vctx_liftN966 n k g g' <=>
   l4_vctx_lift_prime969
     (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) g g'`,
  MESON_TAC [l4_vctx_liftN_to_lift_prime_ind969;l4_vctx_lift_prime_to_liftN_ind969]);;

let l4_vctx_lift_prime_comp_ind969 = prove
 (`!l2 g2 g3.
   l4_vctx_lift_prime969 l2 g2 g3 ==>
   (!l1 g1.
      l4_vctx_lift_prime969 l1 g1 g2 ==>
      l4_vctx_lift_prime969 (l4_vlift_op_comp969 l1 l2) g1 g3)`,
  MATCH_MP_TAC l4_vctx_lift_prime_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlift_op_comp_clauses969];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vlift_op_comp_clauses969] THEN
   MATCH_MP_TAC l4_vctx_lift_prime_skip969 THEN ASM_MESON_TAC [];
   MAP_EVERY X_GEN_TAC [`l2:l4_vlift_op969`;`g2:l4_vexpr961 list`;
                        `g3:l4_vexpr961 list`;`a:l4_vexpr961`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`l1:l4_vlift_op969`;`g1:l4_vexpr961 list`] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [injectivity "list"] THEN STRIP_TAC THEN l4_subst_vars_tac969 THENL
   [REWRITE_TAC [l4_vlift_op_comp_clauses969] THEN
    MATCH_MP_TAC l4_vctx_lift_prime_cons969 THEN
    ASM_MESON_TAC [l4_vctx_lift_prime_refl969;l4_vlift_op_refl_comp969];
    REWRITE_TAC [l4_vlift_op_comp_clauses969] THEN
    MATCH_MP_TAC l4_vctx_lift_prime_skip969 THEN ASM_MESON_TAC [];
    REWRITE_TAC [l4_vlift_op_comp_clauses969;GSYM l4_vlift_prime_comp969] THEN
    MATCH_MP_TAC l4_vctx_lift_prime_cons969 THEN ASM_MESON_TAC []]]);;

let l4_vctx_lift_prime_comp969 = prove
 (`!l1 l2 g1 g2 g3.
   l4_vctx_lift_prime969 l1 g1 g2 /\ l4_vctx_lift_prime969 l2 g2 g3 ==>
   l4_vctx_lift_prime969 (l4_vlift_op_comp969 l1 l2) g1 g3`,
  MESON_TAC [l4_vctx_lift_prime_comp_ind969]);;

let l4_vliftN_one_vlift_prime_cons_n969 = prove
 (`!e l k.
   l4_vliftN961 (l4_vlift_prime969 e (l4_vlift_op_cons_n969 l k)) 1 k =
   l4_vlift_prime969 e (l4_vlift_op_cons_n969 (L4VLSkip969 l) k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969;ONE;l4_vlift_op_skip_n969;
               GSYM l4_vlift_prime_comp969;GSYM l4_vlift_op_cons_n_skip_eq969]);;

let l4_vctx_lift_prime_of_cons_skip969 = prove
 (`!k l g1 g3.
   l4_vctx_lift_prime969 (l4_vlift_op_cons_n969 (L4VLSkip969 l) k) g1 g3 ==>
   ?g2. l4_vctx_lift_prime969 (l4_vlift_op_cons_n969 l k) g1 g2 /\
        l4_vctx_liftN966 1 k g2 g3`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vlift_op_cons_n969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [distinctness "l4_vlift_op969";injectivity "l4_vlift_op969"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THEN
   EXISTS_TAC `g':l4_vexpr961 list` THEN
   ASM_REWRITE_TAC [l4_vctx_liftN_one966];
   REWRITE_TAC [l4_vlift_op_cons_n969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vctx_lift_prime_CASES969] THEN
   REWRITE_TAC [distinctness "l4_vlift_op969";injectivity "l4_vlift_op969"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`l:l4_vlift_op969`;`g:l4_vexpr961 list`;
                                  `g':l4_vexpr961 list`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `g2:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `CONS (l4_vlift_prime969 a (l4_vlift_op_cons_n969 l k)) g2` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vctx_lift_prime_cons969 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [GSYM l4_vliftN_one_vlift_prime_cons_n969] THEN
    MATCH_MP_TAC l4_vctx_liftN_succ966 THEN ASM_REWRITE_TAC []]]);;

let l4_vctx_lift_prime_depth_zero_ind969 = prove
 (`!l g g'.
   l4_vctx_lift_prime969 l g g' ==>
   l4_vlift_op_depth969 l = 0 ==> g = g'`,
  MATCH_MP_TAC l4_vctx_lift_prime_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;];
   REWRITE_TAC [FORALL_SIMP;l4_vlift_op_depth969;NOT_SUC];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [l4_vlift_op_depth969] THEN
   DISCH_TAC THEN BINOP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC l4_vlift_prime_depth_zero969 THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC []]]);;

let l4_vctx_lift_prime_depth_zero969 = prove
 (`!l g g'. l4_vlift_op_depth969 l = 0 /\ l4_vctx_lift_prime969 l g g' ==> g = g'`,
  MESON_TAC [l4_vctx_lift_prime_depth_zero_ind969]);;

let l4_vlookup_weak_prime_ind969 = prove
 (`!rho g g'.
   l4_vctx_lift_prime969 rho g g' ==>
   (!i ty.
      l4_vlookup961 g i ty ==>
      l4_vlookup961 g' (l4_vlift_op_lift_var969 rho i) (l4_vlift_prime969 ty rho))`,
  MATCH_MP_TAC l4_vctx_lift_prime_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vlift_op_lift_var_clauses969;l4_vlift_prime_refl969];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vlift_op_lift_var_clauses969;GSYM l4_vlift_vlift_prime969] THEN
   MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THENL
   [REWRITE_TAC [l4_vlift_op_lift_var_clauses969;l4_vlift_prime_cons_vlift969;
                 GSYM l4_vlift_vlift_prime969;l4_vlookup_RULES961];
    REWRITE_TAC [l4_vlift_op_lift_var_clauses969;l4_vlift_prime_cons_vlift969;
                 GSYM l4_vlift_vlift_prime969] THEN
    MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_MESON_TAC []]]);;

let l4_vlookup_weak_prime969 = prove
 (`!rho g g' i ty.
   l4_vctx_lift_prime969 rho g g' /\ l4_vlookup961 g i ty ==>
   l4_vlookup961 g' (l4_vlift_op_lift_var969 rho i) (l4_vlift_prime969 ty rho)`,
  MESON_TAC [l4_vlookup_weak_prime_ind969]);;

let l4_vlookup_weak_u_inv_ind969 = prove
 (`!rho g g'.
   l4_vctx_lift_prime969 rho g g' ==>
   (!i ty'.
      l4_vlookup961 g' (l4_vlift_op_lift_var969 rho i) ty' ==>
      ?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vlookup961 g i ty)`,
  MATCH_MP_TAC l4_vctx_lift_prime_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vlift_op_lift_var_clauses969] THEN DISCH_TAC THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vlift_prime_refl969];
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;
                        `g':l4_vexpr961 list`;`a:l4_vexpr961`] THEN
   DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`;`ty':l4_vexpr961`] THEN
   REWRITE_TAC [l4_vlift_op_lift_var_clauses969] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";NOT_SUC;SUC_INJ] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THEN
   FIRST_X_ASSUM (fun h -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP h)) THEN
   DISCH_THEN (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `ty0:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vlift_vlift_prime969];
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;
                        `g':l4_vexpr961 list`;`a:l4_vexpr961`] THEN
   DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`;`ty':l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_vlift_op_lift_var_clauses969] THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
    REWRITE_TAC [injectivity "list";distinctness "num"] THEN
    STRIP_TAC THEN l4_subst_vars_tac969 THEN
    EXISTS_TAC `l4_vlift961 a` THEN
    REWRITE_TAC [l4_vlift_prime_cons_vlift969;l4_vlift_vlift_prime969;l4_vlookup_RULES961];
    REWRITE_TAC [l4_vlift_op_lift_var_clauses969] THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
    REWRITE_TAC [injectivity "list";NOT_SUC;SUC_INJ] THEN
    STRIP_TAC THEN l4_subst_vars_tac969 THEN
    FIRST_X_ASSUM (fun h -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP h)) THEN
    DISCH_THEN (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l4_vlift961 ty0` THEN
    ASM_REWRITE_TAC [l4_vlift_prime_cons_vlift969;l4_vlift_vlift_prime969] THEN
    MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_REWRITE_TAC []]]);;

let l4_vlookup_weak_u_inv969 = prove
 (`!rho g g' i ty'.
   l4_vctx_lift_prime969 rho g g' /\
   l4_vlookup961 g' (l4_vlift_op_lift_var969 rho i) ty' ==>
   ?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vlookup961 g i ty`,
  MESON_TAC [l4_vlookup_weak_u_inv_ind969]);;

let l4_vis_defeq_weak_prime_ind969 = prove
 (`!d l g g' env uvars e1 e2 ty.
   l4_vlift_op_depth969 l = d /\
   l4_venv_closed966 env /\
   l4_vctx_lift_prime969 l g g' /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g'
     (l4_vlift_prime969 e1 l) (l4_vlift_prime969 e2 l) (l4_vlift_prime969 ty l)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
  [SUBGOAL_THEN `g:l4_vexpr961 list = g'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_vctx_lift_prime_depth_zero969]; ALL_TAC] THEN
   ASM_SIMP_TAC [l4_vlift_prime_depth_zero969];
   MP_TAC (SPECL [`l:l4_vlift_op969`;`d:num`] l4_vlift_op_depth_succ969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `l0:l4_vlift_op969`
     (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
   MP_TAC (SPECL [`k:num`;`l0:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`]
     l4_vctx_lift_prime_of_cons_skip969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `g1:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   REWRITE_TAC [GSYM l4_vliftN_one_vlift_prime_cons_n969] THEN
   MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
   EXISTS_TAC `g1:l4_vexpr961 list` THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
   ASM_REWRITE_TAC [l4_vlift_op_depth_cons_n969]]);;

let l4_vis_defeq_weak_prime969 = prove
 (`!env uvars l g g' e1 e2 ty.
   l4_venv_closed966 env /\
   l4_vctx_lift_prime969 l g g' /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g'
     (l4_vlift_prime969 e1 l) (l4_vlift_prime969 e2 l) (l4_vlift_prime969 ty l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`l4_vlift_op_depth969 l`;`l:l4_vlift_op969`;
                 `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                 `env:l4_venv961`;`uvars:num`;
                 `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
    l4_vis_defeq_weak_prime_ind969) THEN
  ASM_SIMP_TAC []);;

let l4_vhas_type_weak_prime969 = prove
 (`!env uvars l g g' e ty.
   l4_venv_closed966 env /\
   l4_vctx_lift_prime969 l g g' /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vhas_type961 env uvars g' (l4_vlift_prime969 e l) (l4_vlift_prime969 ty l)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_weak_prime969]);;

let l4_vis_type_weak_prime969 = prove
 (`!env uvars l g g' ty.
   l4_venv_closed966 env /\
   l4_vctx_lift_prime969 l g g' /\
   l4_vis_type961 env uvars g ty ==>
   l4_vis_type961 env uvars g' (l4_vlift_prime969 ty l)`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l:l4_vlift_op969`;
                 `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                 `ty:l4_vexpr961`;`ty:l4_vexpr961`;`L4VSort961 u`]
    l4_vis_defeq_weak_prime969) THEN
  ASM_SIMP_TAC [l4_vlift_prime969]);;

let l4_vis_defeq_u_weak_prime969 = prove
 (`!env uvars l g g' e1 e2.
   l4_venv_closed966 env /\
   l4_vctx_lift_prime969 l g g' /\
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   l4_vis_defeq_u961 env uvars g' (l4_vlift_prime969 e1 l) (l4_vlift_prime969 e2 l)`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_weak_prime969]);;

(* ========================================================================= *)
(* 3. Simultaneous Substitutions (:num -> l4_vexpr961) (VExpr.lean:772-944)  *)
(* ========================================================================= *)

let l4_vsubst_id969 = new_definition
 `l4_vsubst_id969 (i:num) = L4VBVar961 i`;;

let l4_vsubst_head969 = new_definition
 `l4_vsubst_head969 (s:num->l4_vexpr961) = s 0`;;

let l4_vsubst_tail969 = new_definition
 `l4_vsubst_tail969 (s:num->l4_vexpr961) i = s (SUC i)`;;

let l4_vsubst_cons969 = new_recursive_definition num_RECURSION
 `(l4_vsubst_cons969 (s:num->l4_vexpr961) e 0 = e) /\
  (l4_vsubst_cons969 s e (SUC i) = s i)`;;

let l4_vsubst_one969 = new_definition
 `l4_vsubst_one969 e = l4_vsubst_cons969 l4_vsubst_id969 e`;;

let l4_vsubst_cons_head969 = prove
 (`!s e. l4_vsubst_head969 (l4_vsubst_cons969 s e) = e`,
  REWRITE_TAC [l4_vsubst_head969;l4_vsubst_cons969]);;

let l4_vsubst_cons_tail969 = prove
 (`!s e. l4_vsubst_tail969 (l4_vsubst_cons969 s e) = s`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_tail969;l4_vsubst_cons969]);;

let l4_vsubst_lift969 = new_recursive_definition num_RECURSION
 `(l4_vsubst_lift969 (s:num->l4_vexpr961) 0 = L4VBVar961 0) /\
  (l4_vsubst_lift969 s (SUC i) = l4_vlift961 (s i))`;;

let l4_vsubst_lift_n969 = new_recursive_definition num_RECURSION
 `(l4_vsubst_lift_n969 s 0 = s) /\
  (l4_vsubst_lift_n969 s (SUC k) = l4_vsubst_lift969 (l4_vsubst_lift_n969 s k))`;;

let l4_vsubst969 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vsubst969 (L4VBVar961 i) s = s i) /\
  (l4_vsubst969 (L4VSort961 u) s = L4VSort961 u) /\
  (l4_vsubst969 (L4VConst961 c us) s = L4VConst961 c us) /\
  (l4_vsubst969 (L4VApp961 f a) s = L4VApp961 (l4_vsubst969 f s) (l4_vsubst969 a s)) /\
  (l4_vsubst969 (L4VLam961 dom body) s =
    L4VLam961 (l4_vsubst969 dom s) (l4_vsubst969 body (l4_vsubst_lift969 s))) /\
  (l4_vsubst969 (L4VForallE961 dom cod) s =
    L4VForallE961 (l4_vsubst969 dom s) (l4_vsubst969 cod (l4_vsubst_lift969 s)))`;;

let l4_vsubst_lift_r969 = new_definition
 `l4_vsubst_lift_r969 (s:num->l4_vexpr961) rho i = l4_vlift_prime969 (s i) rho`;;

let l4_vsubst_lift_l969 = new_definition
 `l4_vsubst_lift_l969 rho (s:num->l4_vexpr961) i = s (l4_vlift_op_lift_var969 rho i)`;;

let l4_vsubst_lift_l_lift969 = prove
 (`!rho s.
   l4_vsubst_lift969 (l4_vsubst_lift_l969 rho s) =
   l4_vsubst_lift_l969 (L4VLCons969 rho) (l4_vsubst_lift969 s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_lift969;l4_vsubst_lift_l969;l4_vlift_op_lift_var_clauses969]);;

let l4_vsubst_lift_r_lift969 = prove
 (`!s rho.
   l4_vsubst_lift969 (l4_vsubst_lift_r969 s rho) =
   l4_vsubst_lift_r969 (l4_vsubst_lift969 s) (L4VLCons969 rho)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_lift969;l4_vsubst_lift_r969;l4_vlift_prime969;
               l4_vlift_op_lift_var_clauses969;
               l4_vlift_vlift_prime969;l4_vlift_prime_cons_vlift969]);;

let l4_vsubst_vlift_prime969 = prove
 (`!e rho s.
   l4_vsubst969 (l4_vlift_prime969 e rho) s =
   l4_vsubst969 e (l4_vsubst_lift_l969 rho s)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vlift_prime969;l4_vsubst969;l4_vsubst_lift_l969;
               l4_vsubst_lift_l_lift969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vlift_prime_vsubst969 = prove
 (`!e s rho.
   l4_vlift_prime969 (l4_vsubst969 e s) rho =
   l4_vsubst969 e (l4_vsubst_lift_r969 s rho)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vlift_prime969;l4_vsubst969;l4_vsubst_lift_r969;
               l4_vsubst_lift_r_lift969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vsubst_comp969 = new_definition
 `l4_vsubst_comp969 (s1:num->l4_vexpr961) (s2:num->l4_vexpr961) i =
   l4_vsubst969 (s1 i) s2`;;

let l4_vsubst_comp_lift969 = prove
 (`!s1 s2.
   l4_vsubst_lift969 (l4_vsubst_comp969 s1 s2) =
   l4_vsubst_comp969 (l4_vsubst_lift969 s1) (l4_vsubst_lift969 s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC [l4_vsubst_lift969;l4_vsubst_comp969;l4_vsubst969] THEN
  REWRITE_TAC [l4_vlift_eq_vlift_prime969;l4_vlift_prime_vsubst969;l4_vsubst_vlift_prime969] THEN
  AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_r969;l4_vsubst_lift_l969;
                                l4_vlift_op_lift_var_clauses969;l4_vsubst_lift969;
                                GSYM l4_vlift_eq_vlift_prime969]);;

let l4_vsubst_comp_eq969 = prove
 (`!e s1 s2.
   l4_vsubst969 (l4_vsubst969 e s1) s2 =
   l4_vsubst969 e (l4_vsubst_comp969 s1 s2)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vsubst969;l4_vsubst_comp969;l4_vsubst_comp_lift969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vliftN_vsubst969 = prove
 (`!e n k s.
   l4_vsubst969 (l4_vliftN961 e n k) s =
   l4_vsubst969 e
     (l4_vsubst_lift_l969
       (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969;l4_vsubst_vlift_prime969]);;

let l4_vsubst_id_lift969 = prove
 (`l4_vsubst_lift969 l4_vsubst_id969 = l4_vsubst_id969`,
  REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_lift969;l4_vsubst_id969;l4_vlift961;
               l4_vliftN961;l4_vlift_var961;LT] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let l4_vsubst_id_eq969 = prove
 (`!e. l4_vsubst969 e l4_vsubst_id969 = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vsubst969;l4_vsubst_id969;l4_vsubst_id_lift969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vsubst_lift_l_refl969 = prove
 (`!s. l4_vsubst_lift_l969 L4VLRefl969 s = s`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_l969;l4_vlift_op_lift_var_clauses969]);;

let l4_vsubst_lift_l_skip969 = prove
 (`!rho s.
   l4_vsubst_lift_l969 (L4VLSkip969 rho) s =
   l4_vsubst_lift_l969 rho (l4_vsubst_tail969 s)`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_l969;l4_vsubst_tail969;
               l4_vlift_op_lift_var_clauses969]);;

let l4_vlift_vsubst969 = prove
 (`!e s. l4_vsubst969 (l4_vlift961 e) s = l4_vsubst969 e (l4_vsubst_tail969 s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlift_eq_vlift_prime969;l4_vsubst_vlift_prime969;
               l4_vsubst_lift_l_skip969;l4_vsubst_lift_l_refl969]);;

let l4_vsubst_lift_r_tail969 = prove
 (`!s rho.
   l4_vsubst_tail969 (l4_vsubst_lift_r969 s rho) =
   l4_vsubst_lift_r969 (l4_vsubst_tail969 s) rho`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_tail969;l4_vsubst_lift_r969]);;

let l4_vlift_op_inv969 = new_recursive_definition l4_vlift_op_RECURSION969
 `(l4_vlift_op_inv969 L4VLRefl969 = l4_vsubst_id969) /\
  (l4_vlift_op_inv969 (L4VLSkip969 rho) =
    l4_vsubst_cons969 (l4_vlift_op_inv969 rho) l4_vexpr_default969) /\
  (l4_vlift_op_inv969 (L4VLCons969 rho) =
    l4_vsubst_lift969 (l4_vlift_op_inv969 rho))`;;

let l4_vsubst_lift_l_inv_var969 = prove
 (`!rho i. l4_vlift_op_inv969 rho (l4_vlift_op_lift_var969 rho i) = L4VBVar961 i`,
  MATCH_MP_TAC l4_vlift_op_INDUCT969 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vlift_op_inv969;l4_vlift_op_lift_var_clauses969;l4_vsubst_id969];
   X_GEN_TAC `rho:l4_vlift_op969` THEN DISCH_TAC THEN GEN_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_inv969;l4_vlift_op_lift_var_clauses969;l4_vsubst_cons969];
   X_GEN_TAC `rho:l4_vlift_op969` THEN DISCH_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_inv969;l4_vlift_op_lift_var_clauses969;l4_vsubst_lift969;
                    l4_vlift961;l4_vliftN961;l4_vlift_var961;LT;ARITH_RULE `1 + i = SUC i`]]);;

let l4_vsubst_lift_l_inv969 = prove
 (`!rho. l4_vsubst_lift_l969 rho (l4_vlift_op_inv969 rho) = l4_vsubst_id969`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_l969;l4_vsubst_id969;l4_vsubst_lift_l_inv_var969]);;

let l4_vlift_prime_inj969 = prove
 (`!e1 e2 rho. l4_vlift_prime969 e1 rho = l4_vlift_prime969 e2 rho <=> e1 = e2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_THEN (MP_TAC o C AP_THM `l4_vlift_op_inv969 rho` o AP_TERM `l4_vsubst969`) THEN
   REWRITE_TAC [l4_vsubst_vlift_prime969;l4_vsubst_lift_l_inv969;l4_vsubst_id_eq969];
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let l4_vlookup_weak_prime_iff969 = prove
 (`!rho g g' i ty.
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vlookup961 g' (l4_vlift_op_lift_var969 rho i) (l4_vlift_prime969 ty rho) <=>
    l4_vlookup961 g i ty)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN
   MP_TAC (SPECL [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `i:num`;`l4_vlift_prime969 ty rho`] l4_vlookup_weak_u_inv969) THEN
   ASM_REWRITE_TAC [l4_vlift_prime_inj969] THEN MESON_TAC [];
   ASM_MESON_TAC [l4_vlookup_weak_prime969]]);;

let l4_vlookup_weakN_iff969 = prove
 (`!n k g g' i ty.
   l4_vctx_liftN966 n k g g' ==>
   (l4_vlookup961 g' (l4_vlift_var961 n i k) (l4_vliftN961 ty n k) <=>
    l4_vlookup961 g i ty)`,
  MESON_TAC [l4_vctx_liftN_iff_lift_prime969;
             l4_vlift_op_lift_var_cons_n_skip_n969;
             l4_vlift_prime_cons_n_skip_n969;
             l4_vlookup_weak_prime_iff969]);;

let l4_vinst_var_eq_vsubst_lift_n969 = prove
 (`!k i a.
   l4_vinst_var961 i a k = l4_vsubst_lift_n969 (l4_vsubst_one969 a) k i`,
  INDUCT_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
  [REWRITE_TAC [l4_vinst_var961;LT;l4_vliftN_zero961;
                l4_vsubst_lift_n969;l4_vsubst_one969;l4_vsubst_cons969];
   REWRITE_TAC [l4_vinst_var961;LT;NOT_SUC;SUC_SUB1;
                l4_vsubst_lift_n969;l4_vsubst_one969;l4_vsubst_cons969;l4_vsubst_id969];
   REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;
                l4_vsubst_lift_n969;l4_vsubst_lift969];
   ASM_REWRITE_TAC [l4_vinst_var_succ966;l4_vsubst_lift_n969;l4_vsubst_lift969]]);;

let l4_vinst_n_eq_vsubst969 = prove
 (`!e a k. l4_vinst961 e a k = l4_vsubst969 e (l4_vsubst_lift_n969 (l4_vsubst_one969 a) k)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinst961;l4_vsubst969;l4_vinst_var_eq_vsubst_lift_n969;
               GSYM l4_vsubst_lift_n969] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_vinst0_eq_vsubst969 = prove
 (`!e a. l4_vinst0961 e a = l4_vsubst969 e (l4_vsubst_one969 a)`,
  REWRITE_TAC [l4_vinst0961;l4_vinst_n_eq_vsubst969;l4_vsubst_lift_n969]);;

let l4_vsubst_depth969 = new_definition
 `l4_vsubst_depth969 (s:num->l4_vexpr961) n n' <=> !i. s (i + n') = L4VBVar961 (i + n)`;;

let l4_vsubst_trunc969 = new_definition
 `l4_vsubst_trunc969 (s:num->l4_vexpr961) n n' i =
   if n' <= i then L4VBVar961 ((i - n') + n) else s i`;;

let l4_vsubst_lift_r_one969 = prove
 (`!e rho.
   l4_vsubst_lift_r969 (l4_vsubst_one969 e) rho =
   l4_vsubst_lift_l969 (L4VLCons969 rho) (l4_vsubst_one969 (l4_vlift_prime969 e rho))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_lift_r969;l4_vsubst_lift_l969;l4_vsubst_one969;
               l4_vsubst_cons969;l4_vsubst_id969;l4_vlift_prime969;
               l4_vlift_op_lift_var_clauses969]);;

let l4_vlift_prime_vinst0_hi969 = prove
 (`!e1 e2 rho.
   l4_vlift_prime969 (l4_vinst0961 e1 e2) rho =
   l4_vinst0961 (l4_vlift_prime969 e1 (L4VLCons969 rho)) (l4_vlift_prime969 e2 rho)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vinst0_eq_vsubst969;l4_vlift_prime_vsubst969;
               l4_vsubst_vlift_prime969;l4_vsubst_lift_r_one969]);;

let l4_vsubst_fixes969 = new_definition
 `l4_vsubst_fixes969 (s:num->l4_vexpr961) n <=> !i. i < n ==> s i = L4VBVar961 i`;;

let l4_vsubst_fixes_zero969 = prove
 (`!s. l4_vsubst_fixes969 s 0`,
  REWRITE_TAC [l4_vsubst_fixes969;LT]);;

let l4_vsubst_fixes_lift969 = prove
 (`!s n. l4_vsubst_fixes969 s n ==> l4_vsubst_fixes969 (l4_vsubst_lift969 s) (SUC n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vsubst_fixes969] THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC [l4_vsubst_lift969;LT_SUC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [l4_vlift961;l4_vliftN961;l4_vlift_var961;LT;ARITH_RULE `1 + i = SUC i`]);;

let l4_vclosed_n_vsubst_eq969 = prove
 (`!e k s. l4_vclosedN961 e k /\ l4_vsubst_fixes969 s k ==> l4_vsubst969 e s = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [FORALL_SIMP;l4_vclosedN961;l4_vsubst969] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vsubst_fixes969] THEN MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN
   ASM_MESON_TAC [l4_vsubst_fixes_lift969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN
   ASM_MESON_TAC [l4_vsubst_fixes_lift969]]);;

let l4_vclosed0_vsubst_eq969 = prove
 (`!e s. l4_vclosedN961 e 0 ==> l4_vsubst969 e s = e`,
  MESON_TAC [l4_vclosed_n_vsubst_eq969;l4_vsubst_fixes_zero969]);;

let l4_vlift_vsubst_cons969 = prove
 (`!e s t. l4_vsubst969 (l4_vlift961 e) (l4_vsubst_cons969 s t) = l4_vsubst969 e s`,
  REWRITE_TAC [l4_vlift_vsubst969;l4_vsubst_cons_tail969]);;

let l4_vlift_vsubst_lift969 = prove
 (`!e s. l4_vsubst969 (l4_vlift961 e) (l4_vsubst_lift969 s) = l4_vlift961 (l4_vsubst969 e s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlift_eq_vlift_prime969;l4_vsubst_vlift_prime969;l4_vlift_prime_vsubst969] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_l969;l4_vsubst_lift_r969;
               l4_vlift_op_lift_var_clauses969;l4_vsubst_lift969;
               GSYM l4_vlift_eq_vlift_prime969]);;

let l4_vsubst_vinst969 = prove
 (`!e a s.
   l4_vsubst969 (l4_vinst0961 e a) s =
   l4_vinst0961 (l4_vsubst969 e (l4_vsubst_lift969 s)) (l4_vsubst969 a s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vinst0_eq_vsubst969;l4_vsubst_comp_eq969] THEN
  AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_comp969;l4_vsubst_one969;l4_vsubst_cons969;
               l4_vsubst_id969;l4_vsubst_lift969;l4_vsubst969;
               l4_vlift_vsubst_cons969;l4_vsubst_id_eq969]);;

let l4_vinst_vsubst_lift_cons969 = prove
 (`!e s x.
   l4_vinst0961 (l4_vsubst969 e (l4_vsubst_lift969 s)) x =
   l4_vsubst969 e (l4_vsubst_cons969 s x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vinst0_eq_vsubst969;l4_vsubst_comp_eq969] THEN
  AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC [l4_vsubst_comp969;l4_vsubst_lift969;l4_vsubst_one969;
               l4_vsubst_cons969;l4_vsubst969;
               l4_vlift_vsubst_cons969;l4_vsubst_id_eq969]);;

let l4_vinst_l_vsubst_lift_comm969 = prove
 (`!ls s.
   l4_vsubst_lift969 (\i. l4_vinstL961 ls (s i)) =
   (\i. l4_vinstL961 ls (l4_vsubst_lift969 s i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
  BETA_TAC THEN REWRITE_TAC [l4_vsubst_lift969;l4_vinstL961] THEN
  BETA_TAC THEN REWRITE_TAC [l4_vinstL_vlift966]);;

let l4_vinst_l_vsubst969 = prove
 (`!e ls s.
   l4_vinstL961 ls (l4_vsubst969 e s) =
   l4_vsubst969 (l4_vinstL961 ls e) (\i. l4_vinstL961 ls (s i))`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vsubst969;l4_vinstL961;l4_vinst_l_vsubst_lift_comm969] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(* ========================================================================= *)
(* 4. Pointwise Substitution Typing: Ctx.SubstEq (Typing/Lemmas.lean:901)    *)
(* ========================================================================= *)

let l4_vctx_subst_eq_RULES969,l4_vctx_subst_eq_INDUCT969,l4_vctx_subst_eq_CASES969 =
  new_inductive_definition
 `(!env uvars g0 s s'.
     l4_vctx_subst_eq969 env uvars g0 s s' []) /\
  (!env uvars g0 s s' g a u.
     l4_vctx_subst_eq969 env uvars g0 (l4_vsubst_tail969 s) (l4_vsubst_tail969 s') g /\
     l4_vhas_type961 env uvars g a (L4VSort961 u) /\
     l4_vis_defeq961 env uvars g0 (l4_vsubst_head969 s) (l4_vsubst_head969 s')
       (l4_vsubst969 a (l4_vsubst_tail969 s)) ==>
     l4_vctx_subst_eq969 env uvars g0 s s' (CONS a g))`;;

let l4_vctx_subst_eq_nil969, l4_vctx_subst_eq_cons969 =
  match CONJUNCTS l4_vctx_subst_eq_RULES969 with
  | [c1;c2] -> (c1,c2)
  | _ -> failwith "l4_vctx_subst_eq_RULES969: unexpected arity";;

let l4_vctx_subst_eq_left_ind969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==>
   l4_vctx_subst_eq969 env uvars g0 s s g`,
  MATCH_MP_TAC l4_vctx_subst_eq_INDUCT969 THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vctx_subst_eq_nil969];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]]);;

let l4_vctx_subst_eq_left969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==>
   l4_vctx_subst_eq969 env uvars g0 s s g`,
  ACCEPT_TAC l4_vctx_subst_eq_left_ind969);;

let l4_vctx_subst_eq_lookup_ind969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==>
   (!i ty.
      l4_vlookup961 g i ty ==>
      l4_vis_defeq961 env uvars g0 (s i) (s' i) (l4_vsubst969 ty s))`,
  MATCH_MP_TAC l4_vctx_subst_eq_INDUCT969 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [NOT_CONS_NIL];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                        `s:num->l4_vexpr961`;`s':num->l4_vexpr961`;
                        `g:l4_vexpr961 list`;`a:l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`;`ty:l4_vexpr961`] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst_head969]) THEN
    ASM_REWRITE_TAC [l4_vlift_vsubst969];
    REWRITE_TAC [l4_vlift_vsubst969;GSYM l4_vsubst_tail969] THEN
    ASM_MESON_TAC []]]);;

let l4_vctx_subst_eq_lookup969 = prove
 (`!env uvars g0 s s' g i ty.
   l4_vctx_subst_eq969 env uvars g0 s s' g /\
   l4_vlookup961 g i ty ==>
   l4_vis_defeq961 env uvars g0 (s i) (s' i) (l4_vsubst969 ty s)`,
  MESON_TAC [l4_vctx_subst_eq_lookup_ind969]);;

let l4_vctx_subst_eq_skip_ind969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==>
   (!b. l4_venv_closed966 env ==>
     l4_vctx_subst_eq969 env uvars (CONS b g0)
       (l4_vsubst_lift_r969 s (L4VLSkip969 L4VLRefl969))
       (l4_vsubst_lift_r969 s' (L4VLSkip969 L4VLRefl969)) g)`,
  MATCH_MP_TAC l4_vctx_subst_eq_INDUCT969 THEN CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vctx_subst_eq_nil969];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                        `s:num->l4_vexpr961`;`s':num->l4_vexpr961`;
                        `g:l4_vexpr961 list`;`a:l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN X_GEN_TAC `b:l4_vexpr961` THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_REWRITE_TAC [l4_vsubst_lift_r_tail969] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vsubst_head969;l4_vsubst_lift_r969;
                 GSYM l4_vlift_prime_vsubst969] THEN
    MATCH_MP_TAC l4_vis_defeq_weak_prime969 THEN
    EXISTS_TAC `g0:l4_vexpr961 list` THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst_head969]) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_lift_prime_skip969 THEN
    REWRITE_TAC [l4_vctx_lift_prime_refl969]]]);;

let l4_vctx_subst_eq_skip969 = prove
 (`!env uvars g0 b s s' g.
   l4_venv_closed966 env /\
   l4_vctx_subst_eq969 env uvars g0 s s' g ==>
   l4_vctx_subst_eq969 env uvars (CONS b g0)
     (l4_vsubst_lift_r969 s (L4VLSkip969 L4VLRefl969))
     (l4_vsubst_lift_r969 s' (L4VLSkip969 L4VLRefl969)) g`,
  MESON_TAC [l4_vctx_subst_eq_skip_ind969]);;

let l4_vsubst_lift_tail_eq_lift_r969 = prove
 (`!s. l4_vsubst_tail969 (l4_vsubst_lift969 s) =
       l4_vsubst_lift_r969 s (L4VLSkip969 L4VLRefl969)`,
  GEN_TAC THEN
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_tail969;l4_vsubst_lift969;
               l4_vsubst_lift_r969;l4_vlift_eq_vlift_prime969]);;

let l4_vctx_subst_eq_lift969 = prove
 (`!env uvars g0 s s' g a u.
   l4_venv_closed966 env /\
   l4_vctx_subst_eq969 env uvars g0 s s' g /\
   l4_vhas_type961 env uvars g a (L4VSort961 u) ==>
   l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 a s) g0)
     (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS a g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
  ASM_REWRITE_TAC [l4_vsubst_lift_tail_eq_lift_r969;l4_vsubst_head969;
                   l4_vsubst_lift969;GSYM l4_vlift_prime_vsubst969;
                   GSYM l4_vlift_eq_vlift_prime969] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC l4_vctx_subst_eq_skip969 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961]]);;

let l4_vctx_subst_eq_lift_at969 = prove
 (`!env uvars g0 s s' g a x u.
   l4_venv_closed966 env /\
   l4_vctx_subst_eq969 env uvars g0 s s' g /\
   l4_vhas_type961 env uvars g a (L4VSort961 u) /\
   l4_vis_defeq961 env uvars g0 (l4_vsubst969 a s) x (L4VSort961 u) ==>
   l4_vctx_subst_eq969 env uvars (CONS x g0)
     (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS a g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
  ASM_REWRITE_TAC [l4_vsubst_lift_tail_eq_lift_r969;l4_vsubst_head969;
                   l4_vsubst_lift969;GSYM l4_vlift_prime_vsubst969;
                   GSYM l4_vlift_eq_vlift_prime969] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC l4_vctx_subst_eq_skip969 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift961 x`;`u:l4_vlevel961`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;`x:l4_vexpr961`;
                   `l4_vsubst969 a s`;`x:l4_vexpr961`;`L4VSort961 u`]
      l4_vis_defeq_weak966) THEN
    ASM_SIMP_TAC [l4_vlift961;l4_vliftN961];
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961]]]);;

let l4_vctx_subst_eq_wf_ind969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==> l4_vctx_wf966 env uvars g`,
  MATCH_MP_TAC l4_vctx_subst_eq_INDUCT969 THEN
  REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN MESON_TAC []);;

let l4_vctx_subst_eq_wf969 = prove
 (`!env uvars g0 s s' g.
   l4_vctx_subst_eq969 env uvars g0 s s' g ==> l4_vctx_wf966 env uvars g`,
  ACCEPT_TAC l4_vctx_subst_eq_wf_ind969);;

let l4_vsubst_id_lift_r_skip969 = prove
 (`l4_vsubst_lift_r969 l4_vsubst_id969 (L4VLSkip969 L4VLRefl969) =
   l4_vsubst_tail969 l4_vsubst_id969`,
  REWRITE_TAC [FUN_EQ_THM;l4_vsubst_lift_r969;l4_vsubst_id969;l4_vsubst_tail969;
               l4_vlift_prime969;l4_vlift_op_lift_var_clauses969]);;

let l4_vctx_subst_eq_id969 = prove
 (`!g env uvars.
   l4_venv_closed966 env /\ l4_vctx_wf966 env uvars g ==>
   l4_vctx_subst_eq969 env uvars g l4_vsubst_id969 l4_vsubst_id969 g`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vctx_subst_eq_nil969];
   REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [REWRITE_TAC [GSYM l4_vsubst_id_lift_r_skip969] THEN
    MATCH_MP_TAC l4_vctx_subst_eq_skip969 THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vsubst_head969;l4_vsubst_id969;
                 GSYM l4_vsubst_id_lift_r_skip969;
                 GSYM l4_vlift_prime_vsubst969;l4_vsubst_id_eq969;
                 GSYM l4_vlift_eq_vlift_prime969] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961]]]);;
