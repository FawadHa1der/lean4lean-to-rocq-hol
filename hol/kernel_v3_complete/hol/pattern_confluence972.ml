(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of Lean4Lean/Theory/Typing/{Pattern,Injectivity,UniqueTyping,
   ChurchRosser,HeadReduction}.lean:
   1. Orthogonal higher-order patterns, match environments, pattern intersection,
      pattern RHS application, check preservation, and simple patterns.
   2. Parameterized Pi/Sort injectivity (l4_defeq_injectivity972) and
      uniqueness of typing modulo definitional equality (l4_vis_defeq_uniq_same972,
      l4_vis_defeq_u_trans972, l4_vhas_type_weakN_iff972, l4_vhas_type_weak_prime_iff972).
   3. Normal equivalence (l4_vnormal_eq972), typed parallel reduction (l4_vpar_red_t972),
      Takahashi complete development (l4_vcpar_red_t972), PatternParams, and
      typed Church-Rosser confluence (l4_vis_defeq_church_rosser972, closing both
      upstream .extra cases unconditionally).
   4. Weak head reduction determinism (l4_vwhred_determ972), Kashima
      standardization (l4_vpar_red_ts_standard972), and syntax-directed type
      inference (l4_vinfer_type972, l4_vinfer_type_determ972, l4_vinfer_type_exists972).
   5. Unconditional non-vacuity on l4_venv_empty961 / extra-free environments.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/level_sat968.ml";;
needs "hol/strong_typing970.ml";;

let l4_vhas_type_lam_inv970 = REWRITE_RULE [l4_vis_type961] l4_vhas_type_lam_inv970;;
let l4_subst_vars_tac972 = l4_subst_vars_tac966;;
let l4_vlookup_zero961 = CONJUNCT1 l4_vlookup_RULES961;;
let l4_vexpr_CASES961 = cases "l4_vexpr961";;

(* ========================================================================= *)
(* 1. Patterns & Orthogonal Matching (Lean4Lean/Theory/Typing/Pattern.lean)  *)
(* ========================================================================= *)

let l4_opt_bind972 = new_recursive_definition option_RECURSION
 `(l4_opt_bind972 NONE (f:A->B option) = NONE) /\
  (l4_opt_bind972 (SOME x) f = f x)`;;

let l4_opt_bind_eq_some972 = prove
 (`!m (f:A->B option) y.
   l4_opt_bind972 m f = SOME y <=> ?x. m = SOME x /\ f x = SOME y`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `m:A option` (cases "option")) THEN
  REWRITE_TAC [l4_opt_bind972;distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_vpattern_INDUCT972,l4_vpattern_RECURSION972 = define_type
 "l4_vpattern972 =
    L4VPConst972 l4_name
  | L4VPApp972 l4_vpattern972 l4_vpattern972
  | L4VPVar972 l4_vpattern972";;

let l4_vpattern_varN972 = new_recursive_definition num_RECURSION
 `(l4_vpattern_varN972 p 0 = p) /\
  (l4_vpattern_varN972 p (SUC n) = L4VPVar972 (l4_vpattern_varN972 p n))`;;

let l4_vpattern_size972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpattern_size972 (L4VPConst972 c) = 1) /\
  (l4_vpattern_size972 (L4VPApp972 f a) = 1 + l4_vpattern_size972 f + l4_vpattern_size972 a) /\
  (l4_vpattern_size972 (L4VPVar972 f) = 1 + l4_vpattern_size972 f)`;;

let l4_vexpr_size972 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vexpr_size972 (L4VBVar961 i) = 1) /\
  (l4_vexpr_size972 (L4VSort961 u) = 1) /\
  (l4_vexpr_size972 (L4VConst961 c ls) = 1) /\
  (l4_vexpr_size972 (L4VApp961 f a) = 1 + l4_vexpr_size972 f + l4_vexpr_size972 a) /\
  (l4_vexpr_size972 (L4VLam961 dom body) = 1 + l4_vexpr_size972 dom + l4_vexpr_size972 body) /\
  (l4_vexpr_size972 (L4VForallE961 dom cod) = 1 + l4_vexpr_size972 dom + l4_vexpr_size972 cod)`;;

let l4_vsubpattern_RULES972,l4_vsubpattern_INDUCT972,l4_vsubpattern_CASES972 =
  new_inductive_definition
 `(!p. l4_vsubpattern972 p p) /\
  (!p f a. l4_vsubpattern972 p f ==> l4_vsubpattern972 p (L4VPApp972 f a)) /\
  (!p f a. l4_vsubpattern972 p a ==> l4_vsubpattern972 p (L4VPApp972 f a)) /\
  (!p f. l4_vsubpattern972 p f ==> l4_vsubpattern972 p (L4VPVar972 f))`;;

let l4_vsubpattern_refl972,
    l4_vsubpattern_appL972,
    l4_vsubpattern_appR972,
    l4_vsubpattern_varL972 =
  match CONJUNCTS l4_vsubpattern_RULES972 with
  | [c1;c2;c3;c4] -> (c1,c2,c3,c4)
  | _ -> failwith "l4_vsubpattern_RULES972: unexpected arity";;

let l4_vsubpattern_varN972 = prove
 (`!p f n. l4_vsubpattern972 p f ==> l4_vsubpattern972 p (l4_vpattern_varN972 f n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [l4_vpattern_varN972] THEN DISCH_TAC THEN
  MATCH_MP_TAC l4_vsubpattern_varL972 THEN ASM_SIMP_TAC []);;

let l4_vsubpattern_trans_ind972 = prove
 (`!p2 p3. l4_vsubpattern972 p2 p3 ==> (!p1. l4_vsubpattern972 p1 p2 ==> l4_vsubpattern972 p1 p3)`,
  MATCH_MP_TAC l4_vsubpattern_INDUCT972 THEN
  MESON_TAC [l4_vsubpattern_appL972;l4_vsubpattern_appR972;l4_vsubpattern_varL972]);;

let l4_vsubpattern_trans972 = prove
 (`!p1 p2 p3. l4_vsubpattern972 p1 p2 /\ l4_vsubpattern972 p2 p3 ==> l4_vsubpattern972 p1 p3`,
  MESON_TAC [l4_vsubpattern_trans_ind972]);;

let l4_vsubpattern_size_le972 = prove
 (`!p1 p2. l4_vsubpattern972 p1 p2 ==> l4_vpattern_size972 p1 <= l4_vpattern_size972 p2`,
  MATCH_MP_TAC l4_vsubpattern_INDUCT972 THEN
  REWRITE_TAC [l4_vpattern_size972] THEN ARITH_TAC);;

let l4_vsubpattern_antisymm972 = prove
 (`!p1 p2. l4_vsubpattern972 p1 p2 /\ l4_vsubpattern972 p2 p1 ==> p2 = p1`,
  REPEAT STRIP_TAC THEN
  MP_TAC (MATCH_MP l4_vsubpattern_size_le972 (ASSUME `l4_vsubpattern972 p1 p2`)) THEN
  UNDISCH_TAC `l4_vsubpattern972 p2 p1` THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vsubpattern_CASES972] THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP l4_vsubpattern_size_le972) THEN
  ASM_REWRITE_TAC [l4_vpattern_size972] THEN ARITH_TAC);;

let l4_vsubpattern_varN_const_ind972 = prove
 (`!p p'. l4_vsubpattern972 p p' ==>
   (!c n. p' = l4_vpattern_varN972 (L4VPConst972 c) n ==>
          ?m. p = l4_vpattern_varN972 (L4VPConst972 c) m)`,
  MATCH_MP_TAC l4_vsubpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `c:l4_name` THEN
   INDUCT_TAC THEN REWRITE_TAC [l4_vpattern_varN972;distinctness "l4_vpattern972"];
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `c:l4_name` THEN
   INDUCT_TAC THEN REWRITE_TAC [l4_vpattern_varN972;distinctness "l4_vpattern972"];
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `c:l4_name` THEN
   INDUCT_TAC THEN REWRITE_TAC [l4_vpattern_varN972;distinctness "l4_vpattern972";
                                injectivity "l4_vpattern972"] THEN
   ASM_MESON_TAC []]);;

let l4_vsubpattern_varN_const972 = prove
 (`!p c n.
   l4_vsubpattern972 p (l4_vpattern_varN972 (L4VPConst972 c) n) ==>
   ?m. p = l4_vpattern_varN972 (L4VPConst972 c) m`,
  MESON_TAC [l4_vsubpattern_varN_const_ind972]);;

let l4_vpattern_inter_const972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpattern_inter_const972 c (L4VPConst972 c') =
     if c = c' then SOME (L4VPConst972 c) else NONE) /\
  (l4_vpattern_inter_const972 c (L4VPApp972 f' a') = NONE) /\
  (l4_vpattern_inter_const972 c (L4VPVar972 f') = NONE)`;;

let l4_vpattern_inter_app972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpattern_inter_app972 (recf:l4_vpattern972->l4_vpattern972 option)
     (reca:l4_vpattern972->l4_vpattern972 option) a (L4VPConst972 c') = NONE) /\
  (l4_vpattern_inter_app972 recf reca a (L4VPApp972 f' a') =
     l4_opt_bind972 (recf f') (\fi.
       l4_opt_bind972 (reca a') (\ai. SOME (L4VPApp972 fi ai)))) /\
  (l4_vpattern_inter_app972 recf reca a (L4VPVar972 f') =
     l4_opt_bind972 (recf f') (\fi. SOME (L4VPApp972 fi a)))`;;

let l4_vpattern_inter_var972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpattern_inter_var972 (recf:l4_vpattern972->l4_vpattern972 option) (L4VPConst972 c') = NONE) /\
  (l4_vpattern_inter_var972 recf (L4VPApp972 f' a') =
     l4_opt_bind972 (recf f') (\fi. SOME (L4VPApp972 fi a'))) /\
  (l4_vpattern_inter_var972 recf (L4VPVar972 f') =
     l4_opt_bind972 (recf f') (\fi. SOME (L4VPVar972 fi)))`;;

let l4_vpattern_inter972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpattern_inter972 (L4VPConst972 c) q = l4_vpattern_inter_const972 c q) /\
  (l4_vpattern_inter972 (L4VPApp972 f a) q =
     l4_vpattern_inter_app972 (l4_vpattern_inter972 f) (l4_vpattern_inter972 a) a q) /\
  (l4_vpattern_inter972 (L4VPVar972 f) q =
     l4_vpattern_inter_var972 (l4_vpattern_inter972 f) q)`;;

let l4_vpattern_inter_clauses972 = prove
 (`(!c c'. l4_vpattern_inter972 (L4VPConst972 c) (L4VPConst972 c') =
           if c = c' then SOME (L4VPConst972 c) else NONE) /\
   (!c f' a'. l4_vpattern_inter972 (L4VPConst972 c) (L4VPApp972 f' a') = NONE) /\
   (!c f'. l4_vpattern_inter972 (L4VPConst972 c) (L4VPVar972 f') = NONE) /\
   (!f a c'. l4_vpattern_inter972 (L4VPApp972 f a) (L4VPConst972 c') = NONE) /\
   (!f a f' a'. l4_vpattern_inter972 (L4VPApp972 f a) (L4VPApp972 f' a') =
           l4_opt_bind972 (l4_vpattern_inter972 f f') (\fi.
             l4_opt_bind972 (l4_vpattern_inter972 a a') (\ai. SOME (L4VPApp972 fi ai)))) /\
   (!f a f'. l4_vpattern_inter972 (L4VPApp972 f a) (L4VPVar972 f') =
           l4_opt_bind972 (l4_vpattern_inter972 f f') (\fi. SOME (L4VPApp972 fi a))) /\
   (!f c'. l4_vpattern_inter972 (L4VPVar972 f) (L4VPConst972 c') = NONE) /\
   (!f f' a'. l4_vpattern_inter972 (L4VPVar972 f) (L4VPApp972 f' a') =
           l4_opt_bind972 (l4_vpattern_inter972 f f') (\fi. SOME (L4VPApp972 fi a'))) /\
   (!f f'. l4_vpattern_inter972 (L4VPVar972 f) (L4VPVar972 f') =
           l4_opt_bind972 (l4_vpattern_inter972 f f') (\fi. SOME (L4VPVar972 fi)))`,
  REWRITE_TAC [l4_vpattern_inter972;l4_vpattern_inter_const972;
               l4_vpattern_inter_app972;l4_vpattern_inter_var972]);;

let l4_vpattern_inter_self972 = prove
 (`!p. l4_vpattern_inter972 p p = SOME p`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN
  SIMP_TAC [l4_vpattern_inter_clauses972;l4_opt_bind972]);;

(* Paths (bool list) and Match Environments (bool list -> l4_vexpr961) *)

let l4_vpath_valid_app972 = new_recursive_definition list_RECURSION
 `(l4_vpath_valid_app972 (pf:bool list->bool) (pa:bool list->bool) [] = F) /\
  (l4_vpath_valid_app972 pf pa (CONS h xs) = if h then pa xs else pf xs)`;;

let l4_vpath_valid_var972 = new_recursive_definition list_RECURSION
 `(l4_vpath_valid_var972 (pf:bool list->bool) [] = T) /\
  (l4_vpath_valid_var972 pf (CONS h xs) = if h then F else pf xs)`;;

let l4_vpath_valid972 = new_recursive_definition l4_vpattern_RECURSION972
 `(l4_vpath_valid972 (L4VPConst972 c) x = F) /\
  (l4_vpath_valid972 (L4VPApp972 f a) x =
     l4_vpath_valid_app972 (l4_vpath_valid972 f) (l4_vpath_valid972 a) x) /\
  (l4_vpath_valid972 (L4VPVar972 f) x =
     l4_vpath_valid_var972 (l4_vpath_valid972 f) x)`;;

let l4_vpath_valid_clauses972 = prove
 (`(!c x. l4_vpath_valid972 (L4VPConst972 c) x <=> F) /\
   (!f a. l4_vpath_valid972 (L4VPApp972 f a) [] <=> F) /\
   (!f a xs. l4_vpath_valid972 (L4VPApp972 f a) (CONS F xs) <=> l4_vpath_valid972 f xs) /\
   (!f a xs. l4_vpath_valid972 (L4VPApp972 f a) (CONS T xs) <=> l4_vpath_valid972 a xs) /\
   (!f. l4_vpath_valid972 (L4VPVar972 f) [] <=> T) /\
   (!f xs. l4_vpath_valid972 (L4VPVar972 f) (CONS F xs) <=> l4_vpath_valid972 f xs) /\
   (!f xs. l4_vpath_valid972 (L4VPVar972 f) (CONS T xs) <=> F)`,
  REWRITE_TAC [l4_vpath_valid972;l4_vpath_valid_app972;l4_vpath_valid_var972]);;

let l4_vmenv_empty972 = new_definition
 `l4_vmenv_empty972 (x:bool list) = L4VBVar961 0`;;

let l4_vmenv_var972 = new_recursive_definition list_RECURSION
 `(l4_vmenv_var972 (a:l4_vexpr961) (mf:bool list->l4_vexpr961) [] = a) /\
  (l4_vmenv_var972 a mf (CONS h xs) = if h then L4VBVar961 0 else mf xs)`;;

let l4_vmenv_app972 = new_recursive_definition list_RECURSION
 `(l4_vmenv_app972 (mf:bool list->l4_vexpr961) (ma:bool list->l4_vexpr961) [] = L4VBVar961 0) /\
  (l4_vmenv_app972 mf ma (CONS h xs) = if h then ma xs else mf xs)`;;

let l4_vmenv_clauses972 = prove
 (`(!x. l4_vmenv_empty972 x = L4VBVar961 0) /\
   (!a mf. l4_vmenv_var972 a mf [] = a) /\
   (!a mf xs. l4_vmenv_var972 a mf (CONS F xs) = mf xs) /\
   (!a mf xs. l4_vmenv_var972 a mf (CONS T xs) = L4VBVar961 0) /\
   (!mf ma. l4_vmenv_app972 mf ma [] = L4VBVar961 0) /\
   (!mf ma xs. l4_vmenv_app972 mf ma (CONS F xs) = mf xs) /\
   (!mf ma xs. l4_vmenv_app972 mf ma (CONS T xs) = ma xs)`,
  REWRITE_TAC [l4_vmenv_empty972;l4_vmenv_var972;l4_vmenv_app972]);;

let l4_vmenv_wf972 = new_definition
 `l4_vmenv_wf972 p (m:bool list->l4_vexpr961) <=>
   !x. ~l4_vpath_valid972 p x ==> m x = L4VBVar961 0`;;

let l4_vmenv_wf_empty972 = prove
 (`!c. l4_vmenv_wf972 (L4VPConst972 c) l4_vmenv_empty972`,
  REWRITE_TAC [l4_vmenv_wf972;l4_vmenv_clauses972]);;

let l4_vmenv_wf_app972 = prove
 (`!f a mf ma.
   l4_vmenv_wf972 f mf /\ l4_vmenv_wf972 a ma ==>
   l4_vmenv_wf972 (L4VPApp972 f a) (l4_vmenv_app972 mf ma)`,
  REWRITE_TAC [l4_vmenv_wf972] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:bool list` THEN
  STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
  REWRITE_TAC [l4_vmenv_clauses972] THEN
  STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
  ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]);;

let l4_vmenv_wf_var972 = prove
 (`!f a mf.
   l4_vmenv_wf972 f mf ==>
   l4_vmenv_wf972 (L4VPVar972 f) (l4_vmenv_var972 a mf)`,
  REWRITE_TAC [l4_vmenv_wf972] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `x:bool list` THEN
  STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
  REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
  STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
  ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]);;

let l4_vmenv_map972 = new_definition
 `l4_vmenv_map972 (g:l4_vexpr961->l4_vexpr961) (p:l4_vpattern972)
    (m:bool list->l4_vexpr961) (x:bool list) =
   if l4_vpath_valid972 p x then g (m x) else L4VBVar961 0`;;

let l4_vmenv_map_valid972 = prove
 (`!g p m x. l4_vpath_valid972 p x ==> l4_vmenv_map972 g p m x = g (m x)`,
  SIMP_TAC [l4_vmenv_map972]);;

let l4_vmenv_map_const972 = prove
 (`!g c m. l4_vmenv_map972 g (L4VPConst972 c) m = l4_vmenv_empty972`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM;l4_vmenv_map972;
                                   l4_vpath_valid_clauses972;l4_vmenv_clauses972]);;

let l4_vmenv_map_app972 = prove
 (`!g f a mf ma.
   l4_vmenv_map972 g (L4VPApp972 f a) (l4_vmenv_app972 mf ma) =
   l4_vmenv_app972 (l4_vmenv_map972 g f mf) (l4_vmenv_map972 g a ma)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC `x:bool list` THEN
  STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
  REWRITE_TAC [l4_vmenv_map972;l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
  STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
  REWRITE_TAC [l4_vmenv_map972;l4_vpath_valid_clauses972;l4_vmenv_clauses972]);;

let l4_vmenv_map_var972 = prove
 (`!g f a mf.
   l4_vmenv_map972 g (L4VPVar972 f) (l4_vmenv_var972 a mf) =
   l4_vmenv_var972 (g a) (l4_vmenv_map972 g f mf)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC `x:bool list` THEN
  STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
  REWRITE_TAC [l4_vmenv_map972;l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
  STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
  REWRITE_TAC [l4_vmenv_map972;l4_vpath_valid_clauses972;l4_vmenv_clauses972]);;

let l4_vmenv_rel_choice972 = prove
 (`!p (R:bool list->l4_vexpr961->bool).
   (!x. l4_vpath_valid972 p x ==> ?y. R x y) ==>
   ?m. l4_vmenv_wf972 p m /\ (!x. l4_vpath_valid972 p x ==> R x (m x))`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN EXISTS_TAC `l4_vmenv_empty972` THEN
   REWRITE_TAC [l4_vmenv_wf_empty972;l4_vpath_valid_clauses972];
   MAP_EVERY X_GEN_TAC [`f:l4_vpattern972`;`a:l4_vpattern972`] THEN
   STRIP_TAC THEN X_GEN_TAC `R:bool list->l4_vexpr961->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?mf. l4_vmenv_wf972 f mf /\ (!x. l4_vpath_valid972 f x ==> R (CONS F x) (mf x))`
     (X_CHOOSE_THEN `mf:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM (fun th ->
      MATCH_MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPEC `\x:bool list. (R:bool list->l4_vexpr961->bool) (CONS F x)` th))) THEN
    X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC `CONS F x`) THEN
    ASM_SIMP_TAC [l4_vpath_valid_clauses972]; ALL_TAC] THEN
   SUBGOAL_THEN `?ma. l4_vmenv_wf972 a ma /\ (!x. l4_vpath_valid972 a x ==> R (CONS T x) (ma x))`
     (X_CHOOSE_THEN `ma:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM (fun th ->
      MATCH_MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPEC `\x:bool list. (R:bool list->l4_vexpr961->bool) (CONS T x)` th))) THEN
    X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC `CONS T x`) THEN
    ASM_SIMP_TAC [l4_vpath_valid_clauses972]; ALL_TAC] THEN
   EXISTS_TAC `l4_vmenv_app972 mf ma` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [l4_vmenv_wf_app972];
    X_GEN_TAC `x:bool list` THEN
    STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
    REWRITE_TAC [l4_vpath_valid_clauses972] THEN
    STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
    ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]];
   X_GEN_TAC `f:l4_vpattern972` THEN DISCH_TAC THEN
   X_GEN_TAC `R:bool list->l4_vexpr961->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?y0:l4_vexpr961. R ([]:bool list) y0` (X_CHOOSE_TAC `y0:l4_vexpr961`) THENL
   [FIRST_ASSUM (MP_TAC o SPEC `[]:bool list`) THEN
    SIMP_TAC [l4_vpath_valid_clauses972]; ALL_TAC] THEN
   SUBGOAL_THEN `?mf. l4_vmenv_wf972 f mf /\ (!x. l4_vpath_valid972 f x ==> R (CONS F x) (mf x))`
     (X_CHOOSE_THEN `mf:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM (fun th ->
      MATCH_MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPEC `\x:bool list. (R:bool list->l4_vexpr961->bool) (CONS F x)` th))) THEN
    X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC `CONS F x`) THEN
    ASM_SIMP_TAC [l4_vpath_valid_clauses972]; ALL_TAC] THEN
   EXISTS_TAC `l4_vmenv_var972 y0 mf` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [l4_vmenv_wf_var972];
    X_GEN_TAC `x:bool list` THEN
    STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
    REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
    ASM_REWRITE_TAC [] THEN
    STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
    ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]]]);;

(* Inductive Pattern Matching *)

let l4_vpattern_matches_RULES972,
    l4_vpattern_matches_INDUCT972,
    l4_vpattern_matches_CASES972 =
  new_inductive_definition
 `(!c ls.
     l4_vpattern_matches972 (L4VPConst972 c) (L4VConst961 c ls) ls l4_vmenv_empty972) /\
  (!f f' a' ls mf.
     l4_vpattern_matches972 f f' ls mf ==>
     l4_vpattern_matches972 (L4VPVar972 f) (L4VApp961 f' a') ls (l4_vmenv_var972 a' mf)) /\
  (!f a f' a' ls1 ls2 mf ma.
     l4_vpattern_matches972 f f' ls1 mf /\
     l4_vpattern_matches972 a a' ls2 ma ==>
     l4_vpattern_matches972 (L4VPApp972 f a) (L4VApp961 f' a') ls1 (l4_vmenv_app972 mf ma))`;;

let l4_vpm_const972, l4_vpm_var972, l4_vpm_app972 =
  match CONJUNCTS l4_vpattern_matches_RULES972 with
  | [c1;c2;c3] -> (c1,c2,c3)
  | _ -> failwith "l4_vpattern_matches_RULES972: unexpected arity";;

let l4_vpattern_matches_const_inv972 = prove
 (`!c e m1 m2.
   l4_vpattern_matches972 (L4VPConst972 c) e m1 m2 <=>
   e = L4VConst961 c m1 /\ m2 = l4_vmenv_empty972`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
  MESON_TAC []);;

let l4_vpattern_matches_var_inv972 = prove
 (`!pf e m1 m2.
   l4_vpattern_matches972 (L4VPVar972 pf) e m1 m2 <=>
   ?f' a' mf.
     e = L4VApp961 f' a' /\
     m2 = l4_vmenv_var972 a' mf /\
     l4_vpattern_matches972 pf f' m1 mf`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
  MESON_TAC []);;

let l4_vpattern_matches_app_inv972 = prove
 (`!pf pa e m1 m2.
   l4_vpattern_matches972 (L4VPApp972 pf pa) e m1 m2 <=>
   ?f' a' ls2 mf ma.
     e = L4VApp961 f' a' /\
     m2 = l4_vmenv_app972 mf ma /\
     l4_vpattern_matches972 pf f' m1 mf /\
     l4_vpattern_matches972 pa a' ls2 ma`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
  MESON_TAC []);;

let l4_vpattern_matches_not_bvar972 = prove
 (`!p i m1 m2. ~l4_vpattern_matches972 p (L4VBVar961 i) m1 m2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"]);;

let l4_vpattern_matches_not_sort972 = prove
 (`!p u m1 m2. ~l4_vpattern_matches972 p (L4VSort961 u) m1 m2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"]);;

let l4_vpattern_matches_not_lam972 = prove
 (`!p dom body m1 m2. ~l4_vpattern_matches972 p (L4VLam961 dom body) m1 m2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"]);;

let l4_vpattern_matches_not_forallE972 = prove
 (`!p dom cod m1 m2. ~l4_vpattern_matches972 p (L4VForallE961 dom cod) m1 m2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [l4_vpattern_matches_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"]);;

let l4_vpattern_matches_not_app_lam972 = prove
 (`!p dom e1 e2 m1 m2.
   ~l4_vpattern_matches972 p (L4VApp961 (L4VLam961 dom e1) e2) m1 m2`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
  REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
               l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
               injectivity "l4_vexpr961"] THEN
  MESON_TAC [l4_vpattern_matches_not_lam972]);;

let l4_vpattern_matches_uniq_ind972 = prove
 (`!p e m1 m2.
   l4_vpattern_matches972 p e m1 m2 ==>
   (!m1' m2'. l4_vpattern_matches972 p e m1' m2' ==> m1 = m1' /\ m2 = m2')`,
  MATCH_MP_TAC l4_vpattern_matches_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vpattern_matches_const_inv972;injectivity "l4_vexpr961"] THEN MESON_TAC [];
   REWRITE_TAC [l4_vpattern_matches_var_inv972;injectivity "l4_vexpr961"] THEN MESON_TAC [];
   REWRITE_TAC [l4_vpattern_matches_app_inv972;injectivity "l4_vexpr961"] THEN MESON_TAC []]);;

let l4_vpattern_matches_uniq972 = prove
 (`!p e m1 m2 m1' m2'.
   l4_vpattern_matches972 p e m1 m2 /\ l4_vpattern_matches972 p e m1' m2' ==>
   m1 = m1' /\ m2 = m2'`,
  MESON_TAC [l4_vpattern_matches_uniq_ind972]);;

let l4_vpattern_matches_path_size_ind972 = prove
 (`!p e m1 m2.
   l4_vpattern_matches972 p e m1 m2 ==>
   (!x. l4_vpath_valid972 p x ==> l4_vexpr_size972 (m2 x) < l4_vexpr_size972 e)`,
  MATCH_MP_TAC l4_vpattern_matches_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vpath_valid_clauses972];
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:bool list` THEN
   STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972;l4_vexpr_size972] THEN
   TRY ARITH_TAC THEN
   STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
   DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `t:bool list`) THEN
   ASM_REWRITE_TAC [] THEN ARITH_TAC;
   MAP_EVERY X_GEN_TAC [`f:l4_vpattern972`;`a:l4_vpattern972`;`f':l4_vexpr961`;`a':l4_vexpr961`;
                        `ls1:l4_vlevel961 list`;`ls2:l4_vlevel961 list`;
                        `mf:bool list->l4_vexpr961`;`ma:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN X_GEN_TAC `x:bool list` THEN
   STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972;l4_vexpr_size972] THEN
   STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN DISCH_TAC THENL
   [FIRST_ASSUM (fun th ->
      MP_TAC (MATCH_MP (SPEC `t:bool list` th) (ASSUME `l4_vpath_valid972 a t`))) THEN
    ARITH_TAC;
    FIRST_ASSUM (fun th ->
      MP_TAC (MATCH_MP (SPEC `t:bool list` th) (ASSUME `l4_vpath_valid972 f t`))) THEN
    ARITH_TAC]]);;

let l4_vpattern_matches_path_size972 = prove
 (`!p e m1 m2 a.
   l4_vpattern_matches972 p e m1 m2 /\ l4_vpath_valid972 p a ==>
   l4_vexpr_size972 (m2 a) < l4_vexpr_size972 e`,
  MESON_TAC [l4_vpattern_matches_path_size_ind972]);;

(* Pattern RHS & Check *)

let l4_vrhs_INDUCT972,l4_vrhs_RECURSION972 = define_type
 "l4_vrhs972 =
    L4VRHSFixed972 l4_vexpr961
  | L4VRHSApp972 l4_vrhs972 l4_vrhs972
  | L4VRHSVar972 (bool list)";;

let l4_vrhs_wf972 = new_recursive_definition l4_vrhs_RECURSION972
 `(l4_vrhs_wf972 p (L4VRHSFixed972 c) <=> l4_vclosedN961 c 0) /\
  (l4_vrhs_wf972 p (L4VRHSApp972 f a) <=> l4_vrhs_wf972 p f /\ l4_vrhs_wf972 p a) /\
  (l4_vrhs_wf972 p (L4VRHSVar972 path) <=> l4_vpath_valid972 p path)`;;

let l4_vrhs_apply972 = new_recursive_definition l4_vrhs_RECURSION972
 `(l4_vrhs_apply972 m1 m2 (L4VRHSFixed972 c) = l4_vinstL961 m1 c) /\
  (l4_vrhs_apply972 m1 m2 (L4VRHSApp972 f a) =
     L4VApp961 (l4_vrhs_apply972 m1 m2 f) (l4_vrhs_apply972 m1 m2 a)) /\
  (l4_vrhs_apply972 m1 m2 (L4VRHSVar972 path) = m2 path)`;;

let l4_vpattern_check_INDUCT972,l4_vpattern_check_RECURSION972 = define_type
 "l4_vpattern_check972 =
    L4VCheckTrue972
  | L4VCheckDefEq972 l4_vrhs972 l4_vrhs972 l4_vpattern_check972";;

let l4_vcheck_wf972 = new_recursive_definition l4_vpattern_check_RECURSION972
 `(l4_vcheck_wf972 p L4VCheckTrue972 <=> T) /\
  (l4_vcheck_wf972 p (L4VCheckDefEq972 a b rest) <=>
     l4_vrhs_wf972 p a /\ l4_vrhs_wf972 p b /\ l4_vcheck_wf972 p rest)`;;

let l4_vpattern_check_ok972 = new_recursive_definition l4_vpattern_check_RECURSION972
 `(l4_vpattern_check_ok972 (df:l4_vexpr961->l4_vexpr961->bool) m1 m2 L4VCheckTrue972 <=> T) /\
  (l4_vpattern_check_ok972 df m1 m2 (L4VCheckDefEq972 a b rest) <=>
     df (l4_vrhs_apply972 m1 m2 a) (l4_vrhs_apply972 m1 m2 b) /\
     l4_vpattern_check_ok972 df m1 m2 rest)`;;

let l4_vpattern_check_ok_map_ind972 = prove
 (`!ck p df df' m1 m2 m1' m2'.
   l4_vcheck_wf972 p ck /\
   l4_vpattern_check_ok972 df m1 m2 ck /\
   (!ra rb. l4_vrhs_wf972 p ra /\ l4_vrhs_wf972 p rb /\
            df (l4_vrhs_apply972 m1 m2 ra) (l4_vrhs_apply972 m1 m2 rb) ==>
            df' (l4_vrhs_apply972 m1' m2' ra) (l4_vrhs_apply972 m1' m2' rb)) ==>
   l4_vpattern_check_ok972 df' m1' m2' ck`,
  MATCH_MP_TAC l4_vpattern_check_INDUCT972 THEN
  REWRITE_TAC [l4_vcheck_wf972;l4_vpattern_check_ok972] THEN MESON_TAC []);;

let l4_vpattern_check_ok_map972 = prove
 (`!p df df' ck m1 m2 m1' m2'.
   l4_vcheck_wf972 p ck /\
   l4_vpattern_check_ok972 df m1 m2 ck /\
   (!ra rb. l4_vrhs_wf972 p ra /\ l4_vrhs_wf972 p rb /\
            df (l4_vrhs_apply972 m1 m2 ra) (l4_vrhs_apply972 m1 m2 rb) ==>
            df' (l4_vrhs_apply972 m1' m2' ra) (l4_vrhs_apply972 m1' m2' rb)) ==>
   l4_vpattern_check_ok972 df' m1' m2' ck`,
  MESON_TAC [l4_vpattern_check_ok_map_ind972]);;

let l4_vrhs_apply_ext_ind972 = prove
 (`!r p m1 m2 m2'.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==> m2 a = m2' a) ==>
   l4_vrhs_apply972 m1 m2 r = l4_vrhs_apply972 m1 m2' r`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972] THEN MESON_TAC []);;

let l4_vrhs_apply_ext972 = prove
 (`!p r m1 m2 m2'.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==> m2 a = m2' a) ==>
   l4_vrhs_apply972 m1 m2 r = l4_vrhs_apply972 m1 m2' r`,
  MESON_TAC [l4_vrhs_apply_ext_ind972]);;

let l4_vrhs_apply_vlift_prime_ind972 = prove
 (`!r p m1 m2 rho.
   l4_vrhs_wf972 p r ==>
   l4_vlift_prime969 (l4_vrhs_apply972 m1 m2 r) rho =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2) r`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972;l4_vlift_prime969] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vclosed_n_vlift_prime_eq969 THEN
   EXISTS_TAC `0` THEN REWRITE_TAC [l4_vlift_op_fixes_clauses969] THEN
   ASM_REWRITE_TAC [l4_vinstL_preserves_vclosedN966];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vmenv_map_valid972]]);;

let l4_vrhs_apply_vlift_prime972 = prove
 (`!p m1 m2 r rho.
   l4_vrhs_wf972 p r ==>
   l4_vlift_prime969 (l4_vrhs_apply972 m1 m2 r) rho =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2) r`,
  MESON_TAC [l4_vrhs_apply_vlift_prime_ind972]);;

let l4_vrhs_apply_vliftN_ind972 = prove
 (`!r p m1 m2 n k.
   l4_vrhs_wf972 p r ==>
   l4_vliftN961 (l4_vrhs_apply972 m1 m2 r) n k =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vliftN961 x n k) p m2) r`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972;l4_vliftN961] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vclosedN_vliftN_eq966 THEN
   MATCH_MP_TAC l4_vclosedN_mono966 THEN EXISTS_TAC `0` THEN REWRITE_TAC [LE_0] THEN
   ASM_REWRITE_TAC [l4_vinstL_preserves_vclosedN966];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vmenv_map_valid972]]);;

let l4_vrhs_apply_vliftN972 = prove
 (`!p m1 m2 r n k.
   l4_vrhs_wf972 p r ==>
   l4_vliftN961 (l4_vrhs_apply972 m1 m2 r) n k =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vliftN961 x n k) p m2) r`,
  MESON_TAC [l4_vrhs_apply_vliftN_ind972]);;

let l4_vrhs_apply_vinst_ind972 = prove
 (`!r p m1 m2 e0 k.
   l4_vrhs_wf972 p r ==>
   l4_vinst961 (l4_vrhs_apply972 m1 m2 r) e0 k =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vinst961 x e0 k) p m2) r`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972;l4_vinst961] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vclosedN_vinst_eq966 THEN
   MATCH_MP_TAC l4_vclosedN_mono966 THEN EXISTS_TAC `0` THEN REWRITE_TAC [LE_0] THEN
   ASM_REWRITE_TAC [l4_vinstL_preserves_vclosedN966];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vmenv_map_valid972]]);;

let l4_vrhs_apply_vinst972 = prove
 (`!p m1 m2 r e0 k.
   l4_vrhs_wf972 p r ==>
   l4_vinst961 (l4_vrhs_apply972 m1 m2 r) e0 k =
   l4_vrhs_apply972 m1 (l4_vmenv_map972 (\x. l4_vinst961 x e0 k) p m2) r`,
  MESON_TAC [l4_vrhs_apply_vinst_ind972]);;

let l4_vpattern_matches_vlift_prime_fwd_ind972 = prove
 (`!p e m1 m2.
   l4_vpattern_matches972 p e m1 m2 ==>
   (!rho. l4_vpattern_matches972 p (l4_vlift_prime969 e rho) m1
            (l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2))`,
  MATCH_MP_TAC l4_vpattern_matches_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vlift_prime969;l4_vmenv_map_const972;l4_vpm_const972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969;l4_vmenv_map_var972] THEN
   MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969;l4_vmenv_map_app972] THEN
   MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC []]);;

let l4_vpattern_matches_vlift_prime_bwd_ind972 = prove
 (`!p rho e m1 m2'.
   l4_vpattern_matches972 p (l4_vlift_prime969 e rho) m1 m2' ==>
   ?m2. l4_vpattern_matches972 p e m1 m2 /\
        m2' = l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [X_GEN_TAC `c:l4_name` THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vlift_prime969;l4_vpattern_matches_const_inv972;
                distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   EXISTS_TAC `l4_vmenv_empty972` THEN
   REWRITE_TAC [l4_vpm_const972;l4_vmenv_map_const972];
   MAP_EVERY X_GEN_TAC [`pf:l4_vpattern972`;`pa:l4_vpattern972`] THEN
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vlift_prime969] THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE
     [l4_vpattern_matches_app_inv972; distinctness "l4_vexpr961"; injectivity "l4_vexpr961"]) THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `(?mf0. l4_vpattern_matches972 pf a0 m1 mf0 /\
                        mf = l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) pf mf0) /\
                 (?ma0. l4_vpattern_matches972 pa a1 ls2 ma0 /\
                        ma = l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) pa ma0)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [];
    EXISTS_TAC `l4_vmenv_app972 mf0 ma0` THEN
    ASM_REWRITE_TAC [l4_vmenv_map_app972] THEN
    MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC []];
   X_GEN_TAC `pf:l4_vpattern972` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vlift_prime969] THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE
     [l4_vpattern_matches_var_inv972; distinctness "l4_vexpr961"; injectivity "l4_vexpr961"]) THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?mf0. l4_vpattern_matches972 pf a0 m1 mf0 /\
                       mf = l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) pf mf0`
     (X_CHOOSE_THEN `mf0:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [];
    EXISTS_TAC `l4_vmenv_var972 a1 mf0` THEN
    ASM_REWRITE_TAC [l4_vmenv_map_var972] THEN
    MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC []]]);;

let l4_vpattern_matches_vlift_prime972 = prove
 (`!p rho e m1 m2'.
   l4_vpattern_matches972 p (l4_vlift_prime969 e rho) m1 m2' <=>
   ?m2. l4_vpattern_matches972 p e m1 m2 /\
        m2' = l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2`,
  MESON_TAC [l4_vpattern_matches_vlift_prime_fwd_ind972;
             l4_vpattern_matches_vlift_prime_bwd_ind972]);;

let l4_vpattern_matches_vliftN972 = prove
 (`!p n k e m1 m2'.
   l4_vpattern_matches972 p (l4_vliftN961 e n k) m1 m2' <=>
   ?m2. l4_vpattern_matches972 p e m1 m2 /\
        m2' = l4_vmenv_map972 (\x. l4_vliftN961 x n k) p m2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969] THEN
  REWRITE_TAC [l4_vpattern_matches_vlift_prime972] THEN
  SUBGOAL_THEN `(\x. l4_vlift_prime969 x (l4_vlift_op_cons_n969 (l4_vlift_op_skip_n969 L4VLRefl969 n) k)) =
                (\x. l4_vliftN961 x n k)` SUBST1_TAC THENL
  [REWRITE_TAC [FUN_EQ_THM;l4_vlift_prime_cons_n_skip_n969]; REFL_TAC]);;

let l4_vpattern_matches_vinst_ind972 = prove
 (`!p e m1 m2.
   l4_vpattern_matches972 p e m1 m2 ==>
   (!e0 k. l4_vpattern_matches972 p (l4_vinst961 e e0 k) m1
             (l4_vmenv_map972 (\x. l4_vinst961 x e0 k) p m2))`,
  MATCH_MP_TAC l4_vpattern_matches_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vinst961;l4_vmenv_map_const972;l4_vpm_const972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vmenv_map_var972] THEN
   MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vmenv_map_app972] THEN
   MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC []]);;

let l4_vpattern_matches_vinst972 = prove
 (`!p e m1 m2 e0 k.
   l4_vpattern_matches972 p e m1 m2 ==>
   l4_vpattern_matches972 p (l4_vinst961 e e0 k) m1
     (l4_vmenv_map972 (\x. l4_vinst961 x e0 k) p m2)`,
  MESON_TAC [l4_vpattern_matches_vinst_ind972]);;

let l4_vpattern_matches_inter_fwd972 = prove
 (`!p q e.
   (?m1 m2. l4_vpattern_matches972 p e m1 m2) /\
   (?m1 m2. l4_vpattern_matches972 q e m1 m2) ==>
   ?r m1 m2. l4_vpattern_inter972 p q = SOME r /\ l4_vpattern_matches972 r e m1 m2`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [X_GEN_TAC `c:l4_name` THEN X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_app_inv972;
                l4_vpattern_matches_var_inv972;l4_vpattern_inter_clauses972] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [distinctness "l4_vexpr961";injectivity "l4_vexpr961"]) THEN
   ASM_MESON_TAC [l4_vpm_const972];
   MAP_EVERY X_GEN_TAC [`pf:l4_vpattern972`;`pa:l4_vpattern972`] THEN
   STRIP_TAC THEN X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_app_inv972;
                l4_vpattern_matches_var_inv972;l4_vpattern_inter_clauses972] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [distinctness "l4_vexpr961";injectivity "l4_vexpr961"]) THEN
   REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN l4_subst_vars_tac972 THEN
   TRY (FIRST_ASSUM CONTR_TAC) THENL
   [SUBGOAL_THEN `(?rf mrf1 mrf2. l4_vpattern_inter972 pf a0 = SOME rf /\
                                  l4_vpattern_matches972 rf f' mrf1 mrf2) /\
                  (?ra mra1 mra2. l4_vpattern_inter972 pa a1 = SOME ra /\
                                  l4_vpattern_matches972 ra a' mra1 mra2)`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [];
     MAP_EVERY EXISTS_TAC [`L4VPApp972 rf ra`;`mrf1:l4_vlevel961 list`;
                           `l4_vmenv_app972 mrf2 mra2`] THEN
     ASM_REWRITE_TAC [l4_opt_bind972] THEN
     MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `mra1:l4_vlevel961 list` THEN ASM_REWRITE_TAC []];
    SUBGOAL_THEN `?rf mrf1 mrf2. l4_vpattern_inter972 pf a = SOME rf /\
                                 l4_vpattern_matches972 rf f' mrf1 mrf2`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [];
     MAP_EVERY EXISTS_TAC [`L4VPApp972 rf pa`;`mrf1:l4_vlevel961 list`;
                           `l4_vmenv_app972 mrf2 ma`] THEN
     ASM_REWRITE_TAC [l4_opt_bind972] THEN
     MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC []]];
   X_GEN_TAC `pf:l4_vpattern972` THEN DISCH_TAC THEN
   X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_app_inv972;
                l4_vpattern_matches_var_inv972;l4_vpattern_inter_clauses972] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [distinctness "l4_vexpr961";injectivity "l4_vexpr961"]) THEN
   REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN l4_subst_vars_tac972 THEN
   TRY (FIRST_ASSUM CONTR_TAC) THENL
   [SUBGOAL_THEN `?rf mrf1 mrf2. l4_vpattern_inter972 pf a0 = SOME rf /\
                                 l4_vpattern_matches972 rf f' mrf1 mrf2`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [];
     MAP_EVERY EXISTS_TAC [`L4VPApp972 rf a1`;`mrf1:l4_vlevel961 list`;
                           `l4_vmenv_app972 mrf2 ma`] THEN
     ASM_REWRITE_TAC [l4_opt_bind972] THEN
     MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC []];
    SUBGOAL_THEN `?rf mrf1 mrf2. l4_vpattern_inter972 pf a = SOME rf /\
                                 l4_vpattern_matches972 rf f' mrf1 mrf2`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [];
     MAP_EVERY EXISTS_TAC [`L4VPVar972 rf`;`mrf1:l4_vlevel961 list`;
                           `l4_vmenv_var972 a' mrf2`] THEN
     ASM_REWRITE_TAC [l4_opt_bind972] THEN
     MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC []]]]);;

let l4_vpattern_matches_inter_bwd972 = prove
 (`!p q e.
   (?r m1 m2. l4_vpattern_inter972 p q = SOME r /\ l4_vpattern_matches972 r e m1 m2) ==>
   (?m1 m2. l4_vpattern_matches972 p e m1 m2) /\
   (?m1 m2. l4_vpattern_matches972 q e m1 m2)`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [X_GEN_TAC `c:l4_name` THEN X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_inter_clauses972;distinctness "option"] THEN
   COND_CASES_TAC THEN REWRITE_TAC [distinctness "option";injectivity "option"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN ASM_MESON_TAC [];
   MAP_EVERY X_GEN_TAC [`pf:l4_vpattern972`;`pa:l4_vpattern972`] THEN
   STRIP_TAC THEN X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_inter_clauses972;l4_opt_bind_eq_some972;
                distinctness "option";injectivity "option"] THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [l4_vpattern_matches_app_inv972]) THEN
   l4_subst_vars_tac972 THENL
   [SUBGOAL_THEN `((?m1 m2. l4_vpattern_matches972 pf f' m1 m2) /\
                   (?m1 m2. l4_vpattern_matches972 a0 f' m1 m2)) /\
                  ((?m1 m2. l4_vpattern_matches972 pa a' m1 m2) /\
                   (?m1 m2. l4_vpattern_matches972 a1 a' m1 m2))`
      (fun th -> MESON_TAC [th;l4_vpm_app972]) THEN
    ASM_MESON_TAC [];
    SUBGOAL_THEN `(?m1 m2. l4_vpattern_matches972 pf f' m1 m2) /\
                  (?m1 m2. l4_vpattern_matches972 a f' m1 m2)`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC []; ASM_MESON_TAC [l4_vpm_app972;l4_vpm_var972]]];
   X_GEN_TAC `pf:l4_vpattern972` THEN DISCH_TAC THEN
   X_GEN_TAC `q:l4_vpattern972` THEN X_GEN_TAC `e:l4_vexpr961` THEN
   STRUCT_CASES_TAC (SPEC `q:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_inter_clauses972;l4_opt_bind_eq_some972;
                distinctness "option";injectivity "option"] THEN
   STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [l4_vpattern_matches_app_inv972]) THEN
    l4_subst_vars_tac972 THEN
    SUBGOAL_THEN `(?m1 m2. l4_vpattern_matches972 pf f' m1 m2) /\
                  (?m1 m2. l4_vpattern_matches972 a0 f' m1 m2)`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC []; ASM_MESON_TAC [l4_vpm_app972;l4_vpm_var972]];
    POP_ASSUM MP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [l4_vpattern_matches_var_inv972]) THEN
    l4_subst_vars_tac972 THEN
    SUBGOAL_THEN `(?m1 m2. l4_vpattern_matches972 pf f' m1 m2) /\
                  (?m1 m2. l4_vpattern_matches972 a f' m1 m2)`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC []; ASM_MESON_TAC [l4_vpm_var972]]]]);;

let l4_vpattern_matches_inter972 = prove
 (`!p q e.
   ((?m1 m2. l4_vpattern_matches972 p e m1 m2) /\
    (?m1 m2. l4_vpattern_matches972 q e m1 m2)) <=>
   (?r m1 m2. l4_vpattern_inter972 p q = SOME r /\ l4_vpattern_matches972 r e m1 m2)`,
  MESON_TAC [l4_vpattern_matches_inter_fwd972;l4_vpattern_matches_inter_bwd972]);;

let l4_vsimple_pattern_INDUCT972,l4_vsimple_pattern_RECURSION972 = define_type
 "l4_vsimple_pattern972 =
    L4VSPIota972 l4_name num l4_name num
  | L4VSPDefn972 l4_name";;

let l4_vsimple_to_pattern972 = new_recursive_definition l4_vsimple_pattern_RECURSION972
 `(l4_vsimple_to_pattern972 (L4VSPIota972 r m c n) =
     L4VPApp972 (l4_vpattern_varN972 (L4VPConst972 r) m)
                (l4_vpattern_varN972 (L4VPConst972 c) n)) /\
  (l4_vsimple_to_pattern972 (L4VSPDefn972 c) = L4VPConst972 c)`;;

(* ========================================================================= *)
(* 2. Injectivity & Uniqueness of Typing                                     *)
(*    (Lean4Lean/Theory/Typing/{Injectivity,UniqueTyping}.lean)              *)
(* ========================================================================= *)

let l4_vlookup_determ_ind972 = prove
 (`!g i ty1. l4_vlookup961 g i ty1 ==> (!ty2. l4_vlookup961 g i ty2 ==> ty1 = ty2)`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [distinctness "list";injectivity "list";NOT_SUC] THEN
   MESON_TAC [];
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [distinctness "list";injectivity "list";NOT_SUC;SUC_INJ] THEN
   ASM_MESON_TAC []]);;

let l4_vlookup_determ972 = prove
 (`!g i ty1 ty2. l4_vlookup961 g i ty1 /\ l4_vlookup961 g i ty2 ==> ty1 = ty2`,
  MESON_TAC [l4_vlookup_determ_ind972]);;

let l4_vlift_prime_inj972 = l4_vlift_prime_inj969;;

let l4_vlift_forall_eq972 = prove
 (`!a b. L4VForallE961 (l4_vlift961 a) (l4_vliftN961 b 1 1) =
         l4_vlift961 (L4VForallE961 a b)`,
  REWRITE_TAC [l4_vlift961;l4_vliftN961;ONE]);;

let l4_vctx_cons972 = prove
 (`!env uvars g dom u.
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g dom (L4VSort961 u) ==>
   l4_vctx_wf966 env uvars (CONS dom g)`,
  REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN MESON_TAC []);;

let l4_vlevel_imax_zero972 = prove
 (`!u. l4_vlevel_equiv961 (L4VLIMax961 u L4VLZero961) L4VLZero961`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961;l4_vlevel_imax_nat961]);;

let l4_vlevel_imax_eq_zero972 = prove
 (`!u v. l4_vlevel_equiv961 (L4VLIMax961 u v) L4VLZero961 ==>
         l4_vlevel_equiv961 v L4VLZero961`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961;l4_vlevel_imax_nat961] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `ls:num list`) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC);;

let l4_vhas_type_sort972 = prove
 (`!env uvars g u.
   l4_vlevel_wf961 uvars u ==>
   l4_vhas_type961 env uvars g (L4VSort961 u) (L4VSort961 (L4VLSucc961 u))`,
  REWRITE_TAC [l4_vhas_type961] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_sort961 THEN
  ASM_REWRITE_TAC [l4_vlevel_equiv_refl961]);;

let l4_vhas_type_const972 = prove
 (`!env uvars g c ci ls.
   l4_venv_lookup_const961 env c ci /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = l4_vc_uvars961 ci ==>
   l4_vhas_type961 env uvars g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci))`,
  REWRITE_TAC [l4_vhas_type961] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_const961 THEN
  ASM_REWRITE_TAC [l4_all2_vlevel_equiv_refl970]);;

let l4_vhas_type_app972 = prove
 (`!env uvars g f a dom cod.
   l4_vhas_type961 env uvars g f (L4VForallE961 dom cod) /\
   l4_vhas_type961 env uvars g a dom ==>
   l4_vhas_type961 env uvars g (L4VApp961 f a) (l4_vinst0961 cod a)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_app961]);;

let l4_vhas_type_lam972 = prove
 (`!env uvars g u dom cod body.
   l4_vhas_type961 env uvars g dom (L4VSort961 u) /\
   l4_vhas_type961 env uvars (CONS dom g) body cod ==>
   l4_vhas_type961 env uvars g (L4VLam961 dom body) (L4VForallE961 dom cod)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_lam961]);;

let l4_vhas_type_forall972 = prove
 (`!env uvars g u v dom cod.
   l4_vhas_type961 env uvars g dom (L4VSort961 u) /\
   l4_vhas_type961 env uvars (CONS dom g) cod (L4VSort961 v) ==>
   l4_vhas_type961 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v))`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_forall961]);;

let l4_vhas_type_forall_inv972 = prove
 (`!env uvars g dom cod ty.
   l4_venv_wf966 env /\
   l4_vhas_type961 env uvars g (L4VForallE961 dom cod) ty ==>
   l4_vis_type961 env uvars g dom /\
   l4_vis_type961 env uvars (CONS dom g) cod`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `L4VForallE961 dom cod`;`L4VForallE961 dom cod`;`ty:l4_vexpr961`]
    l4_vis_defeq_forall_inv_ind966) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`dom:l4_vexpr961`;`cod:l4_vexpr961`]) THEN
  ASM_SIMP_TAC [l4_venv_wf_closed966;l4_venv_wf_forall_inv966]);;

let l4_vis_defeq_sort_inv_l972 = prove
 (`!env uvars g u e2 v.
   l4_vis_defeq961 env uvars g (L4VSort961 u) e2 v ==> l4_vlevel_wf961 uvars u`,
  MESON_TAC [l4_vis_defeq_sort_inv'966]);;

let l4_vis_defeq_sort_inv_r972 = prove
 (`!env uvars g e1 u v.
   l4_vis_defeq961 env uvars g e1 (L4VSort961 u) v ==> l4_vlevel_wf961 uvars u`,
  MESON_TAC [l4_vis_defeq_sort_inv'966]);;

let l4_vis_defeq_u_symm972 = prove
 (`!env uvars g e1 e2.
   l4_vis_defeq_u961 env uvars g e1 e2 ==> l4_vis_defeq_u961 env uvars g e2 e1`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_symm961]);;

let l4_vis_defeq_ctx_wf_ind972 = prove
 (`!env uvars g0 g1 g2.
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
   (l4_venv_closed966 env /\ l4_vctx_wf966 env uvars g0 ==> l4_vctx_wf966 env uvars g1)`,
  MATCH_MP_TAC l4_vis_defeq_ctx_STRONG_INDUCT966 THEN
  REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN
  MESON_TAC [l4_vis_defeq_refl_l961]);;

let l4_vis_defeq_ctx_wf972 = prove
 (`!env uvars g0 g1 g2.
   l4_venv_closed966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
   l4_vctx_wf966 env uvars g1`,
  MESON_TAC [l4_vis_defeq_ctx_wf_ind972]);;

let l4_vctx_instN_wf_ind972 = prove
 (`!g0 e0 a0 k g1 g.
   l4_vctx_instN966 g0 e0 a0 k g1 g ==>
   (!env uvars.
      l4_venv_closed966 env /\
      l4_vhas_type961 env uvars g0 e0 a0 /\
      l4_vctx_wf966 env uvars g1 ==>
      l4_vctx_wf966 env uvars g0 /\ l4_vctx_wf966 env uvars g)`,
  MATCH_MP_TAC (derive_strong_induction (l4_vctx_instN_RULES966, l4_vctx_instN_INDUCT966)) THEN
  REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN CONJ_TAC THENL
  [MESON_TAC [];
   REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC [];
    ASM_MESON_TAC [];
    EXISTS_TAC `u:l4_vlevel961` THEN
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `e0:l4_vexpr961`;`g0':l4_vexpr961`;`g1:l4_vexpr961 list`;
                   `a:l4_vexpr961`;`a:l4_vexpr961`;`L4VSort961 u`;
                   `k:num`;`g:l4_vexpr961 list`]
      l4_vis_defeq_instN966) THEN
    ASM_SIMP_TAC [l4_vinst961;GSYM l4_vhas_type961]]]);;

let l4_vctx_instN_wf972 = prove
 (`!env uvars g0 e0 a0 k g1 g.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vctx_wf966 env uvars g1 ==>
   l4_vctx_wf966 env uvars g0 /\ l4_vctx_wf966 env uvars g`,
  MESON_TAC [l4_vctx_instN_wf_ind972]);;

(* Parameterized Injectivity Predicate (ZERO Axioms!) *)

let l4_defeq_injectivity972 = new_definition
 `l4_defeq_injectivity972 env <=>
   (!uvars g u v.
      l4_vctx_wf966 env uvars g /\
      l4_vis_defeq_u961 env uvars g (L4VSort961 u) (L4VSort961 v) ==>
      l4_vlevel_equiv961 u v) /\
   (!uvars g dom cod dom' cod' ty ty' n n'.
      l4_vctx_wf966 env uvars g /\
      l4_vis_defeq_u961 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod') /\
      l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom cod) ty T n /\
      l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom' cod') ty' T n' ==>
      (?u. l4_vis_defeq961 env uvars g dom dom' (L4VSort961 u) /\
           l4_vhas_type_stratified970 env uvars g dom (L4VSort961 u) T n) /\
      (?v. l4_vis_defeq961 env uvars (CONS dom g) cod cod' (L4VSort961 v) /\
           l4_vhas_type_stratified970 env uvars (CONS dom g) cod (L4VSort961 v) T n /\
           l4_vhas_type_stratified970 env uvars (CONS dom' g) cod' (L4VSort961 v) T n')) /\
   (!uvars g u dom cod.
      l4_vctx_wf966 env uvars g ==>
      ~l4_vis_defeq_u961 env uvars g (L4VSort961 u) (L4VForallE961 dom cod)) /\
   (!uvars n k g g' e1 e2.
      l4_vctx_wf966 env uvars g' /\
      l4_vctx_liftN966 n k g g' ==>
      (l4_vis_defeq_u961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) <=>
       l4_vis_defeq_u961 env uvars g e1 e2))`;;

let l4_vis_defeq_u_sort_inv972 = prove
 (`!env uvars g u v.
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g (L4VSort961 u) (L4VSort961 v) ==>
   l4_vlevel_equiv961 u v`,
  REWRITE_TAC [l4_defeq_injectivity972] THEN MESON_TAC []);;

let l4_vis_defeq_u_forallE_inv_stratified972 = prove
 (`!env uvars g dom cod dom' cod' ty ty' n n'.
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod') /\
   l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom cod) ty T n /\
   l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom' cod') ty' T n' ==>
   (?u. l4_vis_defeq961 env uvars g dom dom' (L4VSort961 u) /\
        l4_vhas_type_stratified970 env uvars g dom (L4VSort961 u) T n) /\
   (?v. l4_vis_defeq961 env uvars (CONS dom g) cod cod' (L4VSort961 v) /\
        l4_vhas_type_stratified970 env uvars (CONS dom g) cod (L4VSort961 v) T n /\
        l4_vhas_type_stratified970 env uvars (CONS dom' g) cod' (L4VSort961 v) T n')`,
  REWRITE_TAC [l4_defeq_injectivity972] THEN MESON_TAC []);;

let l4_vis_defeq_u_forallE_inv972 = prove
 (`!env uvars g dom cod dom' cod'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod') ==>
   (?u. l4_vis_defeq961 env uvars g dom dom' (L4VSort961 u)) /\
   (?v. l4_vis_defeq961 env uvars (CONS dom g) cod cod' (L4VSort961 v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `l4_vis_defeq_u961 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod')` THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN DISCH_THEN (X_CHOOSE_TAC `ty:l4_vexpr961`) THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod') ty`
    ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g (L4VForallE961 dom cod) ty T /\
                l4_vhas_type_strong970 env uvars g (L4VForallE961 dom' cod') ty T`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_has_type'970]; ALL_TAC] THEN
  SUBGOAL_THEN `(?n. l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom cod) ty T n) /\
                (?n'. l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom' cod') ty T n')`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vhas_type_strong_stratify970]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `dom:l4_vexpr961`;`cod:l4_vexpr961`;`dom':l4_vexpr961`;`cod':l4_vexpr961`;
                 `ty:l4_vexpr961`;`ty:l4_vexpr961`;`n:num`;`n':num`]
    l4_vis_defeq_u_forallE_inv_stratified972) THEN
  ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []);;

let l4_vis_defeq_u_sort_forallE_inv972 = prove
 (`!env uvars g u dom cod.
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g ==>
   ~l4_vis_defeq_u961 env uvars g (L4VSort961 u) (L4VForallE961 dom cod)`,
  REWRITE_TAC [l4_defeq_injectivity972] THEN MESON_TAC []);;

let l4_vis_defeq_u_weakN_iff972 = prove
 (`!env uvars n k g g' e1 e2.
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vis_defeq_u961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) <=>
    l4_vis_defeq_u961 env uvars g e1 e2)`,
  REWRITE_TAC [l4_defeq_injectivity972] THEN MESON_TAC []);;

(* Uniqueness of Typing via Stratified Induction *)

let l4_vis_defeq_uniq_stratified_base_aux972 = prove
 (`!env uvars g e ty2 b n2.
   l4_vhas_type_stratified970 env uvars g e ty2 b n2 ==>
   (!ty1 n1 n0.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g /\
      b = T /\
      n1 <= n0 /\ n2 <= n0 /\
      (!k. k < n0 ==>
           !g' e' a' b' b_fl m1 m2.
             l4_vctx_wf966 env uvars g' /\ m1 <= k /\ m2 <= k /\
             l4_vhas_type_stratified970 env uvars g' e' a' b_fl m1 /\
             l4_vhas_type_stratified970 env uvars g' e' b' b_fl m2 ==>
             ?u. l4_vis_defeq961 env uvars g' a' b' (L4VSort961 u) /\
                 ?v. l4_vlevel_equiv961 u v /\
                     l4_vhas_type_stratified970 env uvars g' a' (L4VSort961 u) T (k - 1) /\
                     l4_vhas_type_stratified970 env uvars g' b' (L4VSort961 v) T (k - 1)) /\
      (!ty_q m_q.
         m_q <= n0 /\
         l4_vhas_type_stratified970 env uvars g e ty_q F m_q ==>
         ?u. l4_vis_defeq961 env uvars g ty1 ty_q (L4VSort961 u) /\
             ?v. l4_vlevel_equiv961 u v /\
                 l4_vhas_type_stratified970 env uvars g ty1 (L4VSort961 u) T (n0 - 1) /\
                 l4_vhas_type_stratified970 env uvars g ty_q (L4VSort961 v) T (n0 - 1)) ==>
      ?u. l4_vis_defeq961 env uvars g ty1 ty2 (L4VSort961 u) /\
          ?v. l4_vlevel_equiv961 u v /\
              l4_vhas_type_stratified970 env uvars g ty1 (L4VSort961 u) T (n0 - 1) /\
              l4_vhas_type_stratified970 env uvars g ty2 (L4VSort961 v) T (n0 - 1))`,
  MATCH_MP_TAC l4_vhas_type_stratified_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC []; REWRITE_TAC []; REWRITE_TAC []; REWRITE_TAC [];
   REWRITE_TAC []; REWRITE_TAC [];
   (* base *)
   REPEAT STRIP_TAC THEN ASM_MESON_TAC [];
   (* defeq *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u':l4_vlevel961`;`ty_mid:l4_vexpr961`;`ty2:l4_vexpr961`;
                        `e:l4_vexpr961`;`m':num`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`ty1:l4_vexpr961`;`n1:num`;`n0:num`] THEN STRIP_TAC THEN
   SUBGOAL_THEN `?k. n0 = SUC k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `SUC m' <= n0` THEN STRUCT_CASES_TAC (SPEC `n0:num` num_CASES) THENL
    [ARITH_TAC; DISCH_TAC THEN EXISTS_TAC `n:num` THEN REFL_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `m' <= k /\ k < SUC k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC m' <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN
     `?u1. l4_vis_defeq961 env uvars g ty1 ty_mid (L4VSort961 u1) /\
           ?u2. l4_vlevel_equiv961 u1 u2 /\
                l4_vhas_type_stratified970 env uvars g ty1 (L4VSort961 u1) T k /\
                l4_vhas_type_stratified970 env uvars g ty_mid (L4VSort961 u2) T k`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM (fun th ->
      let th1 = SPECL [`ty1:l4_vexpr961`;`n1:num`;`SUC k`] th in
      if free_in `e:l4_vexpr961` (concl th1) && free_in `ty_mid:l4_vexpr961` (concl th1)
      then MP_TAC th1 else failwith "skip") THEN
    ASM_REWRITE_TAC [SUC_SUB1] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC m' <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `?s1. l4_vis_defeq961 env uvars g (L4VSort961 u') (L4VSort961 u2) (L4VSort961 s1)`
     (X_CHOOSE_TAC `s1:l4_vlevel961`) THENL
   [FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
    DISCH_THEN (MP_TAC o SPECL [`g:l4_vexpr961 list`;`ty_mid:l4_vexpr961`;
                                `L4VSort961 u'`;`L4VSort961 u2`;`T`;`m':num`;`k:num`]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u' u2` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s1` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u1` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_sort_r966 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`ty1:l4_vexpr961`;`ty1:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`k:num`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u1 u'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `u2:l4_vlevel961` THEN
    ASM_SIMP_TAC [l4_vlevel_equiv_symm961]; ALL_TAC] THEN
   EXISTS_TAC `u1:l4_vlevel961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `ty_mid:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VSort961 u'`;`L4VLSucc961 u1`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN
    MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_mono970 THEN EXISTS_TAC `m':num` THEN
    ASM_REWRITE_TAC []]]);;

let l4_vis_defeq_uniq_stratified_step972 = prove
 (`!env uvars g e ty1 b n1.
   l4_vhas_type_stratified970 env uvars g e ty1 b n1 ==>
   (!ty2 n2 n0.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g /\
      n1 <= n0 /\ n2 <= n0 /\
      (!k. k < n0 ==>
           !g' e' a' b' b_fl m1 m2.
             l4_vctx_wf966 env uvars g' /\ m1 <= k /\ m2 <= k /\
             l4_vhas_type_stratified970 env uvars g' e' a' b_fl m1 /\
             l4_vhas_type_stratified970 env uvars g' e' b' b_fl m2 ==>
             ?u. l4_vis_defeq961 env uvars g' a' b' (L4VSort961 u) /\
                 ?v. l4_vlevel_equiv961 u v /\
                     l4_vhas_type_stratified970 env uvars g' a' (L4VSort961 u) T (k - 1) /\
                     l4_vhas_type_stratified970 env uvars g' b' (L4VSort961 v) T (k - 1)) /\
      l4_vhas_type_stratified970 env uvars g e ty2 b n2 ==>
      ?u. l4_vis_defeq961 env uvars g ty1 ty2 (L4VSort961 u) /\
          ?v. l4_vlevel_equiv961 u v /\
              l4_vhas_type_stratified970 env uvars g ty1 (L4VSort961 u) T (n0 - 1) /\
              l4_vhas_type_stratified970 env uvars g ty2 (L4VSort961 v) T (n0 - 1))`,
  MATCH_MP_TAC l4_vhas_type_stratified_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `i:num`;`ty1:l4_vexpr961`;`u:l4_vlevel961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VBVar961 i) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `ty1:l4_vexpr961 = ty2` SUBST_ALL_TAC THENL
   [FIRST_ASSUM (fun h1 -> FIRST_ASSUM (fun h2 ->
      ACCEPT_TAC (MATCH_MP l4_vlookup_determ972 (CONJ h1 h2)))); ALL_TAC] THEN
   EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `u:l4_vlevel961` THEN REWRITE_TAC [l4_vlevel_equiv_refl961] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_mono970 THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC [] THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC];
   (* sort *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `l1:l4_vlevel961`;`l2:l4_vlevel961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VSort961 l1) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 (L4VLSucc961 l2') (L4VLSucc961 l2)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vlevel_succ_equiv970 THEN
    MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `l1':l4_vlevel961` THEN
    ASM_SIMP_TAC [l4_vlevel_equiv_symm961]; ALL_TAC] THEN
   EXISTS_TAC `L4VLSucc961 (L4VLSucc961 l2')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
    ASM_REWRITE_TAC [l4_vlevel_wf961];
    EXISTS_TAC `L4VLSucc961 (L4VLSucc961 l2)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vlevel_succ_equiv970 THEN ASM_REWRITE_TAC [];
     CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_base970 THEN
     MATCH_MP_TAC l4_vhas_type_stratified_sort970 THEN
     ASM_SIMP_TAC [l4_vlevel_wf961;l4_vlevel_equiv_symm961;l4_vlevel_equiv_refl961]]];
   (* const *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `c:l4_name`;`ci:l4_vconstant961`;`ls:l4_vlevel961 list`;
                        `u:l4_vlevel961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VConst961 c ls) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `ci':l4_vconstant961 = ci` SUBST_ALL_TAC THENL
   [FIRST_ASSUM (fun h1 -> FIRST_ASSUM (fun h2 ->
      ACCEPT_TAC (MATCH_MP l4_venv_wf_lookup_unique966
        (CONJ (ASSUME `l4_venv_wf966 env`) (CONJ h1 h2))))); ALL_TAC] THEN
   EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `u:l4_vlevel961` THEN REWRITE_TAC [l4_vlevel_equiv_refl961] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_mono970 THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC [] THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `f:l4_vexpr961`;`a:l4_vexpr961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VApp961 f a) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?k. n0 = SUC k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n0 - 1` THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m <= k /\ n <= k /\ k < SUC k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC m <= SUC k` THEN UNDISCH_TAC `SUC n <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN
     `?w. l4_vis_defeq961 env uvars g (L4VForallE961 dom cod) (L4VForallE961 dom' cod') (L4VSort961 w) /\
          ?w'. l4_vlevel_equiv961 w w' /\
               l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom cod) (L4VSort961 w) T k /\
               l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom' cod') (L4VSort961 w') T k`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM (fun th ->
      let th1 = SPECL [`L4VForallE961 dom' cod'`;`n:num`;`SUC k`] th in
      if free_in `f':l4_vexpr961` (concl th1) && free_in `L4VForallE961 dom cod` (concl th1)
      then MP_TAC th1 else failwith "skip") THEN
    ASM_REWRITE_TAC [SUC_SUB1] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`;`dom':l4_vexpr961`;`cod':l4_vexpr961`;
                  `L4VSort961 w`;`L4VSort961 w'`;`k:num`;`k:num`]
     l4_vis_defeq_u_forallE_inv_stratified972) THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN
   ANTS_TAC THENL [EXISTS_TAC `L4VSort961 w` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC)
     (X_CHOOSE_THEN `u0:l4_vlevel961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom' g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`n:num`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `(?s1. l4_vis_defeq961 env uvars (CONS dom g) (L4VSort961 v) (L4VSort961 u0) (L4VSort961 s1)) /\
                 (?s2. l4_vis_defeq961 env uvars (CONS dom' g) (L4VSort961 v') (L4VSort961 u0) (L4VSort961 s2))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`CONS (dom:l4_vexpr961) g`;`cod:l4_vexpr961`;
                                 `L4VSort961 v`;`L4VSort961 u0`;`T`;`m:num`;`k:num`]) THEN
     ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC [];
     FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`CONS (dom':l4_vexpr961) g`;`cod':l4_vexpr961`;
                                 `L4VSort961 v'`;`L4VSort961 u0`;`T`;`n:num`;`k:num`]) THEN
     ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC []]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 v u0 /\ l4_vlevel_equiv961 v' u0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THENL
    [MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s1` THEN ASM_REWRITE_TAC [];
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`CONS (dom':l4_vexpr961) g`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s2` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars v /\ l4_vlevel_wf961 uvars u0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort_inv_l972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom:l4_vexpr961) g`;`L4VSort961 u0`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_r972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom:l4_vexpr961) g`;`L4VSort961 v`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC []]; ALL_TAC] THEN
   EXISTS_TAC `v:l4_vlevel961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VSort961 u0`;`L4VLSucc961 u0`] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_SIMP_TAC [l4_vlevel_equiv_symm961];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                    `cod:l4_vexpr961`;`cod':l4_vexpr961`;`L4VSort961 u0`;`a':l4_vexpr961`]
       l4_vis_defeq_inst0966) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vinst0961;l4_vinst961] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
     MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC []];
    EXISTS_TAC `v':l4_vlevel961` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `u0:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_vlevel_equiv_symm961];
     CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
     [EXISTS_TAC `m:num`; EXISTS_TAC `n:num`] THEN ASM_REWRITE_TAC []]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `body:l4_vexpr961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VLam961 dom body) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?k. n0 = SUC k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n0 - 1` THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m <= k /\ n <= k /\ k < SUC k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC m <= SUC k` THEN UNDISCH_TAC `SUC n <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom' g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `?u1. l4_vis_defeq961 env uvars (CONS dom' g) cod cod' (L4VSort961 u1) /\
           ?u2. l4_vlevel_equiv961 u1 u2 /\
                l4_vhas_type_stratified970 env uvars (CONS dom' g) cod (L4VSort961 u1) T k /\
                l4_vhas_type_stratified970 env uvars (CONS dom' g) cod' (L4VSort961 u2) T k`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM (fun th ->
      let th1 = SPECL [`cod':l4_vexpr961`;`n:num`;`SUC k`] th in
      if free_in `body':l4_vexpr961` (concl th1) then MP_TAC th1 else failwith "skip") THEN
    ASM_REWRITE_TAC [SUC_SUB1] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN
     `(?s1. l4_vis_defeq961 env uvars g (L4VSort961 u) (L4VSort961 u') (L4VSort961 s1)) /\
      (?s2. l4_vis_defeq961 env uvars (CONS dom' g) (L4VSort961 v) (L4VSort961 u1) (L4VSort961 s2)) /\
      (?s3. l4_vis_defeq961 env uvars (CONS dom' g) (L4VSort961 v') (L4VSort961 u2) (L4VSort961 s3))`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`g:l4_vexpr961 list`;`dom':l4_vexpr961`;
                                 `L4VSort961 u`;`L4VSort961 u'`;`T`;`m:num`;`n:num`]) THEN
     ASM_REWRITE_TAC [] THEN MESON_TAC [];
     FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`CONS (dom':l4_vexpr961) g`;`cod:l4_vexpr961`;
                                 `L4VSort961 v`;`L4VSort961 u1`;`T`;`m:num`;`k:num`]) THEN
     ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC [];
     FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`CONS (dom':l4_vexpr961) g`;`cod':l4_vexpr961`;
                                 `L4VSort961 v'`;`L4VSort961 u2`;`T`;`n:num`;`k:num`]) THEN
     ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC []]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u u' /\ l4_vlevel_equiv961 v u1 /\ l4_vlevel_equiv961 v' u2`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THENL
    [MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s1` THEN ASM_REWRITE_TAC [];
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`CONS (dom':l4_vexpr961) g`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s2` THEN ASM_REWRITE_TAC [];
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`CONS (dom':l4_vexpr961) g`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s3` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars v /\ l4_vlevel_wf961 uvars u1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort_inv_l972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom':l4_vexpr961) g`;`L4VSort961 u1`;`L4VSort961 s2`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_r972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom':l4_vexpr961) g`;`L4VSort961 v`;`L4VSort961 s2`] THEN
     ASM_REWRITE_TAC []]; ALL_TAC] THEN
   EXISTS_TAC `L4VLIMax961 u v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_forall961 THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
     MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`L4VSort961 u1`;`L4VLSucc961 v`] THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
     ASM_REWRITE_TAC []];
    EXISTS_TAC `L4VLIMax961 u' v'` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vlevel_imax_equiv970 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `u1:l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `u2:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_vlevel_equiv_symm961];
     CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
     [EXISTS_TAC `m:num`; EXISTS_TAC `n:num`] THEN ASM_REWRITE_TAC []]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type_stratified970 env uvars g (L4VForallE961 dom cod) ty2 F n2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_stratified_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?k. n0 = SUC k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n0 - 1` THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m <= k /\ n <= k /\ k < SUC k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC m <= SUC k` THEN UNDISCH_TAC `SUC n <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom' g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_stratified_has_type970 THEN
    MAP_EVERY EXISTS_TAC [`T`;`m:num`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `(?s1. l4_vis_defeq961 env uvars g (L4VSort961 u) (L4VSort961 u') (L4VSort961 s1)) /\
      (?s2. l4_vis_defeq961 env uvars (CONS dom' g) (L4VSort961 v) (L4VSort961 v') (L4VSort961 s2))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`g:l4_vexpr961 list`;`dom':l4_vexpr961`;
                                 `L4VSort961 u`;`L4VSort961 u'`;`T`;`m:num`;`n:num`]) THEN
     ASM_REWRITE_TAC [] THEN MESON_TAC [];
     FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
     DISCH_THEN (MP_TAC o SPECL [`CONS (dom':l4_vexpr961) g`;`cod':l4_vexpr961`;
                                 `L4VSort961 v`;`L4VSort961 v'`;`T`;`m:num`;`n:num`]) THEN
     ASM_REWRITE_TAC [] THEN MESON_TAC []]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u u' /\ l4_vlevel_equiv961 v v'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THENL
    [MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s1` THEN ASM_REWRITE_TAC [];
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`CONS (dom':l4_vexpr961) g`] THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s2` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars u' /\
                 l4_vlevel_wf961 uvars v /\ l4_vlevel_wf961 uvars v'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort_inv_l972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`L4VSort961 u'`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_r972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`L4VSort961 u`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_l972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom':l4_vexpr961) g`;`L4VSort961 v'`;`L4VSort961 s2`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_r972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom':l4_vexpr961) g`;`L4VSort961 v`;`L4VSort961 s2`] THEN
     ASM_REWRITE_TAC []]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 (L4VLIMax961 u v) (L4VLIMax961 u' v')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vlevel_imax_equiv970 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   EXISTS_TAC `L4VLSucc961 (L4VLIMax961 u v)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [l4_vlevel_wf961];
    EXISTS_TAC `L4VLSucc961 (L4VLIMax961 u v)` THEN REWRITE_TAC [l4_vlevel_equiv_refl961] THEN
    CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_base970 THEN
    MATCH_MP_TAC l4_vhas_type_stratified_sort970 THEN
    ASM_SIMP_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961;l4_vlevel_equiv_symm961]];
   (* base *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e:l4_vexpr961`;`ty2:l4_vexpr961`;`T`;`n2:num`]
     l4_vis_defeq_uniq_stratified_base_aux972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`ty:l4_vexpr961`;`n:num`;`n0:num`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`ty_q:l4_vexpr961`;`m_q:num`;`n0:num`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
   (* defeq *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`ty_mid:l4_vexpr961`;`ty1:l4_vexpr961`;
                        `e:l4_vexpr961`;`m:num`] THEN
   STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`ty2:l4_vexpr961`;`n2:num`;`n0:num`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `?k. n0 = SUC k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n0 - 1` THEN UNDISCH_TAC `SUC m <= n0` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m <= k /\ k < SUC k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC m <= SUC k` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN
     `?u1. l4_vis_defeq961 env uvars g ty_mid ty2 (L4VSort961 u1) /\
           ?u2. l4_vlevel_equiv961 u1 u2 /\
                l4_vhas_type_stratified970 env uvars g ty_mid (L4VSort961 u1) T k /\
                l4_vhas_type_stratified970 env uvars g ty2 (L4VSort961 u2) T k`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM (fun th ->
      let th1 = SPECL [`ty2:l4_vexpr961`;`n2:num`;`SUC k`] th in
      if free_in `e:l4_vexpr961` (concl th1) && free_in `ty_mid:l4_vexpr961` (concl th1)
      then MP_TAC th1 else failwith "skip") THEN
    ASM_REWRITE_TAC [SUC_SUB1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `?s1. l4_vis_defeq961 env uvars g (L4VSort961 u) (L4VSort961 u1) (L4VSort961 s1)`
     (X_CHOOSE_TAC `s1:l4_vlevel961`) THENL
   [FIRST_ASSUM (fun th -> MP_TAC (MP (SPEC `k:num` th) (ASSUME `k < SUC k`))) THEN
    DISCH_THEN (MP_TAC o SPECL [`g:l4_vexpr961 list`;`ty_mid:l4_vexpr961`;
                                `L4VSort961 u`;`L4VSort961 u1`;`T`;`m:num`;`k:num`]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u u1` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 s1` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars u1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort_inv_l972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`L4VSort961 u1`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_sort_inv_r972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`L4VSort961 u`;`L4VSort961 s1`] THEN
     ASM_REWRITE_TAC []]; ALL_TAC] THEN
   EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `ty_mid:l4_vexpr961` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`L4VSort961 u1`;`L4VLSucc961 u`] THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
     ASM_REWRITE_TAC []];
    EXISTS_TAC `u2:l4_vlevel961` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vlevel_equiv_trans961 THEN EXISTS_TAC `u1:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THEN
     EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC []]]]);;

let l4_vis_defeq_uniq_stratified972 = prove
 (`!env uvars n g e a b b_fl n1 n2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   n1 <= n /\ n2 <= n /\
   l4_vhas_type_stratified970 env uvars g e a b_fl n1 /\
   l4_vhas_type_stratified970 env uvars g e b b_fl n2 ==>
   ?u. l4_vis_defeq961 env uvars g a b (L4VSort961 u) /\
       ?v. l4_vlevel_equiv961 u v /\
           l4_vhas_type_stratified970 env uvars g a (L4VSort961 u) T (n - 1) /\
           l4_vhas_type_stratified970 env uvars g b (L4VSort961 v) T (n - 1)`,
  MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`] THEN
  MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `e:l4_vexpr961`;`a:l4_vexpr961`;`b_fl:bool`;`n1:num`]
    l4_vis_defeq_uniq_stratified_step972) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`b:l4_vexpr961`;`n2:num`;`n:num`]) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`b_fl':bool`;`m1:num`;`m2:num`] THEN
  ASM_REWRITE_TAC []);;

let l4_vis_defeq_uniq_same972 = prove
 (`!env uvars g e1 e2 e3 a1 a2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 a1 /\
   l4_vis_defeq961 env uvars g e2 e3 a2 ==>
   ?u. l4_vis_defeq961 env uvars g a1 a2 (L4VSort961 u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g e1 e2 a1 /\
                l4_vis_defeq_strong970 env uvars g e2 e3 a2` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g e2 a1 T /\
                l4_vhas_type_strong970 env uvars g e2 a2 T` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_has_type'970]; ALL_TAC] THEN
  SUBGOAL_THEN `(?n1. l4_vhas_type_stratified970 env uvars g e2 a1 T n1) /\
                (?n2. l4_vhas_type_stratified970 env uvars g e2 a2 T n2)` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vhas_type_strong_stratify970]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`MAX n1 n2`;`g:l4_vexpr961 list`;
                 `e2:l4_vexpr961`;`a1:l4_vexpr961`;`a2:l4_vexpr961`;`T`;`n1:num`;`n2:num`]
    l4_vis_defeq_uniq_stratified972) THEN
  ASM_REWRITE_TAC [ARITH_RULE `!a b. a <= MAX a b /\ b <= MAX a b`] THEN MESON_TAC []);;

let l4_vis_defeq_uniq_u972 = prove
 (`!env uvars g e1 e2 e3 a b.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 a /\
   l4_vis_defeq961 env uvars g e2 e3 b ==>
   l4_vis_defeq_u961 env uvars g a b`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_uniq_same972]);;

let l4_vis_defeq_trans_r972 = prove
 (`!env uvars g e1 e2 e3 a b.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 a /\
   l4_vis_defeq961 env uvars g e2 e3 b ==>
   l4_vis_defeq961 env uvars g e1 e3 b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 env uvars g a b (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_uniq_same972];
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `e2:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vis_defeq_conv961]]);;

let l4_vis_defeq_trans_l972 = prove
 (`!env uvars g e1 e2 e3 a b.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 a /\
   l4_vis_defeq961 env uvars g e2 e3 b ==>
   l4_vis_defeq961 env uvars g e1 e3 a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 env uvars g a b (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_uniq_same972];
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `e2:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vis_defeq_conv961;l4_vis_defeq_symm961]]);;

let l4_vis_defeq_trans_u_r972 = prove
 (`!env uvars g e1 e2 e3 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g e1 e2 /\
   l4_vis_defeq961 env uvars g e2 e3 a ==>
   l4_vis_defeq961 env uvars g e1 e3 a`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_trans_r972]);;

let l4_vis_defeq_trans_u_l972 = prove
 (`!env uvars g e1 e2 e3 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 a /\
   l4_vis_defeq_u961 env uvars g e2 e3 ==>
   l4_vis_defeq961 env uvars g e1 e3 a`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_trans_l972]);;

let l4_vis_defeq_u_defeqDF972 = prove
 (`!env uvars g e1 e2 a b.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g a b /\
   l4_vis_defeq961 env uvars g e1 e2 a ==>
   l4_vis_defeq961 env uvars g e1 e2 b`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?u. l4_vhas_type961 env uvars g a (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961];
   MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`a:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`a:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961]]);;

let l4_vis_defeq_u_of_l972 = prove
 (`!env uvars g e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g e1 e2 /\
   l4_vhas_type961 env uvars g e1 a ==>
   l4_vis_defeq961 env uvars g e1 e2 a`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_trans_u_l972]);;

let l4_vis_defeq_u_of_r972 = prove
 (`!env uvars g e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g e1 e2 /\
   l4_vhas_type961 env uvars g e2 a ==>
   l4_vis_defeq961 env uvars g e1 e2 a`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_trans_u_r972]);;

let l4_vhas_type_defeq_u_l972 = prove
 (`!env uvars g e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g e1 e2 /\
   l4_vhas_type961 env uvars g e1 a ==>
   l4_vhas_type961 env uvars g e2 a`,
  MESON_TAC [l4_vis_defeq_u_of_l972;l4_vis_defeq_refl_r961]);;

let l4_vhas_type_defeq_u_r972 = prove
 (`!env uvars g e a1 a2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g a1 a2 /\
   l4_vhas_type961 env uvars g e a1 ==>
   l4_vhas_type961 env uvars g e a2`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_u_defeqDF972]);;

let l4_vis_defeq_u_trans972 = prove
 (`!env uvars g e1 e2 e3.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g e1 e2 /\
   l4_vis_defeq_u961 env uvars g e2 e3 ==>
   l4_vis_defeq_u961 env uvars g e1 e3`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_trans_l972]);;

(* Weakening Inversion & Iff Lemmas *)

let l4_vis_defeq_weakN_iff'972 = prove
 (`!env uvars n k g g' e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_wf966 env uvars g /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vis_defeq961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) (l4_vliftN961 a n k) <=>
    l4_vis_defeq961 env uvars g e1 e2 a)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN
   SUBGOAL_THEN `?b. l4_vis_defeq961 env uvars g e1 e2 b` (X_CHOOSE_TAC `b:l4_vexpr961`) THENL
   [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`]
      l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vliftN961 a n k` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_defeqDF972 THEN EXISTS_TAC `b:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                  `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;`b:l4_vexpr961`;`a:l4_vexpr961`]
     l4_vis_defeq_u_weakN_iff972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 e1 n k`;`l4_vliftN961 e2 n k`;`l4_vliftN961 e1 n k`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_weakN966 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []];
   DISCH_TAC THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966]]);;

let l4_vctx_wf_append_inv972 = prove
 (`!env uvars xs g.
   l4_vctx_wf966 env uvars (APPEND xs g) ==> l4_vctx_wf966 env uvars g`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [APPEND;l4_vctx_wf966] THEN ASM_MESON_TAC []);;

let l4_vctx_wf_weakN_inv_ind972 = prove
 (`!n k g g'.
   l4_vctx_liftN966 n k g g' ==>
   (!env uvars.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g' ==>
      l4_vctx_wf966 env uvars g)`,
  MATCH_MP_TAC (derive_strong_induction (l4_vctx_liftN_RULES966, l4_vctx_liftN_INDUCT966)) THEN CONJ_TAC THENL
  [MESON_TAC [l4_vctx_wf_append_inv972];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vctx_wf966;l4_vis_type961;l4_vhas_type961] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN EXISTS_TAC `u:l4_vlevel961` THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                  `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `a:l4_vexpr961`;`a:l4_vexpr961`;`L4VSort961 u`]
     l4_vis_defeq_weakN_iff'972) THEN
   ASM_SIMP_TAC [l4_vliftN961]]);;

let l4_vctx_wf_weakN_inv972 = prove
 (`!env uvars n k g g'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vctx_wf966 env uvars g' ==>
   l4_vctx_wf966 env uvars g`,
  MESON_TAC [l4_vctx_wf_weakN_inv_ind972]);;

let l4_vis_defeq_weakN_iff972 = prove
 (`!env uvars n k g g' e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vis_defeq961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) (l4_vliftN961 a n k) <=>
    l4_vis_defeq961 env uvars g e1 e2 a)`,
  MESON_TAC [l4_vis_defeq_weakN_iff'972;l4_vctx_wf_weakN_inv972]);;

let l4_vhas_type_weakN_iff972 = prove
 (`!env uvars n k g g' e a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vhas_type961 env uvars g' (l4_vliftN961 e n k) (l4_vliftN961 a n k) <=>
    l4_vhas_type961 env uvars g e a)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_weakN_iff972]);;

let l4_vctx_wf_weak_prime_inv_aux972 = prove
 (`!d rho env uvars g g'.
   l4_vlift_op_depth969 rho = d /\
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vctx_wf966 env uvars g' ==>
   l4_vctx_wf966 env uvars g`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
  [SUBGOAL_THEN `g':l4_vexpr961 list = g` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_vctx_lift_prime_depth_zero969]; ASM_REWRITE_TAC []];
   MP_TAC (SPECL [`rho:l4_vlift_op969`;`d:num`] l4_vlift_op_depth_succ969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `l0:l4_vlift_op969` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
   l4_subst_vars_tac972 THEN
   MP_TAC (SPECL [`k:num`;`l0:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`]
     l4_vctx_lift_prime_of_cons_skip969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `g1:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_op_cons_n969 l0 k`;`g1:l4_vexpr961 list`] THEN
   ASM_REWRITE_TAC [l4_vlift_op_depth_cons_n969] THEN
   ASM_MESON_TAC [l4_vctx_wf_weakN_inv972]]);;

let l4_vctx_wf_weak_prime_inv972 = prove
 (`!env uvars rho g g'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vctx_wf966 env uvars g' ==>
   l4_vctx_wf966 env uvars g`,
  MESON_TAC [l4_vctx_wf_weak_prime_inv_aux972]);;

let l4_vis_defeq_u_weak_prime_iff_aux972 = prove
 (`!d rho env uvars g g' e1 e2.
   l4_vlift_op_depth969 rho = d /\
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vis_defeq_u961 env uvars g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho) <=>
    l4_vis_defeq_u961 env uvars g e1 e2)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
  [SUBGOAL_THEN `g':l4_vexpr961 list = g` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_vctx_lift_prime_depth_zero969]; ALL_TAC] THEN
   ASM_SIMP_TAC [l4_vlift_prime_depth_zero969];
   MP_TAC (SPECL [`rho:l4_vlift_op969`;`d:num`] l4_vlift_op_depth_succ969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `l0:l4_vlift_op969` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
   l4_subst_vars_tac972 THEN
   MP_TAC (SPECL [`k:num`;`l0:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`]
     l4_vctx_lift_prime_of_cons_skip969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `g1:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   ONCE_REWRITE_TAC [l4_vlift_op_cons_n_skip_eq969] THEN
   REWRITE_TAC [l4_vlift_prime_comp969] THEN
   SUBGOAL_THEN `L4VLSkip969 L4VLRefl969 = l4_vlift_op_skip_n969 L4VLRefl969 1` SUBST1_TAC THENL
   [REWRITE_TAC [ONE;l4_vlift_op_skip_n969]; ALL_TAC] THEN
   REWRITE_TAC [l4_vlift_prime_cons_n_skip_n969] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`k:num`;
                  `g1:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `l4_vlift_prime969 e1 (l4_vlift_op_cons_n969 l0 k)`;
                  `l4_vlift_prime969 e2 (l4_vlift_op_cons_n969 l0 k)`]
     l4_vis_defeq_u_weakN_iff972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_depth_cons_n969] THEN
   ASM_MESON_TAC [l4_vctx_wf_weakN_inv972]]);;

let l4_vis_defeq_u_weak_prime_iff972 = prove
 (`!env uvars rho g g' e1 e2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vis_defeq_u961 env uvars g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho) <=>
    l4_vis_defeq_u961 env uvars g e1 e2)`,
  MESON_TAC [l4_vis_defeq_u_weak_prime_iff_aux972]);;

let l4_vis_defeq_weak_prime_iff_aux972 = prove
 (`!d rho env uvars g g' e1 e2 a.
   l4_vlift_op_depth969 rho = d /\
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vis_defeq961 env uvars g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho) (l4_vlift_prime969 a rho) <=>
    l4_vis_defeq961 env uvars g e1 e2 a)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
  [SUBGOAL_THEN `g':l4_vexpr961 list = g` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_vctx_lift_prime_depth_zero969]; ALL_TAC] THEN
   ASM_SIMP_TAC [l4_vlift_prime_depth_zero969];
   MP_TAC (SPECL [`rho:l4_vlift_op969`;`d:num`] l4_vlift_op_depth_succ969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `l0:l4_vlift_op969` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
   l4_subst_vars_tac972 THEN
   MP_TAC (SPECL [`k:num`;`l0:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`]
     l4_vctx_lift_prime_of_cons_skip969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `g1:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   ONCE_REWRITE_TAC [l4_vlift_op_cons_n_skip_eq969] THEN
   REWRITE_TAC [l4_vlift_prime_comp969] THEN
   SUBGOAL_THEN `L4VLSkip969 L4VLRefl969 = l4_vlift_op_skip_n969 L4VLRefl969 1` SUBST1_TAC THENL
   [REWRITE_TAC [ONE;l4_vlift_op_skip_n969]; ALL_TAC] THEN
   REWRITE_TAC [l4_vlift_prime_cons_n_skip_n969] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`k:num`;
                  `g1:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `l4_vlift_prime969 e1 (l4_vlift_op_cons_n969 l0 k)`;
                  `l4_vlift_prime969 e2 (l4_vlift_op_cons_n969 l0 k)`;
                  `l4_vlift_prime969 a (l4_vlift_op_cons_n969 l0 k)`]
     l4_vis_defeq_weakN_iff972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [l4_vlift_op_depth_cons_n969] THEN
   ASM_MESON_TAC [l4_vctx_wf_weakN_inv972]]);;

let l4_vis_defeq_weak_prime_iff972 = prove
 (`!env uvars rho g g' e1 e2 a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vis_defeq961 env uvars g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho) (l4_vlift_prime969 a rho) <=>
    l4_vis_defeq961 env uvars g e1 e2 a)`,
  MESON_TAC [l4_vis_defeq_weak_prime_iff_aux972]);;

let l4_vhas_type_weak_prime_iff972 = prove
 (`!env uvars rho g g' e a.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' ==>
   (l4_vhas_type961 env uvars g' (l4_vlift_prime969 e rho) (l4_vlift_prime969 a rho) <=>
    l4_vhas_type961 env uvars g e a)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_weak_prime_iff972]);;

(* ========================================================================= *)
(* 3a. Reflexive-Transitive Closure, Pattern Typing, and Normal Equivalence  *)
(*     (Lean4Lean/Theory/Typing/ChurchRosser.lean lines 1-465)               *)
(* ========================================================================= *)

let l4_vrt_closure_RULES972,l4_vrt_closure_INDUCT972,l4_vrt_closure_CASES972 =
  new_inductive_definition
 `(!(R:A->A->bool) x. l4_vrt_closure972 R x x) /\
  (!(R:A->A->bool) x y z. l4_vrt_closure972 R x y /\ R y z ==> l4_vrt_closure972 R x z)`;;

let l4_vrtc_rfl972, l4_vrtc_tail972 =
  match CONJUNCTS l4_vrt_closure_RULES972 with
  | [c1;c2] -> (c1,c2)
  | _ -> failwith "l4_vrt_closure_RULES972: unexpected arity";;

let l4_vrt_closure_STRONG_INDUCT972 =
  derive_strong_induction (l4_vrt_closure_RULES972, l4_vrt_closure_INDUCT972);;

let l4_vrtc_single972 = prove
 (`!(R:A->A->bool) x y. R x y ==> l4_vrt_closure972 R x y`,
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972]);;

let l4_vrtc_trans_ind972 = prove
 (`!(R:A->A->bool) y z.
   l4_vrt_closure972 R y z ==> (!x. l4_vrt_closure972 R x y ==> l4_vrt_closure972 R x z)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN
  MESON_TAC [l4_vrtc_tail972]);;

let l4_vrtc_trans972 = prove
 (`!(R:A->A->bool) x y z.
   l4_vrt_closure972 R x y /\ l4_vrt_closure972 R y z ==> l4_vrt_closure972 R x z`,
  MESON_TAC [l4_vrtc_trans_ind972]);;

let l4_vrtc_head972 = prove
 (`!(R:A->A->bool) x y z.
   R x y /\ l4_vrt_closure972 R y z ==> l4_vrt_closure972 R x z`,
  MESON_TAC [l4_vrtc_single972;l4_vrtc_trans972]);;

let l4_vrtc_hd_RULES972,l4_vrtc_hd_INDUCT972,l4_vrtc_hd_CASES972 =
  new_inductive_definition
 `(!(R:A->A->bool) x. l4_vrtc_hd972 R x x) /\
  (!(R:A->A->bool) x y z. R x y /\ l4_vrtc_hd972 R y z ==> l4_vrtc_hd972 R x z)`;;

let l4_vrtch_rfl972, l4_vrtch_head972 =
  match CONJUNCTS l4_vrtc_hd_RULES972 with
  | [c1;c2] -> (c1,c2)
  | _ -> failwith "l4_vrtc_hd_RULES972: unexpected arity";;

let l4_vrtc_hd_STRONG_INDUCT972 =
  derive_strong_induction (l4_vrtc_hd_RULES972, l4_vrtc_hd_INDUCT972);;

let l4_vrtch_snoc_ind972 = prove
 (`!(R:A->A->bool) x y.
   l4_vrtc_hd972 R x y ==> (!z. R y z ==> l4_vrtc_hd972 R x z)`,
  MATCH_MP_TAC l4_vrtc_hd_INDUCT972 THEN
  MESON_TAC [l4_vrtch_rfl972;l4_vrtch_head972]);;

let l4_vrtc_to_hd_ind972 = prove
 (`!(R:A->A->bool) x z. l4_vrt_closure972 R x z ==> l4_vrtc_hd972 R x z`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN
  MESON_TAC [l4_vrtch_rfl972;l4_vrtch_snoc_ind972]);;

let l4_vrtc_of_hd_ind972 = prove
 (`!(R:A->A->bool) x z. l4_vrtc_hd972 R x z ==> l4_vrt_closure972 R x z`,
  MATCH_MP_TAC l4_vrtc_hd_INDUCT972 THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_head972]);;

let l4_vrtc_head_ind_aux972 = prove
 (`!(R:A->A->bool) (P:A->A->bool).
   (!x. P x x) /\
   (!x y z. R x y /\ l4_vrt_closure972 R y z /\ P y z ==> P x z) ==>
   (!R0 x z. l4_vrtc_hd972 R0 x z ==> (R0 = R ==> P x z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC l4_vrtc_hd_STRONG_INDUCT972 THEN
  ASM_MESON_TAC [l4_vrtc_of_hd_ind972]);;

let l4_vrtc_head_ind972 = prove
 (`!(R:A->A->bool) (P:A->A->bool).
   (!x. P x x) /\
   (!x y z. R x y /\ l4_vrt_closure972 R y z /\ P y z ==> P x z) ==>
   (!x z. l4_vrt_closure972 R x z ==> P x z)`,
  MESON_TAC [l4_vrtc_head_ind_aux972;l4_vrtc_to_hd_ind972]);;

(* Pattern RHS & Matches Typing Helpers *)

let l4_vis_defeq_apply_pat_ind972 = prove
 (`!r env uvars g p m1 m2 m2' ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vrhs_wf972 p r /\
   (!path ty0. l4_vpath_valid972 p path /\
               l4_vhas_type961 env uvars g (m2 path) ty0 ==>
               l4_vis_defeq_u961 env uvars g (m2 path) (m2' path)) /\
   l4_vhas_type961 env uvars g (l4_vrhs_apply972 m1 m2 r) ty ==>
   l4_vis_defeq961 env uvars g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m2' r) ty`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN SIMP_TAC [];
   MAP_EVERY X_GEN_TAC [`rf:l4_vrhs972`;`ra:l4_vrhs972`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `l4_vrhs_apply972 m1 m2 rf`;`l4_vrhs_apply972 m1 m2 ra`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`L4VApp961 (l4_vrhs_apply972 m1 m2 rf) (l4_vrhs_apply972 m1 m2 ra)`;
                         `l4_vinst0961 cod0 (l4_vrhs_apply972 m1 m2 ra)`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom0:l4_vexpr961` THEN
   ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
   ASM_MESON_TAC []]);;

let l4_vis_defeq_apply_pat972 = prove
 (`!env uvars g p m1 m2 m2' r ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vrhs_wf972 p r /\
   (!path ty0. l4_vpath_valid972 p path /\
               l4_vhas_type961 env uvars g (m2 path) ty0 ==>
               l4_vis_defeq_u961 env uvars g (m2 path) (m2' path)) /\
   l4_vhas_type961 env uvars g (l4_vrhs_apply972 m1 m2 r) ty ==>
   l4_vis_defeq961 env uvars g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m2' r) ty`,
  MESON_TAC [l4_vis_defeq_apply_pat_ind972]);;

let l4_vpattern_matches_has_type_ind972 = prove
 (`!p e m1 m2.
   l4_vpattern_matches972 p e m1 m2 ==>
   (!env uvars g ty x.
      l4_venv_wf966 env /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e ty /\
      l4_vpath_valid972 p x ==>
      ?ty_a. l4_vhas_type961 env uvars g (m2 x) ty_a)`,
  MATCH_MP_TAC l4_vpattern_matches_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vpath_valid_clauses972];
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`ty:l4_vexpr961`;`x:bool list`] THEN
   STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THENL
   [STRIP_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `f':l4_vexpr961`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
      (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `dom0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
    REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `f':l4_vexpr961`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
      (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    ASM_MESON_TAC []];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`ty:l4_vexpr961`;`x:bool list`] THEN
   STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
   STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
   REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f':l4_vexpr961`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   ASM_MESON_TAC []]);;

let l4_vpattern_matches_has_type972 = prove
 (`!env uvars g p e m1 m2 ty a.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vpattern_matches972 p e m1 m2 /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpath_valid972 p a ==>
   ?ty_a. l4_vhas_type961 env uvars g (m2 a) ty_a`,
  MESON_TAC [l4_vpattern_matches_has_type_ind972]);;

(* NormalEq: Equivalence on Normal/Neutral Forms up to Levels, Eta, ProofIrrel *)

let l4_vnormal_eq_RULES972,l4_vnormal_eq_INDUCT972,l4_vnormal_eq_CASES972 =
  new_inductive_definition
 `(!env uvars g e ty.
     l4_vhas_type961 env uvars g e ty ==>
     l4_vnormal_eq972 env uvars g e e) /\
  (!env uvars g l1 l2.
     l4_vlevel_wf961 uvars l1 /\
     l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_vnormal_eq972 env uvars g (L4VSort961 l1) (L4VSort961 l2)) /\
  (!env uvars g c ci ls ls'.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     ALL (l4_vlevel_wf961 uvars) ls' /\
     LENGTH ls = l4_vc_uvars961 ci /\
     ALL2 l4_vlevel_equiv961 ls ls' ==>
     l4_vnormal_eq972 env uvars g (L4VConst961 c ls) (L4VConst961 c ls')) /\
  (!env uvars g f1 f2 x1 x2 dom cod.
     l4_vhas_type961 env uvars g f1 (L4VForallE961 dom cod) /\
     l4_vhas_type961 env uvars g f2 (L4VForallE961 dom cod) /\
     l4_vhas_type961 env uvars g x1 dom /\
     l4_vhas_type961 env uvars g x2 dom /\
     l4_vnormal_eq972 env uvars g f1 f2 /\
     l4_vnormal_eq972 env uvars g x1 x2 ==>
     l4_vnormal_eq972 env uvars g (L4VApp961 f1 x1) (L4VApp961 f2 x2)) /\
  (!env uvars g dom dom1 dom2 b1 b2 u.
     l4_vis_defeq961 env uvars g dom dom1 (L4VSort961 u) /\
     l4_vis_defeq961 env uvars g dom dom2 (L4VSort961 u) /\
     l4_vnormal_eq972 env uvars (CONS dom g) b1 b2 ==>
     l4_vnormal_eq972 env uvars g (L4VLam961 dom1 b1) (L4VLam961 dom2 b2)) /\
  (!env uvars g dom dom1 dom2 cod1 cod2 u v.
     l4_vis_defeq961 env uvars g dom dom1 (L4VSort961 u) /\
     l4_vnormal_eq972 env uvars g dom1 dom2 /\
     l4_vhas_type961 env uvars (CONS dom g) cod1 (L4VSort961 v) /\
     l4_vnormal_eq972 env uvars (CONS dom g) cod1 cod2 ==>
     l4_vnormal_eq972 env uvars g (L4VForallE961 dom1 cod1) (L4VForallE961 dom2 cod2)) /\
  (!env uvars g e' dom cod e.
     l4_vhas_type961 env uvars g e' (L4VForallE961 dom cod) /\
     l4_vnormal_eq972 env uvars (CONS dom g) e (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) ==>
     l4_vnormal_eq972 env uvars g (L4VLam961 dom e) e') /\
  (!env uvars g e' dom cod e.
     l4_vhas_type961 env uvars g e' (L4VForallE961 dom cod) /\
     l4_vnormal_eq972 env uvars (CONS dom g) (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) e ==>
     l4_vnormal_eq972 env uvars g e' (L4VLam961 dom e)) /\
  (!env uvars g p h h'.
     l4_vhas_type961 env uvars g p (L4VSort961 L4VLZero961) /\
     l4_vhas_type961 env uvars g h p /\
     l4_vhas_type961 env uvars g h' p ==>
     l4_vnormal_eq972 env uvars g h h')`;;

let l4_vn_refl972,
    l4_vn_sortDF972,
    l4_vn_constDF972,
    l4_vn_appDF972,
    l4_vn_lamDF972,
    l4_vn_forallEDF972,
    l4_vn_etaL972,
    l4_vn_etaR972,
    l4_vn_proofIrrel972 =
  match CONJUNCTS l4_vnormal_eq_RULES972 with
  | [c1;c2;c3;c4;c5;c6;c7;c8;c9] -> (c1,c2,c3,c4,c5,c6,c7,c8,c9)
  | _ -> failwith "l4_vnormal_eq_RULES972: unexpected arity";;

let l4_vnormal_eq_STRONG_INDUCT972 =
  derive_strong_induction (l4_vnormal_eq_RULES972, l4_vnormal_eq_INDUCT972);;

let l4_vnormal_eq_defeq_ind972 = prove
 (`!env uvars g e1 e2.
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   (l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_vctx_wf966 env uvars g ==>
    l4_vis_defeq_u961 env uvars g e1 e2)`,
  MATCH_MP_TAC l4_vnormal_eq_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   REWRITE_TAC [l4_vhas_type961;l4_vis_defeq_u961] THEN MESON_TAC [];
   (* sortDF *)
   REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_sort961];
   (* constDF *)
   REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_const961];
   (* appDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `l4_vinst0961 cod x1` THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
   EXISTS_TAC `dom:l4_vexpr961` THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_SIMP_TAC [];
   (* lamDF *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   SUBGOAL_THEN `?cod. l4_vis_defeq961 env uvars (CONS dom g) b1 b2 cod`
     (X_CHOOSE_TAC `cod:l4_vexpr961`) THENL
   [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom cod` THEN
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `L4VLam961 dom b2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_SIMP_TAC [l4_vis_defeq_symm961];
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961]];
   (* forallEDF *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `L4VForallE961 dom cod1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vis_defeq_forall961 THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN ASM_SIMP_TAC [];
     MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_SIMP_TAC []]];
   (* etaL *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?ty_c. l4_vis_defeq961 env uvars (CONS dom g) e
                          (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) ty_c`
     (X_CHOOSE_TAC `ty_c:l4_vexpr961`) THENL
   [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom cod` THEN
   MATCH_MP_TAC l4_vis_defeq_trans_u_r972 THEN
   EXISTS_TAC `L4VLam961 dom (L4VApp961 (l4_vlift961 e') (L4VBVar961 0))` THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
   [EXISTS_TAC `L4VForallE961 dom ty_c` THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vis_defeq_eta961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* etaR *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?ty_c. l4_vis_defeq961 env uvars (CONS dom g)
                          (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) e ty_c`
     (X_CHOOSE_TAC `ty_c:l4_vexpr961`) THENL
   [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom cod` THEN
   MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN
   EXISTS_TAC `L4VLam961 dom (L4VApp961 (l4_vlift961 e') (L4VBVar961 0))` THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_eta961 THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    EXISTS_TAC `L4VForallE961 dom ty_c` THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* proofIrrel *)
   REWRITE_TAC [l4_vis_defeq_u961;l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_proof_irrel961]]);;

let l4_vnormal_eq_defeq972 = prove
 (`!env uvars g e1 e2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   l4_vis_defeq_u961 env uvars g e1 e2`,
  MESON_TAC [l4_vnormal_eq_defeq_ind972]);;

let l4_vnormal_eq_symm_ind972 = prove
 (`!env uvars g e1 e2.
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   (l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_vctx_wf966 env uvars g ==>
    l4_vnormal_eq972 env uvars g e2 e1)`,
  MATCH_MP_TAC l4_vnormal_eq_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   MESON_TAC [l4_vn_refl972];
   (* sortDF *)
   MESON_TAC [l4_vn_sortDF972;l4_vlevel_equiv_symm961];
   (* constDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_constDF972 THEN
   EXISTS_TAC `ci:l4_vconstant961` THEN ASM_SIMP_TAC [l4_all2_vlevel_equiv_symm970] THEN
   ASM_MESON_TAC [l4_all2_length_eq970];
   (* appDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_appDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN ASM_SIMP_TAC [];
   (* lamDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_lamDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_MESON_TAC [l4_vis_defeq_refl_l961];
   (* forallEDF *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    ASM_SIMP_TAC [];
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `cod1:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    ASM_SIMP_TAC []];
   (* etaL *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* etaR *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* proofIrrel *)
   MESON_TAC [l4_vn_proofIrrel972]]);;

let l4_vnormal_eq_symm972 = prove
 (`!env uvars g e1 e2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   l4_vnormal_eq972 env uvars g e2 e1`,
  MESON_TAC [l4_vnormal_eq_symm_ind972]);;

let l4_vis_defeq_weakN_sort972 = prove
 (`!env uvars g e1 e2 u n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_defeq961 env uvars g e1 e2 (L4VSort961 u) ==>
   l4_vis_defeq961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) (L4VSort961 u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;
                 `L4VSort961 u`;`n:num`;`k:num`;`g':l4_vexpr961 list`] l4_vis_defeq_weakN966) THEN
  ASM_REWRITE_TAC [l4_vliftN961]);;

let l4_vis_defeq_weakN_forall972 = prove
 (`!env uvars g e1 e2 dom cod n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_defeq961 env uvars g e1 e2 (L4VForallE961 dom cod) ==>
   l4_vis_defeq961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)
     (L4VForallE961 (l4_vliftN961 dom n k) (l4_vliftN961 cod n (SUC k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;
                 `L4VForallE961 dom cod`;`n:num`;`k:num`;`g':l4_vexpr961 list`] l4_vis_defeq_weakN966) THEN
  ASM_REWRITE_TAC [l4_vliftN961]);;

let l4_vis_defeq_instN_sort972 = prove
 (`!env uvars g0 e0 a0 g1 e1 e2 u k g.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_defeq961 env uvars g1 e1 e2 (L4VSort961 u) ==>
   l4_vis_defeq961 env uvars g (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k) (L4VSort961 u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                 `g1:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;`L4VSort961 u`;
                 `k:num`;`g:l4_vexpr961 list`] l4_vis_defeq_instN966) THEN
  ASM_REWRITE_TAC [l4_vinst961]);;

let l4_vis_defeq_instN_forall972 = prove
 (`!env uvars g0 e0 a0 g1 e1 e2 dom cod k g.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_defeq961 env uvars g1 e1 e2 (L4VForallE961 dom cod) ==>
   l4_vis_defeq961 env uvars g (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k)
     (L4VForallE961 (l4_vinst961 dom e0 k) (l4_vinst961 cod e0 (SUC k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                 `g1:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`;`L4VForallE961 dom cod`;
                 `k:num`;`g:l4_vexpr961 list`] l4_vis_defeq_instN966) THEN
  ASM_REWRITE_TAC [l4_vinst961]);;

let l4_vnormal_eq_weakN_ind972 = prove
 (`!env uvars g e1 e2.
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   (!n k g'.
      l4_venv_wf966 env /\
      l4_vctx_liftN966 n k g g' ==>
      l4_vnormal_eq972 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vnormal_eq_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_refl972 THEN
   EXISTS_TAC `l4_vliftN961 ty n k` THEN REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_weakN966 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
   (* sortDF *)
   REWRITE_TAC [l4_vliftN961] THEN MESON_TAC [l4_vn_sortDF972];
   (* constDF *)
   REWRITE_TAC [l4_vliftN961] THEN MESON_TAC [l4_vn_constDF972];
   (* appDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 dom n k`;`l4_vliftN961 cod n (SUC k)`] THEN
   ASM_SIMP_TAC [] THEN
   REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THENL
   [MATCH_MP_TAC l4_vis_defeq_weakN_forall972;
    MATCH_MP_TAC l4_vis_defeq_weakN_forall972;
    MATCH_MP_TAC l4_vis_defeq_weakN966;
    MATCH_MP_TAC l4_vis_defeq_weakN966] THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
   (* lamDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vn_lamDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 dom n k`;`u:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_weakN_sort972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vis_defeq_weakN_sort972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966]];
   (* forallEDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 dom n k`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_weakN_sort972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966];
    ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN_sort972 THEN
    EXISTS_TAC `CONS (dom:l4_vexpr961) g` THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vctx_liftN_succ966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966]];
   (* etaL *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `l4_vliftN961 cod n (SUC k)` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN_forall972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`SUC k`;`CONS (l4_vliftN961 dom n k) g'`]) THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966]];
   (* etaR *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `l4_vliftN961 cod n (SUC k)` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN_forall972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`SUC k`;`CONS (l4_vliftN961 dom n k) g'`]) THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966]];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_proofIrrel972 THEN
   EXISTS_TAC `l4_vliftN961 p n k` THEN
   REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THENL
   [MATCH_MP_TAC l4_vis_defeq_weakN_sort972;
    MATCH_MP_TAC l4_vis_defeq_weakN966;
    MATCH_MP_TAC l4_vis_defeq_weakN966] THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]]);;

let l4_vnormal_eq_weakN972 = prove
 (`!env uvars n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   l4_vnormal_eq972 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_vnormal_eq_weakN_ind972]);;

let l4_vnormal_eq_instN_ind972 = prove
 (`!env uvars g e1 e2.
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   (!g0 e0 a0 k g'.
      l4_venv_wf966 env /\
      l4_vhas_type961 env uvars g0 e0 a0 /\
      l4_vctx_instN966 g0 e0 a0 k g g' ==>
      l4_vnormal_eq972 env uvars g' (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k))`,
  MATCH_MP_TAC l4_vnormal_eq_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_refl972 THEN
   EXISTS_TAC `l4_vinst961 ty e0 k` THEN REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_instN966 THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
   (* sortDF *)
   REWRITE_TAC [l4_vinst961] THEN MESON_TAC [l4_vn_sortDF972];
   (* constDF *)
   REWRITE_TAC [l4_vinst961] THEN MESON_TAC [l4_vn_constDF972];
   (* appDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom e0 k`;`l4_vinst961 cod e0 (SUC k)`] THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_forall972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_forall972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    ASM_MESON_TAC [];
    ASM_MESON_TAC []];
   (* lamDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_lamDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom e0 k`;`u:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`] THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966]];
   (* forallEDF *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom e0 k`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vctx_instN_succ966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`] THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966]];
   (* etaL *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `l4_vinst961 cod e0 (SUC k)` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_forall972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM (MP_TAC o SPECL [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                                   `SUC k`;`CONS (l4_vinst961 dom e0 k) g'`]) THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966;l4_vinst961;l4_vinst_var961;LT_0;l4_vinst_vlift_succ966]];
   (* etaR *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `l4_vinst961 cod e0 (SUC k)` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_forall972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM (MP_TAC o SPECL [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                                   `SUC k`;`CONS (l4_vinst961 dom e0 k) g'`]) THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966;l4_vinst961;l4_vinst_var961;LT_0;l4_vinst_vlift_succ966]];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_proofIrrel972 THEN
   EXISTS_TAC `l4_vinst961 p e0 k` THEN
   REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THENL
   [MATCH_MP_TAC l4_vis_defeq_instN_sort972;
    MATCH_MP_TAC l4_vis_defeq_instN966;
    MATCH_MP_TAC l4_vis_defeq_instN966] THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g:l4_vexpr961 list`] THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]]);;

let l4_vnormal_eq_instN972 = prove
 (`!env uvars g0 e0 a0 k g1 g e1 e2.
   l4_venv_wf966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vnormal_eq972 env uvars g1 e1 e2 ==>
   l4_vnormal_eq972 env uvars g (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k)`,
  MESON_TAC [l4_vnormal_eq_instN_ind972]);;

let l4_vnormal_eq_instN_r_bvar_ind972 = prove
 (`!g0 e0 a0 k g1 g.
   l4_vctx_instN966 g0 e0 a0 k g1 g ==>
   (!env uvars e0' i ty.
      l4_venv_wf966 env /\
      l4_vnormal_eq972 env uvars g0 e0 e0' /\
      l4_vlookup961 g1 i ty ==>
      l4_vnormal_eq972 env uvars g (l4_vinst_var961 i e0 k) (l4_vinst_var961 i e0' k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [distinctness "list";injectivity "list"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [REWRITE_TAC [l4_vinst_var961;LT_REFL;l4_vliftN_zero961] THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vinst_var961;LT;NOT_SUC;SUC_SUB1] THEN
    ASM_MESON_TAC [l4_vn_refl972;l4_vhas_type961;l4_vis_defeq_bvar961]];
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [distinctness "list";injectivity "list"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [REWRITE_TAC [l4_vinst_var961;LT_0] THEN
    ASM_MESON_TAC [l4_vn_refl972;l4_vhas_type961;l4_vis_defeq_bvar961;l4_vlookup_zero961];
    REWRITE_TAC [l4_vinst_var_succ966;l4_vlift961] THEN
    ASM_MESON_TAC [l4_vnormal_eq_weakN972;l4_vctx_liftN_one966]]]);;

let l4_vnormal_eq_instN_r_ind972 = prove
 (`!e env uvars g0 e0 e0' ty0 k g1 g ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g1 /\
   l4_vhas_type961 env uvars g0 e0 ty0 /\
   l4_vnormal_eq972 env uvars g0 e0 e0' /\
   l4_vctx_instN966 g0 e0 ty0 k g1 g /\
   l4_vhas_type961 env uvars g1 e ty ==>
   l4_vnormal_eq972 env uvars g (l4_vinst961 e e0 k) (l4_vinst961 e e0' k)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;`a:num`;`ty:l4_vexpr961`]
     l4_vhas_type_bvar_inv970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `ty1:l4_vexpr961`) THEN
   ASM_MESON_TAC [l4_vnormal_eq_instN_r_bvar_ind972];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `L4VSort961 (L4VLSucc961 a)` THEN
   MATCH_MP_TAC l4_vhas_type_sort972 THEN
   ASM_MESON_TAC [l4_vhas_type961;l4_vis_defeq_sort_inv_l972];
   (* const *)
   MAP_EVERY X_GEN_TAC [`c:l4_name`;`ls:l4_vlevel961 list`] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `c:l4_name`;`ls:l4_vlevel961 list`;`ty:l4_vexpr961`]
     l4_vhas_type_const_inv970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `l4_vinstL961 ls (l4_vc_type961 ci)` THEN
   MATCH_MP_TAC l4_vhas_type_const972 THEN ASM_REWRITE_TAC [];
   (* app *)
   MAP_EVERY X_GEN_TAC [`fn:l4_vexpr961`;`arg:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `fn:l4_vexpr961`;`arg:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom1:l4_vexpr961`
     (X_CHOOSE_THEN `cod1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vnormal_eq972 env uvars g (l4_vinst961 fn e0 k) (l4_vinst961 fn e0' k) /\
                 l4_vnormal_eq972 env uvars g (l4_vinst961 arg e0 k) (l4_vinst961 arg e0' k)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g (l4_vinst961 fn e0 k)
                   (L4VForallE961 (l4_vinst961 dom1 e0 k) (l4_vinst961 cod1 e0 (SUC k))) /\
                 l4_vhas_type961 env uvars g (l4_vinst961 arg e0 k) (l4_vinst961 dom1 e0 k)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THENL
    [MATCH_MP_TAC l4_vis_defeq_instN_forall972; MATCH_MP_TAC l4_vis_defeq_instN966] THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_instN_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom1 e0 k`;`l4_vinst961 cod1 e0 (SUC k)`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THENL
   [EXISTS_TAC `l4_vinst961 fn e0 k` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    EXISTS_TAC `l4_vinst961 arg e0 k` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u1:l4_vlevel961`) (X_CHOOSE_TAC `cod1:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g (l4_vinst961 dom e0 k) (L4VSort961 u1)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_instN_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vnormal_eq972 env uvars g (l4_vinst961 dom e0 k) (l4_vinst961 dom e0' k)`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_lamDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom e0 k`;`u1:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;
                          `CONS (dom:l4_vexpr961) g1`;`cod1:l4_vexpr961`] THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966] THEN
    MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u1:l4_vlevel961` THEN ASM_REWRITE_TAC []];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u1:l4_vlevel961`) (X_CHOOSE_TAC `v1:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom e0 k`;`u1:l4_vlevel961`;`v1:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN_sort972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;`CONS (dom:l4_vexpr961) g1`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vctx_instN_succ966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty0:l4_vexpr961`;
                          `CONS (dom:l4_vexpr961) g1`;`L4VSort961 v1`] THEN
    ASM_SIMP_TAC [l4_vctx_instN_succ966] THEN
    MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u1:l4_vlevel961` THEN ASM_REWRITE_TAC []]]);;

let l4_vnormal_eq_instN_r972 = prove
 (`!env uvars g0 e0 e0' a0 k g1 g e ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g1 /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vnormal_eq972 env uvars g0 e0 e0' /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vhas_type961 env uvars g1 e ty ==>
   l4_vnormal_eq972 env uvars g (l4_vinst961 e e0 k) (l4_vinst961 e e0' k)`,
  MESON_TAC [l4_vnormal_eq_instN_r_ind972]);;

let l4_vnormal_eq_defeqDFC_ind972 = prove
 (`!env uvars g1 e1 e2.
   l4_vnormal_eq972 env uvars g1 e1 e2 ==>
   (!g0 g2.
      l4_venv_wf966 env /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
      l4_vnormal_eq972 env uvars g2 e1 e2)`,
  MATCH_MP_TAC l4_vnormal_eq_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
   (* sortDF *)
   MESON_TAC [l4_vn_sortDF972];
   (* constDF *)
   MESON_TAC [l4_vn_constDF972];
   (* appDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_appDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    ASM_MESON_TAC [];
    ASM_MESON_TAC []];
   (* lamDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_lamDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]];
   (* forallEDF *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]];
   (* etaL *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* etaR *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
   REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g:l4_vexpr961 list`] THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]]);;

let l4_vnormal_eq_defeqDFC972 = prove
 (`!env uvars g0 g1 g2 e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vnormal_eq972 env uvars g1 e1 e2 ==>
   l4_vnormal_eq972 env uvars g2 e1 e2`,
  MESON_TAC [l4_vnormal_eq_defeqDFC_ind972]);;

let l4_vnormal_eq_defeq_l972 = prove
 (`!env uvars g a a' u e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g a a' (L4VSort961 u) /\
   l4_vnormal_eq972 env uvars (CONS a g) e1 e2 ==>
   l4_vnormal_eq972 env uvars (CONS a' g) e1 e2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vnormal_eq_defeqDFC972 THEN
  MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (a:l4_vexpr961) g`] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
  EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966]);;

let l4_vnormal_eq_weakN_inv_DFC_ind972 = prove
 (`!env uvars g1 e1' e2'.
   l4_vnormal_eq972 env uvars g1 e1' e2' ==>
   (!n k g g0 g2 e1 e2.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vctx_liftN966 n k g g2 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      e1' = l4_vliftN961 e1 n k /\
      e2' = l4_vliftN961 e2 n k ==>
      l4_vnormal_eq972 env uvars g e1 e2)`,
  MATCH_MP_TAC l4_vnormal_eq_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `e:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `e1:l4_vexpr961 = e2` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_vliftN_inj969]; ALL_TAC] THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g e2 e2` MP_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;`e2:l4_vexpr961`;`e2:l4_vexpr961`]
      l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN MESON_TAC [l4_vn_refl972]];
   (* sortDF *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vn_sortDF972 THEN ASM_REWRITE_TAC [];
   (* constDF *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vn_constDF972 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* appDF *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `f1':l4_vexpr961`;`f2':l4_vexpr961`;`x1':l4_vexpr961`;`x2':l4_vexpr961`;
                        `dom':l4_vexpr961`;`cod':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_wf_weakN_inv972]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 env uvars g2 (l4_vliftN961 a0 n k) (L4VForallE961 dom' cod') /\
      l4_vhas_type961 env uvars g2 (l4_vliftN961 a0' n k) (L4VForallE961 dom' cod') /\
      l4_vhas_type961 env uvars g2 (l4_vliftN961 a1 n k) dom' /\
      l4_vhas_type961 env uvars g2 (l4_vliftN961 a1' n k) dom'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN
     `(?al bl. l4_vhas_type961 env uvars g a0 (L4VForallE961 al bl) /\
               l4_vhas_type961 env uvars g a1 al) /\
      (?ar br. l4_vhas_type961 env uvars g a0' (L4VForallE961 ar br) /\
               l4_vhas_type961 env uvars g a1' ar)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [SUBGOAL_THEN `?ty_l. l4_vis_defeq961 env uvars g (L4VApp961 a0 a1) (L4VApp961 a0 a1) ty_l`
       (X_CHOOSE_TAC `ty_l:l4_vexpr961`) THENL
     [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                     `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                     `L4VApp961 a0 a1`;`L4VApp961 a0 a1`] l4_vis_defeq_u_weakN_iff972) THEN
      ASM_REWRITE_TAC [l4_vliftN961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
      EXISTS_TAC `l4_vinst0961 cod' (l4_vliftN961 a1 n k)` THEN
      MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vhas_type_app_inv970 THEN
      EXISTS_TAC `ty_l:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vhas_type961]];
     SUBGOAL_THEN `?ty_r. l4_vis_defeq961 env uvars g (L4VApp961 a0' a1') (L4VApp961 a0' a1') ty_r`
       (X_CHOOSE_TAC `ty_r:l4_vexpr961`) THENL
     [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                     `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                     `L4VApp961 a0' a1'`;`L4VApp961 a0' a1'`] l4_vis_defeq_u_weakN_iff972) THEN
      ASM_REWRITE_TAC [l4_vliftN961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
      EXISTS_TAC `l4_vinst0961 cod' (l4_vliftN961 a1' n k)` THEN
      MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vhas_type_app_inv970 THEN
      EXISTS_TAC `ty_r:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vhas_type961]]]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 al bl) (L4VForallE961 ar br)`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `L4VForallE961 al bl`;`L4VForallE961 ar br`] l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VForallE961 dom' cod'` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`l4_vliftN961 a0 n k`;`l4_vliftN961 a0 n k`;`l4_vliftN961 a0 n k`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
     EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`l4_vliftN961 a0' n k`;`l4_vliftN961 a0' n k`;`l4_vliftN961 a0' n k`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
     EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]]; ALL_TAC] THEN
   SUBGOAL_THEN `?u0. l4_vis_defeq961 env uvars g al ar (L4VSort961 u0)`
     (X_CHOOSE_TAC `u0:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_forallE_inv972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN MAP_EVERY EXISTS_TAC [`ar:l4_vexpr961`;`br:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `L4VForallE961 al bl` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `al:l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 u0` THEN ASM_REWRITE_TAC [];
    FIRST_ASSUM (fun th -> MATCH_MP_TAC th THEN
      MAP_EVERY EXISTS_TAC [`n:num`;`k:num`;`g0:l4_vexpr961 list`;`g2:l4_vexpr961 list`] THEN
      ASM_REWRITE_TAC [] THEN NO_TAC);
    FIRST_ASSUM (fun th -> MATCH_MP_TAC th THEN
      MAP_EVERY EXISTS_TAC [`n:num`;`k:num`;`g0:l4_vexpr961 list`;`g2:l4_vexpr961 list`] THEN
      ASM_REWRITE_TAC [] THEN NO_TAC)];
   (* lamDF *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `dom':l4_vexpr961`;`dom1':l4_vexpr961`;`dom2':l4_vexpr961`;
                        `b1':l4_vexpr961`;`b2':l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g a0' a0 (L4VSort961 u)` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `a0':l4_vexpr961`;`a0:l4_vexpr961`;`L4VSort961 u`]
      l4_vis_defeq_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vliftN961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vis_defeq_symm961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_lamDF972 THEN MAP_EVERY EXISTS_TAC [`a0':l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`;`SUC k`;`g0:l4_vexpr961 list`;`CONS (l4_vliftN961 a0' n k) g2`] THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN
    MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
   (* forallEDF *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `dom':l4_vexpr961`;`dom1':l4_vexpr961`;`dom2':l4_vexpr961`;
                        `cod1':l4_vexpr961`;`cod2':l4_vexpr961`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_ctx966 env uvars g0 (CONS dom' g1) (CONS (l4_vliftN961 a0 n k) g2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS (l4_vliftN961 a0 n k) g2)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_wf966]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`a0:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `a0:l4_vexpr961`;`L4VSort961 u`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vliftN961;l4_vhas_type961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961];
    FIRST_ASSUM (fun th -> MATCH_MP_TAC th THEN
      MAP_EVERY EXISTS_TAC [`n:num`;`k:num`;`g0:l4_vexpr961 list`;`g2:l4_vexpr961 list`] THEN
      ASM_REWRITE_TAC [] THEN NO_TAC);
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`SUC k`;
                   `CONS (a0:l4_vexpr961) g`;`CONS (l4_vliftN961 a0 n k) g2`;
                   `a1:l4_vexpr961`;`L4VSort961 v`] l4_vhas_type_weakN_iff972) THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;l4_vliftN961;l4_vhas_type961] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`CONS (dom':l4_vexpr961) g1`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    FIRST_ASSUM (fun th -> MATCH_MP_TAC th THEN
      MAP_EVERY EXISTS_TAC [`n:num`;`SUC k`;`g0:l4_vexpr961 list`;`CONS (l4_vliftN961 a0 n k) g2`] THEN
      ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN NO_TAC)];
   (* etaL *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `e2':l4_vexpr961`;`dom':l4_vexpr961`;`cod':l4_vexpr961`;`b1':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `l4_vliftN961 e2 n k`;`l4_vliftN961 e2 n k`;
                  `L4VForallE961 (l4_vliftN961 a0 n k) cod'`] l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `l4_vliftN961 a0 n k`;`cod':l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g2 (l4_vliftN961 e2 n k)
                   (L4VForallE961 (l4_vliftN961 a0 n k) cod') /\
                 l4_vhas_type961 env uvars g2 (l4_vliftN961 a0 n k) (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS (l4_vliftN961 a0 n k) g2)
                   (l4_vliftN961 (L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)) n (SUC k)) cod'`
     ASSUME_TAC THENL
    [REWRITE_TAC [l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966] THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (l4_vliftN961 a0 n k) g2`;
                    `l4_vlift961 (l4_vliftN961 e2 n k)`;`L4VBVar961 0`;
                    `l4_vlift961 (l4_vliftN961 a0 n k)`;`l4_vliftN961 cod' 1 1`] l4_vhas_type_app972) THEN
     REWRITE_TAC [l4_vinst0961;REWRITE_RULE [GSYM ONE] (SPECL [`cod':l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966)] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THENL
     [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
      MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
      REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
      REWRITE_TAC [l4_vlookup_zero961]]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_ctx966 env uvars g0
                   (CONS (l4_vliftN961 a0 n k) g1) (CONS (l4_vliftN961 a0 n k) g2)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS (l4_vliftN961 a0 n k) g2)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_wf966]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?c0. l4_vhas_type961 env uvars (CONS a0 g)
                        (L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)) c0`
     (X_CHOOSE_TAC `c0:l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vhas_type961;GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`SUC k`;
                   `CONS (a0:l4_vexpr961) g`;`CONS (l4_vliftN961 a0 n k) g2`;
                   `L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)`;
                   `L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)`] l4_vis_defeq_u_weakN_iff972) THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
    EXISTS_TAC `cod':l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?w. l4_vis_defeq961 env uvars (CONS (l4_vliftN961 a0 n k) g2)
                       cod' (l4_vliftN961 c0 n (SUC k)) (L4VSort961 w)`
     (X_CHOOSE_TAC `w:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC
      [`l4_vliftN961 (L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)) n (SUC k)`;
       `l4_vliftN961 (L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)) n (SUC k)`;
       `l4_vliftN961 (L4VApp961 (l4_vlift961 e2) (L4VBVar961 0)) n (SUC k)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `CONS (a0:l4_vexpr961) g` THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;GSYM l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `c0:l4_vexpr961` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `e2:l4_vexpr961`;`L4VForallE961 a0 c0`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vliftN961;l4_vhas_type961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VForallE961 (l4_vliftN961 a0 n k) cod'`;`L4VLIMax961 u w`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`;`SUC k`;`g0:l4_vexpr961 list`;`CONS (l4_vliftN961 a0 n k) g2`] THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966]];
   (* etaR *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `e1':l4_vexpr961`;`dom':l4_vexpr961`;`cod':l4_vexpr961`;`b2':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `l4_vliftN961 e1 n k`;`l4_vliftN961 e1 n k`;
                  `L4VForallE961 (l4_vliftN961 a0 n k) cod'`] l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `l4_vliftN961 a0 n k`;`cod':l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g2 (l4_vliftN961 e1 n k)
                   (L4VForallE961 (l4_vliftN961 a0 n k) cod') /\
                 l4_vhas_type961 env uvars g2 (l4_vliftN961 a0 n k) (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS (l4_vliftN961 a0 n k) g2)
                   (l4_vliftN961 (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) n (SUC k)) cod'`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (l4_vliftN961 a0 n k) g2`;
                   `l4_vlift961 (l4_vliftN961 e1 n k)`;`L4VBVar961 0`;
                   `l4_vlift961 (l4_vliftN961 a0 n k)`;`l4_vliftN961 cod' 1 1`] l4_vhas_type_app972) THEN
    REWRITE_TAC [l4_vinst0961;REWRITE_RULE [GSYM ONE] (SPECL [`cod':l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966)] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961]]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_ctx966 env uvars g0
                   (CONS (l4_vliftN961 a0 n k) g1) (CONS (l4_vliftN961 a0 n k) g2)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS (l4_vliftN961 a0 n k) g2)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_wf966]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?c0. l4_vhas_type961 env uvars (CONS a0 g)
                        (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) c0`
     (X_CHOOSE_TAC `c0:l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vhas_type961;GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`SUC k`;
                   `CONS (a0:l4_vexpr961) g`;`CONS (l4_vliftN961 a0 n k) g2`;
                   `L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)`;
                   `L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)`] l4_vis_defeq_u_weakN_iff972) THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
    EXISTS_TAC `cod':l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?w. l4_vis_defeq961 env uvars (CONS (l4_vliftN961 a0 n k) g2)
                       cod' (l4_vliftN961 c0 n (SUC k)) (L4VSort961 w)`
     (X_CHOOSE_TAC `w:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC
      [`l4_vliftN961 (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) n (SUC k)`;
       `l4_vliftN961 (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) n (SUC k)`;
       `l4_vliftN961 (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) n (SUC k)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `CONS (a0:l4_vexpr961) g` THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;GSYM l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `c0:l4_vexpr961` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `e1:l4_vexpr961`;`L4VForallE961 a0 c0`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vliftN961;l4_vhas_type961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VForallE961 (l4_vliftN961 a0 n k) cod'`;`L4VLIMax961 u w`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`;`SUC k`;`g0:l4_vexpr961 list`;`CONS (l4_vliftN961 a0 n k) g2`] THEN
    ASM_SIMP_TAC [l4_vctx_liftN_succ966;l4_vliftN961;l4_vlift_var961;LT_0;l4_vliftN_vlift966]];
   (* proofIrrel *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                        `p:l4_vexpr961`;`h1:l4_vexpr961`;`h2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`g0:l4_vexpr961 list`;
                        `g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g2` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 env uvars g2 p (L4VSort961 L4VLZero961) /\
      l4_vhas_type961 env uvars g2 (l4_vliftN961 e1 n k) p /\
      l4_vhas_type961 env uvars g2 (l4_vliftN961 e2 n k) p` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `?p0. l4_vhas_type961 env uvars g e1 p0` (X_CHOOSE_TAC `p0:l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vhas_type961;GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;`e1:l4_vexpr961`;`e1:l4_vexpr961`]
      l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
    EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?w. l4_vis_defeq961 env uvars g2 p (l4_vliftN961 p0 n k) (L4VSort961 w)`
     (X_CHOOSE_TAC `w:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vliftN961 e1 n k`;`l4_vliftN961 e1 n k`;`l4_vliftN961 e1 n k`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p0:l4_vexpr961` THEN REPEAT CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `p0:l4_vexpr961`;`L4VSort961 L4VLZero961`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vliftN961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w` THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                   `g:l4_vexpr961 list`;`g2:l4_vexpr961 list`;
                   `e2:l4_vexpr961`;`p0:l4_vexpr961`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vhas_type961] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vexpr961`;`w:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]]]);;

let l4_vnormal_eq_weakN_iff972 = prove
 (`!env uvars n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vnormal_eq972 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) <=>
    l4_vnormal_eq972 env uvars g e1 e2)`,
  MESON_TAC [l4_vnormal_eq_weakN_inv_DFC_ind972;l4_vnormal_eq_weakN972;l4_vis_defeq_ctx_zero966]);;

(* Transitivity of NormalEq via Measure Induction *)

let l4_vnorm_meas972 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vnorm_meas972 (L4VBVar961 i) = 0) /\
  (l4_vnorm_meas972 (L4VSort961 u) = 0) /\
  (l4_vnorm_meas972 (L4VConst961 c ls) = 0) /\
  (l4_vnorm_meas972 (L4VApp961 f a) = l4_vnorm_meas972 f + l4_vnorm_meas972 a + 1) /\
  (l4_vnorm_meas972 (L4VLam961 dom body) = l4_vnorm_meas972 dom + l4_vnorm_meas972 body + 3) /\
  (l4_vnorm_meas972 (L4VForallE961 dom cod) = l4_vnorm_meas972 dom + l4_vnorm_meas972 cod + 1)`;;

let l4_vnorm_meas_vliftN972 = prove
 (`!e n k. l4_vnorm_meas972 (l4_vliftN961 e n k) = l4_vnorm_meas972 e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN ASM_SIMP_TAC [l4_vliftN961;l4_vnorm_meas972]);;

let l4_vnorm_meas_vlift972 = prove
 (`!e. l4_vnorm_meas972 (l4_vlift961 e) = l4_vnorm_meas972 e`,
  REWRITE_TAC [l4_vlift961;l4_vnorm_meas_vliftN972]);;

let l4_vinst_vliftN_bvar0_11_972 =
  REWRITE_RULE [GSYM ONE] (GEN `e:l4_vexpr961` (SPECL [`e:l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966));;

let l4_vnormal_eq_trans_meas972 = prove
 (`!env uvars.
   l4_venv_wf966 env /\ l4_defeq_injectivity972 env ==>
   !m g e1 e2 e3.
     l4_vnorm_meas972 e1 + l4_vnorm_meas972 e2 + l4_vnorm_meas972 e3 <= m /\
     l4_vctx_wf966 env uvars g /\
     l4_vnormal_eq972 env uvars g e1 e2 /\
     l4_vnormal_eq972 env uvars g e2 e3 ==>
     l4_vnormal_eq972 env uvars g e1 e3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_closed966 env` ASSUME_TAC THENL
  [ASM_SIMP_TAC [l4_venv_wf_closed966]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_THEN (LABEL_TAC "HIH") THEN
  SUBGOAL_THEN
    `!g0 d1 d2 dom cod e.
       l4_vnorm_meas972 d1 + l4_vnorm_meas972 d2 + l4_vnorm_meas972 (L4VLam961 dom e) <= m /\
       l4_vctx_wf966 env uvars g0 /\
       l4_vnormal_eq972 env uvars g0 d1 d2 /\
       l4_vhas_type961 env uvars g0 d2 (L4VForallE961 dom cod) /\
       l4_vnormal_eq972 env uvars (CONS dom g0) (L4VApp961 (l4_vlift961 d2) (L4VBVar961 0)) e ==>
       l4_vnormal_eq972 env uvars g0 d1 (L4VLam961 dom e)`
    (LABEL_TAC "Heta") THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                  `d2:l4_vexpr961`;`d2:l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g0 d1 (L4VForallE961 dom cod)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `d2:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   USE_THEN "HIH" (MP_TAC o SPEC
     `l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d1) (L4VBVar961 0)) +
      l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d2) (L4VBVar961 0)) +
      l4_vnorm_meas972 e`) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `l4_vnorm_meas972 d1 + l4_vnorm_meas972 d2 + l4_vnorm_meas972 (L4VLam961 dom e) <= m` THEN
    REWRITE_TAC [l4_vnorm_meas972;l4_vnorm_meas_vlift972] THEN ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `L4VApp961 (l4_vlift961 d2) (L4VBVar961 0)` THEN
   ASM_REWRITE_TAC [LE_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_appDF972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vlift961 dom`;`l4_vliftN961 cod 1 1`] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961];
     REWRITE_TAC [l4_vlift961] THEN MATCH_MP_TAC l4_vnormal_eq_weakN972 THEN
     EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vctx_liftN_one966];
     MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `l4_vlift961 dom` THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961]]]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`d1:l4_vexpr961`;`d2:l4_vexpr961`;`d3:l4_vexpr961`] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hmeas")
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "H12") (LABEL_TAC "H23")))) THEN
  USE_THEN "H12" MP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
  [(* 1. refl on left *)
   ASM_REWRITE_TAC [];
   (* 2. sortDF on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_sortDF972 THEN ASM_MESON_TAC [l4_vlevel_equiv_trans961];
    ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VSort961 l2` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 3. constDF on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_constDF972 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
    ASM_MESON_TAC [l4_all2_vlevel_equiv_trans970];
    ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VConst961 c ls'` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 4. appDF on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_appDF972 THEN MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`cod':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `L4VForallE961 dom cod` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`f1':l4_vexpr961`;`f1':l4_vexpr961`;`f1':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`x1':l4_vexpr961`;`x1':l4_vexpr961`;`x1':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 f1 + l4_vnorm_meas972 f1' + l4_vnorm_meas972 f2'`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `f1':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL]];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 x1 + l4_vnorm_meas972 x1' + l4_vnorm_meas972 x2'`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `x1':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL]]];
    ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VApp961 f2 x2` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 5. lamDF on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    (* lamDF + lamDF *)
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g0 dom dom' (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
     MAP_EVERY EXISTS_TAC [`dom1':l4_vexpr961`;`L4VSort961 u'`] THEN
     ASM_SIMP_TAC [l4_vis_defeq_symm961]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vn_lamDF972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
     MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`L4VSort961 u'`] THEN
     ASM_REWRITE_TAC [];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 b1 + l4_vnorm_meas972 b1' + l4_vnorm_meas972 b2'`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972] THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `b1':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
      MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
      MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`u:l4_vlevel961`] THEN
      ASM_SIMP_TAC [l4_vis_defeq_symm961]]];
    (* lamDF + etaL *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `d3:l4_vexpr961`;`d3:l4_vexpr961`;`L4VForallE961 dom' cod`]
      l4_vis_defeq_is_type966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom':l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g0 dom' dom1 (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vis_defeq_symm961]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`L4VForallE961 dom' cod`;`L4VLIMax961 u v`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 b1 + l4_vnorm_meas972 e +
        l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d3) (L4VBVar961 0))`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972;l4_vnorm_meas_vlift972] THEN
      ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `e:l4_vexpr961` THEN REWRITE_TAC [LE_REFL] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961];
      MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
      MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC []]];
    (* lamDF + etaR *)
    ASM_MESON_TAC [];
    (* lamDF + proofIrrel *)
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VLam961 dom2 b2` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 6. forallEDF on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g0 dom' dom (L4VSort961 u')` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
     MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`L4VSort961 u`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom1':l4_vexpr961` THEN
      ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972];
      MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vn_forallEDF972 THEN
    MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 dom1 + l4_vnorm_meas972 dom1' + l4_vnorm_meas972 dom2'`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `dom1':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL]];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 cod1 + l4_vnorm_meas972 cod1' + l4_vnorm_meas972 cod2'`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `cod1':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
       ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
       MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
       MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`u':l4_vlevel961`] THEN ASM_REWRITE_TAC []]]];
    ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VForallE961 dom2 cod2` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 7. etaL on left *)
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                  `d2:l4_vexpr961`;`d2:l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g0 d3 (L4VForallE961 dom cod)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `d2:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   USE_THEN "HIH" (MP_TAC o SPEC
     `l4_vnorm_meas972 e +
      l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d2) (L4VBVar961 0)) +
      l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d3) (L4VBVar961 0))`) THEN
   ANTS_TAC THENL
   [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972;l4_vnorm_meas_vlift972] THEN
    ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L4VApp961 (l4_vlift961 d2) (L4VBVar961 0)` THEN
   ASM_REWRITE_TAC [LE_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_appDF972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vlift961 dom`;`l4_vliftN961 cod 1 1`] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961];
     REWRITE_TAC [l4_vlift961] THEN MATCH_MP_TAC l4_vnormal_eq_weakN972 THEN
     EXISTS_TAC `g0:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vctx_liftN_one966];
     MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `l4_vlift961 dom` THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961]]];
   (* 8. etaR on left *)
   REMOVE_THEN "H23" MP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [];
    (* etaR + lamDF *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `d1:l4_vexpr961`;`d1:l4_vexpr961`;`L4VForallE961 dom1 cod`]
      l4_vis_defeq_is_type966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom1:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g0 dom1 dom2 (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vis_defeq_symm961]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`L4VForallE961 dom1 cod`;`L4VLIMax961 u v`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d1) (L4VBVar961 0)) +
        l4_vnorm_meas972 b1 + l4_vnorm_meas972 b2`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972;l4_vnorm_meas_vlift972] THEN
      ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `b1:l4_vexpr961` THEN REWRITE_TAC [LE_REFL] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_MESON_TAC [l4_vis_defeq_refl_r961;l4_vhas_type961];
      MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
      MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vnormal_eq_defeq_l972 THEN
      MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC []]];
    (* etaR + etaL *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `d1:l4_vexpr961`;`d1:l4_vexpr961`;`L4VForallE961 dom' cod`]
      l4_vis_defeq_is_type966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom':l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom' g0)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vnormal_eq972 env uvars (CONS dom' g0)
                    (L4VApp961 (l4_vlift961 d1) (L4VBVar961 0))
                    (L4VApp961 (l4_vlift961 d3) (L4VBVar961 0))` MP_TAC THENL
    [USE_THEN "HIH" (MP_TAC o SPEC
       `l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d1) (L4VBVar961 0)) +
        l4_vnorm_meas972 e' +
        l4_vnorm_meas972 (L4VApp961 (l4_vlift961 d3) (L4VBVar961 0))`) THEN
     ANTS_TAC THENL
     [USE_THEN "Hmeas" MP_TAC THEN REWRITE_TAC [l4_vnorm_meas972;l4_vnorm_meas_vlift972] THEN
      ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `e':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL]];
     ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
    REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
    [(* refl *)
     SUBGOAL_THEN `d1:l4_vexpr961 = d3` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [l4_vliftN_inj969;l4_vlift961];
      MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `L4VForallE961 dom' cod'` THEN ASM_REWRITE_TAC []];
     (* appDF *)
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`0`;
                    `g0:l4_vexpr961 list`;`CONS (dom':l4_vexpr961) g0`;`d1:l4_vexpr961`;`d3:l4_vexpr961`]
       l4_vnormal_eq_weakN_iff972) THEN
     ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961];
     (* proofIrrel *)
     SUBGOAL_THEN `l4_vlevel_wf961 uvars u` ASSUME_TAC THENL
     [ASM_MESON_TAC [l4_vis_defeq_sort_r966;l4_vhas_type961]; ALL_TAC] THEN
     MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `L4VForallE961 dom' p` THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN
      EXISTS_TAC `L4VSort961 (L4VLIMax961 u L4VLZero961)` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
      [EXISTS_TAC `L4VSort961 (L4VLSucc961 (L4VLIMax961 u L4VLZero961))` THEN
       MATCH_MP_TAC l4_vis_defeq_sort961 THEN
       ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_imax_zero972];
       MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC []];
      MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
      EXISTS_TAC `L4VLam961 dom' (L4VApp961 (l4_vlift961 d1) (L4VBVar961 0))` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
      [EXISTS_TAC `L4VForallE961 dom' cod` THEN MATCH_MP_TAC l4_vis_defeq_eta961 THEN
       ASM_REWRITE_TAC [GSYM l4_vhas_type961];
       MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
      MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
      EXISTS_TAC `L4VLam961 dom' (L4VApp961 (l4_vlift961 d3) (L4VBVar961 0))` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
      [EXISTS_TAC `L4VForallE961 dom' cod'` THEN MATCH_MP_TAC l4_vis_defeq_eta961 THEN
       ASM_REWRITE_TAC [GSYM l4_vhas_type961];
       MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []]]];
    (* etaR + etaR *)
    ASM_MESON_TAC [];
    (* etaR + proofIrrel *)
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `L4VLam961 dom e` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972]];
   (* 9. proofIrrel on left *)
   MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `d2:l4_vexpr961` THEN
   ASM_SIMP_TAC [l4_vnormal_eq_defeq972]]);;

let l4_vnormal_eq_trans972 = prove
 (`!env uvars g e1 e2 e3.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 /\
   l4_vnormal_eq972 env uvars g e2 e3 ==>
   l4_vnormal_eq972 env uvars g e1 e3`,
  MESON_TAC [l4_vnormal_eq_trans_meas972;LE_REFL]);;

let l4_vnormal_eq_apply_pat_ind972 = prove
 (`!r env uvars g p m1 m2 m2' ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vrhs_wf972 p r /\
   (!path ty0. l4_vpath_valid972 p path /\
               l4_vhas_type961 env uvars g (m2 path) ty0 ==>
               l4_vnormal_eq972 env uvars g (m2 path) (m2' path)) /\
   l4_vhas_type961 env uvars g (l4_vrhs_apply972 m1 m2 r) ty ==>
   l4_vnormal_eq972 env uvars g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m2' r)`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972] THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vn_refl972];
   MAP_EVERY X_GEN_TAC [`rf:l4_vrhs972`;`ra:l4_vrhs972`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `l4_vrhs_apply972 m1 m2 rf`;`l4_vrhs_apply972 m1 m2 ra`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `l4_vnormal_eq972 env uvars g (l4_vrhs_apply972 m1 m2 rf) (l4_vrhs_apply972 m1 m2' rf) /\
      l4_vnormal_eq972 env uvars g (l4_vrhs_apply972 m1 m2 ra) (l4_vrhs_apply972 m1 m2' ra)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN MAP_EVERY EXISTS_TAC [`dom0:l4_vexpr961`;`cod0:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THENL
   [EXISTS_TAC `l4_vrhs_apply972 m1 m2 rf` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    EXISTS_TAC `l4_vrhs_apply972 m1 m2 ra` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]];
   MESON_TAC []]);;

let l4_vnormal_eq_apply_pat972 = prove
 (`!env uvars g p m1 m2 m2' r ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vrhs_wf972 p r /\
   (!path ty0. l4_vpath_valid972 p path /\
               l4_vhas_type961 env uvars g (m2 path) ty0 ==>
               l4_vnormal_eq972 env uvars g (m2 path) (m2' path)) /\
   l4_vhas_type961 env uvars g (l4_vrhs_apply972 m1 m2 r) ty ==>
   l4_vnormal_eq972 env uvars g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m2' r)`,
  MESON_TAC [l4_vnormal_eq_apply_pat_ind972]);;

let l4_all_vlevel_inst_wf972 = prove
 (`!us ks uvars.
   ALL (l4_vlevel_wf961 uvars) ks ==>
   ALL (l4_vlevel_wf961 uvars) (MAP (l4_vlevel_inst961 ks) us)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;ALL] THEN
  ASM_MESON_TAC [l4_vlevel_inst_wf_any966]);;

let l4_veq_up_to_levels_vinstL_any972 = prove
 (`!e uvars ls ls'.
   ALL (l4_vlevel_wf961 uvars) ls /\
   ALL (l4_vlevel_wf961 uvars) ls' /\
   ALL2 l4_vlevel_equiv961 ls ls' ==>
   l4_veq_up_to_levels970 uvars (l4_vinstL961 ls e) (l4_vinstL961 ls' e)`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vinstL961] THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_veq_up_to_levels_bvar970];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_veq_up_to_levels_sort970 THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vlevel_inst_congr_r970];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_veq_up_to_levels_const970 THEN
   ASM_SIMP_TAC [l4_all_vlevel_inst_wf972;l4_all2_map_vlevel_inst_congr970];
   MESON_TAC [l4_veq_up_to_levels_app970];
   MESON_TAC [l4_veq_up_to_levels_lam970];
   MESON_TAC [l4_veq_up_to_levels_forall970]]);;

let l4_veq_up_to_levels_vrhs_const_ind972 = prove
 (`!r uvars c ls ls'.
   l4_vrhs_wf972 (L4VPConst972 c) r /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   ALL (l4_vlevel_wf961 uvars) ls' /\
   ALL2 l4_vlevel_equiv961 ls ls' ==>
   l4_veq_up_to_levels970 uvars
     (l4_vrhs_apply972 ls l4_vmenv_empty972 r)
     (l4_vrhs_apply972 ls' l4_vmenv_empty972 r)`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972;l4_vpath_valid_clauses972] THEN
  MESON_TAC [l4_veq_up_to_levels_vinstL_any972;l4_veq_up_to_levels_app970]);;

let l4_veq_up_to_levels_vrhs_const972 = prove
 (`!uvars c ls ls' r.
   l4_vrhs_wf972 (L4VPConst972 c) r /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   ALL (l4_vlevel_wf961 uvars) ls' /\
   ALL2 l4_vlevel_equiv961 ls ls' ==>
   l4_veq_up_to_levels970 uvars
     (l4_vrhs_apply972 ls l4_vmenv_empty972 r)
     (l4_vrhs_apply972 ls' l4_vmenv_empty972 r)`,
  MESON_TAC [l4_veq_up_to_levels_vrhs_const_ind972]);;

let l4_veq_up_to_levels_normal_eq_ind972 = prove
 (`!uvars e1 e2.
   l4_veq_up_to_levels970 uvars e1 e2 ==>
   (!env g ty.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e1 ty ==>
      l4_vnormal_eq972 env uvars g e1 e2)`,
  MATCH_MP_TAC l4_veq_up_to_levels_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MESON_TAC [l4_vn_refl972];
   (* const *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `c:l4_name`;`ls1:l4_vlevel961 list`;`ty:l4_vexpr961`]
     l4_vhas_type_const_inv970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vn_constDF972 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* sort *)
   MESON_TAC [l4_vn_sortDF972];
   (* app *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f1:l4_vexpr961`;`a1:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vnormal_eq972 env uvars g f1 f2 /\ l4_vnormal_eq972 env uvars g a1 a2`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_appDF972 THEN MAP_EVERY EXISTS_TAC [`dom0:l4_vexpr961`;`cod0:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THENL
   [EXISTS_TAC `f1:l4_vexpr961` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    EXISTS_TAC `a1:l4_vexpr961` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]];
   (* lam *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom1:l4_vexpr961`;`b1:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `cod0:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vnormal_eq972 env uvars g dom1 dom2` ASSUME_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vn_lamDF972 THEN MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `cod0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
   (* forallE *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom1:l4_vexpr961`;`cod1:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vn_forallEDF972 THEN
   MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 v` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []]]);;

let l4_veq_up_to_levels_normal_eq972 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_veq_up_to_levels970 uvars e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vnormal_eq972 env uvars g e1 e2`,
  MESON_TAC [l4_veq_up_to_levels_normal_eq_ind972]);;

(* ========================================================================= *)
(* 3b. Typed Parallel Reduction, Takahashi Complete Development,             *)
(*     PatternParams, and Typed Church-Rosser Confluence                     *)
(* ========================================================================= *)

let l4_vpar_red_t_RULES972,l4_vpar_red_t_INDUCT972,l4_vpar_red_t_CASES972 =
  new_inductive_definition
 `(!env uvars (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g i.
     l4_vpar_red_t972 env uvars pat g (L4VBVar961 i) (L4VBVar961 i)) /\
  (!env uvars pat g u.
     l4_vpar_red_t972 env uvars pat g (L4VSort961 u) (L4VSort961 u)) /\
  (!env uvars pat g c ls.
     l4_vpar_red_t972 env uvars pat g (L4VConst961 c ls) (L4VConst961 c ls)) /\
  (!env uvars pat g f f' a a'.
     l4_vpar_red_t972 env uvars pat g f f' /\
     l4_vpar_red_t972 env uvars pat g a a' ==>
     l4_vpar_red_t972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a')) /\
  (!env uvars pat g dom dom' body body'.
     l4_vpar_red_t972 env uvars pat g dom dom' /\
     l4_vpar_red_t972 env uvars pat (CONS dom g) body body' ==>
     l4_vpar_red_t972 env uvars pat g (L4VLam961 dom body) (L4VLam961 dom' body')) /\
  (!env uvars pat g dom dom' cod cod'.
     l4_vpar_red_t972 env uvars pat g dom dom' /\
     l4_vpar_red_t972 env uvars pat (CONS dom g) cod cod' ==>
     l4_vpar_red_t972 env uvars pat g (L4VForallE961 dom cod) (L4VForallE961 dom' cod')) /\
  (!env uvars pat g dom e1 e1' e2 e2'.
     l4_vpar_red_t972 env uvars pat (CONS dom g) e1 e1' /\
     l4_vpar_red_t972 env uvars pat g e2 e2' ==>
     l4_vpar_red_t972 env uvars pat g
       (L4VApp961 (L4VLam961 dom e1) e2) (l4_vinst0961 e1' e2')) /\
  (!env uvars pat g p r ck e m1 m2 m2'.
     pat p (r, ck) /\
     l4_vrhs_wf972 p r /\
     l4_vcheck_wf972 p ck /\
     l4_vpattern_matches972 p e m1 m2 /\
     l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
     (!a. l4_vpath_valid972 p a ==>
          l4_vpar_red_t972 env uvars pat g (m2 a) (m2' a)) ==>
     l4_vpar_red_t972 env uvars pat g e (l4_vrhs_apply972 m1 m2' r))`;;

let l4_vprt_bvar972,
    l4_vprt_sort972,
    l4_vprt_const972,
    l4_vprt_app972,
    l4_vprt_lam972,
    l4_vprt_forallE972,
    l4_vprt_beta972,
    l4_vprt_extra972 =
  match CONJUNCTS l4_vpar_red_t_RULES972 with
  | [c1;c2;c3;c4;c5;c6;c7;c8] -> (c1,c2,c3,c4,c5,c6,c7,c8)
  | _ -> failwith "l4_vpar_red_t_RULES972: unexpected arity";;

let l4_vpar_red_t_STRONG_INDUCT972 =
  derive_strong_induction (l4_vpar_red_t_RULES972, l4_vpar_red_t_INDUCT972);;

let l4_vnon_neutral972 = new_definition
 `l4_vnon_neutral972 env uvars
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e <=>
   (?dom e1 e2. e = L4VApp961 (L4VLam961 dom e1) e2) \/
   (?p r ck m1 m2.
      pat p (r, ck) /\
      l4_vrhs_wf972 p r /\
      l4_vcheck_wf972 p ck /\
      l4_vpattern_matches972 p e m1 m2 /\
      l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck)`;;

let l4_vcpar_red_t_RULES972,l4_vcpar_red_t_INDUCT972,l4_vcpar_red_t_CASES972 =
  new_inductive_definition
 `(!env uvars (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g i.
     l4_vcpar_red_t972 env uvars pat g (L4VBVar961 i) (L4VBVar961 i)) /\
  (!env uvars pat g u.
     l4_vcpar_red_t972 env uvars pat g (L4VSort961 u) (L4VSort961 u)) /\
  (!env uvars pat g c ls.
     ~l4_vnon_neutral972 env uvars pat g (L4VConst961 c ls) ==>
     l4_vcpar_red_t972 env uvars pat g (L4VConst961 c ls) (L4VConst961 c ls)) /\
  (!env uvars pat g f f' a a'.
     ~l4_vnon_neutral972 env uvars pat g (L4VApp961 f a) /\
     l4_vcpar_red_t972 env uvars pat g f f' /\
     l4_vcpar_red_t972 env uvars pat g a a' ==>
     l4_vcpar_red_t972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a')) /\
  (!env uvars pat g dom dom' body body'.
     l4_vcpar_red_t972 env uvars pat g dom dom' /\
     l4_vcpar_red_t972 env uvars pat (CONS dom g) body body' ==>
     l4_vcpar_red_t972 env uvars pat g (L4VLam961 dom body) (L4VLam961 dom' body')) /\
  (!env uvars pat g dom dom' cod cod'.
     l4_vcpar_red_t972 env uvars pat g dom dom' /\
     l4_vcpar_red_t972 env uvars pat (CONS dom g) cod cod' ==>
     l4_vcpar_red_t972 env uvars pat g (L4VForallE961 dom cod) (L4VForallE961 dom' cod')) /\
  (!env uvars pat g dom e1 e1' e2 e2'.
     l4_vcpar_red_t972 env uvars pat (CONS dom g) e1 e1' /\
     l4_vcpar_red_t972 env uvars pat g e2 e2' ==>
     l4_vcpar_red_t972 env uvars pat g
       (L4VApp961 (L4VLam961 dom e1) e2) (l4_vinst0961 e1' e2')) /\
  (!env uvars pat g p r ck e m1 m2 m2'.
     pat p (r, ck) /\
     l4_vrhs_wf972 p r /\
     l4_vcheck_wf972 p ck /\
     l4_vpattern_matches972 p e m1 m2 /\
     l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
     (!a. l4_vpath_valid972 p a ==>
          l4_vcpar_red_t972 env uvars pat g (m2 a) (m2' a)) ==>
     l4_vcpar_red_t972 env uvars pat g e (l4_vrhs_apply972 m1 m2' r))`;;

let l4_vcprt_bvar972,
    l4_vcprt_sort972,
    l4_vcprt_const972,
    l4_vcprt_app972,
    l4_vcprt_lam972,
    l4_vcprt_forallE972,
    l4_vcprt_beta972,
    l4_vcprt_extra972 =
  match CONJUNCTS l4_vcpar_red_t_RULES972 with
  | [c1;c2;c3;c4;c5;c6;c7;c8] -> (c1,c2,c3,c4,c5,c6,c7,c8)
  | _ -> failwith "l4_vcpar_red_t_RULES972: unexpected arity";;

let l4_vcpar_red_t_STRONG_INDUCT972 =
  derive_strong_induction (l4_vcpar_red_t_RULES972, l4_vcpar_red_t_INDUCT972);;

let l4_vpar_red_ts972 = new_definition
 `l4_vpar_red_ts972 env uvars
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e1 e2 <=>
   l4_vrt_closure972 (l4_vpar_red_t972 env uvars pat g) e1 e2`;;

let l4_vcr_defeq972 = new_definition
 `l4_vcr_defeq972 env uvars
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e1 e2 <=>
   (?ty1. l4_vhas_type961 env uvars g e1 ty1) /\
   (?ty2. l4_vhas_type961 env uvars g e2 ty2) /\
   (?e1' e2'.
      l4_vpar_red_ts972 env uvars pat g e1 e1' /\
      l4_vpar_red_ts972 env uvars pat g e2 e2' /\
      l4_vnormal_eq972 env uvars g e1' e2')`;;

let l4_pattern_params_for972 = new_definition
 `l4_pattern_params_for972 env
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) <=>
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   (!p r ck. pat p (r, ck) ==> l4_vrhs_wf972 p r /\ l4_vcheck_wf972 p ck) /\
   (!p r ck. pat p (r, ck) ==> ?sp. p = l4_vsimple_to_pattern972 sp) /\
   (!p1 p2 p3 p4 r ck r' ck'.
      pat p1 (r, ck) /\ pat p2 (r', ck') /\
      l4_vsubpattern972 p3 p1 /\
      l4_vpattern_inter972 p2 p3 = SOME p4 ==>
      p1 = p2 /\ p2 = p3) /\
   (!p r ck r' ck'.
      pat p (r, ck) /\ pat p (r', ck') ==> r = r' /\ ck = ck') /\
   (!uvars g p r ck e m1 m2 ty.
      pat p (r, ck) /\
      l4_vpattern_matches972 p e m1 m2 /\
      l4_vhas_type961 env uvars g e ty /\
      l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck ==>
      l4_vis_defeq_u961 env uvars g e (l4_vrhs_apply972 m1 m2 r)) /\
   (!p r ck p1 p2 p3 p4.
      pat p (r, ck) /\
      l4_vsubpattern972 (L4VPApp972 p1 p2) p ==>
      ~l4_vsubpattern972 (L4VPApp972 p3 p4) p1) /\
   (!p p' r ck r' ck' p1 p2 p1' p2' p3.
      pat p (r, ck) /\ pat p' (r', ck') /\
      l4_vsubpattern972 (L4VPApp972 p1 p2) p /\
      l4_vsubpattern972 (L4VPApp972 p1' p2') p' /\
      l4_vsubpattern972 (L4VPVar972 p3) p1 ==>
      l4_vpattern_inter972 p1' p3 = NONE) /\
   (!p p' r ck r' ck' p1 p2 p1' p2' p3 p3'.
      pat p (r, ck) /\ pat p' (r', ck') /\
      l4_vsubpattern972 (L4VPApp972 p1 p2) p /\
      l4_vsubpattern972 (L4VPApp972 p1' p2') p' /\
      l4_vsubpattern972 p3 p1 /\
      l4_vsubpattern972 p3' p2' ==>
      l4_vpattern_inter972 p3 p3' = NONE) /\
   (!uvars g df ls.
      l4_venv_has_defeq961 env df /\
      ALL (l4_vlevel_wf961 uvars) ls /\
      LENGTH ls = l4_vdf_uvars961 df ==>
      ?p r ck m1 m2.
        pat p (r, ck) /\
        l4_vpattern_matches972 p (l4_vinstL961 ls (l4_vdf_lhs961 df)) m1 m2 /\
        l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
        l4_vinstL961 ls (l4_vdf_rhs961 df) = l4_vrhs_apply972 m1 m2 r) /\
   (!uvars g f1 f2 a1 a2 dom cod p r ck m1 m2 m2'.
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g f1 (L4VForallE961 dom cod) /\
      l4_vhas_type961 env uvars g f2 (L4VForallE961 dom cod) /\
      l4_vhas_type961 env uvars g a1 dom /\
      l4_vhas_type961 env uvars g a2 dom /\
      l4_vnormal_eq972 env uvars g f1 f2 /\
      l4_vnormal_eq972 env uvars g a1 a2 /\
      pat p (r, ck) /\
      l4_vpattern_matches972 p (L4VApp961 f2 a2) m1 m2 /\
      l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
      (!x. l4_vpath_valid972 p x ==>
           l4_vpar_red_t972 env uvars pat g (m2 x) (m2' x)) ==>
      ?e1'. l4_vpar_red_ts972 env uvars pat g (L4VApp961 f1 a1) e1' /\
            l4_vnormal_eq972 env uvars g e1' (l4_vrhs_apply972 m1 m2' r))`;;

let l4_pattern_params972 = new_definition
 `l4_pattern_params972 env <=> ?pat. l4_pattern_params_for972 env pat`;;

let l4_pp_wf972 = prove
 (`!env pat. l4_pattern_params_for972 env pat ==> l4_venv_wf966 env`,
  SIMP_TAC [l4_pattern_params_for972]);;

let l4_pp_inj972 = prove
 (`!env pat. l4_pattern_params_for972 env pat ==> l4_defeq_injectivity972 env`,
  SIMP_TAC [l4_pattern_params_for972]);;

let l4_pp_rhs_check_wf972 = prove
 (`!env pat p r ck.
   l4_pattern_params_for972 env pat /\ pat p (r, ck) ==>
   l4_vrhs_wf972 p r /\ l4_vcheck_wf972 p ck`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_simple972 = prove
 (`!env pat p r ck.
   l4_pattern_params_for972 env pat /\ pat p (r, ck) ==>
   ?sp. p = l4_vsimple_to_pattern972 sp`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_uniq972 = prove
 (`!env pat p1 p2 p3 p4 r ck r' ck'.
   l4_pattern_params_for972 env pat /\
   pat p1 (r, ck) /\ pat p2 (r', ck') /\
   l4_vsubpattern972 p3 p1 /\
   l4_vpattern_inter972 p2 p3 = SOME p4 ==>
   p1 = p2 /\ p2 = p3`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_rhs_uniq972 = prove
 (`!env pat p r ck r' ck'.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\ pat p (r', ck') ==>
   r = r' /\ ck = ck'`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_pat_wf972 = prove
 (`!env pat uvars g p r ck e m1 m2 ty.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\
   l4_vpattern_matches972 p e m1 m2 /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck ==>
   l4_vis_defeq_u961 env uvars g e (l4_vrhs_apply972 m1 m2 r)`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_app_l972 = prove
 (`!env pat p r ck p1 p2 p3 p4.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\
   l4_vsubpattern972 (L4VPApp972 p1 p2) p ==>
   ~l4_vsubpattern972 (L4VPApp972 p3 p4) p1`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_app_l_uniq972 = prove
 (`!env pat p p' r ck r' ck' p1 p2 p1' p2' p3.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\ pat p' (r', ck') /\
   l4_vsubpattern972 (L4VPApp972 p1 p2) p /\
   l4_vsubpattern972 (L4VPApp972 p1' p2') p' /\
   l4_vsubpattern972 (L4VPVar972 p3) p1 ==>
   l4_vpattern_inter972 p1' p3 = NONE`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_app_uniq972 = prove
 (`!env pat p p' r ck r' ck' p1 p2 p1' p2' p3 p3'.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\ pat p' (r', ck') /\
   l4_vsubpattern972 (L4VPApp972 p1 p2) p /\
   l4_vsubpattern972 (L4VPApp972 p1' p2') p' /\
   l4_vsubpattern972 p3 p1 /\
   l4_vsubpattern972 p3' p2' ==>
   l4_vpattern_inter972 p3 p3' = NONE`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_extra_pat972 = prove
 (`!env pat uvars g df ls.
   l4_pattern_params_for972 env pat /\
   l4_venv_has_defeq961 env df /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = l4_vdf_uvars961 df ==>
   ?p r ck m1 m2.
     pat p (r, ck) /\
     l4_vpattern_matches972 p (l4_vinstL961 ls (l4_vdf_lhs961 df)) m1 m2 /\
     l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
     l4_vinstL961 ls (l4_vdf_rhs961 df) = l4_vrhs_apply972 m1 m2 r`,
  REWRITE_TAC [l4_pattern_params_for972] THEN MESON_TAC []);;

let l4_pp_norm_app972 = prove
 (`!env pat uvars g f1 f2 a1 a2 dom cod p r ck m1 m2 m2'.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g f1 (L4VForallE961 dom cod) /\
   l4_vhas_type961 env uvars g f2 (L4VForallE961 dom cod) /\
   l4_vhas_type961 env uvars g a1 dom /\
   l4_vhas_type961 env uvars g a2 dom /\
   l4_vnormal_eq972 env uvars g f1 f2 /\
   l4_vnormal_eq972 env uvars g a1 a2 /\
   pat p (r, ck) /\
   l4_vpattern_matches972 p (L4VApp961 f2 a2) m1 m2 /\
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck /\
   (!x. l4_vpath_valid972 p x ==>
        l4_vpar_red_t972 env uvars pat g (m2 x) (m2' x)) ==>
   ?e1'. l4_vpar_red_ts972 env uvars pat g (L4VApp961 f1 a1) e1' /\
         l4_vnormal_eq972 env uvars g e1' (l4_vrhs_apply972 m1 m2' r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2
    (fun th ->
      MP_TAC (SPECL [`uvars:num`;`g:l4_vexpr961 list`;`f1:l4_vexpr961`;`f2:l4_vexpr961`;
                     `a1:l4_vexpr961`;`a2:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                     `p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`;
                     `m2':bool list->l4_vexpr961`]
               (last (CONJUNCTS (REWRITE_RULE [l4_pattern_params_for972] th)))))
    (fun th -> DISCH_THEN (fun imp -> ACCEPT_TAC (MP imp th)))));;

let l4_params_pat_not_var972 = prove
 (`!env pat p r ck.
   l4_pattern_params_for972 env pat ==> ~pat (L4VPVar972 p) (r, ck)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                 `L4VPVar972 p`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`] l4_pp_simple972) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `sp:l4_vsimple_pattern972`) THEN
  UNDISCH_TAC `L4VPVar972 p = l4_vsimple_to_pattern972 sp` THEN
  STRUCT_CASES_TAC (SPEC `sp:l4_vsimple_pattern972` (cases "l4_vsimple_pattern972")) THEN
  REWRITE_TAC [l4_vsimple_to_pattern972;distinctness "l4_vpattern972"]);;

let l4_vpattern_check_ok_weakN972 = prove
 (`!env uvars n k g g' p ck m1 m2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vcheck_wf972 p ck /\
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck ==>
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g') m1
     (l4_vmenv_map972 (\x. l4_vliftN961 x n k) p m2) ck`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
  MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g`;
                        `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty:l4_vexpr961`))) THEN
  EXISTS_TAC `l4_vliftN961 ty n k` THEN
  ASM_SIMP_TAC [GSYM l4_vrhs_apply_vliftN972] THEN
  MATCH_MP_TAC l4_vis_defeq_weakN966 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_SIMP_TAC [l4_venv_wf_closed966]);;

let l4_vpattern_check_ok_instN972 = prove
 (`!env uvars g0 e0 a0 k g1 g p ck m1 m2.
   l4_venv_wf966 env /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vcheck_wf972 p ck /\
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g1) m1 m2 ck ==>
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1
     (l4_vmenv_map972 (\x. l4_vinst961 x e0 k) p m2) ck`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
  MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g1`;
                        `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty:l4_vexpr961`))) THEN
  EXISTS_TAC `l4_vinst961 ty e0 k` THEN
  ASM_SIMP_TAC [GSYM l4_vrhs_apply_vinst972] THEN
  MATCH_MP_TAC l4_vis_defeq_instN966 THEN
  MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
  ASM_SIMP_TAC [l4_venv_wf_closed966]);;

let l4_vpar_red_t_refl_ind972 = prove
 (`!e env uvars pat g. l4_vpar_red_t972 env uvars pat g e e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [l4_vprt_bvar972;l4_vprt_sort972;l4_vprt_const972;
                l4_vprt_app972;l4_vprt_lam972;l4_vprt_forallE972]);;

let l4_vpar_red_t_refl972 = prove
 (`!env uvars pat g e. l4_vpar_red_t972 env uvars pat g e e`,
  MESON_TAC [l4_vpar_red_t_refl_ind972]);;

let l4_vpar_red_t_weakN_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vpar_red_t972 env uvars pat g e1 e2 ==>
   (!n k g'.
      l4_venv_wf966 env /\
      l4_vctx_liftN966 n k g g' ==>
      l4_vpar_red_t972 env uvars pat g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vliftN961;l4_vprt_bvar972];
   REWRITE_TAC [l4_vliftN961;l4_vprt_sort972];
   REWRITE_TAC [l4_vliftN961;l4_vprt_const972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vprt_app972 THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vprt_lam972 THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vprt_forallE972 THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
   MATCH_MP_TAC l4_vprt_beta972 THEN ASM_SIMP_TAC [l4_vctx_liftN_succ966];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vliftN972] THEN
   MATCH_MP_TAC l4_vprt_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
     `l4_vmenv_map972 (\x. l4_vliftN961 x n k) p m2`] THEN
   ASM_REWRITE_TAC [l4_vpattern_matches_vliftN972] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `m2:bool list->l4_vexpr961` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vpattern_check_ok_weakN972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vmenv_map_valid972]]]);;

let l4_vpar_red_t_weakN972 = prove
 (`!env uvars pat n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vpar_red_t972 env uvars pat g e1 e2 ==>
   l4_vpar_red_t972 env uvars pat g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_vpar_red_t_weakN_ind972]);;

let l4_vpar_red_t_instN_bvar972 = prove
 (`!g0 a1 a0 k g1 g.
   l4_vctx_instN966 g0 a1 a0 k g1 g ==>
   (!env uvars pat a2 i.
      l4_venv_wf966 env /\
      l4_vpar_red_t972 env uvars pat g0 a1 a2 ==>
      l4_vpar_red_t972 env uvars pat g (l4_vinst_var961 i a1 k) (l4_vinst_var961 i a2 k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
   REWRITE_TAC [l4_vinst_var961;LT_REFL;ARITH_RULE `~(SUC n < 0)`;
                ARITH_RULE `~(SUC n = 0)`;l4_vliftN_zero961;l4_vprt_bvar972] THEN
   ASM_REWRITE_TAC [];
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`a1:l4_vexpr961`;`a0:l4_vexpr961`;
                        `k:num`;`g1:l4_vexpr961 list`;`g:l4_vexpr961 list`;`c:l4_vexpr961`] THEN
   DISCH_TAC THEN REPEAT STRIP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;l4_vprt_bvar972];
    REWRITE_TAC [l4_vinst_var_succ966;l4_vlift961] THEN
    MATCH_MP_TAC l4_vpar_red_t_weakN972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
    ASM_SIMP_TAC [l4_vctx_liftN_one966]]]);;

let l4_vpar_red_t_instN_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vpar_red_t972 env uvars pat g1 e1 e2 ==>
   (!g0 a1 a2 a0 k g.
      l4_venv_wf966 env /\
      l4_vpar_red_t972 env uvars pat g0 a1 a2 /\
      l4_vhas_type961 env uvars g0 a1 a0 /\
      l4_vctx_instN966 g0 a1 a0 k g1 g ==>
      l4_vpar_red_t972 env uvars pat g (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k))`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   ASM_MESON_TAC [l4_vpar_red_t_instN_bvar972];
   REWRITE_TAC [l4_vinst961;l4_vprt_sort972];
   REWRITE_TAC [l4_vinst961;l4_vprt_const972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vprt_app972 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vprt_lam972 THEN ASM_MESON_TAC [l4_vctx_instN_succ966];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vprt_forallE972 THEN ASM_MESON_TAC [l4_vctx_instN_succ966];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   MATCH_MP_TAC l4_vprt_beta972 THEN ASM_MESON_TAC [l4_vctx_instN_succ966];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vinst972] THEN
   MATCH_MP_TAC l4_vprt_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
     `l4_vmenv_map972 (\x. l4_vinst961 x a1 k) p m2`] THEN
   ASM_SIMP_TAC [l4_vpattern_matches_vinst972] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vpattern_check_ok_instN972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vmenv_map_valid972] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `a:bool list`) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`] THEN
    ASM_REWRITE_TAC []]]);;

let l4_vpar_red_t_instN972 = prove
 (`!env uvars pat g0 a1 a2 a0 k g1 g e1 e2.
   l4_venv_wf966 env /\
   l4_vpar_red_t972 env uvars pat g0 a1 a2 /\
   l4_vhas_type961 env uvars g0 a1 a0 /\
   l4_vctx_instN966 g0 a1 a0 k g1 g /\
   l4_vpar_red_t972 env uvars pat g1 e1 e2 ==>
   l4_vpar_red_t972 env uvars pat g (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k)`,
  MESON_TAC [l4_vpar_red_t_instN_ind972]);;

let l4_vpar_red_t_defeq_ind972 = prove
 (`!env uvars pat g e e'.
   l4_vpar_red_t972 env uvars pat g e e' ==>
   (!ty.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e ty ==>
      l4_vis_defeq961 env uvars g e e' ty)`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN SIMP_TAC [];
   REWRITE_TAC [l4_vhas_type961] THEN SIMP_TAC [];
   REWRITE_TAC [l4_vhas_type961] THEN SIMP_TAC [];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;
     `a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`L4VApp961 f a`;`l4_vinst0961 cod0 a`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom0:l4_vexpr961` THEN
   CONJ_TAC THEN ASM_SIMP_TAC [];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `body:l4_vexpr961`;`body':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `cod0:l4_vexpr961`)) THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`L4VLam961 dom0 body`;`L4VForallE961 dom0 cod0`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_SIMP_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `cod0:l4_vexpr961`;`cod0':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`cod0:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`L4VForallE961 dom0 cod0`;`L4VSort961 (L4VLIMax961 u v)`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_SIMP_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom0:l4_vexpr961`;
     `e1:l4_vexpr961`;`e1':l4_vexpr961`;`e2:l4_vexpr961`;`e2':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VLam961 dom0 e1`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
     (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 a1 b1`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `b2:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g (L4VLam961 dom0 e1) (L4VForallE961 dom0 b2)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 a1 b1) (L4VForallE961 dom0 b2)`
     MP_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`L4VLam961 dom0 e1`;`L4VLam961 dom0 e1`;`L4VLam961 dom0 e1`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   DISCH_THEN (fun th ->
     MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
       (CONJ (ASSUME `l4_defeq_injectivity972 env`)
         (CONJ (ASSUME `l4_vctx_wf966 env uvars g`) th))))) THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `w:l4_vlevel961` ASSUME_TAC) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g e2 dom0` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `a1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars (CONS dom0 g) e1 e1' b2` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g e2 e2' dom0` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`L4VApp961 (L4VLam961 dom0 e1) e2`;`l4_vinst0961 b2 e2'`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN
   EXISTS_TAC `L4VApp961 (L4VLam961 dom0 e1') e2'` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN
    MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom0:l4_vexpr961` THEN
    CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vis_defeq_beta961 THEN REWRITE_TAC [GSYM l4_vhas_type961] THEN
    CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_refl_r961 THENL
    [EXISTS_TAC `e1:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `e2:l4_vexpr961` THEN ASM_REWRITE_TAC []]];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g e (l4_vrhs_apply972 m1 m2 r)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_pp_pat_wf972 THEN
    MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                          `p:l4_vpattern972`;`ck:l4_vpattern_check972`;`ty:l4_vexpr961`] THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
   MAP_EVERY EXISTS_TAC [`e:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_trans_u_r972 THEN
   EXISTS_TAC `l4_vrhs_apply972 m1 m2 r` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_apply_pat972 THEN
   EXISTS_TAC `p:l4_vpattern972` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
    EXISTS_TAC `ty0:l4_vexpr961` THEN FIRST_X_ASSUM (MP_TAC o SPEC `path:bool list`) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `e:l4_vexpr961` THEN
    ASM_REWRITE_TAC []]]);;

let l4_vpar_red_t_defeq972 = prove
 (`!env uvars pat g e e' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vpar_red_t972 env uvars pat g e e' /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vis_defeq961 env uvars g e e' ty`,
  MESON_TAC [l4_vpar_red_t_defeq_ind972]);;

let l4_vpar_red_t_has_type972 = prove
 (`!env uvars pat g e e' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vpar_red_t972 env uvars pat g e e' /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vhas_type961 env uvars g e' ty`,
  MESON_TAC [l4_vpar_red_t_defeq972;l4_vis_defeq_refl_r961]);;

let l4_vpar_red_t_defeqDFC_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vpar_red_t972 env uvars pat g1 e1 e2 ==>
   (!g0 g2 ty.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      l4_vhas_type961 env uvars g1 e1 ty ==>
      l4_vpar_red_t972 env uvars pat g2 e1 e2)`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vprt_bvar972];
   REWRITE_TAC [l4_vprt_sort972];
   REWRITE_TAC [l4_vprt_const972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;
     `a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vprt_app972 THEN ASM_MESON_TAC [];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `body:l4_vexpr961`;`body':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `cod0:l4_vexpr961`)) THEN
   MATCH_MP_TAC l4_vprt_lam972 THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`cod0:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `cod0:l4_vexpr961`;`cod0':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`cod0:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vprt_forallE972 THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`L4VSort961 v`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`dom0:l4_vexpr961`;
     `e1:l4_vexpr961`;`e1':l4_vexpr961`;`e2:l4_vexpr961`;`e2':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `L4VLam961 dom0 e1`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
     (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom0:l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 a1 b1`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `b2:l4_vexpr961`)) THEN
   MATCH_MP_TAC l4_vprt_beta972 THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`b2:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ASM_MESON_TAC []];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vprt_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
                         `m2:bool list->l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g1`;
                          `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty0:l4_vexpr961`))) THEN
    EXISTS_TAC `ty0:l4_vexpr961` THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966];
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                   `p:l4_vpattern972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
                   `m2:bool list->l4_vexpr961`;`ty:l4_vexpr961`;`a:bool list`]
      l4_vpattern_matches_has_type972) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `ty_a:l4_vexpr961`) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `a:bool list`) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`ty_a:l4_vexpr961`] THEN
    ASM_REWRITE_TAC []]]);;

let l4_vpar_red_t_defeqDFC972 = prove
 (`!env uvars pat g0 g1 g2 e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vhas_type961 env uvars g1 e1 ty /\
   l4_vpar_red_t972 env uvars pat g1 e1 e2 ==>
   l4_vpar_red_t972 env uvars pat g2 e1 e2`,
  MESON_TAC [l4_vpar_red_t_defeqDFC_ind972]);;

let l4_vpar_red_t_apply_pat_ind972 = prove
 (`!r env uvars pat g p m1 m2 m3.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==>
        l4_vpar_red_t972 env uvars pat g (m2 a) (m3 a)) ==>
   l4_vpar_red_t972 env uvars pat g
     (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m3 r)`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN
  REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972;l4_vpar_red_t_refl972] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC l4_vprt_app972 THEN ASM_MESON_TAC [];
   ASM_SIMP_TAC []]);;

let l4_vpar_red_t_apply_pat972 = prove
 (`!env uvars pat g p r m1 m2 m3.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==>
        l4_vpar_red_t972 env uvars pat g (m2 a) (m3 a)) ==>
   l4_vpar_red_t972 env uvars pat g
     (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m3 r)`,
  MESON_TAC [l4_vpar_red_t_apply_pat_ind972]);;

let l4_vpar_red_t_weakN_inv_ind972 = prove
 (`!env uvars pat g' e1' e2'.
   l4_vpar_red_t972 env uvars pat g' e1' e2' ==>
   (!n k g e1 ty.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g' /\
      l4_vctx_liftN966 n k g g' /\
      l4_vhas_type961 env uvars g' (l4_vliftN961 e1 n k) ty /\
      e1' = l4_vliftN961 e1 n k ==>
      ?e2. l4_vpar_red_t972 env uvars pat g e1 e2 /\
           e2' = l4_vliftN961 e2 n k)`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961"] THEN
   STRIP_TAC THEN EXISTS_TAC `L4VBVar961 a` THEN
   ASM_REWRITE_TAC [l4_vprt_bvar972;l4_vliftN961];
   (* sort *)
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN EXISTS_TAC `L4VSort961 a` THEN
   ASM_REWRITE_TAC [l4_vprt_sort972;l4_vliftN961];
   (* const *)
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN EXISTS_TAC `L4VConst961 a0 a1` THEN
   ASM_REWRITE_TAC [l4_vprt_const972;l4_vliftN961];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;
     `a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `l4_vliftN961 a0 n k`;`l4_vliftN961 a1 n k`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `(?f2. l4_vpar_red_t972 env uvars pat g a0 f2 /\ f' = l4_vliftN961 f2 n k) /\
                 (?a2. l4_vpar_red_t972 env uvars pat g a1 a2 /\ a' = l4_vliftN961 a2 n k)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC [];
    EXISTS_TAC `L4VApp961 f2 a2` THEN ASM_SIMP_TAC [l4_vprt_app972;l4_vliftN961]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `body:l4_vexpr961`;`body':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `l4_vliftN961 a0 n k`;`l4_vliftN961 a1 n (SUC k)`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `cod0:l4_vexpr961`)) THEN
   SUBGOAL_THEN `(?d2. l4_vpar_red_t972 env uvars pat g a0 d2 /\ dom0' = l4_vliftN961 d2 n k) /\
                 (?b2. l4_vpar_red_t972 env uvars pat (CONS a0 g) a1 b2 /\
                       body' = l4_vliftN961 b2 n (SUC k))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC [];
     FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `cod0:l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN
     MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
    EXISTS_TAC `L4VLam961 d2 b2` THEN ASM_SIMP_TAC [l4_vprt_lam972;l4_vliftN961]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom0:l4_vexpr961`;`dom0':l4_vexpr961`;
     `cod0:l4_vexpr961`;`cod0':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `l4_vliftN961 a0 n k`;`l4_vliftN961 a1 n (SUC k)`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `(?d2. l4_vpar_red_t972 env uvars pat g a0 d2 /\ dom0' = l4_vliftN961 d2 n k) /\
                 (?c2. l4_vpar_red_t972 env uvars pat (CONS a0 g) a1 c2 /\
                       cod0' = l4_vliftN961 c2 n (SUC k))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC [];
     FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 v` THEN
     ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN
     MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
    EXISTS_TAC `L4VForallE961 d2 c2` THEN ASM_SIMP_TAC [l4_vprt_forallE972;l4_vliftN961]];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom0:l4_vexpr961`;
     `b0:l4_vexpr961`;`b0':l4_vexpr961`;`arg0:l4_vexpr961`;`arg0':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
   STRUCT_CASES_TAC (SPEC `a0:l4_vexpr961` (cases "l4_vexpr961")) THEN
   REWRITE_TAC [l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `L4VLam961 (l4_vliftN961 a0' n k) (l4_vliftN961 a1' n (SUC k))`;
                  `l4_vliftN961 a1 n k`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `d_f:l4_vexpr961`
     (X_CHOOSE_THEN `c_f:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `l4_vliftN961 a0' n k`;`l4_vliftN961 a1' n (SUC k)`;
                  `L4VForallE961 d_f c_f`] l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `c_b:l4_vexpr961`)) THEN
   SUBGOAL_THEN `(?b2. l4_vpar_red_t972 env uvars pat (CONS a0' g) a1' b2 /\
                       b0' = l4_vliftN961 b2 n (SUC k)) /\
                 (?a2. l4_vpar_red_t972 env uvars pat g a1 a2 /\
                       arg0' = l4_vliftN961 a2 n k)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `c_b:l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vctx_liftN_succ966] THEN
     MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ASM_MESON_TAC []];
    EXISTS_TAC `l4_vinst0961 b2 a2` THEN
    ASM_SIMP_TAC [l4_vprt_beta972;l4_vliftN_vinst0966]];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`;`k:num`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   MP_TAC (SPECL [`p:l4_vpattern972`;`n:num`;`k:num`;`e1:l4_vexpr961`;
                  `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`]
     l4_vpattern_matches_vliftN972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `m3:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `?m3'. l4_vmenv_wf972 p m3' /\
                       (!a. l4_vpath_valid972 p a ==>
                            l4_vpar_red_t972 env uvars pat g (m3 a) (m3' a) /\
                            m2' a = l4_vliftN961 (m3' a) n k)`
     (X_CHOOSE_THEN `m3':bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [MP_TAC (SPECL [`p:l4_vpattern972`;
                   `\(a:bool list) (y:l4_vexpr961).
                      l4_vpar_red_t972 env uvars pat g ((m3:bool list->l4_vexpr961) a) y /\
                      (m2':bool list->l4_vexpr961) a = l4_vliftN961 y n k`]
              l4_vmenv_rel_choice972) THEN
    REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `a:bool list` THEN DISCH_TAC THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                   `p:l4_vpattern972`;`l4_vliftN961 e1 n k`;`m1:l4_vlevel961 list`;
                   `m2:bool list->l4_vexpr961`;`ty:l4_vexpr961`;`a:bool list`]
      l4_vpattern_matches_has_type972) THEN
    ASM_SIMP_TAC [l4_vmenv_map_valid972] THEN DISCH_THEN (X_CHOOSE_TAC `ty_a:l4_vexpr961`) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `a:bool list`) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `ty_a:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vmenv_map_valid972];
    EXISTS_TAC `l4_vrhs_apply972 m1 m3' r` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vprt_extra972 THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
                           `m3:bool list->l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
      MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g'`;
                            `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN STRIP_TAC THEN
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;
                     `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                     `l4_vrhs_apply972 m1 m3 ra`;`l4_vrhs_apply972 m1 m3 rb`]
        l4_vis_defeq_u_weakN_iff972) THEN
      ASM_SIMP_TAC [SPEC `p:l4_vpattern972` l4_vrhs_apply_vliftN972];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC []];
     ASM_SIMP_TAC [SPEC `p:l4_vpattern972` l4_vrhs_apply_vliftN972] THEN
     MATCH_MP_TAC l4_vrhs_apply_ext972 THEN EXISTS_TAC `p:l4_vpattern972` THEN
     ASM_SIMP_TAC [l4_vmenv_map_valid972]]]]);;

let l4_vpar_red_t_weakN_inv972 = prove
 (`!env uvars pat n k g g' e1 e2' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' /\
   l4_vhas_type961 env uvars g' (l4_vliftN961 e1 n k) ty /\
   l4_vpar_red_t972 env uvars pat g' (l4_vliftN961 e1 n k) e2' ==>
   ?e2. l4_vpar_red_t972 env uvars pat g e1 e2 /\ e2' = l4_vliftN961 e2 n k`,
  MESON_TAC [l4_vpar_red_t_weakN_inv_ind972]);;

let l4_vcpar_red_t_to_vpar_red_t972 = prove
 (`!env uvars pat g e e'.
   l4_vcpar_red_t972 env uvars pat g e e' ==>
   l4_vpar_red_t972 env uvars pat g e e'`,
  MATCH_MP_TAC l4_vcpar_red_t_INDUCT972 THEN
  MESON_TAC [l4_vprt_bvar972;l4_vprt_sort972;l4_vprt_const972;l4_vprt_app972;
             l4_vprt_lam972;l4_vprt_forallE972;l4_vprt_beta972;l4_vprt_extra972]);;

let l4_vcpar_red_t_exists_ind972 = prove
 (`!sz env uvars pat g e ty.
   l4_vexpr_size972 e <= sz /\
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty ==>
   ?e'. l4_vcpar_red_t972 env uvars pat g e e'`,
  MATCH_MP_TAC num_WF THEN
  MAP_EVERY X_GEN_TAC [`sz:num`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
    `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
    `g:l4_vexpr961 list`;`e:l4_vexpr961`;`ty:l4_vexpr961`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vnon_neutral972 env uvars pat g e ==>
                ?e'. l4_vcpar_red_t972 env uvars pat g e e'` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vnon_neutral972] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [l4_subst_vars_tac972 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `L4VLam961 dom e1`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
      (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 a1 b1`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `b2:l4_vexpr961`)) THEN
    SUBGOAL_THEN `(?e1'. l4_vcpar_red_t972 env uvars pat (CONS dom g) e1 e1') /\
                  (?e2'. l4_vcpar_red_t972 env uvars pat g e2 e2')`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 e1`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `b2:l4_vexpr961` THEN
       ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC l4_vctx_cons972 THEN
       EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
      FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 e2`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a1:l4_vexpr961` THEN
       ASM_REWRITE_TAC [LE_REFL]]];
     EXISTS_TAC `l4_vinst0961 e1' e2'` THEN MATCH_MP_TAC l4_vcprt_beta972 THEN
     ASM_REWRITE_TAC []];
    SUBGOAL_THEN `?m2'. l4_vmenv_wf972 p m2' /\
                        (!x. l4_vpath_valid972 p x ==>
                             l4_vcpar_red_t972 env uvars pat g (m2 x) (m2' x))`
      (X_CHOOSE_THEN `m2':bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [MP_TAC (SPECL [`p:l4_vpattern972`;
                    `\(x:bool list) (y:l4_vexpr961).
                       l4_vcpar_red_t972 env uvars pat g ((m2:bool list->l4_vexpr961) x) y`]
               l4_vmenv_rel_choice972) THEN
     REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `p:l4_vpattern972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
                    `m2:bool list->l4_vexpr961`;`ty:l4_vexpr961`;`x:bool list`]
       l4_vpattern_matches_has_type972) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `ty_x:l4_vexpr961`) THEN
     MP_TAC (SPECL [`p:l4_vpattern972`;`e:l4_vexpr961`;`m1:l4_vlevel961 list`;
                    `m2:bool list->l4_vexpr961`;`x:bool list`]
       l4_vpattern_matches_path_size972) THEN
     ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
     FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 ((m2:bool list->l4_vexpr961) x)`) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `ty_x:l4_vexpr961` THEN
     ASM_REWRITE_TAC [LE_REFL];
     EXISTS_TAC `l4_vrhs_apply972 m1 m2' r` THEN
     MATCH_MP_TAC l4_vcprt_extra972 THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
                           `m2:bool list->l4_vexpr961`] THEN
     ASM_REWRITE_TAC []]];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vexpr_size972 e <= sz` THEN
  UNDISCH_TAC `l4_vhas_type961 env uvars g e ty` THEN
  UNDISCH_TAC `l4_vnon_neutral972 env uvars pat g e ==> ?e'. l4_vcpar_red_t972 env uvars pat g e e'` THEN
  STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REPEAT DISCH_TAC THENL
  [EXISTS_TAC `L4VBVar961 a` THEN REWRITE_TAC [l4_vcprt_bvar972];
   EXISTS_TAC `L4VSort961 a` THEN REWRITE_TAC [l4_vcprt_sort972];
   ASM_CASES_TAC `l4_vnon_neutral972 env uvars pat g (L4VConst961 a0 a1)` THENL
   [ASM_SIMP_TAC [];
    EXISTS_TAC `L4VConst961 a0 a1` THEN MATCH_MP_TAC l4_vcprt_const972 THEN ASM_REWRITE_TAC []];
   ASM_CASES_TAC `l4_vnon_neutral972 env uvars pat g (L4VApp961 a0 a1)` THENL
   [ASM_SIMP_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `a0:l4_vexpr961`;`a1:l4_vexpr961`;`ty:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `d0:l4_vexpr961`
      (X_CHOOSE_THEN `c0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(?f'. l4_vcpar_red_t972 env uvars pat g a0 f') /\
                  (?a'. l4_vcpar_red_t972 env uvars pat g a1 a')`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a0`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 a0 a1) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L4VForallE961 d0 c0` THEN
       ASM_REWRITE_TAC [LE_REFL]];
      FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a1`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 a0 a1) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `d0:l4_vexpr961` THEN
       ASM_REWRITE_TAC [LE_REFL]]];
     EXISTS_TAC `L4VApp961 f' a'` THEN MATCH_MP_TAC l4_vcprt_app972 THEN
     ASM_REWRITE_TAC []]];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `a0:l4_vexpr961`;`a1:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `c0:l4_vexpr961`)) THEN
   SUBGOAL_THEN `(?d'. l4_vcpar_red_t972 env uvars pat g a0 d') /\
                 (?b'. l4_vcpar_red_t972 env uvars pat (CONS a0 g) a1 b')`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a0`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 a0 a1) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 u` THEN
      ASM_REWRITE_TAC [LE_REFL]];
     FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a1`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 a0 a1) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `c0:l4_vexpr961` THEN
      ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC l4_vctx_cons972 THEN
      EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []]];
    EXISTS_TAC `L4VLam961 d' b'` THEN MATCH_MP_TAC l4_vcprt_lam972 THEN
    ASM_REWRITE_TAC []];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `a0:l4_vexpr961`;`a1:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `(?d'. l4_vcpar_red_t972 env uvars pat g a0 d') /\
                 (?c'. l4_vcpar_red_t972 env uvars pat (CONS a0 g) a1 c')`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a0`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VForallE961 a0 a1) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 u` THEN
      ASM_REWRITE_TAC [LE_REFL]];
     FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a1`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VForallE961 a0 a1) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 v` THEN
      ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC l4_vctx_cons972 THEN
      EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []]];
    EXISTS_TAC `L4VForallE961 d' c'` THEN MATCH_MP_TAC l4_vcprt_forallE972 THEN
    ASM_REWRITE_TAC []]]);;

let l4_vcpar_red_t_exists972 = prove
 (`!env uvars pat g e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty ==>
   ?e'. l4_vcpar_red_t972 env uvars pat g e e'`,
  MESON_TAC [l4_vcpar_red_t_exists_ind972;LE_REFL]);;

(* Triangle & single-step Church-Rosser for VParRedT *)

let l4_subst_rev_tac972 =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if is_var r && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else if is_var l && not (vfree_in l r) then SUBST_ALL_TAC th
    else fail ()));;

let l4_vpar_red_t_triangle_extra_cases972 = prove
 (`!env uvars pat g e0 e0'.
   l4_vpar_red_t972 env uvars pat g e0 e0' ==>
   (!sz p m1 m2 m2' ty.
      l4_vexpr_size972 e0 <= sz /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e0 ty /\
      l4_vpattern_matches972 p e0 m1 m2 /\
      (!a. l4_vpath_valid972 p a ==>
           l4_vcpar_red_t972 env uvars pat g (m2 a) (m2' a)) /\
      (!m. m < sz ==>
        !g0 d0 d0' o0 ty0.
          l4_vexpr_size972 d0 <= m /\
          l4_vctx_wf966 env uvars g0 /\
          l4_vhas_type961 env uvars g0 d0 ty0 /\
          l4_vpar_red_t972 env uvars pat g0 d0 d0' /\
          l4_vcpar_red_t972 env uvars pat g0 d0 o0 ==>
          ?o'. l4_vpar_red_t972 env uvars pat g0 d0' o' /\
               l4_vnormal_eq972 env uvars g0 o' o0) ==>
      (?m3 m3'.
         l4_vpattern_matches972 p e0' m1 m3 /\
         (!a. l4_vpath_valid972 p a ==>
              l4_vpar_red_t972 env uvars pat g (m2 a) (m3 a)) /\
         (!a. l4_vpath_valid972 p a ==>
              l4_vpar_red_t972 env uvars pat g (m3 a) (m3' a)) /\
         (!a. l4_vpath_valid972 p a ==>
              l4_vnormal_eq972 env uvars g (m3' a) (m2' a))) \/
      (?p1 e1' e1 m1_1 m2_1.
         l4_vsubpattern972 p1 p /\
         (p1 = p ==> e1 = e0 /\ e1' = e0') /\
         l4_vpattern_matches972 p1 e1 m1_1 m2_1 /\
         ?p' r' ck' m1' m2_r m3.
           pat p' (r', ck') /\
           l4_vrhs_wf972 p' r' /\
           l4_vcheck_wf972 p' ck' /\
           l4_vpattern_matches972 p' e1 m1' m2_r /\
           (!a. l4_vpath_valid972 p' a ==>
                l4_vpar_red_t972 env uvars pat g (m2_r a) (m3 a)) /\
           e1' = l4_vrhs_apply972 m1' m3 r'))`,
  MATCH_MP_TAC l4_vpar_red_t_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_bvar972]) THEN
   FIRST_ASSUM CONTR_TAC;
   (* sort *)
   REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_sort972]) THEN
   FIRST_ASSUM CONTR_TAC;
   (* const *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`c:l4_name`;`ls:l4_vlevel961 list`;
     `sz:num`;`p:l4_vpattern972`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
   REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`l4_vmenv_empty972`;`l4_vmenv_empty972`] THEN
   REWRITE_TAC [l4_vpm_const972;l4_vpath_valid_clauses972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;
     `a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH_f"))
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH_a"))) THEN
   MAP_EVERY X_GEN_TAC [`sz:num`;`p:l4_vpattern972`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP l4_pp_wf972) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
     (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `!a. l4_vpath_valid972 p a ==> l4_vcpar_red_t972 env uvars pat g (m2 a) (m2' a)` THEN
   UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 f a) m1 m2` THEN
   MP_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `c0:l4_name` SUBST1_TAC)
     (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `pf:l4_vpattern972` (X_CHOOSE_THEN `pa:l4_vpattern972` SUBST1_TAC))
       (X_CHOOSE_THEN `pf:l4_vpattern972` SUBST1_TAC))) THEN
   GEN_REWRITE_TAC LAND_CONV
     [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
      l4_vpattern_matches_app_inv972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THENL
   [(* L4VPApp972 pf pa *)
    DISCH_THEN (X_CHOOSE_THEN `f0:l4_vexpr961` (X_CHOOSE_THEN `a0_e:l4_vexpr961`
      (X_CHOOSE_THEN `ls2:l4_vlevel961 list` (X_CHOOSE_THEN `mf:bool list->l4_vexpr961`
      (X_CHOOSE_THEN `ma:bool list->l4_vexpr961`
        (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
    DISCH_THEN (LABEL_TAC "Hvcpar") THEN l4_subst_vars_tac972 THEN
    SUBGOAL_THEN
      `(?mf3 mf3'.
          l4_vpattern_matches972 pf f' m1 mf3 /\
          (!x. l4_vpath_valid972 pf x ==> l4_vpar_red_t972 env uvars pat g (mf x) (mf3 x)) /\
          (!x. l4_vpath_valid972 pf x ==> l4_vpar_red_t972 env uvars pat g (mf3 x) (mf3' x)) /\
          (!x. l4_vpath_valid972 pf x ==> l4_vnormal_eq972 env uvars g (mf3' x) (m2' (CONS F x)))) \/
       (?p1 e1' e1 m1_1 m2_1.
          l4_vsubpattern972 p1 pf /\
          (p1 = pf ==> e1 = f /\ e1' = f') /\
          l4_vpattern_matches972 p1 e1 m1_1 m2_1 /\
          ?p' r' ck' m1' m2_r m3.
            pat p' (r', ck') /\ l4_vrhs_wf972 p' r' /\ l4_vcheck_wf972 p' ck' /\
            l4_vpattern_matches972 p' e1 m1' m2_r /\
            (!x. l4_vpath_valid972 p' x ==> l4_vpar_red_t972 env uvars pat g (m2_r x) (m3 x)) /\
            e1' = l4_vrhs_apply972 m1' m3 r')`
      MP_TAC THENL
    [USE_THEN "IH_f" (MP_TAC o BETA_RULE o SPECL [`sz:num`;`pf:l4_vpattern972`;`m1:l4_vlevel961 list`;
       `mf:bool list->l4_vexpr961`;`(\x. (m2':bool list->l4_vexpr961) (CONS F x))`;
       `L4VForallE961 a1 b1`]) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
      USE_THEN "Hvcpar" (MP_TAC o SPEC `CONS F (x:bool list)`) THEN
      REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
    [SUBGOAL_THEN
       `(?ma3 ma3'.
           l4_vpattern_matches972 pa a' ls2 ma3 /\
           (!x. l4_vpath_valid972 pa x ==> l4_vpar_red_t972 env uvars pat g (ma x) (ma3 x)) /\
           (!x. l4_vpath_valid972 pa x ==> l4_vpar_red_t972 env uvars pat g (ma3 x) (ma3' x)) /\
           (!x. l4_vpath_valid972 pa x ==> l4_vnormal_eq972 env uvars g (ma3' x) (m2' (CONS T x)))) \/
        (?p1 e1' e1 m1_1 m2_1.
           l4_vsubpattern972 p1 pa /\
           (p1 = pa ==> e1 = a /\ e1' = a') /\
           l4_vpattern_matches972 p1 e1 m1_1 m2_1 /\
           ?p' r' ck' m1' m2_r m3.
             pat p' (r', ck') /\ l4_vrhs_wf972 p' r' /\ l4_vcheck_wf972 p' ck' /\
             l4_vpattern_matches972 p' e1 m1' m2_r /\
             (!x. l4_vpath_valid972 p' x ==> l4_vpar_red_t972 env uvars pat g (m2_r x) (m3 x)) /\
             e1' = l4_vrhs_apply972 m1' m3 r')`
       MP_TAC THENL
     [USE_THEN "IH_a" (MP_TAC o BETA_RULE o SPECL [`sz:num`;`pa:l4_vpattern972`;`ls2:l4_vlevel961 list`;
        `ma:bool list->l4_vexpr961`;`(\x. (m2':bool list->l4_vexpr961) (CONS T x))`;
        `a1:l4_vexpr961`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
       USE_THEN "Hvcpar" (MP_TAC o SPEC `CONS T (x:bool list)`) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
     DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`l4_vmenv_app972 mf3 ma3`;`l4_vmenv_app972 mf3' ma3'`] THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC [];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]];
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`p1:l4_vpattern972`;`e1':l4_vexpr961`;`e1:l4_vexpr961`;
                            `m1_1:l4_vlevel961 list`;`m2_1:bool list->l4_vexpr961`] THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC l4_vsubpattern_appR972 THEN ASM_REWRITE_TAC [];
       DISCH_THEN (fun th ->
         MP_TAC (MATCH_MP l4_vsubpattern_size_le972 (ASSUME `l4_vsubpattern972 p1 pa`)) THEN
         REWRITE_TAC [th;l4_vpattern_size972] THEN ARITH_TAC);
       ASM_REWRITE_TAC [];
       MAP_EVERY EXISTS_TAC [`p':l4_vpattern972`;`r':l4_vrhs972`;`ck':l4_vpattern_check972`;
                             `m1':l4_vlevel961 list`;`m2_r:bool list->l4_vexpr961`;
                             `m3:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC []]];
     DISJ2_TAC THEN
     MAP_EVERY EXISTS_TAC [`p1:l4_vpattern972`;`e1':l4_vexpr961`;`e1:l4_vexpr961`;
                           `m1_1:l4_vlevel961 list`;`m2_1:bool list->l4_vexpr961`] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vsubpattern_appL972 THEN ASM_REWRITE_TAC [];
      DISCH_THEN (fun th ->
        MP_TAC (MATCH_MP l4_vsubpattern_size_le972 (ASSUME `l4_vsubpattern972 p1 pf`)) THEN
        REWRITE_TAC [th;l4_vpattern_size972] THEN ARITH_TAC);
      ASM_REWRITE_TAC [];
      MAP_EVERY EXISTS_TAC [`p':l4_vpattern972`;`r':l4_vrhs972`;`ck':l4_vpattern_check972`;
                            `m1':l4_vlevel961 list`;`m2_r:bool list->l4_vexpr961`;
                            `m3:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC []]];
    (* L4VPVar972 pf *)
    DISCH_THEN (X_CHOOSE_THEN `f0:l4_vexpr961` (X_CHOOSE_THEN `a0_e:l4_vexpr961`
      (X_CHOOSE_THEN `mf:bool list->l4_vexpr961`
        (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))
          (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
    DISCH_THEN (LABEL_TAC "Hvcpar") THEN l4_subst_vars_tac972 THEN
    SUBGOAL_THEN
      `(?mf3 mf3'.
          l4_vpattern_matches972 pf f' m1 mf3 /\
          (!x. l4_vpath_valid972 pf x ==> l4_vpar_red_t972 env uvars pat g (mf x) (mf3 x)) /\
          (!x. l4_vpath_valid972 pf x ==> l4_vpar_red_t972 env uvars pat g (mf3 x) (mf3' x)) /\
          (!x. l4_vpath_valid972 pf x ==> l4_vnormal_eq972 env uvars g (mf3' x) (m2' (CONS F x)))) \/
       (?p1 e1' e1 m1_1 m2_1.
          l4_vsubpattern972 p1 pf /\
          (p1 = pf ==> e1 = f /\ e1' = f') /\
          l4_vpattern_matches972 p1 e1 m1_1 m2_1 /\
          ?p' r' ck' m1' m2_r m3.
            pat p' (r', ck') /\ l4_vrhs_wf972 p' r' /\ l4_vcheck_wf972 p' ck' /\
            l4_vpattern_matches972 p' e1 m1' m2_r /\
            (!x. l4_vpath_valid972 p' x ==> l4_vpar_red_t972 env uvars pat g (m2_r x) (m3 x)) /\
            e1' = l4_vrhs_apply972 m1' m3 r')`
      MP_TAC THENL
    [USE_THEN "IH_f" (MP_TAC o BETA_RULE o SPECL [`sz:num`;`pf:l4_vpattern972`;`m1:l4_vlevel961 list`;
       `mf:bool list->l4_vexpr961`;`(\x. (m2':bool list->l4_vexpr961) (CONS F x))`;
       `L4VForallE961 a1 b1`]) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
      USE_THEN "Hvcpar" (MP_TAC o SPEC `CONS F (x:bool list)`) THEN
      REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
    [SUBGOAL_THEN `?a3'. l4_vpar_red_t972 env uvars pat g a' a3' /\
                         l4_vnormal_eq972 env uvars g a3' (m2' ([]:bool list))`
       (X_CHOOSE_THEN `a3':l4_vexpr961` STRIP_ASSUME_TAC) THENL
     [FIRST_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 a`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       DISCH_THEN (MP_TAC o SPECL [`g:l4_vexpr961 list`;`a:l4_vexpr961`;`a':l4_vexpr961`;
         `(m2':bool list->l4_vexpr961) []`;`a1:l4_vexpr961`]) THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [LE_REFL] THEN
       USE_THEN "Hvcpar" (MP_TAC o SPEC `[]:bool list`) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
       DISCH_THEN ACCEPT_TAC];
      DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`l4_vmenv_var972 a' mf3`;`l4_vmenv_var972 a3' mf3'`] THEN
      REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC [];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
       ASM_REWRITE_TAC [] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
       ASM_REWRITE_TAC [] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972];
       X_GEN_TAC `x:bool list` THEN
       STRUCT_CASES_TAC (ISPEC `x:bool list` list_CASES) THEN
       REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
       ASM_REWRITE_TAC [] THEN
       STRUCT_CASES_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
       ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]]];
     DISJ2_TAC THEN
     MAP_EVERY EXISTS_TAC [`p1:l4_vpattern972`;`e1':l4_vexpr961`;`e1:l4_vexpr961`;
                           `m1_1:l4_vlevel961 list`;`m2_1:bool list->l4_vexpr961`] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vsubpattern_varL972 THEN ASM_REWRITE_TAC [];
      DISCH_THEN (fun th ->
        MP_TAC (MATCH_MP l4_vsubpattern_size_le972 (ASSUME `l4_vsubpattern972 p1 pf`)) THEN
        REWRITE_TAC [th;l4_vpattern_size972] THEN ARITH_TAC);
      ASM_REWRITE_TAC [];
      MAP_EVERY EXISTS_TAC [`p':l4_vpattern972`;`r':l4_vrhs972`;`ck':l4_vpattern_check972`;
                            `m1':l4_vlevel961 list`;`m2_r:bool list->l4_vexpr961`;
                            `m3:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC []]]];
   (* lam *)
   REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_lam972]) THEN
   FIRST_ASSUM CONTR_TAC;
   (* forallE *)
   REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_forallE972]) THEN
   FIRST_ASSUM CONTR_TAC;
   (* beta *)
   REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_app_lam972]) THEN
   FIRST_ASSUM CONTR_TAC;
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p':l4_vpattern972`;`r':l4_vrhs972`;
     `ck':l4_vpattern_check972`;`e_x:l4_vexpr961`;`m1':l4_vlevel961 list`;
     `m2_r:bool list->l4_vexpr961`;`m3:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`sz:num`;`p:l4_vpattern972`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`;`ty:l4_vexpr961`] THEN
   STRIP_TAC THEN DISJ2_TAC THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vrhs_apply972 m1' m3 r'`;`e_x:l4_vexpr961`;
                         `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vsubpattern_refl972] THEN
   MAP_EVERY EXISTS_TAC [`p':l4_vpattern972`;`r':l4_vrhs972`;`ck':l4_vpattern_check972`;
                         `m1':l4_vlevel961 list`;`m2_r:bool list->l4_vexpr961`;
                         `m3:bool list->l4_vexpr961`] THEN
   ASM_SIMP_TAC []]);;

let l4_vpar_red_t_triangle_ind972 = prove
 (`!sz.
   !env uvars pat g e oo.
     l4_vcpar_red_t972 env uvars pat g e oo ==>
     (!e' ty.
        l4_vexpr_size972 e <= sz /\
        l4_pattern_params_for972 env pat /\
        l4_vctx_wf966 env uvars g /\
        l4_vhas_type961 env uvars g e ty /\
        l4_vpar_red_t972 env uvars pat g e e' ==>
        ?o'. l4_vpar_red_t972 env uvars pat g e' o' /\
             l4_vnormal_eq972 env uvars g o' oo)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `sz:num` THEN DISCH_THEN (LABEL_TAC "IH_wf") THEN
  MATCH_MP_TAC l4_vcpar_red_t_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VBVar961 i) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [EXISTS_TAC `L4VBVar961 i` THEN REWRITE_TAC [l4_vpar_red_t_refl972] THEN
    MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_bvar972]) THEN FIRST_ASSUM CONTR_TAC];
   (* sort *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VSort961 u) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [EXISTS_TAC `L4VSort961 u` THEN REWRITE_TAC [l4_vpar_red_t_refl972] THEN
    MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_sort972]) THEN FIRST_ASSUM CONTR_TAC];
   (* const *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VConst961 c ls) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [EXISTS_TAC `L4VConst961 c ls` THEN REWRITE_TAC [l4_vpar_red_t_refl972] THEN
    MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    SUBGOAL_THEN `l4_vnon_neutral972 env uvars pat g (L4VConst961 c ls)`
      (fun th -> MP_TAC th THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [l4_vnon_neutral972] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                          `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
    ASM_REWRITE_TAC []];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`f_o:l4_vexpr961`;
     `a:l4_vexpr961`;`a_o:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP l4_pp_wf972 th) THEN
                          ASSUME_TAC (MATCH_MP l4_pp_inj972 th)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
     (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VApp961 f a) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `f0:l4_vexpr961` (X_CHOOSE_THEN `f':l4_vexpr961`
       (X_CHOOSE_THEN `a0:l4_vexpr961` (X_CHOOSE_THEN `a':l4_vexpr961` STRIP_ASSUME_TAC))))
     (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN l4_subst_rev_tac972 THENL
   [SUBGOAL_THEN
      `(?of'. l4_vpar_red_t972 env uvars pat g f' of' /\ l4_vnormal_eq972 env uvars g of' f_o) /\
       (?oa'. l4_vpar_red_t972 env uvars pat g a' oa' /\ l4_vnormal_eq972 env uvars g oa' a_o)`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VForallE961 a1 b1` THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `a1:l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f a) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC];
     SUBGOAL_THEN `l4_vhas_type961 env uvars g of' (L4VForallE961 a1 b1) /\
                   l4_vhas_type961 env uvars g oa' a1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`f':l4_vexpr961`] THEN
       ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`f:l4_vexpr961`] THEN
       ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`a':l4_vexpr961`] THEN
       ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`a:l4_vexpr961`] THEN
       ASM_REWRITE_TAC []];
      EXISTS_TAC `L4VApp961 of' oa'` THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vprt_app972 THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vn_appDF972 THEN
       MAP_EVERY EXISTS_TAC [`a1:l4_vexpr961`;`b1:l4_vexpr961`] THEN
       ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THENL
       [EXISTS_TAC `of':l4_vexpr961` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
        EXISTS_TAC `oa':l4_vexpr961` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]]]]];
    SUBGOAL_THEN `l4_vnon_neutral972 env uvars pat g (L4VApp961 (L4VLam961 dom e1) a)`
      (fun th -> MP_TAC th THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [l4_vnon_neutral972] THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`e1:l4_vexpr961`;`a:l4_vexpr961`] THEN REFL_TAC;
    SUBGOAL_THEN `l4_vnon_neutral972 env uvars pat g (L4VApp961 f a)`
      (fun th -> MP_TAC th THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [l4_vnon_neutral972] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                          `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
    ASM_REWRITE_TAC []];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom:l4_vexpr961`;`dom_o:l4_vexpr961`;
     `body:l4_vexpr961`;`body_o:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP l4_pp_wf972 th) THEN
                          ASSUME_TAC (MATCH_MP l4_pp_inj972 th)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `b1:l4_vexpr961`)) THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VLam961 dom body) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `dom0:l4_vexpr961` (X_CHOOSE_THEN `dom':l4_vexpr961`
       (X_CHOOSE_THEN `body0:l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961` STRIP_ASSUME_TAC))))
     STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(?odom'. l4_vpar_red_t972 env uvars pat g dom' odom' /\ l4_vnormal_eq972 env uvars g odom' dom_o) /\
       (?obd'. l4_vpar_red_t972 env uvars pat (CONS dom g) body' obd' /\
               l4_vnormal_eq972 env uvars (CONS dom g) obd' body_o)`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 u` THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 dom body) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `b1:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 dom body) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC];
     SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom dom' (L4VSort961 u)` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
      EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom odom' (L4VSort961 u)` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
      EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
      MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`dom:l4_vexpr961`] THEN
      ASM_REWRITE_TAC []; ALL_TAC] THEN
     EXISTS_TAC `L4VLam961 odom' obd'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vprt_lam972 THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`b1:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
       ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
       MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`body:l4_vexpr961`] THEN
       ASM_REWRITE_TAC []];
      MATCH_MP_TAC l4_vn_lamDF972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `odom':l4_vexpr961` THEN
      ASM_SIMP_TAC [l4_vnormal_eq_defeq972]]];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_lam972]) THEN FIRST_ASSUM CONTR_TAC];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom:l4_vexpr961`;`dom_o:l4_vexpr961`;
     `cod:l4_vexpr961`;`cod_o:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP l4_pp_wf972 th) THEN
                          ASSUME_TAC (MATCH_MP l4_pp_inj972 th)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VForallE961 dom cod) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `dom0:l4_vexpr961` (X_CHOOSE_THEN `dom':l4_vexpr961`
       (X_CHOOSE_THEN `cod0:l4_vexpr961` (X_CHOOSE_THEN `cod':l4_vexpr961` STRIP_ASSUME_TAC))))
     STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(?odom'. l4_vpar_red_t972 env uvars pat g dom' odom' /\ l4_vnormal_eq972 env uvars g odom' dom_o) /\
       (?ocod'. l4_vpar_red_t972 env uvars pat (CONS dom g) cod' ocod' /\
                l4_vnormal_eq972 env uvars (CONS dom g) ocod' cod_o)`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 u` THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VForallE961 dom cod) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `L4VSort961 v` THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VForallE961 dom cod) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC];
     SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom dom' (L4VSort961 u)` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
      EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom odom' (L4VSort961 u)` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
      EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
      MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`dom:l4_vexpr961`] THEN
      ASM_REWRITE_TAC []; ALL_TAC] THEN
     EXISTS_TAC `L4VForallE961 odom' ocod'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vprt_forallE972 THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`L4VSort961 v`] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
       ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
       MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`cod:l4_vexpr961`] THEN
       ASM_REWRITE_TAC []];
      MATCH_MP_TAC l4_vn_forallEDF972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
      MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`cod':l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
      MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`cod:l4_vexpr961`] THEN
      ASM_REWRITE_TAC []]];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_forallE972]) THEN FIRST_ASSUM CONTR_TAC];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom:l4_vexpr961`;
     `e1:l4_vexpr961`;`e1_o:l4_vexpr961`;`e2:l4_vexpr961`;`e2_o:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP l4_pp_wf972 th) THEN
                          ASSUME_TAC (MATCH_MP l4_pp_inj972 th)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VLam961 dom e1`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1:l4_vexpr961`
     (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 a1 b1`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `b2:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 a1 b1) (L4VForallE961 dom b2)`
     MP_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`L4VLam961 dom e1`;`L4VLam961 dom e1`;`L4VLam961 dom e1`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (fun th ->
     MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
       (CONJ (ASSUME `l4_defeq_injectivity972 env`)
         (CONJ (ASSUME `l4_vctx_wf966 env uvars g`) th))))) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g e2 dom` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `a1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VApp961 (L4VLam961 dom e1) e2) e'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `f0:l4_vexpr961` (X_CHOOSE_THEN `f':l4_vexpr961`
       (X_CHOOSE_THEN `a0:l4_vexpr961` (X_CHOOSE_THEN `a':l4_vexpr961` STRIP_ASSUME_TAC))))
     (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `dom0:l4_vexpr961` (X_CHOOSE_THEN `e1_0:l4_vexpr961`
         (X_CHOOSE_THEN `e1':l4_vexpr961` (X_CHOOSE_THEN `e2_0:l4_vexpr961`
           (X_CHOOSE_THEN `e2':l4_vexpr961` STRIP_ASSUME_TAC)))))
       STRIP_ASSUME_TAC)) THEN l4_subst_rev_tac972 THENL
   [(* app vs beta *)
    SUBGOAL_THEN `?oa'. l4_vpar_red_t972 env uvars pat g a' oa' /\
                        l4_vnormal_eq972 env uvars g oa' e2_o`
      (X_CHOOSE_THEN `oa':l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
     UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
     REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VLam961 dom e1) f'` THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
    REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `dom0:l4_vexpr961` (X_CHOOSE_THEN `dom':l4_vexpr961`
        (X_CHOOSE_THEN `body0:l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961` STRIP_ASSUME_TAC))))
      STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
    [SUBGOAL_THEN `?oe'. l4_vpar_red_t972 env uvars pat (CONS dom g) body' oe' /\
                         l4_vnormal_eq972 env uvars (CONS dom g) oe' e1_o`
       (X_CHOOSE_THEN `oe':l4_vexpr961` STRIP_ASSUME_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `b2:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
     EXISTS_TAC `l4_vinst0961 oe' oa'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vprt_beta972 THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`b2:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
       ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966] THEN
       MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
       EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e1:l4_vexpr961`] THEN
       ASM_REWRITE_TAC []];
      MATCH_MP_TAC l4_vnormal_eq_trans972 THEN
      EXISTS_TAC `l4_vinst0961 oe' e2_o` THEN ASM_REWRITE_TAC [l4_vinst0961] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC l4_vnormal_eq_instN_r972 THEN
        MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                              `CONS (dom:l4_vexpr961) g`;`b2:l4_vexpr961`] THEN
        ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN CONJ_TAC THENL
        [MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`a':l4_vexpr961`] THEN
         ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2:l4_vexpr961`] THEN
         ASM_REWRITE_TAC [];
         MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`body':l4_vexpr961`] THEN
         ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e1:l4_vexpr961`] THEN
         ASM_REWRITE_TAC []];
        MATCH_MP_TAC l4_vnormal_eq_instN972 THEN
        MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                              `CONS (dom:l4_vexpr961) g`] THEN
        ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
        MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
        MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2:l4_vexpr961`] THEN
        ASM_SIMP_TAC [l4_vcpar_red_t_to_vpar_red_t972]]];
      RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_lam972]) THEN FIRST_ASSUM CONTR_TAC];
     (* beta vs beta *)
     SUBGOAL_THEN
       `(?oe'. l4_vpar_red_t972 env uvars pat (CONS dom g) e1' oe' /\
               l4_vnormal_eq972 env uvars (CONS dom g) oe' e1_o) /\
        (?oa'. l4_vpar_red_t972 env uvars pat g e2' oa' /\
               l4_vnormal_eq972 env uvars g oa' e2_o)`
       STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `b2:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
       UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC;
       FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
       UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 (L4VLam961 dom e1) e2) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC];
      EXISTS_TAC `l4_vinst0961 oe' oa'` THEN REWRITE_TAC [l4_vinst0961] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vpar_red_t_instN972 THEN
       MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                             `CONS (dom:l4_vexpr961) g`] THEN
       ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
       MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
       MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2:l4_vexpr961`] THEN
       ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vnormal_eq_trans972 THEN
       EXISTS_TAC `l4_vinst961 oe' e2_o 0` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC l4_vnormal_eq_instN_r972 THEN
        MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                              `CONS (dom:l4_vexpr961) g`;`b2:l4_vexpr961`] THEN
        ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN CONJ_TAC THENL
        [MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2':l4_vexpr961`] THEN
         ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2:l4_vexpr961`] THEN
         ASM_REWRITE_TAC [];
         MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e1':l4_vexpr961`] THEN
         ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
         MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e1:l4_vexpr961`] THEN
         ASM_REWRITE_TAC []];
        MATCH_MP_TAC l4_vnormal_eq_instN972 THEN
        MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;
                              `CONS (dom:l4_vexpr961) g`] THEN
        ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
        MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
        MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e2:l4_vexpr961`] THEN
        ASM_SIMP_TAC [l4_vcpar_red_t_to_vpar_red_t972]]]];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_app_lam972]) THEN FIRST_ASSUM CONTR_TAC];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e0:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC
           (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HIH_extra")))))) THEN
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP l4_pp_wf972 th) THEN
                          ASSUME_TAC (MATCH_MP l4_pp_inj972 th)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`e0:l4_vexpr961`;`e':l4_vexpr961`]
     l4_vpar_red_t_triangle_extra_cases972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`sz:num`;`p:l4_vpattern972`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`;`ty:l4_vexpr961`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN
     USE_THEN "HIH_extra" (fun th ->
       ACCEPT_TAC (CONJUNCT1 (MATCH_MP (SPEC `a:bool list` th)
         (ASSUME `l4_vpath_valid972 p a`))));
     REPEAT STRIP_TAC THEN
     USE_THEN "IH_wf" (fun th ->
       MP_TAC (SPECL [`d0':l4_vexpr961`;`ty0:l4_vexpr961`]
         (MATCH_MP (SPECL [`env:l4_venv961`;`uvars:num`;
           `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
           `g0:l4_vexpr961 list`;`d0:l4_vexpr961`;`o0:l4_vexpr961`]
           (MATCH_MP th (ASSUME `m < sz`)))
           (ASSUME `l4_vcpar_red_t972 env uvars pat g0 d0 o0`)))) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* Left: e' still matches p *)
    SUBGOAL_THEN `l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m3 ck`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g`;
                           `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN
     MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
     REWRITE_TAC [l4_vis_defeq_u961] THEN
     DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty_ab:l4_vexpr961`))) THEN
     SUBGOAL_THEN `l4_vis_defeq961 env uvars g (l4_vrhs_apply972 m1 m2 ra)
                     (l4_vrhs_apply972 m1 m3 ra) ty_ab /\
                   l4_vis_defeq961 env uvars g (l4_vrhs_apply972 m1 m2 rb)
                     (l4_vrhs_apply972 m1 m3 rb) ty_ab` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_apply_pat972 THEN
      EXISTS_TAC `p:l4_vpattern972` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
       EXISTS_TAC `ty0:l4_vexpr961` THEN
       MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
       EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
       ASM_SIMP_TAC [];
       MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
       EXISTS_TAC `l4_vrhs_apply972 m1 m2 rb` THEN ASM_REWRITE_TAC [];
       REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
       EXISTS_TAC `ty0:l4_vexpr961` THEN
       MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
       EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
       ASM_SIMP_TAC [];
       MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN
       EXISTS_TAC `l4_vrhs_apply972 m1 m2 ra` THEN ASM_REWRITE_TAC []];
      EXISTS_TAC `ty_ab:l4_vexpr961` THEN
      MATCH_MP_TAC l4_vis_defeq_trans961 THEN
      EXISTS_TAC `l4_vrhs_apply972 m1 m2 ra` THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vis_defeq_trans961 THEN
       EXISTS_TAC `l4_vrhs_apply972 m1 m2 rb` THEN ASM_REWRITE_TAC []]]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat g e' (l4_vrhs_apply972 m1 m3' r)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vprt_extra972 THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
                           `m3:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    EXISTS_TAC `l4_vrhs_apply972 m1 m3' r` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vnormal_eq_apply_pat972 THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ty:l4_vexpr961`] THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
    MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
    MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e0:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [];
    (* Right: overlap with another pattern p' -> pp_uniq forces p = p' = p1 *)
    SUBGOAL_THEN `?p4 mr1 mr2. l4_vpattern_inter972 p' p1 = SOME p4 /\
                               l4_vpattern_matches972 p4 e1 mr1 mr2`
      STRIP_ASSUME_TAC THENL
    [REWRITE_TAC [GSYM l4_vpattern_matches_inter972] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`m1':l4_vlevel961 list`;`m2_r:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC [];
      MAP_EVERY EXISTS_TAC [`m1_1:l4_vlevel961 list`;`m2_1:bool list->l4_vexpr961`] THEN ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    SUBGOAL_THEN `p:l4_vpattern972 = p' /\ p' = p1` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [MATCH_MP_TAC l4_pp_uniq972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;
       `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
       `p4:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
       `r':l4_vrhs972`;`ck':l4_vpattern_check972`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `r:l4_vrhs972 = r' /\ ck:l4_vpattern_check972 = ck'` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [MATCH_MP_TAC l4_pp_rhs_uniq972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;
       `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
       `p1:l4_vpattern972`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `e1:l4_vexpr961 = e0 /\ e1':l4_vexpr961 = e'` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [FIRST_X_ASSUM (fun th -> MATCH_MP_TAC th THEN REFL_TAC); ALL_TAC] THEN
    SUBGOAL_THEN `m1:l4_vlevel961 list = m1' /\ m2:bool list->l4_vexpr961 = m2_r`
      (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [MATCH_MP_TAC l4_vpattern_matches_uniq972 THEN
     MAP_EVERY EXISTS_TAC [`p1:l4_vpattern972`;`e0:l4_vexpr961`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `?m3'. l4_vmenv_wf972 p1 m3' /\
                        (!a. l4_vpath_valid972 p1 a ==>
                             l4_vpar_red_t972 env uvars pat g (m3 a) (m3' a) /\
                             l4_vnormal_eq972 env uvars g (m3' a) (m2' a))`
      (X_CHOOSE_THEN `m3':bool list->l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [MP_TAC (SPECL [`p1:l4_vpattern972`;
                    `\(a:bool list) (y:l4_vexpr961).
                       l4_vpar_red_t972 env uvars pat g ((m3:bool list->l4_vexpr961) a) y /\
                       l4_vnormal_eq972 env uvars g y ((m2':bool list->l4_vexpr961) a)`]
               l4_vmenv_rel_choice972) THEN
     REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `a:bool list` THEN DISCH_TAC THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `p1:l4_vpattern972`;`e0:l4_vexpr961`;`m1':l4_vlevel961 list`;
                    `m2_r:bool list->l4_vexpr961`;`ty:l4_vexpr961`;`a:bool list`]
       l4_vpattern_matches_has_type972) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `ty_a:l4_vexpr961`) THEN
     MP_TAC (SPECL [`p1:l4_vpattern972`;`e0:l4_vexpr961`;`m1':l4_vlevel961 list`;
                    `m2_r:bool list->l4_vexpr961`;`a:bool list`]
       l4_vpattern_matches_path_size972) THEN
     ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
     USE_THEN "HIH_extra" (fun th ->
       MP_TAC (CONJUNCT2 (MATCH_MP (SPEC `a:bool list` th)
         (ASSUME `l4_vpath_valid972 p1 a`)))) THEN
     DISCH_THEN (fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `ty_a:l4_vexpr961` THEN
       ASM_SIMP_TAC [] THEN ASM_ARITH_TAC);
     SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat g (l4_vrhs_apply972 m1' m3 r')
                     (l4_vrhs_apply972 m1' m3' r')` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_t_apply_pat972 THEN EXISTS_TAC `p1:l4_vpattern972` THEN
      ASM_SIMP_TAC []; ALL_TAC] THEN
     EXISTS_TAC `l4_vrhs_apply972 m1' m3' r'` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vnormal_eq_apply_pat972 THEN
     MAP_EVERY EXISTS_TAC [`p1:l4_vpattern972`;`ty:l4_vexpr961`] THEN
     ASM_SIMP_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
     MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                           `l4_vrhs_apply972 m1' m3 r'`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
     MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`e0:l4_vexpr961`] THEN
     UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g e0 e'` THEN ASM_REWRITE_TAC []]]]);;

let l4_vpar_red_t_triangle972 = prove
 (`!env uvars pat g e e' oo ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpar_red_t972 env uvars pat g e e' /\
   l4_vcpar_red_t972 env uvars pat g e oo ==>
   ?o'. l4_vpar_red_t972 env uvars pat g e' o' /\
        l4_vnormal_eq972 env uvars g o' oo`,
  MESON_TAC [l4_vpar_red_t_triangle_ind972;LE_REFL]);;

let l4_vpar_red_t_church_rosser972 = prove
 (`!env uvars pat g e e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpar_red_t972 env uvars pat g e e1 /\
   l4_vpar_red_t972 env uvars pat g e e2 ==>
   ?e1' e2'.
     l4_vpar_red_t972 env uvars pat g e1 e1' /\
     l4_vpar_red_t972 env uvars pat g e2 e2' /\
     l4_vnormal_eq972 env uvars g e1' e2'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?oo. l4_vcpar_red_t972 env uvars pat g e oo` (X_CHOOSE_TAC `oo:l4_vexpr961`) THENL
  [ASM_MESON_TAC [l4_vcpar_red_t_exists972]; ALL_TAC] THEN
  SUBGOAL_THEN `(?e1'. l4_vpar_red_t972 env uvars pat g e1 e1' /\ l4_vnormal_eq972 env uvars g e1' oo) /\
                (?e2'. l4_vpar_red_t972 env uvars pat g e2 e2' /\ l4_vnormal_eq972 env uvars g e2' oo)`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_MESON_TAC [l4_vpar_red_t_triangle972];
   MAP_EVERY EXISTS_TAC [`e1':l4_vexpr961`;`e2':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
   ASM_MESON_TAC [l4_vnormal_eq_trans972;l4_vnormal_eq_symm972;l4_pp_wf972;l4_pp_inj972]]);;

(* Multi-step Typed Parallel Reduction VParRedTS *)

let l4_vpar_red_ts_has_type_ind972 = prove
 (`!R e e'.
   l4_vrt_closure972 R e e' ==>
   (!env uvars pat g ty.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e ty ==>
      l4_vhas_type961 env uvars g e' ty)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN
  MESON_TAC [l4_vpar_red_t_has_type972]);;

let l4_vpar_red_ts_has_type972 = prove
 (`!env uvars pat g e e' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vpar_red_ts972 env uvars pat g e e' /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vhas_type961 env uvars g e' ty`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN MESON_TAC [l4_vpar_red_ts_has_type_ind972]);;

let l4_vpar_red_ts_defeq_ind972 = prove
 (`!R e e'.
   l4_vrt_closure972 R e e' ==>
   (!env uvars pat g ty.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e ty ==>
      l4_vis_defeq961 env uvars g e e' ty)`,
  MATCH_MP_TAC l4_vrt_closure_STRONG_INDUCT972 THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN SIMP_TAC [];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `y:l4_vexpr961` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
    EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
    ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_ts972]]]);;

let l4_vpar_red_ts_defeq972 = prove
 (`!env uvars pat g e e' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vpar_red_ts972 env uvars pat g e e' /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vis_defeq961 env uvars g e e' ty`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN MESON_TAC [l4_vpar_red_ts_defeq_ind972]);;

let l4_vpar_red_ts_defeqDFC_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat g0 g1 g2 ty.
      R = l4_vpar_red_t972 env uvars pat g1 /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      l4_vhas_type961 env uvars g1 e1 ty ==>
      l4_vpar_red_ts972 env uvars pat g2 e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_STRONG_INDUCT972 THEN
  REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g1` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_ctx_wf972;l4_pp_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vrtc_tail972 THEN EXISTS_TAC `y:l4_vexpr961` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`;`ty:l4_vexpr961`] THEN
    ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_ts972]]]);;

let l4_vpar_red_ts_defeqDFC972 = prove
 (`!env uvars pat g0 g1 g2 e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vhas_type961 env uvars g1 e1 ty /\
   l4_vpar_red_ts972 env uvars pat g1 e1 e2 ==>
   l4_vpar_red_ts972 env uvars pat g2 e1 e2`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vpar_red_ts_defeqDFC_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_ts_app_r_ind972 = prove
 (`!R a a'.
   l4_vrt_closure972 R a a' ==>
   (!env uvars pat g f.
      R = l4_vpar_red_t972 env uvars pat g ==>
      l4_vpar_red_ts972 env uvars pat g (L4VApp961 f a) (L4VApp961 f a'))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_app972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_app_l_ind972 = prove
 (`!R f f'.
   l4_vrt_closure972 R f f' ==>
   (!env uvars pat g a.
      R = l4_vpar_red_t972 env uvars pat g ==>
      l4_vpar_red_ts972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_app972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_app972 = prove
 (`!env uvars pat g f f' a a'.
   l4_vpar_red_ts972 env uvars pat g f f' /\
   l4_vpar_red_ts972 env uvars pat g a a' ==>
   l4_vpar_red_ts972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a')`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts_app_r_ind972;
             l4_vpar_red_ts_app_l_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_ts_lam_r_ind972 = prove
 (`!R b b'.
   l4_vrt_closure972 R b b' ==>
   (!env uvars pat g dom.
      R = l4_vpar_red_t972 env uvars pat (CONS dom g) ==>
      l4_vpar_red_ts972 env uvars pat g (L4VLam961 dom b) (L4VLam961 dom b'))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_lam972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_lam_l_ind972 = prove
 (`!R dom dom'.
   l4_vrt_closure972 R dom dom' ==>
   (!env uvars pat g b.
      R = l4_vpar_red_t972 env uvars pat g ==>
      l4_vpar_red_ts972 env uvars pat g (L4VLam961 dom b) (L4VLam961 dom' b))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_lam972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_lam972 = prove
 (`!env uvars pat g dom dom' b b'.
   l4_vpar_red_ts972 env uvars pat g dom dom' /\
   l4_vpar_red_ts972 env uvars pat (CONS dom g) b b' ==>
   l4_vpar_red_ts972 env uvars pat g (L4VLam961 dom b) (L4VLam961 dom' b')`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts_lam_r_ind972;
             l4_vpar_red_ts_lam_l_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_ts_forallE_r_ind972 = prove
 (`!R cod cod'.
   l4_vrt_closure972 R cod cod' ==>
   (!env uvars pat g dom.
      R = l4_vpar_red_t972 env uvars pat (CONS dom g) ==>
      l4_vpar_red_ts972 env uvars pat g (L4VForallE961 dom cod) (L4VForallE961 dom cod'))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_forallE972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_forallE_l_ind972 = prove
 (`!R dom dom'.
   l4_vrt_closure972 R dom dom' ==>
   (!env uvars pat g cod.
      R = l4_vpar_red_t972 env uvars pat g ==>
      l4_vpar_red_ts972 env uvars pat g (L4VForallE961 dom cod) (L4VForallE961 dom' cod))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vprt_forallE972;l4_vpar_red_t_refl972]);;

let l4_vpar_red_ts_forallE972 = prove
 (`!env uvars pat g dom dom' cod cod'.
   l4_vpar_red_ts972 env uvars pat g dom dom' /\
   l4_vpar_red_ts972 env uvars pat (CONS dom g) cod cod' ==>
   l4_vpar_red_ts972 env uvars pat g (L4VForallE961 dom cod) (L4VForallE961 dom' cod')`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts_forallE_r_ind972;
             l4_vpar_red_ts_forallE_l_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_ts_inst_r_ind972 = prove
 (`!R a a'.
   l4_vrt_closure972 R a a' ==>
   (!env uvars pat g f dom.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g a dom ==>
      l4_vpar_red_ts972 env uvars pat g (l4_vinst0961 f a) (l4_vinst0961 f a'))`,
  MATCH_MP_TAC l4_vrt_closure_STRONG_INDUCT972 THEN
  REWRITE_TAC [l4_vpar_red_ts972;l4_vinst0961] THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vrtc_tail972 THEN EXISTS_TAC `l4_vinst961 f y 0` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vpar_red_t_instN972 THEN
    MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
    REWRITE_TAC [l4_vctx_instN_zero966;l4_vpar_red_t_refl972] THEN
    ASM_MESON_TAC [l4_pp_wf972;l4_vpar_red_ts_has_type972;l4_vpar_red_ts972]]]);;

let l4_vpar_red_ts_inst_l_ind972 = prove
 (`!R f f'.
   l4_vrt_closure972 R f f' ==>
   (!env uvars pat g a' dom.
      R = l4_vpar_red_t972 env uvars pat (CONS dom g) /\
      l4_venv_wf966 env /\
      l4_vhas_type961 env uvars g a' dom ==>
      l4_vpar_red_ts972 env uvars pat g (l4_vinst0961 f a') (l4_vinst0961 f' a'))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN
  REWRITE_TAC [l4_vpar_red_ts972;l4_vinst0961] THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vrtc_tail972 THEN EXISTS_TAC `l4_vinst961 y a' 0` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vpar_red_t_instN972 THEN
    MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g`] THEN
    ASM_REWRITE_TAC [l4_vctx_instN_zero966;l4_vpar_red_t_refl972]]]);;

let l4_vpar_red_ts_inst972 = prove
 (`!env uvars pat g f f' a a' dom.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g a dom /\
   l4_vpar_red_ts972 env uvars pat (CONS dom g) f f' /\
   l4_vpar_red_ts972 env uvars pat g a a' ==>
   l4_vpar_red_ts972 env uvars pat g (l4_vinst0961 f a) (l4_vinst0961 f' a')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars g a' dom` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vpar_red_ts_has_type972];
   REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
   EXISTS_TAC `l4_vinst0961 f a'` THEN
   ASM_MESON_TAC [l4_vpar_red_ts_inst_r_ind972;l4_vpar_red_ts_inst_l_ind972;
                  l4_vpar_red_ts972;l4_pp_wf972]]);;

let l4_vpar_red_ts_weakN_ind972 = prove
 (`!R e e'.
   l4_vrt_closure972 R e e' ==>
   (!env uvars pat n k g g'.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_venv_wf966 env /\
      l4_vctx_liftN966 n k g g' ==>
      l4_vpar_red_ts972 env uvars pat g' (l4_vliftN961 e n k) (l4_vliftN961 e' n k))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vpar_red_t_weakN972]);;

let l4_vpar_red_ts_weakN972 = prove
 (`!env uvars pat n k g g' e e'.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vpar_red_ts972 env uvars pat g e e' ==>
   l4_vpar_red_ts972 env uvars pat g' (l4_vliftN961 e n k) (l4_vliftN961 e' n k)`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vpar_red_ts_weakN_ind972;l4_vpar_red_ts972]);;

(* ParRedExt & beta simulation under eta-expanded neutral chains *)

let l4_vpar_red_ext_INDUCT972,l4_vpar_red_ext_RECURSION972 = define_type
 "l4_vpar_red_ext972 = L4VPEBase972
                     | L4VPELift972 l4_vpar_red_ext972
                     | L4VPEApp972 l4_vpar_red_ext972";;

let l4_vpe_depth972 = new_recursive_definition l4_vpar_red_ext_RECURSION972
 `(l4_vpe_depth972 L4VPEBase972 = 0) /\
  (l4_vpe_depth972 (L4VPELift972 l) = l4_vpe_depth972 l + 1) /\
  (l4_vpe_depth972 (L4VPEApp972 l) = l4_vpe_depth972 l + 1)`;;

let l4_vpe_apply972 = new_recursive_definition l4_vpar_red_ext_RECURSION972
 `(l4_vpe_apply972 L4VPEBase972 e = e) /\
  (l4_vpe_apply972 (L4VPELift972 l) e = l4_vlift961 (l4_vpe_apply972 l e)) /\
  (l4_vpe_apply972 (L4VPEApp972 l) e =
     L4VApp961 (l4_vlift961 (l4_vpe_apply972 l e)) (L4VBVar961 0))`;;

let l4_vpe_meas972 = new_recursive_definition l4_vpar_red_ext_RECURSION972
 `(l4_vpe_meas972 L4VPEBase972 = 0) /\
  (l4_vpe_meas972 (L4VPELift972 l) = l4_vpe_meas972 l + 1) /\
  (l4_vpe_meas972 (L4VPEApp972 l) = l4_vpe_meas972 l + 2)`;;

let l4_vis_app972 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vis_app972 (L4VBVar961 i) <=> F) /\
  (l4_vis_app972 (L4VSort961 u) <=> F) /\
  (l4_vis_app972 (L4VConst961 c ls) <=> F) /\
  (l4_vis_app972 (L4VApp961 f a) <=> T) /\
  (l4_vis_app972 (L4VLam961 dom body) <=> F) /\
  (l4_vis_app972 (L4VForallE961 dom cod) <=> F)`;;

let l4_vpe_is_app972 = prove
 (`!l f a. l4_vis_app972 (l4_vpe_apply972 l (L4VApp961 f a))`,
  MATCH_MP_TAC l4_vpar_red_ext_INDUCT972 THEN
  REWRITE_TAC [l4_vpe_apply972;l4_vis_app972] THEN
  X_GEN_TAC `l:l4_vpar_red_ext972` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`f:l4_vexpr961`;`a:l4_vexpr961`]) THEN
  STRUCT_CASES_TAC (SPEC `l4_vpe_apply972 l (L4VApp961 f a)` l4_vexpr_CASES961) THEN
  REWRITE_TAC [l4_vis_app972;l4_vlift961;l4_vliftN961]);;

let l4_has_type_app_bvar0972 = prove
 (`!env uvars g dom e cod.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars (CONS dom g) /\
   l4_vhas_type961 env uvars (CONS dom g) (L4VApp961 (l4_vlift961 e) (L4VBVar961 0)) cod ==>
   ?cod'. l4_vhas_type961 env uvars g e (L4VForallE961 dom cod')`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                 `l4_vlift961 e`;`L4VBVar961 0`;`cod:l4_vexpr961`]
    l4_vhas_type_app_inv970) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `a0:l4_vexpr961`
    (X_CHOOSE_THEN `b0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                 `l4_vlift961 e`;`l4_vlift961 e`;`L4VForallE961 a0 b0`]
    l4_vis_defeq_is_type966) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                 `a0:l4_vexpr961`;`b0:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
  ASM_REWRITE_TAC [l4_vis_type961] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 env uvars (CONS dom g) a0 (l4_vlift961 dom) (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
   MAP_EVERY EXISTS_TAC [`L4VBVar961 0`;`L4VBVar961 0`;`L4VBVar961 0`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
   REWRITE_TAC [l4_vlookup_zero961]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS dom g)
                  (l4_vlift961 e) (L4VForallE961 (l4_vlift961 dom) b0)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `L4VForallE961 a0 b0` THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 env uvars (CONS dom g)
                  (l4_vlift961 (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))))
                  (l4_vlift961 e)` MP_TAC THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 (l4_vlift961 dom) b0` THEN
   SUBGOAL_THEN `l4_vlift961 (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) =
                 L4VLam961 (l4_vlift961 dom) (L4VApp961 (l4_vlift961 (l4_vlift961 e)) (L4VBVar961 0))`
     SUBST1_TAC THENL
   [REWRITE_TAC [l4_vlift961;l4_vliftN961;l4_vlift_var961;ARITH_RULE `0 < SUC 0`;ONE] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (SPECL [`e:l4_vexpr961`;`1`;`1`;`0`;`1`] l4_vliftN_vliftN966) THEN
    REWRITE_TAC [ARITH_RULE `0 <= 1 /\ 1 <= 1 + 0`;l4_vliftN_comp966;l4_vlift961;ONE];
    MATCH_MP_TAC l4_vis_defeq_eta961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`0`;
                 `g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;
                 `L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))`;`e:l4_vexpr961`]
    l4_vis_defeq_u_weakN_iff972) THEN
  ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
  DISCH_THEN (X_CHOOSE_TAC `ty0:l4_vexpr961`) THEN
  SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vctx_wf966]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `dom:l4_vexpr961`;`L4VApp961 (l4_vlift961 e) (L4VBVar961 0)`;`ty0:l4_vexpr961`]
    l4_vhas_type_lam_inv970) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
   EXISTS_TAC `e:l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `w:l4_vlevel961`) (X_CHOOSE_TAC `cod':l4_vexpr961`)) THEN
  EXISTS_TAC `cod':l4_vexpr961` THEN
  MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
  EXISTS_TAC `L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))` THEN
  ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN CONJ_TAC THENL
  [EXISTS_TAC `ty0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `w:l4_vlevel961` THEN ASM_REWRITE_TAC []]);;

let l4_vpe_app_decomp972 = prove
 (`!l dom e' f' a'.
   l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e')) (L4VBVar961 0)) =
   L4VApp961 f' a' ==>
   ?n. a' = L4VBVar961 n /\
       ((f' = l4_vliftN961 (L4VLam961 dom e') (n + 1) 0 /\
         l4_vpe_apply972 l e' = l4_vliftN961 e' n 0) \/
        (?l'. l4_vpe_depth972 l' <= l4_vpe_depth972 l /\
              f' = l4_vpe_apply972 l' (L4VApp961 (l4_vlift961 (L4VLam961 dom e')) (L4VBVar961 0)) /\
              l4_vpe_apply972 l e' = L4VApp961 (l4_vpe_apply972 l' e') (L4VBVar961 n)))`,
  MATCH_MP_TAC l4_vpar_red_ext_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vpe_apply972;injectivity "l4_vexpr961"] THEN
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   EXISTS_TAC `0` THEN REWRITE_TAC [ARITH_RULE `0 + 1 = 1`;l4_vlift961;l4_vliftN_zero961];
   X_GEN_TAC `l:l4_vpar_red_ext972` THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`e':l4_vexpr961`;`f':l4_vexpr961`;`a':l4_vexpr961`] THEN
   REWRITE_TAC [l4_vpe_apply972] THEN
   SUBGOAL_THEN `?a0 a1. l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e')) (L4VBVar961 0)) = L4VApp961 a0 a1`
     (X_CHOOSE_THEN `a0:l4_vexpr961` (X_CHOOSE_THEN `a1:l4_vexpr961` ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom e')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN
    STRUCT_CASES_TAC (SPEC `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e')) (L4VBVar961 0))`
      l4_vexpr_CASES961) THEN
    REWRITE_TAC [l4_vis_app972] THEN MESON_TAC []; ALL_TAC] THEN
   FIRST_ASSUM (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [l4_vlift961] THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [l4_vliftN961] THEN
   GEN_REWRITE_TAC LAND_CONV [injectivity "l4_vexpr961"] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`dom:l4_vexpr961`;`e':l4_vexpr961`;
                                  `a0:l4_vexpr961`;`a1:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC
     (DISJ_CASES_THEN STRIP_ASSUME_TAC))) THENL
   [EXISTS_TAC `1 + n` THEN
    ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961;ARITH_RULE `~(n < 0)`;
                     ARITH_RULE `n + 1 = 1 + n`] THEN
    DISJ1_TAC THEN
    REWRITE_TAC [l4_vlift961;l4_vliftN_comp966;ARITH_RULE `(1 + n) + 1 = 1 + n + 1`;
                 ARITH_RULE `n + 1 = 1 + n`];
    EXISTS_TAC `1 + n` THEN
    ASM_REWRITE_TAC [l4_vliftN961;l4_vlift_var961;ARITH_RULE `~(n < 0)`;
                     ARITH_RULE `n + 1 = 1 + n`] THEN
    DISJ2_TAC THEN EXISTS_TAC `L4VPELift972 l'` THEN
    ASM_REWRITE_TAC [l4_vpe_depth972;l4_vpe_apply972;l4_vlift961;l4_vliftN961;
                 l4_vlift_var961;ARITH_RULE `~(n < 0)`;ARITH_RULE `n + 1 = 1 + n`] THEN
    ASM_ARITH_TAC];
   X_GEN_TAC `l:l4_vpar_red_ext972` THEN DISCH_TAC THEN
   REWRITE_TAC [l4_vpe_apply972;injectivity "l4_vexpr961"] THEN
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   EXISTS_TAC `0` THEN REWRITE_TAC [] THEN DISJ2_TAC THEN
   EXISTS_TAC `L4VPELift972 l` THEN
   REWRITE_TAC [l4_vpe_depth972;l4_vpe_apply972;LE_REFL]]);;

let l4_vinst0_vliftN_succ_bvar972 = prove
 (`!e n. l4_vinst0961 (l4_vliftN961 e (n + 1) 1) (L4VBVar961 n) = l4_vliftN961 e n 0`,
  REPEAT GEN_TAC THEN
  MP_TAC (AP_TERM `(\x. l4_vliftN961 x n 0)` (SPECL [`e:l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966)) THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM l4_vinst0961;l4_vliftN_vinst0966;l4_vliftN961;l4_vlift_var961;
               ARITH_RULE `~(0 < 0)`;ADD_CLAUSES;
               l4_vliftN_comp966;GSYM ONE]);;

let l4_vpe_refl_beta_ind972 = prove
 (`!env uvars pat dom e0'.
   l4_pattern_params_for972 env pat ==>
   !m l g ty.
     l4_vpe_meas972 l <= m /\
     l4_vctx_wf966 env uvars g /\
     l4_vpe_depth972 l <= LENGTH g /\
     l4_vhas_type961 env uvars g
       (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) ty ==>
     ?e. l4_vpar_red_ts972 env uvars pat g
           (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) e /\
         l4_vnormal_eq972 env uvars g e (l4_vpe_apply972 l e0')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`l:l4_vpar_red_ext972`;`g:l4_vexpr961 list`;`ty:l4_vexpr961`] THEN
  STRUCT_CASES_TAC (SPEC `l:l4_vpar_red_ext972` (cases "l4_vpar_red_ext972")) THENL
  [(* base *)
   REWRITE_TAC [l4_vpe_apply972;l4_vlift961;l4_vliftN961;GSYM ONE] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat g
                   (L4VApp961 (L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1))
                              (L4VBVar961 0)) e0'` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
       `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`g:l4_vexpr961 list`;
       `l4_vliftN961 dom 1 0`;`l4_vliftN961 e0' 1 1`;`l4_vliftN961 e0' 1 1`;
       `L4VBVar961 0`;`L4VBVar961 0`] l4_vprt_beta972) THEN
    REWRITE_TAC [l4_vpar_red_t_refl972;l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966];
    EXISTS_TAC `e0':l4_vexpr961` THEN REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_single972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vpar_red_t_has_type972]]];
   (* lift *)
   STRUCT_CASES_TAC (ISPEC `g:l4_vexpr961 list` list_CASES) THENL
   [REWRITE_TAC [l4_vpe_depth972;LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC [l4_vpe_apply972;l4_vpe_meas972;l4_vpe_depth972;LENGTH] THEN STRIP_TAC THEN
   SUBGOAL_THEN `?ty'. l4_vhas_type961 env uvars t
                         (l4_vpe_apply972 a (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) ty'`
     (X_CHOOSE_TAC `ty':l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vhas_type961;GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`0`;
                   `t:l4_vexpr961 list`;`CONS (h:l4_vexpr961) t`;
                   `l4_vpe_apply972 a (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`;
                   `l4_vpe_apply972 a (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`]
      l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
    EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?e_sub. l4_vpar_red_ts972 env uvars pat t
                           (l4_vpe_apply972 a (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) e_sub /\
                         l4_vnormal_eq972 env uvars t e_sub (l4_vpe_apply972 a e0')`
     (X_CHOOSE_THEN `e_sub:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vpe_meas972 a`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
    EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [LE_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [l4_vctx_wf966]; ASM_ARITH_TAC];
    EXISTS_TAC `l4_vlift961 e_sub` THEN REWRITE_TAC [l4_vlift961] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_ts_weakN972 THEN EXISTS_TAC `t:l4_vexpr961 list` THEN
     ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961];
     MATCH_MP_TAC l4_vnormal_eq_weakN972 THEN EXISTS_TAC `t:l4_vexpr961 list` THEN
     ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961]]];
   (* app *)
   STRUCT_CASES_TAC (ISPEC `g:l4_vexpr961 list` list_CASES) THENL
   [REWRITE_TAC [l4_vpe_depth972;LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC [l4_vpe_apply972;l4_vpe_meas972;l4_vpe_depth972;LENGTH] THEN STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (h:l4_vexpr961) t`;
                  `l4_vlift961 (l4_vpe_apply972 a (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))`;
                  `L4VBVar961 0`;`ty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a_app:l4_vexpr961`
     (X_CHOOSE_THEN `b_app:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `?e_sub. l4_vpar_red_ts972 env uvars pat (CONS h t)
                           (l4_vpe_apply972 (L4VPELift972 a)
                              (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) e_sub /\
                         l4_vnormal_eq972 env uvars (CONS h t) e_sub
                           (l4_vpe_apply972 (L4VPELift972 a) e0')`
     (X_CHOOSE_THEN `e_sub:l4_vexpr961` MP_TAC) THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vpe_meas972 (L4VPELift972 a)`) THEN
    ANTS_TAC THENL [REWRITE_TAC [l4_vpe_meas972] THEN ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
    EXISTS_TAC `L4VForallE961 a_app b_app` THEN
    ASM_REWRITE_TAC [l4_vpe_apply972;l4_vpe_depth972;LENGTH;LE_REFL];
    REWRITE_TAC [l4_vpe_apply972] THEN STRIP_TAC THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS h t) e_sub (L4VForallE961 a_app b_app)`
      ASSUME_TAC THENL [ASM_MESON_TAC [l4_vpar_red_ts_has_type972]; ALL_TAC] THEN
    EXISTS_TAC `L4VApp961 e_sub (L4VBVar961 0)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
     MATCH_MP_TAC l4_vn_appDF972 THEN
     MAP_EVERY EXISTS_TAC [`a_app:l4_vexpr961`;`b_app:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `e_sub:l4_vexpr961` THEN
      ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
      MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `a_app:l4_vexpr961` THEN ASM_REWRITE_TAC []]]]]);;

let l4_vpe_proof_irrel_aux972 = prove
 (`!l env uvars g p dom e0'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vpe_depth972 l <= LENGTH g /\
   l4_vhas_type961 env uvars g p (L4VSort961 L4VLZero961) /\
   l4_vhas_type961 env uvars g
     (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) p ==>
   l4_vhas_type961 env uvars g (l4_vpe_apply972 l e0') p`,
  MATCH_MP_TAC l4_vpar_red_ext_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* base *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vhas_type961 env uvars g (l4_vpe_apply972 L4VPEBase972 (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) p` THEN
   REWRITE_TAC [l4_vpe_apply972;l4_vlift961;l4_vliftN961;GSYM ONE] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1)`;
                  `L4VBVar961 0`;`p:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a_app:l4_vexpr961`
     (X_CHOOSE_THEN `b_app:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `l4_vliftN961 dom 1 0`;`l4_vliftN961 e0' 1 1`;
                  `L4VForallE961 a_app b_app`] l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `u_b:l4_vlevel961`) (X_CHOOSE_TAC `b_b:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g
                   (L4VForallE961 (l4_vliftN961 dom 1 0) b_b) (L4VForallE961 a_app b_app)`
     MP_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1)`;
                          `L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1)`;
                          `L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_b:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (fun th ->
     MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
       (CONJ (ASSUME `l4_defeq_injectivity972 env`)
         (CONJ (ASSUME `l4_vctx_wf966 env uvars g`) th))))) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w1:l4_vlevel961`) (K ALL_TAC)) THEN
   MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
   EXISTS_TAC `L4VApp961 (L4VLam961 (l4_vliftN961 dom 1 0) (l4_vliftN961 e0' 1 1)) (L4VBVar961 0)` THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `l4_vinst0961 b_b (L4VBVar961 0)` THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `l4_vliftN961 dom 1 0`;`l4_vliftN961 e0' 1 1`;
                  `L4VBVar961 0`;`b_b:l4_vexpr961`] l4_vis_defeq_beta961) THEN
   REWRITE_TAC [l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966;GSYM l4_vhas_type961] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`a_app:l4_vexpr961`;`w1:l4_vlevel961`] THEN
   ASM_SIMP_TAC [l4_vis_defeq_symm961;GSYM l4_vhas_type961];
   (* lift *)
   X_GEN_TAC `l:l4_vpar_red_ext972` THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `p:l4_vexpr961`;`dom:l4_vexpr961`;`e0':l4_vexpr961`] THEN
   STRUCT_CASES_TAC (ISPEC `g:l4_vexpr961 list` list_CASES) THENL
   [REWRITE_TAC [l4_vpe_depth972;LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC [l4_vpe_apply972;l4_vpe_depth972;LENGTH] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars t` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?p0. l4_vhas_type961 env uvars t
                        (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))) p0`
     (X_CHOOSE_TAC `p0:l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vhas_type961;GSYM l4_vis_defeq_u961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`0`;
                   `t:l4_vexpr961 list`;`CONS (h:l4_vexpr961) t`;
                   `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`;
                   `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`]
      l4_vis_defeq_u_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_vis_defeq_u961;GSYM l4_vhas_type961] THEN
    EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars (CONS h t) p (l4_vlift961 p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC
      [`l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))`;
       `l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))`;
       `l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weak966 THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars t p0 (L4VSort961 L4VLZero961)` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`1`;`0`;
                   `t:l4_vexpr961 list`;`CONS (h:l4_vexpr961) t`;
                   `p0:l4_vexpr961`;`L4VSort961 L4VLZero961`] l4_vhas_type_weakN_iff972) THEN
    ASM_REWRITE_TAC [l4_vctx_liftN_one966;l4_vliftN961;GSYM l4_vlift961] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars t (l4_vpe_apply972 l e0') p0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dom:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `l4_vlift961 p0` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972] THEN
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weak966 THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961]];
   (* app *)
   X_GEN_TAC `l:l4_vpar_red_ext972` THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `p:l4_vexpr961`;`dom:l4_vexpr961`;`e0':l4_vexpr961`] THEN
   STRUCT_CASES_TAC (ISPEC `g:l4_vexpr961 list` list_CASES) THENL
   [REWRITE_TAC [l4_vpe_depth972;LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC [l4_vpe_apply972;l4_vpe_depth972;LENGTH] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars t` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`t:l4_vexpr961 list`;`h:l4_vexpr961`;
                  `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`;
                  `p:l4_vexpr961`] l4_has_type_app_bvar0972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `b_p:l4_vexpr961`) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS h t)
                   (L4VApp961 (l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))))
                              (L4VBVar961 0)) b_p` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (h:l4_vexpr961) t`;
                   `l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))`;
                   `L4VBVar961 0`;`l4_vlift961 h`;`l4_vliftN961 b_p 1 1`] l4_vhas_type_app972) THEN
    REWRITE_TAC [l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961]]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars (CONS h t) p b_p` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC
      [`L4VApp961 (l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))) (L4VBVar961 0)`;
       `L4VApp961 (l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))) (L4VBVar961 0)`;
       `L4VApp961 (l4_vlift961 (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0)))) (L4VBVar961 0)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`t:l4_vexpr961 list`;
                  `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`;
                  `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e0')) (L4VBVar961 0))`;
                  `L4VForallE961 h b_p`] l4_vis_defeq_is_type966) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`t:l4_vexpr961 list`;
                  `h:l4_vexpr961`;`b_p:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_c:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u_c` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_sort_r966;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars t (L4VForallE961 h b_p) (L4VSort961 L4VLZero961)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VSort961 (L4VLIMax961 u_c L4VLZero961)`;
                          `L4VLSucc961 (L4VLIMax961 u_c L4VLZero961)`] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort961 THEN
     ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_imax_zero972];
     REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_forall972 THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
     EXISTS_TAC `p:l4_vexpr961` THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars t (l4_vpe_apply972 l e0') (L4VForallE961 h b_p)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dom:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `b_p:l4_vexpr961` THEN
    ASM_SIMP_TAC [l4_vis_defeq_u_symm972] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (h:l4_vexpr961) t`;
                   `l4_vlift961 (l4_vpe_apply972 l e0')`;`L4VBVar961 0`;
                   `l4_vlift961 h`;`l4_vliftN961 b_p 1 1`] l4_vhas_type_app972) THEN
    REWRITE_TAC [l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
     MATCH_MP_TAC l4_vis_defeq_weak966 THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;GSYM l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     REWRITE_TAC [l4_vlookup_zero961]]]]);;

let l4_vpar_red_ext_par_red_beta_both972 = prove
 (`!env uvars pat.
   l4_pattern_params_for972 env pat ==>
   !sz f g dom e'.
     l4_vexpr_size972 f <= sz /\
     l4_vctx_wf966 env uvars g ==>
     (l4_vnormal_eq972 env uvars g f (L4VLam961 dom e') ==>
      !a cod.
        l4_vhas_type961 env uvars g (L4VApp961 f a) cod ==>
        ?e. l4_vpar_red_ts972 env uvars pat g (L4VApp961 f a) e /\
            l4_vnormal_eq972 env uvars g e (l4_vinst0961 e' a)) /\
     (!l. l4_vpe_depth972 l <= LENGTH g /\
          l4_vnormal_eq972 env uvars g f
            (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom e')) (L4VBVar961 0))) ==>
          ?e. l4_vpar_red_ts972 env uvars pat g f e /\
              l4_vnormal_eq972 env uvars g e (l4_vpe_apply972 l e'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_venv_closed966 env`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_venv_wf_closed966]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `sz:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`f0:l4_vexpr961`;`g0:l4_vexpr961 list`;
                       `dom0:l4_vexpr961`;`e0':l4_vexpr961`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [(* Part 1: f0 =N= VLam dom0 e0' *)
   DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a0:l4_vexpr961`;`b0:l4_vexpr961`] THEN DISCH_TAC THEN
   UNDISCH_TAC `l4_vnormal_eq972 env uvars g0 f0 (L4VLam961 dom0 e0')` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_rev_tac972 THENL
   [(* refl *)
    SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat g0
                    (L4VApp961 (L4VLam961 dom0 e0') a0) (l4_vinst0961 e0' a0)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vprt_beta972 THEN REWRITE_TAC [l4_vpar_red_t_refl972];
     EXISTS_TAC `l4_vinst0961 e0' a0` THEN REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vrtc_single972 THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `b0:l4_vexpr961` THEN
      ASM_MESON_TAC [l4_vpar_red_t_has_type972]]];
    (* lamDF *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `L4VLam961 dom1 b1`;`a0:l4_vexpr961`;`b0:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `a_f:l4_vexpr961`
      (X_CHOOSE_THEN `b_f:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom1:l4_vexpr961`;`b1:l4_vexpr961`;`L4VForallE961 a_f b_f`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `u_f:l4_vlevel961`) (X_CHOOSE_TAC `b_b:l4_vexpr961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0 (L4VForallE961 dom1 b_b) (L4VForallE961 a_f b_f)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VLam961 dom1 b1`;`L4VLam961 dom1 b1`;`L4VLam961 dom1 b1`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_f:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th ->
      MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
        (CONJ (ASSUME `l4_defeq_injectivity972 env`)
          (CONJ (ASSUME `l4_vctx_wf966 env uvars g0`) th))))) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:l4_vlevel961`) (K ALL_TAC)) THEN
    EXISTS_TAC `l4_vinst0961 b1 a0` THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_single972 THEN
     MATCH_MP_TAC l4_vprt_beta972 THEN REWRITE_TAC [l4_vpar_red_t_refl972];
     REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vnormal_eq_instN972 THEN
     MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g0`] THEN
     ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
     MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `a_f:l4_vexpr961` THEN
     ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 u` THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN
     MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
     MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`L4VSort961 w`] THEN ASM_REWRITE_TAC []];
    (* etaL *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `L4VLam961 dom0 e0'`;`L4VLam961 dom0 e0'`;`L4VForallE961 dom cod`]
      l4_vis_defeq_is_type966) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_a:l4_vlevel961`) (K ALL_TAC)) THEN
    SUBGOAL_THEN `?d. l4_vpar_red_ts972 env uvars pat (CONS dom g0) e d /\
                      l4_vnormal_eq972 env uvars (CONS dom g0) d e0'`
      (X_CHOOSE_THEN `d:l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 e`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 dom e) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN (MP_TAC o SPECL [`e:l4_vexpr961`;`CONS (dom:l4_vexpr961) g0`;
                                 `dom0:l4_vexpr961`;`e0':l4_vexpr961`]) THEN
     ANTS_TAC THENL
     [REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC l4_vctx_cons972 THEN
      EXISTS_TAC `u_a:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
     DISCH_THEN (MP_TAC o SPEC `L4VPEBase972` o CONJUNCT2) THEN
     ASM_REWRITE_TAC [l4_vpe_depth972;l4_vpe_apply972;LE_0]; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `L4VLam961 dom e`;`a0:l4_vexpr961`;`b0:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `a_f:l4_vexpr961`
      (X_CHOOSE_THEN `b_f:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`e:l4_vexpr961`;`L4VForallE961 a_f b_f`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `u_c:l4_vlevel961`) (X_CHOOSE_TAC `b_c:l4_vexpr961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0 (L4VForallE961 dom b_c) (L4VForallE961 a_f b_f)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VLam961 dom e`;`L4VLam961 dom e`;`L4VLam961 dom e`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th ->
      MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
        (CONJ (ASSUME `l4_defeq_injectivity972 env`)
          (CONJ (ASSUME `l4_vctx_wf966 env uvars g0`) th))))) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:l4_vlevel961`) (K ALL_TAC)) THEN
    EXISTS_TAC `l4_vinst0961 d a0` THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
     EXISTS_TAC `L4VApp961 (L4VLam961 dom d) a0` THEN CONJ_TAC THENL
     [REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vpar_red_ts_app972 THEN
      REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
      REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN
      ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
      MATCH_MP_TAC l4_vprt_beta972 THEN REWRITE_TAC [l4_vpar_red_t_refl972]];
     REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vnormal_eq_instN972 THEN
     MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`dom:l4_vexpr961`;`CONS (dom:l4_vexpr961) g0`] THEN
     ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`a_f:l4_vexpr961`;`w:l4_vlevel961`] THEN
     ASM_SIMP_TAC [l4_vis_defeq_symm961;GSYM l4_vhas_type961]];
    (* etaR *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `f0:l4_vexpr961`;`a0:l4_vexpr961`;`b0:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `a_f:l4_vexpr961`
      (X_CHOOSE_THEN `b_f:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0 (L4VForallE961 a_f b_f) (L4VForallE961 dom0 cod)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`f0:l4_vexpr961`;`f0:l4_vexpr961`;`f0:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
    DISCH_THEN (fun th ->
      MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
        (CONJ (ASSUME `l4_defeq_injectivity972 env`)
          (CONJ (ASSUME `l4_vctx_wf966 env uvars g0`) th))))) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:l4_vlevel961`) (K ALL_TAC)) THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `a0:l4_vexpr961`;`dom0:l4_vexpr961`;`0`;
                   `CONS (dom0:l4_vexpr961) g0`;`g0:l4_vexpr961 list`;
                   `L4VApp961 (l4_vlift961 f0) (L4VBVar961 0)`;`e0':l4_vexpr961`]
      l4_vnormal_eq_instN972) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`a_f:l4_vexpr961`;`w:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
    REWRITE_TAC [l4_vinst961;l4_vinst_var961;LT_REFL;l4_vliftN_zero961;
                 GSYM l4_vinst0961;l4_vinst0_vlift966] THEN
    DISCH_TAC THEN EXISTS_TAC `L4VApp961 f0 a0` THEN
    ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
    (* proofIrrel *)
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `f0:l4_vexpr961`;`a0:l4_vexpr961`;`b0:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `a_f:l4_vexpr961`
      (X_CHOOSE_THEN `b_f:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0 p (L4VForallE961 a_f b_f)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`f0:l4_vexpr961`;`f0:l4_vexpr961`;`f0:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g0 (L4VForallE961 a_f b_f) (L4VSort961 L4VLZero961)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
     ASM_REWRITE_TAC []; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `a_f:l4_vexpr961`;`b_f:l4_vexpr961`;`L4VSort961 L4VLZero961`]
      l4_vhas_type_forall_inv972) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_b:l4_vlevel961`) (X_CHOOSE_TAC `v_b:l4_vlevel961`)) THEN
    SUBGOAL_THEN `l4_vlevel_equiv961 (L4VLIMax961 u_b v_b) L4VLZero961` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_sort_inv972 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VForallE961 a_f b_f`;`L4VForallE961 a_f b_f`;`L4VForallE961 a_f b_f`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vlevel_wf961 uvars v_b` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_sort_r966 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (a_f:l4_vexpr961) g0`;
                           `b_f:l4_vexpr961`;`b_f:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u_b:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS a_f g0) b_f (L4VSort961 L4VLZero961)`
      ASSUME_TAC THENL
    [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`L4VSort961 v_b`;`L4VLSucc961 v_b`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_sort961 THEN
     ASM_MESON_TAC [l4_vlevel_wf961;l4_vlevel_imax_eq_zero972]; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom0:l4_vexpr961`;`e0':l4_vexpr961`;`p:l4_vexpr961`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_c:l4_vlevel961`) (X_CHOOSE_TAC `b_c:l4_vexpr961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0 (L4VForallE961 dom0 b_c) (L4VForallE961 a_f b_f)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VLam961 dom0 e0'`;`L4VLam961 dom0 e0'`;`L4VLam961 dom0 e0'`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th ->
      MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
        (CONJ (ASSUME `l4_defeq_injectivity972 env`)
          (CONJ (ASSUME `l4_vctx_wf966 env uvars g0`) th))))) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `w1:l4_vlevel961`) (X_CHOOSE_TAC `w2:l4_vlevel961`)) THEN
    EXISTS_TAC `L4VApp961 f0 a0` THEN REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `l4_vinst0961 b_f a0` THEN
    REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `a0:l4_vexpr961`;`a_f:l4_vexpr961`;`CONS (a_f:l4_vexpr961) g0`;
                    `b_f:l4_vexpr961`;`b_f:l4_vexpr961`;`L4VSort961 L4VLZero961`;
                    `0`;`g0:l4_vexpr961 list`] l4_vis_defeq_instN966) THEN
     ASM_REWRITE_TAC [l4_vctx_instN_zero966;l4_vinst961;GSYM l4_vinst0961;GSYM l4_vhas_type961];
     MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `a_f:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     REWRITE_TAC [l4_vhas_type961;l4_vinst0961] THEN MATCH_MP_TAC l4_vis_defeq_instN966 THEN
     MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`dom0:l4_vexpr961`;`CONS (dom0:l4_vexpr961) g0`] THEN
     ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN CONJ_TAC THENL
     [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
      MAP_EVERY EXISTS_TAC [`a_f:l4_vexpr961`;`w1:l4_vlevel961`] THEN
      ASM_SIMP_TAC [l4_vis_defeq_symm961;GSYM l4_vhas_type961];
      MATCH_MP_TAC l4_vis_defeq_conv961 THEN
      MAP_EVERY EXISTS_TAC [`b_c:l4_vexpr961`;`w2:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961]]]];
   (* Part 2: f0 =N= vpe_apply l ((VLam dom0 e0').lift.app (bvar 0)) *)
   X_GEN_TAC `l:l4_vpar_red_ext972` THEN STRIP_TAC THEN
   UNDISCH_TAC `l4_vnormal_eq972 env uvars g0 f0
                  (l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom0 e0')) (L4VBVar961 0)))` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* refl *)
    l4_subst_rev_tac972 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `dom0:l4_vexpr961`;`e0':l4_vexpr961`] l4_vpe_refl_beta_ind972) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`l4_vpe_meas972 l`;`l:l4_vpar_red_ext972`;
                                `g0:l4_vexpr961 list`;`ty:l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [LE_REFL];
    (* sortDF *)
    MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom0 e0')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN ASM_REWRITE_TAC [l4_vis_app972];
    (* constDF *)
    MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom0 e0')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN ASM_REWRITE_TAC [l4_vis_app972];
    (* appDF *)
    SUBGOAL_THEN
      `?n. x2 = L4VBVar961 n /\
           ((f2 = l4_vliftN961 (L4VLam961 dom0 e0') (n + 1) 0 /\
             l4_vpe_apply972 l e0' = l4_vliftN961 e0' n 0) \/
            (?l'. l4_vpe_depth972 l' <= l4_vpe_depth972 l /\
                  f2 = l4_vpe_apply972 l' (L4VApp961 (l4_vlift961 (L4VLam961 dom0 e0')) (L4VBVar961 0)) /\
                  l4_vpe_apply972 l e0' = L4VApp961 (l4_vpe_apply972 l' e0') (L4VBVar961 n)))`
      (X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (DISJ_CASES_THEN STRIP_ASSUME_TAC))) THENL
    [MATCH_MP_TAC l4_vpe_app_decomp972 THEN ASM_REWRITE_TAC [];
     (* base lift case *)
     l4_subst_vars_tac972 THEN
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961;GSYM ONE]) THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `l4_vliftN961 dom0 (n + 1) 0`;`l4_vliftN961 e0' (n + 1) 1`;
                    `L4VForallE961 dom cod`] l4_vhas_type_lam_inv970) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_c:l4_vlevel961`) (X_CHOOSE_TAC `b_c:l4_vexpr961`)) THEN
     SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g0
                     (L4VForallE961 dom cod)
                     (L4VForallE961 (l4_vliftN961 dom0 (n + 1) 0) b_c)` MP_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
      MAP_EVERY EXISTS_TAC
        [`L4VLam961 (l4_vliftN961 dom0 (n + 1) 0) (l4_vliftN961 e0' (n + 1) 1)`;
         `L4VLam961 (l4_vliftN961 dom0 (n + 1) 0) (l4_vliftN961 e0' (n + 1) 1)`;
         `L4VLam961 (l4_vliftN961 dom0 (n + 1) 0) (l4_vliftN961 e0' (n + 1) 1)`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN (fun th ->
       MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
         (CONJ (ASSUME `l4_defeq_injectivity972 env`)
           (CONJ (ASSUME `l4_vctx_wf966 env uvars g0`) th))))) THEN
     DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w1:l4_vlevel961`) (K ALL_TAC)) THEN
     SUBGOAL_THEN `?e_res. l4_vpar_red_ts972 env uvars pat g0 (L4VApp961 f1 x1) e_res /\
                           l4_vnormal_eq972 env uvars g0 e_res
                             (l4_vinst0961 (l4_vliftN961 e0' (n + 1) 1) x1)`
       (X_CHOOSE_THEN `e_res:l4_vexpr961` STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 f1`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f1 x1) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [`f1:l4_vexpr961`;`g0:l4_vexpr961 list`;
                                  `l4_vliftN961 dom0 (n + 1) 0`;`l4_vliftN961 e0' (n + 1) 1`]) THEN
      ASM_REWRITE_TAC [LE_REFL] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPECL [`x1:l4_vexpr961`;`l4_vinst0961 cod x1`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC l4_vhas_type_app972 THEN
      EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [];
      EXISTS_TAC `e_res:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vnormal_eq_trans972 THEN
      EXISTS_TAC `l4_vinst0961 (l4_vliftN961 e0' (n + 1) 1) x1` THEN
      ASM_REWRITE_TAC [GSYM l4_vinst0_vliftN_succ_bvar972;l4_vinst0961] THEN
      MATCH_MP_TAC l4_vnormal_eq_instN_r972 THEN
      MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`l4_vliftN961 dom0 (n + 1) 0`;
                            `CONS (l4_vliftN961 dom0 (n + 1) 0) g0`;`b_c:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vhas_type_defeq_u_r972 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
       ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w1` THEN ASM_REWRITE_TAC []]];
     (* recursive l' case *)
     l4_subst_vars_tac972 THEN
     SUBGOAL_THEN `?e_res. l4_vpar_red_ts972 env uvars pat g0 f1 e_res /\
                           l4_vnormal_eq972 env uvars g0 e_res (l4_vpe_apply972 l' e0')`
       (X_CHOOSE_THEN `e_res:l4_vexpr961` STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 f1`) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `l4_vexpr_size972 (L4VApp961 f1 x1) <= sz` THEN
       REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [`f1:l4_vexpr961`;`g0:l4_vexpr961 list`;
                                  `dom0:l4_vexpr961`;`e0':l4_vexpr961`]) THEN
      ASM_REWRITE_TAC [LE_REFL] THEN DISCH_THEN (MP_TAC o SPEC `l':l4_vpar_red_ext972` o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `l4_vhas_type961 env uvars g0 e_res (L4VForallE961 dom cod)` ASSUME_TAC THENL
      [ASM_MESON_TAC [l4_vpar_red_ts_has_type972]; ALL_TAC] THEN
      EXISTS_TAC `L4VApp961 e_res x1` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
       MATCH_MP_TAC l4_vn_appDF972 THEN
       MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
       ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
       EXISTS_TAC `e_res:l4_vexpr961` THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]]]];
    (* lamDF *)
    MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom0 e0')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN ASM_REWRITE_TAC [l4_vis_app972];
    (* forallEDF *)
    MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom0 e0')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN ASM_REWRITE_TAC [l4_vis_app972];
    (* etaL *)
    l4_subst_vars_tac972 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom0 e0')) (L4VBVar961 0))`;
                   `l4_vpe_apply972 l (L4VApp961 (l4_vlift961 (L4VLam961 dom0 e0')) (L4VBVar961 0))`;
                   `L4VForallE961 dom cod`] l4_vis_defeq_is_type966) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_a:l4_vlevel961`) (K ALL_TAC)) THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g0)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u_a:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `?b_res. l4_vpar_red_ts972 env uvars pat (CONS dom g0) e b_res /\
                          l4_vnormal_eq972 env uvars (CONS dom g0) b_res
                            (l4_vpe_apply972 (L4VPEApp972 l) e0')`
      (X_CHOOSE_THEN `b_res:l4_vexpr961` MP_TAC) THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `l4_vexpr_size972 e`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `l4_vexpr_size972 (L4VLam961 dom e) <= sz` THEN
      REWRITE_TAC [l4_vexpr_size972] THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN (MP_TAC o SPECL [`e:l4_vexpr961`;`CONS (dom:l4_vexpr961) g0`;
                                 `dom0:l4_vexpr961`;`e0':l4_vexpr961`]) THEN
     ASM_REWRITE_TAC [LE_REFL] THEN
     DISCH_THEN (MP_TAC o SPEC `L4VPEApp972 l` o CONJUNCT2) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_vpe_apply972;l4_vpe_depth972;LENGTH] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC [l4_vpe_apply972] THEN STRIP_TAC THEN
     SUBGOAL_THEN `l4_vis_defeq_u961 env uvars (CONS dom g0) b_res
                     (L4VApp961 (l4_vlift961 (l4_vpe_apply972 l e0')) (L4VBVar961 0))` MP_TAC THENL
     [ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; REWRITE_TAC [l4_vis_defeq_u961]] THEN
     DISCH_THEN (X_CHOOSE_THEN `ty_c:l4_vexpr961` (ASSUME_TAC o MATCH_MP l4_vis_defeq_refl_r961)) THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;`dom:l4_vexpr961`;
                    `l4_vpe_apply972 l e0'`;`ty_c:l4_vexpr961`] l4_has_type_app_bvar0972) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `b_new:l4_vexpr961`) THEN
     EXISTS_TAC `L4VLam961 dom b_res` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
      MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `b_new:l4_vexpr961` THEN ASM_REWRITE_TAC []]];
    (* etaR *)
    MP_TAC (SPECL [`l:l4_vpar_red_ext972`;`l4_vlift961 (L4VLam961 dom0 e0')`;`L4VBVar961 0`]
      l4_vpe_is_app972) THEN ASM_REWRITE_TAC [l4_vis_app972];
    (* proofIrrel *)
    EXISTS_TAC `f0:l4_vexpr961` THEN REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
    MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpe_proof_irrel_aux972 THEN
    EXISTS_TAC `dom0:l4_vexpr961` THEN ASM_REWRITE_TAC []]]);;

let l4_vpar_red_ext_par_red_beta972 = prove
 (`!env uvars pat g f dom e' a cod.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g f (L4VLam961 dom e') /\
   l4_vhas_type961 env uvars g (L4VApp961 f a) cod ==>
   ?e. l4_vpar_red_ts972 env uvars pat g (L4VApp961 f a) e /\
       l4_vnormal_eq972 env uvars g e (l4_vinst0961 e' a)`,
  MESON_TAC [l4_vpar_red_ext_par_red_beta_both972;LE_REFL]);;

(* NormalEq.parRed — BOTH upstream .extra cases proved axiom-free! *)
let l4_subst_vars_tac972 = l4_subst_rev_tac972;;

let l4_vnormal_eq_par_red_etaR_split_ind972 = prove
 (`!R start t.
   l4_vrt_closure972 R start t ==>
   (!env uvars pat g dom cod e1.
      R = l4_vpar_red_t972 env uvars pat (CONS dom g) /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vctx_wf966 env uvars (CONS dom g) /\
      l4_vhas_type961 env uvars g e1 (L4VForallE961 dom cod) /\
      start = L4VApp961 (l4_vlift961 e1) (L4VBVar961 0) ==>
      (?dom0. l4_vpar_red_ts972 env uvars pat g e1 (L4VLam961 dom0 t) /\
              l4_vis_defeq_u961 env uvars g dom0 dom) \/
      (?e'. l4_vpar_red_ts972 env uvars pat g e1 e' /\
            t = L4VApp961 (l4_vlift961 e') (L4VBVar961 0)))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e1:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
   MAP_EVERY X_GEN_TAC [`R:l4_vexpr961->l4_vexpr961->bool`;
                        `start:l4_vexpr961`;`y:l4_vexpr961`;`z:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;`e1:l4_vexpr961`] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_venv_closed966 env`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `?u_d. l4_vhas_type961 env uvars g dom (L4VSort961 u_d)`
     (X_CHOOSE_TAC `u_d:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vctx_wf966 env uvars (CONS dom g)` THEN
    REWRITE_TAC [l4_vctx_wf966;l4_vis_type961] THEN MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `(?dom0. l4_vpar_red_ts972 env uvars pat g e1 (L4VLam961 dom0 y) /\
              l4_vis_defeq_u961 env uvars g dom0 dom) \/
      (?e'. l4_vpar_red_ts972 env uvars pat g e1 e' /\
            y = L4VApp961 (l4_vlift961 e') (L4VBVar961 0))`
     (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `cod:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    (* Left: already reduced to VLam dom0 y *)
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom0 dom (L4VSort961 u_d)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_of_r972 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g (L4VLam961 dom0 y) (L4VForallE961 dom cod)`
      ASSUME_TAC THENL [ASM_MESON_TAC [l4_vpar_red_ts_has_type972]; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom0:l4_vexpr961`;`y:l4_vexpr961`;`L4VForallE961 dom cod`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `b_d:l4_vexpr961`)) THEN
    DISJ1_TAC THEN EXISTS_TAC `dom0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
    EXISTS_TAC `L4VLam961 dom0 y` THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972];
     MATCH_MP_TAC l4_vprt_lam972 THEN REWRITE_TAC [l4_vpar_red_t_refl972] THEN
     MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`b_d:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u_d:l4_vlevel961` THEN
      ASM_SIMP_TAC [l4_vis_defeq_ctx_zero966;l4_vis_defeq_symm961];
      REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom0:l4_vexpr961) g`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u_d:l4_vlevel961` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966]]];
    (* Right: y = VApp (vlift e') (bvar 0) *)
    l4_subst_vars_tac972 THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g e' (L4VForallE961 dom cod)` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_vpar_red_ts_has_type972]; ALL_TAC] THEN
    UNDISCH_TAC `l4_vpar_red_t972 env uvars pat (CONS dom g) (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) z` THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
    REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
    [(* app step *)
     UNDISCH_TAC `l4_vpar_red_t972 env uvars pat (CONS dom g) (L4VBVar961 0) a'` THEN
     GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
     REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
     DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
     [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
        `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
        `1`;`0`;`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;
        `e':l4_vexpr961`;`f':l4_vexpr961`;`l4_vlift961 (L4VForallE961 dom cod)`]
        l4_vpar_red_t_weakN_inv972) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC [l4_vctx_liftN_one966;GSYM l4_vlift961] THEN
       REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weak966 THEN
       ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `e'':l4_vexpr961` STRIP_ASSUME_TAC) THEN
      DISJ2_TAC THEN EXISTS_TAC `e'':l4_vexpr961` THEN
      ASM_REWRITE_TAC [l4_vlift961;l4_vpar_red_ts972] THEN
      MATCH_MP_TAC l4_vrtc_tail972 THEN EXISTS_TAC `e':l4_vexpr961` THEN
      ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972];
      ASM_MESON_TAC [l4_vpattern_matches_not_bvar972]];
     (* beta step *)
     UNDISCH_TAC `l4_vpar_red_t972 env uvars pat (CONS dom g) (L4VBVar961 0) e2'` THEN
     GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
     REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
     DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
     [UNDISCH_TAC `l4_vpar_red_ts972 env uvars pat g e1 e'` THEN
      UNDISCH_TAC `l4_vhas_type961 env uvars g e' (L4VForallE961 dom cod)` THEN
      UNDISCH_TAC `l4_vlift961 e' = L4VLam961 dom' e1'` THEN
      STRUCT_CASES_TAC (SPEC `e':l4_vexpr961` l4_vexpr_CASES961) THEN
      REWRITE_TAC [l4_vlift961;l4_vliftN961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
      REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                     `a0:l4_vexpr961`;`a1:l4_vexpr961`;`L4VForallE961 dom cod`]
        l4_vhas_type_lam_inv970) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_c:l4_vlevel961`) (X_CHOOSE_TAC `b_c:l4_vexpr961`)) THEN
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
        `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
        `1`;`SUC 0`;`CONS (a0:l4_vexpr961) g`;
        `CONS (l4_vliftN961 a0 1 0) (CONS (dom:l4_vexpr961) g)`;
        `a1:l4_vexpr961`;`e1'':l4_vexpr961`;`l4_vliftN961 b_c 1 (SUC 0)`]
        l4_vpar_red_t_weakN_inv972) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC [] THEN
       REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN
        ASM_REWRITE_TAC [GSYM l4_vlift961] THEN
        MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                       `dom:l4_vexpr961`;`a0:l4_vexpr961`;`a0:l4_vexpr961`;`L4VSort961 u_c`]
          l4_vis_defeq_weak966) THEN
        ASM_REWRITE_TAC [l4_vlift961;l4_vliftN961;GSYM l4_vhas_type961];
        MATCH_MP_TAC l4_vctx_liftN_succ966 THEN REWRITE_TAC [l4_vctx_liftN_one966];
        REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
        EXISTS_TAC `CONS (a0:l4_vexpr961) g` THEN
        ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
        MATCH_MP_TAC l4_vctx_liftN_succ966 THEN REWRITE_TAC [l4_vctx_liftN_one966]];
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `bd0':l4_vexpr961` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 a0 b_c) (L4VForallE961 dom cod)`
        MP_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
       MAP_EVERY EXISTS_TAC [`L4VLam961 a0 a1`;`L4VLam961 a0 a1`;`L4VLam961 a0 a1`] THEN
       ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
       MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_c:l4_vlevel961` THEN ASM_REWRITE_TAC [];
       ALL_TAC] THEN
      DISCH_THEN (fun th ->
        MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
          (CONJ (ASSUME `l4_defeq_injectivity972 env`)
            (CONJ (ASSUME `l4_vctx_wf966 env uvars g`) th))))) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w1:l4_vlevel961`) (K ALL_TAC)) THEN
      DISJ1_TAC THEN EXISTS_TAC `a0:l4_vexpr961` THEN
      ASM_REWRITE_TAC [l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966] THEN CONJ_TAC THENL
      [REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
       EXISTS_TAC `L4VLam961 a0 a1` THEN ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN
       MATCH_MP_TAC l4_vprt_lam972 THEN ASM_REWRITE_TAC [l4_vpar_red_t_refl972];
       REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w1` THEN ASM_REWRITE_TAC []];
      ASM_MESON_TAC [l4_vpattern_matches_not_bvar972]];
     (* extra step -> impossible *)
     UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
     UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) m1 m2` THEN
     STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
     REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                  l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                  injectivity "l4_vexpr961"] THENL
     [STRIP_TAC THEN l4_subst_vars_tac972 THEN
      RULE_ASSUM_TAC (REWRITE_RULE [l4_vpattern_matches_not_bvar972]) THEN FIRST_ASSUM CONTR_TAC;
      DISCH_TAC THEN DISCH_THEN (fun th ->
        MP_TAC (MATCH_MP l4_params_pat_not_var972 (ASSUME `l4_pattern_params_for972 env pat`)) THEN
        MP_TAC th THEN MESON_TAC [])]]]]);;

let l4_vnormal_eq_par_red_ind972 = prove
 (`!env uvars g e1 e2.
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   (!pat e2'.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vpar_red_t972 env uvars pat g e2 e2' ==>
      ?e1'. l4_vpar_red_ts972 env uvars pat g e1 e1' /\
            l4_vnormal_eq972 env uvars g e1' e2')`,
  MATCH_MP_TAC l4_vnormal_eq_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* refl *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `e2':l4_vexpr961` THEN
   REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vrtc_single972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vpar_red_t_has_type972]];
   (* sortDF *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VSort961 l2) e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [EXISTS_TAC `L4VSort961 l1` THEN REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
    MATCH_MP_TAC l4_vn_sortDF972 THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_vpattern_matches_not_sort972]];
   (* constDF — first upstream .extra sorry proved unconditionally! *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `c:l4_name`;`ci:l4_vconstant961`;
                        `ls:l4_vlevel961 list`;`ls':l4_vlevel961 list`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VConst961 c ls') e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [EXISTS_TAC `L4VConst961 c ls` THEN REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
    MATCH_MP_TAC l4_vn_constDF972 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
    UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
    UNDISCH_TAC `l4_vrhs_wf972 p r` THEN
    UNDISCH_TAC `l4_vcheck_wf972 p ck` THEN
    UNDISCH_TAC `l4_vpattern_matches972 p (L4VConst961 c ls') m1 m2` THEN
    STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
    REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                 l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                 injectivity "l4_vexpr961"] THEN
    REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
    SUBGOAL_THEN `l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) ls l4_vmenv_empty972 ck`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
     MAP_EVERY EXISTS_TAC [`L4VPConst972 c`;`l4_vis_defeq_u961 env uvars g`;
                           `ls':l4_vlevel961 list`;`l4_vmenv_empty972`] THEN
     ASM_REWRITE_TAC [] THEN
     MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
     REWRITE_TAC [l4_vis_defeq_u961] THEN
     DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty_ab:l4_vexpr961`))) THEN
     SUBGOAL_THEN `ALL2 l4_vlevel_equiv961 ls' ls` ASSUME_TAC THENL
     [ASM_MESON_TAC [l4_all2_vlevel_equiv_symm970]; ALL_TAC] THEN
     SUBGOAL_THEN `l4_veq_up_to_levels970 uvars (l4_vrhs_apply972 ls' l4_vmenv_empty972 ra)
                     (l4_vrhs_apply972 ls l4_vmenv_empty972 ra) /\
                   l4_veq_up_to_levels970 uvars (l4_vrhs_apply972 ls' l4_vmenv_empty972 rb)
                     (l4_vrhs_apply972 ls l4_vmenv_empty972 rb)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC l4_veq_up_to_levels_vrhs_const972 THEN
      EXISTS_TAC `c:l4_name` THEN ASM_REWRITE_TAC [];
      EXISTS_TAC `ty_ab:l4_vexpr961` THEN
      ASM_MESON_TAC [l4_vis_defeq_eq_up_to_levels970;l4_vis_defeq_symm961]]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat g (L4VConst961 c ls)
                    (l4_vrhs_apply972 ls l4_vmenv_empty972 r)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vprt_extra972 THEN
     MAP_EVERY EXISTS_TAC [`L4VPConst972 c`;`ck:l4_vpattern_check972`;`l4_vmenv_empty972`] THEN
     ASM_REWRITE_TAC [l4_vpm_const972;l4_vpath_valid_clauses972]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g (l4_vrhs_apply972 ls l4_vmenv_empty972 r)
                    (l4_vinstL961 ls (l4_vc_type961 ci))` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
     MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                           `L4VConst961 c ls`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_const972 THEN
     ASM_REWRITE_TAC []; ALL_TAC] THEN
    EXISTS_TAC `l4_vrhs_apply972 ls l4_vmenv_empty972 r` THEN
    REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_single972 THEN ASM_REWRITE_TAC [];
     SUBGOAL_THEN `l4_vrhs_apply972 ls' m2' r = l4_vrhs_apply972 ls' l4_vmenv_empty972 r` SUBST1_TAC THENL
     [MATCH_MP_TAC l4_vrhs_apply_ext972 THEN EXISTS_TAC `L4VPConst972 c` THEN
      ASM_REWRITE_TAC [l4_vpath_valid_clauses972]; ALL_TAC] THEN
     MATCH_MP_TAC l4_veq_up_to_levels_normal_eq972 THEN
     EXISTS_TAC `l4_vinstL961 ls (l4_vc_type961 ci)` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_veq_up_to_levels_vrhs_const972 THEN
     EXISTS_TAC `c:l4_name` THEN ASM_REWRITE_TAC []]];
   (* appDF — including second upstream .extra case via pp_norm_app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `f1:l4_vexpr961`;`f2:l4_vexpr961`;
                        `x1:l4_vexpr961`;`x2:l4_vexpr961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VApp961 f2 x2) e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [(* app *)
    SUBGOAL_THEN
      `(?f1'. l4_vpar_red_ts972 env uvars pat g f1 f1' /\ l4_vnormal_eq972 env uvars g f1' f') /\
       (?x1'. l4_vpar_red_ts972 env uvars pat g x1 x1' /\ l4_vnormal_eq972 env uvars g x1' a')`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN ASM_MESON_TAC [];
     EXISTS_TAC `L4VApp961 f1' x1'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vn_appDF972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
      ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_t_has_type972]]];
    (* beta *)
    SUBGOAL_THEN
      `(?f'. l4_vpar_red_ts972 env uvars pat g f1 f' /\
             l4_vnormal_eq972 env uvars g f' (L4VLam961 dom' e1')) /\
       (?a'. l4_vpar_red_ts972 env uvars pat g x1 a' /\
             l4_vnormal_eq972 env uvars g a' e2'')`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vprt_lam972 THEN ASM_REWRITE_TAC [l4_vpar_red_t_refl972];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom':l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 dom cod`]
      l4_vhas_type_lam_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u_d:l4_vlevel961`) (X_CHOOSE_TAC `b_d:l4_vexpr961`)) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 dom' b_d) (L4VForallE961 dom cod)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VLam961 dom' e1`;`L4VLam961 dom' e1`;`L4VLam961 dom' e1`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_d:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th ->
      MP_TAC (MATCH_MP l4_vis_defeq_u_forallE_inv972 (CONJ (ASSUME `l4_venv_wf966 env`)
        (CONJ (ASSUME `l4_defeq_injectivity972 env`)
          (CONJ (ASSUME `l4_vctx_wf966 env uvars g`) th))))) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `w1:l4_vlevel961`) (X_CHOOSE_TAC `w2:l4_vlevel961`)) THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom' g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u_d:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS dom' g) e1' cod` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_t_has_type972 THEN
     MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                           `e1:l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`b_d:l4_vexpr961`;`w2:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g a' dom'` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_ts_has_type972 THEN
     MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                           `x1:l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`w1:l4_vlevel961`] THEN
     ASM_SIMP_TAC [l4_vis_defeq_symm961;GSYM l4_vhas_type961]; ALL_TAC] THEN
    SUBGOAL_THEN `?e_res. l4_vpar_red_ts972 env uvars pat g (L4VApp961 f' a') e_res /\
                          l4_vnormal_eq972 env uvars g e_res (l4_vinst0961 e1' a')`
      (X_CHOOSE_THEN `e_res:l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [MATCH_MP_TAC l4_vpar_red_ext_par_red_beta972 THEN
     MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`l4_vinst0961 cod a'`] THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN
     EXISTS_TAC `L4VLam961 dom' e1'` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN MATCH_MP_TAC l4_vnormal_eq_defeq972 THEN
      ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u_d:l4_vlevel961` THEN ASM_REWRITE_TAC []];
     EXISTS_TAC `e_res:l4_vexpr961` THEN CONJ_TAC THENL
     [REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
      EXISTS_TAC `L4VApp961 f' a'` THEN ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN
      MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vnormal_eq_trans972 THEN EXISTS_TAC `l4_vinst0961 e1' a'` THEN
      ASM_REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vnormal_eq_instN_r972 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`dom':l4_vexpr961`;
                            `CONS (dom':l4_vexpr961) g`;`cod:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [l4_vctx_instN_zero966]]];
    (* extra *)
    MATCH_MP_TAC l4_pp_norm_app972 THEN
    MAP_EVERY EXISTS_TAC [`f2:l4_vexpr961`;`x2:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                          `p:l4_vpattern972`;`ck:l4_vpattern_check972`;`m2:bool list->l4_vexpr961`] THEN
    ASM_REWRITE_TAC []];
   (* lamDF *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `dom:l4_vexpr961`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                        `b1:l4_vexpr961`;`b2:l4_vexpr961`;`u:l4_vlevel961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_venv_closed966 env`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_venv_wf_closed966]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VLam961 dom2 b2) e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [SUBGOAL_THEN `l4_vhas_type961 env uvars g dom (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `?cod0. l4_vis_defeq961 env uvars (CONS dom g) b1 b2 cod0`
      (X_CHOOSE_TAC `cod0:l4_vexpr961`) THENL
    [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS dom g) b1 cod0 /\
                  l4_vhas_type961 env uvars (CONS dom g) b2 cod0` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vis_defeq_refl_r961]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat (CONS dom g) b2 body'` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom2:l4_vexpr961) g`;`cod0:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_SIMP_TAC [l4_vis_defeq_ctx_zero966;l4_vis_defeq_symm961];
      REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966]]; ALL_TAC] THEN
    SUBGOAL_THEN `?b1'. l4_vpar_red_ts972 env uvars pat (CONS dom g) b1 b1' /\
                        l4_vnormal_eq972 env uvars (CONS dom g) b1' body'`
      (X_CHOOSE_THEN `b1':l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `L4VLam961 dom1 b1'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN
      REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
      REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vpar_red_ts_defeqDFC972 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`cod0:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
      EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
      MATCH_MP_TAC l4_vn_lamDF972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
      EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN
      EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC []]];
    ASM_MESON_TAC [l4_vpattern_matches_not_lam972]];
   (* forallEDF *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `dom:l4_vexpr961`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                        `cod1:l4_vexpr961`;`cod2:l4_vexpr961`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_venv_closed966 env`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_venv_wf_closed966]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VForallE961 dom2 cod2) e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [SUBGOAL_THEN `?dom1'. l4_vpar_red_ts972 env uvars pat g dom1 dom1' /\
                          l4_vnormal_eq972 env uvars g dom1' dom''`
      (X_CHOOSE_THEN `dom1':l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars g dom (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS dom g) cod2 (L4VSort961 v)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `cod1:l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom dom2 (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vpar_red_t972 env uvars pat (CONS dom g) cod2 cod'` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_t_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom2:l4_vexpr961) g`;`L4VSort961 v`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_SIMP_TAC [l4_vis_defeq_ctx_zero966;l4_vis_defeq_symm961];
      REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
      MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966]]; ALL_TAC] THEN
    SUBGOAL_THEN `?cod1'. l4_vpar_red_ts972 env uvars pat (CONS dom g) cod1 cod1' /\
                          l4_vnormal_eq972 env uvars (CONS dom g) cod1' cod'`
      (X_CHOOSE_THEN `cod1':l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom2 dom'' (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_t_defeq972 THEN
     EXISTS_TAC `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN
     EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    EXISTS_TAC `L4VForallE961 dom1' cod1'` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_ts_forallE972 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vpar_red_ts_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom:l4_vexpr961) g`;`L4VSort961 v`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
     EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
     MATCH_MP_TAC l4_vn_forallEDF972 THEN
     MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom'':l4_vexpr961` THEN
      ASM_SIMP_TAC [l4_vis_defeq_u_symm972;l4_vnormal_eq_defeq972] THEN
      MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN
      ASM_REWRITE_TAC [];
      ASM_MESON_TAC [l4_vpar_red_ts_has_type972]]];
    ASM_MESON_TAC [l4_vpattern_matches_not_forallE972]];
   (* etaL *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `e2:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env` ASSUME_TAC THENL [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e2:l4_vexpr961`;`e2:l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_is_type966) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
   SUBGOAL_THEN `?e_res. l4_vpar_red_ts972 env uvars pat (CONS dom g) e e_res /\
                         l4_vnormal_eq972 env uvars (CONS dom g) e_res
                           (L4VApp961 (l4_vlift961 e2') (L4VBVar961 0))`
     (X_CHOOSE_THEN `e_res:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vprt_app972 THEN REWRITE_TAC [l4_vprt_bvar972;l4_vlift961] THEN
     MATCH_MP_TAC l4_vpar_red_t_weakN972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
     ASM_REWRITE_TAC [l4_vctx_liftN_one966]];
    EXISTS_TAC `L4VLam961 dom e_res` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
     MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vpar_red_t_has_type972]]];
   (* etaR *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `e1:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vpar_red_t972 env uvars pat g (L4VLam961 dom e) e2'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_t_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `e1:l4_vexpr961`;`e1:l4_vexpr961`;`L4VForallE961 dom cod`]
      l4_vis_defeq_is_type966) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vhas_type961]; DISCH_TAC] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_type_forall_inv966) THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (K ALL_TAC)) THEN
    SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `?t. l4_vpar_red_ts972 env uvars pat (CONS dom g)
                        (L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)) t /\
                      l4_vnormal_eq972 env uvars (CONS dom g) t body'`
      (X_CHOOSE_THEN `t:l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    MP_TAC (SPECL [`l4_vpar_red_t972 env uvars pat (CONS dom g)`;
                   `L4VApp961 (l4_vlift961 e1) (L4VBVar961 0)`;`t:l4_vexpr961`]
      l4_vnormal_eq_par_red_etaR_split_ind972) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972]; ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPECL [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `g:l4_vexpr961 list`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;`e1:l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
    [EXISTS_TAC `L4VLam961 dom0 t` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vn_lamDF972 THEN
     MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_r972 THEN
      ASM_REWRITE_TAC [];
      ASM_MESON_TAC [l4_vpar_red_t_defeq972]];
     l4_subst_vars_tac972 THEN
     SUBGOAL_THEN `?ty_b. l4_vis_defeq961 env uvars (CONS dom g)
                            (L4VApp961 (l4_vlift961 e') (L4VBVar961 0)) body' ty_b`
       (X_CHOOSE_TAC `ty_b:l4_vexpr961`) THENL
     [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN ASM_SIMP_TAC [l4_vnormal_eq_defeq972]; ALL_TAC] THEN
     EXISTS_TAC `e':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vnormal_eq_trans972 THEN EXISTS_TAC `L4VLam961 dom body'` THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vn_etaR972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN
      ASM_MESON_TAC [l4_vpar_red_ts_has_type972];
      MATCH_MP_TAC l4_vn_lamDF972 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN CONJ_TAC THENL
      [ASM_MESON_TAC [l4_vpar_red_t_defeq972];
       MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty_b:l4_vexpr961` THEN
       ASM_MESON_TAC [l4_vis_defeq_refl_r961]]]];
    ASM_MESON_TAC [l4_vpattern_matches_not_lam972]];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `h:l4_vexpr961` THEN
   REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
   MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vpar_red_t_has_type972]]);;

let l4_vnormal_eq_par_red972 = prove
 (`!env uvars pat g e1 e2 e2'.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 /\
   l4_vpar_red_t972 env uvars pat g e2 e2' ==>
   ?e1'. l4_vpar_red_ts972 env uvars pat g e1 e1' /\
         l4_vnormal_eq972 env uvars g e1' e2'`,
  MESON_TAC [l4_vnormal_eq_par_red_ind972]);;

let l4_vnormal_eq_par_red_s_ind972 = prove
 (`!R e2 e2'.
   l4_vrt_closure972 R e2 e2' ==>
   (!env uvars pat g e1.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vnormal_eq972 env uvars g e1 e2 ==>
      ?e1'. l4_vpar_red_ts972 env uvars pat g e1 e1' /\
            l4_vnormal_eq972 env uvars g e1' e2')`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN EXISTS_TAC `e1:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?e1_mid. l4_vpar_red_ts972 env uvars pat g e1 e1_mid /\
                          l4_vnormal_eq972 env uvars g e1_mid y`
     (X_CHOOSE_THEN `e1_mid:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [];
    SUBGOAL_THEN `?e1'. l4_vpar_red_ts972 env uvars pat g e1_mid e1' /\
                        l4_vnormal_eq972 env uvars g e1' z`
      (X_CHOOSE_THEN `e1':l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [ASM_MESON_TAC [l4_vnormal_eq_par_red972];
     EXISTS_TAC `e1':l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vpar_red_ts972] THEN
     ASM_MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts972]]]]);;

let l4_vnormal_eq_par_red_s972 = prove
 (`!env uvars pat g e1 e2 e2'.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 /\
   l4_vpar_red_ts972 env uvars pat g e2 e2' ==>
   ?e1'. l4_vpar_red_ts972 env uvars pat g e1 e1' /\
         l4_vnormal_eq972 env uvars g e1' e2'`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vnormal_eq_par_red_s_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_ts_strip_ind972 = prove
 (`!R b a2.
   l4_vrt_closure972 R b a2 ==>
   (!env uvars pat g c ty_b.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g b ty_b /\
      l4_vpar_red_t972 env uvars pat g b c ==>
      ?d1 d2. l4_vpar_red_t972 env uvars pat g a2 d1 /\
              l4_vpar_red_ts972 env uvars pat g c d2 /\
              l4_vnormal_eq972 env uvars g d1 d2)`,
  MATCH_MP_TAC l4_vrt_closure_STRONG_INDUCT972 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MAP_EVERY EXISTS_TAC [`c:l4_vexpr961`;`c:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
   MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty_b:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vpar_red_t_has_type972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?u1 u2. l4_vpar_red_t972 env uvars pat g y u1 /\
                         l4_vpar_red_ts972 env uvars pat g c u2 /\
                         l4_vnormal_eq972 env uvars g u1 u2`
     (X_CHOOSE_THEN `u1:l4_vexpr961` (X_CHOOSE_THEN `u2:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?v1 v2. l4_vpar_red_t972 env uvars pat g u1 v1 /\
                         l4_vpar_red_t972 env uvars pat g z v2 /\
                         l4_vnormal_eq972 env uvars g v1 v2`
     (X_CHOOSE_THEN `v1:l4_vexpr961` (X_CHOOSE_THEN `v2:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MATCH_MP_TAC l4_vpar_red_t_church_rosser972 THEN
    MAP_EVERY EXISTS_TAC [`y:l4_vexpr961`;`ty_b:l4_vexpr961`] THEN
    ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_ts972]; ALL_TAC] THEN
   SUBGOAL_THEN `?w2. l4_vpar_red_ts972 env uvars pat g u2 w2 /\
                      l4_vnormal_eq972 env uvars g w2 v1`
     (X_CHOOSE_THEN `w2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC l4_vnormal_eq_par_red972 THEN EXISTS_TAC `u1:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vnormal_eq_symm972];
    MAP_EVERY EXISTS_TAC [`v2:l4_vexpr961`;`w2:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [l4_vpar_red_ts972] THEN CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts972];
     ASM_MESON_TAC [l4_vnormal_eq_symm972;l4_vnormal_eq_trans972]]]]);;

let l4_vpar_red_ts_cr_ind972 = prove
 (`!R e e2.
   l4_vrt_closure972 R e e2 ==>
   (!env uvars pat g e1 ty.
      R = l4_vpar_red_t972 env uvars pat g /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g /\
      l4_vhas_type961 env uvars g e ty /\
      l4_vpar_red_ts972 env uvars pat g e e1 ==>
      ?e1' e2'. l4_vpar_red_ts972 env uvars pat g e1 e1' /\
                l4_vpar_red_ts972 env uvars pat g e2 e2' /\
                l4_vnormal_eq972 env uvars g e1' e2')`,
  MATCH_MP_TAC l4_vrt_closure_STRONG_INDUCT972 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MAP_EVERY EXISTS_TAC [`e1:l4_vexpr961`;`e1:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN
   MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_ts972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?a1 a2. l4_vpar_red_ts972 env uvars pat g e1 a1 /\
                         l4_vpar_red_ts972 env uvars pat g y a2 /\
                         l4_vnormal_eq972 env uvars g a1 a2`
     (X_CHOOSE_THEN `a1:l4_vexpr961` (X_CHOOSE_THEN `a2:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?d1 d2. l4_vpar_red_t972 env uvars pat g a2 d1 /\
                         l4_vpar_red_ts972 env uvars pat g z d2 /\
                         l4_vnormal_eq972 env uvars g d1 d2`
     (X_CHOOSE_THEN `d1:l4_vexpr961` (X_CHOOSE_THEN `d2:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`l4_vpar_red_t972 env uvars pat g`;`y:l4_vexpr961`;`a2:l4_vexpr961`]
      l4_vpar_red_ts_strip_ind972) THEN
    ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vpar_red_ts972]; ALL_TAC] THEN
   SUBGOAL_THEN `?e1'. l4_vpar_red_ts972 env uvars pat g a1 e1' /\
                       l4_vnormal_eq972 env uvars g e1' d1`
     (X_CHOOSE_THEN `e1':l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vnormal_eq_par_red972];
    MAP_EVERY EXISTS_TAC [`e1':l4_vexpr961`;`d2:l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vrtc_trans972;l4_vpar_red_ts972];
     ASM_MESON_TAC [l4_vnormal_eq_trans972]]]]);;

let l4_vpar_red_ts_church_rosser972 = prove
 (`!env uvars pat g e e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpar_red_ts972 env uvars pat g e e1 /\
   l4_vpar_red_ts972 env uvars pat g e e2 ==>
   l4_vcr_defeq972 env uvars pat g e1 e2`,
  REWRITE_TAC [l4_vcr_defeq972] THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC `ty:l4_vexpr961` THEN ASM_MESON_TAC [l4_vpar_red_ts_has_type972];
   EXISTS_TAC `ty:l4_vexpr961` THEN ASM_MESON_TAC [l4_vpar_red_ts_has_type972];
   ASM_MESON_TAC [l4_vpar_red_ts_cr_ind972;l4_vpar_red_ts972]]);;

(* VCRDefEq equivalence relation and IsDefEq.church_rosser *)

let l4_vcr_defeq_normal_eq972 = prove
 (`!env uvars pat g e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vnormal_eq972 env uvars g e1 e2 ==>
   l4_vcr_defeq972 env uvars pat g e1 e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vcr_defeq972] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ty. l4_vis_defeq961 env uvars g e1 e2 ty` (X_CHOOSE_TAC `ty:l4_vexpr961`) THENL
  [REWRITE_TAC [GSYM l4_vis_defeq_u961] THEN
   ASM_MESON_TAC [l4_vnormal_eq_defeq972;l4_pp_wf972;l4_pp_inj972];
   REPEAT CONJ_TAC THENL
   [EXISTS_TAC `ty:l4_vexpr961` THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961];
    EXISTS_TAC `ty:l4_vexpr961` THEN ASM_MESON_TAC [l4_vis_defeq_refl_r961];
    MAP_EVERY EXISTS_TAC [`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972]]]);;

let l4_vcr_defeq_refl972 = prove
 (`!env uvars pat g e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vcr_defeq972 env uvars pat g e e`,
  MESON_TAC [l4_vcr_defeq_normal_eq972;l4_vn_refl972]);;

let l4_vcr_defeq_defeq972 = prove
 (`!env uvars pat g e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vcr_defeq972 env uvars pat g e1 e2 ==>
   l4_vis_defeq_u961 env uvars g e1 e2`,
  REWRITE_TAC [l4_vcr_defeq972;l4_vis_defeq_u961] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
  EXISTS_TAC `ty1:l4_vexpr961` THEN
  MATCH_MP_TAC l4_vis_defeq_trans_l972 THEN
  MAP_EVERY EXISTS_TAC [`e1':l4_vexpr961`;`ty2:l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC [l4_vpar_red_ts_defeq972];
   MATCH_MP_TAC l4_vis_defeq_trans_u_r972 THEN EXISTS_TAC `e2':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [l4_vnormal_eq_defeq972];
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_MESON_TAC [l4_vpar_red_ts_defeq972]]]);;

let l4_vcr_defeq_symm972 = prove
 (`!env uvars pat g e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vcr_defeq972 env uvars pat g e1 e2 ==>
   l4_vcr_defeq972 env uvars pat g e2 e1`,
  REWRITE_TAC [l4_vcr_defeq972] THEN
  MESON_TAC [l4_vnormal_eq_symm972;l4_pp_wf972;l4_pp_inj972]);;

let l4_vcr_defeq_trans972 = prove
 (`!env uvars pat g e1 e2 e3.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vcr_defeq972 env uvars pat g e1 e2 /\
   l4_vcr_defeq972 env uvars pat g e2 e3 ==>
   l4_vcr_defeq972 env uvars pat g e1 e3`,
  REWRITE_TAC [l4_vcr_defeq972] THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC `ty1:l4_vexpr961` THEN ASM_REWRITE_TAC [];
   EXISTS_TAC `ty2':l4_vexpr961` THEN ASM_REWRITE_TAC [];
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?m1 m2. l4_vpar_red_ts972 env uvars pat g e2' m1 /\
                         l4_vpar_red_ts972 env uvars pat g e1'' m2 /\
                         l4_vnormal_eq972 env uvars g m1 m2`
     (X_CHOOSE_THEN `m1:l4_vexpr961` (X_CHOOSE_THEN `m2:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `g:l4_vexpr961 list`;`e2:l4_vexpr961`;`e2':l4_vexpr961`;`e1'':l4_vexpr961`;
      `ty2:l4_vexpr961`] l4_vpar_red_ts_church_rosser972) THEN
    ASM_REWRITE_TAC [l4_vcr_defeq972] THEN MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `(?a_e1. l4_vpar_red_ts972 env uvars pat g e1' a_e1 /\ l4_vnormal_eq972 env uvars g a_e1 m1) /\
      (?b_e3. l4_vpar_red_ts972 env uvars pat g e2'' b_e3 /\ l4_vnormal_eq972 env uvars g b_e3 m2)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vnormal_eq_par_red_s972];
     ASM_MESON_TAC [l4_vnormal_eq_par_red_s972;l4_vnormal_eq_symm972]];
    MAP_EVERY EXISTS_TAC [`a_e1:l4_vexpr961`;`b_e3:l4_vexpr961`] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
     EXISTS_TAC `e1':l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972];
     REWRITE_TAC [l4_vpar_red_ts972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
     EXISTS_TAC `e2'':l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vpar_red_ts972];
     MATCH_MP_TAC l4_vnormal_eq_trans972 THEN EXISTS_TAC `m2:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vnormal_eq_trans972;l4_vnormal_eq_symm972]]]]);;

let l4_vcr_defeq_mk972 = prove
 (`!env uvars pat g d1 d2 ty d1' d2'.
   l4_vis_defeq961 env uvars g d1 d2 ty /\
   l4_vpar_red_ts972 env uvars pat g d1 d1' /\
   l4_vpar_red_ts972 env uvars pat g d2 d2' /\
   l4_vnormal_eq972 env uvars g d1' d2' ==>
   l4_vcr_defeq972 env uvars pat g d1 d2`,
  REWRITE_TAC [l4_vcr_defeq972] THEN
  MESON_TAC [l4_vis_defeq_refl_l961;l4_vis_defeq_refl_r961]);;

let l4_vis_defeq_church_rosser_ind972 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   (!pat.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g ==>
      l4_vcr_defeq972 env uvars pat g e1 e2)`,
  MATCH_MP_TAC l4_vis_defeq_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vcr_defeq_refl972 THEN
   EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_bvar961 THEN ASM_REWRITE_TAC [];
   (* symm *)
   MESON_TAC [l4_vcr_defeq_symm972];
   (* trans *)
   MESON_TAC [l4_vcr_defeq_trans972];
   (* sort *)
   MESON_TAC [l4_vcr_defeq_normal_eq972;l4_vn_sortDF972];
   (* const *)
   MESON_TAC [l4_vcr_defeq_normal_eq972;l4_vn_constDF972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `f1:l4_vexpr961`;`f2:l4_vexpr961`;`a1:l4_vexpr961`;`a2:l4_vexpr961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(?f1' f2'. l4_vpar_red_ts972 env uvars pat g f1 f1' /\
                 l4_vpar_red_ts972 env uvars pat g f2 f2' /\
                 l4_vnormal_eq972 env uvars g f1' f2') /\
      (?a1' a2'. l4_vpar_red_ts972 env uvars pat g a1 a1' /\
                 l4_vpar_red_ts972 env uvars pat g a2 a2' /\
                 l4_vnormal_eq972 env uvars g a1' a2')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vcr_defeq972];
    MATCH_MP_TAC l4_vcr_defeq_mk972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vinst0961 cod a1`;`L4VApp961 f1' a1'`;`L4VApp961 f2' a2'`] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_app972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vn_appDF972 THEN
     MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
     ASM_MESON_TAC [l4_vpar_red_ts_has_type972;l4_vis_defeq_refl_l961;l4_vis_defeq_refl_r961]]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                        `b1:l4_vexpr961`;`b2:l4_vexpr961`;
                        `u:l4_vlevel961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g dom1 (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(?dom1' dom2'. l4_vpar_red_ts972 env uvars pat g dom1 dom1' /\
                     l4_vpar_red_ts972 env uvars pat g dom2 dom2' /\
                     l4_vnormal_eq972 env uvars g dom1' dom2') /\
      (?b1' b2'. l4_vpar_red_ts972 env uvars pat (CONS dom1 g) b1 b1' /\
                 l4_vpar_red_ts972 env uvars pat (CONS dom1 g) b2 b2' /\
                 l4_vnormal_eq972 env uvars (CONS dom1 g) b1' b2')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vcr_defeq972];
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom1 dom1' (L4VSort961 u)` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_vpar_red_ts_defeq972]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vcr_defeq_mk972 THEN
    MAP_EVERY EXISTS_TAC [`L4VForallE961 dom1 cod`;
                          `L4VLam961 dom1' b1'`;`L4VLam961 dom2' b2'`] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_lam972 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vpar_red_ts_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom1:l4_vexpr961) g`;`cod:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
      ASM_MESON_TAC [l4_vis_defeq_refl_r961]];
     MATCH_MP_TAC l4_vn_lamDF972 THEN
     MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_trans_u_l972 THEN EXISTS_TAC `dom1':l4_vexpr961` THEN
     ASM_SIMP_TAC [l4_vnormal_eq_defeq972]]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                        `cod1:l4_vexpr961`;`cod2:l4_vexpr961`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g dom1 (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(?dom1' dom2'. l4_vpar_red_ts972 env uvars pat g dom1 dom1' /\
                     l4_vpar_red_ts972 env uvars pat g dom2 dom2' /\
                     l4_vnormal_eq972 env uvars g dom1' dom2') /\
      (?cod1' cod2'. l4_vpar_red_ts972 env uvars pat (CONS dom1 g) cod1 cod1' /\
                     l4_vpar_red_ts972 env uvars pat (CONS dom1 g) cod2 cod2' /\
                     l4_vnormal_eq972 env uvars (CONS dom1 g) cod1' cod2')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vcr_defeq972];
    MATCH_MP_TAC l4_vcr_defeq_mk972 THEN
    MAP_EVERY EXISTS_TAC [`L4VSort961 (L4VLIMax961 u v)`;
                          `L4VForallE961 dom1' cod1'`;`L4VForallE961 dom2' cod2'`] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_forallE972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vpar_red_ts_forallE972 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vpar_red_ts_defeqDFC972 THEN
     MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`CONS (dom1:l4_vexpr961) g`;`L4VSort961 v`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN EXISTS_TAC `u:l4_vlevel961` THEN
      ASM_REWRITE_TAC [l4_vis_defeq_ctx_zero966];
      ASM_MESON_TAC [l4_vis_defeq_refl_r961]];
     MATCH_MP_TAC l4_vn_forallEDF972 THEN
     MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vpar_red_ts_defeq972;l4_vpar_red_ts_has_type972;l4_vis_defeq_refl_l961]]];
   (* conv *)
   MESON_TAC [];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `dom:l4_vexpr961`;`body:l4_vexpr961`;`arg:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g (L4VApp961 (L4VLam961 dom body) arg)
                   (l4_vinst0961 body arg) (l4_vinst0961 cod arg)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_beta961 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vcr_defeq_mk972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vinst0961 cod arg`;
                          `l4_vinst0961 body arg`;`l4_vinst0961 body arg`] THEN
    ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_single972 THEN MATCH_MP_TAC l4_vprt_beta972 THEN
     REWRITE_TAC [l4_vpar_red_t_refl972];
     MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `l4_vinst0961 cod arg` THEN
     ASM_MESON_TAC [l4_vis_defeq_refl_r961]]];
   (* eta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `e:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC l4_vcr_defeq_normal_eq972 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vn_etaL972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `cod:l4_vexpr961` THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                  `l4_vlift961 e`;`L4VBVar961 0`;`l4_vlift961 dom`;`l4_vliftN961 cod 1 1`]
     l4_vhas_type_app972) THEN
   REWRITE_TAC [l4_vinst0961;l4_vinst_vliftN_bvar0_11_972;l4_vinst_vliftN_bvar0966] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vhas_type961;l4_vlift_forall_eq972] THEN
    MATCH_MP_TAC l4_vis_defeq_weak966 THEN
    ASM_MESON_TAC [l4_pp_wf972;l4_venv_wf_closed966];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
    REWRITE_TAC [l4_vlookup_zero961]];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vcr_defeq_normal_eq972 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vn_proofIrrel972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vhas_type961];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `df:l4_vdefeq961`;`ls:l4_vlevel961 list`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `uvars:num`;`g:l4_vexpr961 list`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`]
     l4_pp_extra_pat972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `p:l4_vpattern972`
     (X_CHOOSE_THEN `r:l4_vrhs972`
       (X_CHOOSE_THEN `ck:l4_vpattern_check972`
         (X_CHOOSE_THEN `m1:l4_vlevel961 list`
           (X_CHOOSE_THEN `m2:bool list->l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g (l4_vinstL961 ls (l4_vdf_lhs961 df))
                   (l4_vinstL961 ls (l4_vdf_rhs961 df)) (l4_vinstL961 ls (l4_vdf_type961 df))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_extra961 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vcr_defeq_mk972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vinstL961 ls (l4_vdf_type961 df)`;
                          `l4_vrhs_apply972 m1 m2 r`;`l4_vrhs_apply972 m1 m2 r`] THEN
    ASM_REWRITE_TAC [l4_vpar_red_ts972;l4_vrtc_rfl972] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_single972 THEN MATCH_MP_TAC l4_vprt_extra972 THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`;
                           `m2:bool list->l4_vexpr961`] THEN
     ASM_MESON_TAC [l4_pp_rhs_check_wf972;l4_vpar_red_t_refl972];
     MATCH_MP_TAC l4_vn_refl972 THEN EXISTS_TAC `l4_vinstL961 ls (l4_vdf_type961 df)` THEN
     ASM_MESON_TAC [l4_vis_defeq_refl_r961]]]]);;

let l4_vis_defeq_church_rosser972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vcr_defeq972 env uvars pat g e1 e2`,
  MESON_TAC [l4_vis_defeq_church_rosser_ind972]);;

let l4_vis_defeq_church_rosser_params972 = prove
 (`!env uvars g e1 e2 ty.
   l4_pattern_params972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   ?pat. l4_pattern_params_for972 env pat /\ l4_vcr_defeq972 env uvars pat g e1 e2`,
  REWRITE_TAC [l4_pattern_params972] THEN
  MESON_TAC [l4_vis_defeq_church_rosser972]);;

(* ========================================================================= *)
(* 4. Weak Head Reduction, Kashima Standardization, and Type Inference       *)
(*    (Lean4Lean/Theory/Typing/HeadReduction.lean)                           *)
(* ========================================================================= *)

let l4_params_simple_app972 = prove
 (`!env pat p r ck p1 p2.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\
   l4_vsubpattern972 (L4VPApp972 p1 p2) p ==>
   L4VPApp972 p1 p2 = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;
    `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
    `p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`] l4_pp_simple972) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `sp:l4_vsimple_pattern972`) THEN
  l4_subst_vars_tac972 THEN
  UNDISCH_TAC `l4_vsubpattern972 (L4VPApp972 p1 p2) (l4_vsimple_to_pattern972 sp)` THEN
  STRUCT_CASES_TAC (SPEC `sp:l4_vsimple_pattern972` (cases "l4_vsimple_pattern972")) THEN
  REWRITE_TAC [l4_vsimple_to_pattern972] THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vsubpattern_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
  [ASM_REWRITE_TAC [];
   MP_TAC (SPECL [`L4VPApp972 p1 p2`;`a0:l4_name`;`a1:num`] l4_vsubpattern_varN_const972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `k:num`) THEN
   UNDISCH_TAC `L4VPApp972 p1 p2 = l4_vpattern_varN972 (L4VPConst972 a0) k` THEN
   STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
   REWRITE_TAC [l4_vpattern_varN972;distinctness "l4_vpattern972"];
   MP_TAC (SPECL [`L4VPApp972 p1 p2`;`a2:l4_name`;`a3:num`] l4_vsubpattern_varN_const972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `k:num`) THEN
   UNDISCH_TAC `L4VPApp972 p1 p2 = l4_vpattern_varN972 (L4VPConst972 a2) k` THEN
   STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
   REWRITE_TAC [l4_vpattern_varN972;distinctness "l4_vpattern972"]]);;

let l4_vis_major_premise972 = new_definition
 `l4_vis_major_premise972
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) e <=>
   ?p r ck p1 p2 m1 m2.
     pat p (r, ck) /\
     l4_vsubpattern972 (L4VPApp972 p1 p2) p /\
     l4_vpattern_matches972 p1 e m1 m2`;;

let l4_vis_major_premise_lift_prime972 = prove
 (`!pat rho e.
   l4_vis_major_premise972 pat (l4_vlift_prime969 e rho) <=>
   l4_vis_major_premise972 pat e`,
  REWRITE_TAC [l4_vis_major_premise972;l4_vpattern_matches_vlift_prime972] THEN
  MESON_TAC []);;

let l4_vis_major_premise_instN972 = prove
 (`!pat e1 a k.
   l4_vis_major_premise972 pat e1 ==>
   l4_vis_major_premise972 pat (l4_vinst961 e1 a k)`,
  REWRITE_TAC [l4_vis_major_premise972] THEN
  MESON_TAC [l4_vpattern_matches_vinst972]);;

let l4_vis_major_premise_lam972 = prove
 (`!pat dom e. ~l4_vis_major_premise972 pat (L4VLam961 dom e)`,
  REWRITE_TAC [l4_vis_major_premise972] THEN
  MESON_TAC [l4_vpattern_matches_not_lam972]);;

let l4_vpattern_check_ok_weak_prime972 = prove
 (`!env uvars rho g g' p ck m1 m2.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vcheck_wf972 p ck /\
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck ==>
   l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g') m1
     (l4_vmenv_map972 (\x. l4_vlift_prime969 x rho) p m2) ck`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
  MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g`;
                        `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty:l4_vexpr961`))) THEN
  EXISTS_TAC `l4_vlift_prime969 ty rho` THEN
  ASM_SIMP_TAC [GSYM l4_vrhs_apply_vlift_prime972] THEN
  MATCH_MP_TAC l4_vis_defeq_weak_prime969 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_SIMP_TAC [l4_venv_wf_closed966]);;

(* Weak Head Reduction *)

let l4_vwhred_RULES972,l4_vwhred_INDUCT972,l4_vwhred_CASES972 =
  new_inductive_definition
 `(!env uvars (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g f f' a.
     l4_vwhred972 env uvars pat g f f' ==>
     l4_vwhred972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a)) /\
  (!env uvars pat g f a a'.
     l4_vis_major_premise972 pat f /\
     l4_vwhred972 env uvars pat g a a' ==>
     l4_vwhred972 env uvars pat g (L4VApp961 f a) (L4VApp961 f a')) /\
  (!env uvars pat g dom e a.
     l4_vwhred972 env uvars pat g (L4VApp961 (L4VLam961 dom e) a) (l4_vinst0961 e a)) /\
  (!env uvars pat g p r ck e m1 m2.
     pat p (r, ck) /\
     l4_vrhs_wf972 p r /\
     l4_vcheck_wf972 p ck /\
     l4_vpattern_matches972 p e m1 m2 /\
     l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g) m1 m2 ck ==>
     l4_vwhred972 env uvars pat g e (l4_vrhs_apply972 m1 m2 r))`;;

let l4_vwhr_app972,
    l4_vwhr_major972,
    l4_vwhr_beta972,
    l4_vwhr_extra972 =
  match CONJUNCTS l4_vwhred_RULES972 with
  | [c1;c2;c3;c4] -> (c1,c2,c3,c4)
  | _ -> failwith "l4_vwhred_RULES972: unexpected arity";;

let l4_vwhred_STRONG_INDUCT972 =
  derive_strong_induction (l4_vwhred_RULES972, l4_vwhred_INDUCT972);;

let l4_vwhred_defeqDFC_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vwhred972 env uvars pat g1 e1 e2 ==>
   (!g0 g2.
      l4_venv_wf966 env /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
      l4_vwhred972 env uvars pat g2 e1 e2)`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vwhr_app972];
   MESON_TAC [l4_vwhr_major972];
   REWRITE_TAC [l4_vwhr_beta972];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;
     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC l4_vwhr_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g1`;
                         `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN
   MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ty:l4_vexpr961`))) THEN
   EXISTS_TAC `ty:l4_vexpr961` THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`] THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966]]);;

let l4_vwhred_defeqDFC972 = prove
 (`!env uvars pat g0 g1 g2 e1 e2.
   l4_venv_wf966 env /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vwhred972 env uvars pat g1 e1 e2 ==>
   l4_vwhred972 env uvars pat g2 e1 e2`,
  MESON_TAC [l4_vwhred_defeqDFC_ind972]);;

let l4_vwhred_weak_prime_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vwhred972 env uvars pat g e1 e2 ==>
   (!rho g'.
      l4_venv_wf966 env /\
      l4_vctx_lift_prime969 rho g g' ==>
      l4_vwhred972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho))`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vwhr_app972 THEN ASM_SIMP_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vwhr_major972 THEN
   ASM_SIMP_TAC [l4_vis_major_premise_lift_prime972];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vlift_prime969;l4_vlift_prime_vinst0_hi969;l4_vwhr_beta972];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;
     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vlift_prime972] THEN
   MATCH_MP_TAC l4_vwhr_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`] THEN
   ASM_REWRITE_TAC [l4_vpattern_matches_vlift_prime972] THEN CONJ_TAC THENL
   [EXISTS_TAC `m2:bool list->l4_vexpr961` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vpattern_check_ok_weak_prime972 THEN
    EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC []]]);;

let l4_vwhred_weak_prime972 = prove
 (`!env uvars pat rho g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vwhred972 env uvars pat g e1 e2 ==>
   l4_vwhred972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho)`,
  MESON_TAC [l4_vwhred_weak_prime_ind972]);;

let l4_vwhred_weakN972 = prove
 (`!env uvars pat n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vwhred972 env uvars pat g e1 e2 ==>
   l4_vwhred972 env uvars pat g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969] THEN
  MATCH_MP_TAC l4_vwhred_weak_prime972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_REWRITE_TAC [GSYM l4_vctx_liftN_iff_lift_prime969]);;

let l4_vwhred_weak_u_inv_ind972 = prove
 (`!env uvars pat g' e1' e2'.
   l4_vwhred972 env uvars pat g' e1' e2' ==>
   (!rho g e1.
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g' /\
      l4_vctx_lift_prime969 rho g g' /\
      e1' = l4_vlift_prime969 e1 rho ==>
      ?e2. e2' = l4_vlift_prime969 e2 rho /\ l4_vwhred972 env uvars pat g e1 e2)`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;`a:l4_vexpr961`] THEN
   DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`a0:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `f2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VApp961 f2 a1` THEN ASM_SIMP_TAC [l4_vlift_prime969;l4_vwhr_app972];
   (* major *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`f:l4_vexpr961`;`a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`a1:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VApp961 a0 a2` THEN ASM_REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vwhr_major972 THEN
   ASM_MESON_TAC [l4_vis_major_premise_lift_prime972];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom:l4_vexpr961`;`e:l4_vexpr961`;`arg:l4_vexpr961`] THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `e1:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))) THEN
   STRUCT_CASES_TAC (SPEC `a0:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   EXISTS_TAC `l4_vinst0961 a1' a1` THEN
   REWRITE_TAC [l4_vlift_prime_vinst0_hi969;l4_vwhr_beta972];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;
     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MP_TAC (SPECL [`p:l4_vpattern972`;`rho:l4_vlift_op969`;`e1:l4_vexpr961`;
                  `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`]
     l4_vpattern_matches_vlift_prime972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `m2_0:bool list->l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `l4_vrhs_apply972 m1 m2_0 r` THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vlift_prime972] THEN
   MATCH_MP_TAC l4_vwhr_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g'`;
                         `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN
   MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`rho:l4_vlift_op969`;
                  `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `l4_vrhs_apply972 m1 m2_0 ra`;`l4_vrhs_apply972 m1 m2_0 rb`]
     l4_vis_defeq_u_weak_prime_iff972) THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vlift_prime972]]);;

let l4_vwhred_weak_u_inv972 = prove
 (`!env uvars pat rho g g' e1 e2'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vwhred972 env uvars pat g' (l4_vlift_prime969 e1 rho) e2' ==>
   ?e2. e2' = l4_vlift_prime969 e2 rho /\ l4_vwhred972 env uvars pat g e1 e2`,
  MESON_TAC [l4_vwhred_weak_u_inv_ind972]);;

let l4_vwhred_par_red972 = prove
 (`!env uvars pat g e1 e2.
   l4_vwhred972 env uvars pat g e1 e2 ==>
   l4_vpar_red_t972 env uvars pat g e1 e2`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN
  MESON_TAC [l4_vprt_app972;l4_vprt_beta972;l4_vprt_extra972;l4_vpar_red_t_refl972]);;

let l4_vwhred_defeq972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vwhred972 env uvars pat g e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vis_defeq961 env uvars g e1 e2 ty`,
  MESON_TAC [l4_vpar_red_t_defeq972;l4_vwhred_par_red972]);;

let l4_vwhred_has_type972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vwhred972 env uvars pat g e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vhas_type961 env uvars g e2 ty`,
  MESON_TAC [l4_vwhred_defeq972;l4_vis_defeq_refl_r961]);;

let l4_vwhred_instN_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vwhred972 env uvars pat g1 e1 e2 ==>
   (!g0 a a0 k g2.
      l4_venv_wf966 env /\
      l4_vhas_type961 env uvars g0 a a0 /\
      l4_vctx_instN966 g0 a a0 k g1 g2 ==>
      l4_vwhred972 env uvars pat g2 (l4_vinst961 e1 a k) (l4_vinst961 e2 a k))`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vwhr_app972 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vwhr_major972 THEN
   ASM_MESON_TAC [l4_vis_major_premise_instN972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966;l4_vwhr_beta972];
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;
     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vrhs_apply_vinst972] THEN
   MATCH_MP_TAC l4_vwhr_extra972 THEN
   MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`] THEN
   ASM_SIMP_TAC [l4_vpattern_matches_vinst972] THEN
   MATCH_MP_TAC l4_vpattern_check_ok_instN972 THEN
   MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
   ASM_REWRITE_TAC []]);;

let l4_vwhred_instN972 = prove
 (`!env uvars pat g0 a a0 k g1 g e1 e2.
   l4_venv_wf966 env /\
   l4_vhas_type961 env uvars g0 a a0 /\
   l4_vctx_instN966 g0 a a0 k g1 g /\
   l4_vwhred972 env uvars pat g1 e1 e2 ==>
   l4_vwhred972 env uvars pat g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k)`,
  MESON_TAC [l4_vwhred_instN_ind972]);;

(* Weak Head Normal Forms and Determinism *)

let l4_vwhnf972 = new_definition
 `l4_vwhnf972 env uvars
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e <=>
   !e'. ~l4_vwhred972 env uvars pat g e e'`;;

let l4_vwhnf_bvar972 = prove
 (`!env uvars pat g i. l4_vwhnf972 env uvars pat g (L4VBVar961 i)`,
  REWRITE_TAC [l4_vwhnf972] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [l4_vwhred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"] THEN
  MESON_TAC [l4_vpattern_matches_not_bvar972]);;

let l4_vwhnf_lam972 = prove
 (`!env uvars pat g dom e. l4_vwhnf972 env uvars pat g (L4VLam961 dom e)`,
  REWRITE_TAC [l4_vwhnf972] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [l4_vwhred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"] THEN
  MESON_TAC [l4_vpattern_matches_not_lam972]);;

let l4_vwhnf_sort972 = prove
 (`!env uvars pat g u. l4_vwhnf972 env uvars pat g (L4VSort961 u)`,
  REWRITE_TAC [l4_vwhnf972] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [l4_vwhred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"] THEN
  MESON_TAC [l4_vpattern_matches_not_sort972]);;

let l4_vwhnf_forallE972 = prove
 (`!env uvars pat g dom cod. l4_vwhnf972 env uvars pat g (L4VForallE961 dom cod)`,
  REWRITE_TAC [l4_vwhnf972] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [l4_vwhred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961"] THEN
  MESON_TAC [l4_vpattern_matches_not_forallE972]);;

let l4_vwhnf_subpattern_aux_ind972 = prove
 (`!env uvars pat g e e'.
   l4_vwhred972 env uvars pat g e e' ==>
   (!p r ck c n m1 m2.
      l4_pattern_params_for972 env pat /\
      pat p (r, ck) /\
      (!r0 ck0. ~pat (L4VPConst972 c) (r0, ck0)) /\
      l4_vsubpattern972 (l4_vpattern_varN972 (L4VPConst972 c) n) p /\
      l4_vpattern_matches972 (l4_vpattern_varN972 (L4VPConst972 c) n) e m1 m2 ==>
      F)`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;`a:l4_vexpr961`] THEN
   DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                        `c:l4_name`;`n:num`;`m1:l4_vlevel961 list`;
                        `m2:bool list->l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
   REWRITE_TAC [l4_vpattern_varN972;l4_vpattern_matches_const_inv972;
                l4_vpattern_matches_var_inv972;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   MATCH_MP_TAC (TAUT `(a ==> F) ==> ~a`) THEN STRIP_TAC THEN l4_subst_vars_tac972 THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                                  `c:l4_name`;`n':num`;`m1:l4_vlevel961 list`;
                                  `mf:bool list->l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vsubpattern_trans972 THEN
   EXISTS_TAC `L4VPVar972 (l4_vpattern_varN972 (L4VPConst972 c) n')` THEN
   ASM_SIMP_TAC [l4_vsubpattern_varL972;l4_vsubpattern_refl972];
   (* major *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                        `c:l4_name`;`n:num`;`m1:l4_vlevel961 list`;
                        `m2:bool list->l4_vexpr961`] THEN
   STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
   REWRITE_TAC [l4_vpattern_varN972;l4_vpattern_matches_const_inv972;
                l4_vpattern_matches_var_inv972;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   MATCH_MP_TAC (TAUT `(a ==> F) ==> ~a`) THEN STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vis_major_premise972 pat f` THEN
   REWRITE_TAC [l4_vis_major_premise972] THEN
   DISCH_THEN (X_CHOOSE_THEN `p':l4_vpattern972`
     (X_CHOOSE_THEN `r':l4_vrhs972`
       (X_CHOOSE_THEN `ck':l4_vpattern_check972`
         (X_CHOOSE_THEN `p1':l4_vpattern972`
           (X_CHOOSE_THEN `p2':l4_vpattern972`
             (X_CHOOSE_THEN `mf1:l4_vlevel961 list`
               (X_CHOOSE_THEN `mf2:bool list->l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   SUBGOAL_THEN `L4VPApp972 p1' p2' = p'` (SUBST_ALL_TAC o SYM) THENL
   [ASM_MESON_TAC [l4_params_simple_app972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`] l4_pp_simple972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `sp:l4_vsimple_pattern972`) THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?p_int mr1 mr2.
     l4_vpattern_inter972 p1' (l4_vpattern_varN972 (L4VPConst972 c) n') = SOME p_int /\
     l4_vpattern_matches972 p_int f mr1 mr2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC [GSYM l4_vpattern_matches_inter972] THEN ASM_MESON_TAC []; ALL_TAC] THEN
   UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) (l4_vsimple_to_pattern972 sp) (r, ck)` THEN
   UNDISCH_TAC `l4_vsubpattern972 (L4VPVar972 (l4_vpattern_varN972 (L4VPConst972 c) n'))
                  (l4_vsimple_to_pattern972 sp)` THEN
   STRUCT_CASES_TAC (SPEC `sp:l4_vsimple_pattern972` (cases "l4_vsimple_pattern972")) THEN
   PURE_REWRITE_TAC [l4_vsimple_to_pattern972] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsubpattern_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC (TAUT `(a ==> F) ==> ~a`) THEN DISCH_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `L4VPApp972 (l4_vpattern_varN972 (L4VPConst972 a0) a1)
                  (l4_vpattern_varN972 (L4VPConst972 a2) a3)`;
      `L4VPApp972 p1' p2'`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
      `r':l4_vrhs972`;`ck':l4_vpattern_check972`;
      `l4_vpattern_varN972 (L4VPConst972 a0) a1`;
      `l4_vpattern_varN972 (L4VPConst972 a2) a3`;
      `p1':l4_vpattern972`;`p2':l4_vpattern972`;
      `l4_vpattern_varN972 (L4VPConst972 c) n'`] l4_pp_app_l_uniq972) THEN
    ASM_REWRITE_TAC [l4_vsubpattern_refl972;distinctness "option"];
    MP_TAC (SPECL [`env:l4_venv961`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `L4VPApp972 p1' p2'`;
      `L4VPApp972 (l4_vpattern_varN972 (L4VPConst972 a0) a1)
                  (l4_vpattern_varN972 (L4VPConst972 a2) a3)`;
      `r':l4_vrhs972`;`ck':l4_vpattern_check972`;
      `r:l4_vrhs972`;`ck:l4_vpattern_check972`;
      `p1':l4_vpattern972`;`p2':l4_vpattern972`;
      `l4_vpattern_varN972 (L4VPConst972 a0) a1`;
      `l4_vpattern_varN972 (L4VPConst972 a2) a3`;
      `p1':l4_vpattern972`;`l4_vpattern_varN972 (L4VPConst972 c) n'`] l4_pp_app_uniq972) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vsubpattern_refl972] THEN
     MATCH_MP_TAC l4_vsubpattern_trans972 THEN
     EXISTS_TAC `L4VPVar972 (l4_vpattern_varN972 (L4VPConst972 c) n')` THEN
     ASM_SIMP_TAC [l4_vsubpattern_varL972;l4_vsubpattern_refl972];
     ASM_REWRITE_TAC [distinctness "option"]]];
   (* beta *)
   MESON_TAC [l4_vpattern_matches_not_app_lam972];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p':l4_vpattern972`;`r':l4_vrhs972`;
     `ck':l4_vpattern_check972`;`e0:l4_vexpr961`;
     `m1':l4_vlevel961 list`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `?p_int mr1 mr2.
     l4_vpattern_inter972 p' (l4_vpattern_varN972 (L4VPConst972 c) n) = SOME p_int /\
     l4_vpattern_matches972 p_int e0 mr1 mr2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC [GSYM l4_vpattern_matches_inter972] THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `p:l4_vpattern972 = p' /\ p' = l4_vpattern_varN972 (L4VPConst972 c) n`
     STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC l4_pp_uniq972 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `p_int:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
      `r':l4_vrhs972`;`ck':l4_vpattern_check972`] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   l4_subst_vars_tac972 THEN
   UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) (l4_vpattern_varN972 (L4VPConst972 c) n) (r', ck')` THEN
   STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
   REWRITE_TAC [l4_vpattern_varN972] THENL
   [ASM_MESON_TAC []; ASM_MESON_TAC [l4_params_pat_not_var972]]]);;

let l4_vwhnf_subpattern972 = prove
 (`!env uvars pat g p r ck p1 e m1 m2.
   l4_pattern_params_for972 env pat /\
   pat p (r, ck) /\
   l4_vsubpattern972 p1 p /\
   ~(p1 = p) /\
   l4_vpattern_matches972 p1 e m1 m2 ==>
   l4_vwhnf972 env uvars pat g e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?c n. p1 = l4_vpattern_varN972 (L4VPConst972 c) n`
    (X_CHOOSE_THEN `c:l4_name` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)) THENL
  [MP_TAC (SPECL [`env:l4_venv961`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`] l4_pp_simple972) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `sp:l4_vsimple_pattern972`) THEN
   l4_subst_vars_tac972 THEN
   UNDISCH_TAC `~(p1 = l4_vsimple_to_pattern972 sp)` THEN
   UNDISCH_TAC `l4_vsubpattern972 p1 (l4_vsimple_to_pattern972 sp)` THEN
   STRUCT_CASES_TAC (SPEC `sp:l4_vsimple_pattern972` (cases "l4_vsimple_pattern972")) THEN
   REWRITE_TAC [l4_vsimple_to_pattern972] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vsubpattern_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
   ASM_MESON_TAC [l4_vsubpattern_varN_const972]; ALL_TAC] THEN
  SUBGOAL_THEN `!r0 ck0. ~((pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) (L4VPConst972 c) (r0, ck0))` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `p = L4VPConst972 c /\ L4VPConst972 c = L4VPConst972 c` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC l4_pp_uniq972 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `L4VPConst972 c`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
      `r0:l4_vrhs972`;`ck0:l4_vpattern_check972`] THEN
    ASM_REWRITE_TAC [l4_vpattern_inter_self972;l4_vsubpattern_refl972] THEN
    MATCH_MP_TAC l4_vsubpattern_trans972 THEN
    EXISTS_TAC `l4_vpattern_varN972 (L4VPConst972 c) n` THEN
    ASM_SIMP_TAC [l4_vsubpattern_varN972;l4_vsubpattern_refl972];
    l4_subst_vars_tac972 THEN
    ASM_MESON_TAC [l4_vsubpattern_antisymm972;l4_vsubpattern_varN972;l4_vsubpattern_refl972]];
   REWRITE_TAC [l4_vwhnf972] THEN
   ASM_MESON_TAC [l4_vwhnf_subpattern_aux_ind972]]);;

let l4_vis_major_premise_whnf972 = prove
 (`!env uvars pat g e.
   l4_pattern_params_for972 env pat /\
   l4_vis_major_premise972 pat e ==>
   l4_vwhnf972 env uvars pat g e`,
  REWRITE_TAC [l4_vis_major_premise972] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vwhnf_subpattern972 THEN
  MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                        `p1:l4_vpattern972`;`m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vsubpattern_trans972 THEN EXISTS_TAC `L4VPApp972 p1 p2` THEN
   ASM_SIMP_TAC [l4_vsubpattern_appL972;l4_vsubpattern_refl972];
   DISCH_THEN (fun th ->
     MP_TAC (MATCH_MP l4_vsubpattern_size_le972 (ASSUME `l4_vsubpattern972 (L4VPApp972 p1 p2) p`)) THEN
     REWRITE_TAC [GSYM th;l4_vpattern_size972] THEN ARITH_TAC)]);;

let l4_vwhred_determ_ind972 = prove
 (`!env uvars pat g e e1.
   l4_vwhred972 env uvars pat g e e1 ==>
   (!e2. l4_pattern_params_for972 env pat /\
         l4_vwhred972 env uvars pat g e e2 ==> e1 = e2)`,
  MATCH_MP_TAC l4_vwhred_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`f':l4_vexpr961`;`a:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vwhred972 env uvars pat g (L4VApp961 f a) e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [];
    ASM_MESON_TAC [l4_vis_major_premise_whnf972;l4_vwhnf972];
    ASM_MESON_TAC [l4_vwhnf_lam972;l4_vwhnf972];
    UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
    UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 f a) m1 m2` THEN
    STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
    REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                 l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                 injectivity "l4_vexpr961"] THENL
    [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
     ASM_MESON_TAC [l4_vis_major_premise_whnf972;l4_vis_major_premise972;
                    l4_vsubpattern_refl972;l4_vwhnf972];
     DISCH_TAC THEN DISCH_THEN (fun th ->
       MP_TAC (MATCH_MP l4_params_pat_not_var972 (ASSUME `l4_pattern_params_for972 env pat`)) THEN
       MP_TAC th THEN MESON_TAC [])]];
   (* major *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`f:l4_vexpr961`;`a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vwhred972 env uvars pat g (L4VApp961 f a) e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_MESON_TAC [l4_vis_major_premise_whnf972;l4_vwhnf972];
    AP_TERM_TAC THEN ASM_MESON_TAC [];
    ASM_MESON_TAC [l4_vis_major_premise_lam972];
    UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
    UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 f a) m1 m2` THEN
    STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
    REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                 l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                 injectivity "l4_vexpr961"] THENL
    [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
       `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`g:l4_vexpr961 list`;
       `L4VPApp972 a0 a1`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
       `a1:l4_vpattern972`;`a:l4_vexpr961`;`ls2:l4_vlevel961 list`;`ma:bool list->l4_vexpr961`]
       l4_vwhnf_subpattern972) THEN
     ANTS_TAC THENL
     [ASM_SIMP_TAC [l4_vsubpattern_appR972;l4_vsubpattern_refl972] THEN
      DISCH_THEN (fun th ->
        MP_TAC (AP_TERM `l4_vpattern_size972` th) THEN
        REWRITE_TAC [l4_vpattern_size972] THEN ARITH_TAC);
      ASM_MESON_TAC [l4_vwhnf972]];
     DISCH_TAC THEN DISCH_THEN (fun th ->
       MP_TAC (MATCH_MP l4_params_pat_not_var972 (ASSUME `l4_pattern_params_for972 env pat`)) THEN
       MP_TAC th THEN MESON_TAC [])]];
   (* beta *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vwhred972 env uvars pat g (L4VApp961 (L4VLam961 dom e) a) e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [ASM_MESON_TAC [l4_vwhnf_lam972;l4_vwhnf972];
    ASM_MESON_TAC [l4_vis_major_premise_lam972];
    REFL_TAC;
    ASM_MESON_TAC [l4_vpattern_matches_not_app_lam972]];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e:l4_vexpr961`;
     `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vwhred972 env uvars pat g e e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
    UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 f a) m1 m2` THEN
    STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
    REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                 l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                 injectivity "l4_vexpr961"] THENL
    [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
     ASM_MESON_TAC [l4_vis_major_premise_whnf972;l4_vis_major_premise972;
                    l4_vsubpattern_refl972;l4_vwhnf972];
     DISCH_TAC THEN DISCH_THEN (fun th ->
       MP_TAC (MATCH_MP l4_params_pat_not_var972 (ASSUME `l4_pattern_params_for972 env pat`)) THEN
       MP_TAC th THEN MESON_TAC [])];
    UNDISCH_TAC `(pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) p (r,ck)` THEN
    UNDISCH_TAC `l4_vpattern_matches972 p (L4VApp961 f a) m1 m2` THEN
    STRUCT_CASES_TAC (SPEC `p:l4_vpattern972` (cases "l4_vpattern972")) THEN
    REWRITE_TAC [l4_vpattern_matches_const_inv972;l4_vpattern_matches_var_inv972;
                 l4_vpattern_matches_app_inv972;distinctness "l4_vexpr961";
                 injectivity "l4_vexpr961"] THENL
    [REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
       `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`g:l4_vexpr961 list`;
       `L4VPApp972 a0 a1`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
       `a1:l4_vpattern972`;`a:l4_vexpr961`;`ls2:l4_vlevel961 list`;`ma:bool list->l4_vexpr961`]
       l4_vwhnf_subpattern972) THEN
     ANTS_TAC THENL
     [ASM_SIMP_TAC [l4_vsubpattern_appR972;l4_vsubpattern_refl972] THEN
      DISCH_THEN (fun th ->
        MP_TAC (AP_TERM `l4_vpattern_size972` th) THEN
        REWRITE_TAC [l4_vpattern_size972] THEN ARITH_TAC);
      ASM_MESON_TAC [l4_vwhnf972]];
     DISCH_TAC THEN DISCH_THEN (fun th ->
       MP_TAC (MATCH_MP l4_params_pat_not_var972 (ASSUME `l4_pattern_params_for972 env pat`)) THEN
       MP_TAC th THEN MESON_TAC [])];
    ASM_MESON_TAC [l4_vpattern_matches_not_app_lam972];
    SUBGOAL_THEN `?p_int mr1 mr2.
      l4_vpattern_inter972 p' p = SOME p_int /\ l4_vpattern_matches972 p_int e mr1 mr2`
      STRIP_ASSUME_TAC THENL
    [REWRITE_TAC [GSYM l4_vpattern_matches_inter972] THEN ASM_MESON_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `p:l4_vpattern972 = p'` SUBST_ALL_TAC THENL
    [ASM_MESON_TAC [l4_pp_uniq972;l4_vsubpattern_refl972]; ALL_TAC] THEN
    SUBGOAL_THEN `r:l4_vrhs972 = r' /\ ck:l4_vpattern_check972 = ck'` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_pp_rhs_uniq972]; ALL_TAC] THEN
    SUBGOAL_THEN `m1:l4_vlevel961 list = m1' /\ m2:bool list->l4_vexpr961 = m2'`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_vpattern_matches_uniq972]; ASM_REWRITE_TAC []]]]);;

let l4_vwhred_determ972 = prove
 (`!env uvars pat g e e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vwhred972 env uvars pat g e e1 /\
   l4_vwhred972 env uvars pat g e e2 ==>
   e1 = e2`,
  MESON_TAC [l4_vwhred_determ_ind972]);;

(* Multi-step Weak Head Reduction *)

let l4_vwhred_s972 = new_definition
 `l4_vwhred_s972 env uvars
    (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e1 e2 <=>
   l4_vrt_closure972 (l4_vwhred972 env uvars pat g) e1 e2`;;

let l4_vwhred_s_defeqDFC_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat g0 g1 g2.
      R = l4_vwhred972 env uvars pat g1 /\
      l4_venv_wf966 env /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 ==>
      l4_vwhred_s972 env uvars pat g2 e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_defeqDFC972]);;

let l4_vwhred_s_defeqDFC972 = prove
 (`!env uvars pat g0 g1 g2 e1 e2.
   l4_venv_wf966 env /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vwhred_s972 env uvars pat g1 e1 e2 ==>
   l4_vwhred_s972 env uvars pat g2 e1 e2`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_defeqDFC_ind972;l4_vwhred_s972]);;

let l4_vwhred_s_par_red_s_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat g.
      R = l4_vwhred972 env uvars pat g ==>
      l4_vpar_red_ts972 env uvars pat g e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_par_red972]);;

let l4_vwhred_s_par_red_s972 = prove
 (`!env uvars pat g e1 e2.
   l4_vwhred_s972 env uvars pat g e1 e2 ==>
   l4_vpar_red_ts972 env uvars pat g e1 e2`,
  REWRITE_TAC [l4_vwhred_s972] THEN MESON_TAC [l4_vwhred_s_par_red_s_ind972]);;

let l4_vwhred_s_app_ind972 = prove
 (`!R f f'.
   l4_vrt_closure972 R f f' ==>
   (!env uvars pat g a.
      R = l4_vwhred972 env uvars pat g ==>
      l4_vwhred_s972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhr_app972]);;

let l4_vwhred_s_app972 = prove
 (`!env uvars pat g f f' a.
   l4_vwhred_s972 env uvars pat g f f' ==>
   l4_vwhred_s972 env uvars pat g (L4VApp961 f a) (L4VApp961 f' a)`,
  REWRITE_TAC [l4_vwhred_s972] THEN MESON_TAC [l4_vwhred_s_app_ind972;l4_vwhred_s972]);;

let l4_vwhred_s_major_ind972 = prove
 (`!R a a'.
   l4_vrt_closure972 R a a' ==>
   (!env uvars pat g f.
      R = l4_vwhred972 env uvars pat g /\
      l4_vis_major_premise972 pat f ==>
      l4_vwhred_s972 env uvars pat g (L4VApp961 f a) (L4VApp961 f a'))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhr_major972]);;

let l4_vwhred_s_major972 = prove
 (`!env uvars pat g f a a'.
   l4_vis_major_premise972 pat f /\
   l4_vwhred_s972 env uvars pat g a a' ==>
   l4_vwhred_s972 env uvars pat g (L4VApp961 f a) (L4VApp961 f a')`,
  REWRITE_TAC [l4_vwhred_s972] THEN MESON_TAC [l4_vwhred_s_major_ind972;l4_vwhred_s972]);;

let l4_vwhred_s_defeq972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vwhred_s972 env uvars pat g e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vis_defeq961 env uvars g e1 e2 ty`,
  MESON_TAC [l4_vpar_red_ts_defeq972;l4_vwhred_s_par_red_s972]);;

let l4_vwhred_s_has_type972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vwhred_s972 env uvars pat g e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vhas_type961 env uvars g e2 ty`,
  MESON_TAC [l4_vwhred_s_defeq972;l4_vis_defeq_refl_r961]);;

let l4_vwhred_s_weak_prime_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat rho g g'.
      R = l4_vwhred972 env uvars pat g /\
      l4_venv_wf966 env /\
      l4_vctx_lift_prime969 rho g g' ==>
      l4_vwhred_s972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_weak_prime972]);;

let l4_vwhred_s_weak_prime972 = prove
 (`!env uvars pat rho g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vwhred_s972 env uvars pat g e1 e2 ==>
   l4_vwhred_s972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho)`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_weak_prime_ind972;l4_vwhred_s972]);;

let l4_vwhred_s_weakN972 = prove
 (`!env uvars pat n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vwhred_s972 env uvars pat g e1 e2 ==>
   l4_vwhred_s972 env uvars pat g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969] THEN
  MATCH_MP_TAC l4_vwhred_s_weak_prime972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_REWRITE_TAC [GSYM l4_vctx_liftN_iff_lift_prime969]);;

let l4_vwhred_s_instN_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat g0 a a0 k g1 g2.
      R = l4_vwhred972 env uvars pat g1 /\
      l4_venv_wf966 env /\
      l4_vhas_type961 env uvars g0 a a0 /\
      l4_vctx_instN966 g0 a a0 k g1 g2 ==>
      l4_vwhred_s972 env uvars pat g2 (l4_vinst961 e1 a k) (l4_vinst961 e2 a k))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_instN972]);;

let l4_vwhred_s_instN972 = prove
 (`!env uvars pat g0 a a0 k g1 g e1 e2.
   l4_venv_wf966 env /\
   l4_vhas_type961 env uvars g0 a a0 /\
   l4_vctx_instN966 g0 a a0 k g1 g /\
   l4_vwhred_s972 env uvars pat g1 e1 e2 ==>
   l4_vwhred_s972 env uvars pat g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k)`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_instN_ind972;l4_vwhred_s972]);;

let l4_vwhnf_whred_s972 = prove
 (`!env uvars pat g e e'.
   l4_vwhnf972 env uvars pat g e /\
   l4_vwhred_s972 env uvars pat g e e' ==>
   e = e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vwhred_s972] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  UNDISCH_TAC `l4_vwhnf972 env uvars pat g e` THEN
  REWRITE_TAC [IMP_IMP] THEN
  SPEC_TAC (`e':l4_vexpr961`,`e':l4_vexpr961`) THEN
  SPEC_TAC (`e:l4_vexpr961`,`e:l4_vexpr961`) THEN
  REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
  MP_TAC (ISPECL [`l4_vwhred972 env uvars pat g`;
                  `(\x z. l4_vwhnf972 env uvars pat g x ==> x = z)`] l4_vrtc_head_ind972) THEN
  BETA_TAC THEN
  ANTS_TAC THENL [REWRITE_TAC [l4_vwhnf972] THEN MESON_TAC []; MESON_TAC []]);;

let l4_vwhred_s_determ972 = prove
 (`!env uvars pat g e e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vwhred_s972 env uvars pat g e e1 /\
   l4_vwhnf972 env uvars pat g e1 /\
   l4_vwhred_s972 env uvars pat g e e2 /\
   l4_vwhnf972 env uvars pat g e2 ==>
   e1 = e2`,
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC [l4_vwhred_s972] THEN
  MP_TAC (ISPECL [`l4_vwhred972 env uvars pat g`;
                  `(\x z. l4_vwhnf972 env uvars pat g z ==>
                          !e2. l4_vwhred_s972 env uvars pat g x e2 /\
                               l4_vwhnf972 env uvars pat g e2 ==> z = e2)`]
    l4_vrtc_head_ind972) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MESON_TAC [l4_vwhnf_whred_s972];
    MAP_EVERY X_GEN_TAC [`x:l4_vexpr961`;`y:l4_vexpr961`;`z:l4_vexpr961`] THEN
    STRIP_TAC THEN DISCH_TAC THEN X_GEN_TAC `w:l4_vexpr961` THEN
    REWRITE_TAC [l4_vwhred_s972] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP l4_vrtc_to_hd_ind972) ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vrtc_hd_CASES972] THEN
    DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
    [l4_subst_vars_tac972 THEN ASM_MESON_TAC [l4_vwhnf972];
     SUBGOAL_THEN `y:l4_vexpr961 = y'` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [l4_vwhred_determ972];
      ASM_MESON_TAC [l4_vrtc_of_hd_ind972;l4_vwhred_s972]]]];
   REWRITE_TAC [l4_vwhred_s972] THEN MESON_TAC []]);;

let l4_vwhred_s_weak_u_inv_ind972 = prove
 (`!R e1' e2'.
   l4_vrt_closure972 R e1' e2' ==>
   (!env uvars pat rho g g' e1.
      R = l4_vwhred972 env uvars pat g' /\
      l4_venv_wf966 env /\
      l4_defeq_injectivity972 env /\
      l4_vctx_wf966 env uvars g' /\
      l4_vctx_lift_prime969 rho g g' /\
      e1' = l4_vlift_prime969 e1 rho ==>
      ?e2. e2' = l4_vlift_prime969 e2 rho /\ l4_vwhred_s972 env uvars pat g e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN EXISTS_TAC `e1:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?y0. y = l4_vlift_prime969 y0 rho /\ l4_vwhred_s972 env uvars pat g e1 y0`
     (X_CHOOSE_THEN `y0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [];
    l4_subst_vars_tac972 THEN
    SUBGOAL_THEN `?z0. z = l4_vlift_prime969 z0 rho /\ l4_vwhred972 env uvars pat g y0 z0`
      (X_CHOOSE_THEN `z0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
    [ASM_MESON_TAC [l4_vwhred_weak_u_inv972];
     EXISTS_TAC `z0:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vwhred_s972] THEN
     MATCH_MP_TAC l4_vrtc_tail972 THEN EXISTS_TAC `y0:l4_vexpr961` THEN
     ASM_REWRITE_TAC [GSYM l4_vwhred_s972]]]]);;

let l4_vwhred_s_weak_u_inv972 = prove
 (`!env uvars pat rho g g' e1 e2'.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vwhred_s972 env uvars pat g' (l4_vlift_prime969 e1 rho) e2' ==>
   ?e2. e2' = l4_vlift_prime969 e2 rho /\ l4_vwhred_s972 env uvars pat g e1 e2`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_weak_u_inv_ind972;l4_vwhred_s972]);;

(* ========================================================================= *)
(* 4b. Kashima Standard Reduction (l4_vstred972), Standardization,           *)
(*     Head Reduction to Sort/ForallE, and Syntax-Directed Type Inference    *)
(* ========================================================================= *)

let l4_vstred_RULES972,l4_vstred_INDUCT972,l4_vstred_CASES972 =
  new_inductive_definition
 `(!env uvars (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g e i.
     l4_vwhred_s972 env uvars pat g e (L4VBVar961 i) ==>
     l4_vstred972 env uvars pat g e (L4VBVar961 i)) /\
  (!env uvars pat g e u.
     l4_vwhred_s972 env uvars pat g e (L4VSort961 u) ==>
     l4_vstred972 env uvars pat g e (L4VSort961 u)) /\
  (!env uvars pat g e c ls.
     l4_vwhred_s972 env uvars pat g e (L4VConst961 c ls) ==>
     l4_vstred972 env uvars pat g e (L4VConst961 c ls)) /\
  (!env uvars pat g e f f' a a'.
     l4_vwhred_s972 env uvars pat g e (L4VApp961 f a) /\
     l4_vstred972 env uvars pat g f f' /\
     l4_vstred972 env uvars pat g a a' ==>
     l4_vstred972 env uvars pat g e (L4VApp961 f' a')) /\
  (!env uvars pat g e dom dom' body body'.
     l4_vwhred_s972 env uvars pat g e (L4VLam961 dom body) /\
     l4_vstred972 env uvars pat g dom dom' /\
     l4_vstred972 env uvars pat (CONS dom g) body body' ==>
     l4_vstred972 env uvars pat g e (L4VLam961 dom' body')) /\
  (!env uvars pat g e dom dom' cod cod'.
     l4_vwhred_s972 env uvars pat g e (L4VForallE961 dom cod) /\
     l4_vstred972 env uvars pat g dom dom' /\
     l4_vstred972 env uvars pat (CONS dom g) cod cod' ==>
     l4_vstred972 env uvars pat g e (L4VForallE961 dom' cod'))`;;

let l4_vstr_bvar972,
    l4_vstr_sort972,
    l4_vstr_const972,
    l4_vstr_app972,
    l4_vstr_lam972,
    l4_vstr_forallE972 =
  match CONJUNCTS l4_vstred_RULES972 with
  | [c1;c2;c3;c4;c5;c6] -> (c1,c2,c3,c4,c5,c6)
  | _ -> failwith "l4_vstred_RULES972: unexpected arity";;

let l4_vstred_STRONG_INDUCT972 =
  derive_strong_induction (l4_vstred_RULES972, l4_vstred_INDUCT972);;

let l4_vstred_refl_ind972 = prove
 (`!e env uvars pat g. l4_vstred972 env uvars pat g e e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_bvar972 THEN
   REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_sort972 THEN
   REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_const972 THEN
   REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`a0:l4_vexpr961`;`a1:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_lam972 THEN
   MAP_EVERY EXISTS_TAC [`a0:l4_vexpr961`;`a1:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`a0:l4_vexpr961`;`a1:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972]]);;

let l4_vstred_refl972 = prove
 (`!env uvars pat g e. l4_vstred972 env uvars pat g e e`,
  MESON_TAC [l4_vstred_refl_ind972]);;

let l4_vstred_bvar_l972 = prove
 (`!env uvars pat g i e.
   l4_vstred972 env uvars pat g (L4VBVar961 i) e ==> e = L4VBVar961 i`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE [l4_vwhnf_bvar972]
    (SPECL [`env:l4_venv961`;`uvars:num`;
            `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
            `g:l4_vexpr961 list`;`L4VBVar961 i`] l4_vwhnf_whred_s972))) THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);;

let l4_vstred_sort_l972 = prove
 (`!env uvars pat g u e.
   l4_vstred972 env uvars pat g (L4VSort961 u) e ==> e = L4VSort961 u`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE [l4_vwhnf_sort972]
    (SPECL [`env:l4_venv961`;`uvars:num`;
            `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
            `g:l4_vexpr961 list`;`L4VSort961 u`] l4_vwhnf_whred_s972))) THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);;

let l4_vstred_lam_l972 = prove
 (`!env uvars pat g dom body e.
   l4_vstred972 env uvars pat g (L4VLam961 dom body) e ==>
   ?dom' body'.
     e = L4VLam961 dom' body' /\
     l4_vstred972 env uvars pat g dom dom' /\
     l4_vstred972 env uvars pat (CONS dom g) body body'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE [l4_vwhnf_lam972]
    (SPECL [`env:l4_venv961`;`uvars:num`;
            `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
            `g:l4_vexpr961 list`;`L4VLam961 dom body`] l4_vwhnf_whred_s972))) THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN ASM_MESON_TAC []);;

let l4_vstred_forallE_l972 = prove
 (`!env uvars pat g dom cod e.
   l4_vstred972 env uvars pat g (L4VForallE961 dom cod) e ==>
   ?dom' cod'.
     e = L4VForallE961 dom' cod' /\
     l4_vstred972 env uvars pat g dom dom' /\
     l4_vstred972 env uvars pat (CONS dom g) cod cod'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE [l4_vwhnf_forallE972]
    (SPECL [`env:l4_venv961`;`uvars:num`;
            `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
            `g:l4_vexpr961 list`;`L4VForallE961 dom cod`] l4_vwhnf_whred_s972))) THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN ASM_MESON_TAC []);;

let l4_vstred_defeqDFC_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vstred972 env uvars pat g1 e1 e2 ==>
   (!g0 g2 ty.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      l4_vhas_type961 env uvars g1 e1 ty ==>
      l4_vstred972 env uvars pat g2 e1 e2)`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_bvar972 THEN
   ASM_MESON_TAC [l4_vwhred_s_defeqDFC972;l4_pp_wf972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_sort972 THEN
   ASM_MESON_TAC [l4_vwhred_s_defeqDFC972;l4_pp_wf972];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vstr_const972 THEN
   ASM_MESON_TAC [l4_vwhred_s_defeqDFC972;l4_pp_wf972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`e:l4_vexpr961`;`f:l4_vexpr961`;`f':l4_vexpr961`;
     `a:l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VApp961 f a) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `af:l4_vexpr961` (X_CHOOSE_THEN `bf:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vstr_app972 THEN MAP_EVERY EXISTS_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_defeqDFC972];
    ASM_MESON_TAC [];
    ASM_MESON_TAC []];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`e:l4_vexpr961`;`dom:l4_vexpr961`;`dom':l4_vexpr961`;
     `body:l4_vexpr961`;`body':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VLam961 dom body) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `bb:l4_vexpr961`)) THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_defeqDFC972];
    ASM_MESON_TAC [];
    ASM_MESON_TAC [l4_vis_defeq_ctx_succ966;l4_vhas_type961]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g1:l4_vexpr961 list`;`e:l4_vexpr961`;`dom:l4_vexpr961`;`dom':l4_vexpr961`;
     `cod:l4_vexpr961`;`cod':l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VForallE961 dom cod) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_defeqDFC972];
    ASM_MESON_TAC [];
    ASM_MESON_TAC [l4_vis_defeq_ctx_succ966;l4_vhas_type961]]]);;

let l4_vstred_defeqDFC972 = prove
 (`!env uvars pat g0 g1 g2 e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vhas_type961 env uvars g1 e1 ty /\
   l4_vstred972 env uvars pat g1 e1 e2 ==>
   l4_vstred972 env uvars pat g2 e1 e2`,
  MESON_TAC [l4_vstred_defeqDFC_ind972]);;

let l4_vstred_par_red_s972 = prove
 (`!env uvars pat g e e'.
   l4_vstred972 env uvars pat g e e' ==>
   l4_vpar_red_ts972 env uvars pat g e e'`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vwhred_s_par_red_s972];
   MESON_TAC [l4_vwhred_s_par_red_s972];
   MESON_TAC [l4_vwhred_s_par_red_s972];
   REWRITE_TAC [l4_vpar_red_ts972] THEN
   MESON_TAC [l4_vrtc_trans972;l4_vwhred_s_par_red_s972;l4_vpar_red_ts_app972;l4_vpar_red_ts972];
   REWRITE_TAC [l4_vpar_red_ts972] THEN
   MESON_TAC [l4_vrtc_trans972;l4_vwhred_s_par_red_s972;l4_vpar_red_ts_lam972;l4_vpar_red_ts972];
   REWRITE_TAC [l4_vpar_red_ts972] THEN
   MESON_TAC [l4_vrtc_trans972;l4_vwhred_s_par_red_s972;l4_vpar_red_ts_forallE972;l4_vpar_red_ts972]]);;

let l4_vstred_whred972 = prove
 (`!env uvars pat g e1 e2 e'.
   l4_vwhred_s972 env uvars pat g e1 e2 /\
   l4_vstred972 env uvars pat g e2 e' ==>
   l4_vstred972 env uvars pat g e1 e'`,
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THENL
  [MATCH_MP_TAC l4_vstr_bvar972 THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972];
   MATCH_MP_TAC l4_vstr_sort972 THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972];
   MATCH_MP_TAC l4_vstr_const972 THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972];
   MATCH_MP_TAC l4_vstr_app972 THEN MAP_EVERY EXISTS_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972];
   MATCH_MP_TAC l4_vstr_lam972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972];
   MATCH_MP_TAC l4_vstr_forallE972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_vwhred_s972;l4_vrtc_trans972]]);;

let l4_vstred_defeq972 = prove
 (`!env uvars pat g e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vstred972 env uvars pat g e1 e2 /\
   l4_vhas_type961 env uvars g e1 ty ==>
   l4_vis_defeq961 env uvars g e1 e2 ty`,
  MESON_TAC [l4_vpar_red_ts_defeq972;l4_vstred_par_red_s972]);;

let l4_vstred_weak_prime_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vstred972 env uvars pat g e1 e2 ==>
   (!rho g'.
      l4_venv_wf966 env /\
      l4_vctx_lift_prime969 rho g g' ==>
      l4_vstred972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho))`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_bvar972 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                  `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                  `rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `e:l4_vexpr961`;`L4VBVar961 i`] l4_vwhred_s_weak_prime972) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_sort972 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                  `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                  `rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `e:l4_vexpr961`;`L4VSort961 u`] l4_vwhred_s_weak_prime972) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_const972 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                  `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                  `rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `e:l4_vexpr961`;`L4VConst961 c ls`] l4_vwhred_s_weak_prime972) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_prime969 f rho`;`l4_vlift_prime969 a rho`] THEN
   ASM_MESON_TAC [l4_vwhred_s_weak_prime972;l4_vlift_prime969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_prime969 dom rho`;`l4_vlift_prime969 body (L4VLCons969 rho)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_weak_prime972;l4_vlift_prime969;l4_vctx_lift_prime_cons969];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_prime969 dom rho`;`l4_vlift_prime969 cod (L4VLCons969 rho)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_weak_prime972;l4_vlift_prime969;l4_vctx_lift_prime_cons969]]);;

let l4_vstred_weak_prime972 = prove
 (`!env uvars pat rho g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vstred972 env uvars pat g e1 e2 ==>
   l4_vstred972 env uvars pat g' (l4_vlift_prime969 e1 rho) (l4_vlift_prime969 e2 rho)`,
  MESON_TAC [l4_vstred_weak_prime_ind972]);;

let l4_vstred_weakN972 = prove
 (`!env uvars pat n k g g' e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vstred972 env uvars pat g e1 e2 ==>
   l4_vstred972 env uvars pat g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969] THEN
  MATCH_MP_TAC l4_vstred_weak_prime972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_REWRITE_TAC [GSYM l4_vctx_liftN_iff_lift_prime969]);;

let l4_vstred_instN_bvar972 = prove
 (`!g0 a1 a0 k g1 g.
   l4_vctx_instN966 g0 a1 a0 k g1 g ==>
   (!env uvars pat a2 i.
      l4_venv_wf966 env /\
      l4_vstred972 env uvars pat g0 a1 a2 ==>
      l4_vstred972 env uvars pat g (l4_vinst_var961 i a1 k) (l4_vinst_var961 i a2 k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [ASM_REWRITE_TAC [l4_vinst_var961;LT_REFL;l4_vliftN_zero961];
    REWRITE_TAC [l4_vinst_var961;ARITH_RULE `~(SUC n < 0)`;ARITH_RULE `~(SUC n = 0)`;
                 ARITH_RULE `SUC n - 1 = n`] THEN
    REWRITE_TAC [l4_vstred_refl972]];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;l4_vstred_refl972];
    REWRITE_TAC [l4_vinst_var_succ966;l4_vlift961] THEN
    MATCH_MP_TAC l4_vstred_weakN972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
    ASM_REWRITE_TAC [l4_vctx_liftN_one966] THEN ASM_MESON_TAC []]]);;

let l4_vstred_instN_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vstred972 env uvars pat g1 e1 e2 ==>
   (!g0 a1 a2 a0 k g.
      l4_venv_wf966 env /\
      l4_vstred972 env uvars pat g0 a1 a2 /\
      l4_vhas_type961 env uvars g0 a1 a0 /\
      l4_vctx_instN966 g0 a1 a0 k g1 g ==>
      l4_vstred972 env uvars pat g (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k))`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstred_whred972 THEN EXISTS_TAC `l4_vinst_var961 i a1 k` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961];
    ASM_MESON_TAC [l4_vstred_instN_bvar972]];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_sort972 THEN
   ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_const972 THEN
   ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 f a1 k`;`l4_vinst961 a a1 k`] THEN
   ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom a1 k`;`l4_vinst961 body a1 (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961;l4_vctx_instN_succ966];
   (* forallE *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom a1 k`;`l4_vinst961 cod a1 (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_instN972;l4_vinst961;l4_vctx_instN_succ966]]);;

let l4_vstred_instN972 = prove
 (`!env uvars pat g0 a1 a2 a0 k g1 g e1 e2.
   l4_venv_wf966 env /\
   l4_vstred972 env uvars pat g0 a1 a2 /\
   l4_vhas_type961 env uvars g0 a1 a0 /\
   l4_vctx_instN966 g0 a1 a0 k g1 g /\
   l4_vstred972 env uvars pat g1 e1 e2 ==>
   l4_vstred972 env uvars pat g (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k)`,
  MESON_TAC [l4_vstred_instN_ind972]);;

let l4_vstred_apply_pat_ind972 = prove
 (`!r env uvars pat g p m1 m2 m3.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==> l4_vstred972 env uvars pat g (m2 a) (m3 a)) ==>
   l4_vstred972 env uvars pat g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m3 r)`,
  MATCH_MP_TAC l4_vrhs_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vrhs_apply972;l4_vstred_refl972];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vrhs_apply972] THEN
   MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vrhs_apply972 m1 m2 a0`;`l4_vrhs_apply972 m1 m2 a1`] THEN
   REWRITE_TAC [l4_vwhred_s972;l4_vrtc_rfl972] THEN
   ASM_MESON_TAC [l4_vrhs_wf972];
   REWRITE_TAC [l4_vrhs_wf972;l4_vrhs_apply972] THEN MESON_TAC []]);;

let l4_vstred_apply_pat972 = prove
 (`!env uvars pat g p r m1 m2 m3.
   l4_vrhs_wf972 p r /\
   (!a. l4_vpath_valid972 p a ==> l4_vstred972 env uvars pat g (m2 a) (m3 a)) ==>
   l4_vstred972 env uvars pat g (l4_vrhs_apply972 m1 m2 r) (l4_vrhs_apply972 m1 m3 r)`,
  MESON_TAC [l4_vstred_apply_pat_ind972]);;

let l4_vstred_triangle_extra_pullback972 = prove
 (`!p' env uvars pat g1 p r ck e1_p m1_p m2_p e_p.
   pat p (r, ck) /\
   l4_vsubpattern972 p' p /\
   l4_vpattern_matches972 p' e1_p m1_p m2_p /\
   l4_vstred972 env uvars pat g1 e_p e1_p ==>
   ?e0_p m3_p.
     l4_vwhred_s972 env uvars pat g1 e_p e0_p /\
     l4_vpattern_matches972 p' e0_p m1_p m3_p /\
     (!x. l4_vpath_valid972 p' x ==> l4_vstred972 env uvars pat g1 (m3_p x) (m2_p x))`,
  MATCH_MP_TAC l4_vpattern_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* const *)
   X_GEN_TAC `c:l4_name` THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpattern_matches972 (L4VPConst972 c) e1_p m1_p m2_p` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e_p (L4VConst961 c m1_p)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MAP_EVERY EXISTS_TAC [`L4VConst961 c m1_p`;`l4_vmenv_empty972`] THEN
   ASM_REWRITE_TAC [l4_vpm_const972;l4_vpath_valid_clauses972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`pf:l4_vpattern972`;`pa:l4_vpattern972`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHf") (LABEL_TAC "IHa")) THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpattern_matches972 (L4VPApp972 pf pa) e1_p m1_p m2_p` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_app_inv972] THEN STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e_p (L4VApp961 f' a')` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN
     `(?f0' mf3. l4_vwhred_s972 env uvars pat g1 f f0' /\
                 l4_vpattern_matches972 pf f0' m1_p mf3 /\
                 (!x. l4_vpath_valid972 pf x ==> l4_vstred972 env uvars pat g1 (mf3 x) (mf x))) /\
      (?a0' ma3. l4_vwhred_s972 env uvars pat g1 a a0' /\
                 l4_vpattern_matches972 pa a0' ls2 ma3 /\
                 (!x. l4_vpath_valid972 pa x ==> l4_vstred972 env uvars pat g1 (ma3 x) (ma x)))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [USE_THEN "IHf" MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;`f':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vsubpattern_trans972 THEN EXISTS_TAC `L4VPApp972 pf pa` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vsubpattern_appL972 THEN REWRITE_TAC [l4_vsubpattern_refl972];
     USE_THEN "IHa" MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;`a':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vsubpattern_trans972 THEN EXISTS_TAC `L4VPApp972 pf pa` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vsubpattern_appR972 THEN REWRITE_TAC [l4_vsubpattern_refl972]];
    SUBGOAL_THEN `l4_vis_major_premise972 pat f0'` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vis_major_premise972] THEN
     MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;
                           `pf:l4_vpattern972`;`pa:l4_vpattern972`;`m1_p:l4_vlevel961 list`;
                           `mf3:bool list->l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MAP_EVERY EXISTS_TAC [`L4VApp961 f0' a0'`;`l4_vmenv_app972 mf3 ma3`] THEN
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
      EXISTS_TAC `L4VApp961 f a` THEN ASM_REWRITE_TAC [GSYM l4_vwhred_s972] THEN
      REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
      EXISTS_TAC `L4VApp961 f0' a` THEN REWRITE_TAC [GSYM l4_vwhred_s972] THEN
      ASM_MESON_TAC [l4_vwhred_s_app972;l4_vwhred_s_major972];
      MATCH_MP_TAC l4_vpm_app972 THEN EXISTS_TAC `ls2:l4_vlevel961 list` THEN ASM_REWRITE_TAC [];
      LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vpath_valid_clauses972] THEN
      BOOL_CASES_TAC `h:bool` THEN
      ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]]]];
   (* var *)
   X_GEN_TAC `pf:l4_vpattern972` THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vpattern_matches972 (L4VPVar972 pf) e1_p m1_p m2_p` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vpattern_matches_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vpattern972";injectivity "l4_vpattern972"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e_p (L4VApp961 f' a')` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN
     `?f0' mf3. l4_vwhred_s972 env uvars pat g1 f'' f0' /\
                l4_vpattern_matches972 pf f0' m1_p mf3 /\
                (!x. l4_vpath_valid972 pf x ==> l4_vstred972 env uvars pat g1 (mf3 x) (mf x))`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`r:l4_vrhs972`;`ck:l4_vpattern_check972`;`f':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vsubpattern_trans972 THEN EXISTS_TAC `L4VPVar972 pf` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vsubpattern_varL972 THEN REWRITE_TAC [l4_vsubpattern_refl972];
    MAP_EVERY EXISTS_TAC [`L4VApp961 f0' a`;`l4_vmenv_var972 a mf3`] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_trans972 THEN
     EXISTS_TAC `L4VApp961 f'' a` THEN ASM_REWRITE_TAC [GSYM l4_vwhred_s972] THEN
     ASM_MESON_TAC [l4_vwhred_s_app972];
     MATCH_MP_TAC l4_vpm_var972 THEN ASM_REWRITE_TAC [];
     LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972] THEN
     ASM_REWRITE_TAC [] THEN BOOL_CASES_TAC `h:bool` THEN
     ASM_SIMP_TAC [l4_vpath_valid_clauses972;l4_vmenv_clauses972]]]]);;

let l4_vstred_triangle_ind972 = prove
 (`!env uvars pat g2 e1 e2.
   l4_vpar_red_t972 env uvars pat g2 e1 e2 ==>
   (!g0 g1 e ty.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      l4_vhas_type961 env uvars g1 e ty /\
      l4_vstred972 env uvars pat g1 e e1 ==>
      l4_vstred972 env uvars pat g1 e e2)`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MESON_TAC [];
   (* sort *)
   MESON_TAC [];
   (* const *)
   MESON_TAC [];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g2:l4_vexpr961 list`;`f1:l4_vexpr961`;`f2:l4_vexpr961`;
     `a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e (L4VApp961 f1 a1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VApp961 f a) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `af:l4_vexpr961` (X_CHOOSE_THEN `bf:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vstr_app972 THEN MAP_EVERY EXISTS_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   ASM_MESON_TAC [];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g2:l4_vexpr961 list`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
     `body1:l4_vexpr961`;`body2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e (L4VLam961 dom1 body1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VLam961 dom body) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`body:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `bb:l4_vexpr961`)) THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`bb:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vstred_defeq972]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g2:l4_vexpr961 list`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
     `cod1:l4_vexpr961`;`cod2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e (L4VForallE961 dom1 cod1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VForallE961 dom cod) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`cod:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`L4VSort961 v`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vstred_defeq972]];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g2:l4_vexpr961 list`;`dom:l4_vexpr961`;`bd1:l4_vexpr961`;`bd2:l4_vexpr961`;
     `arg1:l4_vexpr961`;`arg2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 e (L4VApp961 (L4VLam961 dom bd1) arg1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vstred972 env uvars pat g1 f (L4VLam961 dom bd1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_vctx_wf966 env uvars g1`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VApp961 f a) ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`a:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `af:l4_vexpr961` (X_CHOOSE_THEN `bf:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 (L4VLam961 dom' body) (L4VForallE961 af bf)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g1:l4_vexpr961 list`;
                  `dom':l4_vexpr961`;`body:l4_vexpr961`;`L4VForallE961 af bf`] l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `ua:l4_vlevel961`) (X_CHOOSE_TAC `bb:l4_vexpr961`)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g1 (L4VForallE961 af bf) (L4VForallE961 dom' bb)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`L4VLam961 dom' body`;`L4VLam961 dom' body`;`L4VLam961 dom' body`] THEN
    ASM_MESON_TAC [l4_vhas_type961;l4_vhas_type_lam972]; ALL_TAC] THEN
   SUBGOAL_THEN `?w1. l4_vis_defeq961 env uvars g1 af dom' (L4VSort961 w1)`
     (X_CHOOSE_TAC `w1:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_forallE_inv972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vstred_whred972 THEN EXISTS_TAC `l4_vinst0961 body a` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
    EXISTS_TAC `L4VApp961 (L4VLam961 dom' body) a` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_trans972 THEN EXISTS_TAC `L4VApp961 f a` THEN
     ASM_MESON_TAC [l4_vwhred_s972;l4_vwhred_s_app972];
     REWRITE_TAC [l4_vwhr_beta972]];
    REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vstred_instN972 THEN
    MAP_EVERY EXISTS_TAC [`g1:l4_vexpr961 list`;`dom':l4_vexpr961`;`CONS (dom':l4_vexpr961) g1`] THEN
    ASM_REWRITE_TAC [l4_vctx_instN_zero966] THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC [];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`af:l4_vexpr961`;`w1:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     FIRST_ASSUM MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`bb:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_ctx_succ966 THEN
     EXISTS_TAC `ua:l4_vlevel961` THEN ASM_MESON_TAC [l4_vstred_defeq972]]];
   (* extra *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g2:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
     `ck:l4_vpattern_check972`;`e1:l4_vexpr961`;`m1:l4_vlevel961 list`;
     `m2:bool list->l4_vexpr961`;`m2':bool list->l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env /\ l4_vctx_wf966 env uvars g1`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972;l4_vis_defeq_ctx_wf972;l4_venv_wf_closed966]; ALL_TAC] THEN
   MP_TAC (SPECL [`p:l4_vpattern972`;`env:l4_venv961`;`uvars:num`;
                  `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                  `g1:l4_vexpr961 list`;`p:l4_vpattern972`;`r:l4_vrhs972`;
                  `ck:l4_vpattern_check972`;`e1:l4_vexpr961`;`m1:l4_vlevel961 list`;
                  `m2:bool list->l4_vexpr961`;`e':l4_vexpr961`]
     l4_vstred_triangle_extra_pullback972) THEN
   ASM_REWRITE_TAC [l4_vsubpattern_refl972] THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961`
     (X_CHOOSE_THEN `m3:bool list->l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 e0 ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_has_type972]; ALL_TAC] THEN
   SUBGOAL_THEN `!x. l4_vpath_valid972 p x ==> ?tx. l4_vhas_type961 env uvars g1 (m3 x) tx`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vpattern_matches_has_type972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vpattern_check_ok972 (l4_vis_defeq_u961 env uvars g1) m1 m3 ck`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vpattern_check_ok_map972 THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`l4_vis_defeq_u961 env uvars g2`;
                          `m1:l4_vlevel961 list`;`m2:bool list->l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [`ra:l4_vrhs972`;`rb:l4_vrhs972`] THEN STRIP_TAC THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN
    SUBGOAL_THEN `?tx. l4_vis_defeq961 env uvars g1
                         (l4_vrhs_apply972 m1 m2 ra) (l4_vrhs_apply972 m1 m2 rb) tx`
      (X_CHOOSE_TAC `tx:l4_vexpr961`) THENL
    [UNDISCH_TAC `l4_vis_defeq_u961 env uvars g2 (l4_vrhs_apply972 m1 m2 ra) (l4_vrhs_apply972 m1 m2 rb)` THEN
     REWRITE_TAC [l4_vis_defeq_u961] THEN DISCH_THEN (X_CHOOSE_TAC `tx:l4_vexpr961`) THEN
     EXISTS_TAC `tx:l4_vexpr961` THEN
     MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
     MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`g2:l4_vexpr961 list`] THEN
     ASM_MESON_TAC [l4_venv_wf_closed966;l4_vis_defeq_ctx_symm966]; ALL_TAC] THEN
    SUBGOAL_THEN `!x b. l4_vpath_valid972 p x /\ l4_vhas_type961 env uvars g1 (m2 x) b ==>
                        l4_vis_defeq_u961 env uvars g1 (m2 x) (m3 x)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vstred_defeq972]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq961 env uvars g1 (l4_vrhs_apply972 m1 m2 ra)
                    (l4_vrhs_apply972 m1 m3 ra) tx /\
                  l4_vis_defeq961 env uvars g1 (l4_vrhs_apply972 m1 m2 rb)
                    (l4_vrhs_apply972 m1 m3 rb) tx` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_apply_pat972 THEN
     EXISTS_TAC `p:l4_vpattern972` THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vis_defeq_refl_r961];
     EXISTS_TAC `tx:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vis_defeq_trans961;l4_vis_defeq_symm961]]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vstred_whred972 THEN EXISTS_TAC `l4_vrhs_apply972 m1 m3 r` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
    EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vwhred_s972] THEN
    MATCH_MP_TAC l4_vwhr_extra972 THEN
    MAP_EVERY EXISTS_TAC [`p:l4_vpattern972`;`ck:l4_vpattern_check972`] THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vstred_apply_pat972 THEN EXISTS_TAC `p:l4_vpattern972` THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC `x:bool list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?tx. l4_vhas_type961 env uvars g1 ((m3:bool list->l4_vexpr961) x) tx` (X_CHOOSE_TAC `tx:l4_vexpr961`) THENL
    [ASM_SIMP_TAC [];
     FIRST_ASSUM (fun th -> MATCH_MP_TAC (SPECL [`g0:l4_vexpr961 list`;`g1:l4_vexpr961 list`;
       `(m3:bool list->l4_vexpr961) x`;`tx:l4_vexpr961`] (MATCH_MP th (ASSUME `l4_vpath_valid972 p x`)))) THEN
     ASM_SIMP_TAC []]]]);;

let l4_vstred_triangle972 = prove
 (`!env uvars pat g0 g1 g2 e e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vhas_type961 env uvars g1 e ty /\
   l4_vstred972 env uvars pat g1 e e1 /\
   l4_vpar_red_t972 env uvars pat g2 e1 e2 ==>
   l4_vstred972 env uvars pat g1 e e2`,
  MESON_TAC [l4_vstred_triangle_ind972]);;

let l4_vstred_triangle_s_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars pat g0 g1 g2 e ty.
      R = l4_vpar_red_t972 env uvars pat g2 /\
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
      l4_vhas_type961 env uvars g1 e ty /\
      l4_vstred972 env uvars pat g1 e e1 ==>
      l4_vstred972 env uvars pat g1 e e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN CONJ_TAC THENL
  [MESON_TAC []; MESON_TAC [l4_vstred_triangle972]]);;

let l4_vstred_triangle_s972 = prove
 (`!env uvars pat g0 g1 g2 e e1 e2 ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vhas_type961 env uvars g1 e ty /\
   l4_vstred972 env uvars pat g1 e e1 /\
   l4_vpar_red_ts972 env uvars pat g2 e1 e2 ==>
   l4_vstred972 env uvars pat g1 e e2`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN MESON_TAC [l4_vstred_triangle_s_ind972]);;

let l4_vpar_red_ts_standard972 = prove
 (`!env uvars pat g e e' ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e ty /\
   l4_vpar_red_ts972 env uvars pat g e e' ==>
   l4_vstred972 env uvars pat g e e'`,
  MESON_TAC [l4_vstred_triangle_s972;l4_vis_defeq_ctx_zero966;l4_vstred_refl972]);;

(* Head Reduction to Sorts and Pi Types *)

let l4_vlevel_not_succ_zero972 = prove
 (`!u. ~l4_vlevel_equiv961 (L4VLSucc961 u) L4VLZero961`,
  REWRITE_TAC [l4_vlevel_equiv961;NOT_FORALL_THM] THEN GEN_TAC THEN
  EXISTS_TAC `[]:num list` THEN
  REWRITE_TAC [l4_vlevel_eval961] THEN ARITH_TAC);;

let l4_vis_defeq_reduce_sort972 = prove
 (`!env uvars pat g e u ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e (L4VSort961 u) ty ==>
   ?u'. l4_vwhred_s972 env uvars pat g e (L4VSort961 u') /\ l4_vlevel_equiv961 u' u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vcr_defeq972 env uvars pat g e (L4VSort961 u)` MP_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_church_rosser972]; ALL_TAC] THEN
  REWRITE_TAC [l4_vcr_defeq972] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e':l4_vexpr961`
        (X_CHOOSE_THEN `s':l4_vexpr961` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `s' = L4VSort961 u` SUBST_ALL_TAC THENL
  [MATCH_MP_TAC l4_vstred_sort_l972 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`g:l4_vexpr961 list`] THEN
   ASM_MESON_TAC [l4_vpar_red_ts_standard972;l4_vis_defeq_refl_r961]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vlevel_wf961 uvars u` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_sort_inv_r972]; ALL_TAC] THEN
  SUBGOAL_THEN `?v. e' = L4VSort961 v /\ l4_vlevel_equiv961 v u`
    (X_CHOOSE_THEN `v:l4_vlevel961` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `l4_vnormal_eq972 env uvars g e' (L4VSort961 u)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [EXISTS_TAC `u:l4_vlevel961` THEN REWRITE_TAC [l4_vlevel_equiv_refl961];
    EXISTS_TAC `l1:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    (* etaL: e' = lam, L4VSort961 u has type forallE -> impossible *)
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VSort961 (L4VLSucc961 u)) (L4VForallE961 dom cod)`
      MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VSort961 u`;`L4VSort961 u`;`L4VSort961 u`] THEN
     ASM_MESON_TAC [l4_vhas_type961;l4_vhas_type_sort972];
     ASM_MESON_TAC [l4_vis_defeq_u_sort_forallE_inv972]];
    (* proofIrrel: L4VSort961 u : p : Sort 0 -> Sort (Succ u) == Sort 0 -> impossible *)
    SUBGOAL_THEN `l4_vhas_type961 env uvars g (L4VSort961 (L4VLSucc961 u)) (L4VSort961 L4VLZero961)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
     MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VSort961 u`;`L4VSort961 u`;`L4VSort961 u`] THEN
     ASM_MESON_TAC [l4_vhas_type961;l4_vhas_type_sort972];
     SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g
                     (L4VSort961 (L4VLSucc961 (L4VLSucc961 u))) (L4VSort961 L4VLZero961)`
       MP_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
      MAP_EVERY EXISTS_TAC [`L4VSort961 (L4VLSucc961 u)`;`L4VSort961 (L4VLSucc961 u)`;
                            `L4VSort961 (L4VLSucc961 u)`] THEN
      ASM_MESON_TAC [l4_vhas_type961;l4_vhas_type_sort972;l4_vlevel_wf961];
      ASM_MESON_TAC [l4_vis_defeq_u_sort_inv972;l4_vlevel_not_succ_zero972]]]];
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_vstred972 env uvars pat g e (L4VSort961 v)` MP_TAC THENL
   [ASM_MESON_TAC [l4_vpar_red_ts_standard972;l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   EXISTS_TAC `v:l4_vlevel961` THEN ASM_REWRITE_TAC []]);;

let l4_vis_defeq_reduce_forallE972 = prove
 (`!env uvars pat g e dom cod ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e (L4VForallE961 dom cod) ty ==>
   ?dom' cod'. l4_vwhred_s972 env uvars pat g e (L4VForallE961 dom' cod')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vcr_defeq972 env uvars pat g e (L4VForallE961 dom cod)` MP_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_church_rosser972]; ALL_TAC] THEN
  REWRITE_TAC [l4_vcr_defeq972] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e':l4_vexpr961`
        (X_CHOOSE_THEN `pi':l4_vexpr961` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `?a1 b1. pi' = L4VForallE961 a1 b1 /\
                        l4_vstred972 env uvars pat g dom a1 /\
                        l4_vstred972 env uvars pat (CONS dom g) cod b1`
    (X_CHOOSE_THEN `a1:l4_vexpr961` (X_CHOOSE_THEN `b1:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
  [MATCH_MP_TAC l4_vstred_forallE_l972 THEN
   ASM_MESON_TAC [l4_vpar_red_ts_standard972;l4_vis_defeq_refl_r961]; ALL_TAC] THEN
  l4_subst_vars_tac972 THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `dom:l4_vexpr961`;`cod:l4_vexpr961`;`ty:l4_vexpr961`] l4_vhas_type_forall_inv972) THEN
  ASM_REWRITE_TAC [l4_vis_type961] THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_refl_r961]; ALL_TAC] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g dom a1 (L4VSort961 u)` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vstred_defeq972]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS a1 g) b1 (L4VSort961 v)` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_defeqDF_l966 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vpar_red_ts_has_type972 THEN
    MAP_EVERY EXISTS_TAC [`pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;`cod:l4_vexpr961`] THEN
    ASM_MESON_TAC [l4_vctx_cons972;l4_vstred_par_red_s972]]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars g (L4VForallE961 a1 b1) (L4VSort961 (L4VLIMax961 u v))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_MESON_TAC [l4_vis_defeq_refl_r961]; ALL_TAC] THEN
  SUBGOAL_THEN `?dom' cod'. e' = L4VForallE961 dom' cod'`
    (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `cod':l4_vexpr961` SUBST_ALL_TAC)) THENL
  [UNDISCH_TAC `l4_vnormal_eq972 env uvars g e' (L4VForallE961 a1 b1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vnormal_eq_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [MAP_EVERY EXISTS_TAC [`a1:l4_vexpr961`;`b1:l4_vexpr961`] THEN REFL_TAC;
    MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`cod1:l4_vexpr961`] THEN REFL_TAC;
    (* etaL: forallE has type forallE -> impossible *)
    SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VSort961 (L4VLIMax961 u v))
                    (L4VForallE961 dom' cod')` MP_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VForallE961 a1 b1`;`L4VForallE961 a1 b1`;`L4VForallE961 a1 b1`] THEN
     ASM_MESON_TAC [l4_vhas_type961];
     ASM_MESON_TAC [l4_vis_defeq_u_sort_forallE_inv972]];
    (* proofIrrel: forallE : p : Sort 0 -> Sort (IMax u v) : Sort 0 -> impossible *)
    SUBGOAL_THEN `l4_vhas_type961 env uvars g (L4VSort961 (L4VLIMax961 u v))
                    (L4VSort961 L4VLZero961)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_defeq_u_l972 THEN EXISTS_TAC `p:l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
     MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VForallE961 a1 b1`;`L4VForallE961 a1 b1`;`L4VForallE961 a1 b1`] THEN
     ASM_MESON_TAC [l4_vhas_type961];
     SUBGOAL_THEN `l4_vlevel_wf961 uvars (L4VLIMax961 u v)` ASSUME_TAC THENL
     [ASM_MESON_TAC [l4_vhas_type961;l4_vis_defeq_sort_inv_l972];
      SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g
                      (L4VSort961 (L4VLSucc961 (L4VLIMax961 u v))) (L4VSort961 L4VLZero961)`
        MP_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
       MAP_EVERY EXISTS_TAC [`L4VSort961 (L4VLIMax961 u v)`;`L4VSort961 (L4VLIMax961 u v)`;
                             `L4VSort961 (L4VLIMax961 u v)`] THEN
       ASM_MESON_TAC [l4_vhas_type961;l4_vhas_type_sort972];
       ASM_MESON_TAC [l4_vis_defeq_u_sort_inv972;l4_vlevel_not_succ_zero972]]]]];
   SUBGOAL_THEN `l4_vstred972 env uvars pat g e (L4VForallE961 dom' cod')` MP_TAC THENL
   [ASM_MESON_TAC [l4_vpar_red_ts_standard972;l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MAP_EVERY EXISTS_TAC [`dom'':l4_vexpr961`;`cod'':l4_vexpr961`] THEN ASM_REWRITE_TAC []]);;

(* Syntax-Directed Type Inference (l4_vinfer_type972 and l4_vinfer_type_s972) *)

let l4_vinfer_type_RULES972,l4_vinfer_type_INDUCT972,l4_vinfer_type_CASES972 =
  new_inductive_definition
 `(!env uvars (pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool) g i ty.
     l4_vlookup961 g i ty ==>
     l4_vinfer_type972 env uvars pat g (L4VBVar961 i) ty) /\
  (!env uvars pat g u.
     l4_vlevel_wf961 uvars u ==>
     l4_vinfer_type972 env uvars pat g (L4VSort961 u) (L4VSort961 (L4VLSucc961 u))) /\
  (!env uvars pat g c ci ls.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vc_uvars961 ci ==>
     l4_vinfer_type972 env uvars pat g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci))) /\
  (!env uvars pat g f fty dom cod a.
     l4_vinfer_type972 env uvars pat g f fty /\
     l4_vwhred_s972 env uvars pat g fty (L4VForallE961 dom cod) /\
     l4_vhas_type961 env uvars g a dom ==>
     l4_vinfer_type972 env uvars pat g (L4VApp961 f a) (l4_vinst0961 cod a)) /\
  (!env uvars pat g dom u body cod.
     l4_vhas_type961 env uvars g dom (L4VSort961 u) /\
     l4_vinfer_type972 env uvars pat (CONS dom g) body cod ==>
     l4_vinfer_type972 env uvars pat g (L4VLam961 dom body) (L4VForallE961 dom cod)) /\
  (!env uvars pat g dom uty u cod vty v.
     l4_vinfer_type972 env uvars pat g dom uty /\
     l4_vwhred_s972 env uvars pat g uty (L4VSort961 u) /\
     l4_vinfer_type972 env uvars pat (CONS dom g) cod vty /\
     l4_vwhred_s972 env uvars pat (CONS dom g) vty (L4VSort961 v) ==>
     l4_vinfer_type972 env uvars pat g (L4VForallE961 dom cod)
       (L4VSort961 (L4VLIMax961 u v)))`;;

let l4_vit_bvar972,
    l4_vit_sort972,
    l4_vit_const972,
    l4_vit_app972,
    l4_vit_lam972,
    l4_vit_forallE972 =
  match CONJUNCTS l4_vinfer_type_RULES972 with
  | [c1;c2;c3;c4;c5;c6] -> (c1,c2,c3,c4,c5,c6)
  | _ -> failwith "l4_vinfer_type_RULES972: unexpected arity";;

let l4_vinfer_type_STRONG_INDUCT972 =
  derive_strong_induction (l4_vinfer_type_RULES972, l4_vinfer_type_INDUCT972);;

let l4_vinfer_type_has_type_ind972 = prove
 (`!env uvars pat g e ty.
   l4_vinfer_type972 env uvars pat g e ty ==>
   (l4_pattern_params_for972 env pat /\ l4_vctx_wf966 env uvars g ==>
    l4_vhas_type961 env uvars g e ty)`,
  MATCH_MP_TAC l4_vinfer_type_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_bvar961];
   (* sort *)
   MESON_TAC [l4_vhas_type_sort972];
   (* const *)
   MESON_TAC [l4_vhas_type_const972];
   (* app *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vhas_type961 env uvars g f fty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `?w. l4_vhas_type961 env uvars g fty (L4VSort961 w)`
     (X_CHOOSE_TAC `w:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`fty:l4_vexpr961`;`w:l4_vlevel961`] THEN
   ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961];
   (* lam *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vhas_type_lam972 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vctx_cons972];
   (* forallE *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vhas_type961 env uvars g dom uty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972]; ALL_TAC] THEN
   SUBGOAL_THEN `?wu. l4_vhas_type961 env uvars g uty (L4VSort961 wu)`
     (X_CHOOSE_TAC `wu:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g dom (L4VSort961 u)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`uty:l4_vexpr961`;`wu:l4_vlevel961`] THEN
    ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_cons972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars (CONS dom g) cod vty` ASSUME_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?wv. l4_vhas_type961 env uvars (CONS dom g) vty (L4VSort961 wv)`
     (X_CHOOSE_TAC `wv:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`vty:l4_vexpr961`;`wv:l4_vlevel961`] THEN
   ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961]]);;

let l4_vinfer_type_has_type972 = prove
 (`!env uvars pat g e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vinfer_type972 env uvars pat g e ty ==>
   l4_vhas_type961 env uvars g e ty`,
  MESON_TAC [l4_vinfer_type_has_type_ind972]);;

let l4_vinfer_type_determ_ind972 = prove
 (`!env uvars pat g e ty1.
   l4_vinfer_type972 env uvars pat g e ty1 ==>
   (!ty2.
      l4_pattern_params_for972 env pat /\
      l4_vinfer_type972 env uvars pat g e ty2 ==>
      ty1 = ty2)`,
  MATCH_MP_TAC l4_vinfer_type_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   ASM_MESON_TAC [l4_vlookup_determ972];
   (* sort *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   MESON_TAC [];
   (* const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   ASM_MESON_TAC [l4_pp_wf972;l4_venv_wf_lookup_unique966];
   (* app *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `fty:l4_vexpr961 = fty'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `L4VForallE961 dom cod = L4VForallE961 dom' cod'` MP_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_determ972;l4_vwhnf_forallE972];
    REWRITE_TAC [injectivity "l4_vexpr961"] THEN STRIP_TAC THEN ASM_REWRITE_TAC []];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   AP_TERM_TAC THEN ASM_MESON_TAC [];
   (* forallE *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ty2:l4_vexpr961` THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vinfer_type_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `uty:l4_vexpr961 = uty'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `L4VSort961 u = L4VSort961 u'` MP_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_determ972;l4_vwhnf_sort972]; ALL_TAC] THEN
   REWRITE_TAC [injectivity "l4_vexpr961"] THEN DISCH_THEN SUBST_ALL_TAC THEN
   SUBGOAL_THEN `vty:l4_vexpr961 = vty'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `L4VSort961 v = L4VSort961 v'` MP_TAC THENL
   [ASM_MESON_TAC [l4_vwhred_s_determ972;l4_vwhnf_sort972];
    REWRITE_TAC [injectivity "l4_vexpr961"] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC]]);;

let l4_vinfer_type_determ972 = prove
 (`!env uvars pat g e ty1 ty2.
   l4_pattern_params_for972 env pat /\
   l4_vinfer_type972 env uvars pat g e ty1 /\
   l4_vinfer_type972 env uvars pat g e ty2 ==>
   ty1 = ty2`,
  MESON_TAC [l4_vinfer_type_determ_ind972]);;

let l4_vinfer_type_weak_prime_ind972 = prove
 (`!env uvars pat g e ty.
   l4_vinfer_type972 env uvars pat g e ty ==>
   (!rho g'.
      l4_venv_wf966 env /\
      l4_vctx_lift_prime969 rho g g' ==>
      l4_vinfer_type972 env uvars pat g' (l4_vlift_prime969 e rho) (l4_vlift_prime969 ty rho))`,
  MATCH_MP_TAC l4_vinfer_type_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_bvar972 THEN ASM_MESON_TAC [l4_vlookup_weak_prime969];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_sort972 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   SUBGOAL_THEN `l4_vlift_prime969 (l4_vinstL961 ls (l4_vc_type961 ci)) rho =
                 l4_vinstL961 ls (l4_vc_type961 ci)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_vclosed_n_vlift_prime_eq969 THEN EXISTS_TAC `0` THEN
    REWRITE_TAC [l4_vlift_op_fixes_clauses969] THEN
    ASM_MESON_TAC [l4_closed_inst_const966;l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vit_const972 THEN ASM_REWRITE_TAC []];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969;l4_vlift_prime_vinst0_hi969] THEN
   MATCH_MP_TAC l4_vit_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_prime969 fty rho`;`l4_vlift_prime969 dom rho`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                   `fty:l4_vexpr961`;`L4VForallE961 dom cod`] l4_vwhred_s_weak_prime972) THEN
    ASM_REWRITE_TAC [l4_vlift_prime969];
    ASM_MESON_TAC [l4_vhas_type_weak_prime969;l4_venv_wf_closed966]];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`rho:l4_vlift_op969`;
                   `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`L4VSort961 u`] l4_vhas_type_weak_prime969) THEN
    ASM_MESON_TAC [l4_venv_wf_closed966;l4_vlift_prime969];
    ASM_MESON_TAC [l4_vctx_lift_prime_cons969]];
   (* forallE *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlift_prime969 uty rho`;
                         `l4_vlift_prime969 vty (L4VLCons969 rho)`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                   `uty:l4_vexpr961`;`L4VSort961 u`] l4_vwhred_s_weak_prime972) THEN
    ASM_REWRITE_TAC [l4_vlift_prime969];
    ASM_MESON_TAC [l4_vctx_lift_prime_cons969];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `L4VLCons969 rho`;`CONS (dom:l4_vexpr961) g`;
                   `CONS (l4_vlift_prime969 dom rho) g'`;
                   `vty:l4_vexpr961`;`L4VSort961 v`] l4_vwhred_s_weak_prime972) THEN
    ASM_SIMP_TAC [l4_vlift_prime969;l4_vctx_lift_prime_cons969]]]);;

let l4_vinfer_type_weak_prime972 = prove
 (`!env uvars pat rho g g' e ty.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vinfer_type972 env uvars pat g e ty ==>
   l4_vinfer_type972 env uvars pat g' (l4_vlift_prime969 e rho) (l4_vlift_prime969 ty rho)`,
  MESON_TAC [l4_vinfer_type_weak_prime_ind972]);;

let l4_vinfer_type_weakN972 = prove
 (`!env uvars pat n k g g' e ty.
   l4_venv_wf966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vinfer_type972 env uvars pat g e ty ==>
   l4_vinfer_type972 env uvars pat g' (l4_vliftN961 e n k) (l4_vliftN961 ty n k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM l4_vlift_prime_cons_n_skip_n969] THEN
  MATCH_MP_TAC l4_vinfer_type_weak_prime972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_REWRITE_TAC [GSYM l4_vctx_liftN_iff_lift_prime969]);;

let l4_vinfer_type_weak_u_inv_ind972 = prove
 (`!env uvars pat g' e' ty'.
   l4_vinfer_type972 env uvars pat g' e' ty' ==>
   (!rho g e.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g' /\
      l4_vctx_lift_prime969 rho g g' /\
      e' = l4_vlift_prime969 e rho ==>
      ?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vinfer_type972 env uvars pat g e ty)`,
  MATCH_MP_TAC l4_vinfer_type_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`i:num`;`ty:l4_vexpr961`] THEN
   DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   MP_TAC (SPECL [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                  `a:num`;`ty:l4_vexpr961`] l4_vlookup_weak_u_inv969) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `ty0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vit_bvar972 THEN ASM_REWRITE_TAC [];
   (* sort *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
   EXISTS_TAC `L4VSort961 (L4VLSucc961 u)` THEN
   ASM_REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_sort972 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   EXISTS_TAC `l4_vinstL961 ls (l4_vc_type961 ci)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC l4_vclosed_n_vlift_prime_eq969 THEN EXISTS_TAC `0` THEN
    REWRITE_TAC [l4_vlift_op_fixes_clauses969] THEN
    ASM_MESON_TAC [l4_closed_inst_const966;l4_pp_wf972;l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vit_const972 THEN ASM_REWRITE_TAC []];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`f':l4_vexpr961`;`fty':l4_vexpr961`;
     `dom':l4_vexpr961`;`cod':l4_vexpr961`;`a':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?fty0. fty' = l4_vlift_prime969 fty0 rho /\ l4_vinfer_type972 env uvars pat g a0 fty0`
     (X_CHOOSE_THEN `fty0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?pi0. L4VForallE961 dom' cod' = l4_vlift_prime969 pi0 rho /\
                       l4_vwhred_s972 env uvars pat g fty0 pi0`
     (X_CHOOSE_THEN `pi0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vwhred_s_weak_u_inv972]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vwhred_s972 env uvars pat g fty0 pi0` THEN
   UNDISCH_TAC `L4VForallE961 dom' cod' = l4_vlift_prime969 pi0 rho` THEN
   STRUCT_CASES_TAC (SPEC `pi0:l4_vexpr961` l4_vexpr_CASES961) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   EXISTS_TAC `l4_vinst0961 a1' a1` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vlift_prime_vinst0_hi969];
    MATCH_MP_TAC l4_vit_app972 THEN
    MAP_EVERY EXISTS_TAC [`fty0:l4_vexpr961`;`a0':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [l4_vhas_type_weak_prime_iff972]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom':l4_vexpr961`;`u:l4_vlevel961`;
     `body':l4_vexpr961`;`cod':l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?cod0. cod' = l4_vlift_prime969 cod0 (L4VLCons969 rho) /\
                        l4_vinfer_type972 env uvars pat (CONS a0 g) a1 cod0`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_vctx_cons972;l4_vctx_lift_prime_cons969];
    EXISTS_TAC `L4VForallE961 a0 cod0` THEN ASM_REWRITE_TAC [l4_vlift_prime969] THEN
    MATCH_MP_TAC l4_vit_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`rho:l4_vlift_op969`;
                   `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                   `a0:l4_vexpr961`;`L4VSort961 u`] l4_vhas_type_weak_prime_iff972) THEN
    ASM_REWRITE_TAC [l4_vlift_prime969]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;
     `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
     `g':l4_vexpr961 list`;`dom':l4_vexpr961`;`uty':l4_vexpr961`;`u:l4_vlevel961`;
     `cod':l4_vexpr961`;`vty':l4_vexpr961`;`v:l4_vlevel961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`rho:l4_vlift_op969`;`g:l4_vexpr961 list`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` l4_vexpr_CASES961) THEN
   REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";
                injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?u0. uty' = l4_vlift_prime969 u0 rho /\ l4_vinfer_type972 env uvars pat g a0 u0`
     (X_CHOOSE_THEN `u0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?s0. L4VSort961 u = l4_vlift_prime969 s0 rho /\
                      l4_vwhred_s972 env uvars pat g u0 s0`
     (X_CHOOSE_THEN `s0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vwhred_s_weak_u_inv972]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vwhred_s972 env uvars pat g u0 s0` THEN
   UNDISCH_TAC `L4VSort961 u = l4_vlift_prime969 s0 rho` THEN
   STRUCT_CASES_TAC (SPEC `s0:l4_vexpr961` l4_vexpr_CASES961) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_wf_weak_prime_inv972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g a0 u0` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vinfer_type_has_type972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g a0 (L4VSort961 u)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?wu. l4_vhas_type961 env uvars g u0 (L4VSort961 wu)`
      (X_CHOOSE_TAC `wu:l4_vlevel961`) THENL
    [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`u0:l4_vexpr961`;`wu:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961]]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS (l4_vlift_prime969 a0 rho) g')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_cons972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`rho:l4_vlift_op969`;
                   `g:l4_vexpr961 list`;`g':l4_vexpr961 list`;
                   `a0:l4_vexpr961`;`L4VSort961 u`] l4_vhas_type_weak_prime969) THEN
    ASM_MESON_TAC [l4_venv_wf_closed966;l4_vlift_prime969]; ALL_TAC] THEN
   SUBGOAL_THEN `?v0. vty' = l4_vlift_prime969 v0 (L4VLCons969 rho) /\
                      l4_vinfer_type972 env uvars pat (CONS a0 g) a1 v0`
     (X_CHOOSE_THEN `v0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vctx_lift_prime_cons969]; ALL_TAC] THEN
   l4_subst_vars_tac972 THEN
   SUBGOAL_THEN `?s1. L4VSort961 v = l4_vlift_prime969 s1 (L4VLCons969 rho) /\
                      l4_vwhred_s972 env uvars pat (CONS a0 g) v0 s1`
     (X_CHOOSE_THEN `s1:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vwhred_s_weak_u_inv972;l4_vctx_lift_prime_cons969]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vwhred_s972 env uvars pat (CONS a0 g) v0 s1` THEN
   UNDISCH_TAC `L4VSort961 v = l4_vlift_prime969 s1 (L4VLCons969 rho)` THEN
   STRUCT_CASES_TAC (SPEC `s1:l4_vexpr961` l4_vexpr_CASES961) THEN
   ASM_REWRITE_TAC [l4_vlift_prime969;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
   EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
   ASM_REWRITE_TAC [l4_vlift_prime969] THEN
   MATCH_MP_TAC l4_vit_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`u0:l4_vexpr961`;`v0:l4_vexpr961`] THEN ASM_REWRITE_TAC []]);;

let l4_vinfer_type_weak_u_inv972 = prove
 (`!env uvars pat rho g g' e ty'.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vinfer_type972 env uvars pat g' (l4_vlift_prime969 e rho) ty' ==>
   ?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vinfer_type972 env uvars pat g e ty`,
  MESON_TAC [l4_vinfer_type_weak_u_inv_ind972]);;

let l4_vinfer_type_weak_prime_inv972 = prove
 (`!env uvars pat rho g g' e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vinfer_type972 env uvars pat g' (l4_vlift_prime969 e rho) (l4_vlift_prime969 ty rho) ==>
   l4_vinfer_type972 env uvars pat g e ty`,
  MESON_TAC [l4_vinfer_type_weak_u_inv972;l4_vlift_prime_inj972]);;

let l4_vinfer_type_instN_bvar972 = prove
 (`!g0 e0 a0 k g1 g.
   l4_vctx_instN966 g0 e0 a0 k g1 g ==>
   (!env uvars pat i ty.
      l4_venv_wf966 env /\
      l4_vinfer_type972 env uvars pat g0 e0 a0 /\
      l4_vlookup961 g1 i ty ==>
      l4_vinfer_type972 env uvars pat g (l4_vinst_var961 i e0 k) (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`] THEN
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vlookup961 (CONS a0 g0) i ty` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list"] THEN STRIP_TAC THEN l4_subst_vars_tac972 THENL
   [ASM_REWRITE_TAC [l4_vinst_var961;LT_REFL;l4_vliftN_zero961;
                     GSYM l4_vinst0961;l4_vinst0_vlift966];
    REWRITE_TAC [l4_vinst_var961;ARITH_RULE `~(SUC i' < 0)`;ARITH_RULE `~(SUC i' = 0)`;
                 ARITH_RULE `SUC i' - 1 = i'`;GSYM l4_vinst0961;l4_vinst0_vlift966] THEN
    MATCH_MP_TAC l4_vit_bvar972 THEN ASM_REWRITE_TAC []];
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                        `k:num`;`g1:l4_vexpr961 list`;`g:l4_vexpr961 list`;
                        `c:l4_vexpr961`] THEN
   DISCH_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vlookup961 (CONS c g1) i ty` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list"] THEN STRIP_TAC THEN l4_subst_vars_tac972 THENL
   [REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;l4_vinst_vlift_succ966] THEN
    ASM_MESON_TAC [l4_vit_bvar972;l4_vlookup_zero961];
    REWRITE_TAC [l4_vinst_var_succ966;l4_vinst_vlift_succ966;l4_vlift961] THEN
    MATCH_MP_TAC l4_vinfer_type_weakN972 THEN EXISTS_TAC `g:l4_vexpr961 list` THEN
    ASM_REWRITE_TAC [l4_vctx_liftN_one966] THEN ASM_MESON_TAC []]]);;

let l4_vinfer_type_instN_ind972 = prove
 (`!env uvars pat g1 e ty.
   l4_vinfer_type972 env uvars pat g1 e ty ==>
   (!g0 e0 a0 k g.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g0 /\
      l4_vctx_wf966 env uvars g1 /\
      l4_vinfer_type972 env uvars pat g0 e0 a0 /\
      l4_vctx_instN966 g0 e0 a0 k g1 g ==>
      l4_vinfer_type972 env uvars pat g (l4_vinst961 e e0 k) (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vinfer_type_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   ASM_MESON_TAC [l4_vinfer_type_instN_bvar972;l4_pp_wf972];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vit_sort972 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_vinst961 (l4_vinstL961 ls (l4_vc_type961 ci)) e0 k =
                 l4_vinstL961 ls (l4_vc_type961 ci)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_vclosedN_vinst_eq966 THEN
    ASM_MESON_TAC [l4_closed_inst_const966;l4_pp_wf972;l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vit_const972 THEN ASM_REWRITE_TAC []];
   (* app *)
   MAP_EVERY X_GEN_TAC
     [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `g1:l4_vexpr961 list`;`f:l4_vexpr961`;`fty:l4_vexpr961`;
      `dom:l4_vexpr961`;`cod:l4_vexpr961`;`a:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;`k:num`;`g:l4_vexpr961 list`] THEN
   STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vhas_type961 env uvars g0 e0 a0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vinfer_type_has_type972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vit_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 fty e0 k`;`l4_vinst961 dom e0 k`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                   `k:num`;`g1:l4_vexpr961 list`;`g:l4_vexpr961 list`;
                   `fty:l4_vexpr961`;`L4VForallE961 dom cod`] l4_vwhred_s_instN972) THEN
    REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_instN966 THEN
    MAP_EVERY EXISTS_TAC [`g0:l4_vexpr961 list`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`] THEN
    ASM_MESON_TAC [l4_venv_wf_closed966;l4_vhas_type961]];
   (* lam *)
   MAP_EVERY X_GEN_TAC
     [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `g1:l4_vexpr961 list`;`dom:l4_vexpr961`;`u:l4_vlevel961`;
      `body:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;`k:num`;`g:l4_vexpr961 list`] THEN
   STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vhas_type961 env uvars g0 e0 a0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vinfer_type_has_type972]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vit_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                   `e0:l4_vexpr961`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`dom:l4_vexpr961`;`L4VSort961 u`;
                   `k:num`;`g:l4_vexpr961 list`] l4_vis_defeq_instN966) THEN
    REWRITE_TAC [l4_vinst961;GSYM l4_vhas_type961] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_venv_wf_closed966];
    ASM_MESON_TAC [l4_vctx_cons972;l4_vctx_instN_succ966]];
   (* forallE *)
   MAP_EVERY X_GEN_TAC
     [`env:l4_venv961`;`uvars:num`;
      `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
      `g1:l4_vexpr961 list`;`dom:l4_vexpr961`;`uty:l4_vexpr961`;
      `u:l4_vlevel961`;`cod:l4_vexpr961`;`vty:l4_vexpr961`;`v:l4_vlevel961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;`k:num`;`g:l4_vexpr961 list`] THEN
   STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_vhas_type961 env uvars g0 e0 a0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_vinfer_type_has_type972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 dom uty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vinfer_type_has_type972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g1 dom (L4VSort961 u)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?wu. l4_vhas_type961 env uvars g1 uty (L4VSort961 wu)`
      (X_CHOOSE_TAC `wu:l4_vlevel961`) THENL
    [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`uty:l4_vexpr961`;`wu:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961]]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vit_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 uty e0 k`;`l4_vinst961 vty e0 (SUC k)`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                   `k:num`;`g1:l4_vexpr961 list`;`g:l4_vexpr961 list`;
                   `uty:l4_vexpr961`;`L4VSort961 u`] l4_vwhred_s_instN972) THEN
    REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_vctx_cons972;l4_vctx_instN_succ966];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                   `pat:l4_vpattern972->l4_vrhs972#l4_vpattern_check972->bool`;
                   `g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                   `SUC k`;`CONS (dom:l4_vexpr961) g1`;`CONS (l4_vinst961 dom e0 k) g`;
                   `vty:l4_vexpr961`;`L4VSort961 v`] l4_vwhred_s_instN972) THEN
    REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_vctx_instN_succ966]]]);;

let l4_vinfer_type_instN972 = prove
 (`!env uvars pat g0 e0 a0 k g1 g e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_wf966 env uvars g1 /\
   l4_vinfer_type972 env uvars pat g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vinfer_type972 env uvars pat g1 e ty ==>
   l4_vinfer_type972 env uvars pat g (l4_vinst961 e e0 k) (l4_vinst961 ty e0 k)`,
  MESON_TAC [l4_vinfer_type_instN_ind972]);;

let l4_vinfer_type_inst972 = prove
 (`!env uvars pat g a a0 e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vinfer_type972 env uvars pat g a a0 /\
   l4_vinfer_type972 env uvars pat (CONS a0 g) e ty ==>
   l4_vinfer_type972 env uvars pat g (l4_vinst0961 e a) (l4_vinst0961 ty a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  SUBGOAL_THEN `?u. l4_vhas_type961 env uvars g a0 (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_pp_wf972;
                  l4_vinfer_type_has_type972;l4_vhas_type961];
   MATCH_MP_TAC l4_vinfer_type_instN972 THEN
   MAP_EVERY EXISTS_TAC [`g:l4_vexpr961 list`;`a0:l4_vexpr961`;`CONS (a0:l4_vexpr961) g`] THEN
   ASM_MESON_TAC [l4_vctx_cons972;l4_vctx_instN_zero966]]);;

let l4_vinfer_type_exists_ind972 = prove
 (`!env uvars g a ty b.
   l4_vhas_type_strong970 env uvars g a ty b ==>
   (!pat.
      l4_pattern_params_for972 env pat /\
      l4_vctx_wf966 env uvars g ==>
      ?ty'. l4_vinfer_type972 env uvars pat g a ty')`,
  MATCH_MP_TAC l4_vhas_type_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   MESON_TAC [l4_vit_bvar972];
   (* sort *)
   MESON_TAC [l4_vit_sort972];
   (* const *)
   MESON_TAC [l4_vit_const972];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `?fty. l4_vinfer_type972 env uvars pat g f fty`
     (X_CHOOSE_TAC `fty:l4_vexpr961`) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?w. l4_vis_defeq961 env uvars g fty (L4VForallE961 dom cod) (L4VSort961 w)`
     (X_CHOOSE_TAC `w:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_uniq_same972;l4_vinfer_type_has_type972;
                   l4_vhas_type_strong_has_type970;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `?dom' cod'. l4_vwhred_s972 env uvars pat g fty (L4VForallE961 dom' cod')`
     (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `cod':l4_vexpr961` ASSUME_TAC)) THENL
   [ASM_MESON_TAC [l4_vis_defeq_reduce_forallE972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 env uvars g (L4VForallE961 dom' cod') (L4VForallE961 dom cod)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 w` THEN
    MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `fty:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vwhred_s_defeq972;l4_vis_defeq_refl_l961]; ALL_TAC] THEN
   SUBGOAL_THEN `?w1. l4_vis_defeq961 env uvars g dom' dom (L4VSort961 w1)`
     (X_CHOOSE_TAC `w1:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_forallE_inv972]; ALL_TAC] THEN
   EXISTS_TAC `l4_vinst0961 cod' a` THEN MATCH_MP_TAC l4_vit_app972 THEN
   MAP_EVERY EXISTS_TAC [`fty:l4_vexpr961`;`dom':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`w1:l4_vlevel961`] THEN
   ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vhas_type_strong_has_type970;l4_vhas_type961];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `body:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g dom (L4VSort961 u)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vhas_type_strong_has_type970]; ALL_TAC] THEN
   SUBGOAL_THEN `?cod'. l4_vinfer_type972 env uvars pat (CONS dom g) body cod'`
     (X_CHOOSE_TAC `cod':l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vctx_cons972];
    EXISTS_TAC `L4VForallE961 dom cod'` THEN MATCH_MP_TAC l4_vit_lam972 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
   (* forall *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env /\ l4_defeq_injectivity972 env` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_pp_wf972;l4_pp_inj972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 env uvars g dom (L4VSort961 u)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vhas_type_strong_has_type970]; ALL_TAC] THEN
   SUBGOAL_THEN `?uty. l4_vinfer_type972 env uvars pat g dom uty`
     (X_CHOOSE_TAC `uty:l4_vexpr961`) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?wu. l4_vis_defeq961 env uvars g uty (L4VSort961 u) (L4VSort961 wu)`
     (X_CHOOSE_TAC `wu:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_uniq_same972;l4_vinfer_type_has_type972;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `?u'. l4_vwhred_s972 env uvars pat g uty (L4VSort961 u') /\ l4_vlevel_equiv961 u' u`
     (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vis_defeq_reduce_sort972]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 env uvars (CONS dom g)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_cons972]; ALL_TAC] THEN
   SUBGOAL_THEN `?vty. l4_vinfer_type972 env uvars pat (CONS dom g) cod vty`
     (X_CHOOSE_TAC `vty:l4_vexpr961`) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?wv. l4_vis_defeq961 env uvars (CONS dom g) vty (L4VSort961 v) (L4VSort961 wv)`
     (X_CHOOSE_TAC `wv:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_uniq_same972;l4_vinfer_type_has_type972;
                   l4_vhas_type_strong_has_type970;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `?v'. l4_vwhred_s972 env uvars pat (CONS dom g) vty (L4VSort961 v') /\
                      l4_vlevel_equiv961 v' v`
     (X_CHOOSE_THEN `v':l4_vlevel961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vis_defeq_reduce_sort972]; ALL_TAC] THEN
   EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v')` THEN MATCH_MP_TAC l4_vit_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`uty:l4_vexpr961`;`vty:l4_vexpr961`] THEN ASM_REWRITE_TAC [];
   (* base *)
   MESON_TAC [];
   (* defeq *)
   MESON_TAC []]);;

let l4_vinfer_type_exists972 = prove
 (`!env uvars pat g a ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g a ty ==>
   ?ty'. l4_vinfer_type972 env uvars pat g a ty'`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vinfer_type_exists_ind972;l4_pp_wf972;
             l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_has_type'970]);;

(* InferTypeS: Type inference followed by weak head reduction *)

let l4_vinfer_type_s972 = new_definition
 `l4_vinfer_type_s972 env uvars pat g e ty <=>
   ?ty'. l4_vinfer_type972 env uvars pat g e ty' /\
         l4_vwhred_s972 env uvars pat g ty' ty`;;

let l4_vinfer_type_s_has_type972 = prove
 (`!env uvars pat g e ty.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g /\
   l4_vinfer_type_s972 env uvars pat g e ty ==>
   l4_vhas_type961 env uvars g e ty`,
  REWRITE_TAC [l4_vinfer_type_s972] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vhas_type961 env uvars g e ty'` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vinfer_type_has_type972]; ALL_TAC] THEN
  SUBGOAL_THEN `?u. l4_vhas_type961 env uvars g ty' (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type966;l4_vis_type961;l4_pp_wf972;l4_vhas_type961];
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_MESON_TAC [l4_vwhred_s_defeq972;l4_vhas_type961]]);;

let l4_vwhred_s_infer_type972 = prove
 (`!env uvars pat g e e1 e2.
   l4_pattern_params_for972 env pat /\
   l4_vwhred_s972 env uvars pat g e e1 /\
   l4_vwhnf972 env uvars pat g e1 /\
   l4_vwhred_s972 env uvars pat g e e2 /\
   l4_vwhnf972 env uvars pat g e2 ==>
   e1 = e2`,
  REWRITE_TAC [l4_vwhred_s_determ972]);;

let l4_vinfer_type_s_determ972 = prove
 (`!env uvars pat g e ty1 ty2.
   l4_pattern_params_for972 env pat /\
   l4_vinfer_type_s972 env uvars pat g e ty1 /\
   l4_vwhnf972 env uvars pat g ty1 /\
   l4_vinfer_type_s972 env uvars pat g e ty2 /\
   l4_vwhnf972 env uvars pat g ty2 ==>
   ty1 = ty2`,
  REWRITE_TAC [l4_vinfer_type_s972] THEN
  MESON_TAC [l4_vinfer_type_determ972;l4_vwhred_s_determ972]);;

let l4_vinfer_type_s_weak_prime972 = prove
 (`!env uvars pat rho g g' e ty.
   l4_venv_wf966 env /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vinfer_type_s972 env uvars pat g e ty ==>
   l4_vinfer_type_s972 env uvars pat g' (l4_vlift_prime969 e rho) (l4_vlift_prime969 ty rho)`,
  REWRITE_TAC [l4_vinfer_type_s972] THEN
  MESON_TAC [l4_vinfer_type_weak_prime972;l4_vwhred_s_weak_prime972]);;

let l4_vinfer_type_s_weak_u_inv972 = prove
 (`!env uvars pat rho g g' e ty'.
   l4_pattern_params_for972 env pat /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_lift_prime969 rho g g' /\
   l4_vinfer_type_s972 env uvars pat g' (l4_vlift_prime969 e rho) ty' ==>
   ?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vinfer_type_s972 env uvars pat g e ty`,
  REWRITE_TAC [l4_vinfer_type_s972] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?ty0. ty'' = l4_vlift_prime969 ty0 rho /\ l4_vinfer_type972 env uvars pat g e ty0`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_vinfer_type_weak_u_inv972]; ALL_TAC] THEN
  SUBGOAL_THEN `?ty. ty' = l4_vlift_prime969 ty rho /\ l4_vwhred_s972 env uvars pat g ty0 ty`
    (X_CHOOSE_THEN `ty:l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_vwhred_s_weak_u_inv972;l4_pp_wf972;l4_pp_inj972];
   EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `ty0:l4_vexpr961` THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 5. Unconditional Non-Vacuity on Empty / Extra-Free Environments           *)
(* ========================================================================= *)

let l4_vpat_empty972 = new_definition
 `l4_vpat_empty972 (p:l4_vpattern972) (rck:l4_vrhs972#l4_vpattern_check972) <=> F`;;

let l4_pattern_params_for_of_no_defeqs972 = prove
 (`!env.
   l4_venv_wf966 env /\
   (!df. ~l4_venv_has_defeq961 env df) /\
   l4_defeq_injectivity972 env ==>
   l4_pattern_params_for972 env l4_vpat_empty972`,
  REWRITE_TAC [l4_pattern_params_for972;l4_vpat_empty972] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []);;

let l4_pattern_params_of_no_defeqs972 = prove
 (`!env.
   l4_venv_wf966 env /\
   (!df. ~l4_venv_has_defeq961 env df) /\
   l4_defeq_injectivity972 env ==>
   l4_pattern_params972 env`,
  REWRITE_TAC [l4_pattern_params972] THEN
  MESON_TAC [l4_pattern_params_for_of_no_defeqs972]);;

let l4_pattern_params_for_empty972 = prove
 (`l4_defeq_injectivity972 l4_venv_empty961 ==>
   l4_pattern_params_for972 l4_venv_empty961 l4_vpat_empty972`,
  DISCH_TAC THEN MATCH_MP_TAC l4_pattern_params_for_of_no_defeqs972 THEN
  ASM_REWRITE_TAC [l4_venv_empty_wf966;l4_venv_empty961;l4_venv_has_defeq961;
                   l4_venv_defeqs_list961;MEM]);;

let l4_pattern_params_empty972 = prove
 (`l4_defeq_injectivity972 l4_venv_empty961 ==>
   l4_pattern_params972 l4_venv_empty961`,
  REWRITE_TAC [l4_pattern_params972] THEN MESON_TAC [l4_pattern_params_for_empty972]);;

(* Unconditional Equivalence with Pure-Beta Parallel Reduction *)

let l4_vpar_red_t_vpat_empty_fwd_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vpar_red_t972 env uvars pat g e1 e2 ==>
   (pat = l4_vpat_empty972 ==> l4_vpar_red961 e1 e2)`,
  MATCH_MP_TAC l4_vpar_red_t_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vpat_empty972]) THEN
  ASM_MESON_TAC [l4_vpar_red_bvar968;l4_vpar_red_sort968;l4_vpar_red_const968;
                 l4_vpar_red_app968;l4_vpar_red_lam968;l4_vpar_red_forall968;
                 l4_vpar_red_beta968]);;

let l4_vpar_red_t_vpat_empty_bwd_ind972 = prove
 (`!e1 e2.
   l4_vpar_red961 e1 e2 ==>
   (!env uvars g. l4_vpar_red_t972 env uvars l4_vpat_empty972 g e1 e2)`,
  MATCH_MP_TAC l4_vpar_red_INDUCT961 THEN
  MESON_TAC [l4_vprt_bvar972;l4_vprt_sort972;l4_vprt_const972;
             l4_vprt_app972;l4_vprt_lam972;l4_vprt_forallE972;l4_vprt_beta972]);;

let l4_vpar_red_t_vpat_empty_iff972 = prove
 (`!env uvars g e1 e2.
   l4_vpar_red_t972 env uvars l4_vpat_empty972 g e1 e2 <=> l4_vpar_red961 e1 e2`,
  MESON_TAC [l4_vpar_red_t_vpat_empty_fwd_ind972;l4_vpar_red_t_vpat_empty_bwd_ind972]);;

let l4_vpar_red_ts_vpat_empty_fwd_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars g. R = l4_vpar_red_t972 env uvars l4_vpat_empty972 g ==>
                  l4_vpar_red_star961 e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN
  MESON_TAC [l4_vpar_red_star_refl961;l4_vpar_red_star_trans961;
             l4_vpar_red_star_single961;l4_vpar_red_t_vpat_empty_iff972]);;

let l4_vpar_red_ts_vpat_empty_bwd_ind972 = prove
 (`!e1 e2.
   l4_vpar_red_star961 e1 e2 ==>
   (!env uvars g. l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e1 e2)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_head972;l4_vpar_red_t_vpat_empty_iff972]);;

let l4_vpar_red_ts_vpat_empty_iff972 = prove
 (`!env uvars g e1 e2.
   l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e1 e2 <=> l4_vpar_red_star961 e1 e2`,
  REWRITE_TAC [l4_vpar_red_ts972] THEN
  MESON_TAC [l4_vpar_red_ts_vpat_empty_fwd_ind972;
             l4_vpar_red_ts_vpat_empty_bwd_ind972;l4_vpar_red_ts972]);;

let l4_vpar_red_t_vpat_empty_diamond972 = prove
 (`!env uvars g e e1 e2.
   l4_vpar_red_t972 env uvars l4_vpat_empty972 g e e1 /\
   l4_vpar_red_t972 env uvars l4_vpat_empty972 g e e2 ==>
   ?e3. l4_vpar_red_t972 env uvars l4_vpat_empty972 g e1 e3 /\
        l4_vpar_red_t972 env uvars l4_vpat_empty972 g e2 e3`,
  REWRITE_TAC [l4_vpar_red_t_vpat_empty_iff972;l4_vpar_red_diamond968]);;

let l4_vpar_red_ts_vpat_empty_church_rosser972 = prove
 (`!env uvars g e e1 e2.
   l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e e1 /\
   l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e e2 ==>
   ?e3. l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e1 e3 /\
        l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e2 e3`,
  REWRITE_TAC [l4_vpar_red_ts_vpat_empty_iff972;l4_vpar_red_star_church_rosser968]);;

let l4_vpar_red_ts_empty_uncond_church_rosser972 = prove
 (`!uvars g e e1 e2.
   l4_vpar_red_ts972 l4_venv_empty961 uvars l4_vpat_empty972 g e e1 /\
   l4_vpar_red_ts972 l4_venv_empty961 uvars l4_vpat_empty972 g e e2 ==>
   ?e3. l4_vpar_red_ts972 l4_venv_empty961 uvars l4_vpat_empty972 g e1 e3 /\
        l4_vpar_red_ts972 l4_venv_empty961 uvars l4_vpat_empty972 g e2 e3`,
  REWRITE_TAC [l4_vpar_red_ts_vpat_empty_church_rosser972]);;

(* Unconditional Weak Head Reduction Determinism & Concrete Inhabited Witness *)

let l4_vis_major_premise_vpat_empty972 = prove
 (`!e. ~l4_vis_major_premise972 l4_vpat_empty972 e`,
  REWRITE_TAC [l4_vis_major_premise972;l4_vpat_empty972]);;

let l4_vwhred_vpat_empty_determ_ind972 = prove
 (`!env uvars pat g e e1.
   l4_vwhred972 env uvars pat g e e1 ==>
   (!e2. pat = l4_vpat_empty972 /\ l4_vwhred972 env uvars pat g e e2 ==> e1 = e2)`,
  MATCH_MP_TAC l4_vwhred_STRONG_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* app *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vwhred972 env uvars l4_vpat_empty972 g (L4VApp961 f a) e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961";
                l4_vpat_empty972;l4_vis_major_premise_vpat_empty972] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [];
    ASM_MESON_TAC [l4_vwhnf_lam972;l4_vwhnf972]];
   (* major *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   ASM_MESON_TAC [l4_vis_major_premise_vpat_empty972];
   (* beta *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vwhred972 env uvars l4_vpat_empty972 g (L4VApp961 (L4VLam961 dom e) a) e2` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vwhred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961";
                l4_vpat_empty972;l4_vis_major_premise_vpat_empty972] THEN
   DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN l4_subst_vars_tac972 THEN
   ASM_MESON_TAC [l4_vwhnf_lam972;l4_vwhnf972];
   (* extra *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpat_empty972]) THEN ASM_MESON_TAC []]);;

let l4_vwhred_vpat_empty_determ972 = prove
 (`!env uvars g e e1 e2.
   l4_vwhred972 env uvars l4_vpat_empty972 g e e1 /\
   l4_vwhred972 env uvars l4_vpat_empty972 g e e2 ==>
   e1 = e2`,
  MESON_TAC [l4_vwhred_vpat_empty_determ_ind972]);;

let l4_vwhred_s_vpat_empty_determ972 = prove
 (`!env uvars g e e1 e2.
   l4_vwhred_s972 env uvars l4_vpat_empty972 g e e1 /\
   l4_vwhnf972 env uvars l4_vpat_empty972 g e1 /\
   l4_vwhred_s972 env uvars l4_vpat_empty972 g e e2 /\
   l4_vwhnf972 env uvars l4_vpat_empty972 g e2 ==>
   e1 = e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MP_TAC (ISPECL [`l4_vwhred972 env uvars l4_vpat_empty972 g`;
                  `(\x z. l4_vwhnf972 env uvars l4_vpat_empty972 g z ==>
                          !e2. l4_vwhred_s972 env uvars l4_vpat_empty972 g x e2 /\
                               l4_vwhnf972 env uvars l4_vpat_empty972 g e2 ==> z = e2)`]
    l4_vrtc_head_ind972) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MESON_TAC [l4_vwhnf_whred_s972];
    MAP_EVERY X_GEN_TAC [`x:l4_vexpr961`;`y:l4_vexpr961`;`z:l4_vexpr961`] THEN
    STRIP_TAC THEN DISCH_TAC THEN X_GEN_TAC `w:l4_vexpr961` THEN
    REWRITE_TAC [l4_vwhred_s972] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP l4_vrtc_to_hd_ind972) ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vrtc_hd_CASES972] THEN
    DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
    [l4_subst_vars_tac972 THEN ASM_MESON_TAC [l4_vwhnf972];
     SUBGOAL_THEN `y:l4_vexpr961 = y'` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [l4_vwhred_vpat_empty_determ972];
      ASM_MESON_TAC [l4_vrtc_of_hd_ind972;l4_vwhred_s972]]]];
   REWRITE_TAC [l4_vwhred_s972] THEN MESON_TAC []]);;

let l4_vwhred_empty_determ972 = prove
 (`!uvars g e e1 e2.
   l4_vwhred972 l4_venv_empty961 uvars l4_vpat_empty972 g e e1 /\
   l4_vwhred972 l4_venv_empty961 uvars l4_vpat_empty972 g e e2 ==>
   e1 = e2`,
  REWRITE_TAC [l4_vwhred_vpat_empty_determ972]);;

let l4_vwhred_s_empty_determ972 = prove
 (`!uvars g e e1 e2.
   l4_vwhred_s972 l4_venv_empty961 uvars l4_vpat_empty972 g e e1 /\
   l4_vwhnf972 l4_venv_empty961 uvars l4_vpat_empty972 g e1 /\
   l4_vwhred_s972 l4_venv_empty961 uvars l4_vpat_empty972 g e e2 /\
   l4_vwhnf972 l4_venv_empty961 uvars l4_vpat_empty972 g e2 ==>
   e1 = e2`,
  REWRITE_TAC [l4_vwhred_s_vpat_empty_determ972]);;

let l4_vwhred_s_empty_id_sort_witness972 = prove
 (`l4_vwhred_s972 l4_venv_empty961 0 l4_vpat_empty972 []
     (L4VApp961 (L4VLam961 (L4VSort961 (L4VLSucc961 L4VLZero961)) (L4VBVar961 0))
                (L4VSort961 L4VLZero961))
     (L4VSort961 L4VLZero961) /\
   l4_vwhnf972 l4_venv_empty961 0 l4_vpat_empty972 [] (L4VSort961 L4VLZero961)`,
  REWRITE_TAC [l4_vwhnf_sort972;l4_vwhred_s972] THEN
  MATCH_MP_TAC l4_vrtc_single972 THEN
  MP_TAC (SPECL [`l4_venv_empty961`;`0`;`l4_vpat_empty972`;`[]:l4_vexpr961 list`;
                 `L4VSort961 (L4VLSucc961 L4VLZero961)`;`L4VBVar961 0`;
                 `L4VSort961 L4VLZero961`] l4_vwhr_beta972) THEN
  REWRITE_TAC [l4_vinst0961;l4_vinst961;l4_vinst_var961;LT_REFL;l4_vliftN_zero961]);;

(* Unconditional Kashima Standardization on Pure Beta / l4_vpat_empty972 *)

let l4_vwhred_vpat_empty_ctx_irrel_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vwhred972 env uvars pat g1 e1 e2 ==>
   (!env' uvars' g2. pat = l4_vpat_empty972 ==>
                     l4_vwhred972 env' uvars' l4_vpat_empty972 g2 e1 e2)`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vpat_empty972;l4_vis_major_premise_vpat_empty972]) THEN
  ASM_MESON_TAC [l4_vwhr_app972;l4_vwhr_beta972]);;

let l4_vwhred_vpat_empty_ctx_irrel972 = prove
 (`!env uvars g1 env' uvars' g2 e1 e2.
   l4_vwhred972 env uvars l4_vpat_empty972 g1 e1 e2 ==>
   l4_vwhred972 env' uvars' l4_vpat_empty972 g2 e1 e2`,
  MESON_TAC [l4_vwhred_vpat_empty_ctx_irrel_ind972]);;

let l4_vwhred_s_vpat_empty_ctx_irrel_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars g1 env' uvars' g2.
      R = l4_vwhred972 env uvars l4_vpat_empty972 g1 ==>
      l4_vwhred_s972 env' uvars' l4_vpat_empty972 g2 e1 e2)`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_vpat_empty_ctx_irrel972]);;

let l4_vwhred_s_vpat_empty_ctx_irrel972 = prove
 (`!env uvars g1 env' uvars' g2 e1 e2.
   l4_vwhred_s972 env uvars l4_vpat_empty972 g1 e1 e2 ==>
   l4_vwhred_s972 env' uvars' l4_vpat_empty972 g2 e1 e2`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_vpat_empty_ctx_irrel_ind972;l4_vwhred_s972]);;

let l4_vstred_vpat_empty_ctx_irrel_ind972 = prove
 (`!env uvars pat g1 e1 e2.
   l4_vstred972 env uvars pat g1 e1 e2 ==>
   (!env' uvars' g2. pat = l4_vpat_empty972 ==>
                     l4_vstred972 env' uvars' l4_vpat_empty972 g2 e1 e2)`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
  ASM_MESON_TAC [l4_vstr_bvar972;l4_vstr_sort972;l4_vstr_const972;
                 l4_vstr_app972;l4_vstr_lam972;l4_vstr_forallE972;
                 l4_vwhred_s_vpat_empty_ctx_irrel972]);;

let l4_vstred_vpat_empty_ctx_irrel972 = prove
 (`!env uvars g1 env' uvars' g2 e1 e2.
   l4_vstred972 env uvars l4_vpat_empty972 g1 e1 e2 ==>
   l4_vstred972 env' uvars' l4_vpat_empty972 g2 e1 e2`,
  MESON_TAC [l4_vstred_vpat_empty_ctx_irrel_ind972]);;

let l4_vwhred_vpat_empty_weakN_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vwhred972 env uvars pat g e1 e2 ==>
   (!n k. pat = l4_vpat_empty972 ==>
          l4_vwhred972 env uvars l4_vpat_empty972 g (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
  REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vpat_empty972;l4_vis_major_premise_vpat_empty972]) THEN
  ASM_MESON_TAC [l4_vwhr_app972;l4_vwhr_beta972]);;

let l4_vwhred_vpat_empty_weakN972 = prove
 (`!env uvars g n k e1 e2.
   l4_vwhred972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vwhred972 env uvars l4_vpat_empty972 g (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_vwhred_vpat_empty_weakN_ind972]);;

let l4_vwhred_s_vpat_empty_weakN_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars g n k.
      R = l4_vwhred972 env uvars l4_vpat_empty972 g ==>
      l4_vwhred_s972 env uvars l4_vpat_empty972 g (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_vpat_empty_weakN972]);;

let l4_vwhred_s_vpat_empty_weakN972 = prove
 (`!env uvars g n k e1 e2.
   l4_vwhred_s972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vwhred_s972 env uvars l4_vpat_empty972 g (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_vpat_empty_weakN_ind972;l4_vwhred_s972]);;

let l4_vstred_vpat_empty_weakN_ind972 = prove
 (`!env uvars pat g0 e1 e2.
   l4_vstred972 env uvars pat g0 e1 e2 ==>
   (!g' n k. pat = l4_vpat_empty972 ==>
             l4_vstred972 env uvars l4_vpat_empty972 g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vliftN961] THENL
  [MATCH_MP_TAC l4_vstr_bvar972 THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961];
   MATCH_MP_TAC l4_vstr_sort972 THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961];
   MATCH_MP_TAC l4_vstr_const972 THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961];
   MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 f n k`;`l4_vliftN961 a n k`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961];
   MATCH_MP_TAC l4_vstr_lam972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 dom n k`;`l4_vliftN961 body n (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961];
   MATCH_MP_TAC l4_vstr_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 dom n k`;`l4_vliftN961 cod n (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_weakN972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vliftN961]]);;

let l4_vstred_vpat_empty_weakN972 = prove
 (`!env uvars g n k e1 e2.
   l4_vstred972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vstred972 env uvars l4_vpat_empty972 g (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_vstred_vpat_empty_weakN_ind972]);;

let l4_vwhred_vpat_empty_inst_ind972 = prove
 (`!env uvars pat g e1 e2.
   l4_vwhred972 env uvars pat g e1 e2 ==>
   (!a k. pat = l4_vpat_empty972 ==>
          l4_vwhred972 env uvars l4_vpat_empty972 g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k))`,
  MATCH_MP_TAC l4_vwhred_INDUCT972 THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN
  REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vpat_empty972;l4_vis_major_premise_vpat_empty972]) THEN
  ASM_MESON_TAC [l4_vwhr_app972;l4_vwhr_beta972]);;

let l4_vwhred_vpat_empty_inst972 = prove
 (`!env uvars g a k e1 e2.
   l4_vwhred972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vwhred972 env uvars l4_vpat_empty972 g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k)`,
  MESON_TAC [l4_vwhred_vpat_empty_inst_ind972]);;

let l4_vwhred_s_vpat_empty_inst_ind972 = prove
 (`!R e1 e2.
   l4_vrt_closure972 R e1 e2 ==>
   (!env uvars g a k.
      R = l4_vwhred972 env uvars l4_vpat_empty972 g ==>
      l4_vwhred_s972 env uvars l4_vpat_empty972 g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k))`,
  MATCH_MP_TAC l4_vrt_closure_INDUCT972 THEN REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vrtc_rfl972;l4_vrtc_tail972;l4_vwhred_vpat_empty_inst972]);;

let l4_vwhred_s_vpat_empty_inst972 = prove
 (`!env uvars g a k e1 e2.
   l4_vwhred_s972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vwhred_s972 env uvars l4_vpat_empty972 g (l4_vinst961 e1 a k) (l4_vinst961 e2 a k)`,
  REWRITE_TAC [l4_vwhred_s972] THEN
  MESON_TAC [l4_vwhred_s_vpat_empty_inst_ind972;l4_vwhred_s972]);;

let l4_vstred_vpat_empty_inst_ind972 = prove
 (`!env uvars pat g0 e1 e2.
   l4_vstred972 env uvars pat g0 e1 e2 ==>
   (!g' a1 a2 k.
      pat = l4_vpat_empty972 /\
      l4_vstred972 env uvars l4_vpat_empty972 g' a1 a2 ==>
      l4_vstred972 env uvars l4_vpat_empty972 g' (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k))`,
  MATCH_MP_TAC l4_vstred_INDUCT972 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstred_whred972 THEN EXISTS_TAC `l4_vinst_var961 i a1 k` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                   `a1:l4_vexpr961`;`k:num`;`e:l4_vexpr961`;`L4VBVar961 i`]
      l4_vwhred_s_vpat_empty_inst972) THEN
    REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_vwhred_s_vpat_empty_ctx_irrel972];
    REWRITE_TAC [l4_vinst_var961] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_vstred_refl972] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_vstred_refl972] THEN
    ASM_MESON_TAC [l4_vstred_vpat_empty_weakN972]];
   (* sort *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_sort972 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `a1:l4_vexpr961`;`k:num`;`e:l4_vexpr961`;`L4VSort961 u`]
     l4_vwhred_s_vpat_empty_inst972) THEN
   REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_ctx_irrel972];
   (* const *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_const972 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                  `a1:l4_vexpr961`;`k:num`;`e:l4_vexpr961`;`L4VConst961 c ls`]
     l4_vwhred_s_vpat_empty_inst972) THEN
   REWRITE_TAC [l4_vinst961] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_ctx_irrel972];
   (* app *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_app972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 f a1 k`;`l4_vinst961 a a1 k`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_inst972;l4_vwhred_s_vpat_empty_ctx_irrel972;l4_vinst961];
   (* lam *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom a1 k`;`l4_vinst961 body a1 (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_inst972;l4_vwhred_s_vpat_empty_ctx_irrel972;
                  l4_vstred_vpat_empty_ctx_irrel972;l4_vinst961];
   (* forallE *)
   REPEAT STRIP_TAC THEN l4_subst_vars_tac972 THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 dom a1 k`;`l4_vinst961 cod a1 (SUC k)`] THEN
   ASM_MESON_TAC [l4_vwhred_s_vpat_empty_inst972;l4_vwhred_s_vpat_empty_ctx_irrel972;
                  l4_vstred_vpat_empty_ctx_irrel972;l4_vinst961]]);;

let l4_vstred_vpat_empty_inst972 = prove
 (`!env uvars g a1 a2 e1 e2 k.
   l4_vstred972 env uvars l4_vpat_empty972 g a1 a2 /\
   l4_vstred972 env uvars l4_vpat_empty972 g e1 e2 ==>
   l4_vstred972 env uvars l4_vpat_empty972 g (l4_vinst961 e1 a1 k) (l4_vinst961 e2 a2 k)`,
  MESON_TAC [l4_vstred_vpat_empty_inst_ind972]);;

let l4_vstred_vpat_empty_triangle_ind972 = prove
 (`!e1 e2.
   l4_vpar_red961 e1 e2 ==>
   (!env uvars g e.
      l4_vstred972 env uvars l4_vpat_empty972 g e e1 ==>
      l4_vstred972 env uvars l4_vpat_empty972 g e e2)`,
  MATCH_MP_TAC l4_vpar_red_INDUCT961 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [];
   MESON_TAC [];
   MESON_TAC [];
   (* app *)
   MAP_EVERY X_GEN_TAC [`f1:l4_vexpr961`;`f2:l4_vexpr961`;`a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars l4_vpat_empty972 g e (L4VApp961 f1 a1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vstr_app972 THEN MAP_EVERY EXISTS_TAC [`f:l4_vexpr961`;`a:l4_vexpr961`] THEN
   ASM_MESON_TAC [];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`body1:l4_vexpr961`;`body2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars l4_vpat_empty972 g e (L4VLam961 dom1 body1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vstr_lam972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
   ASM_MESON_TAC [];
   (* forall *)
   MAP_EVERY X_GEN_TAC [`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`cod1:l4_vexpr961`;`cod2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars l4_vpat_empty972 g e (L4VForallE961 dom1 cod1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vstr_forallE972 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   ASM_MESON_TAC [];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`dom:l4_vexpr961`;`bd1:l4_vexpr961`;`bd2:l4_vexpr961`;
                        `arg1:l4_vexpr961`;`arg2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vstred972 env uvars l4_vpat_empty972 g e (L4VApp961 (L4VLam961 dom bd1) arg1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   UNDISCH_TAC `l4_vstred972 env uvars l4_vpat_empty972 g f (L4VLam961 dom bd1)` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac972 THEN
   MATCH_MP_TAC l4_vstred_whred972 THEN EXISTS_TAC `l4_vinst0961 body a` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vwhred_s972] THEN MATCH_MP_TAC l4_vrtc_tail972 THEN
    EXISTS_TAC `L4VApp961 (L4VLam961 dom' body) a` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vrtc_trans972 THEN EXISTS_TAC `L4VApp961 f a` THEN
     ASM_MESON_TAC [l4_vwhred_s972;l4_vwhred_s_app972];
     REWRITE_TAC [l4_vwhr_beta972]];
    REWRITE_TAC [l4_vinst0961] THEN MATCH_MP_TAC l4_vstred_vpat_empty_inst972 THEN
    ASM_MESON_TAC [l4_vstred_vpat_empty_ctx_irrel972]]]);;

let l4_vstred_vpat_empty_triangle972 = prove
 (`!env uvars g e e1 e2.
   l4_vstred972 env uvars l4_vpat_empty972 g e e1 /\
   l4_vpar_red961 e1 e2 ==>
   l4_vstred972 env uvars l4_vpat_empty972 g e e2`,
  MESON_TAC [l4_vstred_vpat_empty_triangle_ind972]);;

let l4_vstred_vpat_empty_triangle_star_ind972 = prove
 (`!x y.
   l4_vpar_red_star961 x y ==>
   (!env uvars g z.
      l4_vstred972 env uvars l4_vpat_empty972 g z x ==>
      l4_vstred972 env uvars l4_vpat_empty972 g z y)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN CONJ_TAC THENL
  [MESON_TAC []; MESON_TAC [l4_vstred_vpat_empty_triangle972]]);;

let l4_vpar_red_ts_vpat_empty_standard972 = prove
 (`!env uvars g e e'.
   l4_vpar_red_ts972 env uvars l4_vpat_empty972 g e e' ==>
   l4_vstred972 env uvars l4_vpat_empty972 g e e'`,
  REWRITE_TAC [l4_vpar_red_ts_vpat_empty_iff972] THEN
  MESON_TAC [l4_vstred_vpat_empty_triangle_star_ind972;l4_vstred_refl972]);;

let l4_vpar_red_star_standard_empty972 = prove
 (`!e e'.
   l4_vpar_red_star961 e e' ==>
   l4_vstred972 l4_venv_empty961 0 l4_vpat_empty972 [] e e'`,
  MESON_TAC [l4_vpar_red_ts_vpat_empty_standard972;l4_vpar_red_ts_vpat_empty_iff972]);;

let l4_vpar_red_star_whred_s_sort_empty972 = prove
 (`!e u.
   l4_vpar_red_star961 e (L4VSort961 u) ==>
   l4_vwhred_s972 l4_venv_empty961 0 l4_vpat_empty972 [] e (L4VSort961 u)`,
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP l4_vpar_red_star_standard_empty972) THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vpar_red_star_whred_s_forallE_empty972 = prove
 (`!e dom cod.
   l4_vpar_red_star961 e (L4VForallE961 dom cod) ==>
   ?dom0 cod0.
     l4_vwhred_s972 l4_venv_empty961 0 l4_vpat_empty972 [] e (L4VForallE961 dom0 cod0) /\
     l4_vpar_red_star961 dom0 dom /\
     l4_vpar_red_star961 cod0 cod`,
  MAP_EVERY X_GEN_TAC [`e:l4_vexpr961`;`dom1:l4_vexpr961`;`cod1:l4_vexpr961`] THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vpar_red_star_standard_empty972) THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vstred_CASES972] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN l4_subst_vars_tac972 THEN
  MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
  ASM_MESON_TAC [l4_vpar_red_ts_vpat_empty_iff972;l4_vstred_par_red_s972]);;
