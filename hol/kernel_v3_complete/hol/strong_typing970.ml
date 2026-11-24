(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of Lean4Lean/Theory/Typing/Strong.lean:
   1. Strong definitional equality (l4_vis_defeq_strong970), syntax-directed
      strong typing (l4_vhas_type_strong970), level-equivalence congruence
      (l4_veq_up_to_levels970), strong context/environment predicates
      (l4_vctx_strong970, l4_venv_strong970), and stratified typing
      (l4_vhas_type_stratified970).
   2. Equivalence of declarative and strong definitional equality
      (l4_vis_defeq_strong_thm970), right-hand level replacement
      (l4_vis_defeq_eq_up_to_levels970, l4_vis_defeq_instL_r970), and
      stratification (l4_vhas_type_strong_stratify970).
   3. Syntactic typing inversions modulo definitional equality:
      l4_vhas_type_app_inv970, l4_vhas_type_lam_inv970,
      l4_vhas_type_const_inv970, l4_vhas_type_bvar_inv970.
   4. Simultaneous definitional-equality substitution:
      l4_vis_defeq_strong_subst_eq970, l4_vis_defeq_subst_df970, and
      corollaries l4_vis_defeq_subst970, l4_vhas_type_subst970,
      l4_vis_defeq_u_subst970, l4_vis_type_subst970.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/subst_theory969.ml";;

(* ========================================================================= *)
(* 1. Level Congruence & ALL2 Helpers                                        *)
(* ========================================================================= *)

let l4_vlevel_succ_equiv970 = prove
 (`!u v. l4_vlevel_equiv961 u v ==> l4_vlevel_equiv961 (L4VLSucc961 u) (L4VLSucc961 v)`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961] THEN MESON_TAC []);;

let l4_vlevel_max_equiv970 = prove
 (`!a1 a2 b1 b2.
   l4_vlevel_equiv961 a1 a2 /\ l4_vlevel_equiv961 b1 b2 ==>
   l4_vlevel_equiv961 (L4VLMax961 a1 b1) (L4VLMax961 a2 b2)`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961] THEN MESON_TAC []);;

let l4_vlevel_imax_equiv970 = prove
 (`!a1 a2 b1 b2.
   l4_vlevel_equiv961 a1 a2 /\ l4_vlevel_equiv961 b1 b2 ==>
   l4_vlevel_equiv961 (L4VLIMax961 a1 b1) (L4VLIMax961 a2 b2)`,
  REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961] THEN MESON_TAC []);;

let l4_vnth_level_equiv970 = prove
 (`!ls1 ls2 i.
   ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
   l4_vlevel_equiv961 (l4_vnth_level961 ls1 i) (l4_vnth_level961 ls2 i)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [FORALL_SIMP;ALL2;l4_vnth_level961] THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vlevel_equiv_refl961];
   GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC []]);;

let l4_vlevel_inst_congr_r970 = prove
 (`!u ls1 ls2.
   ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
   l4_vlevel_equiv961 (l4_vlevel_inst961 ls1 u) (l4_vlevel_inst961 ls2 u)`,
  MATCH_MP_TAC l4_vlevel_INDUCT961 THEN
  REWRITE_TAC [FORALL_SIMP;l4_vlevel_inst961;l4_vlevel_equiv_refl961] THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vlevel_succ_equiv970];
   MESON_TAC [l4_vlevel_max_equiv970];
   MESON_TAC [l4_vlevel_imax_equiv970];
   MESON_TAC [l4_vnth_level_equiv970]]);;

let l4_all2_vlevel_equiv_refl970 = prove
 (`!ls. ALL2 l4_vlevel_equiv961 ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]);;

let l4_all2_vlevel_equiv_symm970 = prove
 (`!ls1 ls2. ALL2 l4_vlevel_equiv961 ls1 ls2 ==> ALL2 l4_vlevel_equiv961 ls2 ls1`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2] THEN
  ASM_MESON_TAC [l4_vlevel_equiv_symm961]);;

let l4_all2_vlevel_equiv_trans970 = prove
 (`!ls1 ls2 ls3.
   ALL2 l4_vlevel_equiv961 ls1 ls2 /\ ALL2 l4_vlevel_equiv961 ls2 ls3 ==>
   ALL2 l4_vlevel_equiv961 ls1 ls3`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2] THEN
  ASM_MESON_TAC [l4_vlevel_equiv_trans961]);;

let l4_all2_length_eq970 = prove
 (`!R (xs:A list) (ys:B list). ALL2 R xs ys ==> LENGTH xs = LENGTH ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [ALL2;LENGTH] THEN STRIP_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC []);;

let l4_all2_map_vlevel_inst_congr970 = prove
 (`!us ls1 ls2.
   ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
   ALL2 l4_vlevel_equiv961
     (MAP (l4_vlevel_inst961 ls1) us)
     (MAP (l4_vlevel_inst961 ls2) us)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MAP;ALL2] THEN
  DISCH_TAC THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vlevel_inst_congr_r970 THEN ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 2. Inductive Definitions: IsDefEqStrong, HasTypeStrong, EqUpToLevels      *)
(* ========================================================================= *)

let l4_vis_defeq_strong_RULES970,l4_vis_defeq_strong_INDUCT970,l4_vis_defeq_strong_CASES970 =
  new_inductive_definition
 `(!env uvars g i ty u.
     l4_vlookup961 g i ty /\
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq_strong970 env uvars g ty ty (L4VSort961 u) ==>
     l4_vis_defeq_strong970 env uvars g (L4VBVar961 i) (L4VBVar961 i) ty) /\
  (!env uvars g e1 e2 ty.
     l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
     l4_vis_defeq_strong970 env uvars g e2 e1 ty) /\
  (!env uvars g e1 e2 e3 ty.
     l4_vis_defeq_strong970 env uvars g e1 e2 ty /\
     l4_vis_defeq_strong970 env uvars g e2 e3 ty ==>
     l4_vis_defeq_strong970 env uvars g e1 e3 ty) /\
  (!env uvars g l1 l2.
     l4_vlevel_wf961 uvars l1 /\
     l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_vis_defeq_strong970 env uvars g (L4VSort961 l1) (L4VSort961 l2)
       (L4VSort961 (L4VLSucc961 l1))) /\
  (!env uvars g c ci ls1 ls2 u.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls1 /\
     ALL (l4_vlevel_wf961 uvars) ls2 /\
     LENGTH ls1 = l4_vc_uvars961 ci /\
     ALL2 l4_vlevel_equiv961 ls1 ls2 /\
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq_strong970 env uvars []
       (l4_vinstL961 ls1 (l4_vc_type961 ci))
       (l4_vinstL961 ls2 (l4_vc_type961 ci)) (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinstL961 ls1 (l4_vc_type961 ci))
       (l4_vinstL961 ls2 (l4_vc_type961 ci)) (L4VSort961 u) ==>
     l4_vis_defeq_strong970 env uvars g (L4VConst961 c ls1) (L4VConst961 c ls2)
       (l4_vinstL961 ls1 (l4_vc_type961 ci))) /\
  (!env uvars g u v dom cod f1 f2 a1 a2.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars g f1 f2 (L4VForallE961 dom cod) /\
     l4_vis_defeq_strong970 env uvars g a1 a2 dom /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinst0961 cod a1) (l4_vinst0961 cod a2) (L4VSort961 v) ==>
     l4_vis_defeq_strong970 env uvars g
       (L4VApp961 f1 a1) (L4VApp961 f2 a2) (l4_vinst0961 cod a1)) /\
  (!env uvars g u v dom1 dom2 cod b1 b2.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vis_defeq_strong970 env uvars g dom1 dom2 (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars (CONS dom1 g) cod cod (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars (CONS dom2 g) cod cod (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars (CONS dom1 g) b1 b2 cod /\
     l4_vis_defeq_strong970 env uvars (CONS dom2 g) b1 b2 cod ==>
     l4_vis_defeq_strong970 env uvars g
       (L4VLam961 dom1 b1) (L4VLam961 dom2 b2) (L4VForallE961 dom1 cod)) /\
  (!env uvars g u v dom1 dom2 cod1 cod2.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vis_defeq_strong970 env uvars g dom1 dom2 (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars (CONS dom1 g) cod1 cod2 (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars (CONS dom2 g) cod1 cod2 (L4VSort961 v) ==>
     l4_vis_defeq_strong970 env uvars g
       (L4VForallE961 dom1 cod1) (L4VForallE961 dom2 cod2)
       (L4VSort961 (L4VLIMax961 u v))) /\
  (!env uvars g u ty1 ty2 e1 e2.
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq_strong970 env uvars g ty1 ty2 (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars g e1 e2 ty1 ==>
     l4_vis_defeq_strong970 env uvars g e1 e2 ty2) /\
  (!env uvars g u v dom cod body arg.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g) body body cod /\
     l4_vis_defeq_strong970 env uvars g arg arg dom /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinst0961 cod arg) (l4_vinst0961 cod arg) (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinst0961 body arg) (l4_vinst0961 body arg) (l4_vinst0961 cod arg) ==>
     l4_vis_defeq_strong970 env uvars g
       (L4VApp961 (L4VLam961 dom body) arg) (l4_vinst0961 body arg)
       (l4_vinst0961 cod arg)) /\
  (!env uvars g u v dom cod e.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars (CONS (l4_vlift961 dom) (CONS dom g))
       (l4_vliftN961 cod 1 1) (l4_vliftN961 cod 1 1) (L4VSort961 v) /\
     l4_vis_defeq_strong970 env uvars g e e (L4VForallE961 dom cod) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g)
       (l4_vlift961 e) (l4_vlift961 e)
       (L4VForallE961 (l4_vlift961 dom) (l4_vliftN961 cod 1 1)) /\
     l4_vis_defeq_strong970 env uvars (CONS dom g)
       (l4_vlift961 dom) (l4_vlift961 dom) (L4VSort961 u) ==>
     l4_vis_defeq_strong970 env uvars g
       (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) e
       (L4VForallE961 dom cod)) /\
  (!env uvars g p h1 h2.
     l4_vis_defeq_strong970 env uvars g p p (L4VSort961 L4VLZero961) /\
     l4_vis_defeq_strong970 env uvars g h1 h1 p /\
     l4_vis_defeq_strong970 env uvars g h2 h2 p ==>
     l4_vis_defeq_strong970 env uvars g h1 h2 p) /\
  (!env uvars g df ls u.
     l4_venv_has_defeq961 env df /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vdf_uvars961 df /\
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq_strong970 env uvars []
       (l4_vinstL961 ls (l4_vdf_type961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)) (L4VSort961 u) /\
     l4_vis_defeq_strong970 env uvars []
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)) /\
     l4_vis_defeq_strong970 env uvars []
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)) /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)) /\
     l4_vis_defeq_strong970 env uvars g
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)) ==>
     l4_vis_defeq_strong970 env uvars g
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)))`;;

let l4_vis_defeq_strong_bvar970,
    l4_vis_defeq_strong_symm970,
    l4_vis_defeq_strong_trans970,
    l4_vis_defeq_strong_sort970,
    l4_vis_defeq_strong_const970,
    l4_vis_defeq_strong_app970,
    l4_vis_defeq_strong_lam970,
    l4_vis_defeq_strong_forall970,
    l4_vis_defeq_strong_conv970,
    l4_vis_defeq_strong_beta970,
    l4_vis_defeq_strong_eta970,
    l4_vis_defeq_strong_proof_irrel970,
    l4_vis_defeq_strong_extra970 =
  match CONJUNCTS l4_vis_defeq_strong_RULES970 with
  | [c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13] ->
      (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13)
  | _ -> failwith "l4_vis_defeq_strong_RULES970: unexpected arity";;

let l4_vis_defeq_strong_STRONG_INDUCT970 =
  derive_strong_induction (l4_vis_defeq_strong_RULES970, l4_vis_defeq_strong_INDUCT970);;

let l4_vhas_type_strong_RULES970,l4_vhas_type_strong_INDUCT970,l4_vhas_type_strong_CASES970 =
  new_inductive_definition
 `(!env uvars g i ty u.
     l4_vlookup961 g i ty /\
     l4_vlevel_wf961 uvars u /\
     l4_vhas_type_strong970 env uvars g ty (L4VSort961 u) T ==>
     l4_vhas_type_strong970 env uvars g (L4VBVar961 i) ty F) /\
  (!env uvars g l1 l2.
     l4_vlevel_wf961 uvars l1 /\
     l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_vhas_type_strong970 env uvars g (L4VSort961 l1) (L4VSort961 (L4VLSucc961 l2)) F) /\
  (!env uvars g c ci ls u.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vc_uvars961 ci /\
     l4_vlevel_wf961 uvars u /\
     l4_vhas_type_strong970 env uvars [] (l4_vinstL961 ls (l4_vc_type961 ci)) (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars g (l4_vinstL961 ls (l4_vc_type961 ci)) (L4VSort961 u) T ==>
     l4_vhas_type_strong970 env uvars g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci)) F) /\
  (!env uvars g u v dom cod f a.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vhas_type_strong970 env uvars g dom (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars (CONS dom g) cod (L4VSort961 v) T /\
     l4_vhas_type_strong970 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T /\
     l4_vhas_type_strong970 env uvars g f (L4VForallE961 dom cod) T /\
     l4_vhas_type_strong970 env uvars g a dom T /\
     l4_vhas_type_strong970 env uvars g (l4_vinst0961 cod a) (L4VSort961 v) T ==>
     l4_vhas_type_strong970 env uvars g (L4VApp961 f a) (l4_vinst0961 cod a) F) /\
  (!env uvars g u v dom cod body.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vhas_type_strong970 env uvars g dom (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars (CONS dom g) cod (L4VSort961 v) T /\
     l4_vhas_type_strong970 env uvars (CONS dom g) body cod T /\
     l4_vhas_type_strong970 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T ==>
     l4_vhas_type_strong970 env uvars g (L4VLam961 dom body) (L4VForallE961 dom cod) F) /\
  (!env uvars g u v dom cod.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vhas_type_strong970 env uvars g dom (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars (CONS dom g) cod (L4VSort961 v) T ==>
     l4_vhas_type_strong970 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) F) /\
  (!env uvars g e ty.
     l4_vhas_type_strong970 env uvars g e ty F ==>
     l4_vhas_type_strong970 env uvars g e ty T) /\
  (!env uvars g u ty1 ty2 e.
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq_strong970 env uvars g ty1 ty2 (L4VSort961 u) /\
     l4_vhas_type_strong970 env uvars g ty1 (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars g ty2 (L4VSort961 u) T /\
     l4_vhas_type_strong970 env uvars g e ty1 T ==>
     l4_vhas_type_strong970 env uvars g e ty2 T)`;;

let l4_vhas_type_strong_bvar970,
    l4_vhas_type_strong_sort970,
    l4_vhas_type_strong_const970,
    l4_vhas_type_strong_app970,
    l4_vhas_type_strong_lam970,
    l4_vhas_type_strong_forall970,
    l4_vhas_type_strong_base970,
    l4_vhas_type_strong_defeq970 =
  match CONJUNCTS l4_vhas_type_strong_RULES970 with
  | [c1;c2;c3;c4;c5;c6;c7;c8] -> (c1,c2,c3,c4,c5,c6,c7,c8)
  | _ -> failwith "l4_vhas_type_strong_RULES970: unexpected arity";;

let l4_vhas_type_strong_STRONG_INDUCT970 =
  derive_strong_induction (l4_vhas_type_strong_RULES970, l4_vhas_type_strong_INDUCT970);;

let l4_veq_up_to_levels_RULES970,l4_veq_up_to_levels_INDUCT970,l4_veq_up_to_levels_CASES970 =
  new_inductive_definition
 `(!uvars i. l4_veq_up_to_levels970 uvars (L4VBVar961 i) (L4VBVar961 i)) /\
  (!uvars c ls1 ls2.
     ALL (l4_vlevel_wf961 uvars) ls1 /\
     ALL (l4_vlevel_wf961 uvars) ls2 /\
     ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
     l4_veq_up_to_levels970 uvars (L4VConst961 c ls1) (L4VConst961 c ls2)) /\
  (!uvars l1 l2.
     l4_vlevel_wf961 uvars l1 /\
     l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_veq_up_to_levels970 uvars (L4VSort961 l1) (L4VSort961 l2)) /\
  (!uvars f1 f2 a1 a2.
     l4_veq_up_to_levels970 uvars f1 f2 /\
     l4_veq_up_to_levels970 uvars a1 a2 ==>
     l4_veq_up_to_levels970 uvars (L4VApp961 f1 a1) (L4VApp961 f2 a2)) /\
  (!uvars dom1 dom2 b1 b2.
     l4_veq_up_to_levels970 uvars dom1 dom2 /\
     l4_veq_up_to_levels970 uvars b1 b2 ==>
     l4_veq_up_to_levels970 uvars (L4VLam961 dom1 b1) (L4VLam961 dom2 b2)) /\
  (!uvars dom1 dom2 cod1 cod2.
     l4_veq_up_to_levels970 uvars dom1 dom2 /\
     l4_veq_up_to_levels970 uvars cod1 cod2 ==>
     l4_veq_up_to_levels970 uvars (L4VForallE961 dom1 cod1) (L4VForallE961 dom2 cod2))`;;

let l4_veq_up_to_levels_bvar970,
    l4_veq_up_to_levels_const970,
    l4_veq_up_to_levels_sort970,
    l4_veq_up_to_levels_app970,
    l4_veq_up_to_levels_lam970,
    l4_veq_up_to_levels_forall970 =
  match CONJUNCTS l4_veq_up_to_levels_RULES970 with
  | [c1;c2;c3;c4;c5;c6] -> (c1,c2,c3,c4,c5,c6)
  | _ -> failwith "l4_veq_up_to_levels_RULES970: unexpected arity";;

(* ========================================================================= *)
(* 3. Basic Metatheory of IsDefEqStrong & EqUpToLevels                       *)
(* ========================================================================= *)

let l4_vis_defeq_strong_refl_l970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g e1 e1 ty`,
  MESON_TAC [l4_vis_defeq_strong_symm970;l4_vis_defeq_strong_trans970]);;

let l4_vis_defeq_strong_refl_r970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g e2 e2 ty`,
  MESON_TAC [l4_vis_defeq_strong_symm970;l4_vis_defeq_strong_trans970]);;

let l4_vis_defeq_strong_to_defeq970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g e1 e2 ty`,
  MATCH_MP_TAC l4_vis_defeq_strong_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_bvar961];
   MESON_TAC [l4_vis_defeq_symm961];
   MESON_TAC [l4_vis_defeq_trans961];
   MESON_TAC [l4_vis_defeq_sort961];
   MESON_TAC [l4_vis_defeq_const961];
   MESON_TAC [l4_vis_defeq_app961];
   MESON_TAC [l4_vis_defeq_lam961];
   MESON_TAC [l4_vis_defeq_forall961];
   MESON_TAC [l4_vis_defeq_conv961];
   MESON_TAC [l4_vis_defeq_beta961;l4_vhas_type961];
   MESON_TAC [l4_vis_defeq_eta961;l4_vhas_type961];
   MESON_TAC [l4_vis_defeq_proof_irrel961;l4_vhas_type961];
   MESON_TAC [l4_vis_defeq_extra961]]);;

let l4_vis_defeq_strong_mono_ind970 = prove
 (`!env1 uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env1 uvars g e1 e2 ty ==>
   (!env2. l4_venv_ordered961 env1 env2 ==>
           l4_vis_defeq_strong970 env2 uvars g e1 e2 ty)`,
  MATCH_MP_TAC l4_vis_defeq_strong_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_strong_bvar970];
   MESON_TAC [l4_vis_defeq_strong_symm970];
   MESON_TAC [l4_vis_defeq_strong_trans970];
   MESON_TAC [l4_vis_defeq_strong_sort970];
   MESON_TAC [l4_venv_ordered961;l4_vis_defeq_strong_const970];
   MESON_TAC [l4_vis_defeq_strong_app970];
   MESON_TAC [l4_vis_defeq_strong_lam970];
   MESON_TAC [l4_vis_defeq_strong_forall970];
   MESON_TAC [l4_vis_defeq_strong_conv970];
   MESON_TAC [l4_vis_defeq_strong_beta970];
   MESON_TAC [l4_vis_defeq_strong_eta970];
   MESON_TAC [l4_vis_defeq_strong_proof_irrel970];
   MESON_TAC [l4_venv_ordered961;l4_vis_defeq_strong_extra970]]);;

let l4_vis_defeq_strong_mono970 = prove
 (`!env1 env2 uvars g e1 e2 ty.
   l4_venv_ordered961 env1 env2 /\
   l4_vis_defeq_strong970 env1 uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env2 uvars g e1 e2 ty`,
  MESON_TAC [l4_vis_defeq_strong_mono_ind970]);;

let l4_vliftN_one_one_comm970 = prove
 (`!e n k.
   l4_vliftN961 (l4_vliftN961 e 1 1) n (SUC (SUC k)) =
   l4_vliftN961 (l4_vliftN961 e n (SUC k)) 1 1`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`n:num`;`1`;`SUC k`;`1`] l4_vliftN_comm966) THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC [ARITH_RULE `1 + SUC k = SUC (SUC k)`]]);;

let l4_vis_defeq_strong_weakN_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   (!n k g'.
      l4_venv_closed966 env /\ l4_vctx_liftN966 n k g g' ==>
      l4_vis_defeq_strong970 env uvars g'
        (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) (l4_vliftN961 ty n k))`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
   ASM_MESON_TAC [l4_vlookup_weakN966];
   (* symm *)
   MESON_TAC [l4_vis_defeq_strong_symm970];
   (* trans *)
   MESON_TAC [l4_vis_defeq_strong_trans970];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   SUBGOAL_THEN `l4_vliftN961 (l4_vinstL961 ls1 (l4_vc_type961 ci)) n k =
                 l4_vinstL961 ls1 (l4_vc_type961 ci) /\
                 l4_vliftN961 (l4_vinstL961 ls2 (l4_vc_type961 ci)) n k =
                 l4_vinstL961 ls2 (l4_vc_type961 ci)` (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC l4_vclosedN_vliftN_eq966 THEN
    ASM_MESON_TAC [l4_closed_inst_const966];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_MESON_TAC []];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vliftN961 dom n k`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961;l4_vliftN_vinst0966]) THEN
   ASM_MESON_TAC [l4_vctx_liftN_succ966];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
   ASM_MESON_TAC [l4_vctx_liftN_succ966];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
   ASM_MESON_TAC [l4_vctx_liftN_succ966];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`l4_vliftN961 ty1 n k`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_MESON_TAC [];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961;l4_vliftN_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961;l4_vliftN_vinst0966]) THEN
   ASM_MESON_TAC [l4_vctx_liftN_succ966];
   (* eta *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961;ARITH_RULE `0 < SUC k`;l4_vliftN_vlift966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   SUBGOAL_THEN `l4_vctx_liftN966 n (SUC k) (CONS dom g) (CONS (l4_vliftN961 dom n k) g')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_liftN_succ966 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_liftN966 n (SUC (SUC k))
                   (CONS (l4_vlift961 dom) (CONS dom g))
                   (CONS (l4_vliftN961 (l4_vlift961 dom) n (SUC k)) (CONS (l4_vliftN961 dom n k) g'))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_liftN_succ966 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [GSYM l4_vliftN_vlift966;GSYM l4_vliftN_one_one_comm970] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN
    ASM_MESON_TAC []];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_proof_irrel970 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vliftN961]) THEN ASM_MESON_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   MP_TAC (GEN `m:num`
     (SPECL [`env:l4_venv961`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`;`m:num`]
       l4_closed_inst_defeq966)) THEN
   ASM_REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC THEN
   ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   RULE_ASSUM_TAC (SIMP_RULE [ASSUME `!m. l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_type961 df)) m`;
                              ASSUME `!m. l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_lhs961 df)) m`;
                              ASSUME `!m. l4_vclosedN961 (l4_vinstL961 ls (l4_vdf_rhs961 df)) m`;
                              l4_vclosedN_vliftN_eq966;l4_vliftN961]) THEN
   ASM_MESON_TAC []]);;

let l4_vis_defeq_strong_weakN970 = prove
 (`!env uvars g e1 e2 ty n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g'
     (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k) (l4_vliftN961 ty n k)`,
  MESON_TAC [l4_vis_defeq_strong_weakN_ind970]);;

let l4_vis_defeq_strong_weak970 = prove
 (`!env uvars g e1 e2 ty b.
   l4_venv_closed966 env /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars (CONS b g)
     (l4_vlift961 e1) (l4_vlift961 e2) (l4_vlift961 ty)`,
  REWRITE_TAC [l4_vlift961] THEN
  MESON_TAC [l4_vis_defeq_strong_weakN970;l4_vctx_liftN_one966]);;

let l4_vis_defeq_strong_weak0970 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_closed966 env /\
   l4_vis_defeq_strong970 env uvars [] e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g e1 e2 ty`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`]
    l4_vis_defeq_closedN966) THEN
  ANTS_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970;l4_vctx_closed966]; ALL_TAC] THEN
  REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`;
                 `LENGTH (g:l4_vexpr961 list)`;`0`;`APPEND (g:l4_vexpr961 list) []`]
    l4_vis_defeq_strong_weakN970) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REFL_TAC;
   ASM_SIMP_TAC [APPEND_NIL;l4_vclosedN_vliftN_eq966;LE_0]]);;

(* EqUpToLevels lemmas *)
let l4_veq_up_to_levels_instL_ind970 = prove
 (`!env uvars' g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars' g e1 e2 ty ==>
   (!uvars ls1 ls2.
      ALL (l4_vlevel_wf961 uvars) ls1 /\
      ALL (l4_vlevel_wf961 uvars) ls2 /\
      ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
      l4_veq_up_to_levels970 uvars (l4_vinstL961 ls1 e1) (l4_vinstL961 ls2 e1) /\
      l4_veq_up_to_levels970 uvars (l4_vinstL961 ls1 e2) (l4_vinstL961 ls2 e2))`,
  MATCH_MP_TAC l4_vis_defeq_strong_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [FORALL_SIMP;l4_vinstL961;l4_veq_up_to_levels_bvar970];
   MESON_TAC [];
   MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_sort970 THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vlevel_inst_congr_r970];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_const970 THEN
   ASM_SIMP_TAC [l4_all_vlevel_inst_wf966;l4_all2_map_vlevel_inst_congr970];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_app970 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_lam970 THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_forall970 THEN ASM_MESON_TAC [];
   MESON_TAC [];
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [l4_vinstL961] THEN MATCH_MP_TAC l4_veq_up_to_levels_app970 THEN
    CONJ_TAC THENL [MATCH_MP_TAC l4_veq_up_to_levels_lam970; ALL_TAC] THEN ASM_MESON_TAC [];
    ASM_MESON_TAC []];
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [l4_vinstL961] THEN MATCH_MP_TAC l4_veq_up_to_levels_lam970 THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC [];
     MATCH_MP_TAC l4_veq_up_to_levels_app970 THEN
     REWRITE_TAC [l4_veq_up_to_levels_bvar970] THEN ASM_MESON_TAC []];
    ASM_MESON_TAC []];
   MESON_TAC [];
   MESON_TAC []]);;

let l4_veq_up_to_levels_instL970 = prove
 (`!env uvars uvars' g e1 e2 ty ls1 ls2.
   ALL (l4_vlevel_wf961 uvars) ls1 /\
   ALL (l4_vlevel_wf961 uvars) ls2 /\
   ALL2 l4_vlevel_equiv961 ls1 ls2 /\
   l4_vis_defeq_strong970 env uvars' g e1 e2 ty ==>
   l4_veq_up_to_levels970 uvars (l4_vinstL961 ls1 e1) (l4_vinstL961 ls2 e1) /\
   l4_veq_up_to_levels970 uvars (l4_vinstL961 ls1 e2) (l4_vinstL961 ls2 e2)`,
  MESON_TAC [l4_veq_up_to_levels_instL_ind970]);;

let l4_veq_up_to_levels_refl970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vctx_level_wf966 uvars g /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_veq_up_to_levels970 uvars e1 e1 /\ l4_veq_up_to_levels970 uvars e2 e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vexpr_level_wf966 uvars e1 /\ l4_vexpr_level_wf966 uvars e2`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_level_wf966;l4_vis_defeq_strong_to_defeq970];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`;
                  `l4_vlevel_params966 uvars`;`l4_vlevel_params966 uvars`]
     l4_veq_up_to_levels_instL970) THEN
   ASM_SIMP_TAC [l4_vlevel_params_wf966;l4_all2_vlevel_equiv_refl970;l4_vinstL_params966]]);;

let l4_veq_up_to_levels_weakN_ind970 = prove
 (`!uvars e1 e2.
   l4_veq_up_to_levels970 uvars e1 e2 ==>
   (!n k. l4_veq_up_to_levels970 uvars (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k))`,
  MATCH_MP_TAC l4_veq_up_to_levels_INDUCT970 THEN
  REWRITE_TAC [FORALL_SIMP;l4_vliftN961;l4_veq_up_to_levels_bvar970] THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_veq_up_to_levels_const970];
   MESON_TAC [l4_veq_up_to_levels_sort970];
   MESON_TAC [l4_veq_up_to_levels_app970];
   MESON_TAC [l4_veq_up_to_levels_lam970];
   MESON_TAC [l4_veq_up_to_levels_forall970]]);;

let l4_veq_up_to_levels_weakN970 = prove
 (`!uvars e1 e2 n k.
   l4_veq_up_to_levels970 uvars e1 e2 ==>
   l4_veq_up_to_levels970 uvars (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  MESON_TAC [l4_veq_up_to_levels_weakN_ind970]);;

let l4_veq_up_to_levels_instN_ind970 = prove
 (`!uvars e1 e2.
   l4_veq_up_to_levels970 uvars e1 e2 ==>
   (!v1 v2 k.
      l4_veq_up_to_levels970 uvars v1 v2 ==>
      l4_veq_up_to_levels970 uvars (l4_vinst961 e1 v1 k) (l4_vinst961 e2 v2 k))`,
  MATCH_MP_TAC l4_veq_up_to_levels_INDUCT970 THEN
  REWRITE_TAC [l4_vinst961] THEN REPEAT CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`uvars:num`;`i:num`;`v1:l4_vexpr961`;`v2:l4_vexpr961`;`k:num`] THEN
   DISCH_TAC THEN REWRITE_TAC [l4_vinst_var961] THEN
   ASM_CASES_TAC `i < k` THEN ASM_REWRITE_TAC [l4_veq_up_to_levels_bvar970] THEN
   ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC [l4_veq_up_to_levels_bvar970] THEN
   MATCH_MP_TAC l4_veq_up_to_levels_weakN970 THEN ASM_REWRITE_TAC [];
   MESON_TAC [l4_veq_up_to_levels_const970];
   MESON_TAC [l4_veq_up_to_levels_sort970];
   MESON_TAC [l4_veq_up_to_levels_app970];
   MESON_TAC [l4_veq_up_to_levels_lam970];
   MESON_TAC [l4_veq_up_to_levels_forall970]]);;

let l4_veq_up_to_levels_inst0970 = prove
 (`!uvars e1 e2 v1 v2.
   l4_veq_up_to_levels970 uvars e1 e2 /\ l4_veq_up_to_levels970 uvars v1 v2 ==>
   l4_veq_up_to_levels970 uvars (l4_vinst0961 e1 v1) (l4_vinst0961 e2 v2)`,
  REWRITE_TAC [l4_vinst0961] THEN MESON_TAC [l4_veq_up_to_levels_instN_ind970]);;

let l4_veq_up_to_levels_bvar_inv970 = prove
 (`!uvars i e'. l4_veq_up_to_levels970 uvars (L4VBVar961 i) e' <=> e' = L4VBVar961 i`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

let l4_veq_up_to_levels_const_inv970 = prove
 (`!uvars c ls e'.
   l4_veq_up_to_levels970 uvars (L4VConst961 c ls) e' <=>
   ?ls'. e' = L4VConst961 c ls' /\
         ALL (l4_vlevel_wf961 uvars) ls /\
         ALL (l4_vlevel_wf961 uvars) ls' /\
         ALL2 l4_vlevel_equiv961 ls ls'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

let l4_veq_up_to_levels_sort_inv970 = prove
 (`!uvars l e'.
   l4_veq_up_to_levels970 uvars (L4VSort961 l) e' <=>
   ?l'. e' = L4VSort961 l' /\
        l4_vlevel_wf961 uvars l /\
        l4_vlevel_wf961 uvars l' /\
        l4_vlevel_equiv961 l l'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

let l4_veq_up_to_levels_app_inv970 = prove
 (`!uvars f a e'.
   l4_veq_up_to_levels970 uvars (L4VApp961 f a) e' <=>
   ?f' a'. e' = L4VApp961 f' a' /\
           l4_veq_up_to_levels970 uvars f f' /\
           l4_veq_up_to_levels970 uvars a a'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

let l4_veq_up_to_levels_lam_inv970 = prove
 (`!uvars dom body e'.
   l4_veq_up_to_levels970 uvars (L4VLam961 dom body) e' <=>
   ?dom' body'. e' = L4VLam961 dom' body' /\
                l4_veq_up_to_levels970 uvars dom dom' /\
                l4_veq_up_to_levels970 uvars body body'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

let l4_veq_up_to_levels_forall_inv970 = prove
 (`!uvars dom cod e'.
   l4_veq_up_to_levels970 uvars (L4VForallE961 dom cod) e' <=>
   ?dom' cod'. e' = L4VForallE961 dom' cod' /\
               l4_veq_up_to_levels970 uvars dom dom' /\
               l4_veq_up_to_levels970 uvars cod cod'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [l4_veq_up_to_levels_CASES970] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN MESON_TAC []);;

(* ========================================================================= *)
(* 4. Strong Context & Environment Predicates + InstN / InstL                *)
(* ========================================================================= *)

let l4_vis_defeq_strong_instL_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   (!uvars' ls.
      ALL (l4_vlevel_wf961 uvars') ls ==>
      l4_vis_defeq_strong970 env uvars' (MAP (l4_vinstL961 ls) g)
        (l4_vinstL961 ls e1) (l4_vinstL961 ls e2) (l4_vinstL961 ls ty))`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN EXISTS_TAC `l4_vlevel_inst961 ls u` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961]) THEN
   ASM_SIMP_TAC [l4_vlookup_instL966;l4_vlevel_inst_wf_any966];
   (* symm *)
   MESON_TAC [l4_vis_defeq_strong_symm970];
   (* trans *)
   MESON_TAC [l4_vis_defeq_strong_trans970];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vlevel_inst961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vlevel_inst_equiv966];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinstL966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN EXISTS_TAC `l4_vlevel_inst961 ls u` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961;l4_vinstL_vinstL966]) THEN
   ASM_SIMP_TAC [l4_all_vlevel_inst_wf966;LENGTH_MAP;l4_all2_vlevel_inst_equiv966;
                 l4_vlevel_inst_wf_any966];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls u`;`l4_vlevel_inst961 ls v`;
                         `l4_vinstL961 ls dom`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961;l4_vinstL_vinst0966]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls u`;`l4_vlevel_inst961 ls v`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vlevel_inst961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls u`;`l4_vinstL961 ls ty1`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL961;l4_vinstL_vinst0966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls u`;`l4_vlevel_inst961 ls v`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961;l4_vinstL_vinst0966]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* eta *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vinstL961;l4_vinstL_vlift966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls u`;`l4_vlevel_inst961 ls v`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961;l4_vinstL_vlift966;l4_vinstL_vliftN966]) THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_proof_irrel970 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinstL961;l4_vlevel_inst961]) THEN ASM_SIMP_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinstL_vinstL966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN EXISTS_TAC `l4_vlevel_inst961 ls' u` THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MAP;l4_vinstL961;l4_vinstL_vinstL966]) THEN
   ASM_SIMP_TAC [l4_all_vlevel_inst_wf966;LENGTH_MAP;l4_vlevel_inst_wf_any966]]);;

let l4_vis_defeq_strong_instL970 = prove
 (`!env uvars uvars' ls g e1 e2 ty.
   ALL (l4_vlevel_wf961 uvars') ls /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars' (MAP (l4_vinstL961 ls) g)
     (l4_vinstL961 ls e1) (l4_vinstL961 ls e2) (l4_vinstL961 ls ty)`,
  MESON_TAC [l4_vis_defeq_strong_instL_ind970]);;

let l4_vctx_strong970 = new_recursive_definition list_RECURSION
 `(l4_vctx_strong970 env uvars [] <=> T) /\
  (l4_vctx_strong970 env uvars (CONS a g) <=>
    l4_vctx_strong970 env uvars g /\
    (?u. l4_vis_defeq_strong970 env uvars g a a (L4VSort961 u)))`;;

let l4_vis_defeq_strong_weak_sort970 = prove
 (`!env uvars g a u b.
   l4_venv_closed966 env /\
   l4_vis_defeq_strong970 env uvars g a a (L4VSort961 u) ==>
   l4_vis_defeq_strong970 env uvars (CONS b g)
     (l4_vlift961 a) (l4_vlift961 a) (L4VSort961 u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `a:l4_vexpr961`;`a:l4_vexpr961`;`L4VSort961 u`;`b:l4_vexpr961`]
    l4_vis_defeq_strong_weak970) THEN
  ASM_SIMP_TAC [l4_vlift961;l4_vliftN961]);;

let l4_vctx_strong_lookup_ind970 = prove
 (`!g i ty.
   l4_vlookup961 g i ty ==>
   (!env uvars.
      l4_venv_closed966 env /\ l4_vctx_strong970 env uvars g ==>
      ?u. l4_vis_defeq_strong970 env uvars g ty ty (L4VSort961 u))`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN
  REWRITE_TAC [l4_vctx_strong970] THEN
  MESON_TAC [l4_vis_defeq_strong_weak_sort970]);;

let l4_vctx_strong_lookup970 = prove
 (`!env uvars g i ty.
   l4_venv_closed966 env /\ l4_vctx_strong970 env uvars g /\ l4_vlookup961 g i ty ==>
   ?u. l4_vis_defeq_strong970 env uvars g ty ty (L4VSort961 u)`,
  MESON_TAC [l4_vctx_strong_lookup_ind970]);;

let l4_vctx_strong_to_wf970 = prove
 (`!g env uvars. l4_vctx_strong970 env uvars g ==> l4_vctx_wf966 env uvars g`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vctx_strong970;l4_vctx_wf966;l4_vis_type961;l4_vhas_type961] THEN
  ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]);;

let l4_vctx_strong_level_wf970 = prove
 (`!g env uvars. l4_vctx_strong970 env uvars g ==> l4_vctx_level_wf966 uvars g`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [FORALL_SIMP;l4_vctx_strong970;l4_vctx_level_wf966] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vctx_level_wf966 uvars t` ASSUME_TAC THENL
  [ASM_MESON_TAC []; ASM_REWRITE_TAC []] THEN
  ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970;l4_vis_defeq_level_wf966]);;

let l4_vlift_vinst_lo970 = prove
 (`!e v k. l4_vlift961 (l4_vinst961 e v k) = l4_vinst961 (l4_vlift961 e) v (SUC k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift961;ARITH_RULE `SUC k = 1 + k`] THEN
  MATCH_MP_TAC l4_vliftN_vinst_lo966 THEN ARITH_TAC);;

let l4_vliftN_one_one_vinst_lo970 = prove
 (`!e v k.
   l4_vliftN961 (l4_vinst961 e v (SUC k)) 1 1 =
   l4_vinst961 (l4_vliftN961 e 1 1) v (SUC (SUC k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [ARITH_RULE `SUC (SUC k) = 1 + SUC k`] THEN
  MATCH_MP_TAC l4_vliftN_vinst_lo966 THEN ARITH_TAC);;

let l4_vinst0_vliftN_one_one_bvar0970 = prove
 (`!e. l4_vinst0961 (l4_vliftN961 e 1 1) (L4VBVar961 0) = e`,
  GEN_TAC THEN REWRITE_TAC [l4_vinst0961] THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966) THEN
  REWRITE_TAC [SYM ONE]);;

let l4_vctx_instN_bvar_strong_ind970 = prove
 (`!g0 e0 a0 k g1 g.
   l4_vctx_instN966 g0 e0 a0 k g1 g ==>
   (!env uvars i ty.
      l4_venv_wf966 env /\
      l4_vctx_strong970 env uvars g0 /\
      l4_vctx_strong970 env uvars g /\
      l4_vis_defeq_strong970 env uvars g0 e0 e0 a0 /\
      l4_vlookup961 g1 i ty ==>
      l4_vis_defeq_strong970 env uvars g
        (l4_vinst_var961 i e0 k) (l4_vinst_var961 i e0 k) (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vctx_instN_INDUCT966 THEN CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`] THEN
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THENL
   [ASM_SIMP_TAC [l4_vinst_var961;LT;l4_vliftN_zero961;GSYM l4_vinst0961;l4_vinst0_vlift966];
    REWRITE_TAC [l4_vinst_var961;LT;NOT_SUC;SUC_SUB1;GSYM l4_vinst0961;l4_vinst0_vlift966] THEN
    ASM_MESON_TAC [l4_vctx_strong_lookup970;l4_venv_wf_closed966;
                   l4_vis_defeq_strong_bvar970;l4_vis_defeq_strong_to_defeq970;
                   l4_vctx_strong_to_wf970;l4_vis_defeq_sort_r966]];
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`e0:l4_vexpr961`;`a0:l4_vexpr961`;
                        `k:num`;`g1:l4_vexpr961 list`;`g:l4_vexpr961 list`;`a:l4_vexpr961`] THEN
   DISCH_TAC THEN REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vlookup_CASES961] THEN
   REWRITE_TAC [injectivity "list";distinctness "num";injectivity "num"] THEN
   STRIP_TAC THEN l4_subst_vars_tac969 THENL
   [REWRITE_TAC [l4_vinst_var961;ARITH_RULE `0 < SUC k`;GSYM l4_vlift_vinst_lo970] THEN
    ASM_MESON_TAC [CONJUNCT1 l4_vlookup_RULES961;l4_vctx_strong_lookup970;l4_venv_wf_closed966;
                   l4_vis_defeq_strong_bvar970;l4_vis_defeq_strong_to_defeq970;
                   l4_vctx_strong_to_wf970;l4_vis_defeq_sort_r966];
    REWRITE_TAC [l4_vinst_var_succ966;GSYM l4_vlift_vinst_lo970] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_weak970 THEN ASM_SIMP_TAC [l4_venv_wf_closed966] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_strong970]) THEN ASM_REWRITE_TAC []]]);;

let l4_vis_defeq_strong_instN_ind970 = prove
 (`!env uvars g1 e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g1 e1 e2 ty ==>
   (!g0 e0 a0 k g.
      l4_venv_wf966 env /\
      l4_vctx_strong970 env uvars g0 /\
      l4_vctx_strong970 env uvars g /\
      l4_vis_defeq_strong970 env uvars g0 e0 e0 a0 /\
      l4_vctx_instN966 g0 e0 a0 k g1 g ==>
      l4_vis_defeq_strong970 env uvars g
        (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k) (l4_vinst961 ty e0 k))`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   ASM_MESON_TAC [l4_vctx_instN_bvar_strong_ind970];
   (* symm *)
   MESON_TAC [l4_vis_defeq_strong_symm970];
   (* trans *)
   MESON_TAC [l4_vis_defeq_strong_trans970];
   (* sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`c:l4_name`;`ci:l4_vconstant961`;`ls1:l4_vlevel961 list`;`k:num`]
     l4_closed_inst_const966) THEN
   ANTS_TAC THENL [ASM_SIMP_TAC [l4_venv_wf_closed966]; DISCH_TAC] THEN
   ASM_SIMP_TAC [l4_vclosedN_vinst_eq966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_SIMP_TAC [l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966];
   (* app *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g'
                   (l4_vinst961 dom e0 k) (l4_vinst961 dom e0 k) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom g) (CONS (l4_vinst961 dom e0 k) g')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970;l4_vctx_instN_succ966];
    MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vinst961 dom e0 k`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961;l4_vinst0_vinst_hi966]) THEN
    ASM_MESON_TAC []];
   (* lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g'
                   (l4_vinst961 dom1 e0 k) (l4_vinst961 dom2 e0 k) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom1 e0 k) g') /\
                 l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom2 e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom1 g) (CONS (l4_vinst961 dom1 e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom2 g) (CONS (l4_vinst961 dom2 e0 k) g')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970;l4_vctx_instN_succ966;
                   l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970];
    MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []];
   (* forall *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g'
                   (l4_vinst961 dom1 e0 k) (l4_vinst961 dom2 e0 k) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom1 e0 k) g') /\
                 l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom2 e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom1 g) (CONS (l4_vinst961 dom1 e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom2 g) (CONS (l4_vinst961 dom2 e0 k) g')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970;l4_vctx_instN_succ966;
                   l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970];
    MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []];
   (* conv *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`l4_vinst961 ty1 e0 k`] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* beta *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vinst961;l4_vinst0_vinst_hi966] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g'
                   (l4_vinst961 dom e0 k) (l4_vinst961 dom e0 k) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom g) (CONS (l4_vinst961 dom e0 k) g')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970;l4_vctx_instN_succ966];
    MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961;l4_vinst0_vinst_hi966]) THEN
    ASM_MESON_TAC []];
   (* eta *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vinst961;l4_vinst_var961;ARITH_RULE `0 < SUC k`;GSYM l4_vlift_vinst_lo970] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g'
                   (l4_vinst961 dom e0 k) (l4_vinst961 dom e0 k) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS (l4_vinst961 dom e0 k) g') /\
                 l4_vctx_instN966 g0 e0 a0 (SUC k) (CONS dom g) (CONS (l4_vinst961 dom e0 k) g')`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970;l4_vctx_instN_succ966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vinst961 dom e0 k) g')
                   (l4_vlift961 (l4_vinst961 dom e0 k))
                   (l4_vlift961 (l4_vinst961 dom e0 k)) (L4VSort961 u)`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g':l4_vexpr961 list`;
                   `l4_vinst961 dom e0 k`;`l4_vinst961 dom e0 k`;`L4VSort961 u`;
                   `l4_vinst961 dom e0 k`] l4_vis_defeq_strong_weak970) THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars
                   (CONS (l4_vlift961 (l4_vinst961 dom e0 k)) (CONS (l4_vinst961 dom e0 k) g')) /\
                 l4_vctx_instN966 g0 e0 a0 (SUC (SUC k))
                   (CONS (l4_vlift961 dom) (CONS dom g))
                   (CONS (l4_vlift961 (l4_vinst961 dom e0 k)) (CONS (l4_vinst961 dom e0 k) g'))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vctx_strong970];
     REWRITE_TAC [l4_vlift_vinst_lo970] THEN
     MATCH_MP_TAC l4_vctx_instN_succ966 THEN ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    REWRITE_TAC [l4_vlift_vinst_lo970;l4_vliftN_one_one_vinst_lo970] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961;l4_vlift_vinst_lo970]) THEN
    ASM_MESON_TAC []];
   (* proofIrrel *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_proof_irrel970 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vinst961]) THEN ASM_MESON_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`;`k:num`]
     l4_closed_inst_defeq966) THEN
   ANTS_TAC THENL [ASM_SIMP_TAC [l4_venv_wf_closed966]; STRIP_TAC] THEN
   ASM_SIMP_TAC [l4_vclosedN_vinst_eq966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_SIMP_TAC [l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966]]);;

let l4_vis_defeq_strong_instN970 = prove
 (`!env uvars g0 e0 a0 k g1 g e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g0 /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g0 e0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_defeq_strong970 env uvars g1 e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g
     (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k) (l4_vinst961 ty e0 k)`,
  MESON_TAC [l4_vis_defeq_strong_instN_ind970]);;

let l4_vis_defeq_strong_inst0970 = prove
 (`!env uvars g e0 a0 e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g e0 e0 a0 /\
   l4_vis_defeq_strong970 env uvars (CONS a0 g) e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g
     (l4_vinst0961 e1 e0) (l4_vinst0961 e2 e0) (l4_vinst0961 ty e0)`,
  REWRITE_TAC [l4_vinst0961] THEN
  MESON_TAC [l4_vis_defeq_strong_instN970;l4_vctx_instN_zero966]);;

let l4_vis_defeq_strong_defeqDF_l970 = prove
 (`!env uvars g dom1 dom2 u e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g dom1 dom2 (L4VSort961 u) /\
   l4_vis_defeq_strong970 env uvars (CONS dom1 g) e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars (CONS dom2 g) e1 e2 ty`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vlevel_wf961 uvars u` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970;l4_vctx_strong_to_wf970;l4_vis_defeq_sort_r966];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom2 dom2 (L4VSort961 u)` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom2 g)` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vctx_strong970]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom2 g)
                  (L4VBVar961 0) (L4VBVar961 0) (l4_vlift961 dom1)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`l4_vlift961 dom2`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`L4VSort961 u`;`dom2:l4_vexpr961`]
      l4_vis_defeq_strong_weak970) THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961];
    MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [l4_vlookup_RULES961] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom2:l4_vexpr961`;`dom2:l4_vexpr961`;`L4VSort961 u`;`dom2:l4_vexpr961`]
      l4_vis_defeq_strong_weak970) THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961]];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vlift961 dom1) (CONS dom2 g))
                  (l4_vliftN961 e1 1 1) (l4_vliftN961 e2 1 1) (l4_vliftN961 ty 1 1)`
    ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom1:l4_vexpr961) g`;
                  `e1:l4_vexpr961`;`e2:l4_vexpr961`;`ty:l4_vexpr961`;
                  `1`;`SUC 0`;`CONS (l4_vliftN961 dom1 1 0) (CONS dom2 g)`]
     l4_vis_defeq_strong_weakN970) THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;ONE;GSYM l4_vlift961;
                 l4_vctx_liftN_succ966;l4_vctx_liftN_one966];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom2:l4_vexpr961) g`;
                  `L4VBVar961 0`;`l4_vlift961 dom1`;
                  `l4_vliftN961 e1 1 1`;`l4_vliftN961 e2 1 1`;`l4_vliftN961 ty 1 1`]
     l4_vis_defeq_strong_inst0970) THEN
   ASM_SIMP_TAC [l4_vinst0_vliftN_one_one_bvar0970]]);;

(* ========================================================================= *)
(* 5. Equivalence of IsDefEq and IsDefEqStrong (Strong.lean:432-708)         *)
(* ========================================================================= *)

let l4_venv_strong970 = new_definition
 `l4_venv_strong970 env uvars e ty <=>
   l4_vis_defeq_strong970 env uvars [] e e ty /\
   (?u. l4_vis_defeq_strong970 env uvars [] ty ty (L4VSort961 u)) /\
   (!uvars' ls1 ls2.
      ALL (l4_vlevel_wf961 uvars') ls1 /\
      ALL (l4_vlevel_wf961 uvars') ls2 /\
      ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
      l4_vis_defeq_strong970 env uvars' []
        (l4_vinstL961 ls1 e) (l4_vinstL961 ls2 e) (l4_vinstL961 ls1 ty)) /\
   (!dom cod. e = L4VForallE961 dom cod ==>
      (?u. l4_vis_defeq_strong970 env uvars [] dom dom (L4VSort961 u)) /\
      (?v. l4_vis_defeq_strong970 env uvars [dom] cod cod (L4VSort961 v)))`;;

let l4_venv_on_types_strong970 = new_definition
 `l4_venv_on_types_strong970 env <=>
   (!c ci. l4_venv_lookup_const961 env c ci ==>
      ?u. l4_venv_strong970 env (l4_vc_uvars961 ci) (l4_vc_type961 ci) (L4VSort961 u)) /\
   (!df. l4_venv_has_defeq961 env df ==>
      l4_venv_strong970 env (l4_vdf_uvars961 df) (l4_vdf_lhs961 df) (l4_vdf_type961 df) /\
      l4_venv_strong970 env (l4_vdf_uvars961 df) (l4_vdf_rhs961 df) (l4_vdf_type961 df))`;;

let l4_forall_inv_strong_instL970 = prove
 (`!env uvars uvars0 g ls e dom cod ty.
   l4_venv_closed966 env /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   l4_vinstL961 ls e = L4VForallE961 dom cod /\
   l4_venv_strong970 env uvars0 e ty ==>
   (?u. l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u)) /\
   (?v. l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `e:l4_vexpr961` (cases "l4_vexpr961")) THEN
  REWRITE_TAC [l4_vinstL961;distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN l4_subst_vars_tac966 THEN
  UNDISCH_TAC `l4_venv_strong970 env uvars0 (L4VForallE961 a0 a1) ty` THEN
  REWRITE_TAC [l4_venv_strong970] THEN
  DISCH_THEN (MP_TAC o SPECL [`a0:l4_vexpr961`;`a1:l4_vexpr961`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC [] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u0:l4_vlevel961`) (X_CHOOSE_TAC `v0:l4_vlevel961`)) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars0:num`;`uvars:num`;`ls:l4_vlevel961 list`;
                 `[]:l4_vexpr961 list`;`a0:l4_vexpr961`;`a0:l4_vexpr961`;`L4VSort961 u0`]
    l4_vis_defeq_strong_instL970) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars0:num`;`uvars:num`;`ls:l4_vlevel961 list`;
                 `[a0:l4_vexpr961]`;`a1:l4_vexpr961`;`a1:l4_vexpr961`;`L4VSort961 v0`]
    l4_vis_defeq_strong_instL970) THEN
  ASM_REWRITE_TAC [MAP;l4_vinstL961] THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `l4_vinstL961 ls a0`;`l4_vinstL961 ls a0`;
                 `L4VSort961 (l4_vlevel_inst961 ls u0)`] l4_vis_defeq_closedN966) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970;l4_vctx_closed966]; ALL_TAC] THEN
  REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[l4_vinstL961 ls a0]`;
                 `l4_vinstL961 ls a1`;`l4_vinstL961 ls a1`;
                 `L4VSort961 (l4_vlevel_inst961 ls v0)`] l4_vis_defeq_closedN966) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_vctx_closed966;LENGTH] THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]; ALL_TAC] THEN
  REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN CONJ_TAC THENL
  [EXISTS_TAC `l4_vlevel_inst961 ls u0` THEN
   MATCH_MP_TAC l4_vis_defeq_strong_weak0970 THEN ASM_REWRITE_TAC [];
   EXISTS_TAC `l4_vlevel_inst961 ls v0` THEN
   SUBGOAL_THEN `l4_vctx_liftN966 (LENGTH (g:l4_vexpr961 list)) (SUC 0)
                   [l4_vinstL961 ls a0] (CONS (l4_vinstL961 ls a0) g)` ASSUME_TAC THENL
   [SUBGOAL_THEN `CONS (l4_vinstL961 ls a0) g =
                  CONS (l4_vliftN961 (l4_vinstL961 ls a0) (LENGTH g) 0) (APPEND g [])`
      SUBST1_TAC THENL
    [ASM_SIMP_TAC [APPEND_NIL;l4_vclosedN_vliftN_eq966;LE_0];
     MATCH_MP_TAC l4_vctx_liftN_succ966 THEN
     MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REFL_TAC];
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[l4_vinstL961 ls a0]`;
                   `l4_vinstL961 ls a1`;`l4_vinstL961 ls a1`;
                   `L4VSort961 (l4_vlevel_inst961 ls v0)`;
                   `LENGTH (g:l4_vexpr961 list)`;`SUC 0`;
                   `CONS (l4_vinstL961 ls a0) g`]
      l4_vis_defeq_strong_weakN970) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966;LE_REFL;l4_vliftN961]]]);;

let l4_vis_defeq_strong_forall_inv_ind970 = prove
 (`!env uvars g e1 e2 v.
   l4_vis_defeq_strong970 env uvars g e1 e2 v ==>
   (!dom cod.
      l4_venv_wf966 env /\
      l4_venv_on_types_strong970 env /\
      l4_vctx_strong970 env uvars g /\
      (e1 = L4VForallE961 dom cod \/ e2 = L4VForallE961 dom cod) ==>
      (?u. l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u)) /\
      (?w. l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 w)))`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   REWRITE_TAC [distinctness "l4_vexpr961";l4_forall_t966];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [injectivity "l4_vexpr961"] THEN STRIP_TAC THEN l4_subst_vars_tac966 THENL
   [ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970];
    CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970];
     EXISTS_TAC `v:l4_vlevel961` THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970;l4_vis_defeq_strong_defeqDF_l970]]];
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
    SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_vctx_strong970]; ALL_TAC] THEN
    SUBGOAL_THEN `(?u0. l4_vis_defeq_strong970 env uvars (CONS dom g) dom0 dom0 (L4VSort961 u0)) /\
                  (?w0. l4_vis_defeq_strong970 env uvars (CONS dom0 (CONS dom g)) cod0 cod0 (L4VSort961 w0))`
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom_q dom_q (L4VSort961 u0)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `arg:l4_vexpr961`;`dom:l4_vexpr961`;`0`;
                    `CONS (dom:l4_vexpr961) g`;`g:l4_vexpr961 list`;
                    `dom0:l4_vexpr961`;`dom0:l4_vexpr961`;`L4VSort961 u0`]
       l4_vis_defeq_strong_instN970) THEN
     ASM_SIMP_TAC [l4_vctx_instN_zero966;l4_vinst961];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `u0:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `w0:l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `arg:l4_vexpr961`;`dom:l4_vexpr961`;`1`;
                    `CONS (dom0:l4_vexpr961) (CONS dom g)`;
                    `CONS (l4_vinst961 dom0 arg 0) g`;
                    `cod0:l4_vexpr961`;`cod0:l4_vexpr961`;`L4VSort961 w0`]
       l4_vis_defeq_strong_instN970) THEN
     REWRITE_TAC [l4_vinst961;ONE] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [GSYM ONE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [l4_vctx_strong970];
      REWRITE_TAC [ONE] THEN MATCH_MP_TAC l4_vctx_instN_succ966 THEN
      REWRITE_TAC [l4_vctx_instN_zero966]]]];
   (* eta *)
   REWRITE_TAC [distinctness "l4_vexpr961"] THEN MESON_TAC [];
   (* proofIrrel *)
   MESON_TAC [];
   (* extra *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC l4_forall_inv_strong_instL970 THEN
    MAP_EVERY EXISTS_TAC [`l4_vdf_uvars961 df`;`ls:l4_vlevel961 list`;
                          `l4_vdf_lhs961 df`;`l4_vdf_type961 df`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970]) THEN
    ASM_MESON_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_forall_inv_strong_instL970 THEN
    MAP_EVERY EXISTS_TAC [`l4_vdf_uvars961 df`;`ls:l4_vlevel961 list`;
                          `l4_vdf_rhs961 df`;`l4_vdf_type961 df`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970]) THEN
    ASM_MESON_TAC [l4_venv_wf_closed966]]]);;

let l4_vis_defeq_strong_is_type_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_venv_wf966 env /\
   l4_venv_on_types_strong970 env /\
   l4_vctx_strong970 env uvars g ==>
   ?u. l4_vis_defeq_strong970 env uvars g ty ty (L4VSort961 u)`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* symm *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ASM_MESON_TAC [];
   (* trans *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ASM_MESON_TAC [];
   (* sort *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `L4VLSucc961 (L4VLSucc961 l1)` THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   (* const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970];
   (* app *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `v:l4_vlevel961` THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `L4VLIMax961 u v` THEN
   MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `L4VLSucc961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   (* conv *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `v:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* eta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ASM_MESON_TAC [];
   (* proofIrrel *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `L4VLZero961` THEN ASM_REWRITE_TAC [];
   (* extra *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `u:l4_vlevel961` THEN
   MATCH_MP_TAC l4_vis_defeq_strong_weak0970 THEN
   CONJ_TAC THENL [ASM_MESON_TAC [l4_venv_wf_closed966]; ASM_REWRITE_TAC []]]);;

let l4_vis_defeq_strong_instDF_aux970 = prove
 (`!env uvars g dom cod f f' a a' u v.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vlevel_wf961 uvars u /\
   l4_vlevel_wf961 uvars v /\
   l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u) /\
   l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v) /\
   l4_vis_defeq_strong970 env uvars (CONS dom g) f f' cod /\
   l4_vis_defeq_strong970 env uvars g a a' dom /\
   l4_vis_defeq_strong970 env uvars g
     (l4_vinst0961 cod a) (l4_vinst0961 cod a') (L4VSort961 v) ==>
   l4_vis_defeq_strong970 env uvars g
     (l4_vinst0961 f a) (l4_vinst0961 f' a') (l4_vinst0961 cod a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g a a dom /\
                l4_vis_defeq_strong970 env uvars g a' a' dom /\
                l4_vis_defeq_strong970 env uvars (CONS dom g) f f cod /\
                l4_vis_defeq_strong970 env uvars (CONS dom g) f' f' cod`
    STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                  (l4_vinst0961 f a) (L4VApp961 (L4VLam961 dom f) a) (l4_vinst0961 cod a)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
   MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THEN
   ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_inst0970];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                  (L4VApp961 (L4VLam961 dom f) a)
                  (L4VApp961 (L4VLam961 dom f') a') (l4_vinst0961 cod a)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                  (L4VApp961 (L4VLam961 dom f') a') (l4_vinst0961 f' a') (l4_vinst0961 cod a)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`v:l4_vlevel961`;`l4_vinst0961 cod a'`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_strong_symm970];
    MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970;l4_vis_defeq_strong_inst0970]];
   ASM_MESON_TAC [l4_vis_defeq_strong_trans970]]);;

let l4_vis_defeq_strong_instDF970 = prove
 (`!env uvars g dom cod f f' a a' u v.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vlevel_wf961 uvars u /\
   l4_vlevel_wf961 uvars v /\
   l4_vis_defeq_strong970 env uvars g dom dom (L4VSort961 u) /\
   l4_vis_defeq_strong970 env uvars (CONS dom g) cod cod (L4VSort961 v) /\
   l4_vis_defeq_strong970 env uvars (CONS dom g) f f' cod /\
   l4_vis_defeq_strong970 env uvars g a a' dom ==>
   l4_vis_defeq_strong970 env uvars g
     (l4_vinst0961 f a) (l4_vinst0961 f' a') (l4_vinst0961 cod a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                  (l4_vinst0961 cod a) (l4_vinst0961 cod a') (L4VSort961 v)`
    ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `dom:l4_vexpr961`;`L4VSort961 v`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                  `a:l4_vexpr961`;`a':l4_vexpr961`;`u:l4_vlevel961`;`L4VLSucc961 v`]
     l4_vis_defeq_strong_instDF_aux970) THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vinst0961;l4_vinst961] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
   ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
   MATCH_MP_TAC l4_vis_defeq_strong_instDF_aux970 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   ASM_REWRITE_TAC []]);;

(* EqUpToLevels.defeq *)
let l4_veq_up_to_levels_defeq_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   (!e1' e2'.
      l4_venv_wf966 env /\
      l4_venv_on_types_strong970 env /\
      l4_vctx_strong970 env uvars g /\
      l4_veq_up_to_levels970 uvars e1 e1' /\
      l4_veq_up_to_levels970 uvars e2 e2' ==>
      l4_vis_defeq_strong970 env uvars g e1' e2' ty)`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_bvar_inv970] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* symm *)
   MESON_TAC [l4_vis_defeq_strong_symm970];
   (* trans *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars e2 e2` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_veq_up_to_levels_refl970;l4_vctx_strong_level_wf970];
    MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `e2:l4_vexpr961` THEN
    CONJ_TAC THEN ASM_MESON_TAC []];
   (* sort *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_sort_inv970] THEN STRIP_TAC THEN l4_subst_vars_tac966 THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`L4VLSucc961 (L4VLSucc961 l1)`;`L4VSort961 (L4VLSucc961 l')`] THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
    MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
    ASM_SIMP_TAC [l4_vlevel_wf961;l4_vlevel_succ_equiv970];
    MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [l4_vlevel_equiv_symm961;l4_vlevel_equiv_trans961]];
   (* const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_const_inv970] THEN STRIP_TAC THEN l4_subst_vars_tac966 THEN
   UNDISCH_TAC `l4_venv_on_types_strong970 env` THEN REWRITE_TAC [l4_venv_on_types_strong970] THEN
   DISCH_THEN (MP_TAC o SPECL [`c:l4_name`;`ci:l4_vconstant961`] o CONJUNCT1) THEN
   ASM_REWRITE_TAC [l4_venv_strong970] THEN
   DISCH_THEN (X_CHOOSE_THEN `u0:l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `ALL2 l4_vlevel_equiv961 ls' ls''` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_all2_vlevel_equiv_symm970;l4_all2_vlevel_equiv_trans970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars []
                   (l4_vinstL961 ls' (l4_vc_type961 ci))
                   (l4_vinstL961 ls'' (l4_vc_type961 ci))
                   (L4VSort961 (l4_vlevel_inst961 ls' u0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPECL [`uvars:num`;`ls':l4_vlevel961 list`;`ls'':l4_vlevel961 list`]) THEN
    ASM_SIMP_TAC [l4_vinstL961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars []
                   (l4_vinstL961 ls1 (l4_vc_type961 ci))
                   (l4_vinstL961 ls' (l4_vc_type961 ci))
                   (L4VSort961 (l4_vlevel_inst961 ls1 u0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPECL [`uvars:num`;`ls1:l4_vlevel961 list`;`ls':l4_vlevel961 list`]) THEN
    ASM_SIMP_TAC [l4_vinstL961];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`l4_vlevel_inst961 ls1 u0`;`l4_vinstL961 ls' (l4_vc_type961 ci)`] THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
    MATCH_MP_TAC l4_vis_defeq_strong_weak0970 THEN ASM_SIMP_TAC [l4_venv_wf_closed966];
    MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN
    EXISTS_TAC `l4_vlevel_inst961 ls' u0` THEN
    ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966] THEN
    ASM_MESON_TAC [l4_all2_length_eq970]];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `f1:l4_vexpr961`;`f2:l4_vexpr961`;
                        `a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_app_inv970] THEN STRIP_TAC THEN l4_subst_vars_tac966 THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars a2 a2` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `a1:l4_vexpr961`;`a2:l4_vexpr961`;`dom:l4_vexpr961`]
      l4_veq_up_to_levels_refl970) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g a' a2 dom /\
                 l4_vis_defeq_strong970 env uvars g f' f'' (L4VForallE961 dom cod) /\
                 l4_vis_defeq_strong970 env uvars g a' a'' dom`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g a' a1 dom` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `a2:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`v:l4_vlevel961`;`l4_vinst0961 cod a'`] THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`L4VSort961 v`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                   `a':l4_vexpr961`;`a1:l4_vexpr961`;`u:l4_vlevel961`;`L4VLSucc961 v`]
      l4_vis_defeq_strong_instDF970) THEN
    ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vinst0961;l4_vinst961] THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
     SIMP_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`L4VSort961 v`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                   `a':l4_vexpr961`;`a'':l4_vexpr961`;`u:l4_vlevel961`;`L4VLSucc961 v`]
      l4_vis_defeq_strong_instDF970) THEN
    ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vinst0961;l4_vinst961] THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
     SIMP_TAC []]];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_lam_inv970] THEN STRIP_TAC THEN l4_subst_vars_tac966 THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars dom1 dom1 /\
                 l4_veq_up_to_levels970 uvars dom2 dom2` STRIP_ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`L4VSort961 u`]
      l4_veq_up_to_levels_refl970) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom2 (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom1 dom'' (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom' dom'' (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom1 (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vctx_strong970] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `u:l4_vlevel961` THEN MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN
    EXISTS_TAC `dom2:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom1 g) body' body'' cod` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`L4VLIMax961 u v`;`L4VForallE961 dom' cod`] THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
    MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
    MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN TRY (MATCH_MP_TAC l4_vis_defeq_strong_symm970) THEN
    ASM_REWRITE_TAC []];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_forall_inv970] THEN STRIP_TAC THEN l4_subst_vars_tac966 THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars dom1 dom1 /\
                 l4_veq_up_to_levels970 uvars dom2 dom2` STRIP_ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`L4VSort961 u`]
      l4_veq_up_to_levels_refl970) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom2 (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom1 dom'' (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom' dom'' (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom1 (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `dom2:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vctx_strong970] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `u:l4_vlevel961` THEN MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN
    EXISTS_TAC `dom2:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom1 g) cod' cod'' (L4VSort961 v)`
     ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
   MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN TRY (MATCH_MP_TAC l4_vis_defeq_strong_symm970) THEN
   ASM_REWRITE_TAC [];
   (* conv *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`ty1:l4_vexpr961`] THEN
   ASM_SIMP_TAC [];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_app_inv970] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `f_tmp:l4_vexpr961`
             (X_CHOOSE_THEN `arg':l4_vexpr961`
               (CONJUNCTS_THEN2 SUBST_ALL_TAC
                 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))
           ASSUME_TAC)))) THEN
   REWRITE_TAC [l4_veq_up_to_levels_lam_inv970] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vctx_strong970] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars dom dom /\
                 l4_veq_up_to_levels970 uvars arg arg /\
                 l4_veq_up_to_levels970 uvars cod cod /\
                 l4_veq_up_to_levels970 uvars (l4_vinst0961 cod arg) (l4_vinst0961 cod arg)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `dom:l4_vexpr961`;`dom:l4_vexpr961`;`L4VSort961 u`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `arg:l4_vexpr961`;`arg:l4_vexpr961`;`dom:l4_vexpr961`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                    `cod:l4_vexpr961`;`cod:l4_vexpr961`;`L4VSort961 v`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `l4_vinst0961 cod arg`;`l4_vinst0961 cod arg`;`L4VSort961 v`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g arg' arg dom /\
                 l4_vis_defeq_strong970 env uvars (CONS dom g) body' body' cod`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                   (l4_vinst0961 cod arg') (l4_vinst0961 cod arg) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars g
                   (l4_vinst0961 body' arg') e2' (l4_vinst0961 cod arg)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC [l4_veq_up_to_levels_inst0970]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN
   EXISTS_TAC `l4_vinst0961 body' arg'` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`v:l4_vlevel961`;`l4_vinst0961 cod arg'`] THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom' g) cod cod (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS dom' g) body' body' cod /\
                 l4_vis_defeq_strong970 env uvars g arg' arg' dom'`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
     MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
     CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
      MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`dom:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN EXISTS_TAC `arg:l4_vexpr961` THEN
       ASM_REWRITE_TAC []]]];
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom' (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom' g)` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vctx_strong970] THEN ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                     `arg':l4_vexpr961`;`dom':l4_vexpr961`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                     `L4VSort961 v`] l4_vis_defeq_strong_inst0970) THEN
      ASM_SIMP_TAC [l4_vinst0961;l4_vinst961];
      MATCH_MP_TAC l4_vis_defeq_strong_inst0970 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
      ASM_REWRITE_TAC []]]];
   (* eta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_veq_up_to_levels_lam_inv970] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `dom':l4_vexpr961`
             (X_CHOOSE_THEN `app_tmp:l4_vexpr961`
               (CONJUNCTS_THEN2 SUBST_ALL_TAC
                 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))
           ASSUME_TAC)))) THEN
   REWRITE_TAC [l4_veq_up_to_levels_app_inv970;l4_veq_up_to_levels_bvar_inv970] THEN
   DISCH_THEN (X_CHOOSE_THEN `el':l4_vexpr961`
     (X_CHOOSE_THEN `bv_tmp:l4_vexpr961`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vctx_strong970] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars dom dom /\
                 l4_veq_up_to_levels970 uvars e e /\
                 l4_veq_up_to_levels970 uvars (l4_vlift961 e) (l4_vlift961 e)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `dom:l4_vexpr961`;`dom:l4_vexpr961`;`L4VSort961 u`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `e:l4_vexpr961`;`e:l4_vexpr961`;`L4VForallE961 dom cod`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                    `l4_vlift961 e`;`l4_vlift961 e`;
                    `L4VForallE961 (l4_vlift961 dom) (l4_vliftN961 cod 1 1)`]
       l4_veq_up_to_levels_refl970) THEN ANTS_TAC THENL [ASM_MESON_TAC [l4_vctx_strong_level_wf970]; SIMP_TAC []]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom' dom (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars (CONS dom g) el' (l4_vlift961 e)
                   (L4VForallE961 (l4_vlift961 dom) (l4_vliftN961 cod 1 1)) /\
                 l4_vis_defeq_strong970 env uvars g e e2' (L4VForallE961 dom cod)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom g)
                   (L4VApp961 el' (L4VBVar961 0))
                   (L4VApp961 (l4_vlift961 e) (L4VBVar961 0)) cod`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                   `u:l4_vlevel961`;`v:l4_vlevel961`;
                   `l4_vlift961 dom`;`l4_vliftN961 cod 1 1`;
                   `el':l4_vexpr961`;`l4_vlift961 e`;
                   `L4VBVar961 0`;`L4VBVar961 0`] l4_vis_defeq_strong_app970) THEN
    REWRITE_TAC [l4_vinst0_vliftN_one_one_bvar0970] THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_REWRITE_TAC [CONJUNCT1 l4_vlookup_RULES961];
     SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom dom' (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars (CONS dom' g) cod cod (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS dom g)
                   (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))
                   (L4VApp961 el' (L4VBVar961 0)) cod /\
                 l4_vis_defeq_strong970 env uvars (CONS dom' g)
                   (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))
                   (L4VApp961 el' (L4VBVar961 0)) cod`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
     CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
      MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
      CONJ_TAC THENL
      [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
       MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
       MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN
       ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
       ASM_REWRITE_TAC []]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                   (L4VLam961 dom' (L4VApp961 el' (L4VBVar961 0)))
                   (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0)))
                   (L4VForallE961 dom cod)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
    MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN
    EXISTS_TAC `L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `e:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC []];
   (* proofIrrel *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_proof_irrel970 THEN
   ASM_SIMP_TAC [];
   (* extra *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_veq_up_to_levels970 uvars
                   (l4_vinstL961 ls (l4_vdf_lhs961 df))
                   (l4_vinstL961 ls (l4_vdf_lhs961 df)) /\
                 l4_veq_up_to_levels970 uvars
                   (l4_vinstL961 ls (l4_vdf_rhs961 df))
                   (l4_vinstL961 ls (l4_vdf_rhs961 df))`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                    `l4_vinstL961 ls (l4_vdf_lhs961 df)`;
                    `l4_vinstL961 ls (l4_vdf_lhs961 df)`;
                    `l4_vinstL961 ls (l4_vdf_type961 df)`]
       l4_veq_up_to_levels_refl970) THEN
     ASM_SIMP_TAC [l4_vctx_level_wf966];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                    `l4_vinstL961 ls (l4_vdf_rhs961 df)`;
                    `l4_vinstL961 ls (l4_vdf_rhs961 df)`;
                    `l4_vinstL961 ls (l4_vdf_type961 df)`]
       l4_veq_up_to_levels_refl970) THEN
     ASM_SIMP_TAC [l4_vctx_level_wf966]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars []` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vctx_strong970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars [] e1'
                   (l4_vinstL961 ls (l4_vdf_lhs961 df)) (l4_vinstL961 ls (l4_vdf_type961 df)) /\
                 l4_vis_defeq_strong970 env uvars [] e2'
                   (l4_vinstL961 ls (l4_vdf_rhs961 df)) (l4_vinstL961 ls (l4_vdf_type961 df))`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_weak0970 THEN ASM_SIMP_TAC [l4_venv_wf_closed966] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN
   EXISTS_TAC `l4_vinstL961 ls (l4_vdf_lhs961 df)` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN
   EXISTS_TAC `l4_vinstL961 ls (l4_vdf_rhs961 df)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC []]]);;

let l4_veq_up_to_levels_defeq970 = prove
 (`!env uvars g e1 e2 e1' e2' ty.
   l4_venv_wf966 env /\
   l4_venv_on_types_strong970 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty /\
   l4_veq_up_to_levels970 uvars e1 e1' /\
   l4_veq_up_to_levels970 uvars e2 e2' ==>
   l4_vis_defeq_strong970 env uvars g e1' e2' ty`,
  MESON_TAC [l4_veq_up_to_levels_defeq_ind970]);;

let l4_vctx_strong_cons970 = prove
 (`!env uvars g a b u.
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g a b (L4VSort961 u) ==>
   l4_vctx_strong970 env uvars (CONS a g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vctx_strong970] THEN
  ASM_REWRITE_TAC [] THEN EXISTS_TAC `u:l4_vlevel961` THEN
  MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN
  EXISTS_TAC `b:l4_vexpr961` THEN ASM_REWRITE_TAC []);;

let l4_vctx_strong_sort_r970 = prove
 (`!env uvars g e1 e2 u.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq_strong970 env uvars g e1 e2 (L4VSort961 u) ==>
   l4_vlevel_wf961 uvars u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_sort_r966 THEN
  MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
  ASM_SIMP_TAC [l4_vctx_strong_to_wf970;l4_vis_defeq_strong_to_defeq970]);;

let l4_vctx_strong_defeq_sort_r970 = prove
 (`!env uvars g e1 e2 u.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 (L4VSort961 u) ==>
   l4_vlevel_wf961 uvars u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_sort_r966 THEN
  MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
  ASM_SIMP_TAC [l4_vctx_strong_to_wf970]);;

(* IsDefEq.strong' *)
let l4_vis_defeq_to_strong_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_venv_wf966 env /\
   l4_venv_on_types_strong970 env /\
   l4_vctx_strong970 env uvars g ==>
   l4_vis_defeq_strong970 env uvars g e1 e2 ty`,
  MATCH_MP_TAC l4_vis_defeq_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;`i:num`;`ty:l4_vexpr961`]
     l4_vctx_strong_lookup970) THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966] THEN DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961`) THEN
   MATCH_MP_TAC l4_vis_defeq_strong_bvar970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`ty:l4_vexpr961`;`ty:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [];
   (* symm *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_SIMP_TAC [];
   (* trans *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `e2:l4_vexpr961` THEN
   ASM_SIMP_TAC [];
   (* sort *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [];
   (* const *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_venv_on_types_strong970 env` THEN REWRITE_TAC [l4_venv_on_types_strong970] THEN
   DISCH_THEN (MP_TAC o SPECL [`c:l4_name`;`cinfo:l4_vconstant961`] o CONJUNCT1) THEN
   ASM_REWRITE_TAC [l4_venv_strong970;l4_vinstL961] THEN
   DISCH_THEN (X_CHOOSE_THEN `u0:l4_vlevel961`
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (K ALL_TAC)
         (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))))) THEN
   DISCH_THEN (MP_TAC o SPECL [`uvars:num`;`ls1:l4_vlevel961 list`;`ls2:l4_vlevel961 list`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN
   EXISTS_TAC `l4_vlevel_inst961 ls1 u0` THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966];
   (* app *)
   TRY (X_GEN_TAC `env:l4_venv961` THEN X_GEN_TAC `uvars:num`) THEN
   MAP_EVERY X_GEN_TAC [`g:l4_vexpr961 list`;`f1:l4_vexpr961`;`f2:l4_vexpr961`;
                        `a1:l4_vexpr961`;`a2:l4_vexpr961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g f1 f2 (L4VForallE961 dom cod) /\
                 l4_vis_defeq_strong970 env uvars g a1 a2 dom` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f1:l4_vexpr961`;`f2:l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_strong_is_type_ind970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `w:l4_vlevel961`) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VForallE961 dom cod`;`L4VForallE961 dom cod`;`L4VSort961 w`]
     l4_vis_defeq_strong_forall_inv_ind970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`dom:l4_vexpr961`;`cod:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_cons970 THEN
    MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`dom:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom:l4_vexpr961) g`;`cod:l4_vexpr961`;`cod:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `dom:l4_vexpr961`;`L4VSort961 v`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                   `a1:l4_vexpr961`;`a2:l4_vexpr961`;`u:l4_vlevel961`;`L4VLSucc961 v`]
      l4_vis_defeq_strong_instDF970) THEN
    ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vinst0961;l4_vinst961] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
    ASM_REWRITE_TAC [l4_vlevel_equiv_refl961]];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom1 dom2 (L4VSort961 u)` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_cons970 THEN
    MAP_EVERY EXISTS_TAC [`dom2:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom1 g) b1 b2 cod` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom1:l4_vexpr961) g`;
                  `b1:l4_vexpr961`;`b2:l4_vexpr961`;`cod:l4_vexpr961`]
     l4_vis_defeq_strong_is_type_ind970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `v:l4_vlevel961`) THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom1:l4_vexpr961) g`;`cod:l4_vexpr961`;`cod:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
    MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC []];
   (* forall *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom1 dom2 (L4VSort961 u)` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom1 g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_cons970 THEN
    MAP_EVERY EXISTS_TAC [`dom2:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom1 g) cod1 cod2 (L4VSort961 v)`
     ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom1:l4_vexpr961) g`;`cod1:l4_vexpr961`;`cod2:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_defeqDF_l970 THEN
    MAP_EVERY EXISTS_TAC [`dom1:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC []];
   (* conv *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`ty1:l4_vexpr961`] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_defeq_sort_r970 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`ty1:l4_vexpr961`;`ty2:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [];
    ASM_SIMP_TAC []];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g arg arg dom` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `arg:l4_vexpr961`;`arg:l4_vexpr961`;`dom:l4_vexpr961`]
     l4_vis_defeq_strong_is_type_ind970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961`) THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_cons970 THEN
    MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS dom g) body body cod` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                  `body:l4_vexpr961`;`body:l4_vexpr961`;`cod:l4_vexpr961`]
     l4_vis_defeq_strong_is_type_ind970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `v:l4_vlevel961`) THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`dom:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom:l4_vexpr961) g`;`cod:l4_vexpr961`;`cod:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `arg:l4_vexpr961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;`cod:l4_vexpr961`;
                    `L4VSort961 v`] l4_vis_defeq_strong_inst0970) THEN
     ASM_SIMP_TAC [l4_vinst0961;l4_vinst961];
     MATCH_MP_TAC l4_vis_defeq_strong_inst0970 THEN EXISTS_TAC `dom:l4_vexpr961` THEN
     ASM_REWRITE_TAC []]];
   (* eta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g e e (L4VForallE961 dom cod)` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `e:l4_vexpr961`;`e:l4_vexpr961`;`L4VForallE961 dom cod`]
     l4_vis_defeq_strong_is_type_ind970) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `w:l4_vlevel961`) THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VForallE961 dom cod`;`L4VForallE961 dom cod`;`L4VSort961 w`]
     l4_vis_defeq_strong_forall_inv_ind970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`dom:l4_vexpr961`;`cod:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_strong_cons970 THEN
    MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`u:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vlevel_wf961 uvars u /\ l4_vlevel_wf961 uvars v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`g:l4_vexpr961 list`;`dom:l4_vexpr961`;`dom:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vctx_strong_sort_r970 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_venv961`;`CONS (dom:l4_vexpr961) g`;`cod:l4_vexpr961`;`cod:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
    REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                    `cod:l4_vexpr961`;`cod:l4_vexpr961`;`L4VSort961 v`;
                    `1`;`SUC 0`;`CONS (l4_vliftN961 dom 1 0) (CONS dom g)`]
       l4_vis_defeq_strong_weakN970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;ONE;GSYM l4_vlift961;l4_vliftN961;
                   l4_vctx_liftN_succ966;l4_vctx_liftN_one966];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `e:l4_vexpr961`;`e:l4_vexpr961`;`L4VForallE961 dom cod`;`dom:l4_vexpr961`]
       l4_vis_defeq_strong_weak970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961;ONE];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `dom:l4_vexpr961`;`dom:l4_vexpr961`;`L4VSort961 u`;`dom:l4_vexpr961`]
       l4_vis_defeq_strong_weak970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961]]];
   (* proofIrrel *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_proof_irrel970 THEN ASM_SIMP_TAC [];
   (* extra *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_venv_on_types_strong970 env` THEN REWRITE_TAC [l4_venv_on_types_strong970] THEN
   DISCH_THEN (MP_TAC o SPEC `df:l4_vdefeq961` o CONJUNCT2) THEN
   ASM_REWRITE_TAC [l4_venv_strong970] THEN
   DISCH_THEN (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u0:l4_vlevel961`) (K ALL_TAC)))
     (ASSUME_TAC o CONJUNCT1)) THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars []
                   (l4_vinstL961 ls (l4_vdf_type961 df))
                   (l4_vinstL961 ls (l4_vdf_type961 df))
                   (L4VSort961 (l4_vlevel_inst961 ls u0)) /\
                 l4_vis_defeq_strong970 env uvars []
                   (l4_vinstL961 ls (l4_vdf_lhs961 df))
                   (l4_vinstL961 ls (l4_vdf_lhs961 df))
                   (l4_vinstL961 ls (l4_vdf_type961 df)) /\
                 l4_vis_defeq_strong970 env uvars []
                   (l4_vinstL961 ls (l4_vdf_rhs961 df))
                   (l4_vinstL961 ls (l4_vdf_rhs961 df))
                   (l4_vinstL961 ls (l4_vdf_type961 df))`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`uvars:num`;`ls:l4_vlevel961 list`;
                    `[]:l4_vexpr961 list`;`l4_vdf_type961 df`;`l4_vdf_type961 df`;`L4VSort961 u0`]
       l4_vis_defeq_strong_instL970) THEN ASM_SIMP_TAC [MAP;l4_vinstL961];
     MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`uvars:num`;`ls:l4_vlevel961 list`;
                    `[]:l4_vexpr961 list`;`l4_vdf_lhs961 df`;`l4_vdf_lhs961 df`;`l4_vdf_type961 df`]
       l4_vis_defeq_strong_instL970) THEN ASM_SIMP_TAC [MAP];
     MP_TAC (SPECL [`env:l4_venv961`;`l4_vdf_uvars961 df`;`uvars:num`;`ls:l4_vlevel961 list`;
                    `[]:l4_vexpr961 list`;`l4_vdf_rhs961 df`;`l4_vdf_rhs961 df`;`l4_vdf_type961 df`]
       l4_vis_defeq_strong_instL970) THEN ASM_SIMP_TAC [MAP]];
    MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN
    EXISTS_TAC `l4_vlevel_inst961 ls u0` THEN
    ASM_SIMP_TAC [l4_vlevel_inst_wf_any966;l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966]]]);;

let l4_vctx_strong_of_wf'970 = prove
 (`!g env uvars.
   l4_venv_wf966 env /\ l4_venv_on_types_strong970 env /\ l4_vctx_wf966 env uvars g ==>
   l4_vctx_strong970 env uvars g`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [FORALL_SIMP;l4_vctx_wf966;l4_vctx_strong970;l4_vis_type961;l4_vhas_type961] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vctx_strong970 env uvars t` ASSUME_TAC THENL
  [ASM_MESON_TAC []; ASM_REWRITE_TAC []] THEN
  EXISTS_TAC `u:l4_vlevel961` THEN
  ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970]);;

let l4_venv_strong_mono970 = prove
 (`!env1 env2 uvars e ty.
   l4_venv_ordered961 env1 env2 /\ l4_venv_strong970 env1 uvars e ty ==>
   l4_venv_strong970 env2 uvars e ty`,
  REWRITE_TAC [l4_venv_strong970] THEN MESON_TAC [l4_vis_defeq_strong_mono970]);;

let l4_venv_strong_of_has_type970 = prove
 (`!env uvars e ty.
   l4_venv_wf966 env /\
   l4_venv_on_types_strong970 env /\
   l4_vhas_type961 env uvars [] e ty ==>
   l4_venv_strong970 env uvars e ty`,
  REWRITE_TAC [l4_vhas_type961;l4_venv_strong970] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_vctx_strong970];
   ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_vis_defeq_strong_is_type_ind970;l4_vctx_strong970];
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars [] e e ty` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_vctx_strong970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars' []
                   (l4_vinstL961 ls1 e) (l4_vinstL961 ls1 e) (l4_vinstL961 ls1 ty)`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`uvars':num`;`ls1:l4_vlevel961 list`;
                   `[]:l4_vexpr961 list`;`e:l4_vexpr961`;`e:l4_vexpr961`;`ty:l4_vexpr961`]
      l4_vis_defeq_strong_instL970) THEN ASM_SIMP_TAC [MAP];
    MATCH_MP_TAC l4_veq_up_to_levels_defeq970 THEN
    MAP_EVERY EXISTS_TAC [`l4_vinstL961 ls1 e`;`l4_vinstL961 ls1 e`] THEN
    ASM_REWRITE_TAC [l4_vctx_strong970] THEN
    ASM_MESON_TAC [l4_veq_up_to_levels_refl970;l4_vctx_level_wf966;l4_veq_up_to_levels_instL970]];
   ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_vis_defeq_strong_forall_inv_ind970;
                  l4_vctx_strong970];
   ASM_MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_vis_defeq_strong_forall_inv_ind970;
                  l4_vctx_strong970]]);;

let l4_venv_wf_on_types_strong970 = prove
 (`!env. l4_venv_wf966 env ==> l4_venv_on_types_strong970 env`,
  MATCH_MP_TAC l4_venv_wf_STRONG_INDUCT966 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_venv_on_types_strong970;l4_venv_lookup_const961;l4_venv_has_defeq961;
                l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_venv_on_types_strong970] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c_q:l4_name`;`ci_q:l4_vconstant961`] THEN
    REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;PAIR_EQ] THEN
    STRIP_TAC THEN l4_subst_vars_tac966 THENL
    [RULE_ASSUM_TAC (REWRITE_RULE [l4_vconstant_wf966;l4_vis_type961]) THEN
     REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
     FIRST_X_ASSUM (X_CHOOSE_TAC `u0:l4_vlevel961`) THEN
     EXISTS_TAC `u0:l4_vlevel961` THEN
     MATCH_MP_TAC l4_venv_strong_mono970 THEN EXISTS_TAC `L4VEnv961 cs dfs` THEN
     REWRITE_TAC [l4_venv_cons_const_ordered966] THEN
     MATCH_MP_TAC l4_venv_strong_of_has_type970 THEN ASM_REWRITE_TAC [];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970;l4_venv_lookup_const961;
                                   l4_venv_consts_list961]) THEN
     ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_strong_mono970]];
    X_GEN_TAC `df_q:l4_vdefeq961` THEN
    REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970;l4_venv_has_defeq961;
                                  l4_venv_defeqs_list961]) THEN
    ASM_MESON_TAC [l4_venv_cons_const_ordered966;l4_venv_strong_mono970]];
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_venv_on_types_strong970] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970;l4_venv_lookup_const961;
                                  l4_venv_consts_list961]) THEN
    ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_strong_mono970];
    X_GEN_TAC `df_q:l4_vdefeq961` THEN
    REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM] THEN
    STRIP_TAC THEN l4_subst_vars_tac966 THENL
    [RULE_ASSUM_TAC (REWRITE_RULE [l4_vdefeq_wf966]) THEN
     CONJ_TAC THEN MATCH_MP_TAC l4_venv_strong_mono970 THEN
     EXISTS_TAC `L4VEnv961 cs dfs` THEN REWRITE_TAC [l4_venv_cons_defeq_ordered966] THEN
     MATCH_MP_TAC l4_venv_strong_of_has_type970 THEN ASM_REWRITE_TAC [];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_venv_on_types_strong970;l4_venv_has_defeq961;
                                   l4_venv_defeqs_list961]) THEN
     ASM_MESON_TAC [l4_venv_cons_defeq_ordered966;l4_venv_strong_mono970]]]]);;

let l4_vctx_strong_of_wf970 = prove
 (`!env uvars g.
   l4_venv_wf966 env /\ l4_vctx_wf966 env uvars g ==>
   l4_vctx_strong970 env uvars g`,
  MESON_TAC [l4_vctx_strong_of_wf'970;l4_venv_wf_on_types_strong970]);;

let l4_vis_defeq_strong_thm970 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g e1 e2 ty`,
  MESON_TAC [l4_vis_defeq_to_strong_ind970;l4_venv_wf_on_types_strong970;l4_vctx_strong_of_wf970]);;

let l4_vis_defeq_eq_up_to_levels970 = prove
 (`!env uvars g e1 e2 e2' ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty /\
   l4_veq_up_to_levels970 uvars e2 e2' ==>
   l4_vis_defeq961 env uvars g e1 e2' ty`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_strong_to_defeq970 THEN
  SUBGOAL_THEN `l4_vctx_strong970 env uvars g /\
                l4_vis_defeq_strong970 env uvars g e1 e2 ty`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vctx_strong_of_wf970;l4_vis_defeq_strong_thm970]; ALL_TAC] THEN
  MATCH_MP_TAC l4_veq_up_to_levels_defeq970 THEN
  MAP_EVERY EXISTS_TAC [`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
  ASM_MESON_TAC [l4_venv_wf_on_types_strong970;l4_veq_up_to_levels_refl970;
                 l4_vctx_strong_level_wf970]);;

let l4_vctx_wf_instL970 = prove
 (`!g env uvars uvars' ls.
   ALL (l4_vlevel_wf961 uvars') ls /\ l4_vctx_wf966 env uvars g ==>
   l4_vctx_wf966 env uvars' (MAP (l4_vinstL961 ls) g)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [FORALL_SIMP;MAP;l4_vctx_wf966] THEN
  REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC [];
   ASM_MESON_TAC [l4_vis_type_instL966]]);;

let l4_vis_defeq_instL_r970 = prove
 (`!env uvars uvars' g e1 e2 ty ls1 ls2.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars' g /\
   ALL (l4_vlevel_wf961 uvars) ls1 /\
   ALL (l4_vlevel_wf961 uvars) ls2 /\
   ALL2 l4_vlevel_equiv961 ls1 ls2 /\
   l4_vis_defeq961 env uvars' g e1 e2 ty ==>
   l4_vis_defeq961 env uvars (MAP (l4_vinstL961 ls1) g)
     (l4_vinstL961 ls1 e1) (l4_vinstL961 ls2 e2) (l4_vinstL961 ls1 ty)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars' g e1 e2 ty` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970]; ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_eq_up_to_levels970 THEN
  EXISTS_TAC `l4_vinstL961 ls1 e2` THEN
  ASM_MESON_TAC [l4_vctx_wf_instL970;l4_vis_defeq_instL966;l4_veq_up_to_levels_instL970]);;

(* ========================================================================= *)
(* 6. HasTypeStrong, Syntactic Inversions, and Stratification                *)
(* ========================================================================= *)

let l4_vis_defeq_strong_has_type'970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vhas_type_strong970 env uvars g e1 ty T /\
   l4_vhas_type_strong970 env uvars g e2 ty T`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `i:num`;`ty:l4_vexpr961`;`u:l4_vlevel961`] l4_vhas_type_strong_bvar970) THEN
   ASM_SIMP_TAC [];
   (* symm *)
   MESON_TAC [];
   (* trans *)
   MESON_TAC [];
   (* sort *)
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MATCH_MP_TAC l4_vhas_type_strong_sort970 THEN
    ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
    MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MATCH_MP_TAC l4_vhas_type_strong_sort970 THEN
    ASM_MESON_TAC [l4_vlevel_equiv_symm961]];
   (* const *)
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `c:l4_name`;`ci:l4_vconstant961`;`ls1:l4_vlevel961 list`;`u:l4_vlevel961`]
      l4_vhas_type_strong_const970) THEN
    ASM_SIMP_TAC [];
    SUBGOAL_THEN `LENGTH (ls2:l4_vlevel961 list) = l4_vc_uvars961 ci` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_all2_length_eq970]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g (L4VConst961 c ls2)
                    (l4_vinstL961 ls2 (l4_vc_type961 ci)) T` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `c:l4_name`;`ci:l4_vconstant961`;`ls2:l4_vlevel961 list`;`u:l4_vlevel961`]
       l4_vhas_type_strong_const970) THEN
     ASM_SIMP_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                    (l4_vinstL961 ls2 (l4_vc_type961 ci))
                    (l4_vinstL961 ls1 (l4_vc_type961 ci)) (L4VSort961 u)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`l4_vinstL961 ls2 (l4_vc_type961 ci)`;
                    `l4_vinstL961 ls1 (l4_vc_type961 ci)`;`L4VConst961 c ls2`]
       l4_vhas_type_strong_defeq970) THEN
     ASM_SIMP_TAC []]];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `f1:l4_vexpr961`;`f2:l4_vexpr961`;
                        `a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                   (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`]
      l4_vhas_type_strong_forall970) THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                   `f1:l4_vexpr961`;`a1:l4_vexpr961`] l4_vhas_type_strong_app970) THEN
    ASM_SIMP_TAC [];
    SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g (L4VApp961 f2 a2) (l4_vinst0961 cod a2) T`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                    `f2:l4_vexpr961`;`a2:l4_vexpr961`] l4_vhas_type_strong_app970) THEN
     ASM_SIMP_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                    (l4_vinst0961 cod a2) (l4_vinst0961 cod a1) (L4VSort961 v)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `v:l4_vlevel961`;`l4_vinst0961 cod a2`;`l4_vinst0961 cod a1`;
                    `L4VApp961 f2 a2`] l4_vhas_type_strong_defeq970) THEN
     ASM_SIMP_TAC []]];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                   (L4VForallE961 dom1 cod) (L4VSort961 (L4VLIMax961 u v)) T /\
                 l4_vhas_type_strong970 env uvars g
                   (L4VForallE961 dom2 cod) (L4VSort961 (L4VLIMax961 u v)) T`
     STRIP_ASSUME_TAC THENL
   [(CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_strong_base970) THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom1:l4_vexpr961`;`cod:l4_vexpr961`]
       l4_vhas_type_strong_forall970) THEN ASM_SIMP_TAC [];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom2:l4_vexpr961`;`cod:l4_vexpr961`]
       l4_vhas_type_strong_forall970) THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
    MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `u:l4_vlevel961`;`v:l4_vlevel961`;`dom1:l4_vexpr961`;`cod:l4_vexpr961`;
                   `b1:l4_vexpr961`] l4_vhas_type_strong_lam970) THEN
    ASM_SIMP_TAC [];
    SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                    (L4VLam961 dom2 b2) (L4VForallE961 dom2 cod) T` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom2:l4_vexpr961`;`cod:l4_vexpr961`;
                    `b2:l4_vexpr961`] l4_vhas_type_strong_lam970) THEN
     ASM_SIMP_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g
                    (L4VForallE961 dom2 cod) (L4VForallE961 dom1 cod)
                    (L4VSort961 (L4VLIMax961 u v))` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                    `cod:l4_vexpr961`;`cod:l4_vexpr961`] l4_vis_defeq_strong_forall970) THEN
     ASM_SIMP_TAC [];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `L4VLIMax961 u v`;`L4VForallE961 dom2 cod`;`L4VForallE961 dom1 cod`;
                    `L4VLam961 dom2 b2`] l4_vhas_type_strong_defeq970) THEN
     ASM_SIMP_TAC [l4_vlevel_wf961]]];
   (* forall *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
   MATCH_MP_TAC l4_vhas_type_strong_forall970 THEN ASM_REWRITE_TAC [];
   (* conv *)
   MESON_TAC [l4_vhas_type_strong_defeq970];
   (* beta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                    (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`]
       l4_vhas_type_strong_forall970) THEN
     ASM_SIMP_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                    (L4VLam961 dom body) (L4VForallE961 dom cod) T` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                    `body:l4_vexpr961`] l4_vhas_type_strong_lam970) THEN
     ASM_SIMP_TAC [];
     MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                    `L4VLam961 dom body`;`arg:l4_vexpr961`] l4_vhas_type_strong_app970) THEN
     ASM_SIMP_TAC []];
    ASM_REWRITE_TAC []];
   (* eta *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `l4_vhas_type_strong970 env uvars g
                    (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T /\
                  l4_vhas_type_strong970 env uvars (CONS dom g)
                    (L4VForallE961 (l4_vlift961 dom) (l4_vliftN961 cod 1 1))
                    (L4VSort961 (L4VLIMax961 u v)) T /\
                  l4_vhas_type_strong970 env uvars (CONS dom g)
                    (L4VBVar961 0) (l4_vlift961 dom) T`
      STRIP_ASSUME_TAC THENL
    [(REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_strong_base970) THENL
     [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                     `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`]
        l4_vhas_type_strong_forall970) THEN ASM_SIMP_TAC [];
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                     `u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vlift961 dom`;`l4_vliftN961 cod 1 1`]
        l4_vhas_type_strong_forall970) THEN ASM_SIMP_TAC [];
      MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                     `0`;`l4_vlift961 dom`;`u:l4_vlevel961`]
        l4_vhas_type_strong_bvar970) THEN ASM_SIMP_TAC [CONJUNCT1 l4_vlookup_RULES961]];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vhas_type_strong970 env uvars (CONS dom g)
                    (L4VApp961 (l4_vlift961 e) (L4VBVar961 0)) cod T` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (dom:l4_vexpr961) g`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;
                    `l4_vlift961 dom`;`l4_vliftN961 cod 1 1`;
                    `l4_vlift961 e`;`L4VBVar961 0`] l4_vhas_type_strong_app970) THEN
     REWRITE_TAC [l4_vinst0_vliftN_one_one_bvar0970] THEN ASM_SIMP_TAC [];
     MATCH_MP_TAC l4_vhas_type_strong_base970 THEN
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`;`cod:l4_vexpr961`;
                    `L4VApp961 (l4_vlift961 e) (L4VBVar961 0)`] l4_vhas_type_strong_lam970) THEN
     ASM_SIMP_TAC []];
    ASM_REWRITE_TAC []];
   (* proofIrrel *)
   MESON_TAC [];
   (* extra *)
   MESON_TAC []]);;

let l4_vhas_type_strong_refl970 = prove
 (`!env uvars g e ty b.
   l4_vhas_type_strong970 env uvars g e ty b ==>
   l4_vis_defeq_strong970 env uvars g e e ty`,
  MATCH_MP_TAC l4_vhas_type_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_strong_bvar970];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
   MAP_EVERY EXISTS_TAC [`L4VLSucc961 (L4VLSucc961 l1)`;`L4VSort961 (L4VLSucc961 l1)`] THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961] THEN CONJ_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN
   ASM_SIMP_TAC [l4_vlevel_wf961;l4_vlevel_succ_equiv970;l4_vlevel_equiv_refl961];
   MESON_TAC [l4_vis_defeq_strong_const970;l4_all2_vlevel_equiv_refl970];
   MESON_TAC [l4_vis_defeq_strong_app970];
   MESON_TAC [l4_vis_defeq_strong_lam970];
   MESON_TAC [l4_vis_defeq_strong_forall970];
   MESON_TAC [];
   MESON_TAC [l4_vis_defeq_strong_conv970]]);;

let l4_vhas_type_strong_has_type970 = prove
 (`!env uvars g e ty b.
   l4_vhas_type_strong970 env uvars g e ty b ==>
   l4_vhas_type961 env uvars g e ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vhas_type_strong_refl970;l4_vis_defeq_strong_to_defeq970]);;

let l4_vhas_type_strong_to_core970 = prove
 (`!env uvars g e ty b.
   l4_vhas_type_strong970 env uvars g e ty b ==>
   ?ty0. l4_vhas_type_strong970 env uvars g e ty0 F`,
  MATCH_MP_TAC l4_vhas_type_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vhas_type_strong_bvar970];
   MESON_TAC [l4_vhas_type_strong_sort970];
   MESON_TAC [l4_vhas_type_strong_const970];
   MESON_TAC [l4_vhas_type_strong_app970];
   MESON_TAC [l4_vhas_type_strong_lam970];
   MESON_TAC [l4_vhas_type_strong_forall970];
   MESON_TAC [];
   MESON_TAC []]);;

(* 4 Syntactic typing inversions modulo l4_vis_defeq961 *)
let l4_vhas_type_app_inv970 = prove
 (`!env uvars g f a ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (L4VApp961 f a) ty ==>
   ?dom cod.
     l4_vhas_type961 env uvars g f (L4VForallE961 dom cod) /\
     l4_vhas_type961 env uvars g a dom`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ty0. l4_vhas_type_strong970 env uvars g (L4VApp961 f a) ty0 F`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` MP_TAC) THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_has_type'970;
                  l4_vhas_type_strong_to_core970];
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_strong_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN
   MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`cod:l4_vexpr961`] THEN
   REWRITE_TAC [GSYM l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vhas_type_strong_has_type970]]);;

let l4_vhas_type_lam_inv970 = prove
 (`!env uvars g dom body ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (L4VLam961 dom body) ty ==>
   l4_vis_type961 env uvars g dom /\
   (?cod. l4_vhas_type961 env uvars (CONS dom g) body cod)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ty0. l4_vhas_type_strong970 env uvars g (L4VLam961 dom body) ty0 F`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` MP_TAC) THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_has_type'970;
                  l4_vhas_type_strong_to_core970];
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_strong_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN
   REWRITE_TAC [l4_vis_type961;GSYM l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vhas_type_strong_has_type970]]);;

let l4_vhas_type_const_inv970 = prove
 (`!env uvars g c ls ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (L4VConst961 c ls) ty ==>
   ?ci. l4_venv_lookup_const961 env c ci /\
        ALL (l4_vlevel_wf961 uvars) ls /\
        LENGTH ls = l4_vc_uvars961 ci`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ty0. l4_vhas_type_strong970 env uvars g (L4VConst961 c ls) ty0 F`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` MP_TAC) THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_has_type'970;
                  l4_vhas_type_strong_to_core970];
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_strong_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   MESON_TAC []]);;

let l4_vhas_type_bvar_inv970 = prove
 (`!env uvars g i ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (L4VBVar961 i) ty ==>
   ?a. l4_vlookup961 g i a`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ty0. l4_vhas_type_strong970 env uvars g (L4VBVar961 i) ty0 F`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` MP_TAC) THENL
  [ASM_MESON_TAC [l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_has_type'970;
                  l4_vhas_type_strong_to_core970];
   GEN_REWRITE_TAC LAND_CONV [l4_vhas_type_strong_CASES970] THEN
   REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
   MESON_TAC []]);;

(* Stratified typing: HasTypeStratified *)
let l4_vhas_type_stratified_RULES970,
    l4_vhas_type_stratified_INDUCT970,
    l4_vhas_type_stratified_CASES970 =
  new_inductive_definition
 `(!env uvars g i ty u n.
     l4_vlookup961 g i ty /\
     l4_vhas_type_stratified970 env uvars g ty (L4VSort961 u) T n ==>
     l4_vhas_type_stratified970 env uvars g (L4VBVar961 i) ty F (SUC n)) /\
  (!env uvars g l1 l2 n.
     l4_vlevel_wf961 uvars l1 /\
     l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_vhas_type_stratified970 env uvars g (L4VSort961 l1) (L4VSort961 (L4VLSucc961 l2)) F n) /\
  (!env uvars g c ci ls u n.
     l4_venv_lookup_const961 env c ci /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vc_uvars961 ci /\
     l4_vhas_type_stratified970 env uvars g (l4_vinstL961 ls (l4_vc_type961 ci)) (L4VSort961 u) T n ==>
     l4_vhas_type_stratified970 env uvars g
       (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci)) F (SUC n)) /\
  (!env uvars g u v dom cod f a n.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vhas_type_stratified970 env uvars g dom (L4VSort961 u) T n /\
     l4_vhas_type_stratified970 env uvars (CONS dom g) cod (L4VSort961 v) T n /\
     l4_vhas_type_stratified970 env uvars g f (L4VForallE961 dom cod) T n /\
     l4_vhas_type_stratified970 env uvars g a dom T n /\
     l4_vhas_type_stratified970 env uvars g (l4_vinst0961 cod a) (L4VSort961 v) T n ==>
     l4_vhas_type_stratified970 env uvars g (L4VApp961 f a) (l4_vinst0961 cod a) F (SUC n)) /\
  (!env uvars g u v dom cod body n.
     l4_vhas_type_stratified970 env uvars g dom (L4VSort961 u) T n /\
     l4_vhas_type_stratified970 env uvars (CONS dom g) cod (L4VSort961 v) T n /\
     l4_vhas_type_stratified970 env uvars (CONS dom g) body cod T n /\
     l4_vhas_type_stratified970 env uvars g
       (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) T n ==>
     l4_vhas_type_stratified970 env uvars g
       (L4VLam961 dom body) (L4VForallE961 dom cod) F (SUC n)) /\
  (!env uvars g u v dom cod n.
     l4_vlevel_wf961 uvars u /\
     l4_vlevel_wf961 uvars v /\
     l4_vhas_type_stratified970 env uvars g dom (L4VSort961 u) T n /\
     l4_vhas_type_stratified970 env uvars (CONS dom g) cod (L4VSort961 v) T n ==>
     l4_vhas_type_stratified970 env uvars g
       (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v)) F (SUC n)) /\
  (!env uvars g e ty n.
     l4_vhas_type_stratified970 env uvars g e ty F n ==>
     l4_vhas_type_stratified970 env uvars g e ty T n) /\
  (!env uvars g u ty1 ty2 e n.
     l4_vlevel_wf961 uvars u /\
     l4_vis_defeq961 env uvars g ty1 ty2 (L4VSort961 u) /\
     l4_vhas_type_stratified970 env uvars g ty1 (L4VSort961 u) T n /\
     l4_vhas_type_stratified970 env uvars g ty2 (L4VSort961 u) T n /\
     l4_vhas_type_stratified970 env uvars g e ty1 T n ==>
     l4_vhas_type_stratified970 env uvars g e ty2 T (SUC n))`;;

let l4_vhas_type_stratified_bvar970,
    l4_vhas_type_stratified_sort970,
    l4_vhas_type_stratified_const970,
    l4_vhas_type_stratified_app970,
    l4_vhas_type_stratified_lam970,
    l4_vhas_type_stratified_forall970,
    l4_vhas_type_stratified_base970,
    l4_vhas_type_stratified_defeq970 =
  match CONJUNCTS l4_vhas_type_stratified_RULES970 with
  | [c1;c2;c3;c4;c5;c6;c7;c8] -> (c1,c2,c3,c4,c5,c6,c7,c8)
  | _ -> failwith "l4_vhas_type_stratified_RULES970: unexpected arity";;

let l4_vhas_type_stratified_STRONG_INDUCT970 =
  derive_strong_induction
    (l4_vhas_type_stratified_RULES970, l4_vhas_type_stratified_INDUCT970);;

let l4_vhas_type_stratified_has_type970 = prove
 (`!env uvars g e ty b n.
   l4_vhas_type_stratified970 env uvars g e ty b n ==>
   l4_vhas_type961 env uvars g e ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vhas_type_stratified_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_bvar961];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`L4VSort961 (L4VLSucc961 l1)`;`L4VLSucc961 (L4VLSucc961 l1)`] THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_SIMP_TAC [l4_vlevel_wf961;l4_vlevel_succ_equiv970;l4_vlevel_equiv_refl961];
   MESON_TAC [l4_vis_defeq_const961;l4_all2_vlevel_equiv_refl970];
   MESON_TAC [l4_vis_defeq_app961];
   MESON_TAC [l4_vis_defeq_lam961];
   MESON_TAC [l4_vis_defeq_forall961];
   MESON_TAC [];
   MESON_TAC [l4_vis_defeq_conv961]]);;

let l4_vhas_type_stratified_mono_ind970 = prove
 (`!env uvars g e ty b m.
   l4_vhas_type_stratified970 env uvars g e ty b m ==>
   (!n. m <= n ==> l4_vhas_type_stratified970 env uvars g e ty b n)`,
  MATCH_MP_TAC l4_vhas_type_stratified_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_bvar970 THEN ASM_MESON_TAC [];
   MESON_TAC [l4_vhas_type_stratified_sort970];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_const970 THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_app970 THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_lam970 THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_forall970 THEN ASM_MESON_TAC [];
   MESON_TAC [l4_vhas_type_stratified_base970];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE;NOT_SUC;LE_SUC] THEN
   DISCH_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_defeq970 THEN ASM_MESON_TAC []]);;

let l4_vhas_type_stratified_mono970 = prove
 (`!env uvars g e ty b m n.
   m <= n /\ l4_vhas_type_stratified970 env uvars g e ty b m ==>
   l4_vhas_type_stratified970 env uvars g e ty b n`,
  MESON_TAC [l4_vhas_type_stratified_mono_ind970]);;

let l4_vhas_type_strong_stratify970 = prove
 (`!env uvars g e ty b.
   l4_vhas_type_strong970 env uvars g e ty b ==>
   ?n. l4_vhas_type_stratified970 env uvars g e ty b n`,
  MATCH_MP_TAC l4_vhas_type_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vhas_type_stratified_bvar970];
   MESON_TAC [l4_vhas_type_stratified_sort970];
   MESON_TAC [l4_vhas_type_stratified_const970];
   (* app *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n1:num`))
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n2:num`))
           (CONJUNCTS_THEN2 (K ALL_TAC)
             (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n3:num`))
               (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n4:num`))
                 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n5:num`))))))))) THEN
   EXISTS_TAC `SUC (MAX n1 (MAX n2 (MAX n3 (MAX n4 n5))))` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_app970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`dom:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN
   MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
   [EXISTS_TAC `n1:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n3:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n4:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n5:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC];
   (* lam *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC)
     (CONJUNCTS_THEN2 (K ALL_TAC)
       (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n1:num`))
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n2:num`))
           (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n3:num`))
             (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n4:num`))))))) THEN
   EXISTS_TAC `SUC (MAX n1 (MAX n2 (MAX n3 n4)))` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_lam970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
   REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
   [EXISTS_TAC `n1:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n3:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n4:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC];
   (* forall *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n1:num`))
         (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n2:num`))))) THEN
   EXISTS_TAC `SUC (MAX n1 n2)` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_forall970 THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
   [EXISTS_TAC `n1:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC];
   (* base *)
   MESON_TAC [l4_vhas_type_stratified_base970];
   (* defeq *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n1:num`))
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n2:num`))
           (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `n3:num`)))))) THEN
   EXISTS_TAC `SUC (MAX n1 (MAX n2 n3))` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_defeq970 THEN
   MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`ty1:l4_vexpr961`] THEN
   ASM_SIMP_TAC [l4_vis_defeq_strong_to_defeq970] THEN
   REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vhas_type_stratified_mono970 THENL
   [EXISTS_TAC `n1:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    EXISTS_TAC `n3:num` THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]]);;

let l4_vhas_type_stratified_to_core_ind970 = prove
 (`!env uvars g e ty b n.
   l4_vhas_type_stratified970 env uvars g e ty b n ==>
   ?ty0. l4_vhas_type_stratified970 env uvars g e ty0 F n`,
  MATCH_MP_TAC l4_vhas_type_stratified_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vhas_type_stratified_bvar970];
   MESON_TAC [l4_vhas_type_stratified_sort970];
   MESON_TAC [l4_vhas_type_stratified_const970];
   MESON_TAC [l4_vhas_type_stratified_app970];
   MESON_TAC [l4_vhas_type_stratified_lam970];
   MESON_TAC [l4_vhas_type_stratified_forall970];
   MESON_TAC [];
   REPEAT STRIP_TAC THEN EXISTS_TAC `ty0'':l4_vexpr961` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_mono970 THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC [ARITH_RULE `n <= SUC n`]]);;

let l4_vhas_type_stratified_to_core970 = prove
 (`!env uvars g e ty n.
   l4_vhas_type_stratified970 env uvars g e ty T n ==>
   ?ty0. l4_vhas_type_stratified970 env uvars g e ty0 F n`,
  MESON_TAC [l4_vhas_type_stratified_to_core_ind970]);;

let l4_vhas_type_stratified_is_type970 = prove
 (`!env uvars g e ty b n.
   l4_vhas_type_stratified970 env uvars g e ty b n ==>
   ?u. l4_vhas_type_stratified970 env uvars g ty (L4VSort961 u) T (n - 1)`,
  MATCH_MP_TAC l4_vhas_type_stratified_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [SUC_SUB1] THEN MESON_TAC [];
   REPEAT STRIP_TAC THEN EXISTS_TAC `L4VLSucc961 (L4VLSucc961 l2)` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_base970 THEN
   MATCH_MP_TAC l4_vhas_type_stratified_sort970 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   REWRITE_TAC [SUC_SUB1] THEN MESON_TAC [];
   REWRITE_TAC [SUC_SUB1] THEN MESON_TAC [];
   REWRITE_TAC [SUC_SUB1] THEN MESON_TAC [];
   REPEAT STRIP_TAC THEN EXISTS_TAC `L4VLSucc961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vhas_type_stratified_base970 THEN
   MATCH_MP_TAC l4_vhas_type_stratified_sort970 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961;l4_vlevel_equiv_refl961];
   MESON_TAC [];
   REWRITE_TAC [SUC_SUB1] THEN MESON_TAC []]);;

(* ========================================================================= *)
(* 7. Simultaneous Substitution: IsDefEqStrong.substEq' & IsDefEq.substDF    *)
(* ========================================================================= *)

let l4_eta_subst_eq970 = prove
 (`!dom e s.
   l4_vsubst969 (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) s =
   L4VLam961 (l4_vsubst969 dom s) (L4VApp961 (l4_vlift961 (l4_vsubst969 e s)) (L4VBVar961 0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vsubst969;l4_vsubst_lift969;l4_vlift_vsubst_lift969]);;

let l4_vis_defeq_strong_subst_eq_ind970 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   (!g0 s s'.
      l4_venv_wf966 env /\
      l4_vctx_strong970 env uvars g /\
      l4_vctx_strong970 env uvars g0 /\
      l4_vctx_subst_eq969 env uvars g0 s s' g ==>
      l4_vis_defeq_strong970 env uvars g0
        (l4_vsubst969 e1 s) (l4_vsubst969 e1 s') (l4_vsubst969 ty s) /\
      l4_vis_defeq_strong970 env uvars g0
        (l4_vsubst969 e2 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s) /\
      l4_vis_defeq_strong970 env uvars g0
        (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s))`,
  MATCH_MP_TAC l4_vis_defeq_strong_STRONG_INDUCT970 THEN REPEAT CONJ_TAC THENL
  [(* bvar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vsubst969] THEN
   MATCH_MP_TAC l4_vis_defeq_strong_thm970 THEN
   ASM_SIMP_TAC [l4_vctx_strong_to_wf970] THEN
   MATCH_MP_TAC l4_vctx_subst_eq_lookup969 THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [];
   (* symm *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e1 s) (l4_vsubst969 e1 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e2 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC [];
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_symm970;l4_vis_defeq_strong_trans970]];
   (* trans *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e1 s) (l4_vsubst969 e1 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e2 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e3 s) (l4_vsubst969 e3 s') (l4_vsubst969 ty s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e2 s) (l4_vsubst969 e3 s') (l4_vsubst969 ty s)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC [];
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_symm970;l4_vis_defeq_strong_trans970]];
   (* sort *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vsubst969] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (L4VSort961 l1) (L4VSort961 l2) (L4VSort961 (L4VLSucc961 l1))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_sort970 THEN ASM_REWRITE_TAC [];
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970]];
   (* const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [l4_vsubst969] THEN
   SUBGOAL_THEN `l4_vsubst969 (l4_vinstL961 ls1 (l4_vc_type961 ci)) s =
                 l4_vinstL961 ls1 (l4_vc_type961 ci)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_vclosed0_vsubst_eq969 THEN
    ASM_MESON_TAC [l4_closed_inst_const966;l4_venv_wf_closed966];
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                    (L4VConst961 c ls1) (L4VConst961 c ls2)
                    (l4_vinstL961 ls1 (l4_vc_type961 ci))` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_const970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966];
     REPEAT CONJ_TAC THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970]]];
   (* app *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `f1:l4_vexpr961`;`f2:l4_vexpr961`;
                        `a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;`s':num->l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0 s s g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_subst_eq_left969]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s) (l4_vsubst969 dom s) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_strong970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s) (CONS dom g)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `!x y. l4_vis_defeq_strong970 env uvars g0 x y (l4_vsubst969 dom s) ==>
                       l4_vis_defeq_strong970 env uvars g0
                         (l4_vinst0961 (l4_vsubst969 cod (l4_vsubst_lift969 s)) x)
                         (l4_vinst0961 (l4_vsubst969 cod (l4_vsubst_lift969 s)) y)
                         (L4VSort961 v)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [l4_vinst_vsubst_lift_cons969] THEN
    SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0
                    (l4_vsubst_cons969 s x) (l4_vsubst_cons969 s y) (CONS dom g)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_REWRITE_TAC [l4_vsubst_cons_tail969;l4_vsubst_cons_head969;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 f1 s) (l4_vsubst969 f1 s')
                   (L4VForallE961 (l4_vsubst969 dom s) (l4_vsubst969 cod (l4_vsubst_lift969 s))) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 f2 s) (l4_vsubst969 f2 s')
                   (L4VForallE961 (l4_vsubst969 dom s) (l4_vsubst969 cod (l4_vsubst_lift969 s))) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 f1 s) (l4_vsubst969 f2 s')
                   (L4VForallE961 (l4_vsubst969 dom s) (l4_vsubst969 cod (l4_vsubst_lift969 s))) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 a1 s) (l4_vsubst969 a1 s') (l4_vsubst969 dom s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 a2 s) (l4_vsubst969 a2 s') (l4_vsubst969 dom s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 a1 s) (l4_vsubst969 a2 s') (l4_vsubst969 dom s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 a1 s) (l4_vsubst969 a2 s) (l4_vsubst969 dom s)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vsubst969;l4_vsubst_vinst969] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vsubst969 dom s`] THEN
     ASM_SIMP_TAC [];
     MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
     MAP_EVERY EXISTS_TAC [`v:l4_vlevel961`;
                           `l4_vinst0961 (l4_vsubst969 cod (l4_vsubst_lift969 s))
                              (l4_vsubst969 a2 s)`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vis_defeq_strong_symm970];
      MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
      MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vsubst969 dom s`] THEN
      ASM_SIMP_TAC []];
     MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vsubst969 dom s`] THEN
     ASM_SIMP_TAC []]];
   (* lam *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;`cod:l4_vexpr961`;
                        `b1:l4_vexpr961`;`b2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;`s':num->l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0 s s g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_subst_eq_left969]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom1 s) (l4_vsubst969 dom1 s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom2 s) (l4_vsubst969 dom2 s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom1 s) (l4_vsubst969 dom2 s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom1 s) (l4_vsubst969 dom2 s) (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom1 dom1 (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom2 dom2 (L4VSort961 u) /\
                 l4_vctx_strong970 env uvars (CONS dom1 g) /\
                 l4_vctx_strong970 env uvars (CONS dom2 g) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom1 s') g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom2 s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970;l4_vctx_strong970];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom1 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom2 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom2 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s) (CONS dom1 g)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN
    EXISTS_TAC `l4_vsubst969 cod (l4_vsubst_lift969 s')` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s') g0)
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst969 b1 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s))
                   (l4_vsubst969 b2 (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_vsubst969] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
    MAP_EVERY EXISTS_TAC [`L4VLIMax961 u v`;
                          `L4VForallE961 (l4_vsubst969 dom2 s)
                             (l4_vsubst969 cod (l4_vsubst_lift969 s))`] THEN
    ASM_REWRITE_TAC [l4_vlevel_wf961] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_symm970 THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC []];
   (* forall *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom1:l4_vexpr961`;`dom2:l4_vexpr961`;
                        `cod1:l4_vexpr961`;`cod2:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;`s':num->l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom1 s) (l4_vsubst969 dom1 s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom2 s) (l4_vsubst969 dom2 s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom1 s) (l4_vsubst969 dom2 s') (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g dom1 dom1 (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g dom2 dom2 (L4VSort961 u) /\
                 l4_vctx_strong970 env uvars (CONS dom1 g) /\
                 l4_vctx_strong970 env uvars (CONS dom2 g) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom1 s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom1 s') g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom2 s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom2 s') g0)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970;l4_vctx_strong970];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom1 s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom1 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom2 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom2 g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom2 s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom1 g)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]];
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN
    REWRITE_TAC [l4_vsubst969] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN ASM_SIMP_TAC []];
   (* conv *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0 s s g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_subst_eq_left969]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 ty1 s) (l4_vsubst969 ty2 s) (L4VSort961 u)`
     ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC [];
    SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                    (l4_vsubst969 e1 s) (l4_vsubst969 e1 s') (l4_vsubst969 ty1 s) /\
                  l4_vis_defeq_strong970 env uvars g0
                    (l4_vsubst969 e2 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty1 s) /\
                  l4_vis_defeq_strong970 env uvars g0
                    (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty1 s)`
      STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC [];
     REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`l4_vsubst969 ty1 s`] THEN ASM_REWRITE_TAC []]];
   (* beta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;
                        `body:l4_vexpr961`;`arg:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;`s':num->l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0 s s g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_subst_eq_left969]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s) (l4_vsubst969 dom s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s) (l4_vsubst969 dom s) (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s') (l4_vsubst969 dom s') (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_refl_r970 THEN EXISTS_TAC `l4_vsubst969 dom s` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC [l4_vctx_strong970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s) (CONS dom g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom g)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]];
    ALL_TAC] THEN
   SUBGOAL_THEN `!x y. l4_vis_defeq_strong970 env uvars g0 x y (l4_vsubst969 dom s) ==>
                       l4_vis_defeq_strong970 env uvars g0
                         (l4_vinst0961 (l4_vsubst969 cod (l4_vsubst_lift969 s)) x)
                         (l4_vinst0961 (l4_vsubst969 cod (l4_vsubst_lift969 s)) y)
                         (L4VSort961 v)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [l4_vinst_vsubst_lift_cons969] THEN
    SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0
                    (l4_vsubst_cons969 s x) (l4_vsubst_cons969 s y) (CONS dom g)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_cons969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_REWRITE_TAC [l4_vsubst_cons_tail969;l4_vsubst_cons_head969;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 body (l4_vsubst_lift969 s))
                   (l4_vsubst969 body (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 body (l4_vsubst_lift969 s))
                   (l4_vsubst969 body (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst969 body (l4_vsubst_lift969 s))
                   (l4_vsubst969 body (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 arg s) (l4_vsubst969 arg s) (l4_vsubst969 dom s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 arg s) (l4_vsubst969 arg s') (l4_vsubst969 dom s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (l4_vinst0961 body arg) s)
                   (l4_vsubst969 (l4_vinst0961 body arg) s)
                   (l4_vsubst969 (l4_vinst0961 cod arg) s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (l4_vinst0961 body arg) s)
                   (l4_vsubst969 (l4_vinst0961 body arg) s')
                   (l4_vsubst969 (l4_vinst0961 cod arg) s)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_refl_l970 THEN
    EXISTS_TAC `l4_vsubst969 cod (l4_vsubst_lift969 s')` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (L4VApp961 (L4VLam961 dom body) arg) s)
                   (l4_vsubst969 (l4_vinst0961 body arg) s)
                   (l4_vsubst969 (l4_vinst0961 cod arg) s)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vsubst969;l4_vsubst_vinst969] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_beta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst_vinst969]) THEN
    ASM_SIMP_TAC [];
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vsubst969;l4_vsubst_vinst969] THEN
     MATCH_MP_TAC l4_vis_defeq_strong_app970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`;`l4_vsubst969 dom s`] THEN
     ASM_SIMP_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_strong_lam970 THEN
     MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN ASM_REWRITE_TAC [];
     ASM_MESON_TAC [l4_vis_defeq_strong_trans970]]];
   (* eta *)
   MAP_EVERY X_GEN_TAC [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                        `u:l4_vlevel961`;`v:l4_vlevel961`;
                        `dom:l4_vexpr961`;`cod:l4_vexpr961`;`e:l4_vexpr961`] THEN
   STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;`s':num->l4_vexpr961`] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars g0 s s g` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vctx_subst_eq_left969]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s) (l4_vsubst969 dom s') (L4VSort961 u) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s) (l4_vsubst969 dom s) (L4VSort961 u)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 dom s') (l4_vsubst969 dom s') (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_refl_r970 THEN EXISTS_TAC `l4_vsubst969 dom s` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_strong970 env uvars (CONS dom g) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom s) g0) /\
                 l4_vctx_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC [l4_vctx_strong970]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s) (CONS dom g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom g) /\
                 l4_vctx_subst_eq969 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst_lift969 s) (l4_vsubst_lift969 s') (CONS dom g)`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970];
     MATCH_MP_TAC l4_vctx_subst_eq_lift_at969 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vhas_type961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_to_defeq970]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s)) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s) g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e s) (l4_vsubst969 e s')
                   (l4_vsubst969 (L4VForallE961 dom cod) s)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC [l4_vsubst969];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars (CONS (l4_vsubst969 dom s') g0)
                   (l4_vsubst969 cod (l4_vsubst_lift969 s'))
                   (l4_vsubst969 cod (l4_vsubst_lift969 s')) (L4VSort961 v)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_refl_r970 THEN
    EXISTS_TAC `l4_vsubst969 cod (l4_vsubst_lift969 s)` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (L4VForallE961 dom cod) s)
                   (l4_vsubst969 (L4VForallE961 dom cod) s')
                   (L4VSort961 (L4VLIMax961 u v))` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vsubst969] THEN MATCH_MP_TAC l4_vis_defeq_strong_forall970 THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e s) (l4_vsubst969 e s)
                   (l4_vsubst969 (L4VForallE961 dom cod) s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 e s') (l4_vsubst969 e s')
                   (l4_vsubst969 (L4VForallE961 dom cod) s')`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970];
     MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
     MAP_EVERY EXISTS_TAC [`L4VLIMax961 u v`;`l4_vsubst969 (L4VForallE961 dom cod) s`] THEN
     ASM_REWRITE_TAC [l4_vlevel_wf961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_refl_r970]];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) s)
                   (l4_vsubst969 e s)
                   (l4_vsubst969 (L4VForallE961 dom cod) s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) s')
                   (l4_vsubst969 e s')
                   (l4_vsubst969 (L4VForallE961 dom cod) s')`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN
    CONJ_TAC THEN REWRITE_TAC [l4_eta_subst_eq970;l4_vsubst969] THEN
    MATCH_MP_TAC l4_vis_defeq_strong_eta970 THEN
    MAP_EVERY EXISTS_TAC [`u:l4_vlevel961`;`v:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (l4_vsubst969 dom s) g0`;
                    `l4_vsubst969 cod (l4_vsubst_lift969 s)`;
                    `l4_vsubst969 cod (l4_vsubst_lift969 s)`;`L4VSort961 v`;
                    `1`;`SUC 0`;
                    `CONS (l4_vliftN961 (l4_vsubst969 dom s) 1 0) (CONS (l4_vsubst969 dom s) g0)`]
       l4_vis_defeq_strong_weakN970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;ONE;GSYM l4_vlift961;l4_vliftN961;
                   l4_vctx_liftN_succ966;l4_vctx_liftN_one966];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `l4_vsubst969 e s`;`l4_vsubst969 e s`;
                    `L4VForallE961 (l4_vsubst969 dom s) (l4_vsubst969 cod (l4_vsubst_lift969 s))`;
                    `l4_vsubst969 dom s`] l4_vis_defeq_strong_weak970) THEN
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961;ONE];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `l4_vsubst969 dom s`;`l4_vsubst969 dom s`;`L4VSort961 u`;
                    `l4_vsubst969 dom s`] l4_vis_defeq_strong_weak970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`CONS (l4_vsubst969 dom s') g0`;
                    `l4_vsubst969 cod (l4_vsubst_lift969 s')`;
                    `l4_vsubst969 cod (l4_vsubst_lift969 s')`;`L4VSort961 v`;
                    `1`;`SUC 0`;
                    `CONS (l4_vliftN961 (l4_vsubst969 dom s') 1 0) (CONS (l4_vsubst969 dom s') g0)`]
       l4_vis_defeq_strong_weakN970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;ONE;GSYM l4_vlift961;l4_vliftN961;
                   l4_vctx_liftN_succ966;l4_vctx_liftN_one966];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `l4_vsubst969 e s'`;`l4_vsubst969 e s'`;
                    `L4VForallE961 (l4_vsubst969 dom s') (l4_vsubst969 cod (l4_vsubst_lift969 s'))`;
                    `l4_vsubst969 dom s'`] l4_vis_defeq_strong_weak970) THEN
     RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961;ONE];
     MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                    `l4_vsubst969 dom s'`;`l4_vsubst969 dom s'`;`L4VSort961 u`;
                    `l4_vsubst969 dom s'`] l4_vis_defeq_strong_weak970) THEN
     ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vlift961;l4_vliftN961]];
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `l4_vsubst969 e s` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_strong_trans970 THEN EXISTS_TAC `l4_vsubst969 e s'` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_strong_conv970 THEN
     MAP_EVERY EXISTS_TAC [`L4VLIMax961 u v`;`l4_vsubst969 (L4VForallE961 dom cod) s'`] THEN
     ASM_REWRITE_TAC [l4_vlevel_wf961] THEN
     ASM_MESON_TAC [l4_vis_defeq_strong_symm970];
     ASM_MESON_TAC [l4_vis_defeq_strong_trans970]]];
   (* proofIrrel *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 p s) (l4_vsubst969 p s') (L4VSort961 L4VLZero961) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 h1 s) (l4_vsubst969 h1 s') (l4_vsubst969 p s) /\
                 l4_vis_defeq_strong970 env uvars g0
                   (l4_vsubst969 h2 s) (l4_vsubst969 h2 s') (l4_vsubst969 p s)`
     STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE [l4_vsubst969]) THEN ASM_SIMP_TAC [];
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970;
                   l4_vis_defeq_strong_proof_irrel970]];
   (* extra *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`df:l4_vdefeq961`;`ls:l4_vlevel961 list`;`0`]
     l4_closed_inst_defeq966) THEN
   ANTS_TAC THENL [ASM_SIMP_TAC [l4_venv_wf_closed966]; STRIP_TAC] THEN
   ASM_SIMP_TAC [l4_vclosed0_vsubst_eq969] THEN
   SUBGOAL_THEN `l4_vis_defeq_strong970 env uvars g0
                   (l4_vinstL961 ls (l4_vdf_lhs961 df))
                   (l4_vinstL961 ls (l4_vdf_rhs961 df))
                   (l4_vinstL961 ls (l4_vdf_type961 df))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_strong_extra970 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_SIMP_TAC [l4_vis_defeq_strong_weak0970;l4_venv_wf_closed966];
    REPEAT CONJ_TAC THEN
    ASM_MESON_TAC [l4_vis_defeq_strong_refl_l970;l4_vis_defeq_strong_refl_r970]]]);;

let l4_vis_defeq_strong_subst_eq970 = prove
 (`!env uvars g g0 s s' e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_strong970 env uvars g /\
   l4_vctx_strong970 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s' g /\
   l4_vis_defeq_strong970 env uvars g e1 e2 ty ==>
   l4_vis_defeq_strong970 env uvars g0
     (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s)`,
  MESON_TAC [l4_vis_defeq_strong_subst_eq_ind970]);;

let l4_vis_defeq_subst_df970 = prove
 (`!env uvars g g0 s s' e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s' g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g0
     (l4_vsubst969 e1 s) (l4_vsubst969 e2 s') (l4_vsubst969 ty s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_strong_to_defeq970 THEN
  MATCH_MP_TAC l4_vis_defeq_strong_subst_eq970 THEN
  EXISTS_TAC `g:l4_vexpr961 list` THEN
  ASM_MESON_TAC [l4_vctx_strong_of_wf970;l4_vis_defeq_strong_thm970]);;

let l4_vis_defeq_subst970 = prove
 (`!env uvars g g0 s e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_defeq961 env uvars g0
     (l4_vsubst969 e1 s) (l4_vsubst969 e2 s) (l4_vsubst969 ty s)`,
  MESON_TAC [l4_vis_defeq_subst_df970;l4_vctx_subst_eq_wf969]);;

let l4_vhas_type_subst970 = prove
 (`!env uvars g g0 s e ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s g /\
   l4_vhas_type961 env uvars g e ty ==>
   l4_vhas_type961 env uvars g0 (l4_vsubst969 e s) (l4_vsubst969 ty s)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_subst970]);;

let l4_vis_defeq_u_subst970 = prove
 (`!env uvars g g0 s e1 e2.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s g /\
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   l4_vis_defeq_u961 env uvars g0 (l4_vsubst969 e1 s) (l4_vsubst969 e2 s)`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN MESON_TAC [l4_vis_defeq_subst970]);;

let l4_vis_type_subst970 = prove
 (`!env uvars g g0 s ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g0 /\
   l4_vctx_subst_eq969 env uvars g0 s s g /\
   l4_vis_type961 env uvars g ty ==>
   l4_vis_type961 env uvars g0 (l4_vsubst969 ty s)`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `g0:l4_vexpr961 list`;`s:num->l4_vexpr961`;
                 `ty:l4_vexpr961`;`ty:l4_vexpr961`;`L4VSort961 u`]
    l4_vis_defeq_subst970) THEN
  ASM_SIMP_TAC [l4_vsubst969]);;
