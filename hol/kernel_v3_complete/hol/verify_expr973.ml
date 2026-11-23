(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end HOL Light port of Lean4Lean/Verify/{VLCtx,Expr,LocalContext}.lean
   and rocq/VerifyExpr.v:
   1. Universe decision soundness (l4_knormalize_aux555, l4_klevel_le555,
      l4_klevel_equiv555, l4_klevels_equiv555, l4_core_level_positive555).
   2. Hybrid local context (l4_vl_entry973 / l4_vl_ctx_rec973) supporting both
      lambda and let entries for EBVar and EFVar, with WF, lookup typing, and
      definitional-equality context relations.
   3. Literal translations (l4_nat_lit973, l4_bool_lit973, l4_tr_char_list973,
      l4_tr_str_lit973, l4_vbinary_prim_spec973) and HasPrimitives
      (l4_has_primitives973).
   4. Genuine structure-projection translation (l4_vtr_proj973,
      l4_vproj_telescope973), replacing the vacuous l4_tr_proj962 bridge.
   5. Full 12-constructor inductive translation (l4_vtr_expr_s973,
      l4_vtr_expr973, l4_vtr_typing973, l4_vtr_ctx973) covering all executable
      constructors (BVar, FVar, Sort, Const, App, Lam, Pi, Let [nondep F/T],
      Proj, NatLit, StrLit, MData).
   6. Full 18-component environment soundness invariant (l4_venv_sound973) with
      unconditional non-vacuity (l4_venv_sound_empty973).
   7. Uniqueness, context conversion, lifting, substitution (lam + let +
      subst_many), universe instantiation, closed-term weakening, syntactic
      equality (l4_kexpr_eqb480 / l4_core_alpha_eq538), spine decomposition,
      and exact bridge to l4_tr_e967.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/pattern_confluence972.ml";;
needs "hol/env_decl_theory971.ml";;
needs "hol/infer_soundness967.ml";;
needs "hol/checker_soundness962.ml";;
needs "hol/equiv_manager964.ml";;
needs "hol/fuel_config965.ml";;

(* ========================================================================= *)
(* 0. Core VExpr, List, Option, & VIsDefEqU Helpers                          *)
(* ========================================================================= *)

let l4_vliftN_add_le973 = prove
 (`!e n m k.
   l4_vliftN961 (l4_vliftN961 e n k) m k = l4_vliftN961 e (n + m) k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [l4_vliftN_comp966]);;

let l4_vinst_vliftN_ge973 = prove
 (`!e v n k.
   l4_vinst961 (l4_vliftN961 e (SUC n) k) v k = l4_vliftN961 e n k`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`v:l4_vexpr961`;`n:num`;`k:num`;`k:num`]
    l4_vinst_vliftN_gen966) THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC []]);;

let l4_vinst_vliftN_le973 = prove
 (`!e v n j.
   j <= n ==>
   l4_vinst961 (l4_vliftN961 e (SUC n) 0) v j = l4_vliftN961 e n 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`e:l4_vexpr961`;`v:l4_vexpr961`;`n:num`;`0`;`j:num`]
    l4_vinst_vliftN_gen966) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC []]);;

let l4_vliftN_closed_eq973 = prove
 (`!e n k k0.
   l4_vclosedN961 e k0 /\ k0 <= k ==> l4_vliftN961 e n k = e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vclosedN_vliftN_eq966 THEN
  ASM_MESON_TAC [l4_vclosedN_mono966]);;

let l4_vinst_vapps973 = prove
 (`!args f e0 k.
   l4_vinst961 (l4_vapps962 args f) e0 k =
   l4_vapps962 (MAP (\a. l4_vinst961 a e0 k) args) (l4_vinst961 f e0 k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_vapps962;l4_vinst961] THEN
  ASM_REWRITE_TAC [l4_vinst961]);;

let l4_vis_defeq_u_refl973 = prove
 (`!env uvars g e ty.
   l4_vhas_type961 env uvars g e ty ==>
   l4_vis_defeq_u961 env uvars g e e`,
  REWRITE_TAC [l4_vis_defeq_u961;l4_vhas_type961] THEN MESON_TAC []);;

let l4_vis_defeq_u_has_type_l973 = prove
 (`!env uvars g e1 e2.
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   ?ty. l4_vhas_type961 env uvars g e1 ty`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_refl_l961]);;

let l4_vis_defeq_u_has_type_r973 = prove
 (`!env uvars g e1 e2.
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   ?ty. l4_vhas_type961 env uvars g e2 ty`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_refl_r961]);;

let l4_vis_defeq_u_weakN973 = prove
 (`!env uvars g e1 e2 n k g'.
   l4_venv_closed966 env /\
   l4_vctx_liftN966 n k g g' /\
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   l4_vis_defeq_u961 env uvars g' (l4_vliftN961 e1 n k) (l4_vliftN961 e2 n k)`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_weakN966]);;

let l4_vis_defeq_u_instN973 = prove
 (`!env uvars g0 e0 a0 k g1 g e1 e2.
   l4_venv_closed966 env /\
   l4_vhas_type961 env uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vis_defeq_u961 env uvars g1 e1 e2 ==>
   l4_vis_defeq_u961 env uvars g (l4_vinst961 e1 e0 k) (l4_vinst961 e2 e0 k)`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_instN966]);;

let l4_vis_defeq_u_instL973 = prove
 (`!env uvars uvars' ls g e1 e2.
   ALL (l4_vlevel_wf961 uvars') ls /\
   LENGTH ls = uvars /\
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   l4_vis_defeq_u961 env uvars' (MAP (l4_vinstL961 ls) g)
     (l4_vinstL961 ls e1) (l4_vinstL961 ls e2)`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_instL966]);;

let l4_vis_defeq_u_defeqDFC973 = prove
 (`!env uvars g0 g1 g2 e1 e2.
   l4_venv_closed966 env /\
   l4_vis_defeq_ctx966 env uvars g0 g1 g2 /\
   l4_vis_defeq_u961 env uvars g1 e1 e2 ==>
   l4_vis_defeq_u961 env uvars g2 e1 e2`,
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vis_defeq_defeqDFC966]);;

let l4_vis_defeq_u_appDF973 = prove
 (`!env uvars g f1 f2 a1 a2 t1 t2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq_u961 env uvars g f1 f2 /\
   l4_vis_defeq_u961 env uvars g a1 a2 /\
   l4_vhas_type961 env uvars g (L4VApp961 f1 a1) t1 /\
   l4_vhas_type961 env uvars g (L4VApp961 f2 a2) t2 ==>
   l4_vis_defeq_u961 env uvars g (L4VApp961 f1 a1) (L4VApp961 f2 a2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `f1:l4_vexpr961`;`a1:l4_vexpr961`;`t1:l4_vexpr961`]
    l4_vhas_type_app_inv970) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `dom1:l4_vexpr961`
    (X_CHOOSE_THEN `body1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g f1 f2 (L4VForallE961 dom1 body1)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 env uvars g a1 a2 dom1` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  EXISTS_TAC `l4_vinst0961 body1 a1` THEN
  MATCH_MP_TAC l4_vis_defeq_app961 THEN
  EXISTS_TAC `dom1:l4_vexpr961` THEN ASM_REWRITE_TAC []);;

let l4_vhas_type_apps_head973 = prove
 (`!env uvars g args f ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (l4_vapps962 args f) ty ==>
   ?fty. l4_vhas_type961 env uvars g f fty`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vapps962] THENL
  [MESON_TAC [];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`L4VApp961 f h`;`ty:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`h:l4_vexpr961`;`fty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_MESON_TAC []]);;

let l4_vapps_defeq_congr973 = prove
 (`!env uvars g args1 args2 f1 f2 t1 t2.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   ALL2 (l4_vis_defeq_u961 env uvars g) args1 args2 /\
   l4_vis_defeq_u961 env uvars g f1 f2 /\
   l4_vhas_type961 env uvars g (l4_vapps962 args1 f1) t1 /\
   l4_vhas_type961 env uvars g (l4_vapps962 args2 f2) t2 ==>
   l4_vis_defeq_u961 env uvars g (l4_vapps962 args1 f1) (l4_vapps962 args2 f2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `args2:l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_vapps962] THEN SIMP_TAC [];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `args2:l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_vapps962] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `?ft1. l4_vhas_type961 env uvars g (L4VApp961 f1 h) ft1`
     (X_CHOOSE_TAC `ft1:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vhas_type_apps_head973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `?ft2. l4_vhas_type961 env uvars g (L4VApp961 f2 h') ft2`
     (X_CHOOSE_TAC `ft2:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vhas_type_apps_head973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 env uvars g (L4VApp961 f1 h) (L4VApp961 f2 h')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_appDF973 THEN
    MAP_EVERY EXISTS_TAC [`ft1:l4_vexpr961`;`ft2:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o SPECL
     [`t':l4_vexpr961 list`;`L4VApp961 f1 h`;`L4VApp961 f2 h'`;
      `t1:l4_vexpr961`;`t2:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC []]);;

let l4_suc_sub1_973 = ARITH_RULE `!n. SUC n - 1 = n`;;
let l4_lt_suc_973 = ARITH_RULE `(!n. 0 < SUC n) /\ (!m n. SUC m < SUC n <=> m < n) /\ (!n. ~(n < 0))`;;

let l4_nth_error_el973 = prove
 (`!(xs:A list) i x.
   l4_nth_error550 xs i = SOME x <=> i < LENGTH xs /\ x = EL i xs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_nth_error550;LENGTH;l4_lt_suc_973;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC [l4_nth_error550;EL;HD;TL;l4_lt_suc_973;NOT_SUC;l4_suc_sub1_973;
               injectivity "option"] THEN
  ASM_REWRITE_TAC [] THEN MESON_TAC []);;

let l4_firstn_append_skip973 = prove
 (`!(xs:A list) n. APPEND (l4_kfirstn494 xs n) (l4_skip550 xs n) = xs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_kfirstn494;l4_skip550;APPEND;NOT_SUC;l4_suc_sub1_973] THEN
  ASM_REWRITE_TAC []);;

let l4_length_firstn973 = prove
 (`!(xs:A list) n. n <= LENGTH xs ==> LENGTH (l4_kfirstn494 xs n) = n`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_kfirstn494;LENGTH;LE;LE_SUC;NOT_SUC;l4_suc_sub1_973] THEN
  ASM_SIMP_TAC []);;

let l4_length_skip973 = prove
 (`!(xs:A list) n. LENGTH (l4_skip550 xs n) = LENGTH xs - n`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_skip550;LENGTH;SUB_0;NOT_SUC;l4_suc_sub1_973;ARITH_RULE `SUC a - SUC b = a - b`] THEN
  ASM_REWRITE_TAC [ARITH_RULE `0 - n = 0`]);;

let l4_map_firstn973 = prove
 (`!(f:A->B) xs n. MAP f (l4_kfirstn494 xs n) = l4_kfirstn494 (MAP f xs) n`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_kfirstn494;MAP;NOT_SUC;l4_suc_sub1_973] THEN ASM_REWRITE_TAC []);;

let l4_map_skip973 = prove
 (`!(f:A->B) xs n. MAP f (l4_skip550 xs n) = l4_skip550 (MAP f xs) n`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_skip550;MAP;NOT_SUC;l4_suc_sub1_973] THEN ASM_REWRITE_TAC []);;

let l4_all2_firstn973 = prove
 (`!(R:A->B->bool) xs ys n.
   ALL2 R xs ys ==> ALL2 R (l4_kfirstn494 xs n) (l4_kfirstn494 ys n)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_kfirstn494] THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_kfirstn494;ALL2;NOT_SUC;l4_suc_sub1_973] THEN ASM_MESON_TAC []);;

let l4_all2_skip973 = prove
 (`!(R:A->B->bool) xs ys n.
   ALL2 R xs ys ==> ALL2 R (l4_skip550 xs n) (l4_skip550 ys n)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_skip550] THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_skip550;ALL2;NOT_SUC;l4_suc_sub1_973] THEN ASM_MESON_TAC []);;

let l4_all2_nth_error973 = prove
 (`!(R:A->B->bool) xs ys i x.
   ALL2 R xs ys /\ l4_nth_error550 xs i = SOME x ==>
   ?y. l4_nth_error550 ys i = SOME y /\ R x y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_nth_error550;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC [l4_nth_error550;NOT_SUC;l4_suc_sub1_973;injectivity "option"] THEN
  ASM_MESON_TAC []);;

(* ========================================================================= *)
(* 1. Universe Decision Soundness (l4_klevel_le555, l4_klevel_equiv555)      *)
(* ========================================================================= *)

let l4_ksublevels_eval_append973 = prove
 (`!xs ys rho.
   l4_ksublevels_eval555 (APPEND xs ys) rho =
   MAX (l4_ksublevels_eval555 xs rho) (l4_ksublevels_eval555 ys rho)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [APPEND;l4_ksublevels_eval555] THEN
  ASM_REWRITE_TAC [] THEN ARITH_TAC);;

let l4_kguard_holds_insert973 = prove
 (`!rho n path.
   l4_kguard_holds555 rho (l4_kguard_insert555 n path) <=>
   ~(rho n = 0) /\ l4_kguard_holds555 rho path`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_kguard_holds555;l4_kguard_insert555;l4_name_mem437] THEN
  COND_CASES_TAC THEN REWRITE_TAC [ALL] THEN
  ASM_MESON_TAC [ALL_MEM]);;

let l4_kconst_atom_eval973 = prove
 (`!path k rho.
   l4_ksublevels_eval555 (l4_kconst_atom555 path k) rho =
   if l4_kguard_holds555 rho path then k else 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_kconst_atom555] THEN COND_CASES_TAC THEN
  REWRITE_TAC [l4_ksublevels_eval555;l4_ksublevel_eval555] THEN
  ASM_ARITH_TAC);;

let l4_knormalize_aux_eval973 = prove
 (`!fuel u path k xs rho.
   l4_knormalize_aux555 fuel u path k = L4KAccept491 xs ==>
   l4_ksublevels_eval555 xs rho =
   if l4_kguard_holds555 rho path then l4_klevel_eval555 u rho + k else 0`,
  let fwd_ih =
    EVERY_ASSUM (fun ih ->
      if is_forall (concl ih) then
        EVERY_ASSUM (fun th ->
          try ASSUME_TAC (MATCH_MP ih th) with Failure _ -> ALL_TAC)
      else ALL_TAC) in
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_knormalize_aux555;distinctness "l4_kresult491"] THEN
  STRUCT_CASES_TAC (SPEC `u:l4_klevel447` (cases "l4_klevel447")) THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491";
               l4_kcombine_levels555;l4_kr_bind_accept967] THENL
  [(* Zero *)
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_kconst_atom_eval973;l4_klevel_eval555;ADD_CLAUSES];
   (* Succ *)
   DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
     [`a:l4_klevel447`;`path:l4_name list`;`SUC k`;`xs:l4_ksublevel555 list`;`rho:l4_name->num`]) THEN
   ASM_REWRITE_TAC [l4_klevel_eval555;ADD_CLAUSES];
   (* Max *)
   STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN fwd_ih THEN
   ASM_REWRITE_TAC [l4_ksublevels_eval_append973;l4_klevel_eval555] THEN
   COND_CASES_TAC THEN ARITH_TAC;
   (* IMax *)
   STRUCT_CASES_TAC (SPEC `a1:l4_klevel447` (cases "l4_klevel447")) THEN
   REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491";
                l4_kcombine_levels555;l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THENL
   [(* IMax a Zero *)
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_kconst_atom_eval973;l4_klevel_eval555;ADD_CLAUSES];
    (* IMax a (Succ v) *)
    STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN fwd_ih THEN
    ASM_REWRITE_TAC [l4_ksublevels_eval_append973;l4_klevel_eval555;NOT_SUC] THEN
    COND_CASES_TAC THEN ARITH_TAC;
    (* IMax a (Max v w) *)
    STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN fwd_ih THEN
    ASM_REWRITE_TAC [l4_ksublevels_eval_append973] THEN
    REWRITE_TAC [l4_klevel_eval555] THEN
    COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    (* IMax a (IMax v w) *)
    STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN fwd_ih THEN
    ASM_REWRITE_TAC [l4_ksublevels_eval_append973] THEN
    REWRITE_TAC [l4_klevel_eval555] THEN
    COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    (* IMax a (Param n) *)
    STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN fwd_ih THEN
    ASM_REWRITE_TAC [l4_ksublevels_eval_append973;l4_kconst_atom_eval973;
                     l4_ksublevels_eval555;l4_ksublevel_eval555;
                     l4_kguard_holds_insert973;l4_klevel_eval555] THEN
    COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC];
   (* Param *)
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_ksublevels_eval_append973;l4_kconst_atom_eval973;
                l4_ksublevels_eval555;l4_ksublevel_eval555;
                l4_kguard_holds_insert973;l4_klevel_eval555] THEN
   COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
   COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let l4_knormalize_level_eval973 = prove
 (`!fuel u xs rho.
   l4_knormalize_level555 fuel u = L4KAccept491 xs ==>
   l4_ksublevels_eval555 xs rho = l4_klevel_eval555 u rho`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_knormalize_level555] THEN
  COND_CASES_TAC THEN REWRITE_TAC [distinctness "l4_kresult491"] THEN
  DISCH_THEN (MP_TAC o SPEC `rho:l4_name->num` o MATCH_MP l4_knormalize_aux_eval973) THEN
  SIMP_TAC [l4_kguard_holds555;ALL;ADD_CLAUSES]);;

let l4_ksublevel_le_eval973 = prove
 (`!a b rho.
   l4_ksublevel_le555 a b ==>
   l4_ksublevel_eval555 a rho <= l4_ksublevel_eval555 b rho`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `a:l4_ksublevel555` (cases "l4_ksublevel555")) THEN
  STRUCT_CASES_TAC (SPEC `b:l4_ksublevel555` (cases "l4_ksublevel555")) THEN
  REWRITE_TAC [l4_ksublevel_le555;l4_ksublevel_eval555;l4_kguard_subset555;
               l4_kguard_holds555;l4_name_mem437] THEN
  STRIP_TAC THENL
  [COND_CASES_TAC THENL
   [SUBGOAL_THEN `ALL (\n. ~(rho (n:l4_name) = 0)) a0'` ASSUME_TAC THENL
    [ASM_MESON_TAC [ALL_MEM]; ASM_REWRITE_TAC []];
    ARITH_TAC];
   COND_CASES_TAC THENL
   [SUBGOAL_THEN `ALL (\n. ~(rho (n:l4_name) = 0)) a0'` ASSUME_TAC THENL
    [ASM_MESON_TAC [ALL_MEM];
     SUBGOAL_THEN `~(rho (a1':l4_name) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC [ALL_MEM]; ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]];
    ARITH_TAC];
   COND_CASES_TAC THENL
   [SUBGOAL_THEN `ALL (\n. ~(rho (n:l4_name) = 0)) a0'` ASSUME_TAC THENL
    [ASM_MESON_TAC [ALL_MEM]; ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC];
    ARITH_TAC]]);;

let l4_ksublevels_eval_ex973 = prove
 (`!ys a rho.
   EX (l4_ksublevel_le555 a) ys ==>
   l4_ksublevel_eval555 a rho <= l4_ksublevels_eval555 ys rho`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [EX;l4_ksublevels_eval555] THEN
  REPEAT STRIP_TAC THENL
  [MP_TAC (SPECL [`a:l4_ksublevel555`;`h:l4_ksublevel555`;`rho:l4_name->num`]
     l4_ksublevel_le_eval973) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
   FIRST_X_ASSUM (MP_TAC o SPECL [`a:l4_ksublevel555`;`rho:l4_name->num`]) THEN
   ASM_REWRITE_TAC [] THEN ARITH_TAC]);;

let l4_ksublevels_le_eval973 = prove
 (`!xs ys rho.
   l4_ksublevels_le555 xs ys ==>
   l4_ksublevels_eval555 xs rho <= l4_ksublevels_eval555 ys rho`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_ksublevels_le555;ALL;l4_ksublevels_eval555;LE_0] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`ys:l4_ksublevel555 list`;`h:l4_ksublevel555`;`rho:l4_name->num`]
    l4_ksublevels_eval_ex973) THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`ys:l4_ksublevel555 list`;`rho:l4_name->num`]) THEN
  ASM_REWRITE_TAC [l4_ksublevels_le555] THEN ARITH_TAC);;

let l4_klevel_le_sound973 = prove
 (`!fuel u v.
   l4_klevel_le555 fuel u v = L4KAccept491 T ==>
   (!rho. l4_klevel_eval555 u rho <= l4_klevel_eval555 v rho)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_klevel_le555;l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
  STRIP_TAC THEN GEN_TAC THEN
  ASM_MESON_TAC [l4_knormalize_level_eval973;l4_ksublevels_le_eval973]);;

let l4_klevel_equiv_sound973 = prove
 (`!fuel u v.
   l4_klevel_equiv555 fuel u v = L4KAccept491 T ==>
   (!rho. l4_klevel_eval555 u rho = l4_klevel_eval555 v rho)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_klevel_equiv555;l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
  STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC [GSYM LE_ANTISYM] THEN
  ASM_MESON_TAC [l4_knormalize_level_eval973;l4_ksublevels_le_eval973]);;

let l4_opt_nat973 = define
 `(!ls. l4_opt_nat973 ls NONE = 0) /\
  (!ls i. l4_opt_nat973 ls (SOME i) = l4_vnth_nat961 ls i)`;;

let l4_tr_l_eval_eq973 = prove
 (`!u ps u' ls.
   l4_tr_l967 ps u = SOME u' ==>
   l4_vlevel_eval961 ls u' =
   l4_klevel_eval555 u (\n. l4_opt_nat973 ls (l4_index_of_name967 ps n))`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC [l4_tr_l967;distinctness "option";injectivity "option";
               l4_opt_map_eq_some967;l4_opt_map2_eq_some967] THEN
  REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if is_var l && not (vfree_in l r) then SUBST_ALL_TAC th
    else if is_var r && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else fail ())) THEN
  EVERY_ASSUM (fun ih ->
    if is_forall (concl ih) then
      EVERY_ASSUM (fun th ->
        try ASSUME_TAC (GEN_ALL (MATCH_MP ih th)) with Failure _ -> ALL_TAC)
    else ALL_TAC) THEN
  ASM_REWRITE_TAC [l4_vlevel_eval961;l4_klevel_eval555;
                   l4_vlevel_imax_nat961;l4_opt_nat973]);;

let l4_klevel_le_sound_vlevel973 = prove
 (`!fuel ps u v u' v'.
   l4_tr_l967 ps u = SOME u' /\
   l4_tr_l967 ps v = SOME v' /\
   l4_klevel_le555 fuel u v = L4KAccept491 T ==>
   l4_vlevel_le961 u' v'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlevel_le961] THEN GEN_TAC THEN
  EVERY_ASSUM (fun th ->
    try ASSUME_TAC (GEN_ALL (MATCH_MP l4_tr_l_eval_eq973 th)) with Failure _ -> ALL_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_klevel_le_sound973]);;

let l4_klevel_equiv_sound_vlevel973 = prove
 (`!fuel ps u v u' v'.
   l4_tr_l967 ps u = SOME u' /\
   l4_tr_l967 ps v = SOME v' /\
   l4_klevel_equiv555 fuel u v = L4KAccept491 T ==>
   l4_vlevel_equiv961 u' v'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vlevel_equiv961] THEN GEN_TAC THEN
  EVERY_ASSUM (fun th ->
    try ASSUME_TAC (GEN_ALL (MATCH_MP l4_tr_l_eval_eq973 th)) with Failure _ -> ALL_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_klevel_equiv_sound973]);;

let l4_klevels_equiv_sound_vlevels973 = prove
 (`!us fuel ps vs us' vs'.
   l4_tr_ls967 ps us = SOME us' /\
   l4_tr_ls967 ps vs = SOME vs' /\
   l4_klevels_equiv555 us fuel vs = L4KAccept491 T ==>
   ALL2 l4_vlevel_equiv961 us' vs'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:l4_klevel447 list` list_CASES) THEN
  REWRITE_TAC [l4_klevels_equiv555;l4_tr_ls967;NULL;HD;TL;NOT_CONS_NIL;
               distinctness "option";injectivity "option";
               distinctness "l4_kresult491";injectivity "l4_kresult491";
               l4_opt_map2_eq_some967;l4_kr_bind_accept967] THENL
  [STRIP_TAC THEN ASM_MESON_TAC [ALL2];
   STRIP_TAC THEN
   FIRST_X_ASSUM (fun th ->
     if is_cond (lhs (concl th)) then
       MP_TAC th THEN COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_kresult491"]
     else fail ()) THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [ALL2] THEN
   ASM_MESON_TAC [l4_klevel_equiv_sound_vlevel973]]);;

let l4_core_level_positive_eval973 = prove
 (`!u rho. l4_core_level_positive555 u ==> 0 < l4_klevel_eval555 u rho`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN
  REWRITE_TAC [l4_core_level_positive555;l4_klevel_eval555;LT_0] THEN
  MESON_TAC [ARITH_RULE
    `(!a b. (0 < a \/ 0 < b) ==> 0 < MAX a b) /\
     (!a b. 0 < b ==> 0 < (if b = 0 then 0 else MAX a b))`]);;

let l4_core_level_positive_sound973 = prove
 (`!ps u u'.
   l4_tr_l967 ps u = SOME u' /\ l4_core_level_positive555 u ==>
   (!ls. 0 < l4_vlevel_eval961 ls u')`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM (fun th ->
    try ASSUME_TAC (GEN_ALL (MATCH_MP l4_tr_l_eval_eq973 th)) with Failure _ -> ALL_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_core_level_positive_eval973]);;

(* ========================================================================= *)
(* 2. Hybrid Local Context (l4_vl_entry973 / l4_vl_ctx_rec973)               *)
(* ========================================================================= *)

let l4_vl_entry_INDUCT973,l4_vl_entry_RECURSION973 = define_type
 "l4_vl_entry973 = L4VLLam973 l4_vexpr961
                 | L4VLLet973 l4_vexpr961 l4_vexpr961";;

let l4_vl_ctx_rec_INDUCT973,l4_vl_ctx_rec_RECURSION973 = define_type
 "l4_vl_ctx_rec973 = L4VLCtx973 ((l4_name # l4_vl_entry973) list) (l4_vl_entry973 list)";;

let l4_vl_free973 = new_recursive_definition l4_vl_ctx_rec_RECURSION973
 `l4_vl_free973 (L4VLCtx973 fs bs) = fs`;;

let l4_vl_bound973 = new_recursive_definition l4_vl_ctx_rec_RECURSION973
 `l4_vl_bound973 (L4VLCtx973 fs bs) = bs`;;

let l4_vl_empty973 = new_definition
 `l4_vl_empty973 = L4VLCtx973 [] []`;;

let l4_vl_push_lam973 = new_definition
 `l4_vl_push_lam973 l ty =
   L4VLCtx973 (l4_vl_free973 l) (CONS (L4VLLam973 ty) (l4_vl_bound973 l))`;;

let l4_vl_push_let973 = new_definition
 `l4_vl_push_let973 l ty val_e =
   L4VLCtx973 (l4_vl_free973 l) (CONS (L4VLLet973 ty val_e) (l4_vl_bound973 l))`;;

let l4_vl_push_free_lam973 = new_definition
 `l4_vl_push_free_lam973 l n ty =
   L4VLCtx973 (CONS (n, L4VLLam973 ty) (l4_vl_free973 l)) (l4_vl_bound973 l)`;;

let l4_vl_push_free_let973 = new_definition
 `l4_vl_push_free_let973 l n ty val_e =
   L4VLCtx973 (CONS (n, L4VLLet973 ty val_e) (l4_vl_free973 l)) (l4_vl_bound973 l)`;;

let l4_vlentries_to_ctx973 = new_recursive_definition list_RECURSION
 `(l4_vlentries_to_ctx973 [] = []) /\
  (l4_vlentries_to_ctx973 (CONS e rest) =
    match e with
    | L4VLLam973 ty -> CONS ty (l4_vlentries_to_ctx973 rest)
    | L4VLLet973 ty val_e -> l4_vlentries_to_ctx973 rest)`;;

let l4_vl_free_ctx973 = new_definition
 `l4_vl_free_ctx973 (fs:(l4_name # l4_vl_entry973) list) = l4_vlentries_to_ctx973 (MAP SND fs)`;;

let l4_vl_ctx973 = new_definition
 `l4_vl_ctx973 l =
   APPEND (l4_vlentries_to_ctx973 (l4_vl_bound973 l))
          (l4_vl_free_ctx973 (l4_vl_free973 l))`;;

let l4_vl_bound_lams973 = new_definition
 `l4_vl_bound_lams973 l = LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;;

let l4_vlentries_to_ctx_append973 = prove
 (`!es1 es2.
   l4_vlentries_to_ctx973 (APPEND es1 es2) =
   APPEND (l4_vlentries_to_ctx973 es1) (l4_vlentries_to_ctx973 es2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;l4_vlentries_to_ctx973] THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  ASM_REWRITE_TAC [APPEND]);;

let l4_vl_ctx_push_lam973 = prove
 (`!l ty. l4_vl_ctx973 (l4_vl_push_lam973 l ty) = CONS ty (l4_vl_ctx973 l)`,
  REWRITE_TAC [l4_vl_ctx973;l4_vl_push_lam973;l4_vl_bound973;l4_vl_free973;
               l4_vlentries_to_ctx973;APPEND]);;

let l4_vl_ctx_push_let973 = prove
 (`!l ty val_e. l4_vl_ctx973 (l4_vl_push_let973 l ty val_e) = l4_vl_ctx973 l`,
  REWRITE_TAC [l4_vl_ctx973;l4_vl_push_let973;l4_vl_bound973;l4_vl_free973;
               l4_vlentries_to_ctx973]);;

let l4_vl_bound_lams_push_lam973 = prove
 (`!l ty. l4_vl_bound_lams973 (l4_vl_push_lam973 l ty) = SUC (l4_vl_bound_lams973 l)`,
  REWRITE_TAC [l4_vl_bound_lams973;l4_vl_push_lam973;l4_vl_bound973;
               l4_vlentries_to_ctx973;LENGTH]);;

let l4_vl_bound_lams_push_let973 = prove
 (`!l ty val_e. l4_vl_bound_lams973 (l4_vl_push_let973 l ty val_e) = l4_vl_bound_lams973 l`,
  REWRITE_TAC [l4_vl_bound_lams973;l4_vl_push_let973;l4_vl_bound973;
               l4_vlentries_to_ctx973]);;

let l4_vl_lookup_bound973 = new_recursive_definition list_RECURSION
 `(l4_vl_lookup_bound973 [] i d = NONE) /\
  (l4_vl_lookup_bound973 (CONS e rest) i d =
    match e with
    | L4VLLam973 ty ->
        if i = 0 then SOME (L4VBVar961 d, l4_vliftN961 ty (SUC d) 0)
        else l4_vl_lookup_bound973 rest (i - 1) (SUC d)
    | L4VLLet973 ty val_e ->
        if i = 0 then SOME (l4_vliftN961 val_e d 0, l4_vliftN961 ty d 0)
        else l4_vl_lookup_bound973 rest (i - 1) d)`;;

let l4_vl_lookup_free973 = new_recursive_definition list_RECURSION
 `(l4_vl_lookup_free973 [] (n:l4_name) d = NONE) /\
  (l4_vl_lookup_free973 (CONS p rest) n d =
    match SND p with
    | L4VLLam973 ty ->
        if n = FST p then SOME (L4VBVar961 d, l4_vliftN961 ty (SUC d) 0)
        else l4_vl_lookup_free973 rest n (SUC d)
    | L4VLLet973 ty val_e ->
        if n = FST p then SOME (l4_vliftN961 val_e d 0, l4_vliftN961 ty d 0)
        else l4_vl_lookup_free973 rest n d)`;;

let l4_vl_bvar973 = new_definition
 `l4_vl_bvar973 l i = l4_vl_lookup_bound973 (l4_vl_bound973 l) i 0`;;

let l4_vl_fvar973 = new_definition
 `l4_vl_fvar973 l n =
   l4_vl_lookup_free973 (l4_vl_free973 l) n (l4_vl_bound_lams973 l)`;;

let l4_subst_all973 =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if is_var l && not (vfree_in l r) then SUBST_ALL_TAC th
    else if is_var r && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else fail ()));;

let l4_vl_lookup_bound_shift_at973 = prove
 (`!es i d n k e ty.
   l4_vl_lookup_bound973 es i d = SOME (e, ty) /\
   k <= d ==>
   l4_vl_lookup_bound973 es i (d + n) =
   SOME (l4_vliftN961 e n k, l4_vliftN961 ty n k)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961] THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC [injectivity "l4_vexpr961"] THEN ARITH_TAC];
    MP_TAC (SPECL [`a:l4_vexpr961`;`SUC d`;`n:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ARITH_RULE `n + SUC d = SUC (d + n)`]]];
   STRIP_TAC THEN
   REWRITE_TAC [ARITH_RULE `SUC (d + n) = SUC d + n`] THEN
   ASM_MESON_TAC [ARITH_RULE `!k d. k <= d ==> k <= SUC d`];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`a1:l4_vexpr961`;`d:num`;`n:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ADD_SYM]];
    MP_TAC (SPECL [`a0:l4_vexpr961`;`d:num`;`n:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ADD_SYM]]];
   STRIP_TAC THEN ASM_MESON_TAC []]);;

let l4_vl_lookup_free_shift_at973 = prove
 (`!fs n d m k e ty.
   l4_vl_lookup_free973 fs n d = SOME (e, ty) /\
   k <= d ==>
   l4_vl_lookup_free973 fs n (d + m) =
   SOME (l4_vliftN961 e m k, l4_vliftN961 ty m k)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_free973;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name # l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN
  STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961] THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC [injectivity "l4_vexpr961"] THEN ARITH_TAC];
    MP_TAC (SPECL [`a:l4_vexpr961`;`SUC d`;`m:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ARITH_RULE `m + SUC d = SUC (d + m)`]]];
   STRIP_TAC THEN
   REWRITE_TAC [ARITH_RULE `SUC (d + m) = SUC d + m`] THEN
   ASM_MESON_TAC [ARITH_RULE `!k d. k <= d ==> k <= SUC d`];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`a1:l4_vexpr961`;`d:num`;`m:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ADD_SYM]];
    MP_TAC (SPECL [`a0:l4_vexpr961`;`d:num`;`m:num`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC [ADD_SYM]]];
   STRIP_TAC THEN ASM_MESON_TAC []]);;

let l4_vl_entries_wf_RULES973,l4_vl_entries_wf_INDUCT973,l4_vl_entries_wf_CASES973 =
  new_inductive_definition
 `(!env uvars base.
     l4_vctx_wf966 env uvars base ==>
     l4_vl_entries_wf973 env uvars base []) /\
  (!env uvars base es ty.
     l4_vl_entries_wf973 env uvars base es /\
     l4_vis_type961 env uvars (APPEND (l4_vlentries_to_ctx973 es) base) ty ==>
     l4_vl_entries_wf973 env uvars base (CONS (L4VLLam973 ty) es)) /\
  (!env uvars base es ty val_e.
     l4_vl_entries_wf973 env uvars base es /\
     l4_vis_type961 env uvars (APPEND (l4_vlentries_to_ctx973 es) base) ty /\
     l4_vhas_type961 env uvars (APPEND (l4_vlentries_to_ctx973 es) base) val_e ty ==>
     l4_vl_entries_wf973 env uvars base (CONS (L4VLLet973 ty val_e) es))`;;

let [l4_vl_entries_wf_nil973; l4_vl_entries_wf_lam973; l4_vl_entries_wf_let973] =
  CONJUNCTS l4_vl_entries_wf_RULES973;;

let l4_vl_ctx_wf973 = new_definition
 `l4_vl_ctx_wf973 env uvars l <=>
   l4_vl_entries_wf973 env uvars [] (MAP SND (l4_vl_free973 l)) /\
   l4_vl_entries_wf973 env uvars (l4_vl_free_ctx973 (l4_vl_free973 l)) (l4_vl_bound973 l)`;;

let l4_vl_entries_wf_to_vctx_wf973 = prove
 (`!env uvars base es.
   l4_vl_entries_wf973 env uvars base es ==>
   l4_vctx_wf966 env uvars (APPEND (l4_vlentries_to_ctx973 es) base)`,
  MATCH_MP_TAC l4_vl_entries_wf_INDUCT973 THEN
  REWRITE_TAC [l4_vlentries_to_ctx973;APPEND;l4_vctx_wf966] THEN
  MESON_TAC []);;

let l4_vl_ctx_wf_to_vctx_wf973 = prove
 (`!env uvars l.
   l4_vl_ctx_wf973 env uvars l ==> l4_vctx_wf966 env uvars (l4_vl_ctx973 l)`,
  REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_ctx973] THEN
  MESON_TAC [l4_vl_entries_wf_to_vctx_wf973]);;

let l4_vl_ctx_wf_empty973 = prove
 (`!env uvars. l4_vl_ctx_wf973 env uvars l4_vl_empty973`,
  REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_empty973;l4_vl_free973;l4_vl_bound973;
               l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973] THEN
  MESON_TAC [l4_vl_entries_wf_nil973;l4_vctx_wf966]);;

let l4_vl_ctx_wf_push_lam973 = prove
 (`!env uvars l ty.
   l4_vl_ctx_wf973 env uvars l /\
   l4_vis_type961 env uvars (l4_vl_ctx973 l) ty ==>
   l4_vl_ctx_wf973 env uvars (l4_vl_push_lam973 l ty)`,
  REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_push_lam973;l4_vl_free973;
               l4_vl_bound973;l4_vl_ctx973] THEN
  MESON_TAC [l4_vl_entries_wf_lam973]);;

let l4_vl_ctx_wf_push_let973 = prove
 (`!env uvars l ty val_e.
   l4_vl_ctx_wf973 env uvars l /\
   l4_vis_type961 env uvars (l4_vl_ctx973 l) ty /\
   l4_vhas_type961 env uvars (l4_vl_ctx973 l) val_e ty ==>
   l4_vl_ctx_wf973 env uvars (l4_vl_push_let973 l ty val_e)`,
  REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_push_let973;l4_vl_free973;
               l4_vl_bound973;l4_vl_ctx973] THEN
  MESON_TAC [l4_vl_entries_wf_let973]);;

let l4_vl_entries_wf_mono973 = prove
 (`!env1 uvars base es.
   l4_vl_entries_wf973 env1 uvars base es ==>
   (!env2. l4_venv_ordered961 env1 env2 ==> l4_vl_entries_wf973 env2 uvars base es)`,
  MATCH_MP_TAC l4_vl_entries_wf_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_nil973 THEN
   UNDISCH_TAC `l4_vctx_wf966 env uvars base` THEN
   SPEC_TAC (`base:l4_vexpr961 list`,`g:l4_vexpr961 list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vctx_wf966] THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_lam973 THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_let973 THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966;
                  l4_venv_ordered_preserve_vhas_type961]]);;

let l4_vl_ctx_wf_mono973 = prove
 (`!env1 env2 uvars l.
   l4_venv_ordered961 env1 env2 /\ l4_vl_ctx_wf973 env1 uvars l ==>
   l4_vl_ctx_wf973 env2 uvars l`,
  REWRITE_TAC [l4_vl_ctx_wf973] THEN MESON_TAC [l4_vl_entries_wf_mono973]);;

let l4_vl_lookup_bound_has_type_gen973 = prove
 (`!env uvars base es.
   l4_vl_entries_wf973 env uvars base es ==>
   (!pre i e ty.
     l4_venv_closed966 env /\
     l4_vl_lookup_bound973 es i (LENGTH pre) = SOME (e, ty) ==>
     l4_vhas_type961 env uvars
       (APPEND pre (APPEND (l4_vlentries_to_ctx973 es) base)) e ty)`,
  MATCH_MP_TAC l4_vl_entries_wf_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option"];
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_bound973]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
    MP_TAC (SPECL [`pre:l4_vexpr961 list`;
                   `CONS (ty:l4_vexpr961) (APPEND (l4_vlentries_to_ctx973 es) base)`;
                   `0`;`l4_vlift961 ty`] l4_vlookup_append_prefix966) THEN
    REWRITE_TAC [l4_vlookup_zero961] THEN
    REWRITE_TAC [APPEND;ADD_CLAUSES;l4_vlift961;l4_vliftN_add_le973;
                 ARITH_RULE `1 + x = SUC x /\ x + 1 = SUC x`] THEN SIMP_TAC [];
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`APPEND pre [ty:l4_vexpr961]`;`i - 1`;`e:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    REWRITE_TAC [LENGTH_APPEND;LENGTH;ADD_CLAUSES;
                 GSYM APPEND_ASSOC;APPEND;l4_vlentries_to_ctx973] THEN
    ASM_SIMP_TAC []];
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_bound973]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `APPEND (l4_vlentries_to_ctx973 es) base` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REFL_TAC;
    DISCH_TAC THEN
    REWRITE_TAC [l4_vlentries_to_ctx973] THEN
    ASM_MESON_TAC []]]);;

let l4_vl_lookup_bound_has_type973 = prove
 (`!env uvars l i e ty.
   l4_venv_closed966 env /\
   l4_vl_ctx_wf973 env uvars l /\
   l4_vl_bvar973 l i = SOME (e, ty) ==>
   l4_vhas_type961 env uvars (l4_vl_ctx973 l) e ty`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l4_vl_free_ctx973 (l4_vl_free973 l)`;
                 `l4_vl_bound973 l`] l4_vl_lookup_bound_has_type_gen973) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_wf973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`[]:l4_vexpr961 list`;`i:num`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [LENGTH;APPEND;GSYM l4_vl_bvar973;GSYM l4_vl_ctx973]);;

let l4_vl_lookup_free_has_type_gen973 = prove
 (`!env uvars fs.
   l4_vl_entries_wf973 env uvars [] (MAP SND fs) ==>
   (!pre n e ty.
     l4_venv_closed966 env /\
     l4_vl_lookup_free973 fs n (LENGTH pre) = SOME (e, ty) ==>
     l4_vhas_type961 env uvars
       (APPEND pre (l4_vl_free_ctx973 fs)) e ty)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC [l4_vl_lookup_free973;distinctness "option"];
   STRUCT_CASES_TAC (ISPEC `h:l4_name # l4_vl_entry973` PAIR_SURJECTIVE) THEN
   REWRITE_TAC [MAP;SND;FST;l4_vl_free_ctx973;l4_vl_lookup_free973] THEN
   STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
   REWRITE_TAC [] THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vl_entries_wf_CASES973] THEN
   REWRITE_TAC [distinctness "list";injectivity "list";
                distinctness "l4_vl_entry973";injectivity "l4_vl_entry973"] THEN
   STRIP_TAC THEN l4_subst_all973 THEN REPEAT STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
    [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
     l4_subst_all973 THEN
     REWRITE_TAC [l4_vlentries_to_ctx973;l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
     MP_TAC (SPECL [`pre:l4_vexpr961 list`;
                    `CONS (ty:l4_vexpr961) (l4_vlentries_to_ctx973 (MAP SND (t:(l4_name#l4_vl_entry973) list)))`;
                    `0`;`l4_vlift961 ty`] l4_vlookup_append_prefix966) THEN
     REWRITE_TAC [l4_vlookup_zero961] THEN
     REWRITE_TAC [APPEND;ADD_CLAUSES;l4_vlift961;l4_vliftN_add_le973;
                  ARITH_RULE `1 + x = SUC x /\ x + 1 = SUC x`] THEN SIMP_TAC [];
     DISCH_TAC THEN
     FIRST_X_ASSUM (fun ih ->
       FIRST_ASSUM (fun hw ->
         MP_TAC (SPECL [`APPEND pre [ty:l4_vexpr961]`;`n:l4_name`;`e:l4_vexpr961`;`ty':l4_vexpr961`]
           (MATCH_MP ih hw)))) THEN
     ASM_REWRITE_TAC [l4_vl_free_ctx973;LENGTH_APPEND;LENGTH;
                      ADD_CLAUSES;GSYM APPEND_ASSOC;APPEND;
                      l4_vlentries_to_ctx973]];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
    [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
     l4_subst_all973 THEN
     REWRITE_TAC [l4_vlentries_to_ctx973;l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
     EXISTS_TAC `l4_vlentries_to_ctx973 (MAP SND (t:(l4_name#l4_vl_entry973) list))` THEN
     RULE_ASSUM_TAC (REWRITE_RULE [APPEND_NIL]) THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REFL_TAC;
     DISCH_TAC THEN REWRITE_TAC [l4_vlentries_to_ctx973] THEN
     ASM_MESON_TAC [l4_vl_free_ctx973]]]]);;

let l4_vl_lookup_free_has_type973 = prove
 (`!env uvars l n e ty.
   l4_venv_closed966 env /\
   l4_vl_ctx_wf973 env uvars l /\
   l4_vl_fvar973 l n = SOME (e, ty) ==>
   l4_vhas_type961 env uvars (l4_vl_ctx973 l) e ty`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l4_vl_free973 l`]
    l4_vl_lookup_free_has_type_gen973) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_wf973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`l4_vlentries_to_ctx973 (l4_vl_bound973 l)`;`n:l4_name`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973;GSYM l4_vl_ctx973]);;

let l4_vl_entries_defeq_RULES973,l4_vl_entries_defeq_INDUCT973,l4_vl_entries_defeq_CASES973 =
  new_inductive_definition
 `(!env uvars b1 b2.
     l4_vis_defeq_ctx966 env uvars [] b1 b2 ==>
     l4_vl_entries_defeq973 env uvars b1 b2 [] []) /\
  (!env uvars b1 b2 es1 es2 ty1 ty2 u.
     l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 /\
     l4_vis_defeq961 env uvars (APPEND (l4_vlentries_to_ctx973 es1) b1) ty1 ty2 (L4VSort961 u) ==>
     l4_vl_entries_defeq973 env uvars b1 b2
       (CONS (L4VLLam973 ty1) es1) (CONS (L4VLLam973 ty2) es2)) /\
  (!env uvars b1 b2 es1 es2 ty1 ty2 val1 val2 u.
     l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 /\
     l4_vis_defeq961 env uvars (APPEND (l4_vlentries_to_ctx973 es1) b1) ty1 ty2 (L4VSort961 u) /\
     l4_vis_defeq961 env uvars (APPEND (l4_vlentries_to_ctx973 es1) b1) val1 val2 ty1 ==>
     l4_vl_entries_defeq973 env uvars b1 b2
       (CONS (L4VLLet973 ty1 val1) es1) (CONS (L4VLLet973 ty2 val2) es2))`;;

let [l4_vl_entries_defeq_nil973; l4_vl_entries_defeq_lam973; l4_vl_entries_defeq_let973] =
  CONJUNCTS l4_vl_entries_defeq_RULES973;;

let l4_vl_ctx_defeq973 = new_definition
 `l4_vl_ctx_defeq973 env uvars l1 l2 <=>
   MAP FST (l4_vl_free973 l1) = MAP FST (l4_vl_free973 l2) /\
   l4_vl_entries_defeq973 env uvars [] []
     (MAP SND (l4_vl_free973 l1)) (MAP SND (l4_vl_free973 l2)) /\
   l4_vl_entries_defeq973 env uvars
     (l4_vl_free_ctx973 (l4_vl_free973 l1))
     (l4_vl_free_ctx973 (l4_vl_free973 l2))
     (l4_vl_bound973 l1) (l4_vl_bound973 l2)`;;

let l4_vl_entries_defeq_len_ctx973 = prove
 (`!env uvars b1 b2 es1 es2.
   l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 ==>
   LENGTH (l4_vlentries_to_ctx973 es1) = LENGTH (l4_vlentries_to_ctx973 es2)`,
  MATCH_MP_TAC l4_vl_entries_defeq_INDUCT973 THEN
  REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH] THEN SIMP_TAC []);;

let l4_vl_entries_defeq_to_vis_defeq_ctx973 = prove
 (`!env uvars b1 b2 es1 es2.
   l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 ==>
   l4_vis_defeq_ctx966 env uvars []
     (APPEND (l4_vlentries_to_ctx973 es1) b1)
     (APPEND (l4_vlentries_to_ctx973 es2) b2)`,
  MATCH_MP_TAC l4_vl_entries_defeq_INDUCT973 THEN
  REWRITE_TAC [l4_vlentries_to_ctx973;APPEND] THEN
  MESON_TAC [l4_vis_defeq_ctx_succ966]);;

let l4_vl_ctx_defeq_to_vis_defeq_ctx973 = prove
 (`!env uvars l1 l2.
   l4_vl_ctx_defeq973 env uvars l1 l2 ==>
   l4_vis_defeq_ctx966 env uvars [] (l4_vl_ctx973 l1) (l4_vl_ctx973 l2)`,
  REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_ctx973] THEN
  MESON_TAC [l4_vl_entries_defeq_to_vis_defeq_ctx973]);;

let l4_vl_entries_defeq_refl973 = prove
 (`!env uvars base es.
   l4_vl_entries_wf973 env uvars base es ==>
   l4_vl_entries_defeq973 env uvars base base es es`,
  MATCH_MP_TAC l4_vl_entries_wf_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_defeq_nil973 THEN
   UNDISCH_TAC `l4_vctx_wf966 env uvars base` THEN
   SPEC_TAC (`base:l4_vexpr961 list`,`g:l4_vexpr961 list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vctx_wf966;l4_vis_defeq_ctx_zero966] THEN
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_ctx_succ966];
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   MESON_TAC [l4_vl_entries_defeq_lam973];
   REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
   MESON_TAC [l4_vl_entries_defeq_let973]]);;

let l4_vl_ctx_defeq_refl973 = prove
 (`!env uvars l.
   l4_vl_ctx_wf973 env uvars l ==> l4_vl_ctx_defeq973 env uvars l l`,
  REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_ctx_defeq973] THEN
  MESON_TAC [l4_vl_entries_defeq_refl973]);;

let l4_vl_entries_defeq_symm973 = prove
 (`!env uvars b1 b2 es1 es2.
   l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 ==>
   l4_venv_closed966 env ==>
   l4_vl_entries_defeq973 env uvars b2 b1 es2 es1`,
  MATCH_MP_TAC l4_vl_entries_defeq_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_defeq_nil973 THEN
   ASM_MESON_TAC [l4_vis_defeq_ctx_symm966];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_SIMP_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
   MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`APPEND (l4_vlentries_to_ctx973 es1) b1`] THEN
   ASM_MESON_TAC [l4_vl_entries_defeq_to_vis_defeq_ctx973;l4_vis_defeq_ctx_symm966;l4_vis_defeq_symm961];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`APPEND (l4_vlentries_to_ctx973 es1) b1`] THEN
    ASM_MESON_TAC [l4_vl_entries_defeq_to_vis_defeq_ctx973;l4_vis_defeq_ctx_symm966;l4_vis_defeq_symm961];
    MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`APPEND (l4_vlentries_to_ctx973 es1) b1`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vl_entries_defeq_to_vis_defeq_ctx973;l4_vis_defeq_ctx_symm966];
     MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`ty1:l4_vexpr961`;`u:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961]]]]);;

let l4_vl_ctx_defeq_symm973 = prove
 (`!env uvars l1 l2.
   l4_venv_closed966 env /\ l4_vl_ctx_defeq973 env uvars l1 l2 ==>
   l4_vl_ctx_defeq973 env uvars l2 l1`,
  REWRITE_TAC [l4_vl_ctx_defeq973] THEN
  MESON_TAC [l4_vl_entries_defeq_symm973]);;

let l4_vl_lookup_bound_defeq_gen973 = prove
 (`!env uvars b1 b2 es1 es2.
   l4_vl_entries_defeq973 env uvars b1 b2 es1 es2 ==>
   (!pre1 (pre2:l4_vexpr961 list) i e1 ty1.
     l4_venv_closed966 env /\
     LENGTH pre1 = LENGTH pre2 /\
     l4_vl_lookup_bound973 es1 i (LENGTH pre1) = SOME (e1, ty1) ==>
     ?e2 ty2.
       l4_vl_lookup_bound973 es2 i (LENGTH pre2) = SOME (e2, ty2) /\
       l4_vis_defeq961 env uvars
         (APPEND pre1 (APPEND (l4_vlentries_to_ctx973 es1) b1)) e1 e2 ty1)`,
  MATCH_MP_TAC l4_vl_entries_defeq_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option"];
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_bound973]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973] THEN
    MAP_EVERY EXISTS_TAC [`L4VBVar961 (LENGTH (pre2:l4_vexpr961 list))`;
                          `l4_vliftN961 ty2 (SUC (LENGTH (pre2:l4_vexpr961 list))) 0`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
    MP_TAC (SPECL [`pre1:l4_vexpr961 list`;
                   `CONS (ty1:l4_vexpr961) (APPEND (l4_vlentries_to_ctx973 es1) b1)`;
                   `0`;`l4_vlift961 ty1`] l4_vlookup_append_prefix966) THEN
    REWRITE_TAC [l4_vlookup_zero961] THEN
    REWRITE_TAC [APPEND;ADD_CLAUSES;l4_vlift961;l4_vliftN_add_le973;
                 ARITH_RULE `1 + x = SUC x /\ x + 1 = SUC x`] THEN
    ASM_SIMP_TAC [];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`APPEND pre1 [ty1:l4_vexpr961]`;`APPEND pre2 [ty2:l4_vexpr961]`;
       `i - 1`;`e1:l4_vexpr961`;`ty1':l4_vexpr961`]) THEN
    ASM_SIMP_TAC [LENGTH_APPEND;LENGTH;ADD_CLAUSES;
                  GSYM APPEND_ASSOC;APPEND;l4_vlentries_to_ctx973] THEN
    ASM_MESON_TAC []];
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_bound973]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973] THEN
    MAP_EVERY EXISTS_TAC [`l4_vliftN961 val2 (LENGTH (pre2:l4_vexpr961 list)) 0`;
                          `l4_vliftN961 ty2 (LENGTH (pre2:l4_vexpr961 list)) 0`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `APPEND (l4_vlentries_to_ctx973 es1) b1` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_liftN_zero966 THEN ASM_REWRITE_TAC [];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC []]]);;

let l4_vl_lookup_bound_defeq973 = prove
 (`!env uvars l1 l2 i e1 ty1.
   l4_venv_closed966 env /\
   l4_vl_ctx_defeq973 env uvars l1 l2 /\
   l4_vl_bvar973 l1 i = SOME (e1, ty1) ==>
   ?e2 ty2.
     l4_vl_bvar973 l2 i = SOME (e2, ty2) /\
     l4_vis_defeq961 env uvars (l4_vl_ctx973 l1) e1 e2 ty1`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;
                 `l4_vl_free_ctx973 (l4_vl_free973 l1)`;
                 `l4_vl_free_ctx973 (l4_vl_free973 l2)`;
                 `l4_vl_bound973 l1`;`l4_vl_bound973 l2`]
    l4_vl_lookup_bound_defeq_gen973) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_defeq973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`[]:l4_vexpr961 list`;`[]:l4_vexpr961 list`;`i:num`;`e1:l4_vexpr961`;`ty1:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [LENGTH;APPEND;GSYM l4_vl_bvar973;GSYM l4_vl_ctx973]);;

let l4_vl_lookup_free_defeq_gen973 = prove
 (`!env uvars fs1 fs2.
   MAP FST fs1 = MAP FST fs2 /\
   l4_vl_entries_defeq973 env uvars [] [] (MAP SND fs1) (MAP SND fs2) ==>
   (!pre1 (pre2:l4_vexpr961 list) n e1 ty1.
     l4_venv_closed966 env /\
     LENGTH pre1 = LENGTH pre2 /\
     l4_vl_lookup_free973 fs1 n (LENGTH pre1) = SOME (e1, ty1) ==>
     ?e2 ty2.
       l4_vl_lookup_free973 fs2 n (LENGTH pre2) = SOME (e2, ty2) /\
       l4_vis_defeq961 env uvars (APPEND pre1 (l4_vl_free_ctx973 fs1)) e1 e2 ty1)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `fs2:(l4_name#l4_vl_entry973) list` list_CASES) THEN
  REWRITE_TAC [MAP;distinctness "list";injectivity "list";
               l4_vl_lookup_free973;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `h':l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vl_entries_defeq_CASES973]) THEN
  REWRITE_TAC [distinctness "list";injectivity "list";
               distinctness "l4_vl_entry973";injectivity "l4_vl_entry973"] THEN
  STRIP_TAC THEN l4_subst_all973 THEN REPEAT STRIP_TAC THENL
  [POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_free973;FST;SND]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vl_lookup_free973;FST;SND;l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973] THEN
    MAP_EVERY EXISTS_TAC [`L4VBVar961 (LENGTH (pre2:l4_vexpr961 list))`;
                          `l4_vliftN961 ty2 (SUC (LENGTH (pre2:l4_vexpr961 list))) 0`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
    MP_TAC (SPECL [`pre1:l4_vexpr961 list`;
                   `CONS (ty1:l4_vexpr961) (l4_vlentries_to_ctx973 (MAP SND (t:(l4_name#l4_vl_entry973) list)))`;
                   `0`;`l4_vlift961 ty1`] l4_vlookup_append_prefix966) THEN
    REWRITE_TAC [l4_vlookup_zero961] THEN
    REWRITE_TAC [APPEND;ADD_CLAUSES;l4_vlift961;l4_vliftN_add_le973;
                 ARITH_RULE `1 + x = SUC x /\ x + 1 = SUC x`] THEN
    ASM_SIMP_TAC [];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_free973;FST;SND] THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`t':(l4_name#l4_vl_entry973) list`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL
      [`APPEND pre1 [ty1:l4_vexpr961]`;`APPEND pre2 [ty2:l4_vexpr961]`;
       `n:l4_name`;`e1:l4_vexpr961`;`ty1':l4_vexpr961`]) THEN
    ASM_SIMP_TAC [LENGTH_APPEND;LENGTH;ADD_CLAUSES;
                  GSYM APPEND_ASSOC;APPEND;l4_vl_free_ctx973;MAP;SND;
                  l4_vlentries_to_ctx973] THEN
    ASM_MESON_TAC []];
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vl_lookup_free973;FST;SND]) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    REWRITE_TAC [l4_vl_lookup_free973;FST;SND;l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973] THEN
    MAP_EVERY EXISTS_TAC [`l4_vliftN961 val2 (LENGTH (pre2:l4_vexpr961 list)) 0`;
                          `l4_vliftN961 ty2 (LENGTH (pre2:l4_vexpr961 list)) 0`] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vlentries_to_ctx973 (MAP SND (t:(l4_name#l4_vl_entry973) list))` THEN
    RULE_ASSUM_TAC (REWRITE_RULE [APPEND_NIL]) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vctx_liftN_zero966 THEN ASM_REWRITE_TAC [];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_free973;FST;SND;l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [l4_vl_free_ctx973]]]);;

let l4_vl_lookup_free_defeq973 = prove
 (`!env uvars l1 l2 n e1 ty1.
   l4_venv_closed966 env /\
   l4_vl_ctx_defeq973 env uvars l1 l2 /\
   l4_vl_fvar973 l1 n = SOME (e1, ty1) ==>
   ?e2 ty2.
     l4_vl_fvar973 l2 n = SOME (e2, ty2) /\
     l4_vis_defeq961 env uvars (l4_vl_ctx973 l1) e1 e2 ty1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vl_bound_lams973 l1 = l4_vl_bound_lams973 l2` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vl_bound_lams973] THEN
   ASM_MESON_TAC [l4_vl_ctx_defeq973;l4_vl_entries_defeq_len_ctx973];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l4_vl_free973 l1`;`l4_vl_free973 l2`]
    l4_vl_lookup_free_defeq_gen973) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_defeq973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`l4_vlentries_to_ctx973 (l4_vl_bound973 l1)`;
     `l4_vlentries_to_ctx973 (l4_vl_bound973 l2)`;
     `n:l4_name`;`e1:l4_vexpr961`;`ty1:l4_vexpr961`]) THEN
  REWRITE_TAC [GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973;GSYM l4_vl_ctx973] THEN
  ASM_SIMP_TAC []);;

(* ========================================================================= *)
(* 3. Literal Translations & Primitives Specifications                       *)
(* ========================================================================= *)

let l4_nat_lit973 = new_recursive_definition num_RECURSION
 `(l4_nat_lit973 0 = L4VConst961 l4_core_zero_name533 []) /\
  (l4_nat_lit973 (SUC n) = L4VApp961 (L4VConst961 l4_core_succ_name533 []) (l4_nat_lit973 n))`;;

let l4_nat_lit_closed973 = prove
 (`!n k. l4_vclosedN961 (l4_nat_lit973 n) k`,
  INDUCT_TAC THEN REWRITE_TAC [l4_nat_lit973;l4_vclosedN961] THEN
  ASM_REWRITE_TAC []);;

let l4_vliftN_nat_lit973 = prove
 (`!n m k. l4_vliftN961 (l4_nat_lit973 n) m k = l4_nat_lit973 n`,
  INDUCT_TAC THEN REWRITE_TAC [l4_nat_lit973;l4_vliftN961] THEN
  ASM_REWRITE_TAC []);;

let l4_vinst_nat_lit973 = prove
 (`!n v k. l4_vinst961 (l4_nat_lit973 n) v k = l4_nat_lit973 n`,
  INDUCT_TAC THEN REWRITE_TAC [l4_nat_lit973;l4_vinst961] THEN
  ASM_REWRITE_TAC []);;

let l4_vinstL_nat_lit973 = prove
 (`!n ls. l4_vinstL961 ls (l4_nat_lit973 n) = l4_nat_lit973 n`,
  INDUCT_TAC THEN REWRITE_TAC [l4_nat_lit973;l4_vinstL961;MAP] THEN
  ASM_REWRITE_TAC []);;

let l4_vnat_ty973 = new_definition
 `l4_vnat_ty973 = L4VConst961 l4_core_nat_name533 []`;;

let l4_vbool_ty973 = new_definition
 `l4_vbool_ty973 = L4VConst961 l4_core_bool_name533 []`;;

let l4_vchar_ty973 = new_definition
 `l4_vchar_ty973 = L4VConst961 l4_core_char_name533 []`;;

let l4_vstring_ty973 = new_definition
 `l4_vstring_ty973 = L4VConst961 l4_core_string_name533 []`;;

let l4_vlist_char_ty973 = new_definition
 `l4_vlist_char_ty973 =
   L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) l4_vchar_ty973`;;

let l4_vbool_lit973 = new_definition
 `l4_vbool_lit973 b =
   L4VConst961 (if b then l4_core_true_name533 else l4_core_false_name533) []`;;

let l4_tr_char_list973 = new_recursive_definition list_RECURSION
 `(l4_tr_char_list973 [] =
    L4VApp961 (L4VConst961 (L4String l4_core_list_name539 [110;105;108]) [L4VLZero961])
              l4_vchar_ty973) /\
  (l4_tr_char_list973 (CONS c cs) =
    l4_vapps962
      [l4_vchar_ty973;
       L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 c);
       l4_tr_char_list973 cs]
      (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961]))`;;

let l4_tr_str_lit973 = new_definition
 `l4_tr_str_lit973 bytes =
   match l4_core_utf8_539 bytes with
   | NONE -> NONE
   | SOME cs -> SOME (L4VApp961 (L4VConst961 l4_core_string_of_list533 [])
                                (l4_tr_char_list973 cs))`;;

let l4_tr_char_list_closed973 = prove
 (`!cs k. l4_vclosedN961 (l4_tr_char_list973 cs) k`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_tr_char_list973;l4_vapps962;l4_vchar_ty973;l4_vclosedN961;
               l4_nat_lit_closed973] THEN
  ASM_REWRITE_TAC []);;

let l4_vliftN_tr_char_list973 = prove
 (`!cs m k. l4_vliftN961 (l4_tr_char_list973 cs) m k = l4_tr_char_list973 cs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_tr_char_list973;l4_vapps962;l4_vchar_ty973;l4_vliftN961;
               l4_vliftN_nat_lit973] THEN
  ASM_REWRITE_TAC []);;

let l4_vinst_tr_char_list973 = prove
 (`!cs v k. l4_vinst961 (l4_tr_char_list973 cs) v k = l4_tr_char_list973 cs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_tr_char_list973;l4_vapps962;l4_vchar_ty973;l4_vinst961;
               l4_vinst_nat_lit973] THEN
  ASM_REWRITE_TAC []);;

let l4_vinstL_tr_char_list973 = prove
 (`!cs ls. l4_vinstL961 ls (l4_tr_char_list973 cs) = l4_tr_char_list973 cs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_tr_char_list973;l4_vapps962;l4_vchar_ty973;l4_vinstL961;
               MAP;l4_vlevel_inst961;l4_vinstL_nat_lit973] THEN
  ASM_REWRITE_TAC []);;

let l4_tr_str_lit_closed973 = prove
 (`!bytes e k. l4_tr_str_lit973 bytes = SOME e ==> l4_vclosedN961 e k`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [l4_vclosedN961;l4_tr_char_list_closed973]);;

let l4_vliftN_tr_str_lit973 = prove
 (`!bytes e m k. l4_tr_str_lit973 bytes = SOME e ==> l4_vliftN961 e m k = e`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [l4_vliftN961;l4_vliftN_tr_char_list973]);;

let l4_vinst_tr_str_lit973 = prove
 (`!bytes e v k. l4_tr_str_lit973 bytes = SOME e ==> l4_vinst961 e v k = e`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [l4_vinst961;l4_vinst_tr_char_list973]);;

let l4_vinstL_tr_str_lit973 = prove
 (`!bytes e ls. l4_tr_str_lit973 bytes = SOME e ==> l4_vinstL961 ls e = e`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [l4_vinstL961;MAP;l4_vinstL_tr_char_list973]);;

let l4_vbinary_prim_spec973 = new_definition
 `l4_vbinary_prim_spec973 op a b =
   match op with
   | L4KPNatAdd493 -> SOME (l4_nat_lit973 (a + b), l4_vnat_ty973)
   | L4KPNatSub493 -> SOME (l4_nat_lit973 (a - b), l4_vnat_ty973)
   | L4KPNatMul493 -> SOME (l4_nat_lit973 (a * b), l4_vnat_ty973)
   | L4KPNatPow493 -> SOME (l4_nat_lit973 (a EXP b), l4_vnat_ty973)
   | L4KPNatGcd493 -> SOME (l4_nat_lit973 (gcd (a, b)), l4_vnat_ty973)
   | L4KPNatMod493 -> SOME (l4_nat_lit973 (a MOD b), l4_vnat_ty973)
   | L4KPNatDiv493 -> SOME (l4_nat_lit973 (a DIV b), l4_vnat_ty973)
   | L4KPNatBEq493 -> SOME (l4_vbool_lit973 (a = b), l4_vbool_ty973)
   | L4KPNatBLE493 -> SOME (l4_vbool_lit973 (a <= b), l4_vbool_ty973)
   | L4KPNatLAnd493 -> SOME (l4_nat_lit973 (l4_core_bitop544 (\x y. x /\ y) a b), l4_vnat_ty973)
   | L4KPNatLOr493 -> SOME (l4_nat_lit973 (l4_core_bitop544 (\x y. x \/ y) a b), l4_vnat_ty973)
   | L4KPNatXor493 -> SOME (l4_nat_lit973 (l4_core_bitop544 (\x y. ~(x <=> y)) a b), l4_vnat_ty973)
   | L4KPNatShiftLeft493 -> SOME (l4_nat_lit973 (a * 2 EXP b), l4_vnat_ty973)
   | L4KPNatShiftRight493 -> SOME (l4_nat_lit973 (a DIV 2 EXP b), l4_vnat_ty973)
   | _ -> NONE`;;

(* ========================================================================= *)
(* 4. Genuine Structure Projections (l4_vtr_proj973, l4_vproj_telescope973)  *)
(* ========================================================================= *)

let l4_vtr_proj973 = new_definition
 `l4_vtr_proj973 env venv uvars g owner idx sv pv fty <=>
   ?info ctor c d us params indices.
     l4_core_inductive532 env owner = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     idx < l4_kctor_num_fields493 c /\
     LENGTH params = l4_kind_num_params493 info /\
     LENGTH indices = l4_kind_num_indices493 info /\
     ALL (l4_vlevel_wf961 uvars) us /\
     LENGTH us = LENGTH (l4_kdecl_params493 d) /\
     l4_vhas_type961 venv uvars g sv
       (l4_vapps962 (APPEND params indices) (L4VConst961 owner us)) /\
     pv = l4_vproj_expr962 owner idx us params sv /\
     l4_vhas_type961 venv uvars g pv fty`;;

let l4_vproj_telescope_RULES973,l4_vproj_telescope_INDUCT973,l4_vproj_telescope_CASES973 =
  new_inductive_definition
 `(!(env:l4_kdeclaration493 list) venv uvars g owner us params sv mp idx ty dom body.
     l4_vis_defeq_u961 venv uvars g ty (L4VForallE961 dom body) /\
     (mp ==> l4_vhas_type961 venv uvars g dom (L4VSort961 L4VLZero961)) ==>
     l4_vproj_telescope973 env venv uvars g owner us params sv mp 0 idx ty dom) /\
  (!(env:l4_kdeclaration493 list) venv uvars g owner us params sv mp skip idx ty dom body res.
     l4_vis_defeq_u961 venv uvars g ty (L4VForallE961 dom body) /\
     (mp /\ (!b0. ~(body = l4_vlift961 b0)) ==>
       l4_vhas_type961 venv uvars g dom (L4VSort961 L4VLZero961)) /\
     l4_vproj_telescope973 env venv uvars g owner us params sv mp skip (SUC idx)
       (l4_vinst0961 body (l4_vproj_expr962 owner idx us params sv)) res ==>
     l4_vproj_telescope973 env venv uvars g owner us params sv mp (SUC skip) idx ty res)`;;

let [l4_vpt_zero973; l4_vpt_succ973] = CONJUNCTS l4_vproj_telescope_RULES973;;

let l4_vtr_proj_has_type973 = prove
 (`!env venv uvars g owner idx sv pv fty.
   l4_vtr_proj973 env venv uvars g owner idx sv pv fty ==>
   l4_vhas_type961 venv uvars g pv fty`,
  REWRITE_TAC [l4_vtr_proj973] THEN MESON_TAC []);;

let l4_vtr_proj_monotonic_env973 = prove
 (`!env venv1 venv2 uvars g owner idx sv pv fty.
   l4_venv_ordered961 venv1 venv2 /\
   l4_vtr_proj973 env venv1 uvars g owner idx sv pv fty ==>
   l4_vtr_proj973 env venv2 uvars g owner idx sv pv fty`,
  REWRITE_TAC [l4_vtr_proj973] THEN
  MESON_TAC [l4_venv_ordered_preserve_vhas_type961]);;

let l4_vtr_proj_weakN973 = prove
 (`!env venv uvars n k g g' owner idx sv pv fty.
   l4_venv_closed966 venv /\
   l4_vctx_liftN966 n k g g' /\
   l4_vtr_proj973 env venv uvars g owner idx sv pv fty ==>
   l4_vtr_proj973 env venv uvars g' owner idx
     (l4_vliftN961 sv n k) (l4_vliftN961 pv n k) (l4_vliftN961 fty n k)`,
  REWRITE_TAC [l4_vtr_proj973] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`us:l4_vlevel961 list`;
     `MAP (\a. l4_vliftN961 a n k) params`;`MAP (\a. l4_vliftN961 a n k) indices`] THEN
  ASM_REWRITE_TAC [LENGTH_MAP] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [GSYM MAP_APPEND;GSYM l4_vliftN961;GSYM l4_vliftN_vapps962;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `sv:l4_vexpr961`;`sv:l4_vexpr961`;
                  `l4_vapps962 (APPEND params indices) (L4VConst961 owner us)`;
                  `n:num`;`k:num`;`g':l4_vexpr961 list`]
     l4_vis_defeq_weakN966) THEN
   ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vliftN_vapps962;l4_vliftN961;MAP_APPEND];
   ASM_REWRITE_TAC [l4_vproj_expr962;l4_vliftN961;l4_vliftN_vapps962];
   REWRITE_TAC [l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_weakN966;l4_vhas_type961]]);;

let l4_vtr_proj_instN973 = prove
 (`!env venv uvars g0 e0 a0 k g1 g owner idx sv pv fty.
   l4_venv_closed966 venv /\
   l4_vhas_type961 venv uvars g0 e0 a0 /\
   l4_vctx_instN966 g0 e0 a0 k g1 g /\
   l4_vtr_proj973 env venv uvars g1 owner idx sv pv fty ==>
   l4_vtr_proj973 env venv uvars g owner idx
     (l4_vinst961 sv e0 k) (l4_vinst961 pv e0 k) (l4_vinst961 fty e0 k)`,
  REWRITE_TAC [l4_vtr_proj973] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`us:l4_vlevel961 list`;
     `MAP (\a. l4_vinst961 a e0 k) params`;`MAP (\a. l4_vinst961 a e0 k) indices`] THEN
  ASM_REWRITE_TAC [LENGTH_MAP] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g0:l4_vexpr961 list`;
                  `e0:l4_vexpr961`;`a0:l4_vexpr961`;`g1:l4_vexpr961 list`;
                  `sv:l4_vexpr961`;`sv:l4_vexpr961`;
                  `l4_vapps962 (APPEND params indices) (L4VConst961 owner us)`;
                  `k:num`;`g:l4_vexpr961 list`]
     l4_vis_defeq_instN966) THEN
   ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vinst_vapps973;l4_vinst961;MAP_APPEND];
   ASM_REWRITE_TAC [l4_vproj_expr962;l4_vinst961;l4_vinst_vapps973];
   REWRITE_TAC [l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_instN966;l4_vhas_type961]]);;

let l4_vtr_proj_instL973 = prove
 (`!env venv uvars uvars' ls g owner idx sv pv fty.
   ALL (l4_vlevel_wf961 uvars') ls /\
   LENGTH ls = uvars /\
   l4_vtr_proj973 env venv uvars g owner idx sv pv fty ==>
   l4_vtr_proj973 env venv uvars' (MAP (l4_vinstL961 ls) g) owner idx
     (l4_vinstL961 ls sv) (l4_vinstL961 ls pv) (l4_vinstL961 ls fty)`,
  REWRITE_TAC [l4_vtr_proj973] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`MAP (l4_vlevel_inst961 ls) us`;
     `MAP (l4_vinstL961 ls) params`;`MAP (l4_vinstL961 ls) indices`] THEN
  ASM_REWRITE_TAC [LENGTH_MAP] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [ALL_MAP] THEN REWRITE_TAC [GSYM ALL_MEM;o_THM] THEN
   ASM_SIMP_TAC [l4_vlevel_inst_wf_any966];
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`uvars':num`;`ls:l4_vlevel961 list`;
                  `g:l4_vexpr961 list`;`sv:l4_vexpr961`;
                  `l4_vapps962 (APPEND params indices) (L4VConst961 owner us)`]
     l4_vhas_type_instL966) THEN
   ASM_SIMP_TAC [l4_vinstL_vapps962;l4_vinstL961;MAP_APPEND];
   ASM_REWRITE_TAC [l4_vproj_expr962;l4_vinstL961;l4_vinstL_vapps962];
   ASM_MESON_TAC [l4_vhas_type_instL966]]);;

let l4_vtr_proj_defeq_ctx973 = prove
 (`!env venv uvars g0 g1 g2 owner idx sv pv fty.
   l4_venv_closed966 venv /\
   l4_vis_defeq_ctx966 venv uvars g0 g1 g2 /\
   l4_vtr_proj973 env venv uvars g1 owner idx sv pv fty ==>
   l4_vtr_proj973 env venv uvars g2 owner idx sv pv fty`,
  REWRITE_TAC [l4_vtr_proj973;l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_defeqDFC966]);;

(* ========================================================================= *)
(* 5. HasPrimitives Specification & Literal Typing                           *)
(* ========================================================================= *)

let l4_has_primitives973 = new_definition
 `l4_has_primitives973 env venv <=>
   (l4_core_nat_ready533 env ==>
      l4_venv_lookup_const961 venv l4_core_nat_name533
        (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))) /\
      l4_venv_lookup_const961 venv l4_core_zero_name533
        (L4VConstant961 0 l4_vnat_ty973) /\
      l4_venv_lookup_const961 venv l4_core_succ_name533
        (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973))) /\
   (l4_core_bool_ready533 env ==>
      l4_venv_lookup_const961 venv l4_core_bool_name533
        (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))) /\
      l4_venv_lookup_const961 venv l4_core_false_name533
        (L4VConstant961 0 l4_vbool_ty973) /\
      l4_venv_lookup_const961 venv l4_core_true_name533
        (L4VConstant961 0 l4_vbool_ty973)) /\
   (l4_core_string_ready533 env ==>
      l4_venv_lookup_const961 venv l4_core_char_name533
        (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))) /\
      l4_venv_lookup_const961 venv l4_core_char_of_nat533
        (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973)) /\
      l4_venv_lookup_const961 venv l4_core_string_name533
        (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))) /\
      l4_venv_lookup_const961 venv l4_core_string_of_list533
        (L4VConstant961 0 (L4VForallE961 l4_vlist_char_ty973 l4_vstring_ty973)) /\
      l4_venv_lookup_const961 venv l4_core_list_name539
        (L4VConstant961 1 (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
                                         (L4VSort961 (L4VLSucc961 (L4VLParam961 0))))) /\
      l4_venv_lookup_const961 venv (L4String l4_core_list_name539 [110;105;108])
        (L4VConstant961 1
          (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
            (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 0)))) /\
      l4_venv_lookup_const961 venv (L4String l4_core_list_name539 [99;111;110;115])
        (L4VConstant961 1
          (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
            (L4VForallE961 (L4VBVar961 0)
              (L4VForallE961
                (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 1))
                (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 2))))))) /\
   (!n d a.
      l4_core_nat_ready533 env /\
      l4_kfind_decl493 env n = SOME d /\
      l4_kdecl_kind493 d = L4KDPrimitive493 L4KPNatPred493 ==>
      l4_vis_defeq961 venv 0 []
        (L4VApp961 (L4VConst961 n []) (l4_nat_lit973 a))
        (l4_nat_lit973 (a - 1)) l4_vnat_ty973) /\
   (!n d op a b res rty.
      l4_core_nat_ready533 env /\
      l4_kfind_decl493 env n = SOME d /\
      l4_kdecl_kind493 d = L4KDPrimitive493 op /\
      l4_vbinary_prim_spec973 op a b = SOME (res, rty) /\
      (rty = l4_vbool_ty973 ==> l4_core_bool_ready533 env) ==>
      l4_vis_defeq961 venv 0 []
        (L4VApp961 (L4VApp961 (L4VConst961 n []) (l4_nat_lit973 a)) (l4_nat_lit973 b))
        res rty)`;;

let l4_has_primitives_empty973 = prove
 (`l4_has_primitives973 [] l4_venv_empty961`,
  REWRITE_TAC [l4_has_primitives973;l4_core_nat_ready533;l4_core_bool_ready533;
               l4_core_string_ready533;l4_kfind_decl493]);;

let l4_venv_ordered_const973 = prove
 (`!v1 v2 c ci.
   l4_venv_ordered961 v1 v2 /\ l4_venv_lookup_const961 v1 c ci ==>
   l4_venv_lookup_const961 v2 c ci`,
  REWRITE_TAC [l4_venv_ordered961] THEN MESON_TAC []);;

let l4_has_primitives_mono_venv973 = prove
 (`!env venv1 venv2.
   l4_venv_ordered961 venv1 venv2 /\
   l4_has_primitives973 env venv1 ==>
   l4_has_primitives973 env venv2`,
  REWRITE_TAC [l4_has_primitives973] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC [l4_venv_ordered_const973;l4_venv_ordered_preserve_vis_defeq961]);;

let l4_vlevel_equiv_refl_all973 = prove
 (`!ls. ALL2 l4_vlevel_equiv961 ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]);;

let l4_vhas_type_const973 = prove
 (`!env uvars g c ci ls.
   l4_venv_lookup_const961 env c ci /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = l4_vc_uvars961 ci ==>
   l4_vhas_type961 env uvars g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci))`,
  REWRITE_TAC [l4_vhas_type961] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_const961 THEN
  ASM_REWRITE_TAC [l4_vlevel_equiv_refl_all973]);;

let l4_nat_lit_has_type973 = prove
 (`!env venv uvars g n.
   l4_has_primitives973 env venv /\
   l4_core_nat_ready533 env ==>
   l4_vhas_type961 venv uvars g (l4_nat_lit973 n) l4_vnat_ty973`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC [l4_nat_lit973] THEN STRIP_TAC THENL
  [SUBGOAL_THEN
     `l4_venv_lookup_const961 venv l4_core_zero_name533 (L4VConstant961 0 l4_vnat_ty973)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
    REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
    MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `l4_core_zero_name533`;`L4VConstant961 0 l4_vnat_ty973`;
                   `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
    ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vnat_ty973;l4_vinstL961;MAP]];
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g (L4VConst961 l4_core_succ_name533 [])
        (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_venv_lookup_const961 venv l4_core_succ_name533
         (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973))`
      ASSUME_TAC THENL
    [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
     REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
     MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `l4_core_succ_name533`;
                    `L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973)`;
                    `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
     ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vnat_ty973;l4_vinstL961;MAP]];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VConst961 l4_core_succ_name533 []`;`l4_nat_lit973 n`;
                  `l4_vnat_ty973`;`l4_vnat_ty973`] l4_vhas_type_app972) THEN
   ASM_SIMP_TAC [l4_vinst0961;l4_vnat_ty973;l4_vinst961]]);;

let l4_vchar_ty_lift973 = prove
 (`(!n k. l4_vliftN961 l4_vchar_ty973 n k = l4_vchar_ty973) /\
   (!v k. l4_vinst961 l4_vchar_ty973 v k = l4_vchar_ty973) /\
   (!v k. l4_vinst961 l4_vlist_char_ty973 v k = l4_vlist_char_ty973) /\
   (!v k. l4_vinst961 l4_vstring_ty973 v k = l4_vstring_ty973) /\
   (!ls. l4_vinstL961 ls l4_vnat_ty973 = l4_vnat_ty973) /\
   (!ls. l4_vinstL961 ls l4_vchar_ty973 = l4_vchar_ty973) /\
   (!ls. l4_vinstL961 ls l4_vlist_char_ty973 = l4_vlist_char_ty973) /\
   (!ls. l4_vinstL961 ls l4_vstring_ty973 = l4_vstring_ty973)`,
  REWRITE_TAC [l4_vnat_ty973;l4_vchar_ty973;l4_vlist_char_ty973;l4_vstring_ty973;
               l4_vliftN961;l4_vinst961;l4_vinstL961;MAP;l4_vlevel_inst961]);;

let l4_tr_char_list_has_type973 = prove
 (`!env venv uvars g cs.
   l4_has_primitives973 env venv /\
   l4_core_string_ready533 env /\
   l4_core_nat_ready533 env ==>
   l4_vhas_type961 venv uvars g (l4_tr_char_list973 cs) l4_vlist_char_ty973`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_tr_char_list973;l4_vapps962] THEN STRIP_TAC THENL
  [SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g l4_vchar_ty973 (L4VSort961 (L4VLSucc961 L4VLZero961))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_venv_lookup_const961 venv l4_core_char_name533
         (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961)))` ASSUME_TAC THENL
    [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
     REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
     REWRITE_TAC [l4_vchar_ty973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `l4_core_char_name533`;
                    `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))`;
                    `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
     ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vinstL961;l4_vlevel_inst961]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g
        (L4VConst961 (L4String l4_core_list_name539 [110;105;108]) [L4VLZero961])
        (L4VForallE961 (L4VSort961 (L4VLSucc961 L4VLZero961))
          (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 0)))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_venv_lookup_const961 venv (L4String l4_core_list_name539 [110;105;108])
         (L4VConstant961 1
           (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
             (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 0))))`
      ASSUME_TAC THENL
    [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
     REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
     MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `L4String l4_core_list_name539 [110;105;108]`;
                    `L4VConstant961 1
                      (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
                        (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 0)))`;
                    `[L4VLZero961]`] l4_vhas_type_const973) THEN
     ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;ARITH_RULE `SUC 0 = 1`;
                   l4_vlevel_wf961;l4_vinstL961;l4_vlevel_inst961;l4_vnth_level961;MAP]];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VConst961 (L4String l4_core_list_name539 [110;105;108]) [L4VLZero961]`;
                  `l4_vchar_ty973`;
                  `L4VSort961 (L4VLSucc961 L4VLZero961)`;
                  `L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 0)`]
     l4_vhas_type_app972) THEN
   ASM_SIMP_TAC [l4_vinst0961;l4_vinst961;l4_vinst_var961;
                 ARITH_RULE `~(0 < 0)`;l4_vliftN_zero961;
                 GSYM l4_vlist_char_ty973];
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g l4_vchar_ty973 (L4VSort961 (L4VLSucc961 L4VLZero961))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_venv_lookup_const961 venv l4_core_char_name533
         (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961)))` ASSUME_TAC THENL
    [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
     REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
     REWRITE_TAC [l4_vchar_ty973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `l4_core_char_name533`;
                    `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))`;
                    `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
     ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vinstL961;l4_vlevel_inst961]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g
        (L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h))
        l4_vchar_ty973` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_vhas_type961 venv uvars g (L4VConst961 l4_core_char_of_nat533 [])
         (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973)` ASSUME_TAC THENL
    [SUBGOAL_THEN
       `l4_venv_lookup_const961 venv l4_core_char_of_nat533
          (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973))` ASSUME_TAC THENL
     [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
      REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
      MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                     `l4_core_char_of_nat533`;
                     `L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973)`;
                     `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
      ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vinstL961;
                    l4_vchar_ty_lift973]];
     ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`uvars:num`;
                   `g:l4_vexpr961 list`;`h:num`] l4_nat_lit_has_type973) THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `L4VConst961 l4_core_char_of_nat533 []`;`l4_nat_lit973 h`;
                   `l4_vnat_ty973`;`l4_vchar_ty973`] l4_vhas_type_app972) THEN
    ASM_SIMP_TAC [l4_vinst0961;l4_vchar_ty_lift973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g
        (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
        (L4VForallE961 (L4VSort961 (L4VLSucc961 L4VLZero961))
          (L4VForallE961 (L4VBVar961 0)
            (L4VForallE961
              (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 1))
              (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 2)))))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_venv_lookup_const961 venv (L4String l4_core_list_name539 [99;111;110;115])
         (L4VConstant961 1
           (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
             (L4VForallE961 (L4VBVar961 0)
               (L4VForallE961
                 (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 1))
                 (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 2))))))`
      ASSUME_TAC THENL
    [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
     REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
     MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                    `L4String l4_core_list_name539 [99;111;110;115]`;
                    `L4VConstant961 1
                      (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
                        (L4VForallE961 (L4VBVar961 0)
                          (L4VForallE961
                            (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 1))
                            (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 2)))))`;
                    `[L4VLZero961]`] l4_vhas_type_const973) THEN
     ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;ARITH_RULE `SUC 0 = 1`;
                   l4_vlevel_wf961;l4_vinstL961;l4_vlevel_inst961;l4_vnth_level961;MAP]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g
        (L4VApp961 (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
                   l4_vchar_ty973)
        (L4VForallE961 l4_vchar_ty973
          (L4VForallE961 l4_vlist_char_ty973 l4_vlist_char_ty973))` ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961]`;
                   `l4_vchar_ty973`;
                   `L4VSort961 (L4VLSucc961 L4VLZero961)`;
                   `L4VForallE961 (L4VBVar961 0)
                      (L4VForallE961
                        (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 1))
                        (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLZero961]) (L4VBVar961 2)))`]
      l4_vhas_type_app972) THEN
    ASM_SIMP_TAC [l4_vinst0961;l4_vinst961;l4_vinst_var961;
                  ARITH_RULE `~(0 < 0) /\ ~(1 < 1) /\ ~(2 < 2) /\ SUC 0 = 1 /\ SUC 1 = 2`;
                  l4_vchar_ty_lift973;GSYM l4_vlist_char_ty973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv uvars g
        (L4VApp961
          (L4VApp961 (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
                     l4_vchar_ty973)
          (L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h)))
        (L4VForallE961 l4_vlist_char_ty973 l4_vlist_char_ty973)` ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `L4VApp961 (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961]) l4_vchar_ty973`;
                   `L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h)`;
                   `l4_vchar_ty973`;
                   `L4VForallE961 l4_vlist_char_ty973 l4_vlist_char_ty973`]
      l4_vhas_type_app972) THEN
    ASM_SIMP_TAC [l4_vinst0961;l4_vinst961;l4_vchar_ty_lift973];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `L4VApp961
                     (L4VApp961 (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
                                l4_vchar_ty973)
                     (L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h))`;
                  `l4_tr_char_list973 t`;
                  `l4_vlist_char_ty973`;`l4_vlist_char_ty973`]
     l4_vhas_type_app972) THEN
   ASM_SIMP_TAC [l4_vinst0961;l4_vchar_ty_lift973]]);;

let l4_core_string_ready_nat973 = prove
 (`!env. l4_core_string_ready533 env ==> l4_core_nat_ready533 env`,
  GEN_TAC THEN REWRITE_TAC [l4_core_string_ready533] THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env l4_core_char_of_nat533` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `c:l4_kdeclaration493` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env l4_core_string_of_list533` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s:l4_kdeclaration493` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  MP_TAC (SPEC `l4_kdecl_kind493 c` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  MP_TAC (SPEC `l4_kdecl_kind493 s` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  (fun (asl,w) ->
    MAP_EVERY (fun v ->
      if type_of v = `:l4_kprimitive493`
      then STRUCT_CASES_TAC (SPEC v (cases "l4_kprimitive493")) THEN REWRITE_TAC []
      else ALL_TAC) (frees w) (asl,w)) THEN
  SIMP_TAC []);;

let l4_tr_str_lit_has_type973 = prove
 (`!env venv uvars g bytes e.
   l4_has_primitives973 env venv /\
   l4_core_string_ready533 env /\
   l4_tr_str_lit973 bytes = SOME e ==>
   l4_vhas_type961 venv uvars g e l4_vstring_ty973`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv uvars g (L4VConst961 l4_core_string_of_list533 [])
       (L4VForallE961 l4_vlist_char_ty973 l4_vstring_ty973)` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `l4_venv_lookup_const961 venv l4_core_string_of_list533
        (L4VConstant961 0 (L4VForallE961 l4_vlist_char_ty973 l4_vstring_ty973))`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
    REWRITE_TAC [l4_has_primitives973] THEN ASM_SIMP_TAC [];
    MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `l4_core_string_of_list533`;
                   `L4VConstant961 0 (L4VForallE961 l4_vlist_char_ty973 l4_vstring_ty973)`;
                   `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
    ASM_SIMP_TAC [l4_vc_uvars961;l4_vc_type961;ALL;LENGTH;l4_vinstL961;
                  l4_vchar_ty_lift973]];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`uvars:num`;
                 `g:l4_vexpr961 list`;`a:num list`] l4_tr_char_list_has_type973) THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                 `L4VConst961 l4_core_string_of_list533 []`;`l4_tr_char_list973 a`;
                 `l4_vlist_char_ty973`;`l4_vstring_ty973`] l4_vhas_type_app972) THEN
  ASM_SIMP_TAC [l4_core_string_ready_nat973;l4_vinst0961;l4_vchar_ty_lift973]);;

(* ========================================================================= *)
(* 6. Full 12-Constructor Translation (l4_vtr_expr_s973, l4_vtr_expr973)     *)
(* ========================================================================= *)

let l4_vtr_expr_s_RULES973,l4_vtr_expr_s_INDUCT973,l4_vtr_expr_s_CASES973 =
  new_inductive_definition
 `(!env venv ps l i e ty.
     l4_vl_bvar973 l i = SOME (e, ty) /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e ty ==>
     l4_vtr_expr_s973 env venv ps l (L4KBVar447 i) e) /\
  (!env venv ps l n e ty.
     l4_vl_fvar973 l n = SOME (e, ty) /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e ty ==>
     l4_vtr_expr_s973 env venv ps l (L4KFVar447 n) e) /\
  (!env venv ps l u u'.
     l4_tr_l967 ps u = SOME u' /\
     l4_vlevel_wf961 (LENGTH ps) u' ==>
     l4_vtr_expr_s973 env venv ps l (L4KSort447 u) (L4VSort961 u')) /\
  (!env venv ps l c us us' ci.
     l4_tr_ls967 ps us = SOME us' /\
     ALL (l4_vlevel_wf961 (LENGTH ps)) us' /\
     l4_venv_lookup_const961 venv c ci /\
     LENGTH us' = l4_vc_uvars961 ci ==>
     l4_vtr_expr_s973 env venv ps l (L4KConst447 c us) (L4VConst961 c us')) /\
  (!env venv ps l f a f' a' ty.
     l4_vtr_expr_s973 env venv ps l f f' /\
     l4_vtr_expr_s973 env venv ps l a a' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VApp961 f' a') ty ==>
     l4_vtr_expr_s973 env venv ps l (L4KApp447 f a) (L4VApp961 f' a')) /\
  (!env venv ps l n bi dom body dom' body' ty.
     l4_vtr_expr_s973 env venv ps l dom dom' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' /\
     l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom') body body' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VLam961 dom' body') ty ==>
     l4_vtr_expr_s973 env venv ps l (L4KLam447 n bi dom body) (L4VLam961 dom' body')) /\
  (!env venv ps l n bi dom body dom' body' ty.
     l4_vtr_expr_s973 env venv ps l dom dom' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' /\
     l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom') body body' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VForallE961 dom' body') ty ==>
     l4_vtr_expr_s973 env venv ps l (L4KPi447 n bi dom body) (L4VForallE961 dom' body')) /\
  (!env venv ps l n ty val_e body nd ty' val' body'.
     l4_vtr_expr_s973 env venv ps l ty ty' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' /\
     l4_vtr_expr_s973 env venv ps l val_e val' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) val' ty' /\
     l4_vtr_expr_s973 env venv ps (l4_vl_push_let973 l ty' val') body body' ==>
     l4_vtr_expr_s973 env venv ps l (L4KLet447 n ty val_e body nd) body') /\
  (!env venv ps l owner idx e sv pv fty.
     l4_vtr_expr_s973 env venv ps l e sv /\
     l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner idx sv pv fty ==>
     l4_vtr_expr_s973 env venv ps l (L4KProj447 owner idx e) pv) /\
  (!env venv ps l m.
     l4_core_nat_ready533 env /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_nat_lit973 m) l4_vnat_ty973 ==>
     l4_vtr_expr_s973 env venv ps l (L4KNatLit447 m) (l4_nat_lit973 m)) /\
  (!env venv ps l bytes e'.
     l4_core_string_ready533 env /\
     l4_tr_str_lit973 bytes = SOME e' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' l4_vstring_ty973 ==>
     l4_vtr_expr_s973 env venv ps l (L4KStrLit447 bytes) e') /\
  (!env venv ps l e e'.
     l4_vtr_expr_s973 env venv ps l e e' ==>
     l4_vtr_expr_s973 env venv ps l (L4KMData447 e) e')`;;

let [l4_vtr_expr_s_bvar973;
     l4_vtr_expr_s_fvar973;
     l4_vtr_expr_s_sort973;
     l4_vtr_expr_s_const973;
     l4_vtr_expr_s_app973;
     l4_vtr_expr_s_lam973;
     l4_vtr_expr_s_pi973;
     l4_vtr_expr_s_let973;
     l4_vtr_expr_s_proj973;
     l4_vtr_expr_s_natlit973;
     l4_vtr_expr_s_strlit973;
     l4_vtr_expr_s_mdata973] = CONJUNCTS l4_vtr_expr_s_RULES973;;

let l4_vtr_expr973 = new_definition
 `l4_vtr_expr973 env venv ps l e e' <=>
   ?e0. l4_vtr_expr_s973 env venv ps l e e0 /\
        l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) e0 e'`;;

let l4_vtr_typing973 = new_definition
 `l4_vtr_typing973 env venv ps l e ty e' ty' <=>
   l4_vtr_expr973 env venv ps l e e' /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`;;

let l4_vtr_expr_s_has_type973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   ?ty. l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [];
   MESON_TAC [];
   REPEAT STRIP_TAC THEN EXISTS_TAC `L4VSort961 (L4VLSucc961 u')` THEN
   REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
   REPEAT STRIP_TAC THEN EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN
   MATCH_MP_TAC l4_vhas_type_const973 THEN ASM_REWRITE_TAC [];
   MESON_TAC [];
   MESON_TAC [];
   MESON_TAC [];
   REWRITE_TAC [l4_vl_ctx_push_let973] THEN MESON_TAC [];
   MESON_TAC [l4_vtr_proj_has_type973];
   MESON_TAC [];
   MESON_TAC [];
   MESON_TAC []]);;

let l4_vtr_expr_s_to_vtr_expr973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   l4_vtr_expr973 env venv ps l e e'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vtr_expr973] THEN
  EXISTS_TAC `e':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_vtr_expr_s_has_type973;l4_vis_defeq_u_refl973]);;

let l4_vtr_expr_has_type973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr973 env venv ps l e e' ==>
   ?ty. l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty`,
  REWRITE_TAC [l4_vtr_expr973] THEN MESON_TAC [l4_vis_defeq_u_has_type_r973]);;

let l4_vtr_expr_defeq_r973 = prove
 (`!env venv ps l e e1 e2.
   l4_venv_wf966 venv /\
   l4_defeq_injectivity972 venv /\
   l4_vctx_wf966 venv (LENGTH ps) (l4_vl_ctx973 l) /\
   l4_vtr_expr973 env venv ps l e e1 /\
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) e1 e2 ==>
   l4_vtr_expr973 env venv ps l e e2`,
  REWRITE_TAC [l4_vtr_expr973] THEN
  MESON_TAC [l4_vis_defeq_u_trans972]);;

let l4_vtr_expr_s_monotonic_env973 = prove
 (`!env venv1 ps l e e'.
   l4_vtr_expr_s973 env venv1 ps l e e' ==>
   (!venv2. l4_venv_ordered961 venv1 venv2 ==>
     l4_vtr_expr_s973 env venv2 ps l e e')`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vtr_expr_s_bvar973;l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_fvar973;l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_sort973];
   MESON_TAC [l4_vtr_expr_s_const973;l4_venv_ordered_const973];
   MESON_TAC [l4_vtr_expr_s_app973;l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_lam973;l4_venv_ordered_preserve_vis_type966;
              l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_pi973;l4_venv_ordered_preserve_vis_type966;
              l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_let973;l4_venv_ordered_preserve_vis_type966;
              l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_proj973;l4_vtr_proj_monotonic_env973];
   MESON_TAC [l4_vtr_expr_s_natlit973;l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_strlit973;l4_venv_ordered_preserve_vhas_type961];
   MESON_TAC [l4_vtr_expr_s_mdata973]]);;

let l4_vtr_expr_monotonic_env973 = prove
 (`!env venv1 venv2 ps l e e'.
   l4_venv_ordered961 venv1 venv2 /\
   l4_vtr_expr973 env venv1 ps l e e' ==>
   l4_vtr_expr973 env venv2 ps l e e'`,
  REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vtr_expr_s_monotonic_env973;l4_venv_ordered_preserve_vis_defeq961]);;

let l4_vtr_free_ctx_RULES973,l4_vtr_free_ctx_INDUCT973,l4_vtr_free_ctx_CASES973 =
  new_inductive_definition
 `(!env venv ps. l4_vtr_free_ctx973 env venv ps [] []) /\
  (!env venv ps fs fs' n ty ty'.
     l4_vtr_free_ctx973 env venv ps fs fs' /\
     ~(MEM n (MAP FST fs')) /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' []) ty ty' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_free_ctx973 fs') ty' ==>
     l4_vtr_free_ctx973 env venv ps
       (CONS (n, L4KBinding491 ty NONE) fs)
       (CONS (n, L4VLLam973 ty') fs')) /\
  (!env venv ps fs fs' n ty val_e ty' val'.
     l4_vtr_free_ctx973 env venv ps fs fs' /\
     ~(MEM n (MAP FST fs')) /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' []) ty ty' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_free_ctx973 fs') ty' /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' []) val_e val' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_free_ctx973 fs') val' ty' ==>
     l4_vtr_free_ctx973 env venv ps
       (CONS (n, L4KBinding491 ty (SOME val_e)) fs)
       (CONS (n, L4VLLet973 ty' val') fs'))`;;

let [l4_vtr_free_nil973; l4_vtr_free_lam973; l4_vtr_free_let973] =
  CONJUNCTS l4_vtr_free_ctx_RULES973;;

let l4_vtr_bound_ctx_RULES973,l4_vtr_bound_ctx_INDUCT973,l4_vtr_bound_ctx_CASES973 =
  new_inductive_definition
 `(!env venv ps fs'. l4_vtr_bound_ctx973 env venv ps fs' [] []) /\
  (!env venv ps fs' bs bs' ty ty'.
     l4_vtr_bound_ctx973 env venv ps fs' bs bs' /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' bs') ty ty' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 (L4VLCtx973 fs' bs')) ty' ==>
     l4_vtr_bound_ctx973 env venv ps fs'
       (CONS (L4KBinding491 ty NONE) bs)
       (CONS (L4VLLam973 ty') bs')) /\
  (!env venv ps fs' bs bs' ty val_e ty' val'.
     l4_vtr_bound_ctx973 env venv ps fs' bs bs' /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' bs') ty ty' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 (L4VLCtx973 fs' bs')) ty' /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 fs' bs') val_e val' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 (L4VLCtx973 fs' bs')) val' ty' ==>
     l4_vtr_bound_ctx973 env venv ps fs'
       (CONS (L4KBinding491 ty (SOME val_e)) bs)
       (CONS (L4VLLet973 ty' val') bs'))`;;

let [l4_vtr_bound_nil973; l4_vtr_bound_lam973; l4_vtr_bound_let973] =
  CONJUNCTS l4_vtr_bound_ctx_RULES973;;

let l4_vtr_ctx973 = new_definition
 `l4_vtr_ctx973 env venv ps g l <=>
   l4_vtr_free_ctx973 env venv ps (l4_kcontext_free532 g) (l4_vl_free973 l) /\
   l4_vtr_bound_ctx973 env venv ps (l4_vl_free973 l)
     (l4_kcontext_bound532 g) (l4_vl_bound973 l)`;;

let l4_vtr_free_ctx_to_wf973 = prove
 (`!env venv ps fs fs'.
   l4_vtr_free_ctx973 env venv ps fs fs' ==>
   l4_vl_entries_wf973 venv (LENGTH ps) [] (MAP SND fs')`,
  MATCH_MP_TAC l4_vtr_free_ctx_INDUCT973 THEN
  REWRITE_TAC [MAP;SND;l4_vl_free_ctx973;APPEND_NIL] THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_nil973 THEN
   REWRITE_TAC [l4_vctx_wf966];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_lam973 THEN
   ASM_REWRITE_TAC [APPEND_NIL];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vl_entries_wf_let973 THEN
   ASM_REWRITE_TAC [APPEND_NIL]]);;

let l4_vtr_bound_ctx_to_wf973 = prove
 (`!env venv ps fs' bs bs'.
   l4_vtr_bound_ctx973 env venv ps fs' bs bs' ==>
   (l4_vctx_wf966 venv (LENGTH ps) (l4_vl_free_ctx973 fs') ==>
    l4_vl_entries_wf973 venv (LENGTH ps) (l4_vl_free_ctx973 fs') bs')`,
  MATCH_MP_TAC l4_vtr_bound_ctx_INDUCT973 THEN
  REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vl_entries_wf_nil973];
   MESON_TAC [l4_vl_entries_wf_lam973];
   MESON_TAC [l4_vl_entries_wf_let973]]);;

let l4_vtr_ctx_to_vl_wf973 = prove
 (`!env venv ps g l.
   l4_vtr_ctx973 env venv ps g l ==> l4_vl_ctx_wf973 venv (LENGTH ps) l`,
  REWRITE_TAC [l4_vtr_ctx973;l4_vl_ctx_wf973] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC [l4_vtr_free_ctx_to_wf973];
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_free_ctx973 (l4_vl_free973 l))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `l4_vl_entries_wf973 venv (LENGTH (ps:l4_name list)) [] (MAP SND (l4_vl_free973 l))`
      (MP_TAC o MATCH_MP l4_vl_entries_wf_to_vctx_wf973) THENL
    [ASM_MESON_TAC [l4_vtr_free_ctx_to_wf973];
     REWRITE_TAC [APPEND_NIL;GSYM l4_vl_free_ctx973] THEN SIMP_TAC []];
    ASM_MESON_TAC [l4_vtr_bound_ctx_to_wf973]]]);;

let l4_vtr_ctx_to_vctx_wf973 = prove
 (`!env venv ps g l.
   l4_vtr_ctx973 env venv ps g l ==>
   l4_vctx_wf966 venv (LENGTH ps) (l4_vl_ctx973 l)`,
  MESON_TAC [l4_vtr_ctx_to_vl_wf973;l4_vl_ctx_wf_to_vctx_wf973]);;

let l4_vtr_ctx_empty973 = prove
 (`!env venv ps. l4_vtr_ctx973 env venv ps l4_kempty_context532 l4_vl_empty973`,
  REWRITE_TAC [l4_vtr_ctx973;l4_kempty_context532;l4_vl_empty973;
               l4_kcontext_free532;l4_kcontext_bound532;
               l4_vl_free973;l4_vl_bound973;
               l4_vtr_free_nil973;l4_vtr_bound_nil973]);;

let l4_vtr_ctx_push_lam973 = prove
 (`!env venv ps g l ty ty'.
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' ==>
   l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g ty NONE) (l4_vl_push_lam973 l ty')`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `g:l4_kcontext532` (cases "l4_kcontext532")) THEN
  STRUCT_CASES_TAC (SPEC `l:l4_vl_ctx_rec973` (cases "l4_vl_ctx_rec973")) THEN
  REWRITE_TAC [l4_vtr_ctx973;l4_kpush_binding532;l4_vl_push_lam973;
               l4_kcontext_free532;l4_kcontext_bound532;
               l4_vl_free973;l4_vl_bound973] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vtr_bound_lam973 THEN ASM_REWRITE_TAC []);;

let l4_vtr_ctx_push_let973 = prove
 (`!env venv ps g l ty val_e ty' val'.
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' /\
   l4_vtr_expr973 env venv ps l val_e val' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) val' ty' ==>
   l4_vtr_ctx973 env venv ps
     (l4_kpush_binding532 g ty (SOME val_e)) (l4_vl_push_let973 l ty' val')`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `g:l4_kcontext532` (cases "l4_kcontext532")) THEN
  STRUCT_CASES_TAC (SPEC `l:l4_vl_ctx_rec973` (cases "l4_vl_ctx_rec973")) THEN
  REWRITE_TAC [l4_vtr_ctx973;l4_kpush_binding532;l4_vl_push_let973;
               l4_kcontext_free532;l4_kcontext_bound532;
               l4_vl_free973;l4_vl_bound973] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vtr_bound_let973 THEN ASM_REWRITE_TAC []);;

let l4_vtr_ctx_push_free_lam973 = prove
 (`!env venv ps g l n ty ty'.
   l4_kcontext_bound532 g = [] /\
   l4_vl_bound973 l = [] /\
   ~(MEM n (MAP FST (l4_vl_free973 l))) /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' ==>
   l4_vtr_ctx973 env venv ps
     (L4KContext532 [] (CONS (n, L4KBinding491 ty NONE) (l4_kcontext_free532 g)))
     (l4_vl_push_free_lam973 l n ty')`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `l:l4_vl_ctx_rec973` (cases "l4_vl_ctx_rec973")) THEN
  REWRITE_TAC [l4_vtr_ctx973;l4_vl_push_free_lam973;
               l4_kcontext_free532;l4_kcontext_bound532;
               l4_vl_free973;l4_vl_bound973;l4_vl_ctx973] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC [l4_vlentries_to_ctx973;APPEND;l4_vtr_bound_nil973] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC l4_vtr_free_lam973 THEN
  ASM_REWRITE_TAC []);;

(* ========================================================================= *)
(* 7. Full Environment Soundness Invariant (l4_venv_sound973)                *)
(* ========================================================================= *)

let l4_vind_head_inj973 = new_definition
 `l4_vind_head_inj973 env venv <=>
   !uvars g ind1 ind2 info1 info2 us1 us2 args1 args2.
     l4_vctx_wf966 venv uvars g /\
     l4_core_inductive532 env ind1 = SOME info1 /\
     l4_core_inductive532 env ind2 = SOME info2 /\
     l4_vis_defeq_u961 venv uvars g
       (l4_vapps962 args1 (L4VConst961 ind1 us1))
       (l4_vapps962 args2 (L4VConst961 ind2 us2)) ==>
     ind1 = ind2 /\
     ALL2 l4_vlevel_equiv961 us1 us2 /\
     ALL2 (l4_vis_defeq_u961 venv uvars g) args1 args2`;;

let l4_seq973 = new_recursive_definition num_RECURSION
 `(l4_seq973 start 0 = []) /\
  (l4_seq973 start (SUC n) = CONS start (l4_seq973 (SUC start) n))`;;

let l4_venv_sound973 = new_definition
 `l4_venv_sound973 env venv <=>
   l4_venv_wf966 venv /\
   l4_defeq_injectivity972 venv /\
   l4_vind_head_inj973 env venv /\
   l4_has_primitives973 env venv /\
   (!n d.
     l4_kfind_decl493 env n = SOME d ==>
     (match l4_kdecl_kind493 d with
      | L4KDUnsupported493 -> T
      | L4KDUnsafe493 r -> T
      | L4KDPartial493 -> T
      | _ ->
        ?ci. l4_venv_lookup_const961 venv n ci /\
             l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d) /\
             l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973
               (l4_kdecl_type493 d) (l4_vc_type961 ci) /\
             l4_vis_type961 venv (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) /\
             l4_vclosedN961 (l4_vc_type961 ci) 0)) /\
   (!n d val_e.
     l4_kfind_decl493 env n = SOME d /\
     (l4_kdecl_kind493 d = L4KDDefinition493 \/
      l4_kdecl_kind493 d = L4KDTheorem493 \/
      (?p. l4_kdecl_kind493 d = L4KDPrimitive493 p)) /\
     l4_kdecl_value493 d = SOME val_e ==>
     ?ci val'.
       l4_venv_lookup_const961 venv n ci /\
       l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d) /\
       l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973 val_e val' /\
       l4_vclosedN961 val' 0 /\
       l4_vis_defeq961 venv (l4_vc_uvars961 ci) []
         (L4VConst961 n (l4_vlevel_params966 (l4_vc_uvars961 ci)))
         val' (l4_vc_type961 ci)) /\
   (!uvars g n d cn cd us cus args rep idx fn a1 a2.
     l4_vctx_wf966 venv uvars g /\
     l4_kfind_decl493 env n = SOME d /\
     ((l4_kdecl_kind493 d = L4KDQuotient493 L4KQLift493 /\ idx = 5) \/
      (l4_kdecl_kind493 d = L4KDQuotient493 L4KQInd493 /\ idx = 4)) /\
     l4_kfind_decl493 env cn = SOME cd /\
     l4_kdecl_kind493 cd = L4KDQuotient493 L4KQCtor493 /\
     (?maj. l4_nth_error550 args idx = SOME maj /\
            l4_vis_defeq_u961 venv uvars g maj
              (l4_vapps962 [a1;a2;rep] (L4VConst961 cn cus))) /\
     l4_nth_error550 args 3 = SOME fn /\
     (?ty. l4_vhas_type961 venv uvars g (l4_vapps962 args (L4VConst961 n us)) ty) ==>
     l4_vis_defeq_u961 venv uvars g
       (l4_vapps962 args (L4VConst961 n us))
       (l4_vapps962 (l4_skip550 args (SUC idx)) (L4VApp961 fn rep))) /\
   (!uvars g rname d info rus args maj own cn ci cus fs rule rhs_v.
     l4_vctx_wf966 venv uvars g /\
     l4_kfind_decl493 env rname = SOME d /\
     l4_kdecl_kind493 d = L4KDRecursor493 info /\
     l4_nth_error550 args
       (l4_krec_num_params493 info + l4_krec_num_motives493 info +
        l4_krec_num_minors493 info + l4_krec_num_indices493 info) = SOME maj /\
     l4_core_major_induct557
       (l4_krec_num_params493 info + l4_krec_num_motives493 info +
        l4_krec_num_minors493 info + l4_krec_num_indices493 info)
       (l4_kdecl_type493 d) = SOME own /\
     l4_vis_defeq_u961 venv uvars g maj (l4_vapps962 fs (L4VConst961 cn cus)) /\
     l4_core_find_rule557 cn (l4_krec_rules493 info) = SOME rule /\
     l4_core_constructor532 env cn = SOME ci /\
     l4_kctor_induct493 ci = own /\
     LENGTH fs = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci /\
     l4_krule_nfields493 rule = l4_kctor_num_fields493 ci /\
     LENGTH rus = LENGTH (l4_kdecl_params493 d) /\
     ALL (l4_vlevel_wf961 uvars) rus /\
     l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973
       (l4_krule_rhs493 rule) rhs_v /\
     (?ty. l4_vhas_type961 venv uvars g (l4_vapps962 args (L4VConst961 rname rus)) ty) ==>
     l4_vis_defeq_u961 venv uvars g
       (l4_vapps962 args (L4VConst961 rname rus))
       (l4_vapps962
         (APPEND (l4_kfirstn494 args
                   (l4_krec_num_params493 info + l4_krec_num_motives493 info +
                    l4_krec_num_minors493 info))
           (APPEND (l4_skip550 fs (l4_kctor_num_params493 ci))
             (l4_skip550 args
               (SUC (l4_krec_num_params493 info + l4_krec_num_motives493 info +
                     l4_krec_num_minors493 info + l4_krec_num_indices493 info)))))
         (l4_vinstL961 rus rhs_v))) /\
   (!rname d info rule.
     l4_kfind_decl493 env rname = SOME d /\
     l4_kdecl_kind493 d = L4KDRecursor493 info /\
     MEM rule (l4_krec_rules493 info) ==>
     ?rhs_v. l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973
               (l4_krule_rhs493 rule) rhs_v) /\
   (!rname d info own oinfo ctor ci.
     l4_kfind_decl493 env rname = SOME d /\
     l4_kdecl_kind493 d = L4KDRecursor493 info /\
     l4_krec_k493 info /\
     l4_core_major_induct557
       (l4_krec_num_params493 info + l4_krec_num_motives493 info +
        l4_krec_num_minors493 info + l4_krec_num_indices493 info)
       (l4_kdecl_type493 d) = SOME own /\
     l4_core_inductive532 env own = SOME oinfo /\
     l4_kind_ctors493 oinfo = [ctor] /\
     l4_core_constructor532 env ctor = SOME ci ==>
     l4_kctor_num_fields493 ci = 0) /\
   (!own info ctor c d idx.
     l4_core_inductive532 env own = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     idx < l4_kctor_num_fields493 c ==>
     ?pci. l4_venv_lookup_const961 venv (l4_proj_const_name962 own idx) pci /\
           l4_vc_uvars961 pci = LENGTH (l4_kdecl_params493 d)) /\
   (!uvars g own info ctor c d idx us cus params idxs fields fval sv.
     l4_vctx_wf966 venv uvars g /\
     l4_core_inductive532 env own = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     idx < l4_kctor_num_fields493 c /\
     LENGTH params = l4_kind_num_params493 info /\
     LENGTH idxs = l4_kind_num_indices493 info /\
     LENGTH fields = l4_kctor_num_params493 c + l4_kctor_num_fields493 c /\
     l4_kctor_num_params493 c = l4_kind_num_params493 info /\
     l4_nth_error550 fields (l4_kctor_num_params493 c + idx) = SOME fval /\
     l4_vhas_type961 venv uvars g sv
       (l4_vapps962 (APPEND params idxs) (L4VConst961 own us)) /\
     l4_vis_defeq_u961 venv uvars g sv
       (l4_vapps962 fields (L4VConst961 ctor cus)) /\
     (?fty. l4_vhas_type961 venv uvars g (l4_vproj_expr962 own idx us params sv) fty) ==>
     l4_vis_defeq_u961 venv uvars g
       (l4_vproj_expr962 own idx us params sv) fval) /\
   (!uvars g own info ctor c d ci_c idx us params idxs sv usort typ fty mp.
     l4_vctx_wf966 venv uvars g /\
     l4_core_inductive532 env own = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     l4_venv_lookup_const961 venv ctor ci_c /\
     idx < l4_kctor_num_fields493 c /\
     LENGTH params = l4_kind_num_params493 info /\
     LENGTH idxs = l4_kind_num_indices493 info /\
     ALL (l4_vlevel_wf961 uvars) us /\
     LENGTH us = LENGTH (l4_kdecl_params493 d) /\
     l4_vhas_type961 venv uvars g sv
       (l4_vapps962 (APPEND params idxs) (L4VConst961 own us)) /\
     l4_vhas_type961 venv uvars g
       (l4_vapps962 (APPEND params idxs) (L4VConst961 own us)) (L4VSort961 usort) /\
     (~mp ==> ~l4_vlevel_equiv961 usort L4VLZero961) /\
     l4_vhas_type961 venv uvars g
       (l4_vapps962 params (L4VConst961 ctor us)) typ /\
     l4_vproj_telescope973 env venv uvars g own us params sv mp idx 0 typ fty ==>
     l4_vhas_type961 venv uvars g
       (l4_vproj_expr962 own idx us params sv) fty) /\
   (!uvars g own info ctor c d us params sv.
     l4_vctx_wf966 venv uvars g /\
     l4_core_structure532 env own /\
     l4_core_inductive532 env own = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     LENGTH params = l4_kind_num_params493 info /\
     l4_kctor_num_params493 c = l4_kind_num_params493 info /\
     ALL (l4_vlevel_wf961 uvars) us /\
     LENGTH us = LENGTH (l4_kdecl_params493 d) /\
     l4_vhas_type961 venv uvars g sv
       (l4_vapps962 params (L4VConst961 own us)) ==>
     (!i. i < l4_kctor_num_fields493 c ==>
        ?fty. l4_vtr_proj973 env venv uvars g own i sv
                (l4_vproj_expr962 own i us params sv) fty) /\
     l4_vis_defeq961 venv uvars g sv
       (l4_vapps962
          (APPEND params
            (MAP (\i. l4_vproj_expr962 own i us params sv)
              (l4_seq973 0 (l4_kctor_num_fields493 c))))
          (L4VConst961 ctor us))
       (l4_vapps962 params (L4VConst961 own us))) /\
   (!uvars g cn ci cus args t.
     l4_vctx_wf966 venv uvars g /\
     l4_core_constructor532 env cn = SOME ci /\
     LENGTH args = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci /\
     l4_vhas_type961 venv uvars g (l4_vapps962 args (L4VConst961 cn cus)) t ==>
     ?oinfo idxs.
       l4_core_inductive532 env (l4_kctor_induct493 ci) = SOME oinfo /\
       l4_kctor_num_params493 ci = l4_kind_num_params493 oinfo /\
       LENGTH idxs = l4_kind_num_indices493 oinfo /\
       l4_vis_defeq_u961 venv uvars g t
         (l4_vapps962 (APPEND (l4_kfirstn494 args (l4_kctor_num_params493 ci)) idxs)
           (L4VConst961 (l4_kctor_induct493 ci) cus))) /\
   (!own info d_ind ctor c d_ctor.
     l4_kfind_decl493 env own = SOME d_ind /\
     l4_kdecl_kind493 d_ind = L4KDInductive493 info /\
     l4_kfind_decl493 env ctor = SOME d_ctor /\
     l4_kdecl_kind493 d_ctor = L4KDConstructor493 c ==>
     (MEM ctor (l4_kind_ctors493 info) <=> l4_kctor_induct493 c = own) /\
     (MEM ctor (l4_kind_ctors493 info) ==>
       l4_kctor_num_params493 c = l4_kind_num_params493 info /\
       LENGTH (l4_kdecl_params493 d_ctor) = LENGTH (l4_kdecl_params493 d_ind))) /\
   (!uvars g own info us args usort.
     l4_vctx_wf966 venv uvars g /\
     l4_core_inductive532 env own = SOME info /\
     l4_vhas_type961 venv uvars g
       (l4_vapps962 args (L4VConst961 own us)) (L4VSort961 usort) ==>
     LENGTH args = l4_kind_num_params493 info + l4_kind_num_indices493 info) /\
   (!uvars g own info ctor c d us params idxs t.
     l4_vctx_wf966 venv uvars g /\
     l4_core_inductive532 env own = SOME info /\
     l4_kind_ctors493 info = [ctor] /\
     l4_kfind_decl493 env ctor = SOME d /\
     l4_kdecl_kind493 d = L4KDConstructor493 c /\
     LENGTH params = l4_kind_num_params493 info /\
     LENGTH idxs = l4_kind_num_indices493 info /\
     l4_vhas_type961 venv uvars g
       (l4_vapps962 (APPEND params idxs) (L4VConst961 own us)) t ==>
     ?ty_p. l4_vhas_type961 venv uvars g
              (l4_vapps962 params (L4VConst961 ctor us)) ty_p) /\
   (!uvars n k g g' own info t0 us args.
     l4_vctx_wf966 venv uvars g' /\
     l4_vctx_liftN966 n k g g' /\
     l4_core_inductive532 env own = SOME info /\
     l4_vis_defeq_u961 venv uvars g' (l4_vliftN961 t0 n k)
       (l4_vapps962 args (L4VConst961 own us)) ==>
     ?args0.
       LENGTH args0 = LENGTH args /\
       l4_vis_defeq_u961 venv uvars g t0 (l4_vapps962 args0 (L4VConst961 own us)))`;;

let l4_ves_proj_thms973 =
  let raw = UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL l4_venv_sound973))) in
  CONJUNCTS raw;;

let [l4_ves_wf973; l4_ves_inj973; l4_ves_ind_inj973; l4_ves_prims973;
     l4_ves_constants973; l4_ves_delta973; l4_ves_quot_red973;
     l4_ves_recursor_iota973; l4_ves_recursor_rhs973; l4_ves_recursor_k_fields973;
     l4_ves_proj_const973; l4_ves_proj_iota973; l4_ves_proj_telescope973;
     l4_ves_struct_eta973; l4_ves_ctor_type_head973; l4_ves_ind_shape973;
     l4_ves_ind_type_arity973; l4_ves_ctor_params_wf973; l4_ves_ind_weakN973] =
  map (GENL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] o DISCH_ALL) l4_ves_proj_thms973;;

let l4_venv_sound_empty973 = prove
 (`l4_defeq_injectivity972 l4_venv_empty961 ==>
   l4_venv_sound973 [] l4_venv_empty961`,
  DISCH_TAC THEN
  ASM_REWRITE_TAC [l4_venv_sound973;l4_venv_empty_wf966;l4_has_primitives_empty973;
                   l4_vind_head_inj973;l4_core_inductive532;l4_core_constructor532;
                   l4_kfind_decl493;distinctness "option"]);;

let l4_vtr_proj_congr973 = prove
 (`!env venv uvars g owner1 owner2 idx sv1 sv2 pv1 pv2 fty1 fty2.
   l4_venv_sound973 env venv /\
   l4_vctx_wf966 venv uvars g /\
   l4_vtr_proj973 env venv uvars g owner1 idx sv1 pv1 fty1 /\
   l4_vtr_proj973 env venv uvars g owner2 idx sv2 pv2 fty2 /\
   l4_vis_defeq_u961 venv uvars g sv1 sv2 ==>
   owner1 = owner2 /\ l4_vis_defeq_u961 venv uvars g pv1 pv2`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vtr_proj973] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv uvars g
       (l4_vapps962 (APPEND params indices) (L4VConst961 owner1 us))
       (l4_vapps962 (APPEND params' indices') (L4VConst961 owner2 us'))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
   MAP_EVERY EXISTS_TAC [`sv1:l4_vexpr961`;`sv2:l4_vexpr961`;`sv2:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vis_defeq_u_of_l972;l4_vhas_type961];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_inj973) THEN
  ASM_REWRITE_TAC [l4_vind_head_inj973] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`uvars:num`;`g:l4_vexpr961 list`;`owner1:l4_name`;`owner2:l4_name`;
     `info:l4_kinductive_data493`;`info':l4_kinductive_data493`;
     `us:l4_vlevel961 list`;`us':l4_vlevel961 list`;
     `APPEND (params:l4_vexpr961 list) indices`;
     `APPEND (params':l4_vexpr961 list) indices'`]) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  SUBGOAL_THEN `info' = info:l4_kinductive_data493` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `owner2 = owner1:l4_name` SUBST_ALL_TAC THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  CONJ_TAC THENL [REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 (l4_vis_defeq_u961 venv uvars g) params params'` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `!(xs:l4_vexpr961 list) ys. l4_kfirstn494 (APPEND xs ys) (LENGTH xs) = xs`
     (fun th ->
       MP_TAC (ISPECL [`l4_vis_defeq_u961 venv uvars g`;
                       `APPEND (params:l4_vexpr961 list) indices`;
                       `APPEND (params':l4_vexpr961 list) indices'`;
                       `l4_kind_num_params493 info`] l4_all2_firstn973) THEN
       MP_TAC (SPECL [`params:l4_vexpr961 list`;`indices:l4_vexpr961 list`] th) THEN
       MP_TAC (SPECL [`params':l4_vexpr961 list`;`indices':l4_vexpr961 list`] th) THEN
       ASM_SIMP_TAC []) THEN
   LIST_INDUCT_TAC THEN GEN_TAC THEN
   REWRITE_TAC [APPEND;LENGTH;l4_kfirstn494;NOT_SUC;l4_suc_sub1_973] THENL
   [STRUCT_CASES_TAC (ISPEC `ys:l4_vexpr961 list` list_CASES) THEN REWRITE_TAC [l4_kfirstn494];
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?pci. l4_venv_lookup_const961 venv (l4_proj_const_name962 owner1 idx) pci /\
           l4_vc_uvars961 pci = LENGTH (l4_kdecl_params493 d)`
    (X_CHOOSE_THEN `pci:l4_vconstant961` STRIP_ASSUME_TAC) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_proj_const973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`owner1:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
      `c:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`idx:num`]) THEN
   ASM_SIMP_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `ctor = ctor':l4_name` SUBST_ALL_TAC THENL
  [UNDISCH_TAC `l4_kind_ctors493 info = [ctor']` THEN
   ASM_SIMP_TAC [injectivity "list"];
   ALL_TAC] THEN
  SUBGOAL_THEN `d = d':l4_kdeclaration493` SUBST_ALL_TAC THENL
  [UNDISCH_TAC `l4_kfind_decl493 env ctor' = SOME d'` THEN
   ASM_SIMP_TAC [injectivity "option"];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv uvars g
       (L4VConst961 (l4_proj_const_name962 owner1 idx) us)
       (L4VConst961 (l4_proj_const_name962 owner1 idx) us')` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `l4_vinstL961 us (l4_vc_type961 pci)` THEN
   MATCH_MP_TAC l4_vis_defeq_const961 THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [l4_vproj_expr962] THEN
  MATCH_MP_TAC l4_vis_defeq_u_appDF973 THEN
  MAP_EVERY EXISTS_TAC [`fty1:l4_vexpr961`;`fty2:l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_inj973]; ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `?ft1. l4_vhas_type961 venv uvars g
              (l4_vapps962 params (L4VConst961 (l4_proj_const_name962 owner1 idx) us)) ft1`
     (X_CHOOSE_TAC `ft1:l4_vexpr961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `l4_vapps962 params (L4VConst961 (l4_proj_const_name962 owner1 idx) us)`;
                   `sv1:l4_vexpr961`;`fty1:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_wf973) THEN
    UNDISCH_TAC `l4_vhas_type961 venv uvars g pv1 fty1` THEN
    ASM_REWRITE_TAC [l4_vproj_expr962] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?ft2. l4_vhas_type961 venv uvars g
              (l4_vapps962 params' (L4VConst961 (l4_proj_const_name962 owner1 idx) us')) ft2`
     (X_CHOOSE_TAC `ft2:l4_vexpr961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   `l4_vapps962 params' (L4VConst961 (l4_proj_const_name962 owner1 idx) us')`;
                   `sv2:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_wf973) THEN
    UNDISCH_TAC `l4_vhas_type961 venv uvars g pv2 fty2` THEN
    ASM_REWRITE_TAC [l4_vproj_expr962] THEN MESON_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vapps_defeq_congr973 THEN
   MAP_EVERY EXISTS_TAC [`ft1:l4_vexpr961`;`ft2:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; ASM_MESON_TAC [l4_ves_inj973]];
   CONJ_TAC THENL
   [UNDISCH_TAC `l4_vhas_type961 venv uvars g pv1 fty1` THEN
    ASM_REWRITE_TAC [l4_vproj_expr962];
    UNDISCH_TAC `l4_vhas_type961 venv uvars g pv2 fty2` THEN
    ASM_REWRITE_TAC [l4_vproj_expr962]]]);;

(* ========================================================================= *)
(* 8. Uniqueness & Context Conversion for l4_vtr_expr_s973 / l4_vtr_expr973  *)
(* ========================================================================= *)

let l4_elim_case_eqs973 =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if is_var r && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else if is_var l && not (vfree_in l r) then SUBST_ALL_TAC th
    else failwith "no"));;

let l4_strip4_then973 ttac =
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ttac))));;

let l4_vtr_expr_s_defeq_ctx_uniq973 = prove
 (`!env venv ps l e e1.
   l4_vtr_expr_s973 env venv ps l e e1 ==>
   (!l2 e2.
     l4_venv_sound973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l2 /\
     l4_vl_ctx_defeq973 venv (LENGTH ps) l l2 /\
     l4_vtr_expr_s973 env venv ps l2 e e2 ==>
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) e1 e2)`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`;
                  `l2:l4_vl_ctx_rec973`;`i:num`;`e:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vl_lookup_bound_defeq973) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e2':l4_vexpr961`
     (X_CHOOSE_THEN `ty2':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `e2' = e2:l4_vexpr961` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC []];
   (* FVar *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`;
                  `l2:l4_vl_ctx_rec973`;`n:l4_name`;`e:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vl_lookup_free_defeq973) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e2':l4_vexpr961`
     (X_CHOOSE_THEN `ty2':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `e2' = e2:l4_vexpr961` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC []];
   (* Sort *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   ASM_MESON_TAC [injectivity "option";l4_vis_defeq_u961;l4_vis_defeq_sort961;
                  l4_vlevel_equiv_refl961];
   (* Const *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   ASM_MESON_TAC [injectivity "option";l4_vis_defeq_u961;l4_vis_defeq_const961;
                  l4_vlevel_equiv_refl_all973];
   (* App *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   l4_strip4_then973
     (X_CHOOSE_THEN `f0:l4_kexpr447`
      (X_CHOOSE_THEN `a0:l4_kexpr447`
       (X_CHOOSE_THEN `f'':l4_vexpr961`
        (X_CHOOSE_THEN `a'':l4_vexpr961`
         (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) f' f''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' a''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VApp961 f'' a'') ty'`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l2`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_symm973;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_appDF973 THEN
   MAP_EVERY EXISTS_TAC [`ty:l4_vexpr961`;`ty':l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
   (* Lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   l4_strip4_then973
     (X_CHOOSE_THEN `n0:l4_name`
      (X_CHOOSE_THEN `bi0:l4_kbinder447`
       (X_CHOOSE_THEN `dom0:l4_kexpr447`
        (X_CHOOSE_THEN `body0:l4_kexpr447`
         (X_CHOOSE_THEN `dom'':l4_vexpr961`
          (X_CHOOSE_THEN `body'':l4_vexpr961`
           (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom'' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN
    EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l2 dom'')` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2` THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' body''`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vl_ctx_push_lam973;l4_vl_ctx_wf_push_lam973];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `cod:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' body'' cod`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `L4VForallE961 dom' cod` THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN
   EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   (* Pi *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   l4_strip4_then973
     (X_CHOOSE_THEN `n0:l4_name`
      (X_CHOOSE_THEN `bi0:l4_kbinder447`
       (X_CHOOSE_THEN `dom0:l4_kexpr447`
        (X_CHOOSE_THEN `body0:l4_kexpr447`
         (X_CHOOSE_THEN `dom'':l4_vexpr961`
          (X_CHOOSE_THEN `body'':l4_vexpr961`
           (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o REWRITE_RULE [l4_vis_type961]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom'' (L4VSort961 u)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l2 dom'')` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2` THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' body''`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vl_ctx_push_lam973;l4_vl_ctx_wf_push_lam973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' body'' (L4VSort961 v)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [];
   (* Let *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   l4_strip4_then973
     (X_CHOOSE_THEN `n0:l4_name`
      (X_CHOOSE_THEN `ty0:l4_kexpr447`
       (X_CHOOSE_THEN `val_e0:l4_kexpr447`
        (X_CHOOSE_THEN `body0:l4_kexpr447`
         (X_CHOOSE_THEN `nd0:bool`
          (X_CHOOSE_THEN `ty'':l4_vexpr961`
           (X_CHOOSE_THEN `val'':l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' ty''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val' val''`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' ty'' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN
    EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val' val'' ty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_let973 l ty' val') (l4_vl_push_let973 l2 ty'' val'')` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2` THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   ASM_MESON_TAC [l4_vl_ctx_push_let973;l4_vl_ctx_wf_push_let973];
   (* Proj *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   l4_strip4_then973
     (X_CHOOSE_THEN `owner0:l4_name`
      (X_CHOOSE_THEN `idx0:num`
       (X_CHOOSE_THEN `e0:l4_kexpr447`
        (X_CHOOSE_THEN `sv':l4_vexpr961`
         (X_CHOOSE_THEN `fty':l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) sv sv'`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner idx sv' e2 fty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_proj_defeq_ctx973 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l2`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_symm973;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   ASM_MESON_TAC [l4_vtr_proj_congr973;l4_vl_ctx_wf_to_vctx_wf973];
   (* NatLit *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   ASM_MESON_TAC [l4_vis_defeq_u_refl973];
   (* StrLit *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   ASM_MESON_TAC [injectivity "option";l4_vis_defeq_u_refl973];
   (* MData *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_s_uniq973 = prove
 (`!env venv ps l e e1 e2.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr_s973 env venv ps l e e1 /\
   l4_vtr_expr_s973 env venv ps l e e2 ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) e1 e2`,
  MESON_TAC [l4_vtr_expr_s_defeq_ctx_uniq973;l4_vl_ctx_defeq_refl973]);;

let l4_vtr_expr_uniq973 = prove
 (`!env venv ps l e e1 e2.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l e e1 /\
   l4_vtr_expr973 env venv ps l e e2 ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) e1 e2`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 e0'`
    ASSUME_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_uniq973]; ALL_TAC] THEN
  ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                 l4_vis_defeq_u_symm972;l4_vis_defeq_u_trans972]);;

let l4_vtr_expr_s_defeq_ctx_transport973 = prove
 (`!env venv ps l e e1.
   l4_vtr_expr_s973 env venv ps l e e1 ==>
   (!l2.
     l4_venv_sound973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l2 /\
     l4_vl_ctx_defeq973 venv (LENGTH ps) l l2 ==>
     ?e2. l4_vtr_expr_s973 env venv ps l2 e e2 /\
          l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l2) e2 e1)`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`;
                  `l2:l4_vl_ctx_rec973`;`i:num`;`e:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vl_lookup_bound_defeq973) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e2:l4_vexpr961`
     (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `e2:l4_vexpr961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty2:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vl_lookup_bound_has_type973;l4_ves_wf973;l4_venv_wf_closed966];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973]];
   (* FVar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`;
                  `l2:l4_vl_ctx_rec973`;`n:l4_name`;`e:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vl_lookup_free_defeq973) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e2:l4_vexpr961`
     (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `e2:l4_vexpr961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `ty2:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vl_lookup_free_has_type973;l4_ves_wf973;l4_venv_wf_closed966];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973]];
   (* Sort *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `L4VSort961 u'` THEN
   CONJ_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_sort973]; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLSucc961 u')` THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
   (* Const *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `L4VConst961 c us'` THEN
   CONJ_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_const973]; ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN
   MATCH_MP_TAC l4_vis_defeq_const961 THEN ASM_REWRITE_TAC [l4_vlevel_equiv_refl_all973];
   (* App *)
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `l2:l4_vl_ctx_rec973`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `l2:l4_vl_ctx_rec973`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `f2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) (L4VApp961 f' a') ty`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l2`;
                  `f':l4_vexpr961`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom:l4_vexpr961`
     (X_CHOOSE_THEN `body:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) f2 f' (L4VForallE961 dom body)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) a2 a' dom`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2)
        (L4VApp961 f2 a2) (L4VApp961 f' a') (l4_vinst0961 body a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VApp961 f2 a2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vinst0961 body a2` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []];
   (* Lam *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `?dom2. l4_vtr_expr_s973 env venv ps l2 dom dom2 /\
                        l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2 dom'`
     (X_CHOOSE_THEN `dom2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_type_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2 dom' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
                   (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l2 dom2)` ASSUME_TAC THENL
   [MP_TAC (ASSUME `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2`) THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973] THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l2`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_symm973;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN `?body2. l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l2 dom2) body body2 /\
                         l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body2 body'`
     (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973]; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `cod:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body' cod`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom' (l4_vl_ctx973 l)`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;
                   l4_vl_ctx_push_lam973;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body2 body' cod`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2)
        (L4VLam961 dom2 body2) (L4VLam961 dom' body') (L4VForallE961 dom2 cod)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VLam961 dom2 body2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `L4VForallE961 dom2 cod` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []];
   (* Pi *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `?dom2. l4_vtr_expr_s973 env venv ps l2 dom dom2 /\
                        l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2 dom'`
     (X_CHOOSE_THEN `dom2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o REWRITE_RULE [l4_vis_type961]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom' (L4VSort961 u)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2 dom' (L4VSort961 u)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) dom2` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
                   (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l2 dom2)` ASSUME_TAC THENL
   [MP_TAC (ASSUME `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2`) THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973] THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l2`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_symm973;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN `?body2. l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l2 dom2) body body2 /\
                         l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body2 body'`
     (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body' (L4VSort961 v)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom' (l4_vl_ctx973 l)`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;
                   l4_vl_ctx_push_lam973;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom2 (l4_vl_ctx973 l2)) body2 body' (L4VSort961 v)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2)
        (L4VForallE961 dom2 body2) (L4VForallE961 dom' body') (L4VSort961 (L4VLIMax961 u v))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VForallE961 dom2 body2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []];
   (* Let *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `?ty2. l4_vtr_expr_s973 env venv ps l2 ty ty2 /\
                       l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) ty2 ty'`
     (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?val2. l4_vtr_expr_s973 env venv ps l2 val_e val2 /\
                        l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) val2 val'`
     (X_CHOOSE_THEN `val2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_type_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) ty2 ty' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) ty'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) ty2` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) val' ty'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) val2 val' ty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) val2 ty2` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u:l4_vlevel961`] THEN
    ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vis_defeq_refl_l961;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
                   (l4_vl_push_let973 l ty' val') (l4_vl_push_let973 l2 ty2 val2)` ASSUME_TAC THENL
   [MP_TAC (ASSUME `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) l l2`) THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973] THEN CONJ_TAC THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l2`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_symm973;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   SUBGOAL_THEN `?body2. l4_vtr_expr_s973 env venv ps (l4_vl_push_let973 l2 ty2 val2) body body2 /\
                         l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) body2 body'`
     (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC [l4_vl_ctx_wf_push_let973;l4_vl_ctx_push_let973]; ALL_TAC] THEN
   EXISTS_TAC `body2:l4_vexpr961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
    MAP_EVERY EXISTS_TAC [`ty2:l4_vexpr961`;`val2:l4_vexpr961`] THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   (* Proj *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `?sv2. l4_vtr_expr_s973 env venv ps l2 e sv2 /\
                       l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) sv2 sv`
     (X_CHOOSE_THEN `sv2:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) owner idx sv pv fty`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_proj_defeq_ctx973 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973];
    ALL_TAC] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_vtr_proj973]) THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) sv2 sv
        (l4_vapps962 (APPEND params indices) (L4VConst961 owner us))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) sv2
        (l4_vapps962 (APPEND params indices) (L4VConst961 owner us))` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l2`;
                  `l4_vapps962 params (L4VConst961 (l4_proj_const_name962 owner idx) us)`;
                  `sv:l4_vexpr961`;`fty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973;l4_vproj_expr962]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `pdom:l4_vexpr961`
     (X_CHOOSE_THEN `pbody:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) sv2 sv pdom`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2)
        (l4_vproj_expr962 owner idx us params sv2)
        (l4_vproj_expr962 owner idx us params sv)
        (l4_vinst0961 pbody sv2)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vproj_expr962] THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
    EXISTS_TAC `pdom:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   EXISTS_TAC `l4_vproj_expr962 owner idx us params sv2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
    MAP_EVERY EXISTS_TAC [`sv2:l4_vexpr961`;`l4_vinst0961 pbody sv2`] THEN
    ASM_REWRITE_TAC [l4_vtr_proj973] THEN
    MAP_EVERY EXISTS_TAC
      [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
       `d:l4_kdeclaration493`;`us:l4_vlevel961 list`;
       `params:l4_vexpr961 list`;`indices:l4_vexpr961 list`] THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []];
   (* NatLit *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `l4_nat_lit973 m` THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) (l4_nat_lit973 m) l4_vnat_ty973`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ASM_MESON_TAC [l4_vtr_expr_s_natlit973;l4_vis_defeq_u_refl973]];
   (* StrLit *)
   REPEAT STRIP_TAC THEN EXISTS_TAC `e':l4_vexpr961` THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) e' l4_vstring_ty973`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vhas_type961];
    ASM_MESON_TAC [l4_vtr_expr_s_strlit973;l4_vis_defeq_u_refl973]];
   (* MData *)
   REPEAT STRIP_TAC THEN ASM_MESON_TAC [l4_vtr_expr_s_mdata973]]);;

let l4_vtr_expr_defeq_ctx973 = prove
 (`!env venv ps l1 l2 e e1.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l1 /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l2 /\
   l4_vl_ctx_defeq973 venv (LENGTH ps) l1 l2 /\
   l4_vtr_expr973 env venv ps l1 e e1 ==>
   l4_vtr_expr973 env venv ps l2 e e1`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l1:l4_vl_ctx_rec973`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
    l4_vtr_expr_s_defeq_ctx_transport973) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `l2:l4_vl_ctx_rec973`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `e2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e2:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l2) e0 e1`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_defeqDFC973 THEN
   MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`l4_vl_ctx973 l1`] THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_defeq_to_vis_defeq_ctx973];
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                  l4_vis_defeq_u_trans972]]);;

(* ========================================================================= *)
(* 9. Lifting, Substitution (Lam & Let), Universe Instantiation, & Weakening *)
(* ========================================================================= *)

let l4_vl_bound_lift_RULES973,l4_vl_bound_lift_INDUCT973,l4_vl_bound_lift_CASES973 =
  new_inductive_definition
 `(!ins bs. l4_vl_bound_lift973 ins 0 0 bs (APPEND ins bs)) /\
  (!ins idx k bs bs' ty.
     l4_vl_bound_lift973 ins idx k bs bs' ==>
     l4_vl_bound_lift973 ins (SUC idx) (SUC k)
       (CONS (L4VLLam973 ty) bs)
       (CONS (L4VLLam973 (l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k)) bs')) /\
  (!ins idx k bs bs' ty val_e.
     l4_vl_bound_lift973 ins idx k bs bs' ==>
     l4_vl_bound_lift973 ins (SUC idx) k
       (CONS (L4VLLet973 ty val_e) bs)
       (CONS (L4VLLet973 (l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k)
                         (l4_vliftN961 val_e (LENGTH (l4_vlentries_to_ctx973 ins)) k)) bs'))`;;

let [l4_vl_bound_lift_zero973; l4_vl_bound_lift_lam973; l4_vl_bound_lift_let973] =
  CONJUNCTS l4_vl_bound_lift_RULES973;;

let l4_vl_bound_lift_to_vctx_liftN973 = prove
 (`!ins idx k bs bs'.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   (!base. l4_vctx_liftN966 (LENGTH (l4_vlentries_to_ctx973 ins)) k
             (APPEND (l4_vlentries_to_ctx973 bs) base)
             (APPEND (l4_vlentries_to_ctx973 bs') base))`,
  MATCH_MP_TAC l4_vl_bound_lift_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vlentries_to_ctx_append973;GSYM APPEND_ASSOC] THEN
   MATCH_MP_TAC l4_vctx_liftN_zero966 THEN REFL_TAC;
   REWRITE_TAC [l4_vlentries_to_ctx973;APPEND] THEN
   MESON_TAC [l4_vctx_liftN_succ966];
   REWRITE_TAC [l4_vlentries_to_ctx973] THEN MESON_TAC []]);;

let l4_vl_bound_lift_lams973 = prove
 (`!ins idx k bs bs'.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   LENGTH (l4_vlentries_to_ctx973 bs') =
   LENGTH (l4_vlentries_to_ctx973 bs) + LENGTH (l4_vlentries_to_ctx973 ins) /\
   k <= LENGTH (l4_vlentries_to_ctx973 bs)`,
  MATCH_MP_TAC l4_vl_bound_lift_INDUCT973 THEN
  REWRITE_TAC [l4_vlentries_to_ctx_append973;l4_vlentries_to_ctx973;
               LENGTH_APPEND;LENGTH] THEN ARITH_TAC);;

let l4_vl_bound_lift_lookup973 = prove
 (`!ins idx k bs bs'.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   (!i d e ty.
     l4_vl_lookup_bound973 bs i d = SOME (e, ty) ==>
     l4_vl_lookup_bound973 bs' (if i < idx then i else i + LENGTH ins) d =
     SOME (l4_vliftN961 e (LENGTH (l4_vlentries_to_ctx973 ins)) (d + k),
           l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) (d + k)))`,
  MATCH_MP_TAC l4_vl_bound_lift_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* zero *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [LT;ADD_CLAUSES] THEN
   SUBGOAL_THEN
     `!xs bs i d. l4_vl_lookup_bound973 (APPEND xs bs) (i + LENGTH xs) d =
                  l4_vl_lookup_bound973 bs i (d + LENGTH (l4_vlentries_to_ctx973 xs))`
     ASSUME_TAC THENL
    [LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;LENGTH;ADD_CLAUSES;l4_vlentries_to_ctx973] THEN
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
     REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973;LENGTH;
                  NOT_SUC;SUC_SUB1;ARITH_RULE `!d m. d + SUC m = SUC d + m`] THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_lookup_bound_shift_at973 THEN ASM_REWRITE_TAC [LE_REFL];
   (* lam *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vl_lookup_bound973 (CONS (L4VLLam973 ty) bs) i d = SOME (e, ty')` THEN
   REWRITE_TAC [l4_vl_lookup_bound973] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    ASM_REWRITE_TAC [LT_0;l4_vl_lookup_bound973;l4_vliftN961;l4_vlift_var961;
                     injectivity "option";PAIR_EQ] THEN
    CONJ_TAC THENL
    [COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
     MP_TAC (SPECL [`ty:l4_vexpr961`;`LENGTH (l4_vlentries_to_ctx973 ins)`;
                    `SUC d`;`k:num`;`0`] l4_vliftN_comm966) THEN
     REWRITE_TAC [LE_0;ARITH_RULE `!d k. SUC d + k = d + SUC k`] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th])];
    DISCH_TAC THEN
    SUBGOAL_THEN `~((if i < SUC idx then i else i + LENGTH (ins:l4_vl_entry973 list)) = 0)`
      ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
    SUBGOAL_THEN
      `(if i < SUC idx then i else i + LENGTH (ins:l4_vl_entry973 list)) - 1 =
       (if i - 1 < idx then i - 1 else (i - 1) + LENGTH ins)` SUBST1_TAC THENL
    [REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`i - 1`;`SUC d`;`e:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ASM_SIMP_TAC [ARITH_RULE `!d k. SUC d + k = d + SUC k`]];
   (* let *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vl_lookup_bound973 (CONS (L4VLLet973 ty val_e) bs) i d = SOME (e, ty')` THEN
   REWRITE_TAC [l4_vl_lookup_bound973] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    ASM_REWRITE_TAC [LT_0;l4_vl_lookup_bound973;injectivity "option";PAIR_EQ] THEN CONJ_TAC THENL
    [MP_TAC (SPECL [`val_e:l4_vexpr961`;`LENGTH (l4_vlentries_to_ctx973 ins)`;
                    `d:num`;`k:num`;`0`] l4_vliftN_comm966) THEN
     REWRITE_TAC [LE_0] THEN DISCH_THEN (fun th -> REWRITE_TAC [th]);
     MP_TAC (SPECL [`ty:l4_vexpr961`;`LENGTH (l4_vlentries_to_ctx973 ins)`;
                    `d:num`;`k:num`;`0`] l4_vliftN_comm966) THEN
     REWRITE_TAC [LE_0] THEN DISCH_THEN (fun th -> REWRITE_TAC [th])];
    DISCH_TAC THEN
    SUBGOAL_THEN `~((if i < SUC idx then i else i + LENGTH (ins:l4_vl_entry973 list)) = 0)`
      ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
    SUBGOAL_THEN
      `(if i < SUC idx then i else i + LENGTH (ins:l4_vl_entry973 list)) - 1 =
       (if i - 1 < idx then i - 1 else (i - 1) + LENGTH ins)` SUBST1_TAC THENL
    [REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`i - 1`;`d:num`;`e:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC []]]);;

let l4_vtr_expr_s_lift_gen973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!ins idx k bs'.
     l4_venv_closed966 venv /\
     l4_vl_bound_lift973 ins idx k (l4_vl_bound973 l) bs' ==>
     l4_vtr_expr_s973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs')
       (l4_klift447 e (LENGTH ins) idx)
       (l4_vliftN961 e' (LENGTH (l4_vlentries_to_ctx973 ins)) k))`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN
   EXISTS_TAC `l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`ins:l4_vl_entry973 list`;`idx:num`;`k:num`;`l4_vl_bound973 l`;`bs':l4_vl_entry973 list`]
      l4_vl_bound_lift_lookup973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`i:num`;`0`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
    REWRITE_TAC [ADD_CLAUSES;GSYM l4_vl_bvar973] THEN
    ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN SIMP_TAC [ADD_SYM];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
    ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973]];
   (* FVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN
   EXISTS_TAC `l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_fvar973;l4_vl_free973;l4_vl_bound_lams973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`ins:l4_vl_entry973 list`;`idx:num`;`k:num`;`l4_vl_bound973 l`;`bs':l4_vl_entry973 list`]
      l4_vl_bound_lift_lams973) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_lookup_free_shift_at973 THEN
    ASM_REWRITE_TAC [GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
    ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973]];
   (* Sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* App *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN
   EXISTS_TAC `l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k` THEN
   ASM_SIMP_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `L4VApp961 f' a'`;`L4VApp961 f' a'`;`ty:l4_vexpr961`;
                  `LENGTH (l4_vlentries_to_ctx973 ins)`;`k:num`;
                  `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
     l4_vis_defeq_weakN966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vliftN961;l4_vl_ctx973] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
   (* Lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN
   EXISTS_TAC `l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k` THEN
   REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`ins:l4_vl_entry973 list`;`SUC idx`;`SUC k`;
       `CONS (L4VLLam973 (l4_vliftN961 dom' (LENGTH (l4_vlentries_to_ctx973 ins)) k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_bound_lift_lam973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VLam961 dom' body'`;`L4VLam961 dom' body'`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vlentries_to_ctx973 ins)`;`k:num`;
                   `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
      l4_vis_defeq_weakN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vliftN961;l4_vl_ctx973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973]];
   (* Pi *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN
   EXISTS_TAC `l4_vliftN961 ty (LENGTH (l4_vlentries_to_ctx973 ins)) k` THEN
   REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`ins:l4_vl_entry973 list`;`SUC idx`;`SUC k`;
       `CONS (L4VLLam973 (l4_vliftN961 dom' (LENGTH (l4_vlentries_to_ctx973 ins)) k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_bound_lift_lam973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VForallE961 dom' body'`;`L4VForallE961 dom' body'`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vlentries_to_ctx973 ins)`;`k:num`;
                   `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
      l4_vis_defeq_weakN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vliftN961;l4_vl_ctx973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973]];
   (* Let *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC
     [`l4_vliftN961 ty' (LENGTH (l4_vlentries_to_ctx973 ins)) k`;
      `l4_vliftN961 val' (LENGTH (l4_vlentries_to_ctx973 ins)) k`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
    ASM_SIMP_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
    ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
    REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`ins:l4_vl_entry973 list`;`SUC idx`;`k:num`;
       `CONS (L4VLLet973 (l4_vliftN961 ty' (LENGTH (l4_vlentries_to_ctx973 ins)) k)
                         (l4_vliftN961 val' (LENGTH (l4_vlentries_to_ctx973 ins)) k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_bound_lift_let973]];
   (* Proj *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC
     [`l4_vliftN961 sv (LENGTH (l4_vlentries_to_ctx973 ins)) k`;
      `l4_vliftN961 fty (LENGTH (l4_vlentries_to_ctx973 ins)) k`] THEN
   ASM_SIMP_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
   MATCH_MP_TAC l4_vtr_proj_weakN973 THEN
   EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [l4_vl_ctx973] THEN
   ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
   (* NatLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447;l4_vliftN_nat_lit973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `l4_nat_lit973 m`;`l4_nat_lit973 m`;`l4_vnat_ty973`;
                  `LENGTH (l4_vlentries_to_ctx973 ins)`;`k:num`;
                  `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
     l4_vis_defeq_weakN966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vliftN_nat_lit973;l4_vnat_ty973;
                    l4_vliftN961;l4_vl_ctx973] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
   (* StrLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   SUBGOAL_THEN `l4_vliftN961 e' (LENGTH (l4_vlentries_to_ctx973 ins)) k = e'`
     (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vliftN_tr_str_lit973]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`l4_vstring_ty973`;
                  `LENGTH (l4_vlentries_to_ctx973 ins)`;`k:num`;
                  `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
     l4_vis_defeq_weakN966) THEN
   SUBGOAL_THEN `l4_vliftN961 e' (LENGTH (l4_vlentries_to_ctx973 ins)) k = e'`
     (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vliftN_tr_str_lit973]; ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vstring_ty973;l4_vliftN961;l4_vl_ctx973] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973];
   (* MData *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_klift447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_SIMP_TAC []]);;

let l4_vtr_expr_lift_prefix973 = prove
 (`!env venv ps l ins e e'.
   l4_venv_closed966 venv /\
   l4_vtr_expr973 env venv ps l e e' ==>
   l4_vtr_expr973 env venv ps
     (L4VLCtx973 (l4_vl_free973 l) (APPEND ins (l4_vl_bound973 l)))
     (l4_klift447 e (LENGTH ins) 0)
     (l4_vliftN961 e' (LENGTH (l4_vlentries_to_ctx973 ins)) 0)`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `l4_vliftN961 e0 (LENGTH (l4_vlentries_to_ctx973 ins)) 0` THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC [l4_vtr_expr_s_lift_gen973;l4_vl_bound_lift_zero973];
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
   MATCH_MP_TAC l4_vis_defeq_u_weakN973 THEN
   EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [l4_vl_ctx973] THEN
   ASM_MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973;l4_vl_bound_lift_zero973]]);;

let l4_vtr_expr_lift_lam973 = prove
 (`!env venv ps l ty e e'.
   l4_venv_closed966 venv /\
   l4_vtr_expr973 env venv ps l e e' ==>
   l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l ty)
     (l4_klift447 e 1 0) (l4_vlift961 e')`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`[L4VLLam973 ty]`;`e:l4_kexpr447`;`e':l4_vexpr961`]
    l4_vtr_expr_lift_prefix973) THEN
  ASM_REWRITE_TAC [LENGTH;APPEND;l4_vlentries_to_ctx973;GSYM l4_vl_push_lam973;
                   GSYM l4_vlift961;ARITH_RULE `SUC 0 = 1`]);;

let l4_vtr_expr_lift_let973 = prove
 (`!env venv ps l ty val_e e e'.
   l4_venv_closed966 venv /\
   l4_vtr_expr973 env venv ps l e e' ==>
   l4_vtr_expr973 env venv ps (l4_vl_push_let973 l ty val_e)
     (l4_klift447 e 1 0) e'`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`[L4VLLet973 ty val_e]`;`e:l4_kexpr447`;`e':l4_vexpr961`]
    l4_vtr_expr_lift_prefix973) THEN
  ASM_REWRITE_TAC [LENGTH;APPEND;l4_vlentries_to_ctx973;GSYM l4_vl_push_let973;
                   l4_vliftN_zero961;ARITH_RULE `SUC 0 = 1`]);;

(* Substitution under lam and let entries *)
let l4_vl_bound_inst_lam_RULES973,l4_vl_bound_inst_lam_INDUCT973,l4_vl_bound_inst_lam_CASES973 =
  new_inductive_definition
 `(!a0 e0 suf.
     l4_vl_bound_inst_lam973 a0 e0 suf 0 0 (CONS (L4VLLam973 a0) suf) suf) /\
  (!a0 e0 suf idx k bs bs' ty.
     l4_vl_bound_inst_lam973 a0 e0 suf idx k bs bs' ==>
     l4_vl_bound_inst_lam973 a0 e0 suf (SUC idx) (SUC k)
       (CONS (L4VLLam973 ty) bs)
       (CONS (L4VLLam973 (l4_vinst961 ty e0 k)) bs')) /\
  (!a0 e0 suf idx k bs bs' ty val_e.
     l4_vl_bound_inst_lam973 a0 e0 suf idx k bs bs' ==>
     l4_vl_bound_inst_lam973 a0 e0 suf (SUC idx) k
       (CONS (L4VLLet973 ty val_e) bs)
       (CONS (L4VLLet973 (l4_vinst961 ty e0 k) (l4_vinst961 val_e e0 k)) bs'))`;;

let [l4_vl_inst_lam_zero973; l4_vl_inst_lam_lam973; l4_vl_inst_lam_let973] =
  CONJUNCTS l4_vl_bound_inst_lam_RULES973;;

let l4_vl_bound_inst_lam_to_vctx_instN973 = prove
 (`!a0 e0 suf idx k bs bs'.
   l4_vl_bound_inst_lam973 a0 e0 suf idx k bs bs' ==>
   (!base.
     l4_vctx_instN966 (APPEND (l4_vlentries_to_ctx973 suf) base) e0 a0 k
       (APPEND (l4_vlentries_to_ctx973 bs) base)
       (APPEND (l4_vlentries_to_ctx973 bs') base))`,
  MATCH_MP_TAC l4_vl_bound_inst_lam_INDUCT973 THEN
  REWRITE_TAC [l4_vlentries_to_ctx973;APPEND] THEN
  MESON_TAC [l4_vctx_instN_zero966;l4_vctx_instN_succ966]);;

let l4_vl_bound_inst_lam_to_lift973 = prove
 (`!a0 e0 suf idx k bs bs'.
   l4_vl_bound_inst_lam973 a0 e0 suf idx k bs bs' ==>
   ?pre. LENGTH pre = idx /\
         LENGTH (l4_vlentries_to_ctx973 pre) = k /\
         bs' = APPEND pre suf`,
  MATCH_MP_TAC l4_vl_bound_inst_lam_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN EXISTS_TAC `[]:l4_vl_entry973 list` THEN
   REWRITE_TAC [LENGTH;APPEND;l4_vlentries_to_ctx973];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `CONS (L4VLLam973 (l4_vinst961 ty e0 k)) pre` THEN
   ASM_REWRITE_TAC [LENGTH;APPEND;l4_vlentries_to_ctx973];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `CONS (L4VLLet973 (l4_vinst961 ty e0 k) (l4_vinst961 val_e e0 k)) pre` THEN
   ASM_REWRITE_TAC [LENGTH;APPEND;l4_vlentries_to_ctx973]]);;

let l4_vl_bound_inst_lam_lookup973 = prove
 (`!a0 e0 suf idx k bs bs'.
   l4_vl_bound_inst_lam973 a0 e0 suf idx k bs bs' ==>
   (!i d e ty.
     l4_vl_lookup_bound973 bs i d = SOME (e, ty) ==>
     (i < idx ==>
       l4_vl_lookup_bound973 bs' i d =
       SOME (l4_vinst961 e e0 (d + k), l4_vinst961 ty e0 (d + k))) /\
     (i = idx ==>
       e = L4VBVar961 (d + k) /\ ty = l4_vliftN961 a0 (SUC (d + k)) 0) /\
     (idx < i ==>
       l4_vl_lookup_bound973 bs' (i - 1) d =
       SOME (l4_vinst961 e e0 (d + k), l4_vinst961 ty e0 (d + k))))`,
  MATCH_MP_TAC l4_vl_bound_inst_lam_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* zero *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vl_lookup_bound973;LT;ADD_CLAUSES] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC (SPECL [`suf:l4_vl_entry973 list`;`i - 1`;`d:num`;`1`;`d:num`]
      l4_vl_lookup_bound_shift_at973) THEN
    SUBGOAL_THEN `?e' ty'. l4_vl_lookup_bound973 suf (i - 1) d = SOME (e', ty')`
      (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` ASSUME_TAC)) THENL
    [SUBGOAL_THEN
       `!xs j d1 d2 e ty.
         l4_vl_lookup_bound973 xs j d1 = SOME (e, ty) ==>
         ?e' ty'. l4_vl_lookup_bound973 xs j d2 = SOME (e', ty')`
       (fun th -> ASM_MESON_TAC [th]) THEN
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option"] THEN
     STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
     REWRITE_TAC [l4_vl_lookup_bound973] THEN
     COND_CASES_TAC THEN ASM_MESON_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPECL [`e':l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [LE_REFL;GSYM ADD1;injectivity "option";PAIR_EQ] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [injectivity "option";PAIR_EQ;ONE;
                     SPECL [`e':l4_vexpr961`;`e0:l4_vexpr961`;`0`;`d:num`] l4_vinst_vliftN_ge973;
                     SPECL [`ty':l4_vexpr961`;`e0:l4_vexpr961`;`0`;`d:num`] l4_vinst_vliftN_ge973;
                     l4_vliftN_zero961]];
   (* lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vl_lookup_bound973] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    ASM_REWRITE_TAC [LT_0;NOT_SUC;GSYM NOT_SUC;LT;l4_vl_lookup_bound973;l4_vinst961;l4_vinst_var961;
                     injectivity "option";PAIR_EQ] THEN
    CONJ_TAC THENL
    [COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
     MP_TAC (SPECL [`ty:l4_vexpr961`;`e0:l4_vexpr961`;`SUC d`;`0`;`k:num`]
       l4_vliftN_vinst_lo966) THEN
     REWRITE_TAC [LE_0;ARITH_RULE `!d k. SUC d + k = d + SUC k`] THEN SIMP_TAC []];
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`i - 1`;`SUC d`;`e:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [ARITH_RULE `!d k. SUC d + k = d + SUC k`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL
    [ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     SUBGOAL_THEN `~(i - 1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
     SUBGOAL_THEN `i - 1 - 1 = (i - 1) - 1` SUBST1_TAC THENL [REFL_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
   (* let *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vl_lookup_bound973] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
    l4_subst_all973 THEN
    ASM_REWRITE_TAC [LT_0;NOT_SUC;GSYM NOT_SUC;LT;l4_vl_lookup_bound973;
                     injectivity "option";PAIR_EQ] THEN CONJ_TAC THENL
    [MP_TAC (SPECL [`val_e:l4_vexpr961`;`e0:l4_vexpr961`;`d:num`;`0`;`k:num`]
       l4_vliftN_vinst_lo966) THEN REWRITE_TAC [LE_0] THEN SIMP_TAC [];
     MP_TAC (SPECL [`ty:l4_vexpr961`;`e0:l4_vexpr961`;`d:num`;`0`;`k:num`]
       l4_vliftN_vinst_lo966) THEN REWRITE_TAC [LE_0] THEN SIMP_TAC []];
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`i - 1`;`d:num`;`e:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL
    [ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     SUBGOAL_THEN `~(i - 1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let l4_vl_lookup_free_inst_down973 = prove
 (`!fs n e0 d k e ty.
   l4_vl_lookup_free973 fs n (SUC d) = SOME (e, ty) /\
   k <= d ==>
   l4_vl_lookup_free973 fs n d = SOME (l4_vinst961 e e0 k, l4_vinst961 ty e0 k)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_free973;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN
  STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_free973] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   ASM_REWRITE_TAC [l4_vinst961;l4_vinst_var961;injectivity "option";PAIR_EQ] THEN CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC (GSYM l4_vinst_vliftN_le973) THEN ASM_ARITH_TAC];
   STRIP_TAC THEN
   ASM_MESON_TAC [ARITH_RULE `!k d. k <= d ==> k <= SUC d`];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   ASM_REWRITE_TAC [injectivity "option";PAIR_EQ] THEN CONJ_TAC THEN
   MATCH_MP_TAC (GSYM l4_vinst_vliftN_le973) THEN ASM_ARITH_TAC;
   STRIP_TAC THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_s_subst_lam_gen973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!a0 e0 v suf idx k bs'.
     l4_venv_closed966 venv /\
     l4_vtr_expr_s973 env venv ps (L4VLCtx973 (l4_vl_free973 l) suf) v e0 /\
     l4_vhas_type961 venv (LENGTH ps)
       (APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))) e0 a0 /\
     l4_vl_bound_inst_lam973 a0 e0 suf idx k (l4_vl_bound973 l) bs' ==>
     l4_vtr_expr_s973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs')
       (l4_ksubst447 e idx v) (l4_vinst961 e' e0 k))`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`suf:l4_vl_entry973 list`;
                  `idx:num`;`k:num`;`l4_vl_bound973 l`;`bs':l4_vl_entry973 list`]
     l4_vl_bound_inst_lam_lookup973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`i:num`;`0`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [GSYM l4_vl_bvar973;ADD_CLAUSES] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL
   [(* i < idx *)
    MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN
    EXISTS_TAC `l4_vinst961 ty e0 k` THEN
    REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_ctx973;l4_vl_free973] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC [];
     REWRITE_TAC [l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_instN966 THEN
     MAP_EVERY EXISTS_TAC
       [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
        `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
     ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
    COND_CASES_TAC THENL
    [(* i = idx *)
     SUBGOAL_THEN `e = L4VBVar961 k` SUBST_ALL_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
     REWRITE_TAC [l4_vinst961;l4_vinst_var961;LT_REFL] THEN
     MP_TAC (SPECL [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`suf:l4_vl_entry973 list`;
                    `idx:num`;`k:num`;`l4_vl_bound973 l`;`bs':l4_vl_entry973 list`]
       l4_vl_bound_inst_lam_to_lift973) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN `pre:l4_vl_entry973 list` STRIP_ASSUME_TAC) THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 (l4_vl_free973 l) suf`;`v:l4_kexpr447`;`e0:l4_vexpr961`]
       l4_vtr_expr_s_lift_gen973) THEN
     ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973] THEN
     DISCH_THEN (MP_TAC o SPECL [`pre:l4_vl_entry973 list`;`0`;`0`;`APPEND (pre:l4_vl_entry973 list) suf`]) THEN
     ASM_REWRITE_TAC [l4_vl_bound_lift_zero973];
     (* idx < i *)
     SUBGOAL_THEN `idx < i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN
     EXISTS_TAC `l4_vinst961 ty e0 k` THEN
     REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_ctx973;l4_vl_free973] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC [];
      REWRITE_TAC [l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_instN966 THEN
      MAP_EVERY EXISTS_TAC
        [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
         `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
      ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]]]];
   (* FVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `l4_vinst961 ty e0 k` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_fvar973;l4_vl_free973;l4_vl_bound_lams973;l4_vl_bound973] THEN
    SUBGOAL_THEN
      `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)) =
       SUC (LENGTH (l4_vlentries_to_ctx973 bs')) /\
       k <= LENGTH (l4_vlentries_to_ctx973 bs')` STRIP_ASSUME_TAC THENL
    [POP_ASSUM (MP_TAC) THEN SPEC_TAC (`bs':l4_vl_entry973 list`,`bs':l4_vl_entry973 list`) THEN
     SPEC_TAC (`l4_vl_bound973 l`,`bs:l4_vl_entry973 list`) THEN
     SPEC_TAC (`k:num`,`k:num`) THEN SPEC_TAC (`idx:num`,`idx:num`) THEN
     SPEC_TAC (`suf:l4_vl_entry973 list`,`suf:l4_vl_entry973 list`) THEN
     SPEC_TAC (`e0:l4_vexpr961`,`e0:l4_vexpr961`) THEN
     SPEC_TAC (`a0:l4_vexpr961`,`a0:l4_vexpr961`) THEN
     MATCH_MP_TAC l4_vl_bound_inst_lam_INDUCT973 THEN
     REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH] THEN ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC l4_vl_lookup_free_inst_down973 THEN
    ASM_MESON_TAC [l4_vl_fvar973;l4_vl_bound_lams973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_instN966 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
    ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
   (* Sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* App *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vinst961 ty e0 k` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                   `e0:l4_vexpr961`;`a0:l4_vexpr961`;`l4_vl_ctx973 l`;
                   `L4VApp961 f' a'`;`L4VApp961 f' a'`;`ty:l4_vexpr961`;`k:num`;
                   `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
      l4_vis_defeq_instN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vinst961;l4_vl_ctx973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
   (* Lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `l4_vinst961 ty e0 k` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_instN966 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
       `SUC idx`;`SUC k`;`CONS (L4VLLam973 (l4_vinst961 dom' e0 k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_inst_lam_lam973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                   `e0:l4_vexpr961`;`a0:l4_vexpr961`;`l4_vl_ctx973 l`;
                   `L4VLam961 dom' body'`;`L4VLam961 dom' body'`;`ty:l4_vexpr961`;`k:num`;
                   `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
      l4_vis_defeq_instN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vinst961;l4_vl_ctx973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
   (* Pi *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `l4_vinst961 ty e0 k` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_instN966 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
       `SUC idx`;`SUC k`;`CONS (L4VLLam973 (l4_vinst961 dom' e0 k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_inst_lam_lam973];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                   `e0:l4_vexpr961`;`a0:l4_vexpr961`;`l4_vl_ctx973 l`;
                   `L4VForallE961 dom' body'`;`L4VForallE961 dom' body'`;`ty:l4_vexpr961`;`k:num`;
                   `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
      l4_vis_defeq_instN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vinst961;l4_vl_ctx973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
   (* Let *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 ty' e0 k`;`l4_vinst961 val' e0 k`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vis_type_instN966 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_instN966 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vl_ctx973] THEN
    ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
    REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
       `SUC idx`;`k:num`;`CONS (L4VLLet973 (l4_vinst961 ty' e0 k) (l4_vinst961 val' e0 k)) bs'`]) THEN
    REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [l4_vl_inst_lam_let973]];
   (* Proj *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinst961 sv e0 k`;`l4_vinst961 fty e0 k`] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MATCH_MP_TAC l4_vtr_proj_instN973 THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
       `a0:l4_vexpr961`;`l4_vl_ctx973 l`] THEN
    ASM_REWRITE_TAC [l4_vl_ctx973] THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973]];
   (* NatLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447;l4_vinst_nat_lit973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                  `e0:l4_vexpr961`;`a0:l4_vexpr961`;`l4_vl_ctx973 l`;
                  `l4_nat_lit973 m`;`l4_nat_lit973 m`;`l4_vnat_ty973`;`k:num`;
                  `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
     l4_vis_defeq_instN966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vinst_nat_lit973;l4_vnat_ty973;
                    l4_vinst961;l4_vl_ctx973] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
   (* StrLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   SUBGOAL_THEN `l4_vinst961 e' e0 k = e'` (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vinst_tr_str_lit973]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `APPEND (l4_vlentries_to_ctx973 suf) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                  `e0:l4_vexpr961`;`a0:l4_vexpr961`;`l4_vl_ctx973 l`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`l4_vstring_ty973`;`k:num`;
                  `APPEND (l4_vlentries_to_ctx973 bs') (l4_vl_free_ctx973 (l4_vl_free973 l))`]
     l4_vis_defeq_instN966) THEN
   SUBGOAL_THEN `l4_vinst961 e' e0 k = e'` (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vinst_tr_str_lit973]; ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vstring_ty973;l4_vinst961;l4_vl_ctx973] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_vl_bound_inst_lam_to_vctx_instN973];
   (* MData *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vl_ctx_eta973 = prove
 (`!l. L4VLCtx973 (l4_vl_free973 l) (l4_vl_bound973 l) = l`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `l:l4_vl_ctx_rec973` (cases "l4_vl_ctx_rec973")) THEN
  REWRITE_TAC [l4_vl_free973;l4_vl_bound973]);;

let l4_vtr_expr_instantiate_lam973 = prove
 (`!env venv ps l a0 body body' v v'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) a0 /\
   l4_vtr_expr973 env venv ps l v v' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) v' a0 /\
   l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l a0) body body' ==>
   l4_vtr_expr973 env venv ps l (l4_kinst447 body v) (l4_vinst0961 body' v')`,
  REWRITE_TAC [l4_vtr_expr973;l4_kinst447;l4_vinst0961] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 v' a0`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 a0`
    ASSUME_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
  EXISTS_TAC `l4_vinst961 e0' e0 0` THEN CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_lam973 l a0`;`body:l4_kexpr447`;`e0':l4_vexpr961`]
     l4_vtr_expr_s_subst_lam_gen973) THEN
   ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`a0:l4_vexpr961`;`e0:l4_vexpr961`;`v:l4_kexpr447`;`l4_vl_bound973 l`;
      `0`;`0`;`l4_vl_bound973 l`]) THEN
   REWRITE_TAC [l4_vl_ctx_eta973;l4_vl_inst_lam_zero973] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx973];
   UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (l4_vl_push_lam973 l a0)) e0' body'` THEN
   REWRITE_TAC [l4_vl_ctx_push_lam973;l4_vis_defeq_u961] THEN
   DISCH_THEN (X_CHOOSE_TAC `ty:l4_vexpr961`) THEN
   EXISTS_TAC `l4_vinst0961 ty e0` THEN
   REWRITE_TAC [GSYM l4_vinst0961] THEN
   MATCH_MP_TAC l4_vis_defeq_instDF966 THEN EXISTS_TAC `a0:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]]);;

(* Substitution removing a let entry: preserves semantic expression unchanged! *)
let l4_vl_lookup_bound_subst_let973 = prove
 (`!pre suf ty0 val0 j d.
   (j < LENGTH pre ==>
      l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) j d =
      l4_vl_lookup_bound973 (APPEND pre suf) j d) /\
   (j = LENGTH pre ==>
      l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) j d =
      SOME (l4_vliftN961 val0 (d + LENGTH (l4_vlentries_to_ctx973 pre)) 0,
            l4_vliftN961 ty0 (d + LENGTH (l4_vlentries_to_ctx973 pre)) 0)) /\
   (LENGTH pre < j ==>
      l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) j d =
      l4_vl_lookup_bound973 (APPEND pre suf) (j - 1) d)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [APPEND;LENGTH;l4_vlentries_to_ctx973;ADD_CLAUSES;LT;
               l4_vl_lookup_bound973] THENL
  [REPEAT CONJ_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC [ARITH_RULE `!j. 0 < j ==> ~(j = 0)`];
   STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
   REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973;LENGTH] THEN
   REPEAT CONJ_TAC THEN DISCH_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [] THEN TRY ASM_ARITH_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`SUC d`]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`SUC d`]) THEN
    REWRITE_TAC [ARITH_RULE `!d n. SUC d + n = d + SUC n`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(j - 1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`SUC d`]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`d:num`]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`d:num`]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(j - 1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`suf:l4_vl_entry973 list`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`j - 1`;`d:num`]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let l4_vl_ctx_remove_let973 = prove
 (`!l pre suf ty0 val0.
   l4_vl_bound973 l = APPEND pre (CONS (L4VLLet973 ty0 val0) suf) ==>
   l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) (APPEND pre suf)) = l4_vl_ctx973 l /\
   l4_vl_bound_lams973 (L4VLCtx973 (l4_vl_free973 l) (APPEND pre suf)) = l4_vl_bound_lams973 l`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound_lams973;l4_vl_bound973;l4_vl_free973;
                   l4_vlentries_to_ctx_append973;l4_vlentries_to_ctx973]);;

let l4_vtr_expr_s_subst_let_gen973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!ty0 val0 v suf pre.
     l4_venv_sound973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l /\
     l4_vtr_expr_s973 env venv ps (L4VLCtx973 (l4_vl_free973 l) suf) v val0 /\
     l4_vl_bound973 l = APPEND pre (CONS (L4VLLet973 ty0 val0) suf) ==>
     l4_vtr_expr_s973 env venv ps
       (L4VLCtx973 (l4_vl_free973 l) (APPEND pre suf))
       (l4_ksubst447 e (LENGTH pre) v) e')`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MP_TAC (SPECL [`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`;`i:num`;`0`]
     l4_vl_lookup_bound_subst_let973) THEN
   REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973] THEN
     SUBGOAL_THEN
       `l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) i 0 =
        l4_vl_lookup_bound973 (APPEND pre suf) i 0` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC []; ALL_TAC] THEN
     UNDISCH_TAC `l4_vl_bvar973 l i = SOME (e, ty)` THEN
     ASM_REWRITE_TAC [l4_vl_bvar973];
     ASM_REWRITE_TAC []];
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `e = l4_vliftN961 val0 (LENGTH (l4_vlentries_to_ctx973 pre)) 0` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN
        `l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) i 0 =
         SOME (l4_vliftN961 val0 (LENGTH (l4_vlentries_to_ctx973 pre)) 0,
               l4_vliftN961 ty0 (LENGTH (l4_vlentries_to_ctx973 pre)) 0)`
        MP_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
      UNDISCH_TAC `l4_vl_bvar973 l i = SOME (e, ty)` THEN
      REWRITE_TAC [l4_vl_bvar973] THEN
      FIRST_ASSUM (fun th -> if lhs (concl th) = `l4_vl_bound973 l` then REWRITE_TAC [th] else failwith "") THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th;injectivity "option";PAIR_EQ]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 (l4_vl_free973 l) suf`;`v:l4_kexpr447`;`val0:l4_vexpr961`]
       l4_vtr_expr_s_lift_gen973) THEN
     ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973] THEN
     DISCH_THEN (MP_TAC o SPECL [`pre:l4_vl_entry973 list`;`0`;`0`;`APPEND (pre:l4_vl_entry973 list) suf`]) THEN
     REWRITE_TAC [l4_vl_bound_lift_zero973] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966];
     SUBGOAL_THEN `LENGTH (pre:l4_vl_entry973 list) < i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
     CONJ_TAC THENL
     [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973] THEN
      SUBGOAL_THEN
        `l4_vl_lookup_bound973 (APPEND pre (CONS (L4VLLet973 ty0 val0) suf)) i 0 =
         l4_vl_lookup_bound973 (APPEND pre suf) (i - 1) 0` (SUBST1_TAC o SYM) THENL
      [ASM_MESON_TAC []; ALL_TAC] THEN
      UNDISCH_TAC `l4_vl_bvar973 l i = SOME (e, ty)` THEN
      ASM_REWRITE_TAC [l4_vl_bvar973];
      ASM_REWRITE_TAC []]]];
   (* FVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vl_fvar973;l4_vl_free973] THEN
   ASM_MESON_TAC [l4_vl_fvar973];
   (* Sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* App *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL [ASM_MESON_TAC []; ASM_MESON_TAC []; ASM_REWRITE_TAC []];
   (* Lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL
        [`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
         `CONS (L4VLLam973 dom') pre`] th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND;LENGTH] THEN
      DISCH_THEN MATCH_MP_TAC) THEN
    REWRITE_TAC [GSYM l4_vl_push_lam973] THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973];
     ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND]];
    ASM_REWRITE_TAC []];
   (* Pi *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL
        [`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
         `CONS (L4VLLam973 dom') pre`] th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND;LENGTH] THEN
      DISCH_THEN MATCH_MP_TAC) THEN
    REWRITE_TAC [GSYM l4_vl_push_lam973] THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973];
     ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND]];
    ASM_REWRITE_TAC []];
   (* Let *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`val':l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [];
    ASM_MESON_TAC [];
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL
        [`ty0:l4_vexpr961`;`val0:l4_vexpr961`;`v:l4_kexpr447`;`suf:l4_vl_entry973 list`;
         `CONS (L4VLLet973 ty' val') pre`] th) THEN
      REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;APPEND;LENGTH] THEN
      DISCH_THEN MATCH_MP_TAC) THEN
    REWRITE_TAC [GSYM l4_vl_push_let973] THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vl_ctx_wf_push_let973 THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973];
     ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;APPEND]]];
   (* Proj *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`fty:l4_vexpr961`] THEN
   CONJ_TAC THENL [ASM_MESON_TAC []; ASM_REWRITE_TAC []];
   (* NatLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [];
   (* StrLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`pre:l4_vl_entry973 list`;`suf:l4_vl_entry973 list`;
                  `ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_ctx_remove_let973) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [];
   (* MData *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst447] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_instantiate_let973 = prove
 (`!env venv ps l ty0 val0 v body body'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty0 /\
   l4_vtr_expr973 env venv ps l v val0 /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) val0 ty0 /\
   l4_vtr_expr973 env venv ps (l4_vl_push_let973 l ty0 val0) body body' ==>
   l4_vtr_expr973 env venv ps l (l4_kinst447 body v) body'`,
  REWRITE_TAC [l4_vtr_expr973;l4_kinst447] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 val0 ty0`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 ty0`
    ASSUME_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_refl_l961]; ALL_TAC] THEN
  SUBGOAL_THEN `?u. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty0 (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_type961]; ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
       (l4_vl_push_let973 l ty0 val0) (l4_vl_push_let973 l ty0 e0)` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
     l4_vl_ctx_defeq_refl973) THEN
   ASM_REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_REWRITE_TAC [GSYM l4_vl_ctx973;GSYM l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_vis_defeq_symm961];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_vl_push_let973 l ty0 val0`;`body:l4_kexpr447`;`e0':l4_vexpr961`]
    l4_vtr_expr_s_defeq_ctx_transport973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPEC `l4_vl_push_let973 l ty0 e0`) THEN
  ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973] THEN
  DISCH_THEN (X_CHOOSE_THEN `e2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e2:l4_vexpr961` THEN CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_let973 l ty0 e0`;`body:l4_kexpr447`;`e2:l4_vexpr961`]
     l4_vtr_expr_s_subst_let_gen973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`ty0:l4_vexpr961`;`e0:l4_vexpr961`;`v:l4_kexpr447`;
      `l4_vl_bound973 l`;`[]:l4_vl_entry973 list`]) THEN
   ANTS_TAC THENL
   [ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973] THEN
    ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;APPEND;l4_vl_ctx_eta973];
    REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;APPEND;LENGTH;l4_vl_ctx_eta973]];
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vl_ctx_push_let973]) THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `e0':l4_vexpr961` THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973]]);;

(* Syntactic lift / subst_many commutation *)
let l4_klift_0_id973 = prove
 (`!e k. l4_klift447 e 0 k = e`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_klift447;ADD_CLAUSES;COND_ID] THEN SIMP_TAC []);;

let l4_klift_lift_eq973 = prove
 (`!e m n k. l4_klift447 (l4_klift447 e n k) m k = l4_klift447 e (m + n) k`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_klift447] THEN SIMP_TAC [] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC [injectivity "l4_kexpr447"] THEN ASM_ARITH_TAC);;

let l4_ksubst_lift_skip973 = prove
 (`!e idx v. l4_ksubst447 (l4_klift447 e 1 idx) idx v = e`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_klift447;l4_ksubst447] THEN SIMP_TAC [] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC [injectivity "l4_kexpr447"] THEN ASM_ARITH_TAC);;

let l4_ksubst_many_nil973 = prove
 (`!e k. l4_ksubst_many526 e k [] = e`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_many526;LENGTH;LT;SUB_0;COND_ID] THEN
  SIMP_TAC []);;

let l4_klift_lift_gen973 = prove
 (`!e n m k1 k2.
   k1 <= k2 /\ k2 <= n + k1 ==>
   l4_klift447 (l4_klift447 e n k1) m k2 = l4_klift447 e (m + n) k1`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_klift447;injectivity "l4_kexpr447"] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY (REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let l4_ksubst_many_cons973 = prove
 (`!e k v vs.
   l4_ksubst_many526 e k (CONS v vs) =
   l4_ksubst447 (l4_ksubst_many526 e (SUC k) vs) k v`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_many526;l4_ksubst447] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC []] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a < k:num` THEN ASM_REWRITE_TAC [] THENL
  [SUBGOAL_THEN `a < SUC k /\ ~(a = k) /\ ~(k < a)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC [l4_ksubst447]];
   ALL_TAC] THEN
  ASM_CASES_TAC `a = k:num` THENL
  [(* a = k *)
   ASM_REWRITE_TAC [ARITH_RULE `!k. k < SUC k`;SUB_REFL;LENGTH;LT_0;EL;HD;
                    l4_ksubst447;LT_REFL] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_klift_0_id973];
   (* SUC k <= a *)
   SUBGOAL_THEN `~(a < SUC k) /\ a - k = SUC (a - SUC k)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC [LENGTH;LT_SUC;EL;TL] THEN
   ASM_CASES_TAC `a - SUC k < LENGTH (vs:l4_kexpr447 list)` THEN ASM_REWRITE_TAC [] THENL
   [REWRITE_TAC [NOT_SUC] THEN
    MP_TAC (SPECL [`EL (a - SUC k) (vs:l4_kexpr447 list)`;`k:num`;`1`;`0`;`k:num`] l4_klift_lift_gen973) THEN
    ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC [ARITH_RULE `!k. 1 + k = SUC k`]] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_ksubst_lift_skip973] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_klift_0_id973];
    REWRITE_TAC [l4_ksubst447] THEN
    SUBGOAL_THEN `~(a - LENGTH (vs:l4_kexpr447 list) < k) /\
                  ~(a - LENGTH (vs:l4_kexpr447 list) = k) /\
                  (a - LENGTH vs) - 1 = a - SUC (LENGTH vs)` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ASM_REWRITE_TAC []]]]);;

(* Universe level substitution on VTrExprS / VTrExpr *)
let l4_vl_entry_instL973 = new_recursive_definition l4_vl_entry_RECURSION973
 `(l4_vl_entry_instL973 ls (L4VLLam973 ty) = L4VLLam973 (l4_vinstL961 ls ty)) /\
  (l4_vl_entry_instL973 ls (L4VLLet973 ty val_e) =
     L4VLLet973 (l4_vinstL961 ls ty) (l4_vinstL961 ls val_e))`;;

let l4_vl_ctx_instL973 = new_definition
 `l4_vl_ctx_instL973 ls l =
   L4VLCtx973 (MAP (\p. (FST p, l4_vl_entry_instL973 ls (SND p))) (l4_vl_free973 l))
              (MAP (l4_vl_entry_instL973 ls) (l4_vl_bound973 l))`;;

let l4_vlentries_to_ctx_instL973 = prove
 (`!es ls.
   l4_vlentries_to_ctx973 (MAP (l4_vl_entry_instL973 ls) es) =
   MAP (l4_vinstL961 ls) (l4_vlentries_to_ctx973 es)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_vlentries_to_ctx973] THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  ASM_REWRITE_TAC [l4_vl_entry_instL973;l4_vlentries_to_ctx973;MAP]);;

let l4_vl_ctx_instL_ctx973 = prove
 (`!ls l. l4_vl_ctx973 (l4_vl_ctx_instL973 ls l) = MAP (l4_vinstL961 ls) (l4_vl_ctx973 l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_ctx973;l4_vl_ctx_instL973;l4_vl_bound973;l4_vl_free973;
               l4_vl_free_ctx973;MAP_APPEND;l4_vlentries_to_ctx_instL973] THEN
  AP_TERM_TAC THEN REWRITE_TAC [GSYM l4_vlentries_to_ctx_instL973] THEN
  AP_TERM_TAC THEN REWRITE_TAC [GSYM MAP_o;o_DEF;SND]);;

let l4_vl_lookup_bound_instL973 = prove
 (`!es ls i d e ty.
   l4_vl_lookup_bound973 es i d = SOME (e, ty) ==>
   l4_vl_lookup_bound973 (MAP (l4_vl_entry_instL973 ls) es) i d =
   SOME (l4_vinstL961 ls e, l4_vinstL961 ls ty)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [MAP;l4_vl_lookup_bound973;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_entry_instL973;l4_vl_lookup_bound973] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vinstL961;l4_vinstL_vliftN966];
   ASM_MESON_TAC [];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vinstL_vliftN966];
   ASM_MESON_TAC []]);;

let l4_vl_lookup_free_instL973 = prove
 (`!fs ls n d e ty.
   l4_vl_lookup_free973 fs n d = SOME (e, ty) ==>
   l4_vl_lookup_free973 (MAP (\p. (FST p, l4_vl_entry_instL973 ls (SND p))) fs) n d =
   SOME (l4_vinstL961 ls e, l4_vinstL961 ls ty)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [MAP;l4_vl_lookup_free973;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN
  STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_entry_instL973;l4_vl_lookup_free973;FST;SND] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vinstL961;l4_vinstL_vliftN966];
   ASM_MESON_TAC [];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN
   l4_subst_all973 THEN
   REWRITE_TAC [l4_vinstL_vliftN966];
   ASM_MESON_TAC []]);;

let l4_vtr_expr_s_subst_levels973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!ps2 us us'.
     LENGTH us = LENGTH ps /\
     l4_tr_ls967 ps2 us = SOME us' /\
     ALL (l4_vlevel_wf961 (LENGTH ps2)) us' ==>
     l4_vtr_expr_s973 env venv ps2 (l4_vl_ctx_instL973 us' l)
       (l4_ksubst_levels488 ps us e) (l4_vinstL961 us' e'))`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `l4_vinstL961 us' ty` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_bvar973;l4_vl_ctx_instL973;l4_vl_bound973] THEN
    MATCH_MP_TAC l4_vl_lookup_bound_instL973 THEN ASM_REWRITE_TAC [GSYM l4_vl_bvar973];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vhas_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN
    ASM_MESON_TAC [l4_tr_ls_length967]];
   (* FVar *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `l4_vinstL961 us' ty` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_fvar973;l4_vl_ctx_instL973;l4_vl_free973;l4_vl_bound_lams973;
                 l4_vl_bound973;l4_vlentries_to_ctx_instL973;LENGTH_MAP] THEN
    MATCH_MP_TAC l4_vl_lookup_free_instL973 THEN
    ASM_REWRITE_TAC [GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vhas_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN
    ASM_MESON_TAC [l4_tr_ls_length967]];
   (* Sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_tr_l_subst967 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vlevel_inst_wf_any966 THEN ASM_REWRITE_TAC []];
   (* Const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
   ASM_REWRITE_TAC [LENGTH_MAP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_tr_ls_subst967 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [ALL_MAP;GSYM ALL_MEM;o_THM] THEN
    ASM_MESON_TAC [l4_vlevel_inst_wf_any966;l4_tr_ls_length967;ALL_MEM]];
   (* App *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vinstL961 us' ty` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`LENGTH (ps2:l4_name list)`;
                   `us':l4_vlevel961 list`;`l4_vl_ctx973 l`;`L4VApp961 f' a'`;`ty:l4_vexpr961`]
      l4_vhas_type_instL966) THEN
    ASM_REWRITE_TAC [l4_vinstL961] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_tr_ls_length967]];
   (* Lam *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `l4_vinstL961 us' ty` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vis_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN ASM_MESON_TAC [l4_tr_ls_length967];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`ps2:l4_name list`;`us:l4_klevel447 list`;`us':l4_vlevel961 list`] th) THEN
      ASM_REWRITE_TAC [l4_vl_ctx_instL973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;
                       MAP;l4_vl_entry_instL973] THEN
      DISCH_THEN ACCEPT_TAC);
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`LENGTH (ps2:l4_name list)`;
                   `us':l4_vlevel961 list`;`l4_vl_ctx973 l`;`L4VLam961 dom' body'`;`ty:l4_vexpr961`]
      l4_vhas_type_instL966) THEN
    ASM_REWRITE_TAC [l4_vinstL961] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_tr_ls_length967]];
   (* Pi *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `l4_vinstL961 us' ty` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vis_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN ASM_MESON_TAC [l4_tr_ls_length967];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`ps2:l4_name list`;`us:l4_klevel447 list`;`us':l4_vlevel961 list`] th) THEN
      ASM_REWRITE_TAC [l4_vl_ctx_instL973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;
                       MAP;l4_vl_entry_instL973] THEN
      DISCH_THEN ACCEPT_TAC);
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`LENGTH (ps2:l4_name list)`;
                   `us':l4_vlevel961 list`;`l4_vl_ctx973 l`;`L4VForallE961 dom' body'`;`ty:l4_vexpr961`]
      l4_vhas_type_instL966) THEN
    ASM_REWRITE_TAC [l4_vinstL961] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC [l4_tr_ls_length967]];
   (* Let *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 us' ty'`;`l4_vinstL961 us' val'`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vis_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN ASM_MESON_TAC [l4_tr_ls_length967];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN MATCH_MP_TAC l4_vhas_type_instL966 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN ASM_MESON_TAC [l4_tr_ls_length967];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`ps2:l4_name list`;`us:l4_klevel447 list`;`us':l4_vlevel961 list`] th) THEN
      ASM_REWRITE_TAC [l4_vl_ctx_instL973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;
                       MAP;l4_vl_entry_instL973] THEN
      DISCH_THEN ACCEPT_TAC)];
   (* Proj *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 us' sv`;`l4_vinstL961 us' fty`] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
    MATCH_MP_TAC l4_vtr_proj_instL973 THEN
    EXISTS_TAC `LENGTH (ps:l4_name list)` THEN ASM_MESON_TAC [l4_tr_ls_length967]];
   (* NatLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488;l4_vinstL_nat_lit973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`LENGTH (ps2:l4_name list)`;
                  `us':l4_vlevel961 list`;`l4_vl_ctx973 l`;`l4_nat_lit973 m`;`l4_vnat_ty973`]
     l4_vhas_type_instL966) THEN
   ASM_REWRITE_TAC [l4_vinstL_nat_lit973;l4_vnat_ty973;l4_vinstL961;MAP] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_tr_ls_length967];
   (* StrLit *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   SUBGOAL_THEN `l4_vinstL961 us' e' = e'` (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vinstL_tr_str_lit973]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [l4_vl_ctx_instL_ctx973] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`LENGTH (ps2:l4_name list)`;
                  `us':l4_vlevel961 list`;`l4_vl_ctx973 l`;`e':l4_vexpr961`;`l4_vstring_ty973`]
     l4_vhas_type_instL966) THEN
   SUBGOAL_THEN `l4_vinstL961 us' e' = e'` (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vinstL_tr_str_lit973]; ALL_TAC] THEN
   ASM_REWRITE_TAC [l4_vstring_ty973;l4_vinstL961;MAP] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_tr_ls_length967];
   (* MData *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_ksubst_levels488] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_SIMP_TAC []]);;

let l4_vtr_expr_subst_levels973 = prove
 (`!env venv params ps us us' e e'.
   LENGTH us = LENGTH params /\
   l4_tr_ls967 ps us = SOME us' /\
   ALL (l4_vlevel_wf961 (LENGTH ps)) us' /\
   l4_vtr_expr973 env venv params l4_vl_empty973 e e' ==>
   l4_vtr_expr973 env venv ps l4_vl_empty973
     (l4_ksubst_levels488 params us e) (l4_vinstL961 us' e')`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `l4_vinstL961 us' e0` THEN CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`params:l4_name list`;
                  `l4_vl_empty973`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
     l4_vtr_expr_s_subst_levels973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`ps:l4_name list`;`us:l4_klevel447 list`;`us':l4_vlevel961 list`]) THEN
   ASM_REWRITE_TAC [l4_vl_ctx_instL973;l4_vl_empty973;l4_vl_free973;l4_vl_bound973;MAP];
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (params:l4_name list)`;`LENGTH (ps:l4_name list)`;
                  `us':l4_vlevel961 list`;`l4_vl_ctx973 l4_vl_empty973`;`e0:l4_vexpr961`;`e':l4_vexpr961`]
     l4_vis_defeq_u_instL973) THEN
   ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_empty973;l4_vl_free973;l4_vl_bound973;
                    l4_vl_free_ctx973;l4_vlentries_to_ctx973;APPEND;MAP] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_tr_ls_length967]]);;

(* Closed-context weakening: VTrExpr in empty context weakens to any context L! *)
let l4_vctx_liftN_closed_suffix973 = prove
 (`!bs0 g.
   l4_vctx_closed966 bs0 ==>
   l4_vctx_liftN966 (LENGTH g) (LENGTH bs0) bs0 (APPEND bs0 g)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vctx_closed966;LENGTH;APPEND] THENL
  [GEN_TAC THEN
   MP_TAC (SPECL [`LENGTH (g:l4_vexpr961 list)`;`[]:l4_vexpr961 list`;`g:l4_vexpr961 list`]
     l4_vctx_liftN_zero966) THEN
   REWRITE_TAC [APPEND_NIL];
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`LENGTH (g:l4_vexpr961 list)`;`LENGTH (t:l4_vexpr961 list)`;
                  `t:l4_vexpr961 list`;`APPEND (t:l4_vexpr961 list) g`;`h:l4_vexpr961`]
     l4_vctx_liftN_succ966) THEN
   ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966]]);;

let l4_vl_lookup_bound_append_l973 = prove
 (`!bs0 bs i d r.
   l4_vl_lookup_bound973 bs0 i d = SOME r ==>
   l4_vl_lookup_bound973 (APPEND bs0 bs) i d = SOME r`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option";APPEND] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_bound973] THEN
  COND_CASES_TAC THEN SIMP_TAC [] THEN ASM_MESON_TAC []);;

let l4_vctx_liftN_vl_closed_suffix973 = prove
 (`!l l'.
   l4_vl_free973 l = [] /\
   l4_vctx_closed966 (l4_vl_ctx973 l) ==>
   l4_vctx_liftN966 (LENGTH (l4_vl_ctx973 l')) (LENGTH (l4_vl_ctx973 l))
     (l4_vl_ctx973 l)
     (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l'))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l'))) =
     APPEND (l4_vl_ctx973 l) (l4_vl_ctx973 l')`
    (fun th -> REWRITE_TAC [th]) THENL
  [ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                    MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_append973;
                    APPEND_ASSOC];
   MATCH_MP_TAC l4_vctx_liftN_closed_suffix973 THEN ASM_REWRITE_TAC []]);;

let l4_vtr_expr_s_closed_to_any_gen973 = prove
 (`!env venv ps l0 e e'.
   l4_vtr_expr_s973 env venv ps l0 e e' ==>
   (!l.
     l4_venv_closed966 venv /\
     l4_vl_free973 l0 = [] /\
     l4_vctx_closed966 (l4_vl_ctx973 l0) ==>
     l4_vtr_expr_s973 env venv ps
       (L4VLCtx973 (l4_vl_free973 l) (APPEND (l4_vl_bound973 l0) (l4_vl_bound973 l)))
       e e')`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vclosedN961 e (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 ty (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973] THEN
    MATCH_MP_TAC l4_vl_lookup_bound_append_l973 THEN ASM_REWRITE_TAC [GSYM l4_vl_bvar973];
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `e:l4_vexpr961`;`e:l4_vexpr961`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vclosedN_vliftN_eq966]];
   (* FVar: impossible since vl_free l0 = [] *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_vl_fvar973 l n = SOME (e, ty)` THEN
   ASM_REWRITE_TAC [l4_vl_fvar973;l4_vl_lookup_free973;distinctness "option"];
   (* Sort *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   (* App *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vclosedN961 (L4VApp961 f' a') (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 ty (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VApp961 f' a'`;`L4VApp961 f' a'`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vclosedN_vliftN_eq966]];
   (* Lam *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vclosedN961 dom' (LENGTH (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_type961;l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vclosedN961 (L4VLam961 dom' body') (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 ty (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `dom':l4_vexpr961`;`LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_type_weakN966) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPEC `l':l4_vl_ctx_rec973` th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND;
                   l4_vl_ctx_push_lam973;l4_vctx_closed966] THEN
      DISCH_THEN MATCH_MP_TAC) THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VLam961 dom' body'`;`L4VLam961 dom' body'`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vclosedN_vliftN_eq966]];
   (* Pi *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vclosedN961 dom' (LENGTH (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_type961;l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vclosedN961 (L4VForallE961 dom' body') (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 ty (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `dom':l4_vexpr961`;`LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_type_weakN966) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPEC `l':l4_vl_ctx_rec973` th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;APPEND;
                   l4_vl_ctx_push_lam973;l4_vctx_closed966] THEN
      DISCH_THEN MATCH_MP_TAC) THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VForallE961 dom' body'`;`L4VForallE961 dom' body'`;`ty:l4_vexpr961`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vclosedN_vliftN_eq966]];
   (* Let *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vclosedN961 val' (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 ty' (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`val':l4_vexpr961`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `ty':l4_vexpr961`;`LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_type_weakN966) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966];
    ASM_MESON_TAC [];
    REWRITE_TAC [l4_vhas_type961] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `val':l4_vexpr961`;`val':l4_vexpr961`;`ty':l4_vexpr961`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
      l4_vis_defeq_weakN966) THEN
    ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vclosedN_vliftN_eq966];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPEC `l':l4_vl_ctx_rec973` th) THEN
      REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;APPEND;
                   l4_vl_ctx_push_let973] THEN
      DISCH_THEN MATCH_MP_TAC) THEN ASM_REWRITE_TAC []];
   (* Proj *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vclosedN961 sv (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 pv (LENGTH (l4_vl_ctx973 l)) /\
      l4_vclosedN961 fty (LENGTH (l4_vl_ctx973 l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vtr_proj973;l4_vis_defeq_closedN966;l4_vhas_type961]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`fty:l4_vexpr961`] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                   `l4_vl_ctx973 l`;
                   `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`;
                   `owner:l4_name`;`idx:num`;`sv:l4_vexpr961`;`pv:l4_vexpr961`;`fty:l4_vexpr961`]
      l4_vtr_proj_weakN973) THEN
    ASM_SIMP_TAC [l4_vclosedN_vliftN_eq966]];
   (* NatLit *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `l4_nat_lit973 m`;`l4_nat_lit973 m`;`l4_vnat_ty973`;
                  `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                  `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
     l4_vis_defeq_weakN966) THEN
   ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vliftN_nat_lit973;l4_vnat_ty973;l4_vliftN961];
   (* StrLit *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l:l4_vl_ctx_rec973`;`l':l4_vl_ctx_rec973`] l4_vctx_liftN_vl_closed_suffix973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`l4_vstring_ty973`;
                  `LENGTH (l4_vl_ctx973 l')`;`LENGTH (l4_vl_ctx973 l)`;
                  `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l') (APPEND (l4_vl_bound973 l) (l4_vl_bound973 l')))`]
     l4_vis_defeq_weakN966) THEN
   SUBGOAL_THEN `l4_vliftN961 e' (LENGTH (l4_vl_ctx973 l')) (LENGTH (l4_vl_ctx973 l)) = e'`
     (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vliftN_tr_str_lit973]; ALL_TAC] THEN
   ASM_SIMP_TAC [GSYM l4_vhas_type961;l4_vstring_ty973;l4_vliftN961];
   (* MData *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_closed_to_any973 = prove
 (`!env venv ps l e e'.
   l4_venv_closed966 venv /\
   l4_vtr_expr973 env venv ps l4_vl_empty973 e e' ==>
   l4_vtr_expr973 env venv ps l e e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `e0:l4_vexpr961` THEN CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_empty973`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
     l4_vtr_expr_s_closed_to_any_gen973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `l:l4_vl_ctx_rec973`) THEN
   REWRITE_TAC [l4_vl_empty973;l4_vl_free973;l4_vl_bound973;l4_vl_ctx973;
                l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973;APPEND;
                l4_vctx_closed966;l4_vl_ctx_eta973] THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l4_vl_empty973) e0 e'` THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_empty973;l4_vl_free973;l4_vl_bound973;
                l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973;APPEND;l4_vis_defeq_u961] THEN
   DISCH_THEN (X_CHOOSE_TAC `a:l4_vexpr961`) THEN
   SUBGOAL_THEN `l4_vclosedN961 e0 0 /\ l4_vclosedN961 e' 0 /\ l4_vclosedN961 a 0`
     STRIP_ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`[]:l4_vexpr961 list`;
                   `e0:l4_vexpr961`;`e':l4_vexpr961`;`a:l4_vexpr961`]
      l4_vis_defeq_closedN966) THEN
    ASM_REWRITE_TAC [l4_vctx_closed966;LENGTH];
    ALL_TAC] THEN
   EXISTS_TAC `a:l4_vexpr961` THEN
   MATCH_MP_TAC l4_vis_defeq_weak0966 THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 10. Syntactic Equality, Spine/Apps, Inversions, & l4_tr_e967 Bridge       *)
(* ========================================================================= *)

let l4_vtr_expr_s_expr_eqb973 = prove
 (`!e1 e2 env venv ps l v1 v2.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_kexpr_eqb480 e1 e2 /\
   l4_vtr_expr_s973 env venv ps l e1 v1 /\
   l4_vtr_expr_s973 env venv ps l e2 v2 ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) v1 v2`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* FVar *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* MVar *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* Sort *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* Const *)
   REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480] THEN COND_CASES_TAC THEN
   ASM_MESON_TAC [l4_vtr_expr_s_uniq973];
   (* App *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `ef1:l4_kexpr447`
      (X_CHOOSE_THEN `ea1:l4_kexpr447`
       (X_CHOOSE_THEN `f1':l4_vexpr961`
        (X_CHOOSE_THEN `a1':l4_vexpr961`
         (X_CHOOSE_THEN `ty1:l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `ef2:l4_kexpr447`
      (X_CHOOSE_THEN `ea2:l4_kexpr447`
       (X_CHOOSE_THEN `f2':l4_vexpr961`
        (X_CHOOSE_THEN `a2':l4_vexpr961`
         (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   l4_elim_case_eqs973 THEN
   MATCH_MP_TAC l4_vis_defeq_u_appDF973 THEN
   MAP_EVERY EXISTS_TAC [`ty1:l4_vexpr961`;`ty2:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
   (* Lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n1:l4_name`
      (X_CHOOSE_THEN `bi1:l4_kbinder447`
       (X_CHOOSE_THEN `dom1:l4_kexpr447`
        (X_CHOOSE_THEN `body1:l4_kexpr447`
         (X_CHOOSE_THEN `dom1':l4_vexpr961`
          (X_CHOOSE_THEN `body1':l4_vexpr961`
           (X_CHOOSE_THEN `ty1:l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n2:l4_name`
      (X_CHOOSE_THEN `bi2:l4_kbinder447`
       (X_CHOOSE_THEN `dom2:l4_kexpr447`
        (X_CHOOSE_THEN `body2:l4_kexpr447`
         (X_CHOOSE_THEN `dom2':l4_vexpr961`
          (X_CHOOSE_THEN `body2':l4_vexpr961`
           (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom1' dom2'`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom1' dom2' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom1'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom2') (l4_vl_push_lam973 l dom1')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_symm973 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   FIRST_ASSUM (fun th ->
     if free_in `l4_vl_push_lam973 l dom2'` (concl th)
     then MP_TAC (MATCH_MP l4_vtr_expr_s_defeq_ctx_transport973 th)
     else failwith "no") THEN
   DISCH_THEN (MP_TAC o SPEC `l4_vl_push_lam973 l dom1'`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body2_tr:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom1' (l4_vl_ctx973 l)) body1' body2_tr`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom1' (l4_vl_ctx973 l)) body1' body2'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `body2_tr:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom1':l4_vexpr961`;`body1':l4_vexpr961`;`ty1:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `cod:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom1' cod` THEN
   MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
   (* Pi *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n1:l4_name`
      (X_CHOOSE_THEN `bi1:l4_kbinder447`
       (X_CHOOSE_THEN `dom1:l4_kexpr447`
        (X_CHOOSE_THEN `body1:l4_kexpr447`
         (X_CHOOSE_THEN `dom1':l4_vexpr961`
          (X_CHOOSE_THEN `body1':l4_vexpr961`
           (X_CHOOSE_THEN `ty1:l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n2:l4_name`
      (X_CHOOSE_THEN `bi2:l4_kbinder447`
       (X_CHOOSE_THEN `dom2:l4_kexpr447`
        (X_CHOOSE_THEN `body2:l4_kexpr447`
         (X_CHOOSE_THEN `dom2':l4_vexpr961`
          (X_CHOOSE_THEN `body2':l4_vexpr961`
           (X_CHOOSE_THEN `ty2:l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom1' dom2'`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom1':l4_vexpr961`;`body1':l4_vexpr961`;`ty1:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o REWRITE_RULE [l4_vis_type961]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom1' dom2' (L4VSort961 u)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom2') (l4_vl_push_lam973 l dom1')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_symm973 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   FIRST_ASSUM (fun th ->
     if free_in `l4_vl_push_lam973 l dom2'` (concl th)
     then MP_TAC (MATCH_MP l4_vtr_expr_s_defeq_ctx_transport973 th)
     else failwith "no") THEN
   DISCH_THEN (MP_TAC o SPEC `l4_vl_push_lam973 l dom1'`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body2_tr:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (CONS dom1' (l4_vl_ctx973 l)) body1' body2'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `body2_tr:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                   l4_vctx_wf966;l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
   (* Let *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n1:l4_name`
      (X_CHOOSE_THEN `ty1:l4_kexpr447`
       (X_CHOOSE_THEN `val1:l4_kexpr447`
        (X_CHOOSE_THEN `body1:l4_kexpr447`
         (X_CHOOSE_THEN `nd1:bool`
          (X_CHOOSE_THEN `ty1':l4_vexpr961`
           (X_CHOOSE_THEN `val1':l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n2:l4_name`
      (X_CHOOSE_THEN `ty2:l4_kexpr447`
       (X_CHOOSE_THEN `val2:l4_kexpr447`
        (X_CHOOSE_THEN `body2:l4_kexpr447`
         (X_CHOOSE_THEN `nd2:bool`
          (X_CHOOSE_THEN `ty2':l4_vexpr961`
           (X_CHOOSE_THEN `val2':l4_vexpr961` STRIP_ASSUME_TAC))))))) THEN
   l4_elim_case_eqs973 THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty1' ty2'`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val1' val2'`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty1' ty2' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty1'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val1' val2' ty1'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_let973 l ty2' val2') (l4_vl_push_let973 l ty1' val1')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_symm973 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
    REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vl_ctx973];
    ALL_TAC] THEN
   FIRST_ASSUM (fun th ->
     if free_in `l4_vl_push_let973 l ty2' val2'` (concl th)
     then MP_TAC (MATCH_MP l4_vtr_expr_s_defeq_ctx_transport973 th)
     else failwith "no") THEN
   DISCH_THEN (MP_TAC o SPEC `l4_vl_push_let973 l ty1' val1'`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973;l4_vl_ctx_push_let973] THEN
   DISCH_THEN (X_CHOOSE_THEN `b2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `b2:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                  l4_vl_ctx_wf_push_let973;l4_vl_ctx_push_let973];
   (* NatLit *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* StrLit *)
   REWRITE_TAC [l4_kexpr_eqb480] THEN MESON_TAC [l4_vtr_expr_s_uniq973];
   (* Proj *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN STRIP_TAC THEN l4_elim_case_eqs973 THEN
   ASM_MESON_TAC [l4_vtr_proj_congr973;l4_vl_ctx_wf_to_vctx_wf973];
   (* MData *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480] THEN STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   STRIP_TAC THEN STRIP_TAC THEN l4_elim_case_eqs973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_expr_eqb973 = prove
 (`!env venv ps l e1 e2 v1 v2.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_kexpr_eqb480 e1 e2 /\
   l4_vtr_expr973 env venv ps l e1 v1 /\
   l4_vtr_expr973 env venv ps l e2 v2 ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) v1 v2`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 e0'`
    ASSUME_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_expr_eqb973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 v2`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `e0':l4_vexpr961` THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `e0:l4_vexpr961` THEN
  ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972]);;

let l4_core_alpha_to_expr_eqb973 = prove
 (`!e1 budget e2. FST (l4_core_alpha538 budget e1 e2) ==> l4_kexpr_eqb480 e1 e2`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF;l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF;l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF;l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF;l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480;TAUT `(if p then q else F) <=> p /\ q`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;l4_kexpr_eqb480] THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_core_alpha_eq973 = prove
 (`!env venv ps l e1 e2 v1 v2.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_core_alpha_eq538 e1 e2 /\
   l4_vtr_expr973 env venv ps l e1 v1 /\
   l4_vtr_expr973 env venv ps l e2 v2 ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) v1 v2`,
  REWRITE_TAC [l4_core_alpha_eq538] THEN
  MESON_TAC [l4_core_alpha_to_expr_eqb973;l4_vtr_expr_expr_eqb973]);;

(* Spine decomposition & kapply_exprs translation *)
let l4_ksplit_app_kapply973 = prove
 (`!e acc.
   l4_kapply_exprs489 (SND (l4_ksplit_app_aux489 e acc))
                      (FST (l4_ksplit_app_aux489 e acc)) =
   l4_kapply_exprs489 acc e`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_ksplit_app_aux489;FST;SND] THEN
  SIMP_TAC [l4_kapply_exprs489]);;

let l4_ksplit_app_reconstruct973 = prove
 (`!e. l4_kapply_exprs489 (SND (l4_ksplit_app489 e)) (FST (l4_ksplit_app489 e)) = e`,
  GEN_TAC THEN REWRITE_TAC [l4_ksplit_app489;l4_ksplit_app_kapply973;l4_kapply_exprs489]);;

let l4_kapply_exprs_append973 = prove
 (`!args1 args2 f.
   l4_kapply_exprs489 (APPEND args1 args2) f =
   l4_kapply_exprs489 args2 (l4_kapply_exprs489 args1 f)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND;l4_kapply_exprs489]);;

let l4_vtr_expr_s_kapply_inv973 = prove
 (`!args env venv ps l f e'.
   l4_vtr_expr_s973 env venv ps l (l4_kapply_exprs489 args f) e' ==>
   ?f' args'.
     l4_vtr_expr_s973 env venv ps l f f' /\
     ALL2 (l4_vtr_expr_s973 env venv ps l) args args' /\
     e' = l4_vapps962 args' f'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_kapply_exprs489] THEN REPEAT STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`[]:l4_vexpr961 list`] THEN
   ASM_REWRITE_TAC [ALL2;l4_vapps962];
   FIRST_X_ASSUM (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`L4KApp447 f h`;`e':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `fa':l4_vexpr961`
     (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KApp447 f h) fa'` THEN
   GEN_REWRITE_TAC LAND_CONV [l4_vtr_expr_s_CASES973] THEN
   REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `f0:l4_kexpr447`
      (X_CHOOSE_THEN `a0:l4_kexpr447`
       (X_CHOOSE_THEN `f':l4_vexpr961`
        (X_CHOOSE_THEN `a':l4_vexpr961`
         (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC))))) THEN
   l4_elim_case_eqs973 THEN
   MAP_EVERY EXISTS_TAC [`f':l4_vexpr961`;`CONS (a':l4_vexpr961) args'`] THEN
   ASM_REWRITE_TAC [ALL2;l4_vapps962]]);;

let l4_vtr_expr_kapply_inv973 = prove
 (`!env venv ps l f args e'.
   l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args f) e' ==>
   ?f' args'.
     l4_vtr_expr_s973 env venv ps l f f' /\
     ALL2 (l4_vtr_expr_s973 env venv ps l) args args' /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_vapps962 args' f') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN MESON_TAC [l4_vtr_expr_s_kapply_inv973]);;

let l4_vtr_expr_kapply973 = prove
 (`!args env venv ps l f f' args' ty.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l f f' /\
   ALL2 (l4_vtr_expr973 env venv ps l) args args' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_vapps962 args' f') ty ==>
   l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args f) (l4_vapps962 args' f')`,
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `args':l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_kapply_exprs489;l4_vapps962] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `args':l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_kapply_exprs489;l4_vapps962] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `?fat. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VApp961 f' h') fat`
    (X_CHOOSE_TAC `fat:l4_vexpr961`) THENL
  [ASM_MESON_TAC [l4_vhas_type_apps_head973;l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KApp447 f h) (L4VApp961 f' h')` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vtr_expr973 env venv ps l f f'` THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l h h'` THEN
   REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `f':l4_vexpr961`;`h':l4_vexpr961`;`fat:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom:l4_vexpr961`
     (X_CHOOSE_THEN `body:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0' f' (L4VForallE961 dom body)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e0 h' dom`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (L4VApp961 e0' e0) (L4VApp961 f' h') (l4_vinst0961 body e0)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VApp961 e0' e0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vinst0961 body e0` THEN
    ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC []];
   ALL_TAC] THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o SPECL
    [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
     `l:l4_vl_ctx_rec973`;`L4KApp447 f h`;`L4VApp961 f' h'`;
     `t':l4_vexpr961 list`;`ty:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC []]);;

(* Syntactic inversions for VTrExpr *)
let l4_vtr_expr_inv_sort973 = prove
 (`!env venv ps l u e'.
   l4_vtr_expr973 env venv ps l (L4KSort447 u) e' ==>
   ?u'. l4_tr_l967 ps u = SOME u' /\
        l4_vlevel_wf961 (LENGTH ps) u' /\
        l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VSort961 u') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_pi973 = prove
 (`!env venv ps l n bi dom body e'.
   l4_vtr_expr973 env venv ps l (L4KPi447 n bi dom body) e' ==>
   ?dom' body' ty.
     l4_vtr_expr_s973 env venv ps l dom dom' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' /\
     l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom') body body' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VForallE961 dom' body') ty /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VForallE961 dom' body') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_lam973 = prove
 (`!env venv ps l n bi dom body e'.
   l4_vtr_expr973 env venv ps l (L4KLam447 n bi dom body) e' ==>
   ?dom' body' ty.
     l4_vtr_expr_s973 env venv ps l dom dom' /\
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' /\
     l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom') body body' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VLam961 dom' body') ty /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VLam961 dom' body') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_const973 = prove
 (`!env venv ps l c us e'.
   l4_vtr_expr973 env venv ps l (L4KConst447 c us) e' ==>
   ?us' ci.
     l4_tr_ls967 ps us = SOME us' /\
     ALL (l4_vlevel_wf961 (LENGTH ps)) us' /\
     l4_venv_lookup_const961 venv c ci /\
     LENGTH us' = l4_vc_uvars961 ci /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VConst961 c us') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_app973 = prove
 (`!env venv ps l f a e'.
   l4_vtr_expr973 env venv ps l (L4KApp447 f a) e' ==>
   ?f' a' ty.
     l4_vtr_expr_s973 env venv ps l f f' /\
     l4_vtr_expr_s973 env venv ps l a a' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VApp961 f' a') ty /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (L4VApp961 f' a') e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

(* Bridge between l4_tr_e967 (infer_soundness967) and l4_vtr_expr_s973 *)
let l4_vl_of_ctx_lams973 = new_recursive_definition list_RECURSION
 `(l4_vl_of_ctx_lams973 [] = []) /\
  (l4_vl_of_ctx_lams973 (CONS ty rest) = CONS (L4VLLam973 ty) (l4_vl_of_ctx_lams973 rest))`;;

let l4_vlentries_to_ctx_of_lams973 = prove
 (`!g. l4_vlentries_to_ctx973 (l4_vl_of_ctx_lams973 g) = g`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [l4_vl_of_ctx_lams973;l4_vlentries_to_ctx973]);;

let l4_vl_lookup_bound_of_lams973 = prove
 (`!g i d e ty.
   l4_vl_lookup_bound973 (l4_vl_of_ctx_lams973 g) i d = SOME (e, ty) ==>
   e = L4VBVar961 (d + i)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_of_ctx_lams973;l4_vl_lookup_bound973;distinctness "option"] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES];
   DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`i - 1`;`SUC d`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let l4_vlookup_to_vl_bound_of_lams973 = prove
 (`!g i ty.
   l4_vlookup961 g i ty ==>
   (!d. l4_vl_lookup_bound973 (l4_vl_of_ctx_lams973 g) i d =
        SOME (L4VBVar961 (d + i), l4_vliftN961 ty d 0))`,
  MATCH_MP_TAC l4_vlookup_INDUCT961 THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_vl_of_ctx_lams973;l4_vl_lookup_bound973;ADD_CLAUSES;l4_vlift961;
                l4_vliftN_add_le973;ARITH_RULE `!d. 1 + d = SUC d`];
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
   REWRITE_TAC [l4_vl_of_ctx_lams973;l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC d`) THEN
   REWRITE_TAC [ARITH_RULE `!d i. SUC d + i = d + SUC i`;l4_vlift961;l4_vliftN_add_le973;
                ARITH_RULE `!d. 1 + d = SUC d`]]);;

let l4_index_of_name_lt973 = prove
 (`!ps n i. l4_index_of_name967 ps n = SOME i ==> i < LENGTH ps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_index_of_name967;distinctness "option";LENGTH] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ARITH_TAC;
   REWRITE_TAC [l4_opt_map_eq_some967] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [LT_SUC] THEN ASM_MESON_TAC []]);;

let l4_tr_l_wf973 = prove
 (`!u ps u'. l4_tr_l967 ps u = SOME u' ==> l4_vlevel_wf961 (LENGTH ps) u'`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN
  REWRITE_TAC [l4_tr_l967;l4_opt_map_eq_some967;l4_opt_map2_eq_some967;
               distinctness "option";injectivity "option"] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN l4_elim_case_eqs973 THEN
  REWRITE_TAC [l4_vlevel_wf961] THEN
  ASM_MESON_TAC [l4_index_of_name_lt973]);;

let l4_tr_ls_wf973 = prove
 (`!us ps us'. l4_tr_ls967 ps us = SOME us' ==> ALL (l4_vlevel_wf961 (LENGTH ps)) us'`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_tr_ls967;l4_opt_map2_eq_some967;injectivity "option"] THEN
  REPEAT STRIP_TAC THEN l4_elim_case_eqs973 THEN
  REWRITE_TAC [ALL] THEN ASM_MESON_TAC [l4_tr_l_wf973]);;

let l4_vtr_expr_s_of_tr_e973 = prove
 (`!e env venv ps g e' ty.
   l4_venv_wf966 venv /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_tr_e967 ps e = SOME e' /\
   l4_vhas_type961 venv (LENGTH ps) g e' ty ==>
   l4_vtr_expr_s973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) e e'`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [(* BVar *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_e967;injectivity "option"] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                  `a:num`;`ty:l4_vexpr961`] l4_vhas_type_bvar_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `bty:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `bty:l4_vexpr961` THEN
   REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_ctx973;l4_vl_free973;
                l4_vl_free_ctx973;MAP;l4_vlentries_to_ctx973;APPEND_NIL;
                l4_vlentries_to_ctx_of_lams973] THEN
   CONJ_TAC THENL
   [MP_TAC (SPECL [`g:l4_vexpr961 list`;`a:num`;`bty:l4_vexpr961`]
      l4_vlookup_to_vl_bound_of_lams973) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [ADD_CLAUSES;l4_vliftN_zero961];
    REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_bvar961 THEN ASM_REWRITE_TAC []];
   (* Sort *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_e967;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [] THEN
   ASM_MESON_TAC [l4_tr_l_wf973];
   (* Const *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_tr_e967;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                  `a0:l4_name`;`x:l4_vlevel961 list`;`ty:l4_vexpr961`]
     l4_vhas_type_const_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
   ASM_REWRITE_TAC [];
   (* App *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                  `x:l4_vexpr961`;`y:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom:l4_vexpr961`
     (X_CHOOSE_THEN `body:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                    MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973] THEN
   ASM_MESON_TAC [];
   (* Lam *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                  `x:l4_vexpr961`;`y:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`)
     (X_CHOOSE_THEN `cod:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                    MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973;
                    l4_vl_push_lam973;GSYM l4_vl_of_ctx_lams973] THEN
   ASM_MESON_TAC [l4_vis_type961;l4_vctx_wf966];
   (* Pi *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN l4_elim_case_eqs973 THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                  `x:l4_vexpr961`;`y:l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o REWRITE_RULE [l4_vis_type961]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                    MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973;
                    l4_vl_push_lam973;GSYM l4_vl_of_ctx_lams973] THEN
   ASM_MESON_TAC [l4_vis_type961;l4_vctx_wf966];
   (* MData *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_s_eq_tr_e973 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!g e1.
     l4_vl_free973 l = [] /\
     l4_vl_bound973 l = l4_vl_of_ctx_lams973 g /\
     l4_tr_e967 ps e = SOME e1 ==>
     e' = e1)`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KBVar447 i) = SOME e1` THEN
   REWRITE_TAC [l4_tr_e967;injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_TAC `l4_vl_bvar973 l i = SOME (e, ty)` THEN
   ASM_REWRITE_TAC [l4_vl_bvar973] THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vl_lookup_bound_of_lams973) THEN
   REWRITE_TAC [ADD_CLAUSES];
   (* Sort *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KSort447 u) = SOME e1` THEN
   ASM_REWRITE_TAC [l4_tr_e967;l4_opt_map967;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC;
   (* Const *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KConst447 c us) = SOME e1` THEN
   ASM_REWRITE_TAC [l4_tr_e967;l4_opt_map967;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC;
   (* App *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KApp447 f a) = SOME e1` THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_MESON_TAC [];
   (* Lam *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KLam447 n bi dom body) = SOME e1` THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `dom' = x:l4_vexpr961` SUBST_ALL_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `body' = y:l4_vexpr961` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `CONS (x:l4_vexpr961) g` THEN
    ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;l4_vl_of_ctx_lams973];
    ASM_REWRITE_TAC []];
   (* Pi *)
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `l4_tr_e967 ps (L4KPi447 n bi dom body) = SOME e1` THEN
   REWRITE_TAC [l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `dom' = x:l4_vexpr961` SUBST_ALL_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `body' = y:l4_vexpr961` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `CONS (x:l4_vexpr961) g` THEN
    ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;l4_vl_of_ctx_lams973];
    ASM_REWRITE_TAC []]]);;

let l4_vtr_ctx_of_tr_bctx_aux973 = prove
 (`!ps bs g.
   l4_tr_bctx967 ps bs g ==>
   (!env venv.
     l4_venv_wf966 venv /\
     l4_vctx_wf966 venv (LENGTH ps) g ==>
     l4_vtr_bound_ctx973 env venv ps [] bs (l4_vl_of_ctx_lams973 g))`,
  MATCH_MP_TAC l4_tr_bctx_INDUCT967 THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vl_of_ctx_lams973;l4_vtr_bound_nil973];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [l4_vl_of_ctx_lams973] THEN
   MATCH_MP_TAC l4_vtr_bound_lam973 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vctx_wf966]) THEN
   ASM_REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                    MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
    MATCH_MP_TAC l4_vtr_expr_s_of_tr_e973 THEN
    ASM_MESON_TAC [l4_vis_type961]]]);;

let l4_vtr_ctx_of_tr_bctx973 = prove
 (`!env venv ps bs g.
   l4_venv_wf966 venv /\
   l4_tr_bctx967 ps bs g /\
   l4_vctx_wf966 venv (LENGTH ps) g ==>
   l4_vtr_ctx973 env venv ps
     (L4KContext532 bs []) (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [l4_vtr_ctx973;l4_kcontext_free532;l4_kcontext_bound532;
               l4_vl_free973;l4_vl_bound973;l4_vtr_free_nil973] THEN
  ASM_MESON_TAC [l4_vtr_ctx_of_tr_bctx_aux973]);;



