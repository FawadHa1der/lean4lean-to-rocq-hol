(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end soundness of the executable HOL Light v3 kernel type checker
   (`kernel_checker597.ml`), `fuel_config965.ml`, and `equiv_manager964.ml`
   against the declarative typing judgment `l4_vis_defeq961` via the complete
   12-constructor translation relation `l4_vtr_expr973` (`verify_expr973.ml`).

   Direct 1-to-1 port of `rocq/VerifyTypeChecker.v`. Zero new axioms. *)

needs "hol/verify_expr973.ml";;
needs "hol/kernel_checker597.ml";;
needs "hol/fuel_config965.ml";;
needs "hol/equiv_manager964.ml";;

(* ========================================================================= *)
(* 1. Checker-Specific Translation Helpers                                   *)
(* ========================================================================= *)

let l4_vis_defeq_is_type974 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vis_type961 env uvars g ty`,
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_strong_thm970;l4_vis_defeq_strong_is_type_ind970;
             l4_vis_defeq_strong_to_defeq970;l4_venv_wf_on_types_strong970;
             l4_vctx_strong_of_wf970]);;

let l4_vhas_type_conv_u974 = prove
 (`!env uvars g e a b.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e a /\
   l4_vis_defeq_u961 env uvars g a b ==>
   l4_vhas_type961 env uvars g e b`,
  REWRITE_TAC [l4_vhas_type961;l4_vis_defeq_u961] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 env uvars g a a (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_is_type974;l4_vis_type961;l4_vhas_type961]; ALL_TAC] THEN
  SUBGOAL_THEN `?v. l4_vis_defeq961 env uvars g (L4VSort961 u) ty (L4VSort961 v)`
    (X_CHOOSE_TAC `v:l4_vlevel961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
   MAP_EVERY EXISTS_TAC [`a:l4_vexpr961`;`a:l4_vexpr961`;`b:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`a:l4_vexpr961`;`u:l4_vlevel961`] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`ty:l4_vexpr961`;`v:l4_vlevel961`] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []);;

let l4_kfirstn_append_left974 = prove
 (`!(xs:A list) ys n. LENGTH xs = n ==> l4_kfirstn494 (APPEND xs ys) n = xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;APPEND] THENL
  [REPEAT STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
   STRUCT_CASES_TAC (ISPEC `ys:A list` list_CASES) THEN
   REWRITE_TAC [l4_kfirstn494];
   REPEAT STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_kfirstn494;NOT_SUC;SUC_SUB1] THEN AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC]);;

let l4_all2_append974 = prove
 (`!(R:A->B->bool) xs1 ys1 xs2 ys2.
   ALL2 R xs1 ys1 /\ ALL2 R xs2 ys2 ==>
   ALL2 R (APPEND xs1 xs2) (APPEND ys1 ys2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys1:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;APPEND] THEN ASM_MESON_TAC []);;

let l4_all2_symm974 = prove
 (`!(R:A->A->bool) xs ys.
   (!x y. R x y ==> R y x) /\ ALL2 R xs ys ==> ALL2 R ys xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:A list` list_CASES) THEN
  REWRITE_TAC [ALL2] THEN ASM_MESON_TAC []);;

let l4_vis_type_weakN_iff974 = prove
 (`!env uvars n k g g' ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g' /\
   l4_vctx_liftN966 n k g g' ==>
   (l4_vis_type961 env uvars g' (l4_vliftN961 ty n k) <=>
    l4_vis_type961 env uvars g ty)`,
  REWRITE_TAC [l4_vis_type961] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`n:num`;`k:num`;`g:l4_vexpr961 list`;
                 `g':l4_vexpr961 list`;`ty:l4_vexpr961`;`L4VSort961 u`]
    l4_vhas_type_weakN_iff972) THEN
  ASM_REWRITE_TAC [l4_vliftN961]);;

let l4_vapps_wf_prefix974 = prove
 (`!env uvars g xs ys f ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (l4_vapps962 (APPEND xs ys) f) ty ==>
   ?t. l4_vhas_type961 env uvars g (l4_vapps962 xs f) t`,
  REWRITE_TAC [l4_vapps_append962] THEN
  MESON_TAC [l4_vhas_type_apps_head973]);;

let l4_vapps_args_wf974 = prove
 (`!env uvars g args f ty.
   l4_venv_wf966 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (l4_vapps962 args f) ty ==>
   ALL (\a. ?at. l4_vhas_type961 env uvars g a at) args`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [ALL;l4_vapps962] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [SUBGOAL_THEN `?ft. l4_vhas_type961 env uvars g (L4VApp961 f h) ft`
     (X_CHOOSE_TAC `ft:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vhas_type_apps_head973]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f:l4_vexpr961`;`h:l4_vexpr961`;`ft:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_MESON_TAC [];
   ASM_MESON_TAC []]);;

let l4_vapps_defeq_congr_l974 = prove
 (`!env uvars g xs ys f1 f2 ty1.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g (l4_vapps962 xs f1) ty1 /\
   l4_vis_defeq_u961 env uvars g f1 f2 /\
   ALL2 (l4_vis_defeq_u961 env uvars g) xs ys ==>
   (?ty2. l4_vhas_type961 env uvars g (l4_vapps962 ys f2) ty2) /\
   l4_vis_defeq_u961 env uvars g (l4_vapps962 xs f1) (l4_vapps962 ys f2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `ys:l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_vapps962] THEN STRIP_TAC THEN
   ASM_MESON_TAC [l4_vis_defeq_u_has_type_r973];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC (ISPEC `ys:l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_vapps962] THEN STRIP_TAC THEN
   SUBGOAL_THEN `?ft1. l4_vhas_type961 env uvars g (L4VApp961 f1 h) ft1`
     (X_CHOOSE_TAC `ft1:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vhas_type_apps_head973]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                  `f1:l4_vexpr961`;`h:l4_vexpr961`;`ft1:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom1:l4_vexpr961`
     (X_CHOOSE_THEN `cod1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g f1 f2 (L4VForallE961 dom1 cod1)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 env uvars g h h' dom1` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 env uvars g (L4VApp961 f1 h) (L4VApp961 f2 h')`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinst0961 cod1 h` THEN
    MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o SPECL
     [`t':l4_vexpr961 list`;`L4VApp961 f1 h`;`L4VApp961 f2 h'`;`ty1:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC []]);;

let l4_distinct_all974 ty =
  let d = distinctness ty in
  CONJ d (ONCE_REWRITE_RULE [EQ_SYM_EQ] d);;

(* get_constant soundness *)
let l4_get_constant_sound974 = prove
 (`!env venv ps l n us d.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_get_constant528 env ps n us = L4KAccept491 d ==>
   ?ci us'.
     l4_kfind_decl493 env n = SOME d /\
     ~(l4_kdecl_kind493 d = L4KDUnsupported493) /\
     (!r. ~(l4_kdecl_kind493 d = L4KDUnsafe493 r)) /\
     ~(l4_kdecl_kind493 d = L4KDPartial493) /\
     l4_venv_lookup_const961 venv n ci /\
     l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d) /\
     LENGTH us = l4_vc_uvars961 ci /\
     l4_tr_ls967 ps us = SOME us' /\
     ALL (l4_vlevel_wf961 (LENGTH ps)) us' /\
     l4_vtr_expr973 env venv ps l
       (l4_ksubst_levels488 (l4_kdecl_params493 d) us (l4_kdecl_type493 d))
       (l4_vinstL961 us' (l4_vc_type961 ci)) /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l)
       (L4VConst961 n us') (l4_vinstL961 us' (l4_vc_type961 ci))`,
  let res_dis = l4_distinct_all974 "l4_kresult491" in
  let kind_dis = l4_distinct_all974 "l4_kdecl_kind493" in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [l4_get_constant528]) THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env n` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;res_dis])
    (X_CHOOSE_THEN `a:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (fun th ->
    ASSUME_TAC th THEN REWRITE_TAC [th;res_dis]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [res_dis] THEN
  REWRITE_TAC [l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPECL [`n:l4_name`;`a:l4_kdeclaration493`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`us:l4_klevel447 list`;`ps:l4_name list`;`x:1`] l4_check_levels_tr_ls967) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`us':l4_vlevel961 list`] THEN
  ASM_REWRITE_TAC [kind_dis] THEN
  (CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_closed_to_any973 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
    MATCH_MP_TAC l4_vtr_expr_subst_levels973 THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vhas_type_const973 THEN
    ASM_MESON_TAC [l4_tr_ls_length967]]));;

(* Free-context weakening & bound-closedness *)
let l4_vl_lookup_free_in974 = prove
 (`!fs n d r. l4_vl_lookup_free973 fs n d = SOME r ==> MEM n (MAP FST fs)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_free973;distinctness "option";MAP;MEM] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN
  STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_free973;FST;SND] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC []);;

let l4_vl_lookup_bound_lt974 = prove
 (`!bs i d r. l4_vl_lookup_bound973 bs i d = SOME r ==> i < LENGTH bs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option";LENGTH] THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_bound973] THEN
  COND_CASES_TAC THENL
  [DISCH_TAC THEN ASM_ARITH_TAC;
   DISCH_TAC THEN
   SUBGOAL_THEN `i - 1 < LENGTH (t:l4_vl_entry973 list)` ASSUME_TAC THENL
   [ASM_MESON_TAC []; ASM_ARITH_TAC];
   DISCH_TAC THEN ASM_ARITH_TAC;
   DISCH_TAC THEN
   SUBGOAL_THEN `i - 1 < LENGTH (t:l4_vl_entry973 list)` ASSUME_TAC THENL
   [ASM_MESON_TAC []; ASM_ARITH_TAC]]);;

let l4_vtr_expr_s_bound_closed974 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!m. l4_klift447 e m (LENGTH (l4_vl_bound973 l)) = e)`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN
  REWRITE_TAC [l4_klift447;l4_vl_push_lam973;l4_vl_push_let973;l4_vl_bound973;LENGTH] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY (ASM_SIMP_TAC [] THEN NO_TAC) THEN
  (* BVar *)
  SUBGOAL_THEN `i < LENGTH (l4_vl_bound973 l)` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vl_lookup_bound_lt974;l4_vl_bvar973]; ASM_REWRITE_TAC []]);;

let l4_vtr_expr_bound_closed974 = prove
 (`!env venv ps fs e e' m.
   l4_vtr_expr973 env venv ps (L4VLCtx973 fs []) e e' ==>
   l4_klift447 e m 0 = e`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `L4VLCtx973 fs []`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
    l4_vtr_expr_s_bound_closed974) THEN
  ASM_SIMP_TAC [l4_vl_bound973;LENGTH]);;

let l4_vl_lift_bound_at974 = new_recursive_definition list_RECURSION
 `(l4_vl_lift_bound_at974 n [] = []) /\
  (l4_vl_lift_bound_at974 n (CONS e r) =
    match e with
    | L4VLLam973 a ->
        CONS (L4VLLam973 (l4_vliftN961 a n (LENGTH (l4_vlentries_to_ctx973 r))))
             (l4_vl_lift_bound_at974 n r)
    | L4VLLet973 a v ->
        CONS (L4VLLet973 (l4_vliftN961 a n (LENGTH (l4_vlentries_to_ctx973 r)))
                         (l4_vliftN961 v n (LENGTH (l4_vlentries_to_ctx973 r))))
             (l4_vl_lift_bound_at974 n r))`;;

let l4_vl_lift_bound_at_len974 = prove
 (`!bs n.
   LENGTH (l4_vlentries_to_ctx973 (l4_vl_lift_bound_at974 n bs)) =
   LENGTH (l4_vlentries_to_ctx973 bs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH]);;

let l4_vl_entry_shift974 = new_recursive_definition l4_vl_entry_RECURSION973
 `(l4_vl_entry_shift974 (L4VLLam973 a) = 1) /\
  (l4_vl_entry_shift974 (L4VLLet973 a v) = 0)`;;

let l4_vl_lift_bound_at_vctx_liftN974 = prove
 (`!bs entry base.
   l4_vctx_liftN966 (l4_vl_entry_shift974 entry) (LENGTH (l4_vlentries_to_ctx973 bs))
     (APPEND (l4_vlentries_to_ctx973 bs) base)
     (APPEND (l4_vlentries_to_ctx973 (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) bs))
             (APPEND (l4_vlentries_to_ctx973 [entry]) base))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH;APPEND] THEN
   STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
   REWRITE_TAC [l4_vl_entry_shift974;l4_vlentries_to_ctx973;APPEND] THENL
   [MP_TAC (SPECL [`1`;`base:l4_vexpr961 list`;`[a:l4_vexpr961]`] l4_vctx_liftN_zero966) THEN
    REWRITE_TAC [LENGTH;APPEND;ARITH_RULE `SUC 0 = 1`];
    MP_TAC (SPECL [`0`;`base:l4_vexpr961 list`;`[]:l4_vexpr961 list`] l4_vctx_liftN_zero966) THEN
    REWRITE_TAC [LENGTH;APPEND]];
   STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
   REWRITE_TAC [l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH;APPEND] THENL
   [MATCH_MP_TAC l4_vctx_liftN_succ966 THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`entry:l4_vl_entry973`;`base:l4_vexpr961 list`]) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973];
    FIRST_X_ASSUM (MP_TAC o SPECL [`entry:l4_vl_entry973`;`base:l4_vexpr961 list`]) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973]]]);;

let l4_vl_lift_bound_at_lookup974 = prove
 (`!bs n i d e ty.
   l4_vl_lookup_bound973 bs i d = SOME (e, ty) ==>
   l4_vl_lookup_bound973 (l4_vl_lift_bound_at974 n bs) i d =
   SOME (l4_vliftN961 e n (LENGTH (l4_vlentries_to_ctx973 bs) + d),
         l4_vliftN961 ty n (LENGTH (l4_vlentries_to_ctx973 bs) + d))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lift_bound_at974;l4_vl_lookup_bound973;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973;LENGTH] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961;
                ARITH_RULE `!r d. d < SUC r + d`] THEN
   SUBGOAL_THEN `SUC (LENGTH (l4_vlentries_to_ctx973 t)) + d =
                 SUC d + LENGTH (l4_vlentries_to_ctx973 t)`
     (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC] THEN
   MP_TAC (SPECL [`a:l4_vexpr961`;`n:num`;`SUC d`;
                  `LENGTH (l4_vlentries_to_ctx973 t)`;`0`] l4_vliftN_comm966) THEN
   ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (ACCEPT_TAC o SYM)];
   DISCH_TAC THEN
   SUBGOAL_THEN `SUC (LENGTH (l4_vlentries_to_ctx973 t)) + d =
                 LENGTH (l4_vlentries_to_ctx973 t) + SUC d`
     (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ASM_MESON_TAC []];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   SUBGOAL_THEN `LENGTH (l4_vlentries_to_ctx973 t) + d =
                 d + LENGTH (l4_vlentries_to_ctx973 t)`
     (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC (SPECL [`a1:l4_vexpr961`;`n:num`;`d:num`;
                  `LENGTH (l4_vlentries_to_ctx973 t)`;`0`] l4_vliftN_comm966) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (ACCEPT_TAC o SYM)];
    MP_TAC (SPECL [`a0:l4_vexpr961`;`n:num`;`d:num`;
                  `LENGTH (l4_vlentries_to_ctx973 t)`;`0`] l4_vliftN_comm966) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (ACCEPT_TAC o SYM)]];
   ASM_MESON_TAC []]);;

let l4_vtr_expr_s_weak_free_one_l974 = prove
 (`!env venv ps l e e'.
   l4_vtr_expr_s973 env venv ps l e e' ==>
   (!m entry.
     l4_venv_closed966 venv /\
     ~(MEM m (MAP FST (l4_vl_free973 l))) ==>
     l4_vtr_expr_s973 env venv ps
       (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
                   (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
       e
       (l4_vliftN961 e' (l4_vl_entry_shift974 entry)
         (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))))`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN
   EXISTS_TAC `l4_vliftN961 ty (l4_vl_entry_shift974 entry)
                 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`l4_vl_bound973 l`;`l4_vl_entry_shift974 entry`;`i:num`;`0`;
                   `e:l4_vexpr961`;`ty:l4_vexpr961`] l4_vl_lift_bound_at_lookup974) THEN
    ASM_REWRITE_TAC [GSYM l4_vl_bvar973;ADD_CLAUSES];
    ASM_REWRITE_TAC [l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* FVar *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(n = m:l4_name)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vl_lookup_free_in974;l4_vl_fvar973]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN
   EXISTS_TAC `l4_vliftN961 ty (l4_vl_entry_shift974 entry)
                 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [l4_vl_fvar973;l4_vl_free973;l4_vl_bound_lams973;l4_vl_bound973;
                 l4_vl_lift_bound_at_len974] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    ASM_REWRITE_TAC [l4_vl_entry_shift974;l4_vl_lookup_free973;l4_vliftN_zero961] THENL
    [MP_TAC (SPECL [`l4_vl_free973 l`;`n:l4_name`;
                    `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;
                    `1`;
                    `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;
                    `e:l4_vexpr961`;`ty:l4_vexpr961`] l4_vl_lookup_free_shift_at973) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [LE_REFL;GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973];
      REWRITE_TAC [ARITH_RULE `!k. k + 1 = SUC k`]];
     ASM_REWRITE_TAC [GSYM l4_vl_bound_lams973;GSYM l4_vl_fvar973]];
    ASM_REWRITE_TAC [l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* Sort *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
   ASM_REWRITE_TAC [];
   (* App *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN
   EXISTS_TAC `l4_vliftN961 ty (l4_vl_entry_shift974 entry)
                 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_MESON_TAC [];
    ASM_REWRITE_TAC [l4_vhas_type961;GSYM l4_vliftN961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* Lam *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN
   EXISTS_TAC `l4_vliftN961 ty (l4_vl_entry_shift974 entry)
                 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`m:l4_name`;`entry:l4_vl_entry973`] th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;
                   l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN ACCEPT_TAC);
    ASM_REWRITE_TAC [l4_vhas_type961;GSYM l4_vliftN961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* Pi *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vliftN961] THEN
   MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN
   EXISTS_TAC `l4_vliftN961 ty (l4_vl_entry_shift974 entry)
                 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`m:l4_name`;`entry:l4_vl_entry973`] th) THEN
      REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;
                   l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN ACCEPT_TAC);
    ASM_REWRITE_TAC [l4_vhas_type961;GSYM l4_vliftN961] THEN
    MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* Let *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC
     [`l4_vliftN961 ty' (l4_vl_entry_shift974 entry)
        (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))`;
      `l4_vliftN961 val' (l4_vl_entry_shift974 entry)
        (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_type_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [];
    ASM_REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    FIRST_X_ASSUM (fun th ->
      MP_TAC (SPECL [`m:l4_name`;`entry:l4_vl_entry973`] th) THEN
      REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973;
                   l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN ACCEPT_TAC)];
   (* Proj *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC
     [`l4_vliftN961 sv (l4_vl_entry_shift974 entry)
        (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))`;
      `l4_vliftN961 fty (l4_vl_entry_shift974 entry)
        (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l)))`] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_proj_weakN973 THEN
    EXISTS_TAC `l4_vl_ctx973 l` THEN ASM_REWRITE_TAC []];
   (* NatLit *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m', entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vliftN_nat_lit973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `l4_nat_lit973 m`;`l4_nat_lit973 m`;`l4_vnat_ty973`;
                  `l4_vl_entry_shift974 entry`;
                  `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;
                  `APPEND (l4_vlentries_to_ctx973
                             (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
                          (APPEND (l4_vlentries_to_ctx973 [entry])
                                  (l4_vl_free_ctx973 (l4_vl_free973 l)))`]
     l4_vis_defeq_weakN966) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vliftN_nat_lit973;l4_vnat_ty973;l4_vliftN961]];
   (* StrLit *)
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_bound973 l`;`entry:l4_vl_entry973`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [GSYM l4_vl_ctx973] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx973 (L4VLCtx973 (CONS (m, entry) (l4_vl_free973 l))
        (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l))) =
      APPEND (l4_vlentries_to_ctx973
                (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
             (APPEND (l4_vlentries_to_ctx973 [entry]) (l4_vl_free_ctx973 (l4_vl_free973 l)))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;MAP;SND] THEN
    STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
    REWRITE_TAC [l4_vlentries_to_ctx973;APPEND];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vliftN961 e' (l4_vl_entry_shift974 entry)
        (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) = e'`
     (fun th -> REWRITE_TAC [th]) THENL
   [ASM_MESON_TAC [l4_vliftN_tr_str_lit973]; ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `e':l4_vexpr961`;`e':l4_vexpr961`;`l4_vstring_ty973`;
                  `l4_vl_entry_shift974 entry`;
                  `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;
                  `APPEND (l4_vlentries_to_ctx973
                             (l4_vl_lift_bound_at974 (l4_vl_entry_shift974 entry) (l4_vl_bound973 l)))
                          (APPEND (l4_vlentries_to_ctx973 [entry])
                                  (l4_vl_free_ctx973 (l4_vl_free973 l)))`]
     l4_vis_defeq_weakN966) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    SUBGOAL_THEN
      `l4_vliftN961 e' (l4_vl_entry_shift974 entry)
         (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) = e'`
      (fun th -> REWRITE_TAC [th;l4_vstring_ty973;l4_vliftN961]) THEN
    ASM_MESON_TAC [l4_vliftN_tr_str_lit973]];
   (* MData *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_weak_free_one974 = prove
 (`!env venv ps fs m entry e e'.
   l4_venv_closed966 venv /\
   ~(MEM m (MAP FST fs)) /\
   l4_vtr_expr973 env venv ps (L4VLCtx973 fs []) e e' ==>
   l4_vtr_expr973 env venv ps (L4VLCtx973 (CONS (m, entry) fs) [])
     e (l4_vliftN961 e' (l4_vl_entry_shift974 entry) 0)`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `l4_vliftN961 e0 (l4_vl_entry_shift974 entry) 0` THEN
  CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `L4VLCtx973 fs []`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
     l4_vtr_expr_s_weak_free_one_l974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`m:l4_name`;`entry:l4_vl_entry973`]) THEN
   ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973;l4_vl_lift_bound_at974;
                    l4_vlentries_to_ctx973;LENGTH];
   MATCH_MP_TAC l4_vis_defeq_u_weakN973 THEN
   EXISTS_TAC `l4_vl_ctx973 (L4VLCtx973 fs [])` THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                l4_vlentries_to_ctx973;APPEND;MAP;SND] THEN
   MP_TAC (SPECL [`[]:l4_vl_entry973 list`;`entry:l4_vl_entry973`;
                  `l4_vlentries_to_ctx973 (MAP SND (fs:(l4_name#l4_vl_entry973) list))`]
     l4_vl_lift_bound_at_vctx_liftN974) THEN
   REWRITE_TAC [l4_vl_lift_bound_at974;l4_vlentries_to_ctx973;LENGTH;APPEND] THEN
   STRUCT_CASES_TAC (SPEC `entry:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
   REWRITE_TAC [l4_vlentries_to_ctx973;APPEND]]);;

(* Bound & free context lookup under l4_vtr_ctx973 *)
let l4_vtr_bound_ctx_lookup974 = prove
 (`!env venv ps fs' bs bs'.
   l4_vtr_bound_ctx973 env venv ps fs' bs bs' ==>
   (!i b.
     l4_venv_closed966 venv /\
     l4_nth_error550 bs i = SOME b ==>
     ?e' ty'.
       l4_vl_bvar973 (L4VLCtx973 fs' bs') i = SOME (e', ty') /\
       l4_vtr_expr973 env venv ps (L4VLCtx973 fs' bs')
         (l4_klift447 (l4_kbinding_type532 b) (SUC i) 0) ty' /\
       (!v. l4_kbinding_value532 b = SOME v ==>
         l4_vtr_expr973 env venv ps (L4VLCtx973 fs' bs')
           (l4_klift447 v (SUC i) 0) e'))`,
  MATCH_MP_TAC l4_vtr_bound_ctx_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_nth_error550;distinctness "option"];
   (* Lam *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_nth_error550;injectivity "option"] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`L4VBVar961 0`;`l4_vlift961 ty'`] THEN
    REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_lookup_bound973;
                 l4_kbinding_type532;l4_kbinding_value532;distinctness "option";
                 l4_vlift961;ARITH_RULE `SUC 0 = 1`] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;`ty:l4_kexpr447`;`ty':l4_vexpr961`]
      l4_vtr_expr_lift_lam973) THEN
    ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973;l4_vlift961];
    REWRITE_TAC [l4_nth_error550;NOT_SUC;SUC_SUB1] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`b:l4_kbinding491`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961`
      (X_CHOOSE_THEN `ty0':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`l4_vlift961 e'`;`l4_vlift961 ty0'`] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1;
                  l4_vlift961] THEN
     MP_TAC (SPECL [`bs':l4_vl_entry973 list`;`n:num`;`0`;`1`;`0`;
                    `e':l4_vexpr961`;`ty0':l4_vexpr961`] l4_vl_lookup_bound_shift_at973) THEN
     ANTS_TAC THENL
     [REWRITE_TAC [LE_REFL] THEN ASM_MESON_TAC [l4_vl_bvar973;l4_vl_bound973];
      REWRITE_TAC [ADD_CLAUSES;ARITH_RULE `1 = SUC 0`]];
     SUBGOAL_THEN `SUC (SUC n) = 1 + SUC n` (fun th -> REWRITE_TAC [th]) THENL
     [ARITH_TAC; REWRITE_TAC [GSYM l4_klift_lift_eq973]] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;
                    `l4_klift447 (l4_kbinding_type532 b) (SUC n) 0`;`ty0':l4_vexpr961`]
       l4_vtr_expr_lift_lam973) THEN
     ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973];
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `SUC (SUC n) = 1 + SUC n` (fun th -> REWRITE_TAC [th]) THENL
     [ARITH_TAC; REWRITE_TAC [GSYM l4_klift_lift_eq973]] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;
                    `l4_klift447 v (SUC n) 0`;`e':l4_vexpr961`]
       l4_vtr_expr_lift_lam973) THEN
     ASM_SIMP_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973]]];
   (* Let *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC [l4_nth_error550;injectivity "option"] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`ty':l4_vexpr961`] THEN
    REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_lookup_bound973;l4_vliftN_zero961;
                 l4_kbinding_type532;l4_kbinding_value532;injectivity "option";
                 ARITH_RULE `SUC 0 = 1`] THEN
    CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;`val':l4_vexpr961`;
                    `ty:l4_kexpr447`;`ty':l4_vexpr961`] l4_vtr_expr_lift_let973) THEN
     ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973];
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;`val':l4_vexpr961`;
                    `val_e:l4_kexpr447`;`val':l4_vexpr961`] l4_vtr_expr_lift_let973) THEN
     ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973]];
    REWRITE_TAC [l4_nth_error550;NOT_SUC;SUC_SUB1] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`;`b:l4_kbinding491`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961`
      (X_CHOOSE_THEN `ty0':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty0':l4_vexpr961`] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC [l4_vl_bvar973;l4_vl_bound973;l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1] THEN
     ASM_MESON_TAC [l4_vl_bvar973;l4_vl_bound973];
     SUBGOAL_THEN `SUC (SUC n) = 1 + SUC n` (fun th -> REWRITE_TAC [th]) THENL
     [ARITH_TAC; REWRITE_TAC [GSYM l4_klift_lift_eq973]] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;`val':l4_vexpr961`;
                    `l4_klift447 (l4_kbinding_type532 b) (SUC n) 0`;`ty0':l4_vexpr961`]
       l4_vtr_expr_lift_let973) THEN
     ASM_REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973];
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `SUC (SUC n) = 1 + SUC n` (fun th -> REWRITE_TAC [th]) THENL
     [ARITH_TAC; REWRITE_TAC [GSYM l4_klift_lift_eq973]] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `L4VLCtx973 fs' bs'`;`ty':l4_vexpr961`;`val':l4_vexpr961`;
                    `l4_klift447 v (SUC n) 0`;`e':l4_vexpr961`]
       l4_vtr_expr_lift_let973) THEN
     ASM_SIMP_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_bound973]]]]);;

let l4_vtr_ctx_lookup_bound974 = prove
 (`!env venv ps g l i b.
   l4_venv_closed966 venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_nth_error550 (l4_kcontext_bound532 g) i = SOME b ==>
   ?e' ty'.
     l4_vl_bvar973 l i = SOME (e', ty') /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty' /\
     l4_vtr_expr973 env venv ps l (l4_klift447 (l4_kbinding_type532 b) (SUC i) 0) ty' /\
     (!v. l4_kbinding_value532 b = SOME v ==>
       l4_vtr_expr973 env venv ps l (l4_klift447 v (SUC i) 0) e')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vtr_ctx_to_vl_wf973]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_vl_free973 l`;`l4_kcontext_bound532 g`;`l4_vl_bound973 l`]
    l4_vtr_bound_ctx_lookup974) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vtr_ctx973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`i:num`;`b:l4_kbinding491`]) THEN
  ASM_REWRITE_TAC [l4_vl_ctx_eta973] THEN
  DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961`
    (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vl_lookup_bound_has_type973 THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC []);;

let l4_vtr_free_ctx_lookup974 = prove
 (`!env venv ps fs fs'.
   l4_vtr_free_ctx973 env venv ps fs fs' ==>
   (!n b.
     l4_venv_closed966 venv /\
     l4_kfind_free532 n fs = SOME b ==>
     ?e' ty'.
       l4_vl_lookup_free973 fs' n 0 = SOME (e', ty') /\
       l4_vtr_expr973 env venv ps (L4VLCtx973 fs' []) (l4_kbinding_type532 b) ty' /\
       (!v. l4_kbinding_value532 b = SOME v ==>
         l4_vtr_expr973 env venv ps (L4VLCtx973 fs' []) v e'))`,
  MATCH_MP_TAC l4_vtr_free_ctx_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_kfind_free532;distinctness "option"];
   (* Free Lam *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC [l4_kfind_free532;FST;SND] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`L4VBVar961 0`;`l4_vlift961 ty'`] THEN
    ASM_REWRITE_TAC [l4_vl_lookup_free973;l4_kbinding_type532;l4_kbinding_value532;
                     distinctness "option";l4_vlift961;ARITH_RULE `SUC 0 = 1`] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLam973 ty'`;
                   `ty:l4_kexpr447`;`ty':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
    ASM_REWRITE_TAC [l4_vl_entry_shift974];
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`n':l4_name`;`b:l4_kbinding491`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961`
      (X_CHOOSE_THEN `ty0':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`l4_vlift961 e'`;`l4_vlift961 ty0'`] THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC [l4_vl_lookup_free973;l4_vlift961] THEN
     MP_TAC (SPECL [`fs':(l4_name#l4_vl_entry973) list`;`n':l4_name`;`0`;`1`;`0`;
                    `e':l4_vexpr961`;`ty0':l4_vexpr961`] l4_vl_lookup_free_shift_at973) THEN
     ASM_REWRITE_TAC [LE_REFL;ADD_CLAUSES;ARITH_RULE `1 = SUC 0`];
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLam973 ty'`;
                    `l4_kbinding_type532 b`;`ty0':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_REWRITE_TAC [l4_vl_entry_shift974;l4_vlift961];
     REPEAT STRIP_TAC THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLam973 ty'`;
                    `v:l4_kexpr447`;`e':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_SIMP_TAC [l4_vl_entry_shift974;l4_vlift961]]];
   (* Free Let *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC [l4_kfind_free532;FST;SND] THEN COND_CASES_TAC THENL
   [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`ty':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [l4_vl_lookup_free973;l4_vliftN_zero961;
                     l4_kbinding_type532;l4_kbinding_value532;injectivity "option"] THEN
    CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLet973 ty' val'`;
                    `ty:l4_kexpr447`;`ty':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_REWRITE_TAC [l4_vl_entry_shift974;l4_vliftN_zero961];
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLet973 ty' val'`;
                    `val_e:l4_kexpr447`;`val':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_REWRITE_TAC [l4_vl_entry_shift974;l4_vliftN_zero961]];
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`n':l4_name`;`b:l4_kbinding491`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961`
      (X_CHOOSE_THEN `ty0':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty0':l4_vexpr961`] THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC [l4_vl_lookup_free973];
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLet973 ty' val'`;
                    `l4_kbinding_type532 b`;`ty0':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_REWRITE_TAC [l4_vl_entry_shift974;l4_vliftN_zero961];
     REPEAT STRIP_TAC THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `fs':(l4_name#l4_vl_entry973) list`;`n:l4_name`;`L4VLLet973 ty' val'`;
                    `v:l4_kexpr447`;`e':l4_vexpr961`] l4_vtr_expr_weak_free_one974) THEN
     ASM_SIMP_TAC [l4_vl_entry_shift974;l4_vliftN_zero961]]]]);;

let l4_vtr_ctx_lookup_free974 = prove
 (`!env venv ps g l n b.
   l4_venv_closed966 venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_kfind_free532 n (l4_kcontext_free532 g) = SOME b ==>
   ?e' ty'.
     l4_vl_fvar973 l n = SOME (e', ty') /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty' /\
     l4_vtr_expr973 env venv ps l (l4_kbinding_type532 b) ty' /\
     (!v. l4_kbinding_value532 b = SOME v ==>
       l4_vtr_expr973 env venv ps l v e')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_vtr_ctx_to_vl_wf973]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_kcontext_free532 g`;`l4_vl_free973 l`]
    l4_vtr_free_ctx_lookup974) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vtr_ctx973]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`n:l4_name`;`b:l4_kbinding491`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961`
    (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
    [`l4_vliftN961 e0 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) 0`;
     `l4_vliftN961 ty0 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) 0`] THEN
  SUBGOAL_THEN
    `l4_vl_fvar973 l n =
     SOME (l4_vliftN961 e0 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) 0,
           l4_vliftN961 ty0 (LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))) 0)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vl_fvar973;l4_vl_bound_lams973] THEN
   MP_TAC (SPECL [`l4_vl_free973 l`;`n:l4_name`;`0`;
                  `LENGTH (l4_vlentries_to_ctx973 (l4_vl_bound973 l))`;
                  `0`;`e0:l4_vexpr961`;`ty0:l4_vexpr961`]
     l4_vl_lookup_free_shift_at973) THEN
   ASM_REWRITE_TAC [LE_REFL;ADD_CLAUSES];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC l4_vl_lookup_free_has_type973 THEN EXISTS_TAC `n:l4_name` THEN
   ASM_REWRITE_TAC [];
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `L4VLCtx973 (l4_vl_free973 l) []`;`l4_vl_bound973 l`;
                  `l4_kbinding_type532 b`;`ty0:l4_vexpr961`] l4_vtr_expr_lift_prefix973) THEN
   ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973;APPEND_NIL;l4_vl_ctx_eta973] THEN
   SUBGOAL_THEN `l4_klift447 (l4_kbinding_type532 b) (LENGTH (l4_vl_bound973 l)) 0 =
                 l4_kbinding_type532 b` (fun th -> REWRITE_TAC [th]) THEN
   ASM_MESON_TAC [l4_vtr_expr_bound_closed974];
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) []) v e0`
     ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `L4VLCtx973 (l4_vl_free973 l) []`;`l4_vl_bound973 l`;
                  `v:l4_kexpr447`;`e0:l4_vexpr961`] l4_vtr_expr_lift_prefix973) THEN
   ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973;APPEND_NIL;l4_vl_ctx_eta973] THEN
   SUBGOAL_THEN `l4_klift447 v (LENGTH (l4_vl_bound973 l)) 0 = v`
     (fun th -> REWRITE_TAC [th]) THEN
   ASM_MESON_TAC [l4_vtr_expr_bound_closed974]]);;

(* String literal expansion translation *)
let l4_vtr_expr_s_core_char_list974 = prove
 (`!env venv ps l cs.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_core_string_ready533 env ==>
   l4_vtr_expr_s973 env venv ps l (l4_core_char_list539 cs) (l4_tr_char_list973 cs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\
                l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) /\
                l4_core_nat_ready533 env /\ l4_has_primitives973 env venv`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vl_ctx_wf_to_vctx_wf973;
                  l4_core_string_ready_nat973;l4_ves_prims973];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_venv_lookup_const961 venv l4_core_char_name533
       (L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))) /\
     l4_venv_lookup_const961 venv l4_core_char_of_nat533
       (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973)) /\
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
               (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 2))))))`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `l4_has_primitives973 env venv` THEN
   REWRITE_TAC [l4_has_primitives973] THEN STRIP_TAC THEN ASM_SIMP_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr_s973 env venv ps l (L4KConst447 l4_core_char_name533 []) l4_vchar_ty973`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vchar_ty973] THEN MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))` THEN
   ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr_s973 env venv ps l
       (L4KConst447 l4_core_char_of_nat533 []) (L4VConst961 l4_core_char_of_nat533 [])`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vchar_ty973)` THEN
   ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr_s973 env venv ps l
       (L4KConst447 (L4String l4_core_list_name539 [110;105;108]) [L4KZero447])
       (L4VConst961 (L4String l4_core_list_name539 [110;105;108]) [L4VLZero961])`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
       (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 0)))` THEN
   ASM_REWRITE_TAC [l4_tr_ls967;l4_tr_l967;l4_opt_map2967;l4_opt_map967;
                    ALL;l4_vlevel_wf961;LENGTH;l4_vc_uvars961;ARITH_RULE `SUC 0 = 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr_s973 env venv ps l
       (L4KConst447 (L4String l4_core_list_name539 [99;111;110;115]) [L4KZero447])
       (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLSucc961 (L4VLParam961 0)))
       (L4VForallE961 (L4VBVar961 0)
         (L4VForallE961
           (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 1))
           (L4VApp961 (L4VConst961 l4_core_list_name539 [L4VLParam961 0]) (L4VBVar961 2)))))` THEN
   ASM_REWRITE_TAC [l4_tr_ls967;l4_tr_l967;l4_opt_map2967;l4_opt_map967;
                    ALL;l4_vlevel_wf961;LENGTH;l4_vc_uvars961;ARITH_RULE `SUC 0 = 1`];
   ALL_TAC] THEN
  SPEC_TAC (`cs:num list`,`cs:num list`) THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC [l4_core_char_list539;l4_tr_char_list973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vlist_char_ty973` THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `l4_vl_ctx973 l`;`[]:num list`] l4_tr_char_list_has_type973) THEN
   ASM_REWRITE_TAC [l4_tr_char_list973];
   REWRITE_TAC [l4_core_char_list539;l4_kapply_exprs489;l4_tr_char_list973;l4_vapps962] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_tr_char_list973 (CONS h t)) l4_vlist_char_ty973`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_tr_char_list_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [l4_tr_char_list973;l4_vapps962]) THEN
   DISCH_THEN (fun th -> ASSUME_TAC th THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                    `L4VApp961
                       (L4VApp961
                          (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
                          l4_vchar_ty973)
                       (L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h))`;
                    `l4_tr_char_list973 t`;`l4_vlist_char_ty973`]
       l4_vhas_type_app_inv970)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `d1:l4_vexpr961` (X_CHOOSE_THEN `c1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `L4VApp961
                     (L4VConst961 (L4String l4_core_list_name539 [99;111;110;115]) [L4VLZero961])
                     l4_vchar_ty973`;
                  `L4VApp961 (L4VConst961 l4_core_char_of_nat533 []) (l4_nat_lit973 h)`;
                  `L4VForallE961 d1 c1`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `d2:l4_vexpr961` (X_CHOOSE_THEN `c2:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vlist_char_ty973` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `L4VForallE961 d1 c1` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `L4VForallE961 d2 c2` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `d2:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_REWRITE_TAC []]]);;

let l4_vtr_expr_s_core_expand_string974 = prove
 (`!env venv ps l bytes expanded s'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_core_string_ready533 env /\
   l4_core_expand_string539 bytes = L4KAccept491 expanded /\
   l4_tr_str_lit973 bytes = SOME s' ==>
   l4_vtr_expr_s973 env venv ps l expanded s'`,
  let res_dis = l4_distinct_all974 "l4_kresult491" in
  let opt_dis = l4_distinct_all974 "option" in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) s' l4_vstring_ty973`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_tr_str_lit_has_type973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`bytes:num list`] THEN
   ASM_MESON_TAC [l4_ves_prims973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_tr_str_lit973 bytes = SOME s'` THEN
  UNDISCH_TAC `l4_core_expand_string539 bytes = L4KAccept491 expanded` THEN
  REWRITE_TAC [l4_core_expand_string539;l4_tr_str_lit973] THEN
  STRUCT_CASES_TAC (ISPEC `l4_core_utf8_539 bytes` (cases "option")) THEN
  REWRITE_TAC [res_dis;opt_dis;injectivity "l4_kresult491";injectivity "option"] THEN
  REPEAT STRIP_TAC THEN l4_elim_case_eqs973 THEN
  MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vstring_ty973` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
   EXISTS_TAC `L4VConstant961 0 (L4VForallE961 l4_vlist_char_ty973 l4_vstring_ty973)` THEN
   REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_prims973) THEN
   ASM_REWRITE_TAC [l4_has_primitives973] THEN STRIP_TAC THEN ASM_SIMP_TAC [];
   MATCH_MP_TAC l4_vtr_expr_s_core_char_list974 THEN ASM_REWRITE_TAC []]);;

(* Non-occurrence strengthening *)
let l4_vl_lookup_bound_unshift974 = prove
 (`!es j d k e' t'.
   k <= d /\
   l4_vl_lookup_bound973 es j (SUC d) = SOME (e', t') ==>
   ?e t. l4_vl_lookup_bound973 es j d = SOME (e, t) /\
         e' = l4_vliftN961 e 1 k /\ t' = l4_vliftN961 t 1 k`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_bound973;distinctness "option"] THEN
  STRUCT_CASES_TAC (SPEC `h:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_bound973] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   MAP_EVERY EXISTS_TAC [`L4VBVar961 d`;`l4_vliftN961 a (SUC d) 0`] THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961] THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ARITH_TAC];
    MP_TAC (SPECL [`a:l4_vexpr961`;`SUC d`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + SUC d = SUC (SUC d)`])]];
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`j - 1`;`SUC d`;`k:num`;`e':l4_vexpr961`;`t':l4_vexpr961`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC; MESON_TAC []];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 a1 d 0`;`l4_vliftN961 a0 d 0`] THEN
   REWRITE_TAC [] THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`a1:l4_vexpr961`;`d:num`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + d = SUC d`])];
    MP_TAC (SPECL [`a0:l4_vexpr961`;`d:num`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + d = SUC d`])]];
   ASM_MESON_TAC []]);;

let l4_vl_lookup_free_unshift974 = prove
 (`!fs n d k e' t'.
   k <= d /\
   l4_vl_lookup_free973 fs n (SUC d) = SOME (e', t') ==>
   ?e t. l4_vl_lookup_free973 fs n d = SOME (e, t) /\
         e' = l4_vliftN961 e 1 k /\ t' = l4_vliftN961 t 1 k`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vl_lookup_free973;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:l4_name#l4_vl_entry973` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [FST;SND] THEN
  STRUCT_CASES_TAC (SPEC `y:l4_vl_entry973` (cases "l4_vl_entry973")) THEN
  REWRITE_TAC [l4_vl_lookup_free973] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   MAP_EVERY EXISTS_TAC [`L4VBVar961 d`;`l4_vliftN961 a (SUC d) 0`] THEN
   REWRITE_TAC [l4_vliftN961;l4_vlift_var961] THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ARITH_TAC];
    MP_TAC (SPECL [`a:l4_vexpr961`;`SUC d`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + SUC d = SUC (SUC d)`])]];
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`n:l4_name`;`SUC d`;`k:num`;`e':l4_vexpr961`;`t':l4_vexpr961`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC; MESON_TAC []];
   REWRITE_TAC [injectivity "option";PAIR_EQ] THEN STRIP_TAC THEN l4_subst_all973 THEN
   MAP_EVERY EXISTS_TAC [`l4_vliftN961 a1 d 0`;`l4_vliftN961 a0 d 0`] THEN
   REWRITE_TAC [] THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`a1:l4_vexpr961`;`d:num`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + d = SUC d`])];
    MP_TAC (SPECL [`a0:l4_vexpr961`;`d:num`;`1`;`0`;`k:num`] l4_vliftN_vliftN966) THEN
    ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN (fun th -> REWRITE_TAC [th;ARITH_RULE `!d. 1 + d = SUC d`])]];
   ASM_MESON_TAC []]);;

let l4_vl_bound_lift_lookup_inv974 = prove
 (`!ins idx k bs bs'.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   (!a0 i d e' ty'.
     ins = [L4VLLam973 a0] /\
     ~(i = idx) /\
     l4_vl_lookup_bound973 bs' i d = SOME (e', ty') ==>
     ?e ty.
       l4_vl_lookup_bound973 bs (if idx < i then i - 1 else i) d = SOME (e, ty) /\
       e' = l4_vliftN961 e 1 (k + d) /\
       ty' = l4_vliftN961 ty 1 (k + d))`,
  MATCH_MP_TAC l4_vl_bound_lift_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* base *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   UNDISCH_TAC `ins = [L4VLLam973 a0]` THEN DISCH_THEN SUBST_ALL_TAC THEN
   ASM_REWRITE_TAC [APPEND;l4_vl_lookup_bound973] THEN DISCH_TAC THEN
   SUBGOAL_THEN `0 < i` (fun th -> REWRITE_TAC [th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC (SPECL [`bs:l4_vl_entry973 list`;`i - 1`;`d:num`;`0 + d`;`e':l4_vexpr961`;`ty':l4_vexpr961`]
     l4_vl_lookup_bound_unshift974) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC [ADD_CLAUSES;LE_REFL]; MESON_TAC []];
   (* lam *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   UNDISCH_TAC `~(i = SUC idx)` THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [DISCH_TAC THEN
    ASM_REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973;LENGTH;
                     ARITH_RULE `SUC 0 = 1`;injectivity "option";PAIR_EQ] THEN
    STRIP_TAC THEN l4_subst_all973 THEN
    MAP_EVERY EXISTS_TAC [`L4VBVar961 d`;`l4_vliftN961 ty (SUC d) 0`] THEN
    REWRITE_TAC [ARITH_RULE `!idx. ~(SUC idx < 0)`;l4_vl_lookup_bound973;
                 l4_vliftN961;l4_vlift_var961;ARITH_RULE `!k d. d < SUC k + d`] THEN
    SUBGOAL_THEN `SUC k + d = SUC d + k` (fun th -> REWRITE_TAC [th]) THENL
    [ARITH_TAC; ALL_TAC] THEN
    MP_TAC (SPECL [`ty:l4_vexpr961`;`1`;`SUC d`;`k:num`;`0`] l4_vliftN_comm966) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (fun th -> REWRITE_TAC [th])];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a0:l4_vexpr961`;`n:num`;`SUC d`;`e':l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `e:l4_vexpr961`
      (X_CHOOSE_THEN `t:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:l4_vexpr961`;`t:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [ARITH_RULE `!k d. SUC k + d = k + SUC d`;LT_SUC] THEN
    ASM_CASES_TAC `idx < n` THENL
    [POP_ASSUM (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h]) THEN ASSUME_TAC h) THEN
     SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973;SUC_SUB1];
     POP_ASSUM (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h]) THEN ASSUME_TAC h) THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1]]];
   (* let *)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   UNDISCH_TAC `~(i = SUC idx)` THEN
   STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
   [DISCH_TAC THEN
    ASM_REWRITE_TAC [l4_vl_lookup_bound973;l4_vlentries_to_ctx973;LENGTH;
                     ARITH_RULE `SUC 0 = 1`;injectivity "option";PAIR_EQ] THEN
    STRIP_TAC THEN l4_subst_all973 THEN
    MAP_EVERY EXISTS_TAC [`l4_vliftN961 val_e d 0`;`l4_vliftN961 ty d 0`] THEN
    REWRITE_TAC [ARITH_RULE `!idx. ~(SUC idx < 0)`;l4_vl_lookup_bound973] THEN
    SUBGOAL_THEN `k + d = d + k` (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [MP_TAC (SPECL [`val_e:l4_vexpr961`;`1`;`d:num`;`k:num`;`0`] l4_vliftN_comm966) THEN
     ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (fun th -> REWRITE_TAC [th])];
     MP_TAC (SPECL [`ty:l4_vexpr961`;`1`;`d:num`;`k:num`;`0`] l4_vliftN_comm966) THEN
     ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (fun th -> REWRITE_TAC [th])]];
    DISCH_TAC THEN
    REWRITE_TAC [l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a0:l4_vexpr961`;`n:num`;`d:num`;`e':l4_vexpr961`;`ty':l4_vexpr961`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN `e:l4_vexpr961`
      (X_CHOOSE_THEN `t:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:l4_vexpr961`;`t:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [LT_SUC] THEN
    ASM_CASES_TAC `idx < n` THENL
    [POP_ASSUM (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h]) THEN ASSUME_TAC h) THEN
     SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973;SUC_SUB1];
     POP_ASSUM (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h]) THEN ASSUME_TAC h) THEN
     ASM_REWRITE_TAC [l4_vl_lookup_bound973;NOT_SUC;SUC_SUB1]]]]);;

let l4_vl_bound_lift_vctx974 = prove
 (`!ins idx k bs bs' base.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   l4_vctx_liftN966 (LENGTH (l4_vlentries_to_ctx973 ins)) k
     (APPEND (l4_vlentries_to_ctx973 bs) base)
     (APPEND (l4_vlentries_to_ctx973 bs') base)`,
  MESON_TAC [l4_vl_bound_lift_to_vctx_liftN973]);;

let l4_vl_entries_wf_lift_inv974 = prove
 (`!ins idx k bs bs'.
   l4_vl_bound_lift973 ins idx k bs bs' ==>
   (!env uvars base a0.
     ins = [L4VLLam973 a0] /\
     l4_venv_wf966 env /\
     l4_defeq_injectivity972 env /\
     l4_vctx_wf966 env uvars base /\
     l4_vl_entries_wf973 env uvars base bs' ==>
     l4_vl_entries_wf973 env uvars base bs)`,
  let list_dis = l4_distinct_all974 "list" in
  let ent_dis = l4_distinct_all974 "l4_vl_entry973" in
  SUBGOAL_THEN
    `!ins idx k bs bs'.
      l4_vl_bound_lift973 ins idx k bs bs' ==>
      l4_vl_bound_lift973 ins idx k bs bs' /\
      (!env uvars base a0.
        ins = [L4VLLam973 a0] /\
        l4_venv_wf966 env /\
        l4_defeq_injectivity972 env /\
        l4_vctx_wf966 env uvars base /\
        l4_vl_entries_wf973 env uvars base bs' ==>
        l4_vl_entries_wf973 env uvars base bs)`
    (fun th -> MESON_TAC [th]) THEN
  MATCH_MP_TAC l4_vl_bound_lift_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [MATCH_ACCEPT_TAC l4_vl_bound_lift_zero973;
    UNDISCH_TAC `l4_vl_entries_wf973 env uvars base (APPEND ins bs)` THEN
    ASM_REWRITE_TAC [APPEND] THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vl_entries_wf_CASES973] THEN
    REWRITE_TAC [list_dis;injectivity "list";ent_dis;injectivity "l4_vl_entry973"] THEN
    MESON_TAC []];
   REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vl_bound_lift_lam973 THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `ins = [L4VLLam973 a0]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vl_entries_wf_CASES973] THEN
    REWRITE_TAC [list_dis;injectivity "list";ent_dis;injectivity "l4_vl_entry973";
                 l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`] THEN
    REPEAT STRIP_TAC THEN l4_elim_case_eqs973 THEN
    MATCH_MP_TAC l4_vl_entries_wf_lam973 THEN CONJ_TAC THENL
    [ASM_MESON_TAC [];
     MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                    `bs':l4_vl_entry973 list`;`base:l4_vexpr961 list`]
       l4_vl_bound_lift_vctx974) THEN
     ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `l4_vctx_wf966 env uvars (APPEND (l4_vlentries_to_ctx973 bs') base)`
       ASSUME_TAC THENL [ASM_MESON_TAC [l4_vl_entries_wf_to_vctx_wf973]; ALL_TAC] THEN
     ASM_MESON_TAC [l4_vis_type_weakN_iff974]]];
   REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vl_bound_lift_let973 THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `ins = [L4VLLam973 a0]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [l4_vl_entries_wf_CASES973] THEN
    REWRITE_TAC [list_dis;injectivity "list";ent_dis;injectivity "l4_vl_entry973";
                 l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`] THEN
    REPEAT STRIP_TAC THEN l4_elim_case_eqs973 THEN
    MATCH_MP_TAC l4_vl_entries_wf_let973 THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC [];
     MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                    `bs':l4_vl_entry973 list`;`base:l4_vexpr961 list`]
       l4_vl_bound_lift_vctx974) THEN
     ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `l4_vctx_wf966 env uvars (APPEND (l4_vlentries_to_ctx973 bs') base)`
       ASSUME_TAC THENL [ASM_MESON_TAC [l4_vl_entries_wf_to_vctx_wf973]; ALL_TAC] THEN
     ASM_MESON_TAC [l4_vis_type_weakN_iff974];
     MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                    `bs':l4_vl_entry973 list`;`base:l4_vexpr961 list`]
       l4_vl_bound_lift_vctx974) THEN
     ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `l4_vctx_wf966 env uvars (APPEND (l4_vlentries_to_ctx973 bs') base)`
       ASSUME_TAC THENL [ASM_MESON_TAC [l4_vl_entries_wf_to_vctx_wf973]; ALL_TAC] THEN
     ASM_MESON_TAC [l4_vhas_type_weakN_iff972]]]]);;

let l4_kexpr_dis974 = l4_distinct_all974 "l4_kexpr447";;

let l4_vtr_expr_s_CASES_FRESH974 = prove
 (`!a0 a1 a2 a3 a4 a5.
     l4_vtr_expr_s973 a0 a1 a2 a3 a4 a5 <=>
     (?qi ty.
        a4 = L4KBVar447 qi /\
        l4_vl_bvar973 a3 qi = SOME (a5,ty) /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) a5 ty) \/
     (?qn ty.
        a4 = L4KFVar447 qn /\
        l4_vl_fvar973 a3 qn = SOME (a5,ty) /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) a5 ty) \/
     (?qu u'.
        a4 = L4KSort447 qu /\
        a5 = L4VSort961 u' /\
        l4_tr_l967 a2 qu = SOME u' /\
        l4_vlevel_wf961 (LENGTH a2) u') \/
     (?qc qus us' ci.
        a4 = L4KConst447 qc qus /\
        a5 = L4VConst961 qc us' /\
        l4_tr_ls967 a2 qus = SOME us' /\
        ALL (l4_vlevel_wf961 (LENGTH a2)) us' /\
        l4_venv_lookup_const961 a1 qc ci /\
        LENGTH us' = l4_vc_uvars961 ci) \/
     (?qf qa f' a' ty.
        a4 = L4KApp447 qf qa /\
        a5 = L4VApp961 f' a' /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qf f' /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qa a' /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) (L4VApp961 f' a') ty) \/
     (?qn qbi qdom qbody dom' body' ty.
        a4 = L4KLam447 qn qbi qdom qbody /\
        a5 = L4VLam961 dom' body' /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qdom dom' /\
        l4_vis_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) dom' /\
        l4_vtr_expr_s973 a0 a1 a2 (l4_vl_push_lam973 a3 dom') qbody body' /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) (L4VLam961 dom' body') ty) \/
     (?qn qbi qdom qbody dom' body' ty.
        a4 = L4KPi447 qn qbi qdom qbody /\
        a5 = L4VForallE961 dom' body' /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qdom dom' /\
        l4_vis_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) dom' /\
        l4_vtr_expr_s973 a0 a1 a2 (l4_vl_push_lam973 a3 dom') qbody body' /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) (L4VForallE961 dom' body') ty) \/
     (?qn qty qval qbody qnd ty' val'.
        a4 = L4KLet447 qn qty qval qbody qnd /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qty ty' /\
        l4_vis_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) ty' /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qval val' /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) val' ty' /\
        l4_vtr_expr_s973 a0 a1 a2 (l4_vl_push_let973 a3 ty' val') qbody a5) \/
     (?qowner qidx qe sv fty.
        a4 = L4KProj447 qowner qidx qe /\
        l4_vtr_expr_s973 a0 a1 a2 a3 qe sv /\
        l4_vtr_proj973 a0 a1 (LENGTH a2) (l4_vl_ctx973 a3) qowner qidx sv a5 fty) \/
     (?qm.
        a4 = L4KNatLit447 qm /\
        a5 = l4_nat_lit973 qm /\
        l4_core_nat_ready533 a0 /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) (l4_nat_lit973 qm) l4_vnat_ty973) \/
     (?qbytes.
        a4 = L4KStrLit447 qbytes /\
        l4_core_string_ready533 a0 /\
        l4_tr_str_lit973 qbytes = SOME a5 /\
        l4_vhas_type961 a1 (LENGTH a2) (l4_vl_ctx973 a3) a5 l4_vstring_ty973) \/
     (?qe. a4 = L4KMData447 qe /\ l4_vtr_expr_s973 a0 a1 a2 a3 qe a5)`,
  ACCEPT_TAC l4_vtr_expr_s_CASES973);;

let l4_inv_vtr_s974 =
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES_FRESH974]) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  REPEAT STRIP_TAC THEN l4_elim_case_eqs973;;

let l4_vtr_expr_s_no_occurs_subst_aux974 = prove
 (`!e env venv ps l' e' a0 idx k bs any_e.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l' /\
   l4_vl_bound_lift973 [L4VLLam973 a0] idx k bs (l4_vl_bound973 l') /\
   ~l4_core_occurs532 idx e /\
   l4_vtr_expr_s973 env venv ps l' e e' ==>
   ?e0.
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l') (l4_vliftN961 e0 1 k) e' /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l') bs)
       (l4_ksubst447 e idx any_e) e0`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   X_GEN_TAC `i:num` THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e:l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   SUBGOAL_THEN `~(i = idx:num)` ASSUME_TAC THENL
   [UNDISCH_TAC `~l4_core_occurs532 idx (L4KBVar447 i)` THEN
    REWRITE_TAC [l4_core_occurs532];
    ALL_TAC] THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`] l4_vl_bound_lift_lookup_inv974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`a0:l4_vexpr961`;`i:num`;`0`;`e:l4_vexpr961`;`ty:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [GSYM l4_vl_bvar973;ADD_CLAUSES] THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961`
     (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   l4_subst_all973 THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) e0 ty0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    ASM_MESON_TAC [l4_vhas_type_weakN_iff972;l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   EXISTS_TAC `e0:l4_vexpr961` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vliftN961 ty0 1 k` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
    REWRITE_TAC [l4_ksubst447] THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `~(idx < i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty0:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vl_bvar973;l4_vl_bound973];
     SUBGOAL_THEN `idx < i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty0:l4_vexpr961` THEN
     ASM_MESON_TAC [l4_vl_bvar973;l4_vl_bound973]]];
   (* FVar *)
   X_GEN_TAC `n:l4_name` THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e:l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`] l4_vl_bound_lift_lams973) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `!x. x + 1 = SUC x`;
                    ARITH_RULE `SUC 0 = 1`] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`l4_vl_free973 l`;`n:l4_name`;`LENGTH (l4_vlentries_to_ctx973 bs)`;
                  `k:num`;`e:l4_vexpr961`;`ty:l4_vexpr961`] l4_vl_lookup_free_unshift974) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC `l4_vl_fvar973 l n = SOME (e, ty)` THEN
    ASM_REWRITE_TAC [l4_vl_fvar973;l4_vl_bound_lams973];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961`
     (X_CHOOSE_THEN `ty0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   l4_subst_all973 THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) e0 ty0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    ASM_MESON_TAC [l4_vhas_type_weakN_iff972;l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   EXISTS_TAC `e0:l4_vexpr961` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vliftN961 ty0 1 k` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
    REWRITE_TAC [l4_ksubst447] THEN MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN
    EXISTS_TAC `ty0:l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vl_fvar973;l4_vl_free973;l4_vl_bound_lams973;l4_vl_bound973]];
   (* MVar *)
   X_GEN_TAC `n:l4_name` THEN REPEAT STRIP_TAC THEN l4_inv_vtr_s974;
   (* Sort *)
   X_GEN_TAC `u:l4_klevel447` THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   EXISTS_TAC `L4VSort961 u'` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vliftN961;l4_vis_defeq_u961] THEN
    EXISTS_TAC `L4VSort961 (L4VLSucc961 u')` THEN
    MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [l4_vlevel_equiv_refl961];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_ksubst447] THEN
    MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC []];
   (* Const *)
   MAP_EVERY X_GEN_TAC [`c:l4_name`;`us:l4_klevel447 list`] THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   EXISTS_TAC `L4VConst961 c us'` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vliftN961;l4_vis_defeq_u961] THEN
    EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN
    REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_const973 THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_ksubst447] THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
    ASM_REWRITE_TAC []];
   (* App *)
   MAP_EVERY X_GEN_TAC [`f:l4_kexpr447`;`a:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHf") (LABEL_TAC "IHa")) THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532;DE_MORGAN_THM]) THEN
   SUBGOAL_THEN
     `(?f0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 f0 1 k) f' /\
            l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 f idx any_e) f0) /\
      (?a1. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 a1 1 k) a' /\
            l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 a idx any_e) a1)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (L4VLCtx973 (l4_vl_free973 l) bs)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` THEN
    REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                   `l4_vl_bound973 l`] l4_vl_entries_wf_lift_inv974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `a0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_entries_wf_to_vctx_wf973;
                   l4_vl_free_ctx973;APPEND_NIL;l4_vctx_wf966];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `f':l4_vexpr961`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom:l4_vexpr961`
     (X_CHOOSE_THEN `cod:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 f0 1 k) f' (L4VForallE961 dom cod)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 a1 1 k) a' dom` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 (L4VApp961 f0 a1) 1 k) (L4VApp961 f' a')
        (l4_vinst0961 cod (l4_vliftN961 a1 1 k))` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vliftN961] THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
    EXISTS_TAC `dom:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?t0. l4_vhas_type961 venv (LENGTH (ps:l4_name list))
             (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) (L4VApp961 f0 a1) t0`
     (X_CHOOSE_TAC `t0:l4_vexpr961`) THENL
   [SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
         (L4VApp961 f0 a1) (L4VApp961 f0 a1)` MP_TAC THENL
    [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`1`;`k:num`;
                    `APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                    `l4_vl_ctx973 l`;`L4VApp961 f0 a1`;`L4VApp961 f0 a1`]
       l4_vis_defeq_u_weakN_iff972) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
     ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
     REWRITE_TAC [l4_vis_defeq_u961;l4_vhas_type961]];
    ALL_TAC] THEN
   EXISTS_TAC `L4VApp961 f0 a1` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN ASM_MESON_TAC [];
    REWRITE_TAC [l4_ksubst447] THEN
    MP_TAC (SPECL [`[l4_ksubst447 a idx any_e]`;`env:l4_kdeclaration493 list`;
                   `venv:l4_venv961`;`ps:l4_name list`;`L4VLCtx973 (l4_vl_free973 l) bs`;
                   `l4_ksubst447 f idx any_e`;`f0:l4_vexpr961`;`[a1:l4_vexpr961]`;`t0:l4_vexpr961`]
      l4_vtr_expr_kapply973) THEN
    ASM_REWRITE_TAC [ALL2;l4_kapply_exprs489;l4_vapps962]];
   (* Lam *)
   MAP_EVERY X_GEN_TAC [`n:l4_name`;`bi:l4_kbinder447`;`dom:l4_kexpr447`;`body:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHdom") (LABEL_TAC "IHbody")) THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532;DE_MORGAN_THM]) THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (L4VLCtx973 (l4_vl_free973 l) bs)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` THEN
    REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                   `l4_vl_bound973 l`] l4_vl_entries_wf_lift_inv974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `a0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_entries_wf_to_vctx_wf973;
                   l4_vl_free_ctx973;APPEND_NIL;l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?dom0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 dom0 1 k) dom' /\
             l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 dom idx any_e) dom0`
     (X_CHOOSE_THEN `dom0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 dom0 1 k) dom' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 dom0 1 k)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    ASM_MESON_TAC [l4_vis_type_weakN_iff974;l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_lam973 l dom'`;`body:l4_kexpr447`;`body':l4_vexpr961`]
     l4_vtr_expr_s_defeq_ctx_transport973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k)`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `?body0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
                (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
                (l4_vliftN961 body0 1 (SUC k)) body2 /\
              l4_vtr_expr973 env venv ps
                (L4VLCtx973 (l4_vl_free973 l) (CONS (L4VLLam973 dom0) bs))
                (l4_ksubst447 body (SUC idx) any_e) body0`
     (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [USE_THEN "IHbody" (fun th ->
      MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                     `l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k)`;`body2:l4_vexpr961`;
                     `a0:l4_vexpr961`;`SUC idx`;`SUC k`;`CONS (L4VLLam973 dom0) bs`;`any_e:l4_kexpr447`] th) THEN
      ANTS_TAC THENL
      [ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_push_lam973;l4_vl_bound973] THEN
       MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                      `l4_vl_bound973 l`;`dom0:l4_vexpr961`] l4_vl_bound_lift_lam973) THEN
       ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`];
       REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_ctx_push_lam973] THEN
       DISCH_THEN (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `body0:l4_vexpr961` THEN ASM_REWRITE_TAC []]);
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
        (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
        (l4_vliftN961 body0 1 (SUC k)) body'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `body2:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
    ALL_TAC] THEN
   EXISTS_TAC `L4VLam961 dom0 body0` THEN CONJ_TAC THENL
   [UNDISCH_TAC
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
         (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
         (l4_vliftN961 body0 1 (SUC k)) body'` THEN
    REWRITE_TAC [l4_vis_defeq_u961;l4_vliftN961] THEN
    DISCH_THEN (X_CHOOSE_TAC `tb:l4_vexpr961`) THEN
    EXISTS_TAC `L4VForallE961 (l4_vliftN961 dom0 1 k) tb` THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_ksubst447] THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 dom idx any_e) dom0` THEN
    REWRITE_TAC [l4_vtr_expr973] THEN
    DISCH_THEN (X_CHOOSE_THEN `dom0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      `?u0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
              (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0s dom0 (L4VSort961 u0)`
      (X_CHOOSE_TAC `u0:l4_vlevel961`) THENL
    [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0` THEN
     REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `u0:l4_vlevel961`) THEN EXISTS_TAC `u0:l4_vlevel961` THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_type961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0s` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
         (l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0)
         (l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0s)` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`L4VLCtx973 (l4_vl_free973 l) bs`]
       l4_vl_ctx_defeq_refl973) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN
     EXISTS_TAC `u0:l4_vlevel961` THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973;l4_vl_free973;l4_vl_bound973];
     ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0`;
                   `l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0s`;
                   `l4_ksubst447 body (SUC idx) any_e`;`body0:l4_vexpr961`]
      l4_vtr_expr_defeq_ctx973) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973];
     REWRITE_TAC [l4_vtr_expr973;l4_vl_ctx_push_lam973;l4_vis_defeq_u961] THEN
     DISCH_THEN (X_CHOOSE_THEN `b0s:l4_vexpr961`
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `tb0:l4_vexpr961`))) THEN
     EXISTS_TAC `L4VLam961 dom0s b0s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `L4VForallE961 dom0s tb0` THEN
      ASM_REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
      EXISTS_TAC `u0:l4_vlevel961` THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
      EXISTS_TAC `L4VForallE961 dom0s tb0` THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
      EXISTS_TAC `u0:l4_vlevel961` THEN ASM_REWRITE_TAC []]]];
   (* Pi *)
   MAP_EVERY X_GEN_TAC [`n:l4_name`;`bi:l4_kbinder447`;`dom:l4_kexpr447`;`body:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHdom") (LABEL_TAC "IHbody")) THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532;DE_MORGAN_THM]) THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (L4VLCtx973 (l4_vl_free973 l) bs)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` THEN
    REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                   `l4_vl_bound973 l`] l4_vl_entries_wf_lift_inv974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `a0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_entries_wf_to_vctx_wf973;
                   l4_vl_free_ctx973;APPEND_NIL;l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?dom0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 dom0 1 k) dom' /\
             l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 dom idx any_e) dom0`
     (X_CHOOSE_THEN `dom0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_forall_inv972) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o REWRITE_RULE [l4_vis_type961]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 dom0 1 k) dom' (L4VSort961 u)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 dom0 1 k)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    ASM_MESON_TAC [l4_vis_type_weakN_iff974;l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_lam973 l dom'`;`body:l4_kexpr447`;`body':l4_vexpr961`]
     l4_vtr_expr_s_defeq_ctx_transport973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k)`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `?body0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
                (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
                (l4_vliftN961 body0 1 (SUC k)) body2 /\
              l4_vtr_expr973 env venv ps
                (L4VLCtx973 (l4_vl_free973 l) (CONS (L4VLLam973 dom0) bs))
                (l4_ksubst447 body (SUC idx) any_e) body0`
     (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [USE_THEN "IHbody" (fun th ->
      MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                     `l4_vl_push_lam973 l (l4_vliftN961 dom0 1 k)`;`body2:l4_vexpr961`;
                     `a0:l4_vexpr961`;`SUC idx`;`SUC k`;`CONS (L4VLLam973 dom0) bs`;`any_e:l4_kexpr447`] th) THEN
      ANTS_TAC THENL
      [ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_push_lam973;l4_vl_bound973] THEN
       MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                      `l4_vl_bound973 l`;`dom0:l4_vexpr961`] l4_vl_bound_lift_lam973) THEN
       ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`];
       REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_ctx_push_lam973] THEN
       DISCH_THEN (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `body0:l4_vexpr961` THEN ASM_REWRITE_TAC []]);
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
        (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
        (l4_vliftN961 body0 1 (SUC k)) body'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `body2:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l)) body' (L4VSort961 v)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom' (l4_vl_ctx973 l)`] THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vhas_type961;
                   l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vl_ctx_push_lam973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
        (CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l))
        (l4_vliftN961 body0 1 (SUC k)) body' (L4VSort961 v)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966;
                   l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (CONS dom0 (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))) body0 (L4VSort961 v)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`1`;`SUC k`;
                   `CONS dom0 (APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l)))`;
                   `CONS (l4_vliftN961 dom0 1 k) (l4_vl_ctx973 l)`;
                   `body0:l4_vexpr961`;`L4VSort961 v`] l4_vhas_type_weakN_iff972) THEN
    ANTS_TAC THENL
    [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966;
                    l4_vctx_liftN_succ966];
     REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961]];
    ALL_TAC] THEN
   EXISTS_TAC `L4VForallE961 dom0 body0` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961;l4_vliftN961] THEN
    EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
    MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_ksubst447] THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 dom idx any_e) dom0` THEN
    REWRITE_TAC [l4_vtr_expr973] THEN
    DISCH_THEN (X_CHOOSE_THEN `dom0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      `?u0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
              (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0s dom0 (L4VSort961 u0)`
      (X_CHOOSE_TAC `u0:l4_vlevel961`) THENL
    [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0` THEN
     REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `u0:l4_vlevel961`) THEN EXISTS_TAC `u0:l4_vlevel961` THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_type961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) dom0s` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
         (l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0)
         (l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0s)` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`L4VLCtx973 (l4_vl_free973 l) bs`]
       l4_vl_ctx_defeq_refl973) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_lam973 THEN
     EXISTS_TAC `u0:l4_vlevel961` THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973;l4_vl_free973;l4_vl_bound973];
     ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0`;
                   `l4_vl_push_lam973 (L4VLCtx973 (l4_vl_free973 l) bs) dom0s`;
                   `l4_ksubst447 body (SUC idx) any_e`;`body0:l4_vexpr961`]
      l4_vtr_expr_defeq_ctx973) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC [l4_vl_ctx_wf_push_lam973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973];
     REWRITE_TAC [l4_vtr_expr973;l4_vl_ctx_push_lam973] THEN
     DISCH_THEN (X_CHOOSE_THEN `b0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN
       `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
          (CONS dom0s (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))) body0 (L4VSort961 v)`
       ASSUME_TAC THENL
     [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
      MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom0 (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))`] THEN
      ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vhas_type961;
                     l4_vl_ctx_defeq_to_vis_defeq_ctx973;l4_vl_ctx_push_lam973];
      ALL_TAC] THEN
     SUBGOAL_THEN
       `l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
          (CONS dom0s (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))) b0s body0 (L4VSort961 v)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
      ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vctx_wf966;
                     l4_vis_defeq_u_symm972];
      ALL_TAC] THEN
     EXISTS_TAC `L4VForallE961 dom0s b0s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u0 v)` THEN
      ASM_REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
      ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
      REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u0 v)` THEN
      MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC []]]];
   (* Let *)
   MAP_EVERY X_GEN_TAC [`n:l4_name`;`ty:l4_kexpr447`;`val_e:l4_kexpr447`;`body:l4_kexpr447`;`nd:bool`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHty")
     (CONJUNCTS_THEN2 (LABEL_TAC "IHval") (LABEL_TAC "IHbody"))) THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532;DE_MORGAN_THM]) THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (L4VLCtx973 (l4_vl_free973 l) bs)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` THEN
    REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                   `l4_vl_bound973 l`] l4_vl_entries_wf_lift_inv974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `a0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_entries_wf_to_vctx_wf973;
                   l4_vl_free_ctx973;APPEND_NIL;l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(?ty0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 ty0 1 k) ty' /\
             l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 ty idx any_e) ty0) /\
      (?val0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 val0 1 k) val' /\
              l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 val_e idx any_e) val0)`
     STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_MESON_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 ty0 1 k) ty' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty'` THEN
    REWRITE_TAC [l4_vis_type961] THEN STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 val0 1 k) val' ty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 ty0 1 k) /\
      l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 val0 1 k) (l4_vliftN961 ty0 1 k)`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
     REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vis_defeq_refl_l961;l4_vhas_type961]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) ty0 /\
      l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) val0 ty0`
     STRIP_ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
    ASM_MESON_TAC [l4_vis_type_weakN_iff974;l4_vhas_type_weakN_iff972;
                   l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
        (l4_vl_push_let973 l ty' val')
        (l4_vl_push_let973 l (l4_vliftN961 ty0 1 k) (l4_vliftN961 val0 1 k))`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l:l4_vl_ctx_rec973`]
      l4_vl_ctx_defeq_refl973) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_let973 l ty' val'`;`body:l4_kexpr447`;`e':l4_vexpr961`]
     l4_vtr_expr_s_defeq_ctx_transport973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPEC `l4_vl_push_let973 l (l4_vliftN961 ty0 1 k) (l4_vliftN961 val0 1 k)`) THEN
   ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973;l4_vl_ctx_push_let973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `?body0. l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
                (l4_vliftN961 body0 1 k) body2 /\
              l4_vtr_expr973 env venv ps
                (L4VLCtx973 (l4_vl_free973 l) (CONS (L4VLLet973 ty0 val0) bs))
                (l4_ksubst447 body (SUC idx) any_e) body0`
     (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [USE_THEN "IHbody" (fun th ->
      MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                     `l4_vl_push_let973 l (l4_vliftN961 ty0 1 k) (l4_vliftN961 val0 1 k)`;`body2:l4_vexpr961`;
                     `a0:l4_vexpr961`;`SUC idx`;`k:num`;`CONS (L4VLLet973 ty0 val0) bs`;`any_e:l4_kexpr447`] th) THEN
      ANTS_TAC THENL
      [ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973;l4_vl_push_let973;l4_vl_bound973] THEN
       MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;
                      `l4_vl_bound973 l`;`ty0:l4_vexpr961`;`val0:l4_vexpr961`] l4_vl_bound_lift_let973) THEN
       ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`];
       REWRITE_TAC [l4_vl_push_let973;l4_vl_free973;l4_vl_ctx_push_let973] THEN
       DISCH_THEN (X_CHOOSE_THEN `body0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `body0:l4_vexpr961` THEN ASM_REWRITE_TAC []]);
    ALL_TAC] THEN
   EXISTS_TAC `body0:l4_vexpr961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `body2:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
    REWRITE_TAC [l4_ksubst447] THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 ty idx any_e) ty0` THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 val_e idx any_e) val0` THEN
    REWRITE_TAC [l4_vtr_expr973] THEN
    DISCH_THEN (X_CHOOSE_THEN `val0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `ty0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      `?u0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
              (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) ty0s ty0 (L4VSort961 u0)`
      (X_CHOOSE_TAC `u0:l4_vlevel961`) THENL
    [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) ty0` THEN
     REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `u0:l4_vlevel961`) THEN EXISTS_TAC `u0:l4_vlevel961` THEN
     MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_defeq961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) val0s val0 ty0` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_type961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) ty0s /\
       l4_vhas_type961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) val0s ty0s` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [REWRITE_TAC [l4_vis_type961] THEN ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
      REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
      MAP_EVERY EXISTS_TAC [`ty0:l4_vexpr961`;`u0:l4_vlevel961`] THEN
      ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vis_defeq_refl_l961;l4_vhas_type961]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list))
         (l4_vl_push_let973 (L4VLCtx973 (l4_vl_free973 l) bs) ty0 val0)
         (l4_vl_push_let973 (L4VLCtx973 (l4_vl_free973 l) bs) ty0s val0s)` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`L4VLCtx973 (l4_vl_free973 l) bs`]
       l4_vl_ctx_defeq_refl973) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973]; REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vl_entries_defeq_let973 THEN
     EXISTS_TAC `u0:l4_vlevel961` THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vl_ctx973;l4_vl_free973;l4_vl_bound973];
     ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_let973 (L4VLCtx973 (l4_vl_free973 l) bs) ty0 val0`;
                   `l4_vl_push_let973 (L4VLCtx973 (l4_vl_free973 l) bs) ty0s val0s`;
                   `l4_ksubst447 body (SUC idx) any_e`;`body0:l4_vexpr961`]
      l4_vtr_expr_defeq_ctx973) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC [l4_vl_ctx_wf_push_let973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973];
     REWRITE_TAC [l4_vtr_expr973;l4_vl_ctx_push_let973] THEN
     DISCH_THEN (X_CHOOSE_THEN `b0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `b0s:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
     MAP_EVERY EXISTS_TAC [`ty0s:l4_vexpr961`;`val0s:l4_vexpr961`] THEN
     ASM_REWRITE_TAC []]];
   (* NatLit *)
   X_GEN_TAC `m:num` THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   EXISTS_TAC `l4_nat_lit973 m` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vliftN_nat_lit973;l4_vis_defeq_u961] THEN
    EXISTS_TAC `l4_vnat_ty973` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_ksubst447] THEN
    MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973]];
   (* StrLit *)
   X_GEN_TAC `bytes:num list` THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   EXISTS_TAC `e':l4_vexpr961` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `l4_vliftN961 e' 1 k = e'` (fun th -> REWRITE_TAC [th]) THENL
    [ASM_MESON_TAC [l4_vliftN_tr_str_lit973]; ALL_TAC] THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vstring_ty973` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_ksubst447] THEN
    MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_tr_str_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973]];
   (* Proj *)
   MAP_EVERY X_GEN_TAC [`owner:l4_name`;`idx:num`;`e:l4_kexpr447`] THEN
   DISCH_THEN (LABEL_TAC "IHe") THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`pv:l4_vexpr961`;`a0:l4_vexpr961`;
      `idx':num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532]) THEN
   MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx':num`;`k:num`;`bs:l4_vl_entry973 list`;
                  `l4_vl_bound973 l`;`l4_vl_free_ctx973 (l4_vl_free973 l)`]
     l4_vl_bound_lift_vctx974) THEN
   ASM_REWRITE_TAC [l4_vlentries_to_ctx973;LENGTH;ARITH_RULE `SUC 0 = 1`;GSYM l4_vl_ctx973] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (L4VLCtx973 (l4_vl_free973 l) bs)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` THEN
    REWRITE_TAC [l4_vl_ctx_wf973;l4_vl_free973;l4_vl_bound973] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`[L4VLLam973 a0]`;`idx':num`;`k:num`;`bs:l4_vl_entry973 list`;
                   `l4_vl_bound973 l`] l4_vl_entries_wf_lift_inv974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `a0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_entries_wf_to_vctx_wf973;
                   l4_vl_free_ctx973;APPEND_NIL;l4_vctx_wf966];
    ALL_TAC] THEN
   REMOVE_THEN "IHe" (MP_TAC o SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`sv:l4_vexpr961`;
                  `a0:l4_vexpr961`;`idx':num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `sv0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner idx sv pv fty` THEN
   REWRITE_TAC [l4_vtr_proj973] THEN
   DISCH_THEN (X_CHOOSE_THEN `info:l4_kinductive_data493`
     (X_CHOOSE_THEN `ctor:l4_name`
       (X_CHOOSE_THEN `c:l4_kconstructor_data493`
         (X_CHOOSE_THEN `d:l4_kdeclaration493`
           (X_CHOOSE_THEN `us:l4_vlevel961 list`
             (X_CHOOSE_THEN `ps_e:l4_vexpr961 list`
               (X_CHOOSE_THEN `idxs:l4_vexpr961 list` STRIP_ASSUME_TAC))))))) THEN
   UNDISCH_TAC `pv = l4_vproj_expr962 owner idx us ps_e sv` THEN DISCH_THEN SUBST_ALL_TAC THEN
   SUBGOAL_THEN
     `?ta0. l4_vhas_type961 venv (LENGTH (ps:l4_name list))
              (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) sv0 ta0`
     (X_CHOOSE_TAC `ta0:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vtr_expr_has_type973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 sv0 1 k) (l4_vliftN961 ta0 1 k)` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_weakN966 THEN
    EXISTS_TAC `APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l))` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_vhas_type961;
                   l4_vl_ctx973;l4_vl_bound973;l4_vl_free973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 ta0 1 k) (l4_vapps962 (APPEND ps_e idxs) (L4VConst961 owner us))`
     ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 sv0 1 k) sv` THEN
    DISCH_THEN (X_CHOOSE_TAC `ts:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THEN
    SUBGOAL_THEN `?u1. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vliftN961 ta0 1 k) ts (L4VSort961 u1)`
      (X_CHOOSE_TAC `u1:l4_vlevel961`) THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
     MAP_EVERY EXISTS_TAC [`l4_vliftN961 sv0 1 k`;`l4_vliftN961 sv0 1 k`;`l4_vliftN961 sv0 1 k`] THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                    l4_vhas_type961;l4_vis_defeq_refl_l961;l4_vhas_type961];
     ALL_TAC] THEN
    SUBGOAL_THEN `?u2. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ts (l4_vapps962 (APPEND ps_e idxs) (L4VConst961 owner us)) (L4VSort961 u2)`
      (X_CHOOSE_TAC `u2:l4_vlevel961`) THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
     MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`sv:l4_vexpr961`;`sv:l4_vexpr961`] THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                    l4_vhas_type961;l4_vis_defeq_refl_r961];
     ALL_TAC] THEN
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `ts:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u961];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_weakN973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`1`;`k:num`;
      `APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
      `l4_vl_ctx973 l`;`owner:l4_name`;`info:l4_kinductive_data493`;`ta0:l4_vexpr961`;
      `us:l4_vlevel961 list`;`APPEND ps_e idxs:l4_vexpr961 list`]) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `args0:l4_vexpr961 list` STRIP_ASSUME_TAC) THEN
   ABBREV_TAC `ps0 = l4_kfirstn494 (args0:l4_vexpr961 list) (l4_kind_num_params493 info)` THEN
   ABBREV_TAC `idxs0 = l4_skip550 (args0:l4_vexpr961 list) (l4_kind_num_params493 info)` THEN
   SUBGOAL_THEN
     `LENGTH (ps0:l4_vexpr961 list) = l4_kind_num_params493 info /\
      LENGTH (idxs0:l4_vexpr961 list) = l4_kind_num_indices493 info` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (args0:l4_vexpr961 list) = LENGTH (APPEND (ps_e:l4_vexpr961 list) idxs)` THEN
    ASM_REWRITE_TAC [LENGTH_APPEND] THEN DISCH_TAC THEN
    CONJ_TAC THENL
    [EXPAND_TAC "ps0" THEN MATCH_MP_TAC l4_length_firstn973 THEN ASM_ARITH_TAC;
     EXPAND_TAC "idxs0" THEN REWRITE_TAC [l4_length_skip973] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `args0 = APPEND (ps0:l4_vexpr961 list) idxs0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ps0";"idxs0"] THEN
    REWRITE_TAC [l4_firstn_append_skip973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
        (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) sv0
        (l4_vapps962 (APPEND ps0 idxs0) (L4VConst961 owner us))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ta0:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;
                   l4_vl_ctx973;l4_vl_bound973;l4_vl_free973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vapps962 (MAP (\a. l4_vliftN961 a 1 k) (APPEND ps0 idxs0)) (L4VConst961 owner us))
        (l4_vapps962 (APPEND ps_e idxs) (L4VConst961 owner us))` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (l4_vliftN961 ta0 1 k)
         (l4_vapps962 (MAP (\a. l4_vliftN961 a 1 k) (APPEND ps0 idxs0)) (L4VConst961 owner us))`
      ASSUME_TAC THENL
    [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                    `APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                    `ta0:l4_vexpr961`;
                    `l4_vapps962 (APPEND ps0 idxs0) (L4VConst961 owner us)`;
                    `1`;`k:num`;`l4_vl_ctx973 l`]
       l4_vis_defeq_u_weakN973) THEN
     ASM_REWRITE_TAC [l4_vliftN_vapps962;l4_vliftN961] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966];
     ALL_TAC] THEN
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vliftN961 ta0 1 k` THEN
    ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l))
        (MAP (\a. l4_vliftN961 a 1 k) ps0) ps_e` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_inj973) THEN
    ASM_REWRITE_TAC [l4_vind_head_inj973] THEN
    DISCH_THEN (MP_TAC o SPECL
      [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;`owner:l4_name`;
       `info:l4_kinductive_data493`;`info:l4_kinductive_data493`;`us:l4_vlevel961 list`;`us:l4_vlevel961 list`;
       `MAP (\a. l4_vliftN961 a 1 k) (APPEND ps0 idxs0)`;`APPEND ps_e idxs:l4_vexpr961 list`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)) THEN
    REWRITE_TAC [MAP_APPEND] THEN
    DISCH_THEN (MP_TAC o SPEC `l4_kind_num_params493 info` o MATCH_MP l4_all2_firstn973) THEN
    SUBGOAL_THEN
      `l4_kfirstn494 (APPEND (MAP (\a. l4_vliftN961 a 1 k) ps0) (MAP (\a. l4_vliftN961 a 1 k) idxs0))
                     (l4_kind_num_params493 info) = MAP (\a. l4_vliftN961 a 1 k) ps0 /\
       l4_kfirstn494 (APPEND (ps_e:l4_vexpr961 list) idxs) (l4_kind_num_params493 info) = ps_e`
      (fun th -> REWRITE_TAC [th]) THEN
    CONJ_TAC THENL
    [MP_TAC (ISPECL [`MAP (\a. l4_vliftN961 a 1 k) ps0`;`MAP (\a. l4_vliftN961 a 1 k) idxs0`;
                    `l4_kind_num_params493 info`] l4_kfirstn_append_left974) THEN
     ASM_REWRITE_TAC [LENGTH_MAP];
     MP_TAC (ISPECL [`ps_e:l4_vexpr961 list`;`idxs:l4_vexpr961 list`;
                    `l4_kind_num_params493 info`] l4_kfirstn_append_left974) THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(?t_l. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
               (l4_vliftN961 (l4_vproj_expr962 owner idx us ps0 sv0) 1 k) t_l) /\
      l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (l4_vliftN961 (l4_vproj_expr962 owner idx us ps0 sv0) 1 k)
        (l4_vproj_expr962 owner idx us ps_e sv)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (L4VConst961 (l4_proj_const_name962 owner idx) us)
         (L4VConst961 (l4_proj_const_name962 owner idx) us)` ASSUME_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_proj_const973) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MP_TAC o SPECL [`owner:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
                                 `c:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`idx:num`]) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `pci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
     REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinstL961 us (l4_vc_type961 pci)` THEN
     REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_const973 THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l))
         (APPEND ps_e [sv]) (APPEND (MAP (\a. l4_vliftN961 a 1 k) ps0) [l4_vliftN961 sv0 1 k])`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_all2_append974 THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_all2_symm974 THEN ASM_MESON_TAC [l4_vis_defeq_u_symm972];
      REWRITE_TAC [ALL2] THEN ASM_MESON_TAC [l4_vis_defeq_u_symm972]];
     ALL_TAC] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `APPEND ps_e [sv]:l4_vexpr961 list`;
                   `APPEND (MAP (\a. l4_vliftN961 a 1 k) ps0) [l4_vliftN961 sv0 1 k]`;
                   `L4VConst961 (l4_proj_const_name962 owner idx) us`;
                   `L4VConst961 (l4_proj_const_name962 owner idx) us`;`fty:l4_vexpr961`]
      l4_vapps_defeq_congr_l974) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vapps_append962;l4_vapps962;GSYM l4_vproj_expr962] THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
     REWRITE_TAC [l4_vapps_append962;l4_vapps962;l4_vliftN_vapps962;
                  l4_vproj_expr962;l4_vliftN961] THEN
     ASM_MESON_TAC [l4_vis_defeq_u_symm972]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?fty0. l4_vhas_type961 venv (LENGTH (ps:l4_name list))
               (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
               (l4_vproj_expr962 owner idx us ps0 sv0) fty0`
     (X_CHOOSE_TAC `fty0:l4_vexpr961`) THENL
   [SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
         (l4_vproj_expr962 owner idx us ps0 sv0) (l4_vproj_expr962 owner idx us ps0 sv0)`
      MP_TAC THENL
    [REWRITE_TAC [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`1`;`k:num`;
                    `APPEND (l4_vlentries_to_ctx973 bs) (l4_vl_free_ctx973 (l4_vl_free973 l))`;
                    `l4_vl_ctx973 l`;
                    `l4_vproj_expr962 owner idx us ps0 sv0`;
                    `l4_vproj_expr962 owner idx us ps0 sv0`]
       l4_vis_defeq_u_weakN_iff972) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     ASM_MESON_TAC [l4_vis_defeq_u_refl973];
     REWRITE_TAC [l4_vis_defeq_u961;l4_vhas_type961]];
    ALL_TAC] THEN
   EXISTS_TAC `l4_vproj_expr962 owner idx us ps0 sv0` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_ksubst447] THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 e idx' any_e) sv0` THEN
    REWRITE_TAC [l4_vtr_expr973] THEN
    DISCH_THEN (X_CHOOSE_THEN `sv0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)) sv0s
         (l4_vapps962 (APPEND ps0 idxs0) (L4VConst961 owner us))` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `sv0:l4_vexpr961` THEN
     MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
     ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
         (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
         (l4_vproj_expr962 owner idx us ps0 sv0s) (l4_vproj_expr962 owner idx us ps0 sv0)`
      ASSUME_TAC THENL
    [UNDISCH_TAC
       `l4_vhas_type961 venv (LENGTH (ps:l4_name list))
          (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
          (l4_vproj_expr962 owner idx us ps0 sv0) fty0` THEN
     REWRITE_TAC [l4_vproj_expr962] THEN DISCH_TAC THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                    `l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs)`;
                    `l4_vapps962 ps0 (L4VConst961 (l4_proj_const_name962 owner idx) us)`;
                    `sv0:l4_vexpr961`;`fty0:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_ves_wf973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961`
       (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
     REWRITE_TAC [l4_vis_defeq_u961;l4_vproj_expr962] THEN EXISTS_TAC `l4_vinst0961 bp sv0s` THEN
     MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `ap:l4_vexpr961` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC [GSYM l4_vhas_type961];
      MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
      ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vis_defeq_u_symm972]];
     ALL_TAC] THEN
    EXISTS_TAC `l4_vproj_expr962 owner idx us ps0 sv0s` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
     EXISTS_TAC `sv0s:l4_vexpr961` THEN
     UNDISCH_TAC
       `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list))
          (l4_vl_ctx973 (L4VLCtx973 (l4_vl_free973 l) bs))
          (l4_vproj_expr962 owner idx us ps0 sv0s) (l4_vproj_expr962 owner idx us ps0 sv0)` THEN
     REWRITE_TAC [l4_vis_defeq_u961] THEN DISCH_THEN (X_CHOOSE_TAC `tpv:l4_vexpr961`) THEN
     EXISTS_TAC `tpv:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vtr_proj973] THEN
     MAP_EVERY EXISTS_TAC [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
                           `d:l4_kdeclaration493`;`us:l4_vlevel961 list`;
                           `ps0:l4_vexpr961 list`;`idxs0:l4_vexpr961 list`] THEN
     ASM_MESON_TAC [l4_vis_defeq_refl_l961;l4_vhas_type961];
     ASM_REWRITE_TAC []]];
   (* MData *)
   X_GEN_TAC `e:l4_kexpr447` THEN
   DISCH_THEN (LABEL_TAC "IHe") THEN
   MAP_EVERY X_GEN_TAC
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;`a0:l4_vexpr961`;
      `idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`] THEN
   STRIP_TAC THEN l4_inv_vtr_s974 THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_core_occurs532]) THEN
   REMOVE_THEN "IHe" (MP_TAC o SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`e':l4_vexpr961`;
                  `a0:l4_vexpr961`;`idx:num`;`k:num`;`bs:l4_vl_entry973 list`;`any_e:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [l4_ksubst447] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l) bs) (l4_ksubst447 e idx any_e) e0` THEN
   REWRITE_TAC [l4_vtr_expr973] THEN
   DISCH_THEN (X_CHOOSE_THEN `e0s:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `e0s:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_REWRITE_TAC []]);;

let l4_vtr_expr_s_no_occurs_subst974 = prove
 (`!env venv ps l' e e'.
   l4_vtr_expr_s973 env venv ps l' e e' ==>
   (!a0 idx k bs any_e.
     l4_venv_sound973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH ps) l' /\
     l4_vl_bound_lift973 [L4VLLam973 a0] idx k bs (l4_vl_bound973 l') /\
     ~l4_core_occurs532 idx e ==>
     ?e0.
       l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l') (l4_vliftN961 e0 1 k) e' /\
       l4_vtr_expr973 env venv ps (L4VLCtx973 (l4_vl_free973 l') bs)
         (l4_ksubst447 e idx any_e) e0)`,
  MESON_TAC [l4_vtr_expr_s_no_occurs_subst_aux974]);;

let l4_vtr_expr_no_occurs_instantiate974 = prove
 (`!env venv ps l a body body' any_e.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) (l4_vl_push_lam973 l a) /\
   ~l4_core_occurs532 0 body /\
   l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l a) body body' ==>
   ?b0.
     l4_vis_defeq_u961 venv (LENGTH ps) (CONS a (l4_vl_ctx973 l)) (l4_vlift961 b0) body' /\
     l4_vtr_expr973 env venv ps l (l4_kinst447 body any_e) b0`,
  REWRITE_TAC [l4_vtr_expr973;l4_kinst447;l4_vlift961] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_vl_push_lam973 l a`;`body:l4_kexpr447`;`e0:l4_vexpr961`]
    l4_vtr_expr_s_no_occurs_subst974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`a:l4_vexpr961`;`0`;`0`;`l4_vl_bound973 l`;`any_e:l4_kexpr447`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_vl_push_lam973;l4_vl_bound973] THEN
   MP_TAC (SPECL [`[L4VLLam973 a]`;`l4_vl_bound973 l`] l4_vl_bound_lift_zero973) THEN
   REWRITE_TAC [APPEND];
   REWRITE_TAC [l4_vl_push_lam973;l4_vl_free973;l4_vl_ctx_push_lam973;
                l4_vl_ctx_eta973;GSYM l4_vtr_expr973] THEN
   DISCH_THEN (X_CHOOSE_THEN `b0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `b0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `e0:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973;l4_vl_ctx_push_lam973]]);;

(* Remaining VTrExpr syntactic inversions (let, proj, natlit, strlit, mdata) *)
let l4_vtr_expr_inv_let974 = prove
 (`!env venv ps l n ty val_e body nd e'.
   l4_vtr_expr973 env venv ps l (L4KLet447 n ty val_e body nd) e' ==>
   ?ty' val' body'.
     l4_vis_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) val' ty' /\
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vtr_expr973 env venv ps l val_e val' /\
     l4_vtr_expr973 env venv ps (l4_vl_push_let973 l ty' val') body body' /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) body' e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973;l4_vtr_expr973]);;

let l4_vtr_expr_inv_proj974 = prove
 (`!env venv ps l owner idx a e'.
   l4_vtr_expr973 env venv ps l (L4KProj447 owner idx a) e' ==>
   ?a' pv fty.
     l4_vtr_expr973 env venv ps l a a' /\
     l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner idx a' pv fty /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) pv e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973;l4_vtr_expr973]);;

let l4_vtr_expr_inv_natlit974 = prove
 (`!env venv ps l m e'.
   l4_vtr_expr973 env venv ps l (L4KNatLit447 m) e' ==>
   l4_core_nat_ready533 env /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_nat_lit973 m) l4_vnat_ty973 /\
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_nat_lit973 m) e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_strlit974 = prove
 (`!env venv ps l bytes e'.
   l4_vtr_expr973 env venv ps l (L4KStrLit447 bytes) e' ==>
   ?s'. l4_core_string_ready533 env /\
        l4_tr_str_lit973 bytes = SOME s' /\
        l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) s' l4_vstring_ty973 /\
        l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) s' e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_vtr_expr_inv_mdata974 = prove
 (`!env venv ps l a e'.
   l4_vtr_expr973 env venv ps l (L4KMData447 a) e' ==>
   l4_vtr_expr973 env venv ps l a e'`,
  REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th_eq ->
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES973]) THEN
    ASSUME_TAC th_eq) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  ASM_MESON_TAC []);;

let l4_kresult_dis974 = l4_distinct_all974 "l4_kresult491";;

(* ========================================================================= *)
(* 2. FullMethodsSound Specification & inference_only / sort_of              *)
(* ========================================================================= *)

let l4_full_methods_sound974 = new_definition
 `l4_full_methods_sound974 env venv ps chk rec <=>
   (!g l e ty.
     l4_vtr_ctx973 env venv ps g l /\
     chk /\
     l4_infer_method543 rec g e = L4KAccept491 ty ==>
     ?e' ty'. l4_vtr_typing973 env venv ps l e ty e' ty') /\
   (!g l e e' ty.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l e e' /\
     l4_infer_method543 rec g e = L4KAccept491 ty ==>
     ?ty'. l4_vtr_expr973 env venv ps l ty ty' /\
           l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty') /\
   (!g l e e' ty.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l e e' /\
     l4_infer_type_method543 rec g e = L4KAccept491 ty ==>
     ?ty'. l4_vtr_expr973 env venv ps l ty ty' /\
           l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty') /\
   (!cheap g l e e' e1.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l e e' /\
     l4_whnf_core_method543 rec cheap g e = L4KAccept491 e1 ==>
     l4_vtr_expr973 env venv ps l e1 e') /\
   (!g l e e' e1.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l e e' /\
     l4_whnf_method543 rec g e = L4KAccept491 e1 ==>
     l4_vtr_expr973 env venv ps l e1 e') /\
   (!g l t t' s s'.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l t t' /\
     l4_vtr_expr973 env venv ps l s s' /\
     l4_defeq_method543 rec g t s = L4KAccept491 T ==>
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s') /\
   (!g l t t' s s'.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l t t' /\
     l4_vtr_expr973 env venv ps l s s' /\
     l4_eager_defeq_method543 rec g t s = L4KAccept491 T ==>
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s')`;;

let l4_fms_proj_thms974 =
  let raw = UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL l4_full_methods_sound974))) in
  CONJUNCTS raw;;

let [l4_fms_infer974; l4_fms_infer_typed974; l4_fms_infer_type974;
     l4_fms_whnf_core974; l4_fms_whnf974; l4_fms_defeq974; l4_fms_eager_defeq974] =
  map (GENL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
             `chk:bool`;`rec:l4_kmethods543`] o DISCH_ALL) l4_fms_proj_thms974;;

let l4_full_methods_sound_inference_only974 = prove
 (`!env venv ps chk rec.
   l4_full_methods_sound974 env venv ps chk rec ==>
   l4_full_methods_sound974 env venv ps F (l4_inference_only543 rec)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `rec:l4_kmethods543` (cases "l4_kmethods543")) THEN
  REWRITE_TAC [l4_full_methods_sound974;l4_inference_only543;
               l4_infer_method543;l4_infer_type_method543;l4_whnf_method543;
               l4_whnf_core_method543;l4_defeq_method543;l4_eager_defeq_method543] THEN
  MESON_TAC []);;

let l4_application_type_defeq_full_sound974 = prove
 (`!env venv ps chk rec g l a dom dom' aty aty'.
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l dom dom' /\
   l4_vtr_expr973 env venv ps l aty aty' /\
   l4_application_type_defeq543 rec g a dom aty = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' aty'`,
  REWRITE_TAC [l4_application_type_defeq543] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN DISCH_TAC THEN
  ASM_MESON_TAC [l4_fms_eager_defeq974;l4_fms_defeq974]);;

let l4_sort_of_sound_typed974 = prove
 (`!env venv ps chk rec g l e e' u.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_sort_of543 rec g e = L4KAccept491 u ==>
   ?u'. l4_tr_l967 ps u = SOME u' /\
        l4_vlevel_wf961 (LENGTH ps) u' /\
        l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' (L4VSort961 u')`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_sort_of543;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 MP_TAC MP_TAC))))) THEN
  STRUCT_CASES_TAC (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491"] THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `?ty'. l4_vtr_expr973 env venv ps l ty ty' /\
           l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) e' ty'`
    (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_fms_infer_typed974]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 a) ty'` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_fms_whnf974]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`a:l4_klevel447`;`ty':l4_vexpr961`]
    l4_vtr_expr_inv_sort973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
  ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973;l4_vis_defeq_u_symm972]);;

let l4_sort_of_sound_checking974 = prove
 (`!env venv ps rec g l e u.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_sort_of543 rec g e = L4KAccept491 u ==>
   ?e' u'. l4_tr_l967 ps u = SOME u' /\
           l4_vlevel_wf961 (LENGTH ps) u' /\
           l4_vtr_expr973 env venv ps l e e' /\
           l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' (L4VSort961 u')`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_sort_of543;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 MP_TAC MP_TAC))))) THEN
  STRUCT_CASES_TAC (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491"] THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `?e' ty'. l4_vtr_typing973 env venv ps l e ty e' ty'`
    (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` MP_TAC)) THENL
  [ASM_MESON_TAC [l4_fms_infer974]; ALL_TAC] THEN
  REWRITE_TAC [l4_vtr_typing973] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 a) ty'` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_fms_whnf974]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`a:l4_klevel447`;`ty':l4_vexpr961`]
    l4_vtr_expr_inv_sort973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`u':l4_vlevel961`] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
  ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973;l4_vis_defeq_u_symm972]);;
(* ========================================================================= *)
(* 3. Reduction Soundness (Beta, Delta, Nat, Quotient, Recursor, Projection) *)
(* ========================================================================= *)

let l4_hp_proj_thms974 =
  let raw = UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL l4_has_primitives973))) in
  CONJUNCTS raw;;

let [l4_hp_nat974; l4_hp_bool974; l4_hp_string974; l4_hp_pred974; l4_hp_binary974] =
  map (GENL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] o DISCH_ALL) l4_hp_proj_thms974;;

let l4_vnat_ty_ne_vbool_ty974 = prove
 (`~(l4_vnat_ty973 = l4_vbool_ty973)`,
  REWRITE_TAC [l4_vnat_ty973;l4_vbool_ty973;l4_core_nat_name533;l4_core_bool_name533;
               injectivity "l4_vexpr961";injectivity "l4_name";CONS_11] THEN
  ARITH_TAC);;

let l4_kdecl_kind_dis974 = l4_distinct_all974 "l4_kdecl_kind493";;
let l4_kprimitive_dis974 = l4_distinct_all974 "l4_kprimitive493";;
let l4_kquotient_dis974 = l4_distinct_all974 "l4_kquotient493";;
let l4_option_dis974 = l4_distinct_all974 "option";;
let l4_all_dis974 = end_itlist CONJ
  [l4_kexpr_dis974; l4_kresult_dis974; l4_kdecl_kind_dis974;
   l4_kprimitive_dis974; l4_kquotient_dis974; l4_option_dis974;
   injectivity "l4_kdecl_kind493"; injectivity "l4_kresult491";
   injectivity "l4_kexpr447"; PAIR_EQ; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL];;

let l4_strip_as_aprime974 th =
  if is_exists (concl th) then
    let v, _ = dest_exists (concl th) in
    X_CHOOSE_THEN (mk_var ("a'", type_of v)) ASSUME_TAC th
  else ASSUME_TAC th;;

let l4_inv_vtr_s_goal974 =
  DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [l4_vtr_expr_s_CASES_FRESH974]) THEN
  REWRITE_TAC [l4_kexpr_dis974;injectivity "l4_kexpr447"] THEN
  REPEAT STRIP_TAC THEN l4_elim_case_eqs973;;

let l4_all2_nth_error974 = prove
 (`!(R:A->B->bool) xs ys.
   ALL2 R xs ys ==>
   (!i x. l4_nth_error550 xs i = SOME x ==>
     ?y. l4_nth_error550 ys i = SOME y /\ R x y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_nth_error550;l4_all_dis974] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   EXISTS_TAC `h':B` THEN ASM_REWRITE_TAC [];
   ASM_MESON_TAC []]);;

let l4_all2_nth_error_r974 = prove
 (`!(R:A->B->bool) xs ys.
   ALL2 R xs ys ==>
   (!i y. l4_nth_error550 ys i = SOME y ==>
     ?x. l4_nth_error550 xs i = SOME x /\ R x y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_nth_error550;l4_all_dis974] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   EXISTS_TAC `h:A` THEN ASM_REWRITE_TAC [];
   ASM_MESON_TAC []]);;

let l4_all2_skip974 = prove
 (`!(R:A->B->bool) xs ys.
   ALL2 R xs ys ==> !k. ALL2 R (l4_skip550 xs k) (l4_skip550 ys k)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_skip550] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [ALL2] THEN
  ASM_MESON_TAC []);;

let l4_all2_length974 = prove
 (`!(R:A->B->bool) xs ys. ALL2 R xs ys ==> LENGTH xs = LENGTH ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;LENGTH] THEN ASM_MESON_TAC []);;

let l4_all2_pair_inv974 = prove
 (`!(R:A->B->bool) x1 x2 ys.
   ALL2 R [x1; x2] ys <=> (?y1 y2. ys = [y1; y2] /\ R x1 y1 /\ R x2 y2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN REWRITE_TAC [ALL2;NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC (ISPEC `t:B list` list_CASES) THEN REWRITE_TAC [ALL2;NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC (ISPEC `t':B list` list_CASES) THEN REWRITE_TAC [ALL2;NOT_CONS_NIL;CONS_11] THEN
  MESON_TAC []);;

let l4_all2_triple_inv974 = prove
 (`!(R:A->B->bool) x1 x2 x3 ys.
   ALL2 R [x1; x2; x3] ys <=> (?y1 y2 y3. ys = [y1; y2; y3] /\ R x1 y1 /\ R x2 y2 /\ R x3 y3)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;l4_all2_pair_inv974;NOT_CONS_NIL;GSYM NOT_CONS_NIL;CONS_11] THEN
  MESON_TAC []);;

let l4_all2_vtr_s_to_vtr974 = prove
 (`!env venv ps l xs ys.
   ALL2 (l4_vtr_expr_s973 env venv ps l) xs ys ==>
   ALL2 (l4_vtr_expr973 env venv ps l) xs ys`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:l4_vexpr961 list` list_CASES) THEN
  REWRITE_TAC [ALL2] THEN STRIP_TAC THEN CONJ_TAC THENL
  [ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973]; ASM_MESON_TAC []]);;

let l4_all2_vtr_s_refl_u974 = prove
 (`!env venv ps l xs ys.
   ALL2 (l4_vtr_expr_s973 env venv ps l) xs ys ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l)) ys ys`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:l4_vexpr961 list` list_CASES) THEN
  REWRITE_TAC [ALL2] THEN STRIP_TAC THEN CONJ_TAC THENL
  [ASM_MESON_TAC [l4_vtr_expr_s_has_type973;l4_vis_defeq_u_refl973];
   ASM_MESON_TAC []]);;

let l4_core_find_rule_mem974 = prove
 (`!cn rules r. l4_core_find_rule557 cn rules = SOME r ==> MEM r rules`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [l4_core_find_rule557;l4_all_dis974;MEM] THEN
  GEN_TAC THEN COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   DISJ1_TAC THEN REFL_TAC;
   DISCH_TAC THEN DISJ2_TAC THEN ASM_MESON_TAC []]);;

let l4_kfirstn_all_ge974 = prove
 (`!(xs:A list) n. LENGTH xs <= n ==> l4_kfirstn494 xs n = xs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC [l4_kfirstn494;LENGTH;LE_0;ARITH_RULE `!m. ~(SUC m <= 0)`;NOT_SUC;SUC_SUB1;LE_SUC;CONS_11] THEN
  ASM_SIMP_TAC []);;

let l4_core_project_fields_eq_map_seq974 = prove
 (`!n start owner value.
   l4_core_project_fields557 n start owner value =
   MAP (\i. L4KProj447 owner i value) (l4_seq973 start n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_core_project_fields557;l4_seq973;MAP] THEN
  ASM_REWRITE_TAC []);;

let l4_skip550_zero974 = prove
 (`!(xs:A list). l4_skip550 xs 0 = xs`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC [l4_skip550]);;

let l4_skip_cons_vnth974 = prove
 (`!ls k. k < LENGTH ls ==>
   l4_skip550 ls k = CONS (l4_vnth_level961 ls k) (l4_skip550 ls (SUC k))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
  REWRITE_TAC [LENGTH;LT;LT_REFL;LT_SUC;l4_skip550;l4_vnth_level961;NOT_SUC;SUC_SUB1;
               l4_skip550_zero974] THEN
  ASM_SIMP_TAC []);;

let l4_kfirstn494_zero974 = prove
 (`!(xs:A list). l4_kfirstn494 xs 0 = []`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC [l4_kfirstn494]);;

let l4_map_vlevel_inst_vlevel_params_from974 = prove
 (`!m k ls. k + m <= LENGTH ls ==>
   MAP (l4_vlevel_inst961 ls) (l4_vlevel_params_from966 k m) =
   l4_kfirstn494 (l4_skip550 ls k) m`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vlevel_params_from966;MAP;l4_kfirstn494_zero974;l4_vlevel_inst961] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k < LENGTH (ls:l4_vlevel961 list)`
    (fun th -> REWRITE_TAC [MATCH_MP l4_skip_cons_vnth974 th]) THENL
  [ASM_ARITH_TAC;
   REWRITE_TAC [l4_kfirstn494;NOT_SUC;SUC_SUB1;CONS_11] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_map_vlevel_inst_vlevel_params974 = prove
 (`!ls. MAP (l4_vlevel_inst961 ls) (l4_vlevel_params966 (LENGTH ls)) = ls`,
  GEN_TAC THEN REWRITE_TAC [l4_vlevel_params966] THEN
  MP_TAC (SPECL [`LENGTH (ls:l4_vlevel961 list)`;`0`;`ls:l4_vlevel961 list`]
    l4_map_vlevel_inst_vlevel_params_from974) THEN
  REWRITE_TAC [ADD_CLAUSES;LE_REFL;l4_skip550_zero974] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC l4_kfirstn_all_ge974 THEN REWRITE_TAC [LE_REFL]);;

(* 3a. Beta reduction (`l4_kcore_beta_collect526` / `l4_kcore_beta526`) *)
let l4_kinstantiate_many_eq_subst_many974 = prove
 (`!e vs. l4_kinstantiate_many526 e vs = l4_ksubst_many526 e 0 vs`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_kinstantiate_many526] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_ksubst_many_nil973]);;

let l4_core_beta_collect_sound974 = prove
 (`!args env venv ps l head vals e'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l
     (l4_kapply_exprs489 args (l4_kinstantiate_many526 head vals)) e' ==>
   l4_vtr_expr973 env venv ps l (l4_kcore_beta_collect526 head args vals) e'`,
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kcore_beta_collect526;l4_kapply_exprs489];
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kcore_beta_collect526;NOT_CONS_NIL;HD;TL] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [l4_kinstantiate_many_eq_subst_many974;l4_ksubst_many_cons973] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE
     [l4_kapply_exprs489;l4_kinstantiate_many_eq_subst_many974;l4_ksubst_many526]) THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
   DISCH_THEN (X_CHOOSE_THEN `fa':l4_vexpr961`
     (X_CHOOSE_THEN `rest':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC
     `l4_vtr_expr_s973 env venv ps l
        (L4KApp447 (L4KLam447 a0 a1 (l4_ksubst_many526 a2 0 vals) (l4_ksubst_many526 a3 (SUC 0) vals)) h)
        fa'` THEN
   l4_inv_vtr_s_goal974 THEN
   UNDISCH_TAC
     `l4_vtr_expr_s973 env venv ps l
        (L4KLam447 a0 a1 (l4_ksubst_many526 a2 0 vals) (l4_ksubst_many526 a3 (SUC 0) vals)) f'` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `L4VLam961 dom' body'`;`a':l4_vexpr961`;`ty:l4_vexpr961`]
     l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961`
     (X_CHOOSE_THEN `cod0:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom':l4_vexpr961`;`body':l4_vexpr961`;`L4VForallE961 dom0 cod0`]
     l4_vhas_type_lam_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `tb:l4_vexpr961`)) THEN
   SUBGOAL_THEN `?u. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [ASM_MESON_TAC [l4_vis_type961]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (L4VLam961 dom' body') (L4VForallE961 dom' tb)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?u_a. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
              dom0 dom' (L4VSort961 u_a)` (X_CHOOSE_TAC `u_a:l4_vlevel961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `dom0:l4_vexpr961`;`cod0:l4_vexpr961`;`dom':l4_vexpr961`;`tb:l4_vexpr961`]
      l4_vis_defeq_u_forallE_inv972) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VLam961 dom' body'`;`L4VLam961 dom' body'`;`L4VLam961 dom' body'`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     MESON_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' dom'`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`dom0:l4_vexpr961`;`u_a:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (L4VApp961 (L4VLam961 dom' body') a') (l4_vinst0961 body' a') (l4_vinst0961 tb a')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_beta961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vtr_expr973 env venv ps l
        (l4_ksubst447 (l4_ksubst_many526 a3 (SUC 0) vals) 0 h) (l4_vinst0961 body' a')`
     ASSUME_TAC THENL
   [REWRITE_TAC [GSYM l4_kinst447] THEN MATCH_MP_TAC l4_vtr_expr_instantiate_lam973 THEN
    EXISTS_TAC `dom':l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)) rest' rest'`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_all2_vtr_s_refl_u974]; ALL_TAC] THEN
   SUBGOAL_THEN
     `?ty_l. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
               (l4_vapps962 rest' (L4VApp961 (L4VLam961 dom' body') a')) ty_l`
     (X_CHOOSE_TAC `ty_l:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_has_type_l973]; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `rest':l4_vexpr961 list`;`rest':l4_vexpr961 list`;
                  `L4VApp961 (L4VLam961 dom' body') a'`;`l4_vinst0961 body' a'`;
                  `ty_l:l4_vexpr961`] l4_vapps_defeq_congr_l974) THEN
   ANTS_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_u961]; ALL_TAC] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `ty_r:l4_vexpr961`) ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN
   EXISTS_TAC `l4_vapps962 rest' (l4_vinst0961 body' a')` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_r:l4_vexpr961` THEN
    ASM_MESON_TAC [l4_all2_vtr_s_to_vtr974];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
    EXISTS_TAC `l4_vapps962 rest' (L4VApp961 (L4VLam961 dom' body') a')` THEN
    ASM_MESON_TAC [l4_vis_defeq_u_symm972]]]);;

let l4_core_beta_sound974 = prove
 (`!env venv ps l head args e'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e' ==>
   l4_vtr_expr973 env venv ps l (l4_kcore_beta526 head args) e'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_kcore_beta526] THEN
  MATCH_MP_TAC l4_core_beta_collect_sound974 THEN
  ASM_REWRITE_TAC [l4_kinstantiate_many526]);;

(* 3b. Delta unfolding (`l4_core_unfold528`) *)
let l4_core_unfold_sound974 = prove
 (`!env venv ps l e e' e1.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_unfold528 env ps e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973];
   ALL_TAC] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 e)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 e)` THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e'`
    ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN
   ASM_REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_core_unfold528 env ps e = L4KAccept491 (SOME e1)` THEN
  REWRITE_TAC [l4_core_unfold528;LET_DEF;LET_END_DEF] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (fun htr ->
    DISCH_THEN (X_CHOOSE_THEN `d:l4_kdeclaration493`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hbody"))) THEN
    ASSUME_TAC htr) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_klevel447 list`;`d:l4_kdeclaration493`]
    l4_get_constant_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961`
    (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
    `(l4_kdecl_kind493 d = L4KDDefinition493 \/
      l4_kdecl_kind493 d = L4KDTheorem493 \/
      (?p. l4_kdecl_kind493 d = L4KDPrimitive493 p)) /\
     (?val_e. l4_kdecl_value493 d = SOME val_e /\
       e1 = l4_kapply_exprs489 args (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 val_e))`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `val_e:l4_kexpr447` STRIP_ASSUME_TAC)) THENL
  [REMOVE_THEN "Hbody" MP_TAC THEN REWRITE_TAC [l4_if_nil_ksubst_levels967] THEN
   MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974])) THEN
   MP_TAC (ISPEC `l4_kdecl_value493 d` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_kresult_dis974])
     (X_CHOOSE_THEN `v0:l4_kexpr447` (fun th ->
       REWRITE_TAC [th;injectivity "l4_kresult491";injectivity "option"] THEN
       DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [])));
   ALL_TAC] THEN
  REMOVE_THEN "Hbody" (K ALL_TAC) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_delta973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`a0:l4_name`;`d:l4_kdeclaration493`;`val_e:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ci2:l4_vconstant961`
    (X_CHOOSE_THEN `val':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ci2:l4_vconstant961 = ci` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [l4_venv_wf_lookup_unique966]; ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) e'` THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
    (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN `us'':l4_vlevel961 list = us'` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = l4_vc_uvars961 ci` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_tr_ls_length967]; ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (L4VConst961 a0 us') (l4_vinstL961 us' val') (l4_vinstL961 us' (l4_vc_type961 ci))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_weak0966 THEN ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`l4_vc_uvars961 ci`;`LENGTH (ps:l4_name list)`;
                  `us':l4_vlevel961 list`;`[]:l4_vexpr961 list`;
                  `L4VConst961 a0 (l4_vlevel_params966 (l4_vc_uvars961 ci))`;
                  `val':l4_vexpr961`;`l4_vc_type961 ci`] l4_vis_defeq_instL966) THEN
   ASM_REWRITE_TAC [MAP;l4_vinstL961] THEN
   SUBGOAL_THEN `MAP (l4_vlevel_inst961 us') (l4_vlevel_params966 (l4_vc_uvars961 ci)) = us'`
     (fun th -> REWRITE_TAC [th]) THEN
   ASM_MESON_TAC [l4_map_vlevel_inst_vlevel_params974];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps l
       (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 val_e) (l4_vinstL961 us' val')`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_closed_to_any973 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_subst_levels973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)) args' args'`
    ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_all2_vtr_s_refl_u974]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?ty_l. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
              (l4_vapps962 args' (L4VConst961 a0 us')) ty_l`
    (X_CHOOSE_TAC `ty_l:l4_vexpr961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_u_has_type_l973]; ALL_TAC] THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                 `args':l4_vexpr961 list`;`args':l4_vexpr961 list`;
                 `L4VConst961 a0 us'`;`l4_vinstL961 us' val'`;`ty_l:l4_vexpr961`]
    l4_vapps_defeq_congr_l974) THEN
  ANTS_TAC THENL [ASM_MESON_TAC [l4_vis_defeq_u961]; ALL_TAC] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `ty_r:l4_vexpr961`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN
  EXISTS_TAC `l4_vapps962 args' (l4_vinstL961 us' val')` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_r:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_all2_vtr_s_to_vtr974];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN
   ASM_MESON_TAC [l4_vis_defeq_u_symm972]]);;

(* 3c. Native hooks & Nat primitives *)
let l4_core_reduce_native_sound974 = prove
 (`!e e1. ~(l4_core_reduce_native549 e = L4KAccept491 (SOME e1))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [l4_core_reduce_native549] THEN
  STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (SPEC `a0:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (ISPEC `a1':l4_klevel447 list` list_CASES) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (SPEC `a1:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974]);;

let l4_core_nat_value_sound974 = prove
 (`!env venv ps l e e' n.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_core_nat_ready533 env /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_nat_value544 e = SOME n ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_nat_lit973 n) e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_core_nat_value544;l4_all_dis974] THENL
  [DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_const973) THEN
   DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list`
     (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   RULE_ASSUM_TAC (REWRITE_RULE []) THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_tr_ls967;injectivity "option"]) THEN
   ASM_REWRITE_TAC [l4_nat_lit973];
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_natlit974) THEN
   STRIP_TAC THEN REWRITE_TAC [injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC []]);;

let l4_core_shiftr_sound974 = prove
 (`!a b v. l4_core_shiftr544 a b = SOME v ==> v = a DIV (2 EXP b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_shiftr544] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [DIV_0] THEN
    MP_TAC (SPEC `b:num` (ARITH_RULE `!b. ~(2 EXP b = 0) \/ 2 EXP b = 0`)) THEN
    REWRITE_TAC [EXP_EQ_0;ARITH_EQ] THEN
    MESON_TAC [DIV_0];
    SUBGOAL_THEN `bitsize a <= b` ASSUME_TAC THENL
    [MP_TAC (SPEC `a:num` BITSIZE_EQ_0) THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC;
     SUBGOAL_THEN `a < 2 EXP b` ASSUME_TAC THENL
     [ASM_MESON_TAC [BITSIZE_LE];
      ASM_SIMP_TAC [DIV_LT]]]];
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC]);;

let l4_core_binary_nat_sound974 = prove
 (`!env venv ps l fuel n d op a b res.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_core_nat_ready533 env /\
   l4_kfind_decl493 env n = SOME d /\
   l4_kdecl_kind493 d = L4KDPrimitive493 op /\
   l4_core_binary_nat544 fuel env op a b = L4KAccept491 (SOME res) ==>
   ?res_v rty.
     l4_vtr_expr973 env venv ps l res res_v /\
     l4_vis_defeq961 venv (LENGTH ps) (l4_vl_ctx973 l)
       (L4VApp961 (L4VApp961 (L4VConst961 n []) (l4_nat_lit973 a)) (l4_nat_lit973 b))
       res_v rty`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_has_primitives973 env venv /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?res_v rty.
       l4_vbinary_prim_spec973 op a b = SOME (res_v, rty) /\
       (rty = l4_vbool_ty973 ==> l4_core_bool_ready533 env) /\
       l4_vtr_expr973 env venv ps l res res_v /\
       l4_vinstL961 [] res_v = res_v /\
       l4_vinstL961 [] rty = rty`
    (X_CHOOSE_THEN `res_v:l4_vexpr961`
      (X_CHOOSE_THEN `rty:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
  [UNDISCH_TAC `l4_core_binary_nat544 fuel env op a b = L4KAccept491 (SOME res)` THEN
   REWRITE_TAC [l4_core_binary_nat544;LET_DEF;LET_END_DEF] THEN
   (let instL_nat = prove (`l4_vinstL961 [] l4_vnat_ty973 = l4_vnat_ty973`,
      REWRITE_TAC [l4_vnat_ty973;l4_vinstL961;MAP]) in
    let instL_bool = prove (`l4_vinstL961 [] l4_vbool_ty973 = l4_vbool_ty973`,
      REWRITE_TAC [l4_vbool_ty973;l4_vinstL961;MAP]) in
    let instL_blit = prove (`!c. l4_vinstL961 [] (l4_vbool_lit973 c) = l4_vbool_lit973 c`,
      GEN_TAC THEN REWRITE_TAC [l4_vbool_lit973] THEN COND_CASES_TAC THEN REWRITE_TAC [l4_vinstL961;MAP]) in
    let mk_nat_tac expr_tm =
     REWRITE_TAC [injectivity "l4_kresult491";injectivity "option"] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     MAP_EVERY EXISTS_TAC [expr_tm; `l4_vnat_ty973`] THEN
     REWRITE_TAC [l4_vbinary_prim_spec973;l4_all_dis974;l4_vnat_ty_ne_vbool_ty974;
                  l4_vinstL_nat_lit973;instL_nat] THEN
     MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
     MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
     ASM_REWRITE_TAC [] in
    let mk_bool_tac cond_tm =
     COND_CASES_TAC THEN REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";injectivity "option"] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     MAP_EVERY EXISTS_TAC [mk_comb (`l4_vbool_lit973`, cond_tm); `l4_vbool_ty973`] THEN
     REWRITE_TAC [l4_vbinary_prim_spec973;l4_all_dis974;instL_bool;instL_blit] THEN
     ASM_REWRITE_TAC [l4_vbool_lit973] THEN
     MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_bool974) THEN
     ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
     COND_CASES_TAC THEN REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
     EXISTS_TAC `L4VConstant961 0 l4_vbool_ty973` THEN
     ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961] in
    STRUCT_CASES_TAC (SPEC `op:l4_kprimitive493` (cases "l4_kprimitive493")) THEN
    REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THENL
    [(* Add *) mk_nat_tac `l4_nat_lit973 (a + b)`;
     (* Sub *) mk_nat_tac `l4_nat_lit973 (a - b)`;
     (* Mul *) mk_nat_tac `l4_nat_lit973 (a * b)`;
     (* Pow *) COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_kresult491";l4_all_dis974] THEN
               mk_nat_tac `l4_nat_lit973 (a EXP b)`;
     (* Gcd *) mk_nat_tac `l4_nat_lit973 (gcd (a, b))`;
     (* Mod *) mk_nat_tac `l4_nat_lit973 (a MOD b)`;
     (* Div *) mk_nat_tac `l4_nat_lit973 (a DIV b)`;
     (* BEq *) mk_bool_tac `a:num = b`;
     (* BLE *) mk_bool_tac `a:num <= b`;
     (* LAnd *) mk_nat_tac `l4_nat_lit973 (l4_core_bitop544 (\x y. x /\ y) a b)`;
     (* LOr *) mk_nat_tac `l4_nat_lit973 (l4_core_bitop544 (\x y. x \/ y) a b)`;
     (* Xor *) mk_nat_tac `l4_nat_lit973 (l4_core_bitop544 (\x y. ~(x <=> y)) a b)`;
     (* ShiftLeft *) COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_kresult491";l4_all_dis974] THEN
                     mk_nat_tac `l4_nat_lit973 (a * 2 EXP b)`;
     (* ShiftRight *)
     MP_TAC (ISPEC `l4_core_shiftr544 a b` (cases "option")) THEN
     DISCH_THEN (DISJ_CASES_THEN2
       (fun th -> REWRITE_TAC [th;injectivity "l4_kresult491";l4_all_dis974])
       (X_CHOOSE_THEN `sv:num` (fun th ->
         ASSUME_TAC (MATCH_MP l4_core_shiftr_sound974 th) THEN
         REWRITE_TAC [th;injectivity "l4_kresult491";injectivity "option"] THEN
         DISCH_THEN (SUBST1_TAC o SYM) THEN
         MAP_EVERY EXISTS_TAC [`l4_nat_lit973 (a DIV 2 EXP b)`;`l4_vnat_ty973`] THEN
         ASM_REWRITE_TAC [l4_vbinary_prim_spec973;l4_all_dis974;l4_vnat_ty_ne_vbool_ty974;
                          l4_vinstL_nat_lit973;instL_nat] THEN
         MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
         MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
         MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
         ASM_REWRITE_TAC [])))]);
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`res_v:l4_vexpr961`;`rty:l4_vexpr961`] THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_binary974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`n:l4_name`;`d:l4_kdeclaration493`;`op:l4_kprimitive493`;
                              `a:num`;`b:num`;`res_v:l4_vexpr961`;`rty:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_weak0966 THEN ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`0`;`LENGTH (ps:l4_name list)`;
                 `[]:l4_vlevel961 list`;`[]:l4_vexpr961 list`;
                 `L4VApp961 (L4VApp961 (L4VConst961 n []) (l4_nat_lit973 a)) (l4_nat_lit973 b)`;
                 `res_v:l4_vexpr961`;`rty:l4_vexpr961`] l4_vis_defeq_instL966) THEN
  ASM_REWRITE_TAC [ALL;MAP;l4_vinstL961;l4_vinstL_nat_lit973]);;

let l4_core_reduce_nat_sound974 = prove
 (`!env venv ps chk rec fuel g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_reduce_nat549 rec fuel env g e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_has_primitives973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;l4_ves_prims973;
                  l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 e)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 e)` THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e'`
    ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN
   ASM_REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_ksplit_app489 e = (head, args)` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [PAIR]; ALL_TAC] THEN
  UNDISCH_TAC `l4_core_reduce_nat549 rec fuel env g e = L4KAccept491 (SOME e1)` THEN
  ASM_REWRITE_TAC [l4_core_reduce_nat549] THEN
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (ISPEC `a1:l4_klevel447 list` list_CASES) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (ISPEC `args:l4_kexpr447 list` list_CASES) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  STRUCT_CASES_TAC (ISPEC `t:l4_kexpr447 list` list_CASES) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THENL
  [(* Unary: [h] *)
   DISCH_THEN (fun htr -> ASSUME_TAC htr) THEN
   REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
   COND_CASES_TAC THENL
   [(* Nat.succ *)
    REWRITE_TAC [l4_all_dis974] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
    RULE_ASSUM_TAC (REWRITE_RULE []) THEN
    DISCH_THEN (X_CHOOSE_THEN `aw:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (ISPEC `l4_core_nat_value544 aw` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_all_dis974])
      (X_CHOOSE_THEN `av:num` (fun th ->
        ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974;injectivity "option"] THEN
        DISCH_THEN (SUBST1_TAC o SYM)))) THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 [h] (L4KConst447 a0 [])) e'` THEN
    REWRITE_TAC [l4_kapply_exprs489] THEN
    DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_app973) THEN
    DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961`
      (X_CHOOSE_THEN `a':l4_vexpr961` (X_CHOOSE_THEN `ty_a:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VConst961 a0 []) f'`
      ASSUME_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `l:l4_vl_ctx_rec973`;`a0:l4_name`;`[]:l4_klevel447 list`;`f':l4_vexpr961`]
       l4_vtr_expr_inv_const973) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
     REWRITE_TAC [l4_tr_ls967;injectivity "option"] THEN MESON_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vtr_expr973 env venv ps l aw a'` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_fms_whnf974;l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 av) a'`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_core_nat_value_sound974 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`aw:l4_kexpr447`] THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `[a':l4_vexpr961]`;`[l4_nat_lit973 av]`;
                   `f':l4_vexpr961`;`L4VConst961 a0 []`;`ty_a:l4_vexpr961`]
      l4_vapps_defeq_congr_l974) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vapps962;ALL2] THEN
     ASM_MESON_TAC [l4_vis_defeq_u_symm972];
     REWRITE_TAC [l4_vapps962] THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)] THEN
    MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `l4_nat_lit973 (SUC av)` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_nat_lit_has_type973 THEN
     EXISTS_TAC `env:l4_kdeclaration493 list` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VApp961 f' a'` THEN
     ASM_REWRITE_TAC [l4_nat_lit973] THEN
     ASM_MESON_TAC [l4_vis_defeq_u_symm972]];
    (* PNatPred *)
    MP_TAC (ISPEC `l4_kfind_decl493 env a0` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_all_dis974])
      (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
    MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
      l4_strip_as_aprime974 th THEN ASM_REWRITE_TAC [l4_all_dis974])) THEN
    MP_TAC (SPEC `a':l4_kprimitive493` (cases "l4_kprimitive493")) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
      REWRITE_TAC [th;l4_all_dis974] THEN
      TRY (ASSUME_TAC th))) THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
    RULE_ASSUM_TAC (REWRITE_RULE []) THEN
    DISCH_THEN (X_CHOOSE_THEN `aw:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (ISPEC `l4_core_nat_value544 aw` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_all_dis974])
      (X_CHOOSE_THEN `av:num` (fun th ->
        ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974;injectivity "option"] THEN
        DISCH_THEN (SUBST1_TAC o SYM)))) THEN
    UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 [h] (L4KConst447 a0 [])) e'` THEN
    REWRITE_TAC [l4_kapply_exprs489] THEN
    DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_app973) THEN
    DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961`
      (X_CHOOSE_THEN `arg':l4_vexpr961` (X_CHOOSE_THEN `ty_a:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VConst961 a0 []) f'`
      ASSUME_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `l:l4_vl_ctx_rec973`;`a0:l4_name`;`[]:l4_klevel447 list`;`f':l4_vexpr961`]
       l4_vtr_expr_inv_const973) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
     REWRITE_TAC [l4_tr_ls967;injectivity "option"] THEN MESON_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `l4_vtr_expr973 env venv ps l aw arg'` ASSUME_TAC THENL
    [ASM_MESON_TAC [l4_fms_whnf974;l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 av) arg'`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_core_nat_value_sound974 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`aw:l4_kexpr447`] THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (L4VApp961 (L4VConst961 a0 []) (l4_nat_lit973 av))
         (l4_nat_lit973 (av - 1)) l4_vnat_ty973` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_weak0966 THEN ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`0`;`LENGTH (ps:l4_name list)`;
                    `[]:l4_vlevel961 list`;`[]:l4_vexpr961 list`;
                    `L4VApp961 (L4VConst961 a0 []) (l4_nat_lit973 av)`;
                    `l4_nat_lit973 (av - 1)`;`l4_vnat_ty973`] l4_vis_defeq_instL966) THEN
     REWRITE_TAC [ALL;MAP;l4_vinstL961;l4_vinstL_nat_lit973;l4_vnat_ty973] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_pred974) THEN
     ASM_REWRITE_TAC [GSYM l4_vnat_ty973] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`a0:l4_name`;`d:l4_kdeclaration493`;`av:num`]) THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `[arg':l4_vexpr961]`;`[l4_nat_lit973 av]`;
                   `f':l4_vexpr961`;`L4VConst961 a0 []`;`ty_a:l4_vexpr961`]
      l4_vapps_defeq_congr_l974) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vapps962;ALL2] THEN ASM_MESON_TAC [l4_vis_defeq_u_symm972];
     REWRITE_TAC [l4_vapps962] THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)] THEN
    MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `l4_nat_lit973 (av - 1)` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_nat_lit_has_type973 THEN
     EXISTS_TAC `env:l4_kdeclaration493 list` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
     EXISTS_TAC `L4VApp961 (L4VConst961 a0 []) (l4_nat_lit973 av)` THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vnat_ty973` THEN
      MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VApp961 f' arg'` THEN
      ASM_MESON_TAC [l4_vis_defeq_u_symm972]]]];
   (* Binary: [h; h'] when t' = [] *)
   STRUCT_CASES_TAC (ISPEC `t':l4_kexpr447 list` list_CASES) THEN
   REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
   DISCH_THEN (fun htr -> ASSUME_TAC htr) THEN
   MP_TAC (ISPEC `l4_kfind_decl493 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     l4_strip_as_aprime974 th THEN ASM_REWRITE_TAC [l4_all_dis974])) THEN
   DISCH_THEN (LABEL_TAC "Hbin") THEN
   SUBGOAL_THEN
     `?aw bw av bv.
        l4_core_nat_ready533 env /\
        l4_whnf_method543 rec g h = L4KAccept491 aw /\
        l4_whnf_method543 rec g h' = L4KAccept491 bw /\
        l4_core_nat_value544 aw = SOME av /\
        l4_core_nat_value544 bw = SOME bv /\
        l4_core_binary_nat544 fuel env a' av bv = L4KAccept491 (SOME e1)`
     (X_CHOOSE_THEN `aw:l4_kexpr447`
       (X_CHOOSE_THEN `bw:l4_kexpr447`
         (X_CHOOSE_THEN `av:num`
           (X_CHOOSE_THEN `bv:num` STRIP_ASSUME_TAC)))) THENL
   [SUBGOAL_THEN
      `(if ~l4_core_nat_ready533 env then L4KAccept491 NONE else
        l4_kr_bind491 (l4_whnf_method543 rec g h) (\a.
          l4_kr_bind491 (l4_whnf_method543 rec g h') (\b.
            match (l4_core_nat_value544 a, l4_core_nat_value544 b) with
            | (SOME av, SOME bv) -> l4_core_binary_nat544 fuel env a' av bv
            | _ -> L4KAccept491 NONE))) = L4KAccept491 (SOME e1)` MP_TAC THENL
    [REMOVE_THEN "Hbin" MP_TAC THEN
     STRUCT_CASES_TAC (SPEC `a':l4_kprimitive493` (cases "l4_kprimitive493")) THEN
     REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN ACCEPT_TAC;
     ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
    RULE_ASSUM_TAC (REWRITE_RULE []) THEN
    REWRITE_TAC [l4_kr_bind_accept967] THEN
    DISCH_THEN (X_CHOOSE_THEN `aw:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `bw:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
    MP_TAC (ISPEC `l4_core_nat_value544 aw` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974])
      (X_CHOOSE_THEN `av:num` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
    MP_TAC (ISPEC `l4_core_nat_value544 bw` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974])
      (X_CHOOSE_THEN `bv:num` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974;injectivity "option"]))) THEN
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`aw:l4_kexpr447`;`bw:l4_kexpr447`;`av:num`;`bv:num`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REMOVE_THEN "Hbin" (K ALL_TAC) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`fuel:num`;`a0:l4_name`;`d:l4_kdeclaration493`;
                  `a':l4_kprimitive493`;`av:num`;`bv:num`;`e1:l4_kexpr447`]
     l4_core_binary_nat_sound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `res_v:l4_vexpr961`
     (X_CHOOSE_THEN `rty:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 [h; h'] (L4KConst447 a0 [])) e'` THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
   DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961`
     (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `ALL2 (l4_vtr_expr_s973 env venv ps l) [h; h'] args'` THEN
   REWRITE_TAC [l4_all2_pair_inv974] THEN
   DISCH_THEN (X_CHOOSE_THEN `h1':l4_vexpr961`
     (X_CHOOSE_THEN `h2':l4_vexpr961`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VConst961 a0 []) f'`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`a0:l4_name`;`[]:l4_klevel447 list`;`f':l4_vexpr961`]
      l4_vtr_expr_inv_const973) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
    REWRITE_TAC [l4_tr_ls967;injectivity "option"] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l aw h1' /\ l4_vtr_expr973 env venv ps l bw h2'`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_fms_whnf974;l4_vtr_expr_s_to_vtr_expr973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 av) h1' /\
      l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 bv) h2'`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC l4_core_nat_value_sound974 THEN
    ASM_MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?ty_l. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
               (l4_vapps962 [h1'; h2'] f') ty_l`
     (X_CHOOSE_TAC `ty_l:l4_vexpr961`) THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_has_type_l973]; ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `[h1':l4_vexpr961; h2']`;`[l4_nat_lit973 av; l4_nat_lit973 bv]`;
                  `f':l4_vexpr961`;`L4VConst961 a0 []`;`ty_l:l4_vexpr961`]
     l4_vapps_defeq_congr_l974) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [ALL2] THEN ASM_MESON_TAC [l4_vis_defeq_u_symm972];
    REWRITE_TAC [l4_vapps962] THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)] THEN
   MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `res_v:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `L4VApp961 (L4VApp961 (L4VConst961 a0 []) (l4_nat_lit973 av)) (l4_nat_lit973 bv)` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `rty:l4_vexpr961` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
    EXISTS_TAC `L4VApp961 (L4VApp961 f' h1') h2'` THEN
    ASM_MESON_TAC [l4_vis_defeq_u_symm972;l4_vapps962]]]);;


(* 3d. Quotient reduction (`l4_core_reduce_quotient550`) *)
let l4_core_reduce_quotient_sound974 = prove
 (`!env venv ps chk rec g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_reduce_quotient550 rec env g e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 e)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 e)` THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e'`
    ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN
   ASM_REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_ksplit_app489 e = (head, args)` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [PAIR]; ALL_TAC] THEN
  UNDISCH_TAC `l4_core_reduce_quotient550 rec env g e = L4KAccept491 (SOME e1)` THEN
  ASM_REWRITE_TAC [l4_core_reduce_quotient550] THEN
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  DISCH_THEN (fun htr -> ASSUME_TAC htr) THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env a0` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
  DISCH_THEN (LABEL_TAC "Hquot") THEN
  SUBGOAL_THEN
    `?idx.
       ((l4_kdecl_kind493 d = L4KDQuotient493 L4KQLift493 /\ idx = 5) \/
        (l4_kdecl_kind493 d = L4KDQuotient493 L4KQInd493 /\ idx = 4)) /\
       (match (l4_nth_error550 args idx, l4_nth_error550 args 3) with
        | (SOME major, SOME fn) ->
            l4_kr_bind491 (l4_whnf_method543 rec g major) (\ready.
              match l4_ksplit_app489 ready with
              | (L4KConst447 cn cus, [cty; rel; representative]) ->
                  (match l4_kfind_decl493 env cn with
                   | SOME cd ->
                       (match l4_kdecl_kind493 cd with
                        | L4KDQuotient493 L4KQCtor493 ->
                            L4KAccept491 (SOME
                              (l4_kapply_exprs489 (l4_skip550 args (SUC idx))
                                (L4KApp447 fn representative)))
                        | _ -> L4KAccept491 NONE)
                   | NONE -> L4KAccept491 NONE)
              | _ -> L4KAccept491 NONE)
        | _ -> L4KAccept491 NONE) = L4KAccept491 (SOME e1)`
    (X_CHOOSE_THEN `idx:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
  [REMOVE_THEN "Hquot" MP_TAC THEN
   MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     l4_strip_as_aprime974 th THEN ASM_REWRITE_TAC [l4_all_dis974])) THEN
   MP_TAC (SPEC `a':l4_kquotient493` (cases "l4_kquotient493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     REWRITE_TAC [th;l4_all_dis974] THEN TRY (ASSUME_TAC th))) THENL
   [DISCH_TAC THEN EXISTS_TAC `5` THEN ASM_REWRITE_TAC [];
    DISCH_TAC THEN EXISTS_TAC `4` THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  REMOVE_THEN "Hquot" (K ALL_TAC) THEN
  MP_TAC (ISPEC `l4_nth_error550 (args:l4_kexpr447 list) idx` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974])
    (X_CHOOSE_THEN `major:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (ISPEC `l4_nth_error550 (args:l4_kexpr447 list) 3` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974])
    (X_CHOOSE_THEN `fn:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974;injectivity "option"]))) THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `maj_w:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `chead = FST (l4_ksplit_app489 maj_w)` THEN
  ABBREV_TAC `cargs = SND (l4_ksplit_app489 maj_w)` THEN
  SUBGOAL_THEN `l4_ksplit_app489 maj_w = (chead, cargs)` (fun th -> REWRITE_TAC [th]) THENL
  [MAP_EVERY EXPAND_TAC ["chead";"cargs"] THEN REWRITE_TAC [PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_kapply_exprs489 cargs chead = maj_w` MP_TAC THENL
  [MAP_EVERY EXPAND_TAC ["chead";"cargs"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  STRUCT_CASES_TAC (SPEC `chead:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  MP_TAC (ISPEC `cargs:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `h1:l4_kexpr447` (X_CHOOSE_THEN `t1:l4_kexpr447 list` (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
  MP_TAC (ISPEC `t1:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `h2:l4_kexpr447` (X_CHOOSE_THEN `t2:l4_kexpr447 list` (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
  MP_TAC (ISPEC `t2:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `h3:l4_kexpr447` (X_CHOOSE_THEN `t3:l4_kexpr447 list` (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
  MP_TAC (ISPEC `t3:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `h4:l4_kexpr447` (X_CHOOSE_THEN `t4:l4_kexpr447 list` (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
  DISCH_TAC THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env a0'` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `cd:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 cd` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
    l4_strip_as_aprime974 th THEN ASM_REWRITE_TAC [l4_all_dis974])) THEN
  MP_TAC (SPEC `a':l4_kquotient493` (cases "l4_kquotient493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
    REWRITE_TAC [th;l4_all_dis974] THEN TRY (SUBST_ALL_TAC th))) THEN
  REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) e'` THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
    (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN `?maj'. l4_nth_error550 args' idx = SOME maj' /\ l4_vtr_expr_s973 env venv ps l major maj'`
    (X_CHOOSE_THEN `maj':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_all2_nth_error974]; ALL_TAC] THEN
  SUBGOAL_THEN `?fn'. l4_nth_error550 args' 3 = SOME fn' /\ l4_vtr_expr_s973 env venv ps l fn fn'`
    (X_CHOOSE_THEN `fn':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_all2_nth_error974]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 [h1; h2; h3] (L4KConst447 a0' a1')) maj'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`major:l4_kexpr447`;`maj':l4_vexpr961`;
      `l4_kapply_exprs489 [h1; h2; h3] (L4KConst447 a0' a1')`]) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `c':l4_vexpr961`
    (X_CHOOSE_THEN `cargs':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0' a1') c'` THEN
  l4_inv_vtr_s_goal974 THEN
  POP_ASSUM (K ALL_TAC) THEN
  UNDISCH_TAC `ALL2 (l4_vtr_expr_s973 env venv ps l) [h1; h2; h3] cargs'` THEN
  REWRITE_TAC [l4_all2_triple_inv974] THEN
  DISCH_THEN (X_CHOOSE_THEN `c1':l4_vexpr961`
    (X_CHOOSE_THEN `c2':l4_vexpr961`
      (X_CHOOSE_THEN `c3':l4_vexpr961`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (l4_vapps962 args' (L4VConst961 a0 us'))
       (l4_vapps962 (l4_skip550 args' (SUC idx)) (L4VApp961 fn' c3'))`
    ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_quot_red973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;`d:l4_kdeclaration493`;
      `a0':l4_name`;`cd:l4_kdeclaration493`;`us':l4_vlevel961 list`;`us'':l4_vlevel961 list`;
      `args':l4_vexpr961 list`;`c3':l4_vexpr961`;`idx:num`;`fn':l4_vexpr961`;
      `c1':l4_vexpr961`;`c2':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [EXISTS_TAC `maj':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `e':l4_vexpr961` THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN
  EXISTS_TAC `l4_vapps962 (l4_skip550 args' (SUC idx)) (L4VApp961 fn' c3')` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [SUBGOAL_THEN
     `l4_kapply_exprs489 (l4_skip550 (SND (l4_ksplit_app489 e)) (SUC idx)) (L4KApp447 fn h3) =
      l4_kapply_exprs489 (CONS h3 (l4_skip550 (SND (l4_ksplit_app489 e)) (SUC idx))) fn /\
      l4_vapps962 (l4_skip550 args' (SUC idx)) (L4VApp961 fn' c3') =
      l4_vapps962 (CONS c3' (l4_skip550 args' (SUC idx))) fn'`
     (fun th -> REWRITE_TAC [th]) THENL
   [REWRITE_TAC [l4_kapply_exprs489;l4_vapps962]; ALL_TAC] THEN
   SUBGOAL_THEN
     `?ty_r. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
               (l4_vapps962 (CONS c3' (l4_skip550 args' (SUC idx))) fn') ty_r`
     (X_CHOOSE_TAC `ty_r:l4_vexpr961`) THENL
   [REWRITE_TAC [l4_vapps962] THEN MATCH_MP_TAC l4_vis_defeq_u_has_type_r973 THEN
    EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_r:l4_vexpr961` THEN
   ASM_REWRITE_TAC [ALL2] THEN
   REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []) THEN
   MATCH_MP_TAC (REWRITE_RULE [RIGHT_IMP_FORALL_THM] l4_all2_skip974) THEN
   MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []]);;

(* 3e. `l4_core_to_structure585`, `l4_core_to_constructor585`, `l4_core_reduce_recursor585` *)
let l4_core_to_structure_sound974 = prove
 (`!env venv ps rec fuel g l owner k_rule reduced r' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l reduced r' /\
   l4_core_to_structure585 rec fuel env g owner k_rule reduced = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res r'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_core_to_structure585 rec fuel env g owner k_rule reduced = L4KAccept491 res` THEN
  REWRITE_TAC [l4_core_to_structure585] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE []) THEN
  REWRITE_TAC [l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 ty)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 ty)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 args head = ty` MP_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  TRY (DISCH_THEN (K ALL_TAC) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC [] THEN NO_TAC) THEN
  DISCH_TAC THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE []) THEN
  UNDISCH_TAC `a0:l4_name = owner` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC (ISPEC `l4_core_make_structure557 env owner a1 args reduced` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;injectivity "l4_kresult491"] THEN
               DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [])
    (X_CHOOSE_THEN `cand:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  SUBGOAL_THEN
    `?ty'. l4_vtr_expr973 env venv ps l ty0 ty' /\
           l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) r' ty'`
    (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [ASM_MESON_TAC [l4_fms_infer_typed974]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l ty ty'` ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_fms_whnf974]; ALL_TAC] THEN
  ASM_CASES_TAC `k_rule:bool` THEN ASM_REWRITE_TAC [] THENL
  [(* K-rule: proof irrelevance at Prop *)
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `su:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `prop:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   ASM_CASES_TAC `prop:bool` THEN ASM_REWRITE_TAC [] THENL
   [ALL_TAC;
    REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC []] THEN
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ct:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   ASM_CASES_TAC `ok:bool` THEN ASM_REWRITE_TAC [injectivity "l4_kresult491"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THENL
   [ALL_TAC; ASM_REWRITE_TAC []] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `T`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                  `ty:l4_kexpr447`;`ty':l4_vexpr961`;`su:l4_klevel447`]
     l4_sort_of_sound_typed974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `su':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 su' L4VLZero961` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_klevel_equiv_sound_vlevel973 THEN
    MAP_EVERY EXISTS_TAC [`fuel:num`;`ps:l4_name list`;`su:l4_klevel447`;`L4KZero447`] THEN
    ASM_REWRITE_TAC [l4_tr_l967];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' (L4VSort961 L4VLZero961)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`L4VSort961 su'`;`L4VLSucc961 su'`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [l4_vlevel_wf961];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cand' ct'. l4_vtr_typing973 env venv ps l cand ct cand' ct'`
     (X_CHOOSE_THEN `cand':l4_vexpr961` (X_CHOOSE_THEN `ct':l4_vexpr961` MP_TAC)) THENL
   [ASM_MESON_TAC [l4_fms_infer974]; ALL_TAC] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' ct'`
     ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_fms_defeq974]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) cand' ty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ct':l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `cand':l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty':l4_vexpr961` THEN
   MATCH_MP_TAC l4_vis_defeq_proof_irrel961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961];
   (* Structure eta branch *)
   SUBGOAL_THEN `l4_core_structure532 env owner` ASSUME_TAC THENL
   [UNDISCH_TAC `k_rule \/ l4_core_structure532 env owner` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `su:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_kresult491"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THENL
   [ALL_TAC; ASM_REWRITE_TAC []] THEN
   UNDISCH_TAC `l4_core_make_structure557 env owner a1 args reduced = SOME cand` THEN
   REWRITE_TAC [l4_core_make_structure557] THEN
   MP_TAC (ISPEC `l4_core_inductive532 env owner` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `info:l4_kinductive_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (ISPEC `l4_kind_ctors493 info` list_CASES) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `ctor:l4_name` (X_CHOOSE_THEN `ctail:l4_name list`
       (fun th -> REWRITE_TAC [th] THEN ASSUME_TAC th)))) THEN
   MP_TAC (ISPEC `ctail:l4_name list` list_CASES) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974] THEN RULE_ASSUM_TAC (REWRITE_RULE [th]))
     (X_CHOOSE_THEN `c2:l4_name` (X_CHOOSE_THEN `ct2:l4_name list`
       (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
   MP_TAC (ISPEC `l4_core_constructor532 env ctor` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `c:l4_kconstructor_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   REWRITE_TAC [injectivity "option"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `l4_kind_num_indices493 info = 0` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_core_structure532 env owner` THEN
    ASM_REWRITE_TAC [l4_core_structure532] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?d_ind. l4_kfind_decl493 env owner = SOME d_ind /\
              l4_kdecl_kind493 d_ind = L4KDInductive493 info`
     (X_CHOOSE_THEN `d_ind:l4_kdeclaration493` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `l4_core_inductive532 env owner = SOME info` THEN
    REWRITE_TAC [l4_core_inductive532] THEN
    MP_TAC (ISPEC `l4_kfind_decl493 env owner` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_all_dis974])
      (X_CHOOSE_THEN `di:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
    MP_TAC (SPEC `l4_kdecl_kind493 di` (cases "l4_kdecl_kind493")) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
      STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [l4_all_dis974;injectivity "option"])) THEN
    DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `di:l4_kdeclaration493` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?d_ctor. l4_kfind_decl493 env ctor = SOME d_ctor /\
               l4_kdecl_kind493 d_ctor = L4KDConstructor493 c`
     (X_CHOOSE_THEN `d_ctor:l4_kdeclaration493` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `l4_core_constructor532 env ctor = SOME c` THEN
    REWRITE_TAC [l4_core_constructor532] THEN
    MP_TAC (ISPEC `l4_kfind_decl493 env ctor` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC [th;l4_all_dis974])
      (X_CHOOSE_THEN `dc:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
    MP_TAC (SPEC `l4_kdecl_kind493 dc` (cases "l4_kdecl_kind493")) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
      STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [l4_all_dis974;injectivity "option"])) THEN
    DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `dc:l4_kdeclaration493` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_kctor_num_params493 c = l4_kind_num_params493 info /\
      LENGTH (l4_kdecl_params493 d_ctor) = LENGTH (l4_kdecl_params493 d_ind)`
     STRIP_ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_shape973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`owner:l4_name`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
                                `ctor:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`]) THEN
    ASM_REWRITE_TAC [MEM] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 owner a1)) ty'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
     (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 owner a1) h'` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) r'
        (l4_vapps962 args' (L4VConst961 owner us'))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
    ASM_MESON_TAC [l4_vis_defeq_u_symm972];
    ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (args':l4_vexpr961 list) = l4_kind_num_params493 info` ASSUME_TAC THENL
   [SUBGOAL_THEN `?us_s. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
                           (l4_vapps962 args' (L4VConst961 owner us')) (L4VSort961 us_s)`
      (X_CHOOSE_TAC `us_s:l4_vlevel961`) THENL
    [ASM_MESON_TAC [l4_vis_defeq_is_type974;l4_vis_type961;l4_vhas_type961]; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_type_arity973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;
                                `info:l4_kinductive_data493`;`us':l4_vlevel961 list`;
                                `args':l4_vexpr961 list`;`us_s:l4_vlevel961`]) THEN
    ASM_REWRITE_TAC [ADD_CLAUSES];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?ci_i. l4_venv_lookup_const961 venv owner ci_i /\
             l4_vc_uvars961 ci_i = LENGTH (l4_kdecl_params493 d_ind)`
     (X_CHOOSE_THEN `ci_i:l4_vconstant961` STRIP_ASSUME_TAC) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`owner:l4_name`;`d_ind:l4_kdeclaration493`]) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `ci_i:l4_vconstant961 = ci` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [l4_venv_wf_lookup_unique966]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (l4_kdecl_params493 d_ctor)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_struct_eta973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;
                               `info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
                               `d_ctor:l4_kdeclaration493`;`us':l4_vlevel961 list`;
                               `args':l4_vexpr961 list`;`r':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hprojs") (LABEL_TAC "Heta")) THEN
   SUBGOAL_THEN `l4_kfirstn494 (args:l4_kexpr447 list) (l4_kind_num_params493 info) = args`
     (fun th -> ASM_REWRITE_TAC [th]) THENL
   [MATCH_MP_TAC l4_kfirstn_all_ge974 THEN
    SUBGOAL_THEN `LENGTH (args:l4_kexpr447 list) = LENGTH (args':l4_vexpr961 list)`
      (fun th -> ASM_REWRITE_TAC [th;LE_REFL]) THEN
    MATCH_MP_TAC l4_all2_length974 THEN EXISTS_TAC `l4_vtr_expr_s973 env venv ps l` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?ci_c. l4_venv_lookup_const961 venv ctor ci_c /\
             l4_vc_uvars961 ci_c = LENGTH (l4_kdecl_params493 d_ctor)`
     (X_CHOOSE_THEN `ci_c:l4_vconstant961` STRIP_ASSUME_TAC) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`ctor:l4_name`;`d_ctor:l4_kdeclaration493`]) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KConst447 ctor a1) (L4VConst961 ctor us')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `ci_c:l4_vconstant961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [l4_core_project_fields_eq_map_seq974] THEN
   SUBGOAL_THEN
     `ALL2 (l4_vtr_expr973 env venv ps l)
        (MAP (\i. L4KProj447 owner i reduced) (l4_seq973 0 (l4_kctor_num_fields493 c)))
        (MAP (\i. l4_vproj_expr962 owner i us' args' r') (l4_seq973 0 (l4_kctor_num_fields493 c)))`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `!len start. start + len <= l4_kctor_num_fields493 c ==>
         ALL2 (l4_vtr_expr973 env venv ps l)
           (MAP (\i. L4KProj447 owner i reduced) (l4_seq973 start len))
           (MAP (\i. l4_vproj_expr962 owner i us' args' r') (l4_seq973 start len))`
      (fun th -> MATCH_MP_TAC th THEN ARITH_TAC) THEN
    INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC [l4_seq973;MAP;ALL2] THEN
    DISCH_TAC THEN CONJ_TAC THENL
    [USE_THEN "Hprojs" (MP_TAC o SPEC `start:num`) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_TAC `fty:l4_vexpr961`) THEN
     UNDISCH_TAC `l4_vtr_expr973 env venv ps l reduced r'` THEN
     REWRITE_TAC [l4_vtr_expr973] THEN
     DISCH_THEN (X_CHOOSE_THEN `r0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN
       `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) r0
          (l4_vapps962 args' (L4VConst961 owner us'))` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `r':l4_vexpr961` THEN
      MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     UNDISCH_TAC `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner start r' (l4_vproj_expr962 owner start us' args' r') fty` THEN
     REWRITE_TAC [l4_vtr_proj973] THEN
     DISCH_THEN (X_CHOOSE_THEN `info0:l4_kinductive_data493`
       (X_CHOOSE_THEN `ctor0:l4_name`
         (X_CHOOSE_THEN `c0:l4_kconstructor_data493`
           (X_CHOOSE_THEN `d0:l4_kdeclaration493`
             (X_CHOOSE_THEN `us0:l4_vlevel961 list`
               (X_CHOOSE_THEN `ps0:l4_vexpr961 list`
                 (X_CHOOSE_THEN `idxs0:l4_vexpr961 list` STRIP_ASSUME_TAC))))))) THEN
     SUBGOAL_THEN
       `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
          (L4VApp961 (l4_vapps962 ps0 (L4VConst961 (l4_proj_const_name962 owner start) us0)) r') fty`
       ASSUME_TAC THENL
     [REWRITE_TAC [GSYM l4_vproj_expr962] THEN
      POP_ASSUM (fun hty -> POP_ASSUM (fun heq ->
        ASSUME_TAC heq THEN ASSUME_TAC hty THEN
        REWRITE_TAC [GSYM heq] THEN ACCEPT_TAC hty));
      ALL_TAC] THEN
     MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                    `l4_vapps962 ps0 (L4VConst961 (l4_proj_const_name962 owner start) us0)`;
                    `r':l4_vexpr961`;`fty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961` (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
     SUBGOAL_THEN
       `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
          (l4_vproj_expr962 owner start us0 ps0 r0) (l4_vproj_expr962 owner start us0 ps0 r')
          (l4_vinst0961 bp r0)` ASSUME_TAC THENL
     [REWRITE_TAC [l4_vproj_expr962] THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
      EXISTS_TAC `ap:l4_vexpr961` THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC [GSYM l4_vhas_type961];
       MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
       ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
      ALL_TAC] THEN
     REWRITE_TAC [l4_vtr_expr973] THEN
     EXISTS_TAC `l4_vproj_expr962 owner start us0 ps0 r0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN EXISTS_TAC `r0:l4_vexpr961` THEN
      EXISTS_TAC `l4_vinst0961 bp r0` THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       REWRITE_TAC [l4_vtr_proj973] THEN
       MAP_EVERY EXISTS_TAC [`info0:l4_kinductive_data493`;`ctor0:l4_name`;
                             `c0:l4_kconstructor_data493`;`d0:l4_kdeclaration493`;
                             `us0:l4_vlevel961 list`;`ps0:l4_vexpr961 list`;`idxs0:l4_vexpr961 list`] THEN
       REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THENL
       [MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN
        EXISTS_TAC `r':l4_vexpr961` THEN MATCH_MP_TAC l4_vis_defeq_u_of_l972 THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
        MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
        EXISTS_TAC `l4_vproj_expr962 owner start us0 ps0 r'` THEN ASM_REWRITE_TAC []]];
      REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinst0961 bp r0` THEN
      ASM_REWRITE_TAC []];
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN
   EXISTS_TAC
     `l4_vapps962
        (APPEND args'
          (MAP (\i. l4_vproj_expr962 owner i us' args' r')
            (l4_seq973 0 (l4_kctor_num_fields493 c))))
        (L4VConst961 ctor us')` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_kapply973 THEN
    EXISTS_TAC `l4_vapps962 args' (L4VConst961 owner us')` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_all2_append974 THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC []; ASM_REWRITE_TAC []];
     REMOVE_THEN "Heta" (fun th -> ACCEPT_TAC (MATCH_MP l4_vis_defeq_refl_r961 th))];
    REWRITE_TAC [l4_vis_defeq_u961] THEN
    EXISTS_TAC `l4_vapps962 args' (L4VConst961 owner us')` THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN REMOVE_THEN "Heta" ACCEPT_TAC]]);;

let l4_core_to_constructor_sound974 = prove
 (`!env venv ps rec fuel g l owner k_rule value v' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l value v' /\
   l4_core_to_constructor585 rec fuel env g owner k_rule value = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_has_primitives973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973;
                  l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_core_to_constructor585 rec fuel env g owner k_rule value = L4KAccept491 res` THEN
  REWRITE_TAC [l4_core_to_constructor585;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l red v'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`value:l4_kexpr447`;`v':l4_vexpr961`;`red:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!red0. l4_vtr_expr973 env venv ps l red0 v' /\
      (match FST (l4_ksplit_app489 red0) with
       | L4KConst447 n us ->
           (match l4_core_constructor532 env n with
            | SOME info -> L4KAccept491 red0
            | NONE -> l4_core_to_structure585 rec fuel env g owner k_rule red0)
       | _ -> l4_core_to_structure585 rec fuel env g owner k_rule red0) = L4KAccept491 res ==>
      l4_vtr_expr973 env venv ps l res v'` (LABEL_TAC "Hdef") THENL
  [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ABBREV_TAC `hd = FST (l4_ksplit_app489 red0)` THEN
   STRUCT_CASES_TAC (SPEC `hd:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN
   TRY (DISCH_TAC THEN MATCH_MP_TAC l4_core_to_structure_sound974 THEN
        MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                              `owner:l4_name`;`k_rule:bool`;`red0:l4_kexpr447`] THEN
        ASM_REWRITE_TAC [] THEN NO_TAC) THEN
   MP_TAC (ISPEC `l4_core_constructor532 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th] THEN DISCH_TAC THEN
                MATCH_MP_TAC l4_core_to_structure_sound974 THEN
                MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                                      `owner:l4_name`;`k_rule:bool`;`red0:l4_kexpr447`] THEN
                ASM_REWRITE_TAC [])
     (X_CHOOSE_THEN `c0:l4_kconstructor_data493`
       (fun th -> REWRITE_TAC [th;injectivity "l4_kresult491"] THEN
                  DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [])));
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l red v'` THEN
  STRUCT_CASES_TAC (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  TRY (DISCH_THEN (fun htr -> DISCH_THEN (fun heq ->
         REMOVE_THEN "Hdef" (fun hd -> ACCEPT_TAC (MATCH_MP hd (CONJ htr heq))))) THEN NO_TAC) THENL
  [(* NatLit *)
   DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [injectivity "l4_kresult491"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THENL
   [ALL_TAC; ASM_REWRITE_TAC []] THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KNatLit447 a) v'` THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_natlit974) THEN STRIP_TAC THEN
   REWRITE_TAC [l4_core_nat_constructor544] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_nat974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 a) v'` THEN
   STRUCT_CASES_TAC (SPEC `a:num` num_CASES) THEN REWRITE_TAC [NOT_SUC;SUC_SUB1] THEN DISCH_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `L4VConst961 l4_core_zero_name533 []` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `L4VConstant961 0 l4_vnat_ty973` THEN
     ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
     REWRITE_TAC [GSYM l4_nat_lit973] THEN ASM_REWRITE_TAC []];
    REWRITE_TAC [l4_vtr_expr973] THEN
    EXISTS_TAC `L4VApp961 (L4VConst961 l4_core_succ_name533 []) (l4_nat_lit973 n)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `l4_vnat_ty973` THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
      EXISTS_TAC `L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973)` THEN
      ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
      MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
      ASM_REWRITE_TAC [];
      REWRITE_TAC [GSYM l4_nat_lit973] THEN
      MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
      ASM_REWRITE_TAC []];
     REWRITE_TAC [GSYM l4_nat_lit973] THEN ASM_REWRITE_TAC []]];
   (* StrLit *)
   DISCH_TAC THEN REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KStrLit447 a) v'` THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_strlit974) THEN
   DISCH_THEN (X_CHOOSE_THEN `s':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l exp v'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `s':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_core_expand_string974 THEN
    EXISTS_TAC `a:num list` THEN ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`exp:l4_kexpr447`;`v':l4_vexpr961`;`res:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []]]);;

let l4_core_reduce_recursor_sound974 = prove
 (`!env venv ps rec fuel g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_reduce_recursor585 rec fuel env g e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;
                  l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 e)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 e)` THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e'`
    ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN
   ASM_REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_core_reduce_recursor585 rec fuel env g e = L4KAccept491 (SOME e1)` THEN
  REWRITE_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  DISCH_THEN (fun htr -> ASSUME_TAC htr) THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env a0` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
    l4_strip_as_aprime974 th THEN ASM_REWRITE_TAC [l4_all_dis974])) THEN
  ABBREV_TAC `first_idx = l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a'` THEN
  ABBREV_TAC `major_idx = first_idx + l4_krec_num_indices493 a'` THEN
  MP_TAC (ISPEC `l4_nth_error550 (args:l4_kexpr447 list) major_idx` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `major:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (ISPEC `l4_core_major_induct557 major_idx (l4_kdecl_type493 d)` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_kresult_dis974])
    (X_CHOOSE_THEN `owner:l4_name` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `maj1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `ctor = FST (l4_ksplit_app489 maj1)` THEN
  ABBREV_TAC `fields = SND (l4_ksplit_app489 maj1)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 fields ctor = maj1` MP_TAC THENL
  [MAP_EVERY EXPAND_TAC ["ctor";"fields"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  STRUCT_CASES_TAC (SPEC `ctor:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_kresult_dis974;injectivity "l4_kresult491";l4_all_dis974] THEN
  DISCH_TAC THEN
  MP_TAC (ISPEC `l4_core_find_rule557 a0' (l4_krec_rules493 a')` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `rule:l4_krecursor_rule493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (ISPEC `l4_core_constructor532 env a0'` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `ci:l4_kconstructor_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974;injectivity "option"]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;injectivity "option"] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) e'` THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
    (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ADD_ASSOC]) THEN
  SUBGOAL_THEN `?maj'. l4_nth_error550 args' (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a' + l4_krec_num_indices493 a') = SOME maj' /\ l4_vtr_expr_s973 env venv ps l major maj'`
    (X_CHOOSE_THEN `maj':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [MP_TAC (ISPECL [`l4_vtr_expr_s973 env venv ps l`;`SND (l4_ksplit_app489 e)`;`args':l4_vexpr961 list`] l4_all2_nth_error974) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 fields (L4KConst447 a0' a1')) maj'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [MATCH_MP_TAC l4_core_to_constructor_sound974 THEN
   MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                         `l4_kctor_induct493 ci`;`l4_krec_k493 a'`;`major:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `c':l4_vexpr961`
    (X_CHOOSE_THEN `fields':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0' a1') c'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN
    `?rhs_v. l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973
               (l4_krule_rhs493 rule) rhs_v`
    (X_CHOOSE_TAC `rhs_v:l4_vexpr961`) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_recursor_rhs973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`a0:l4_name`;`d:l4_kdeclaration493`;
                                     `a':l4_krecursor_data493`;`rule:l4_krecursor_rule493`]) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_find_rule_mem974 THEN
   EXISTS_TAC `a0':l4_name` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (l4_kdecl_params493 d)` ASSUME_TAC THENL
  [SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (a1:l4_klevel447 list)`
     (fun th -> ASM_REWRITE_TAC [th]) THEN
   MATCH_MP_TAC l4_tr_ls_length967 THEN EXISTS_TAC `ps:l4_name list` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (fields':l4_vexpr961 list) = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `LENGTH (fields:l4_kexpr447 list) = LENGTH (fields':l4_vexpr961 list)`
     (fun th -> ASM_REWRITE_TAC [GSYM th]) THEN
   MATCH_MP_TAC l4_all2_length974 THEN EXISTS_TAC `l4_vtr_expr_s973 env venv ps l` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (l4_vapps962 args' (L4VConst961 a0 us'))
       (l4_vapps962
         (APPEND (l4_kfirstn494 args' (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a'))
           (APPEND (l4_skip550 fields' (l4_kctor_num_params493 ci))
             (l4_skip550 args' (SUC (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a' + l4_krec_num_indices493 a')))))
         (l4_vinstL961 us' rhs_v))` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_recursor_iota973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;`d:l4_kdeclaration493`;
      `a':l4_krecursor_data493`;`us':l4_vlevel961 list`;`args':l4_vexpr961 list`;
      `maj':l4_vexpr961`;`l4_kctor_induct493 ci`;`a0':l4_name`;`ci:l4_kconstructor_data493`;
      `us'':l4_vlevel961 list`;`fields':l4_vexpr961 list`;`rule:l4_krecursor_rule493`;`rhs_v:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [ADD_ASSOC] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ASM_ARITH_TAC;
    MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `e':l4_vexpr961` THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps l
       (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 (l4_krule_rhs493 rule))
       (l4_vinstL961 us' rhs_v)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_closed_to_any973 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_subst_levels973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN
  EXISTS_TAC
    `l4_vapps962
       (APPEND (l4_kfirstn494 args' (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a'))
         (APPEND (l4_skip550 fields' (l4_kctor_num_params493 ci))
           (l4_skip550 args' (SUC (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a' + l4_krec_num_indices493 a')))))
       (l4_vinstL961 us' rhs_v)` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [SUBGOAL_THEN
     `?ty_r. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
               (l4_vapps962
                 (APPEND (l4_kfirstn494 args' (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a'))
                   (APPEND (l4_skip550 fields' (l4_kctor_num_params493 ci))
                     (l4_skip550 args' (SUC (l4_krec_num_params493 a' + l4_krec_num_motives493 a' + l4_krec_num_minors493 a' + l4_krec_num_indices493 a')))))
                 (l4_vinstL961 us' rhs_v)) ty_r`
     (X_CHOOSE_TAC `ty_r:l4_vexpr961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_r973 THEN
    EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_r:l4_vexpr961` THEN
   ASM_REWRITE_TAC [ADD_ASSOC] THEN
   MATCH_MP_TAC l4_all2_append974 THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_all2_firstn973 THEN MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_all2_append974 THEN CONJ_TAC THENL
    [MATCH_MP_TAC (REWRITE_RULE [RIGHT_IMP_FORALL_THM] l4_all2_skip974) THEN
     MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC (REWRITE_RULE [RIGHT_IMP_FORALL_THM] l4_all2_skip974) THEN
     MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC []]];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []]);;

(* 3f. Projection reduction (`l4_core_reduce_proj_core595`, `l4_core_reduce_projection_with550`, `l4_core_reduce_head594`) *)
let l4_core_reduce_proj_core_sound974 = prove
 (`!env venv ps l owner idx val_e val' pv fty fval.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l val_e val' /\
   l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner idx val' pv fty /\
   l4_core_reduce_proj_core595 env idx val_e = SOME fval ==>
   ?fval'.
     l4_vtr_expr973 env venv ps l fval fval' /\
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) pv fval'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vl_ctx_wf_to_vctx_wf973]; ALL_TAC] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 val_e)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 val_e)` THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) val'`
    ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN
   ASM_REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_core_reduce_proj_core595 env idx val_e = SOME fval` THEN
  REWRITE_TAC [l4_core_reduce_proj_core595;LET_DEF;LET_END_DEF] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  DISCH_THEN (fun htr -> ASSUME_TAC htr) THEN
  MP_TAC (ISPEC `l4_core_constructor532 env a0` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `ci:l4_kconstructor_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) val'` THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
    (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN
    `?fval'. l4_nth_error550 args' (l4_kctor_num_params493 ci + idx) = SOME fval' /\
             l4_vtr_expr_s973 env venv ps l fval fval'`
    (X_CHOOSE_THEN `fval':l4_vexpr961` STRIP_ASSUME_TAC) THENL
  [MP_TAC (ISPECL [`l4_vtr_expr_s973 env venv ps l`;`SND (l4_ksplit_app489 val_e)`;`args':l4_vexpr961 list`] l4_all2_nth_error974) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner idx val' pv fty` THEN
  REWRITE_TAC [l4_vtr_proj973] THEN
  DISCH_THEN (X_CHOOSE_THEN `info:l4_kinductive_data493`
    (X_CHOOSE_THEN `ctor:l4_name`
      (X_CHOOSE_THEN `c:l4_kconstructor_data493`
        (X_CHOOSE_THEN `d:l4_kdeclaration493`
          (X_CHOOSE_THEN `us:l4_vlevel961 list`
            (X_CHOOSE_THEN `ps_e:l4_vexpr961 list`
              (X_CHOOSE_THEN `idxs:l4_vexpr961 list` STRIP_ASSUME_TAC))))))) THEN
  UNDISCH_TAC `pv = l4_vproj_expr962 owner idx us ps_e val'` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (args':l4_vexpr961 list) = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `LENGTH (SND (l4_ksplit_app489 val_e)) = LENGTH (args':l4_vexpr961 list)`
     (fun th -> ASM_REWRITE_TAC [GSYM th]) THEN
   MATCH_MP_TAC l4_all2_length974 THEN EXISTS_TAC `l4_vtr_expr_s973 env venv ps l` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?tc. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
            (l4_vapps962 args' (L4VConst961 a0 us')) tc`
    (X_CHOOSE_TAC `tc:l4_vexpr961`) THENL
  [ASM_MESON_TAC [l4_vis_defeq_u_has_type_l973]; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ctor_type_head973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                              `a0:l4_name`;`ci:l4_kconstructor_data493`;
                              `us':l4_vlevel961 list`;`args':l4_vexpr961 list`;`tc:l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `oinfo:l4_kinductive_data493`
    (X_CHOOSE_THEN `oidxs:l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (l4_vapps962 (APPEND (l4_kfirstn494 args' (l4_kctor_num_params493 ci)) oidxs)
         (L4VConst961 (l4_kctor_induct493 ci) us'))
       (l4_vapps962 (APPEND ps_e idxs) (L4VConst961 owner us))` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 args' (L4VConst961 a0 us')) val'` THEN
   DISCH_THEN (X_CHOOSE_TAC `tv:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tc tv` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`l4_vapps962 args' (L4VConst961 a0 us')`;
                          `l4_vapps962 args' (L4VConst961 a0 us')`;
                          `l4_vapps962 args' (L4VConst961 a0 us')`] THEN
    ASM_MESON_TAC [l4_vhas_type961;l4_vis_defeq_refl_l961];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tv
        (l4_vapps962 (APPEND ps_e idxs) (L4VConst961 owner us))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`val':l4_vexpr961`;`val':l4_vexpr961`] THEN
    ASM_MESON_TAC [l4_vhas_type961;l4_vis_defeq_refl_r961];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `tc:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [ASM_MESON_TAC [l4_vis_defeq_u_symm972];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `tv:l4_vexpr961` THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_kctor_induct493 ci = owner` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_inj973) THEN
   ASM_REWRITE_TAC [l4_vind_head_inj973] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
      `l4_kctor_induct493 ci`;`owner:l4_name`;`oinfo:l4_kinductive_data493`;`info:l4_kinductive_data493`;
      `us':l4_vlevel961 list`;`us:l4_vlevel961 list`;
      `APPEND (l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 ci)) (oidxs:l4_vexpr961 list)`;
      `APPEND ps_e idxs:l4_vexpr961 list`]) THEN
   ASM_REWRITE_TAC [] THEN MESON_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?d_ind. l4_kfind_decl493 env owner = SOME d_ind /\
             l4_kdecl_kind493 d_ind = L4KDInductive493 info`
    (X_CHOOSE_THEN `d_ind:l4_kdeclaration493` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `l4_core_inductive532 env owner = SOME info` THEN
   REWRITE_TAC [l4_core_inductive532] THEN
   MP_TAC (ISPEC `l4_kfind_decl493 env owner` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `di:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (SPEC `l4_kdecl_kind493 di` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [l4_all_dis974;injectivity "option"])) THEN
   DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `di:l4_kdeclaration493` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?d_cn. l4_kfind_decl493 env a0 = SOME d_cn /\
            l4_kdecl_kind493 d_cn = L4KDConstructor493 ci`
    (X_CHOOSE_THEN `d_cn:l4_kdeclaration493` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `l4_core_constructor532 env a0 = SOME ci` THEN
   REWRITE_TAC [l4_core_constructor532] THEN
   MP_TAC (ISPEC `l4_kfind_decl493 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `dc:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (SPEC `l4_kdecl_kind493 dc` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [l4_all_dis974;injectivity "option"])) THEN
   DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `dc:l4_kdeclaration493` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `a0:l4_name = ctor /\ l4_kctor_num_params493 ci = l4_kind_num_params493 info`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_shape973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`owner:l4_name`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
                               `a0:l4_name`;`ci:l4_kconstructor_data493`;`d_cn:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [MEM] THEN MESON_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `d_cn:l4_kdeclaration493 = d` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `ci:l4_kconstructor_data493 = c` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "l4_kdecl_kind493"]; ALL_TAC] THEN
  EXISTS_TAC `fval':l4_vexpr961` THEN CONJ_TAC THENL
  [ASM_MESON_TAC [l4_vtr_expr_s_to_vtr_expr973];
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_proj_iota973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;`info:l4_kinductive_data493`;
      `ctor:l4_name`;`c:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`idx:num`;
      `us:l4_vlevel961 list`;`us':l4_vlevel961 list`;`ps_e:l4_vexpr961 list`;`idxs:l4_vexpr961 list`;
      `args':l4_vexpr961 list`;`fval':l4_vexpr961`;`val':l4_vexpr961`]) THEN
   ASM_MESON_TAC [l4_vis_defeq_u_symm972]]);;

let l4_core_reduce_projection_with_sound974 = prove
 (`!env venv ps chk rec reduce g l owner idx val_e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   (!g0 l0 a a' a1.
     l4_vtr_ctx973 env venv ps g0 l0 /\
     l4_vtr_expr973 env venv ps l0 a a' /\
     reduce g0 a = L4KAccept491 a1 ==>
     l4_vtr_expr973 env venv ps l0 a1 a') /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l (L4KProj447 owner idx val_e) e' /\
   l4_core_reduce_projection_with550 rec reduce env g owner idx val_e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KProj447 owner idx val_e) e'` THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_proj974) THEN
  DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961`
    (X_CHOOSE_THEN `pv:l4_vexpr961`
      (X_CHOOSE_THEN `fty:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `l4_core_reduce_projection_with550 rec reduce env g owner idx (val_e:l4_kexpr447) = L4KAccept491 (SOME e1)` THEN
  REWRITE_TAC [l4_core_reduce_projection_with550;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `r1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r2:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Hr2") (LABEL_TAC "Hproj"))))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l r1 val'` ASSUME_TAC THENL
  [FIRST_ASSUM (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`val_e:l4_kexpr447`;`val':l4_vexpr961`;`r1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l r2 val'` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vtr_expr973 env venv ps l r1 val'` THEN
   REMOVE_THEN "Hr2" MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `r1:l4_kexpr447` (cases "l4_kexpr447")) THEN
   TRY (REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        DISCH_THEN ACCEPT_TAC THEN NO_TAC) THEN
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` STRIP_ASSUME_TAC) THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_strlit974) THEN
   DISCH_THEN (X_CHOOSE_THEN `s':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l exp val'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `s':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_core_expand_string974 THEN
    EXISTS_TAC `a:num list` THEN ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`exp:l4_kexpr447`;`val':l4_vexpr961`;`r2:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_reduce_proj_core595 env idx r2 = SOME e1` ASSUME_TAC THENL
  [REMOVE_THEN "Hproj" MP_TAC THEN REWRITE_TAC [l4_core_reduce_proj_core595;LET_DEF;LET_END_DEF] THEN
   ABBREV_TAC `hd = FST (l4_ksplit_app489 r2)` THEN
   ABBREV_TAC `args = SND (l4_ksplit_app489 r2)` THEN
   SUBGOAL_THEN `l4_ksplit_app489 r2 = (hd, args)` (fun th -> REWRITE_TAC [th;FST;SND]) THENL
   [MAP_EVERY EXPAND_TAC ["hd";"args"] THEN REWRITE_TAC [PAIR]; ALL_TAC] THEN
   STRUCT_CASES_TAC (SPEC `hd:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN
   MP_TAC (ISPEC `l4_core_constructor532 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `ci:l4_kconstructor_data493` (fun th -> REWRITE_TAC [th]))) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REMOVE_THEN "Hproj" (K ALL_TAC) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`owner:l4_name`;`idx:num`;`r2:l4_kexpr447`;
                 `val':l4_vexpr961`;`pv:l4_vexpr961`;`fty:l4_vexpr961`;`e1:l4_kexpr447`]
    l4_core_reduce_proj_core_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `fv':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `fv':l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv:l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []);;

let l4_core_reduce_head_sound974 = prove
 (`!env venv ps rec fuel g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_reduce_head594 rec fuel env g e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_reduce_head594;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `nat_res:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MP_TAC (ISPEC `nat_res:l4_kexpr447 option` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `a:l4_kexpr447` SUBST_ALL_TAC)) THENL
  [REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `quot_res:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   MP_TAC (ISPEC `quot_res:l4_kexpr447 option` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `b:l4_kexpr447` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_core_reduce_recursor_sound974 THEN
    MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_all_dis974;injectivity "option"] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_core_reduce_quotient_sound974 THEN
    MAP_EVERY EXISTS_TAC [`T`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
    ASM_REWRITE_TAC []];
   REWRITE_TAC [l4_all_dis974;injectivity "option"] THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   MATCH_MP_TAC l4_core_reduce_nat_sound974 THEN
   MAP_EVERY EXISTS_TAC [`T`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 4. WHNF Soundness (`whnf_core_step`, `whnf_round_step`, `whnf_loop`)      *)
(* ========================================================================= *)

let l4_whnf_core_step_sound974 = prove
 (`!env venv ps rec fuel cheap g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf_core_step594 rec fuel env ps cheap g e = L4KAccept491 e1 ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;
                  l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l e e'` THEN
  UNDISCH_TAC `l4_whnf_core_step594 rec fuel env ps cheap g e = L4KAccept491 e1` THEN
  REWRITE_TAC [l4_whnf_core_step594] THEN
  STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THENL
  [(* L4KBVar447 a *)
   MP_TAC (ISPEC `l4_nth_error550 (l4_kcontext_bound532 g) a` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (ISPEC `l4_kbinding_value532 b` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;injectivity "l4_kresult491"] THEN
                DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC)
     (X_CHOOSE_THEN `v:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   DISCH_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:num`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_bound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `eb':l4_vexpr961` (X_CHOOSE_THEN `tyb':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KBVar447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KBVar447 a) e0` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN `eb':l4_vexpr961 = e0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_klift447 v (SUC a) 0) e'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `e0:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
      l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `l4_klift447 v (SUC a) 0`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   (* L4KFVar447 a *)
   MP_TAC (ISPEC `l4_kfind_free532 a (l4_kcontext_free532 g)` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (ISPEC `l4_kbinding_value532 b` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;injectivity "l4_kresult491"] THEN
                DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC)
     (X_CHOOSE_THEN `v:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   DISCH_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_name`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_free974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ef':l4_vexpr961` (X_CHOOSE_THEN `tyf':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KFVar447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KFVar447 a) e0` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN `ef':l4_vexpr961 = e0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l v e'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `e0:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
      l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `v:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   (* L4KSort447 a *)
   REWRITE_TAC [l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
   DISCH_THEN ACCEPT_TAC;
   (* L4KConst447 a0 a1 *)
   REWRITE_TAC [l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:l4_kdeclaration493` (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
   DISCH_THEN ACCEPT_TAC;
   (* L4KApp447 a0 a1 *)
   REWRITE_TAC [LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
   ABBREV_TAC `head = FST (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
   ABBREV_TAC `args = SND (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
   DISCH_THEN (X_CHOOSE_THEN `fn:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hfn_m"))) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `l4_kapply_exprs489 args head = L4KApp447 a0 a1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args head) e'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961`
     (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l fn h'` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
      l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `head:l4_kexpr447`;`h':l4_vexpr961`;`fn:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args fn) e'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `l4_vapps962 args' h'` THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 args' h') e'` THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN DISCH_THEN (X_CHOOSE_TAC `ty_ap:l4_vexpr961`) THEN
    MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_ap:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
     EXISTS_TAC `e':l4_vexpr961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!fn0.
       l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args fn0) e' /\
       l4_kr_bind491 (l4_core_reduce_quotient550 rec env g (l4_kapply_exprs489 args fn0))
         (\quot.
            l4_kr_bind491
              (match quot with
               | SOME value -> L4KAccept491 (SOME value)
               | NONE -> l4_core_reduce_recursor585 rec fuel env g (l4_kapply_exprs489 args fn0))
              (\step.
                 match step with
                 | SOME value -> l4_whnf_core_method543 rec cheap g value
                 | NONE -> L4KAccept491 (l4_kapply_exprs489 args fn0))) = L4KAccept491 e1 ==>
       l4_vtr_expr973 env venv ps l e1 e'` (LABEL_TAC "Hnonlam") THENL
   [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [l4_kr_bind_accept967] THEN
    DISCH_THEN (X_CHOOSE_THEN `quot:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `step:l4_kexpr447 option` (fun th -> MP_TAC (CONJUNCT2 th) THEN MP_TAC (CONJUNCT1 th))))) THEN
    MP_TAC (ISPEC `quot:l4_kexpr447 option` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `qv:l4_kexpr447` SUBST_ALL_TAC)) THENL
    [REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
     MP_TAC (ISPEC `step:l4_kexpr447 option` (cases "option")) THEN
     DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rv:l4_kexpr447` SUBST_ALL_TAC)) THENL
     [REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [];
      REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
      SUBGOAL_THEN `l4_vtr_expr973 env venv ps l rv e'` ASSUME_TAC THENL
      [MATCH_MP_TAC l4_core_reduce_recursor_sound974 THEN
       MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                             `l4_kapply_exprs489 args fn0`] THEN
       ASM_REWRITE_TAC [];
       MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
         l4_fms_whnf_core974) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                         `rv:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
       ASM_REWRITE_TAC []]];
     REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
     REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
     SUBGOAL_THEN `l4_vtr_expr973 env venv ps l qv e'` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_core_reduce_quotient_sound974 THEN
      MAP_EVERY EXISTS_TAC [`T`;`rec:l4_kmethods543`;`g:l4_kcontext532`;
                            `l4_kapply_exprs489 args fn0`] THEN
      ASM_REWRITE_TAC [];
      MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
        l4_fms_whnf_core974) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                        `qv:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
      ASM_REWRITE_TAC []]];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args fn) e'` THEN
   REMOVE_THEN "Hfn_m" MP_TAC THEN
   STRUCT_CASES_TAC (SPEC `fn:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974;LET_DEF;LET_END_DEF] THEN
   TRY (DISCH_THEN (fun h1 -> DISCH_THEN (fun h2 ->
          REMOVE_THEN "Hnonlam" (fun hn -> ACCEPT_TAC (MATCH_MP hn (CONJ h2 h1))))) THEN NO_TAC) THEN
   (* L4KLam447 *)
   DISCH_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kcore_beta526 (L4KLam447 a0' a1' a2 a3) args) e'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_core_beta_sound974 THEN ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
      l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `l4_kcore_beta526 (L4KLam447 a0' a1' a2 a3) args`;
                                      `e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   (* L4KLam447 *)
   DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC;
   (* L4KPi447 *)
   DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC;
   (* L4KLet447 *)
   DISCH_TAC THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_let974) THEN
   DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961`
     (X_CHOOSE_THEN `val':l4_vexpr961`
       (X_CHOOSE_THEN `body':l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kinst447 a3 a2) e'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `body':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_instantiate_let973 THEN
    MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`val':l4_vexpr961`] THEN ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
      l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `l4_kinst447 a3 a2`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   (* L4KNatLit447 *)
   DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC;
   (* L4KStrLit447 *)
   REWRITE_TAC [l4_kr_bind_accept967;injectivity "l4_kresult491"] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:l4_kexpr447` (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
   DISCH_THEN ACCEPT_TAC;
   (* L4KProj447 a0 a1 a2 *)
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `step:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   MP_TAC (ISPEC `step:l4_kexpr447 option` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `sel:l4_kexpr447` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN ACCEPT_TAC;
    REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `l4_vtr_expr973 env venv ps l sel e'` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_core_reduce_projection_with_sound974 THEN
     MAP_EVERY EXISTS_TAC
       [`T`;`rec:l4_kmethods543`;
        `if cheap then l4_whnf_core_method543 rec T else l4_whnf_method543 rec`;
        `g:l4_kcontext532`;`a0:l4_name`;`a1:num`;`a2:l4_kexpr447`] THEN
     ASM_REWRITE_TAC [] THEN
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN STRIP_TAC THENL
     [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
        l4_fms_whnf_core974) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g0:l4_kcontext532`;`l0:l4_vl_ctx_rec973`;
                                        `a:l4_kexpr447`;`a':l4_vexpr961`;`a1:l4_kexpr447`]) THEN
      ASM_REWRITE_TAC [];
      MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
        l4_fms_whnf974) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MATCH_MP_TAC o SPECL [`g0:l4_kcontext532`;`l0:l4_vl_ctx_rec973`;
                                        `a:l4_kexpr447`;`a':l4_vexpr961`;`a1:l4_kexpr447`]) THEN
      ASM_REWRITE_TAC []];
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
       l4_fms_whnf_core974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                       `sel:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
     ASM_REWRITE_TAC []]];
   (* L4KMData447 a *)
   DISCH_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP l4_vtr_expr_inv_mdata974) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
     l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`cheap:bool`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC []]);;

let l4_whnf_round_dis974 = l4_distinct_all974 "l4_whnf_round543";;

let l4_finish_whnf_unfold_sound974 = prove
 (`!env venv ps l e e' r.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_finish_whnf_unfold594 env ps e = L4KAccept491 r ==>
   l4_vtr_expr973 env venv ps l
     (match r with | L4WhnfDone543 v -> v | L4WhnfContinue543 v -> v) e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_finish_whnf_unfold594;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `unf:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MP_TAC (ISPEC `unf:l4_kexpr447 option` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `uv:l4_kexpr447` SUBST_ALL_TAC)) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_whnf_round_dis974] THENL
  [ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `e:l4_kexpr447` THEN ASM_REWRITE_TAC []]);;

let l4_whnf_round_step_sound974 = prove
 (`!env venv ps rec fuel g l e e' r.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 r ==>
   l4_vtr_expr973 env venv ps l
     (match r with | L4WhnfDone543 v -> v | L4WhnfContinue543 v -> v) e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_has_primitives973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973;l4_vtr_ctx_to_vl_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 r` THEN
  REWRITE_TAC [l4_whnf_round_step594;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hred_m"))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l red e'` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_whnf_core_step_sound974 THEN
   MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`F`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!red0. l4_vtr_expr973 env venv ps l red0 e' /\
      l4_kr_bind491 (l4_core_reduce_native549 red0)
        (\nat_hook.
           match nat_hook with
           | SOME value -> L4KAccept491 (L4WhnfDone543 value)
           | NONE ->
               l4_kr_bind491 (l4_core_reduce_nat549 rec fuel env g red0)
                 (\native.
                    match native with
                    | SOME value -> L4KAccept491 (L4WhnfDone543 value)
                    | NONE -> l4_finish_whnf_unfold594 env ps red0)) = L4KAccept491 r ==>
      l4_vtr_expr973 env venv ps l
        (match r with | L4WhnfDone543 v -> v | L4WhnfContinue543 v -> v) e'`
    (LABEL_TAC "Hnonconst") THENL
  [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `nh:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   MP_TAC (ISPEC `nh:l4_kexpr447 option` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nhv:l4_kexpr447` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
    DISCH_THEN (X_CHOOSE_THEN `nat:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (ISPEC `nat:l4_kexpr447 option` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nv:l4_kexpr447` SUBST_ALL_TAC)) THENL
    [REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN MATCH_MP_TAC l4_finish_whnf_unfold_sound974 THEN
     EXISTS_TAC `red0:l4_kexpr447` THEN ASM_REWRITE_TAC [];
     REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [l4_whnf_round_dis974] THEN MATCH_MP_TAC l4_core_reduce_nat_sound974 THEN
     MAP_EVERY EXISTS_TAC [`T`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`red0:l4_kexpr447`] THEN
     ASM_REWRITE_TAC []];
    DISCH_TAC THEN MP_TAC (SPECL [`red0:l4_kexpr447`;`nhv:l4_kexpr447`] l4_core_reduce_native_sound974) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l red e'` THEN
  REMOVE_THEN "Hred_m" MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  TRY (DISCH_THEN (fun h1 -> DISCH_THEN (fun h2 ->
         REMOVE_THEN "Hnonconst" (fun hn -> ACCEPT_TAC (MATCH_MP hn (CONJ h2 h1))))) THEN NO_TAC) THEN
  (* L4KConst447 a0 a1 *)
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_whnf_round_dis974] THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_const973) THEN
   DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list`
     (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_nat974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   SUBGOAL_THEN `ci = L4VConstant961 0 l4_vnat_ty973` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`l4_core_zero_name533`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `us':l4_vlevel961 list = []` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `LENGTH (us':l4_vlevel961 list) = l4_vc_uvars961 (L4VConstant961 0 l4_vnat_ty973)` THEN
    REWRITE_TAC [l4_vc_uvars961;LENGTH_EQ_NIL];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `l4_nat_lit973 0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_nat_lit973] THEN ASM_REWRITE_TAC []];
   DISCH_TAC THEN DISCH_TAC THEN MATCH_MP_TAC l4_finish_whnf_unfold_sound974 THEN
   EXISTS_TAC `L4KConst447 a0 a1` THEN ASM_REWRITE_TAC []]);;

let l4_whnf_loop_sound974 = prove
 (`!rounds env venv ps rec fuel g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf_loop594 rounds rec fuel env ps g e = L4KAccept491 e1 ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  INDUCT_TAC THEN REWRITE_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_all_dis974] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `rnd:l4_whnf_round543` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                 `l:l4_vl_ctx_rec973`;`e:l4_kexpr447`;`e':l4_vexpr961`;`rnd:l4_whnf_round543`]
    l4_whnf_round_step_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPEC `rnd:l4_whnf_round543` (cases "l4_whnf_round543")) THEN
  DISCH_THEN (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:l4_kexpr447` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `v:l4_kexpr447` SUBST_ALL_TAC)) THEN
  REWRITE_TAC [l4_whnf_round_dis974;injectivity "l4_kresult491"] THENL
  [DISCH_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [];
   DISCH_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`v:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [l4_whnf_loop594]]);;

let l4_whnf_step_sound974 = prove
 (`!env venv ps rec fuel g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf_step594 rec fuel env ps g e = L4KAccept491 e1 ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_has_primitives973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_prims973;l4_vtr_ctx_to_vl_wf973];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_whnf_step594 rec fuel env ps g e = L4KAccept491 e1` THEN
  REWRITE_TAC [l4_whnf_step594;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hred_m"))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l red e'` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_whnf_core_step_sound974 THEN
   MAP_EVERY EXISTS_TAC [`rec:l4_kmethods543`;`fuel:num`;`F`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!red0. l4_vtr_expr973 env venv ps l red0 e' /\
      l4_kr_bind491 (l4_core_reduce_native549 red0)
        (\nat_hook.
           match nat_hook with
           | SOME value -> L4KAccept491 value
           | NONE ->
               l4_kr_bind491 (l4_core_reduce_nat549 rec fuel env g red0)
                 (\native.
                    match native with
                    | SOME value -> L4KAccept491 value
                    | NONE ->
                        l4_kr_bind491 (l4_core_unfold528 env ps red0)
                          (\unfolded.
                             match unfolded with
                             | SOME value -> l4_whnf_method543 rec g value
                             | NONE -> L4KAccept491 red0))) = L4KAccept491 e1 ==>
      l4_vtr_expr973 env venv ps l e1 e'`
    (LABEL_TAC "Hnonconst") THENL
  [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `nh:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   MP_TAC (ISPEC `nh:l4_kexpr447 option` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nhv:l4_kexpr447` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
    DISCH_THEN (X_CHOOSE_THEN `nat:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (ISPEC `nat:l4_kexpr447 option` (cases "option")) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nv:l4_kexpr447` SUBST_ALL_TAC)) THENL
    [REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
     DISCH_THEN (X_CHOOSE_THEN `unf:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
     MP_TAC (ISPEC `unf:l4_kexpr447 option` (cases "option")) THEN
     DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `uv:l4_kexpr447` SUBST_ALL_TAC)) THENL
     [REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [];
      REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
      SUBGOAL_THEN `l4_vtr_expr973 env venv ps l uv e'` ASSUME_TAC THENL
      [MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `red0:l4_kexpr447` THEN ASM_REWRITE_TAC [];
       MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
         l4_fms_whnf974) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                         `uv:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
       ASM_REWRITE_TAC []]];
     REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
     MATCH_MP_TAC l4_core_reduce_nat_sound974 THEN
     MAP_EVERY EXISTS_TAC [`T`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`red0:l4_kexpr447`] THEN
     ASM_REWRITE_TAC []];
    DISCH_TAC THEN MP_TAC (SPECL [`red0:l4_kexpr447`;`nhv:l4_kexpr447`] l4_core_reduce_native_sound974) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps l red e'` THEN
  REMOVE_THEN "Hred_m" MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  TRY (DISCH_THEN (fun h1 -> DISCH_THEN (fun h2 ->
         REMOVE_THEN "Hnonconst" (fun hn -> ACCEPT_TAC (MATCH_MP hn (CONJ h2 h1))))) THEN NO_TAC) THEN
  (* L4KConst447 a0 a1 *)
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
   DISCH_THEN (MP_TAC o MATCH_MP l4_vtr_expr_inv_const973) THEN
   DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list`
     (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_nat974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   SUBGOAL_THEN `ci = L4VConstant961 0 l4_vnat_ty973` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`l4_core_zero_name533`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `us':l4_vlevel961 list = []` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `LENGTH (us':l4_vlevel961 list) = l4_vc_uvars961 (L4VConstant961 0 l4_vnat_ty973)` THEN
    REWRITE_TAC [l4_vc_uvars961;LENGTH_EQ_NIL];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `l4_nat_lit973 0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_nat_lit973] THEN ASM_REWRITE_TAC []];
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `unf:l4_kexpr447 option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   MP_TAC (ISPEC `unf:l4_kexpr447 option` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `uv:l4_kexpr447` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN ACCEPT_TAC;
    REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `l4_vtr_expr973 env venv ps l uv e'` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `L4KConst447 a0 a1` THEN ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`T`;`rec:l4_kmethods543`]
       l4_fms_whnf974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                       `uv:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
     ASM_REWRITE_TAC []]]]);;

(* ========================================================================= *)
(* 5. Type Inference Soundness (`core_apply_type`, `projection_field`,       *)
(*    `core_infer_projection`, `infer_step_sound_true/false`)                *)
(* ========================================================================= *)

let l4_subst_cases_tac974 th =
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) th;;

let l4_ctx_wf_tac974 =
  let use1 th = FIRST_ASSUM (fun h -> ACCEPT_TAC (MATCH_MP th h)) in
  REPEAT CONJ_TAC THEN
  (use1 l4_ves_wf973 ORELSE
   use1 l4_ves_inj973 ORELSE
   use1 l4_ves_prims973 ORELSE
   use1 l4_vtr_ctx_to_vl_wf973 ORELSE
   use1 l4_vtr_ctx_to_vctx_wf973 ORELSE
   FIRST_ASSUM (fun h -> ACCEPT_TAC (MATCH_MP l4_venv_wf_closed966 (MATCH_MP l4_ves_wf973 h))));;

let l4_vis_defeq_u_has_type_right974 = prove
 (`!env uvars g e1 e2 ty.
   l4_venv_wf966 env /\
   l4_defeq_injectivity972 env /\
   l4_vctx_wf966 env uvars g /\
   l4_vhas_type961 env uvars g e1 ty /\
   l4_vis_defeq_u961 env uvars g e1 e2 ==>
   l4_vhas_type961 env uvars g e2 ty`,
  REWRITE_TAC [l4_vhas_type961;l4_vis_defeq_u961] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 env uvars g ty ty' (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
   MAP_EVERY EXISTS_TAC [`e1:l4_vexpr961`;`e1:l4_vexpr961`;`e2:l4_vexpr961`] THEN
   ASM_REWRITE_TAC [];
   REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `e1:l4_vexpr961` THEN
   MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []]);;

let l4_ksubst_level_nil974 = prove
 (`!us u. l4_ksubst_level488 [] us u = u`,
  GEN_TAC THEN MATCH_MP_TAC l4_klevel_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_level488;l4_klookup_level488] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_ksubst_levels_nil974 = prove
 (`!us e. l4_ksubst_levels488 [] us e = e`,
  GEN_TAC THEN MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_levels488;l4_ksubst_level_nil974] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  AP_TERM_TAC THEN SPEC_TAC (`a1:l4_klevel447 list`,`vs:l4_klevel447 list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_ksubst_level_nil974] THEN ASM_REWRITE_TAC []);;

let l4_list_split_at974 = prove
 (`!m (xs:A list) n.
   LENGTH xs = m + n ==>
   ?p q. APPEND p q = xs /\ l4_kfirstn494 xs m = p /\ LENGTH p = m /\ LENGTH q = n`,
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:A list`;`xs:A list`] THEN
   ASM_REWRITE_TAC [APPEND;LENGTH;ADD;l4_kfirstn494_zero974];
   GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xs:A list` list_CASES) THEN
   REWRITE_TAC [LENGTH;ADD;NOT_SUC;SUC_INJ] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`t:A list`;`n:num`]) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `p:A list` (X_CHOOSE_THEN `q:A list` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`CONS (h:A) p`;`q:A list`] THEN
   ASM_REWRITE_TAC [APPEND;LENGTH;l4_kfirstn494;NOT_SUC;SUC_SUB1]]);;

let l4_vl_ctx_defeq_push_lam974 = prove
 (`!env uvars l a1 a2 u.
   l4_venv_wf966 env /\
   l4_vl_ctx_wf973 env uvars l /\
   l4_vis_defeq961 env uvars (l4_vl_ctx973 l) a1 a2 (L4VSort961 u) ==>
   l4_vl_ctx_defeq973 env uvars (l4_vl_push_lam973 l a1) (l4_vl_push_lam973 l a2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l:l4_vl_ctx_rec973`] l4_vl_ctx_defeq_refl973) THEN
  ASM_REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_lam973;l4_vl_free973;l4_vl_bound973] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC (el 1 (CONJUNCTS l4_vl_entries_defeq_RULES973)) THEN
  EXISTS_TAC `u:l4_vlevel961` THEN
  ASM_REWRITE_TAC [GSYM l4_vl_ctx973]);;

let l4_vl_ctx_defeq_push_let974 = prove
 (`!env uvars l ty1 ty2 v1 v2 u.
   l4_venv_wf966 env /\
   l4_vl_ctx_wf973 env uvars l /\
   l4_vis_defeq961 env uvars (l4_vl_ctx973 l) ty1 ty2 (L4VSort961 u) /\
   l4_vis_defeq961 env uvars (l4_vl_ctx973 l) v1 v2 ty1 ==>
   l4_vl_ctx_defeq973 env uvars (l4_vl_push_let973 l ty1 v1) (l4_vl_push_let973 l ty2 v2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`l:l4_vl_ctx_rec973`] l4_vl_ctx_defeq_refl973) THEN
  ASM_REWRITE_TAC [l4_vl_ctx_defeq973;l4_vl_push_let973;l4_vl_free973;l4_vl_bound973] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC (el 2 (CONJUNCTS l4_vl_entries_defeq_RULES973)) THEN
  EXISTS_TAC `u:l4_vlevel961` THEN
  ASM_REWRITE_TAC [GSYM l4_vl_ctx973]);;

let l4_projection_verify_prop_sound974 = prove
 (`!env venv ps chk rec fuel g l dom dom' ign.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l dom dom' /\
   l4_projection_verify_prop577 rec fuel g dom = L4KAccept491 ign ==>
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) dom' (L4VSort961 L4VLZero961)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_projection_verify_prop577;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `du:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `dom:l4_kexpr447`;`dom':l4_vexpr961`;`du:l4_klevel447`]
    l4_sort_of_sound_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `du':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`L4VSort961 du'`;`L4VLSucc961 du'`] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_REWRITE_TAC [l4_vlevel_wf961] THEN
   MATCH_MP_TAC l4_klevel_equiv_sound_vlevel973 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`ps:l4_name list`;`du:l4_klevel447`;`L4KZero447`] THEN
   ASM_REWRITE_TAC [l4_tr_l967];
   ASM_REWRITE_TAC [GSYM l4_vhas_type961]]);;

let l4_core_apply_type_sound974 = prove
 (`!env venv ps chk rec g l args args' h ty ty' res ta.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   ALL2 (l4_vtr_expr973 env venv ps l) args args' /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) h ty' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_vapps962 args' h) ta /\
   l4_core_apply_type543 args rec g ty = L4KAccept491 res ==>
   ?res'.
     l4_vtr_expr973 env venv ps l res res' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_vapps962 args' h) res'`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> SPEC_TAC (v,v))
    [`ta:l4_vexpr961`;`res:l4_kexpr447`;`ty':l4_vexpr961`;`ty:l4_kexpr447`;
     `h:l4_vexpr961`;`args':l4_vexpr961 list`;`args:l4_kexpr447 list`] THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `args':l4_vexpr961 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_core_apply_type543;l4_vapps962;injectivity "l4_kresult491"] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC `ty':l4_vexpr961` THEN ASM_MESON_TAC [];
   X_GEN_TAC `a:l4_kexpr447` THEN X_GEN_TAC `rest:l4_kexpr447 list` THEN
   DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `args':l4_vexpr961 list` list_CASES) THEN
   DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `a':l4_vexpr961` (X_CHOOSE_THEN `rest':l4_vexpr961 list` SUBST_ALL_TAC))) THEN
   REWRITE_TAC [ALL2;l4_core_apply_type543;l4_vapps962;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `tyw:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hcat")))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hcat" MP_TAC THEN
   l4_subst_cases_tac974 (SPEC `tyw:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) ty'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `ty:l4_kexpr447`;`ty':l4_vexpr961`;`L4KPi447 a0 a1 a2 a3`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961`
       (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) h (L4VForallE961 dom' body')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?tha. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VApp961 h a') tha`
     (X_CHOOSE_TAC `tha:l4_vexpr961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `[]:l4_vexpr961 list`;`rest':l4_vexpr961 list`;`L4VApp961 h a'`;`ta:l4_vexpr961`]
      l4_vapps_wf_prefix974) THEN
    ASM_REWRITE_TAC [APPEND;l4_vapps962];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `h:l4_vexpr961`;`a':l4_vexpr961`;`tha:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a1':l4_vexpr961` (X_CHOOSE_THEN `b1':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `?uA. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a1' dom' (L4VSort961 uA)`
     (X_CHOOSE_TAC `uA:l4_vlevel961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `a1':l4_vexpr961`;`b1':l4_vexpr961`;`dom':l4_vexpr961`;`body':l4_vexpr961`]
      l4_vis_defeq_u_forallE_inv972) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`h:l4_vexpr961`;`h:l4_vexpr961`;`h:l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' dom'`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`a1':l4_vexpr961`;`uA:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VApp961 h a') (l4_vinst0961 body' a')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kinst447 a3 a) (l4_vinst0961 body' a')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_instantiate_lam973 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REMOVE_THEN "IH" MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`l4_kinst447 a3 a`;`l4_vinst0961 body' a'`;`ta:l4_vexpr961`] THEN
   ASM_REWRITE_TAC []]);;

let l4_core_projection_field_sound974 = prove
 (`!skip env venv ps chk rec fuel g l
    owner info ctor c d ci_c us' params' indices' sv u_sort ty_p maybe_prop val_e
    idx ty ty' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_core_inductive532 env owner = SOME info /\
   l4_kind_ctors493 info = [ctor] /\
   l4_kfind_decl493 env ctor = SOME d /\
   l4_kdecl_kind493 d = L4KDConstructor493 c /\
   l4_venv_lookup_const961 venv ctor ci_c /\
   LENGTH params' = l4_kind_num_params493 info /\
   LENGTH indices' = l4_kind_num_indices493 info /\
   ALL (l4_vlevel_wf961 (LENGTH ps)) us' /\
   LENGTH us' = LENGTH (l4_kdecl_params493 d) /\
   l4_vtr_expr973 env venv ps l val_e sv /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) sv
     (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us')) /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l)
     (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us'))
     (L4VSort961 u_sort) /\
   (~maybe_prop ==> ~l4_vlevel_equiv961 u_sort L4VLZero961) /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l)
     (l4_vapps962 params' (L4VConst961 ctor us')) ty_p /\
   skip + idx < l4_kctor_num_fields493 c /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   (!k fty.
      l4_vproj_telescope973 env venv (LENGTH ps) (l4_vl_ctx973 l)
        owner us' params' sv maybe_prop k idx ty' fty ==>
      l4_vproj_telescope973 env venv (LENGTH ps) (l4_vl_ctx973 l)
        owner us' params' sv maybe_prop (k + idx) 0 ty_p fty) /\
   l4_core_projection_field577 skip rec fuel g owner val_e maybe_prop idx ty = L4KAccept491 res ==>
   ?fty.
     l4_vtr_expr973 env venv ps l res fty /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l)
       (l4_vproj_expr962 owner (skip + idx) us' params' sv) fty`,
  INDUCT_TAC THENL
  [(* skip = 0 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_projection_field577;l4_kr_bind_accept967;ADD] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hpf_m")))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hpf_m" MP_TAC THEN
   l4_subst_cases_tac974 (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) ty'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `ty:l4_kexpr447`;`ty':l4_vexpr961`;`L4KPi447 a0 a1 a2 a3`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961`
       (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 dom'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `maybe_prop ==> l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 L4VLZero961)`
     ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC l4_projection_verify_prop_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                          `a2:l4_kexpr447`;`ign:1`] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC `(if maybe_prop then l4_projection_verify_prop577 rec fuel g a2 else L4KAccept491 one) = L4KAccept491 ign` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vproj_telescope973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        owner us' params' sv maybe_prop 0 idx ty' dom'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vpt_zero973 THEN EXISTS_TAC `body':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vproj_telescope973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        owner us' params' sv maybe_prop idx 0 ty_p dom'` ASSUME_TAC THENL
   [SUBGOAL_THEN `idx = 0 + idx` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_proj_telescope973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;`info:l4_kinductive_data493`;
      `ctor:l4_name`;`c:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`ci_c:l4_vconstant961`;
      `idx:num`;`us':l4_vlevel961 list`;`params':l4_vexpr961 list`;`indices':l4_vexpr961 list`;
      `sv:l4_vexpr961`;`u_sort:l4_vlevel961`;`ty_p:l4_vexpr961`;`dom':l4_vexpr961`;`maybe_prop:bool`]) THEN
   ASM_REWRITE_TAC [];
   (* skip = SUC skip *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_projection_field577;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hpf_m")))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hpf_m" MP_TAC THEN
   l4_subst_cases_tac974 (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hvp") (LABEL_TAC "Hpf_next"))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) ty'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `ty:l4_kexpr447`;`ty':l4_vexpr961`;`L4KPi447 a0 a1 a2 a3`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961`
       (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 dom'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') a3 body'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `SUC skip + idx = skip + SUC idx` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `l4_core_occurs532 0 a3` THENL
   [(* Dependent field *)
    SUBGOAL_THEN `maybe_prop ==> l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 L4VLZero961)`
      ASSUME_TAC THENL
    [DISCH_TAC THEN MATCH_MP_TAC l4_projection_verify_prop_sound974 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
                           `a2:l4_kexpr447`;`ign:1`] THEN
     ASM_REWRITE_TAC [] THEN REMOVE_THEN "Hvp" MP_TAC THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vproj_telescope973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         owner us' params' sv maybe_prop idx 0 ty_p dom'` ASSUME_TAC THENL
    [SUBGOAL_THEN `idx = 0 + idx` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC l4_vpt_zero973 THEN EXISTS_TAC `body':l4_vexpr961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (l4_vproj_expr962 owner idx us' params' sv) dom'` ASSUME_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_proj_telescope973) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL
       [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;`info:l4_kinductive_data493`;
        `ctor:l4_name`;`c:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`ci_c:l4_vconstant961`;
        `idx:num`;`us':l4_vlevel961 list`;`params':l4_vexpr961 list`;`indices':l4_vexpr961 list`;
        `sv:l4_vexpr961`;`u_sort:l4_vlevel961`;`ty_p:l4_vexpr961`;`dom':l4_vexpr961`;`maybe_prop:bool`]) THEN
     ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vtr_expr973 env venv ps l (L4KProj447 owner idx val_e)
         (l4_vproj_expr962 owner idx us' params' sv)` ASSUME_TAC THENL
    [UNDISCH_TAC `l4_vtr_expr973 env venv ps l val_e sv` THEN
     DISCH_THEN (X_CHOOSE_THEN `v0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `tv:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
     SUBGOAL_THEN
       `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v0
          (l4_vapps962 (APPEND (params':l4_vexpr961 list) indices') (L4VConst961 owner us'))` ASSUME_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `sv:l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
      REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `tv:l4_vexpr961` THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     SUBGOAL_THEN
       `?tpv. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
                (l4_vproj_expr962 owner idx us' params' v0)
                (l4_vproj_expr962 owner idx us' params' sv) tpv`
       (X_CHOOSE_TAC `tpv:l4_vexpr961`) THENL
     [UNDISCH_TAC `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vproj_expr962 owner idx us' params' sv) dom'` THEN
      REWRITE_TAC [l4_vproj_expr962] THEN DISCH_TAC THEN
      MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                     `l4_vapps962 params' (L4VConst961 (l4_proj_const_name962 owner idx) us')`;
                     `sv:l4_vexpr961`;`dom':l4_vexpr961`] l4_vhas_type_app_inv970) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961` (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `?up. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ap tv (L4VSort961 up)`
        (X_CHOOSE_TAC `up:l4_vlevel961`) THENL
      [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
       MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`sv:l4_vexpr961`;`sv:l4_vexpr961`] THEN
       ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
       MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `v0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
       ALL_TAC] THEN
      EXISTS_TAC `l4_vinst0961 bp v0` THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
      EXISTS_TAC `ap:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_conv961 THEN
      MAP_EVERY EXISTS_TAC [`tv:l4_vexpr961`;`up:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN
     EXISTS_TAC `l4_vproj_expr962 owner idx us' params' v0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
      MAP_EVERY EXISTS_TAC [`v0:l4_vexpr961`;`tpv:l4_vexpr961`] THEN
      ASM_REWRITE_TAC [l4_vtr_proj973] THEN
      MAP_EVERY EXISTS_TAC
        [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
         `d:l4_kdeclaration493`;`us':l4_vlevel961 list`;
         `params':l4_vexpr961 list`;`indices':l4_vexpr961 list`] THEN
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
      TRY ASM_ARITH_TAC THEN
      MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
      EXISTS_TAC `l4_vproj_expr962 owner idx us' params' sv` THEN ASM_REWRITE_TAC [];
      EXISTS_TAC `tpv:l4_vexpr961` THEN ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vtr_expr973 env venv ps l (l4_kinst447 a3 (L4KProj447 owner idx val_e))
         (l4_vinst0961 body' (l4_vproj_expr962 owner idx us' params' sv))` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_instantiate_lam973 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
       `info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
       `d:l4_kdeclaration493`;`ci_c:l4_vconstant961`;`indices':l4_vexpr961 list`;
       `u_sort:l4_vlevel961`;`ty_p:l4_vexpr961`;`maybe_prop:bool`;`val_e:l4_kexpr447`;
       `l4_kinst447 a3 (L4KProj447 owner idx val_e)`;
       `l4_vinst0961 body' (l4_vproj_expr962 owner idx us' params' sv)`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [ASM_ARITH_TAC;
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `k + SUC idx = SUC k + idx` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC l4_vpt_succ973 THEN
     MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`body':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
      DISCH_THEN (fun h -> FIRST_ASSUM (fun hp -> ACCEPT_TAC (MP hp (CONJUNCT1 h))))]];
    (* Non-dependent field *)
    SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom')`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`dom':l4_vexpr961`;`a3:l4_kexpr447`;
                   `body':l4_vexpr961`;`L4KProj447 owner idx val_e`]
      l4_vtr_expr_no_occurs_instantiate974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `b0:l4_vexpr961` (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `tb:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) ASSUME_TAC)) THEN
    SUBGOAL_THEN
      `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         ty' (L4VForallE961 dom' (l4_vlift961 b0))` ASSUME_TAC THENL
    [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                    `dom':l4_vexpr961`;`body':l4_vexpr961`;`ty_pi:l4_vexpr961`]
       l4_vhas_type_forall_inv972) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
     REWRITE_TAC [l4_vis_type961] THEN
     DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:l4_vlevel961`) (X_CHOOSE_TAC `v:l4_vlevel961`)) THEN
     SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))`
       ASSUME_TAC THENL
     [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
     SUBGOAL_THEN
       `?vb. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))
               (L4VSort961 v) tb (L4VSort961 vb)` (X_CHOOSE_TAC `vb:l4_vlevel961`) THENL
     [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
      MAP_EVERY EXISTS_TAC [`body':l4_vexpr961`;`body':l4_vexpr961`;`body':l4_vexpr961`] THEN
      ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `l4_vlift961 b0` THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VForallE961 dom' body'` THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
      REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
      MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
      MATCH_MP_TAC l4_vis_defeq_symm961 THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
      MAP_EVERY EXISTS_TAC [`tb:l4_vexpr961`;`vb:l4_vlevel961`] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;
       `info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
       `d:l4_kdeclaration493`;`ci_c:l4_vconstant961`;`indices':l4_vexpr961 list`;
       `u_sort:l4_vlevel961`;`ty_p:l4_vexpr961`;`maybe_prop:bool`;`val_e:l4_kexpr447`;
       `l4_kinst447 a3 (L4KProj447 owner idx val_e)`;`b0:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [ASM_ARITH_TAC;
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `k + SUC idx = SUC k + idx` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC l4_vpt_succ973 THEN
     MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`l4_vlift961 b0`] THEN
     ASM_REWRITE_TAC [l4_vinst0_vlift966] THEN
     DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `b0:l4_vexpr961`)) THEN
     REWRITE_TAC []]]]);;

let l4_core_infer_projection_sound974 = prove
 (`!env venv ps chk rec fuel g l owner idx val_e res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   (chk \/ ?v'. l4_vtr_expr973 env venv ps l val_e v') /\
   l4_core_infer_projection577 rec fuel env g owner idx val_e = L4KAccept491 res ==>
   ?e' ty'.
     l4_vtr_typing973 env venv ps l (L4KProj447 owner idx val_e) res e' ty' /\
     (!v'. l4_vtr_expr973 env venv ps l val_e v' ==>
        ?pv. l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) pv e' /\
             l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner idx v' pv ty')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hcore_ip")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hcore_ip" MP_TAC THEN
  REWRITE_TAC [l4_core_infer_projection577;l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
  DISCH_THEN (X_CHOOSE_THEN `st0:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Hinf")
    (X_CHOOSE_THEN `st:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Hwst") MP_TAC)))) THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 st)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 st)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 args head = st` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_all_dis974] THEN
  MP_TAC (ISPEC `l4_core_inductive532 env owner` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `info:l4_kinductive_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC (ISPEC `l4_kind_ctors493 info` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `ctor:l4_name` (X_CHOOSE_THEN `ctors_tl:l4_name list`
      (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974])))) THEN
  MP_TAC (ISPEC `ctors_tl:l4_name list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> SUBST_ALL_TAC th THEN REWRITE_TAC [l4_all_dis974])
    (X_CHOOSE_THEN `c2:l4_name` (X_CHOOSE_THEN `c2s:l4_name list`
      (fun th -> REWRITE_TAC [th;l4_all_dis974])))) THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env ctor` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_all_dis974])
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
    (fun th ->
       if is_exists (concl th) then
         let v, _ = dest_exists (concl th) in
         X_CHOOSE_THEN (mk_var ("ck", type_of v)) (fun h -> ASSUME_TAC h THEN REWRITE_TAC [h;l4_all_dis974]) th
       else REWRITE_TAC [th;l4_all_dis974])) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty_p_e:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Hcat")
    (X_CHOOSE_THEN `u_s:l4_klevel447` (CONJUNCTS_THEN2 (LABEL_TAC "Hso") (LABEL_TAC "Hip"))))) THEN
  (* Get val' and st' from chk \/ ?v' *)
  SUBGOAL_THEN
    `?val' st'.
       l4_vtr_expr973 env venv ps l val_e val' /\
       l4_vtr_expr973 env venv ps l st st' /\
       l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val' st'`
    (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `st':l4_vexpr961` STRIP_ASSUME_TAC)) THENL
  [UNDISCH_TAC `chk \/ (?v'. l4_vtr_expr973 env venv ps l val_e v')` THEN
   DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `v':l4_vexpr961`)) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`val_e:l4_kexpr447`;`st0:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [l4_vtr_typing973] THEN
    DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `st0':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`st0':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `st0:l4_kexpr447`;`st0':l4_vexpr961`;`st:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [];
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_typed974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                `val_e:l4_kexpr447`;`v':l4_vexpr961`;`st0:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `st0':l4_vexpr961` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`v':l4_vexpr961`;`st0':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `st0:l4_kexpr447`;`st0':l4_vexpr961`;`st:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 owner a1)) st'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961` (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 owner a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  (* Unpack core_inductive env owner = SOME info *)
  SUBGOAL_THEN
    `?d_ind. l4_kfind_decl493 env owner = SOME d_ind /\
             l4_kdecl_kind493 d_ind = L4KDInductive493 info`
    (X_CHOOSE_THEN `d_ind:l4_kdeclaration493` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `l4_core_inductive532 env owner = SOME info` THEN
   REWRITE_TAC [l4_core_inductive532] THEN
   MP_TAC (ISPEC `l4_kfind_decl493 env owner` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `di:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   MP_TAC (SPEC `l4_kdecl_kind493 di` (cases "l4_kdecl_kind493")) THEN
   DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
     (fun th ->
        if is_exists (concl th) then
          let v, _ = dest_exists (concl th) in
          X_CHOOSE_THEN (mk_var ("kd", type_of v)) (fun h -> ASSUME_TAC h THEN REWRITE_TAC [h;l4_all_dis974]) th
        else REWRITE_TAC [th;l4_all_dis974])) THEN
   REWRITE_TAC [injectivity "option"] THEN DISCH_THEN SUBST_ALL_TAC THEN
   EXISTS_TAC `di:l4_kdeclaration493` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  (* Use ves_ind_shape and ves_constants *)
  SUBGOAL_THEN
    `l4_kctor_num_params493 ck = l4_kind_num_params493 info /\
     LENGTH (l4_kdecl_params493 d) = LENGTH (l4_kdecl_params493 d_ind)` STRIP_ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_shape973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL
     [`owner:l4_name`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
      `ctor:l4_name`;`ck:l4_kconstructor_data493`;`d:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d_ind)` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`owner:l4_name`;`d_ind:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [l4_all_dis974] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci_i:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `ci:l4_vconstant961 = ci_i` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`owner:l4_name`] THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?ci_c. l4_venv_lookup_const961 venv ctor ci_c /\
            l4_vc_uvars961 ci_c = LENGTH (l4_kdecl_params493 d) /\
            l4_vtr_expr973 env venv (l4_kdecl_params493 d) l4_vl_empty973
              (l4_kdecl_type493 d) (l4_vc_type961 ci_c)`
    (X_CHOOSE_THEN `ci_c:l4_vconstant961` STRIP_ASSUME_TAC) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`ctor:l4_name`;`d:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [l4_all_dis974] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci_c:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `ci_c:l4_vconstant961` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (a1:l4_klevel447 list)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_tr_ls_length967 THEN EXISTS_TAC `ps:l4_name list` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (a1:l4_klevel447 list) = LENGTH (l4_kdecl_params493 d)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (l4_kdecl_params493 d)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (args':l4_vexpr961 list) = l4_kind_num_params493 info + l4_kind_num_indices493 info`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `LENGTH (args:l4_kexpr447 list) = LENGTH (args':l4_vexpr961 list)`
     (fun th -> REWRITE_TAC [GSYM th] THEN ASM_REWRITE_TAC []) THEN
   MATCH_MP_TAC l4_all2_length974 THEN EXISTS_TAC `l4_vtr_expr_s973 env venv ps l` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`l4_kind_num_params493 info`;`args':l4_vexpr961 list`;`l4_kind_num_indices493 info`]
    l4_list_split_at974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `params':l4_vexpr961 list` (X_CHOOSE_THEN `indices':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val'
       (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us'))` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `st':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `APPEND (params':l4_vexpr961 list) indices' = args'` SUBST1_TAC THENL
   [ASM_REWRITE_TAC []; MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `l4_kapply_exprs489 args (L4KConst447 owner a1)`;`st':l4_vexpr961`;`u_s:l4_klevel447`]
    l4_sort_of_sound_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `u_s':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us')) (L4VSort961 u_s')` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `st':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `APPEND (params':l4_vexpr961 list) indices' = args'` SUBST1_TAC THENL
   [ASM_REWRITE_TAC []; MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(~l4_core_level_positive555 u_s) ==> ~l4_vlevel_equiv961 u_s' L4VLZero961` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vlevel_equiv961;l4_vlevel_eval961] THEN STRIP_TAC THEN
   DISCH_THEN (MP_TAC o SPEC `[]:num list`) THEN
   MP_TAC (SPECL [`ps:l4_name list`;`u_s:l4_klevel447`;`u_s':l4_vlevel961`] l4_core_level_positive_sound973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `[]:num list`) THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?ta. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
            (l4_vapps962 params' (L4VConst961 ctor us')) ta` (X_CHOOSE_TAC `ta:l4_vexpr961`) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ctor_params_wf973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`owner:l4_name`;`info:l4_kinductive_data493`;
      `ctor:l4_name`;`ck:l4_kconstructor_data493`;`d:l4_kdeclaration493`;`us':l4_vlevel961 list`;
      `params':l4_vexpr961 list`;`indices':l4_vexpr961 list`;`L4VSort961 u_s'`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (L4VConst961 ctor us') (l4_vinstL961 us' (l4_vc_type961 ci_c))` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_const972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps l
       (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 (l4_kdecl_type493 d))
       (l4_vinstL961 us' (l4_vc_type961 ci_c))` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_closed_to_any973 THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_subst_levels973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL2 (l4_vtr_expr973 env venv ps l) (l4_kfirstn494 args (l4_kind_num_params493 info)) params'`
    ASSUME_TAC THENL
  [SUBST1_TAC (SYM (ASSUME `l4_kfirstn494 (args':l4_vexpr961 list) (l4_kind_num_params493 info) = params'`)) THEN
   MATCH_MP_TAC l4_all2_firstn973 THEN
   MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL
    [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`chk:bool`;`rec:l4_kmethods543`;
     `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
     `l4_kfirstn494 (args:l4_kexpr447 list) (l4_kind_num_params493 info)`;
     `params':l4_vexpr961 list`;`L4VConst961 ctor us'`;
     `l4_ksubst_levels488 (l4_kdecl_params493 d) a1 (l4_kdecl_type493 d)`;
     `l4_vinstL961 us' (l4_vc_type961 ci_c)`;`ty_p_e:l4_kexpr447`;`ta:l4_vexpr961`]
    l4_core_apply_type_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty_p:l4_vexpr961` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL
    [`idx:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
     `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
     `owner:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;`ck:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`ci_c:l4_vconstant961`;`us':l4_vlevel961 list`;
     `params':l4_vexpr961 list`;`indices':l4_vexpr961 list`;`val':l4_vexpr961`;
     `u_s':l4_vlevel961`;`ty_p:l4_vexpr961`;`~l4_core_level_positive555 u_s`;`val_e:l4_kexpr447`;
     `0`;`ty_p_e:l4_kexpr447`;`ty_p:l4_vexpr961`;`res:l4_kexpr447`]
    l4_core_projection_field_sound974) THEN
  ASM_REWRITE_TAC [ADD_0] THEN
  DISCH_THEN (X_CHOOSE_THEN `fty:l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps l (L4KProj447 owner idx val_e)
       (l4_vproj_expr962 owner idx us' params' val')` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vtr_expr973 env venv ps l val_e val'` THEN
   DISCH_THEN (X_CHOOSE_THEN `v0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `tv:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v0
        (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us'))` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `val':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `tv:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?tpv. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
              (l4_vproj_expr962 owner idx us' params' v0)
              (l4_vproj_expr962 owner idx us' params' val') tpv`
     (X_CHOOSE_TAC `tpv:l4_vexpr961`) THENL
   [UNDISCH_TAC `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vproj_expr962 owner idx us' params' val') fty` THEN
    REWRITE_TAC [l4_vproj_expr962] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `l4_vapps962 params' (L4VConst961 (l4_proj_const_name962 owner idx) us')`;
                   `val':l4_vexpr961`;`fty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961` (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?up. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ap tv (L4VSort961 up)`
      (X_CHOOSE_TAC `up:l4_vlevel961`) THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
     MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`val':l4_vexpr961`;`val':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `v0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    EXISTS_TAC `l4_vinst0961 bp v0` THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
    EXISTS_TAC `ap:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tv:l4_vexpr961`;`up:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN
   EXISTS_TAC `l4_vproj_expr962 owner idx us' params' v0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
    MAP_EVERY EXISTS_TAC [`v0:l4_vexpr961`;`tpv:l4_vexpr961`] THEN
    ASM_REWRITE_TAC [l4_vtr_proj973] THEN
    MAP_EVERY EXISTS_TAC
      [`info:l4_kinductive_data493`;`ctor:l4_name`;`ck:l4_kconstructor_data493`;
       `d:l4_kdeclaration493`;`us':l4_vlevel961 list`;
       `params':l4_vexpr961 list`;`indices':l4_vexpr961 list`] THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
    MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
    EXISTS_TAC `l4_vproj_expr962 owner idx us' params' val'` THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `tpv:l4_vexpr961` THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l4_vproj_expr962 owner idx us' params' val'`;`fty:l4_vexpr961`] THEN
  REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v' val'`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`val_e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v'
       (l4_vapps962 (APPEND params' indices') (L4VConst961 owner us'))` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `val':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (l4_vproj_expr962 owner idx us' params' v')
       (l4_vproj_expr962 owner idx us' params' val')` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v' val'` THEN
   REWRITE_TAC [l4_vis_defeq_u961] THEN DISCH_THEN (X_CHOOSE_TAC `tv:l4_vexpr961`) THEN
   UNDISCH_TAC `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vproj_expr962 owner idx us' params' val') fty` THEN
   REWRITE_TAC [l4_vproj_expr962] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `l4_vapps962 params' (L4VConst961 (l4_proj_const_name962 owner idx) us')`;
                  `val':l4_vexpr961`;`fty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961` (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `?up. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ap tv (L4VSort961 up)`
     (X_CHOOSE_TAC `up:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`val':l4_vexpr961`;`val':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `v':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `l4_vinst0961 bp v'` THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
   EXISTS_TAC `ap:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`tv:l4_vexpr961`;`up:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  EXISTS_TAC `l4_vproj_expr962 owner idx us' params' v'` THEN
  ASM_REWRITE_TAC [l4_vtr_proj973] THEN
  MAP_EVERY EXISTS_TAC
    [`info:l4_kinductive_data493`;`ctor:l4_name`;`ck:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`us':l4_vlevel961 list`;
     `params':l4_vexpr961 list`;`indices':l4_vexpr961 list`] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN
  EXISTS_TAC `l4_vproj_expr962 owner idx us' params' val'` THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []);;

(* Full 13-constructor soundness of `l4_infer_step586 ... T` (checking mode) *)
let l4_infer_step_sound_true974 = prove
 (`!e env venv ps rec fuel g l ty.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_infer_step586 e rec fuel env ps T g = L4KAccept491 ty ==>
   ?e' ty'. l4_vtr_typing973 env venv ps l e ty e' ty'`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [(* L4KBVar447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_closed966 venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   POP_ASSUM (fun hcl -> POP_ASSUM MP_TAC THEN ASSUME_TAC hcl) THEN
   MP_TAC (ISPEC `l4_nth_error550 (l4_kcontext_bound532 g) a` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:num`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_bound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [];
   (* L4KFVar447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_closed966 venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966]; ALL_TAC] THEN
   POP_ASSUM (fun hcl -> POP_ASSUM MP_TAC THEN ASSUME_TAC hcl) THEN
   MP_TAC (ISPEC `l4_kfind_free532 a (l4_kcontext_free532 g)` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_name`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_free974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`] THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [];
   (* L4KMVar447 *)
   REWRITE_TAC [l4_infer_step586;l4_all_dis974];
   (* L4KSort447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))) THEN
   MP_TAC (SPECL [`ps:l4_name list`;`a:l4_klevel447`;`ign:1`] l4_check_level_tr_l967) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   MAP_EVERY EXISTS_TAC [`L4VSort961 u'`;`L4VSort961 (L4VLSucc961 u')`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN
    ASM_REWRITE_TAC [l4_tr_l967;l4_opt_map967;l4_vlevel_wf961];
    MATCH_MP_TAC l4_vhas_type_sort972 THEN ASM_REWRITE_TAC []];
   (* L4KConst447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `d:l4_kdeclaration493` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))) THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vtr_ctx_to_vl_wf973]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_klevel447 list`;`d:l4_kdeclaration493`]
     l4_get_constant_sound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = l4_vc_uvars961 ci` ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (a1:l4_klevel447 list)`
      (fun th -> ASM_REWRITE_TAC [th]) THEN
    MATCH_MP_TAC l4_tr_ls_length967 THEN EXISTS_TAC `ps:l4_name list` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`L4VConst961 a0 us'`;`l4_vinstL961 us' (l4_vc_type961 ci)`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
    COND_CASES_TAC THENL
    [UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 (l4_kdecl_type493 d)) (l4_vinstL961 us' (l4_vc_type961 ci))` THEN
     ASM_REWRITE_TAC [l4_ksubst_levels_nil974];
     ASM_REWRITE_TAC []];
    ASM_REWRITE_TAC []];
   (* L4KApp447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHf") (LABEL_TAC "IHa")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ft0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `ft:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   l4_subst_cases_tac974 (SPEC `ft:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `aty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))
     (SUBST1_TAC o SYM))) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
   REMOVE_THEN "IHf" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`ft0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961` (X_CHOOSE_THEN `ft':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0' a1' a2 a3) ft'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `ft0:l4_kexpr447`;`ft':l4_vexpr961`;`L4KPi447 a0' a1' a2 a3`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961` (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) f' (L4VForallE961 dom' body')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ft':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REMOVE_THEN "IHa" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`aty:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `a':l4_vexpr961` (X_CHOOSE_THEN `aty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' aty'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_application_type_defeq_full_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`T`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`a1:l4_kexpr447`;
                          `a2:l4_kexpr447`;`aty:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' dom'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `aty':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VApp961 f' a') (l4_vinst0961 body' a')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`L4VApp961 f' a'`;`l4_vinst0961 body' a'`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [MP_TAC (SPECL [`[a1:l4_kexpr447]`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`a0:l4_kexpr447`;`f':l4_vexpr961`;`[a':l4_vexpr961]`;
                   `l4_vinst0961 body' a'`] l4_vtr_expr_kapply973) THEN
    ASM_REWRITE_TAC [l4_kapply_exprs489;l4_vapps962;ALL2];
    MATCH_MP_TAC l4_vtr_expr_instantiate_lam973 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   (* L4KLam447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (LABEL_TAC "IHb")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;
                   l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `dt0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `dt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))
       (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   l4_subst_cases_tac974 (SPEC `dt:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
   REMOVE_THEN "IHA" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`dt0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `dt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 a) dt'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `dt0:l4_kexpr447`;`dt':l4_vexpr961`;`L4KSort447 a`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `dt':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHb" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a2 NONE`;
      `l4_vl_push_lam973 l dom'`;`bt:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body':l4_vexpr961` (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?v. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) bt' (L4VSort961 v)`
     (X_CHOOSE_TAC `v:l4_vlevel961`) THENL
   [REWRITE_TAC [GSYM l4_vis_type961] THEN MATCH_MP_TAC l4_vis_defeq_is_type974 THEN
    MAP_EVERY EXISTS_TAC [`body':l4_vexpr961`;`body':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l a2 dom'` THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `td:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
   SUBGOAL_THEN `?ud. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 u') td (L4VSort961 ud)`
     (X_CHOOSE_TAC `ud:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`dom':l4_vexpr961`;`dom':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `dom0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom0 dom' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`td:l4_vexpr961`;`ud:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom0)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l dom0)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_push_lam974 THEN EXISTS_TAC `u':l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?b0 tb0. l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom0) a3 b0 /\
               l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) b0 body' tb0`
     (X_CHOOSE_THEN `b0:l4_vexpr961` (X_CHOOSE_THEN `tb0:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_lam973 l dom'`;`l4_vl_push_lam973 l dom0`;
                   `a3:l4_kexpr447`;`body':l4_vexpr961`] l4_vtr_expr_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973] THEN
    MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?bt0 tbt0. l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom0) bt bt0 /\
                 l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) bt0 bt' tbt0`
     (X_CHOOSE_THEN `bt0:l4_vexpr961` (X_CHOOSE_THEN `tbt0:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_lam973 l dom'`;`l4_vl_push_lam973 l dom0`;
                   `bt:l4_kexpr447`;`bt':l4_vexpr961`] l4_vtr_expr_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973] THEN
    MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_ctx966 venv (LENGTH (ps:l4_name list)) [] (CONS dom' (l4_vl_ctx973 l)) (CONS dom0 (l4_vl_ctx973 l))`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_push_lam973 l dom'`;`l4_vl_push_lam973 l dom0`]
      l4_vl_ctx_defeq_to_vis_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_push_lam973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) bt' (L4VSort961 v)`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom' (l4_vl_ctx973 l)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?v0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) (L4VSort961 v) tbt0 (L4VSort961 v0)`
     (X_CHOOSE_TAC `v0:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`bt':l4_vexpr961`;`bt':l4_vexpr961`;`bt':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `bt0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) bt0 bt' (L4VSort961 v)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tbt0:l4_vexpr961`;`v0:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`L4VLam961 dom' body'`;`L4VForallE961 dom' bt'`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN EXISTS_TAC `L4VLam961 dom0 b0` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `L4VForallE961 dom0 tb0` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u':l4_vlevel961` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `body':l4_vexpr961` THEN ASM_REWRITE_TAC []];
     EXISTS_TAC `L4VForallE961 dom0 tb0` THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
     EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []];
    REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom0 bt0` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v)` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_forall972 THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `bt':l4_vexpr961` THEN ASM_REWRITE_TAC []];
     EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v)` THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []];
   (* L4KPi447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (LABEL_TAC "IHB")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;
                   l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `dt0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `dt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `u0:l4_klevel447` (CONJUNCTS_THEN2 MP_TAC
           (X_CHOOSE_THEN `bt0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
             (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
               (X_CHOOSE_THEN `v0:l4_klevel447` (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))))))))) THEN
   REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   l4_subst_cases_tac974 (SPEC `bt:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
   l4_subst_cases_tac974 (SPEC `dt:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
   REMOVE_THEN "IHA" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`dt0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `dt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 u0) dt'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `dt0:l4_kexpr447`;`dt':l4_vexpr961`;`L4KSort447 u0`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `dt':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHB" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a2 NONE`;
      `l4_vl_push_lam973 l dom'`;`bt0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973;l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body':l4_vexpr961` (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') (L4KSort447 v0) bt'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL
      [`l4_kpush_binding532 g a2 NONE`;`l4_vl_push_lam973 l dom'`;
       `bt0:l4_kexpr447`;`bt':l4_vexpr961`;`L4KSort447 v0`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `v':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' (L4VSort961 v')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `bt':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l a2 dom'` THEN
   DISCH_THEN (X_CHOOSE_THEN `dom0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `td:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
   SUBGOAL_THEN `?ud. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 u') td (L4VSort961 ud)`
     (X_CHOOSE_TAC `ud:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`dom':l4_vexpr961`;`dom':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `dom0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom0 dom' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`td:l4_vexpr961`;`ud:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom0)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom') (l4_vl_push_lam973 l dom0)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_push_lam974 THEN EXISTS_TAC `u':l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?b0 tb0. l4_vtr_expr_s973 env venv ps (l4_vl_push_lam973 l dom0) a3 b0 /\
               l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) b0 body' tb0`
     (X_CHOOSE_THEN `b0:l4_vexpr961` (X_CHOOSE_THEN `tb0:l4_vexpr961` STRIP_ASSUME_TAC)) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_lam973 l dom'`;`l4_vl_push_lam973 l dom0`;
                   `a3:l4_kexpr447`;`body':l4_vexpr961`] l4_vtr_expr_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973] THEN
    MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_ctx966 venv (LENGTH (ps:l4_name list)) [] (CONS dom' (l4_vl_ctx973 l)) (CONS dom0 (l4_vl_ctx973 l))`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_push_lam973 l dom'`;`l4_vl_push_lam973 l dom0`]
      l4_vl_ctx_defeq_to_vis_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_push_lam973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) body' (L4VSort961 v')`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_defeqDFC966 THEN
    MAP_EVERY EXISTS_TAC [`[]:l4_vexpr961 list`;`CONS dom' (l4_vl_ctx973 l)`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?vb0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) (L4VSort961 v') tb0 (L4VSort961 vb0)`
     (X_CHOOSE_TAC `vb0:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`body':l4_vexpr961`;`body':l4_vexpr961`;`body':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `b0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom0 (l4_vl_ctx973 l)) b0 body' (L4VSort961 v')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tb0:l4_vexpr961`;`vb0:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`L4VForallE961 dom' body'`;`L4VSort961 (L4VLIMax961 u' v')`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom0 b0` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v')` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_forall972 THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `body':l4_vexpr961` THEN ASM_REWRITE_TAC []];
     EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v')` THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN
    ASM_REWRITE_TAC [l4_tr_l967;l4_opt_map2967;l4_opt_map967;l4_vlevel_wf961];
    MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC []];
   (* L4KLet447 *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (CONJUNCTS_THEN2 (LABEL_TAC "IHv") (LABEL_TAC "IHb"))) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `st0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `st:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
           (X_CHOOSE_THEN `ign2:1` (CONJUNCTS_THEN2 MP_TAC
             (X_CHOOSE_THEN `vt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
               (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))))
       (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
   l4_subst_cases_tac974 (SPEC `st:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_TAC THEN
   REMOVE_THEN "IHA" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`st0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `tyA':l4_vexpr961` (X_CHOOSE_THEN `st':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 a) st'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `st0:l4_kexpr447`;`st':l4_vexpr961`;`L4KSort447 a`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tyA' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `st':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tyA'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHv" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`vt:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `vt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) vt' tyA'`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `T`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `vt:l4_kexpr447`;`vt':l4_vexpr961`;
                                      `a1:l4_kexpr447`;`tyA':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val' tyA'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `vt':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a1 (SOME a2)) (l4_vl_push_let973 l tyA' val')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_let973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHb" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a1 (SOME a2)`;
      `l4_vl_push_let973 l tyA' val'`;`bt:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973;l4_vl_ctx_push_let973] THEN
   DISCH_THEN (X_CHOOSE_THEN `body':l4_vexpr961` (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l a1 tyA'` THEN
   DISCH_THEN (X_CHOOSE_THEN `tyA0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ta0:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l a2 val'` THEN
   DISCH_THEN (X_CHOOSE_THEN `val0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `tv0:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
   SUBGOAL_THEN `?uA0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 u') ta0 (L4VSort961 uA0)`
     (X_CHOOSE_TAC `uA0:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`tyA':l4_vexpr961`;`tyA':l4_vexpr961`;`tyA':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `tyA0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tyA0 tyA' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`ta0:l4_vexpr961`;`uA0:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?uv0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tyA' tv0 (L4VSort961 uv0)`
     (X_CHOOSE_TAC `uv0:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`val':l4_vexpr961`;`val':l4_vexpr961`;`val':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `val0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val0 val' tyA'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tv0:l4_vexpr961`;`uv0:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tyA0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u':l4_vlevel961` THEN
    MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `tyA':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) val0 tyA0` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tyA':l4_vexpr961`;`u':l4_vlevel961`] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
     REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
     EXISTS_TAC `val':l4_vexpr961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_let973 l tyA' val')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_let973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_let973 l tyA0 val0)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_let973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_let973 l tyA' val') (l4_vl_push_let973 l tyA0 val0)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_push_let974 THEN EXISTS_TAC `u':l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?b0. l4_vtr_expr_s973 env venv ps (l4_vl_push_let973 l tyA0 val0) a3 b0 /\
           l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) b0 body'`
     (X_CHOOSE_THEN `b0:l4_vexpr961` STRIP_ASSUME_TAC) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_push_let973 l tyA' val'`;`l4_vl_push_let973 l tyA0 val0`;
                   `a3:l4_kexpr447`;`body':l4_vexpr961`] l4_vtr_expr_defeq_ctx973) THEN
    ASM_REWRITE_TAC [l4_vtr_expr973;l4_vl_ctx_push_let973];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`body':l4_vexpr961`;`bt':l4_vexpr961`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `b0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
    MAP_EVERY EXISTS_TAC [`tyA0:l4_vexpr961`;`val0:l4_vexpr961`] THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_instantiate_let973 THEN
    MAP_EVERY EXISTS_TAC [`tyA':l4_vexpr961`;`val':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN EXISTS_TAC `val0:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN EXISTS_TAC `tyA':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   (* L4KNatLit447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `l4_has_primitives973 env venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_prims973]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_nat974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 a) l4_vnat_ty973`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`l4_nat_lit973 a`;`l4_vnat_ty973`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_vnat_ty973] THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))` THEN
    ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
    ASM_REWRITE_TAC []];
   (* L4KStrLit447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
   REWRITE_TAC [l4_core_expand_string539] THEN
   MP_TAC (ISPEC `l4_core_utf8_539 a` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `cs:num list` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `l4_has_primitives973 env venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_prims973]; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_string974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_tr_str_lit973 a = SOME (L4VApp961 (L4VConst961 l4_core_string_of_list533 []) (l4_tr_char_list973 cs))`
     ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_tr_str_lit973]; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
        (L4VApp961 (L4VConst961 l4_core_string_of_list533 []) (l4_tr_char_list973 cs)) l4_vstring_ty973`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_tr_str_lit_has_type973 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`a:num list`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC
     [`L4VApp961 (L4VConst961 l4_core_string_of_list533 []) (l4_tr_char_list973 cs)`;`l4_vstring_ty973`] THEN
   REWRITE_TAC [l4_vtr_typing973] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_vstring_ty973] THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))` THEN
    ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
    ASM_REWRITE_TAC []];
   (* L4KProj447 *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   MP_TAC (ISPEC `l4_core_inductive532 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `info:l4_kinductive_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `T`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                  `a0:l4_name`;`a1:num`;`a2:l4_kexpr447`;`ty:l4_kexpr447`]
     l4_core_infer_projection_sound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`] THEN ASM_REWRITE_TAC [];
   (* L4KMData447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   REMOVE_THEN "IH" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`ty:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN
   DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`] THEN ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l a e'` THEN
   REWRITE_TAC [l4_vtr_expr973] THEN DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_REWRITE_TAC []]);;

(* Full 13-constructor soundness of `l4_infer_step586 ... F` (inference-only mode) *)
let l4_infer_step_sound_false974 = prove
 (`!e env venv ps chk rec fuel g l e' ty.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_infer_step586 e rec fuel env ps F g = L4KAccept491 ty ==>
   ?ty'. l4_vtr_expr973 env venv ps l ty ty' /\
         l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [(* L4KBVar447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973];
    ALL_TAC] THEN
   UNDISCH_TAC
     `(match l4_nth_error550 (l4_kcontext_bound532 g) a with
       | SOME b -> L4KAccept491 (l4_klift447 (l4_kbinding_type532 b) (SUC a) 0)
       | NONE -> L4KReject491 L4KLooseBoundVariable491) = L4KAccept491 ty` THEN
   MP_TAC (ISPEC `l4_nth_error550 (l4_kcontext_bound532 g) a` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:num`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_bound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `eb':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KBVar447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KBVar447 a) e0` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN `eb':l4_vexpr961 = e0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ]; ALL_TAC] THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
   (* L4KFVar447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973];
    ALL_TAC] THEN
   UNDISCH_TAC
     `(match l4_kfind_free532 a (l4_kcontext_free532 g) with
       | SOME b -> L4KAccept491 (l4_kbinding_type532 b)
       | NONE -> L4KReject491 L4KUnknownFreeVariable491) = L4KAccept491 ty` THEN
   MP_TAC (ISPEC `l4_kfind_free532 a (l4_kcontext_free532 g)` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `b:l4_kbinding491` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_all_dis974]))) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_name`;`b:l4_kbinding491`]
     l4_vtr_ctx_lookup_free974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ef':l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KFVar447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
   UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KFVar447 a) e0` THEN
   l4_inv_vtr_s_goal974 THEN
   SUBGOAL_THEN `ef':l4_vexpr961 = e0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option";PAIR_EQ]; ALL_TAC] THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
   (* L4KMVar447 *)
   REWRITE_TAC [l4_infer_step586;l4_all_dis974];
   (* L4KSort447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KSort447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THEN
   EXISTS_TAC `L4VSort961 (L4VLSucc961 u')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN
    ASM_REWRITE_TAC [l4_tr_l967;l4_opt_map967;l4_vlevel_wf961];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `L4VSort961 u'` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_sort972 THEN ASM_REWRITE_TAC []];
   (* L4KConst447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `d:l4_kdeclaration493` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_klevel447 list`;`d:l4_kdeclaration493`]
     l4_get_constant_sound974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KConst447 a0 a1) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `us2:l4_vlevel961 list`
     (X_CHOOSE_THEN `ci2:l4_vconstant961` STRIP_ASSUME_TAC) o MATCH_MP l4_vtr_expr_inv_const973) THEN
   SUBGOAL_THEN `us2:l4_vlevel961 list = us'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
   EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN CONJ_TAC THENL
   [COND_CASES_TAC THENL
    [UNDISCH_TAC `l4_vtr_expr973 env venv ps l (l4_ksubst_levels488 (l4_kdecl_params493 d) a1 (l4_kdecl_type493 d)) (l4_vinstL961 us' (l4_vc_type961 ci))` THEN
     ASM_REWRITE_TAC [l4_ksubst_levels_nil974];
     ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `L4VConst961 a0 us'` THEN
    ASM_REWRITE_TAC []];
   (* L4KApp447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHf") (LABEL_TAC "IHa")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ft0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `ft:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   l4_subst_cases_tac974 (SPEC `ft:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KApp447 a0 a1) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961` (X_CHOOSE_THEN `a':l4_vexpr961`
     (X_CHOOSE_THEN `ty_ap:l4_vexpr961` STRIP_ASSUME_TAC)) o MATCH_MP l4_vtr_expr_inv_app973) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `f':l4_vexpr961`;`a':l4_vexpr961`;`ty_ap:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom_a:l4_vexpr961` (X_CHOOSE_THEN `cod_a:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   REMOVE_THEN "IHf" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
      `f':l4_vexpr961`;`ft0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ft':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0' a1' a2 a3) ft'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `ft0:l4_kexpr447`;`ft':l4_vexpr961`;`L4KPi447 a0' a1' a2 a3`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961` (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) f' (L4VForallE961 dom' body')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ft':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?uA. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom_a dom' (L4VSort961 uA)`
     (X_CHOOSE_TAC `uA:l4_vlevel961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `dom_a:l4_vexpr961`;`cod_a:l4_vexpr961`;`dom':l4_vexpr961`;`body':l4_vexpr961`]
      l4_vis_defeq_u_forallE_inv972) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`f':l4_vexpr961`;`f':l4_vexpr961`;`f':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     STRIP_TAC THEN EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' dom'`
     ASSUME_TAC THENL
   [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`dom_a:l4_vexpr961`;`uA:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   EXISTS_TAC `l4_vinst0961 body' a'` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_instantiate_lam973 THEN EXISTS_TAC `dom':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `L4VApp961 f' a'` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_app972 THEN
    EXISTS_TAC `dom':l4_vexpr961` THEN ASM_REWRITE_TAC []];
   (* L4KLam447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (LABEL_TAC "IHb")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973;
                   l4_vtr_ctx_to_vl_wf973;l4_vtr_ctx_to_vctx_wf973];
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))))) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KLam447 a0 a1 a2 a3) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961`
     (X_CHOOSE_THEN `ty_lam:l4_vexpr961` STRIP_ASSUME_TAC)) o MATCH_MP l4_vtr_expr_inv_lam973) THEN
   SUBGOAL_THEN `?u. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 u)`
     (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
   [UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
    REWRITE_TAC [l4_vis_type961]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REMOVE_THEN "IHb" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a2 NONE`;
      `l4_vl_push_lam973 l dom'`;`body':l4_vexpr961`;`bt:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vl_ctx_push_lam973] THEN ANTS_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?v. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) bt' (L4VSort961 v)`
     (X_CHOOSE_TAC `v:l4_vlevel961`) THENL
   [REWRITE_TAC [GSYM l4_vis_type961] THEN MATCH_MP_TAC l4_vis_defeq_is_type974 THEN
    MAP_EVERY EXISTS_TAC [`body':l4_vexpr961`;`body':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') bt bt'` THEN
   DISCH_THEN (X_CHOOSE_THEN `bt0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `tbt0:l4_vexpr961` ASSUME_TAC)) o
     REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THEN
   SUBGOAL_THEN `?v0. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) (L4VSort961 v) tbt0 (L4VSort961 v0)`
     (X_CHOOSE_TAC `v0:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`bt':l4_vexpr961`;`bt':l4_vexpr961`;`bt':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `bt0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) bt0 bt' (L4VSort961 v)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tbt0:l4_vexpr961`;`v0:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VForallE961 dom' bt'` THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom' bt0` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN EXISTS_TAC `bt':l4_vexpr961` THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `L4VSort961 (L4VLIMax961 u v)` THEN MATCH_MP_TAC l4_vis_defeq_forall961 THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `L4VLam961 dom' body'` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC []];
   (* L4KPi447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (LABEL_TAC "IHB")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `dt0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `dt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `u0:l4_klevel447` (CONJUNCTS_THEN2 MP_TAC
           (X_CHOOSE_THEN `bt0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
             (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
               (X_CHOOSE_THEN `v0:l4_klevel447` (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))))))))) THEN
   REWRITE_TAC [injectivity "l4_kresult491"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
   l4_subst_cases_tac974 (SPEC `bt:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
   l4_subst_cases_tac974 (SPEC `dt:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_all_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961`
     (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC)) o MATCH_MP l4_vtr_expr_inv_pi973) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 dom'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHA" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
      `dom':l4_vexpr961`;`dt0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dt':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KSort447 u0) dt'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `dt0:l4_kexpr447`;`dt':l4_vexpr961`;`L4KSort447 u0`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' (L4VSort961 u')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `dt':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHB" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a2 NONE`;
      `l4_vl_push_lam973 l dom'`;`body':l4_vexpr961`;`bt0:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vl_ctx_push_lam973] THEN ANTS_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') (L4KSort447 v0) bt'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL
      [`l4_kpush_binding532 g a2 NONE`;`l4_vl_push_lam973 l dom'`;
       `bt0:l4_kexpr447`;`bt':l4_vexpr961`;`L4KSort447 v0`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [l4_vl_ctx_push_lam973] THEN
   DISCH_THEN (X_CHOOSE_THEN `v':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l)) body' (L4VSort961 v')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `bt':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   EXISTS_TAC `L4VSort961 (L4VLIMax961 u' v')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN
    ASM_REWRITE_TAC [l4_tr_l967;l4_opt_map2967;l4_opt_map967;l4_vlevel_wf961];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `L4VForallE961 dom' body'` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vhas_type_forall972 THEN ASM_REWRITE_TAC []];
   (* L4KLet447 *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHA") (CONJUNCTS_THEN2 (LABEL_TAC "IHv") (LABEL_TAC "IHb"))) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_all_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hinf_m")) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974;
    ALL_TAC] THEN
   REMOVE_THEN "Hinf_m"
     (X_CHOOSE_THEN `ign:1` (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `bt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))))) THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KLet447 a0 a1 a2 a3 a4) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `tyA':l4_vexpr961` (X_CHOOSE_THEN `val':l4_vexpr961`
     (X_CHOOSE_THEN `body':l4_vexpr961` STRIP_ASSUME_TAC)) o MATCH_MP l4_vtr_expr_inv_let974) THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a1 (SOME a2)) (l4_vl_push_let973 l tyA' val')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_let973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REMOVE_THEN "IHb" (MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`l4_kpush_binding532 g a1 (SOME a2)`;
      `l4_vl_push_let973 l tyA' val'`;`body':l4_vexpr961`;`bt:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [l4_vl_ctx_push_let973] THEN
   DISCH_THEN (X_CHOOSE_THEN `bt':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `bt':l4_vexpr961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_instantiate_let973 THEN
    MAP_EVERY EXISTS_TAC [`tyA':l4_vexpr961`;`val':l4_vexpr961`] THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `body':l4_vexpr961` THEN ASM_REWRITE_TAC []];
   (* L4KNatLit447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\ l4_has_primitives973 env venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_ves_prims973;l4_vtr_ctx_to_vctx_wf973]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KNatLit447 a) e'` THEN
   DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP l4_vtr_expr_inv_natlit974) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_nat974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   EXISTS_TAC `l4_vnat_ty973` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_vnat_ty973] THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))` THEN
    ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `l4_nat_lit973 a` THEN ASM_REWRITE_TAC []];
   (* L4KStrLit447 *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_all_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\ l4_has_primitives973 env venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_ves_prims973;l4_vtr_ctx_to_vctx_wf973]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KStrLit447 a) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `s':l4_vexpr961` STRIP_ASSUME_TAC o MATCH_MP l4_vtr_expr_inv_strlit974) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_hp_string974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   EXISTS_TAC `l4_vstring_ty973` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN REWRITE_TAC [l4_vstring_ty973] THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN
    EXISTS_TAC `L4VConstant961 0 (L4VSort961 (L4VLSucc961 L4VLZero961))` THEN
    ASM_REWRITE_TAC [l4_tr_ls967;ALL;LENGTH;l4_vc_uvars961];
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `s':l4_vexpr961` THEN ASM_REWRITE_TAC []];
   (* L4KProj447 *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
   MP_TAC (ISPEC `l4_core_inductive532 env a0` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_all_dis974])
     (X_CHOOSE_THEN `info:l4_kinductive_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973;l4_vtr_ctx_to_vctx_wf973]; ALL_TAC] THEN
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l (L4KProj447 a0 a1 a2) e'` THEN
   DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `pv:l4_vexpr961`
     (X_CHOOSE_THEN `fty:l4_vexpr961` STRIP_ASSUME_TAC)) o MATCH_MP l4_vtr_expr_inv_proj974) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `F`;`l4_inference_only543 rec`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                  `a0:l4_name`;`a1:num`;`a2:l4_kexpr447`;`ty:l4_kexpr447`]
     l4_core_infer_projection_sound974) THEN
   ASM_REWRITE_TAC [l4_vtr_typing973] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC l4_full_methods_sound_inference_only974 THEN EXISTS_TAC `chk:bool` THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `val':l4_vexpr961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `e_p:l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SPEC `val':l4_vexpr961`)))) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `pv2:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) pv pv2`
     ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_ctx973 l`;`a0:l4_name`;`a0:l4_name`;`a1:num`;
                   `val':l4_vexpr961`;`val':l4_vexpr961`;`pv:l4_vexpr961`;`pv2:l4_vexpr961`;
                   `fty:l4_vexpr961`;`ty':l4_vexpr961`] l4_vtr_proj_congr973) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_refl973 THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `l:l4_vl_ctx_rec973`;`a2:l4_kexpr447`;`val':l4_vexpr961`] l4_vtr_expr_has_type973) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `tv:l4_vexpr961`) THEN
     EXISTS_TAC `tv:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     STRIP_TAC THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e_p:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv2:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
   (* L4KMData447 *)
   REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_step586] THEN STRIP_TAC THEN
   REMOVE_THEN "IH" (MATCH_MP_TAC o SPECL
     [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
      `chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
      `e':l4_vexpr961`;`ty:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_inv_mdata974 THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* SECTION 6a: CONVERSION HELPERS & LAZY DELTA LOOPS SOUNDNESS               *)
(* Mirrors rocq/VerifyTypeChecker.v Section 6a-6i (lines 3708-4330).         *)
(* ========================================================================= *)

let l4_conv_dis974 = CONJ l4_all_dis974 (injectivity "option");;

let l4_subst_true_tac974 = DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO);;

let l4_ctx_wf_tac974 =
  let use1 th = FIRST_ASSUM (fun h -> ACCEPT_TAC (MATCH_MP th h)) in
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   use1 l4_ves_wf973 ORELSE
   use1 l4_ves_inj973 ORELSE
   use1 l4_ves_prims973 ORELSE
   use1 l4_vtr_ctx_to_vl_wf973 ORELSE
   use1 l4_vtr_ctx_to_vctx_wf973 ORELSE
   use1 l4_vl_ctx_wf_to_vctx_wf973 ORELSE
   FIRST_ASSUM (fun h -> ACCEPT_TAC (MATCH_MP l4_venv_wf_closed966 (MATCH_MP l4_ves_wf973 h))));;

let l4_conversion_progress_dis974 = end_itlist CONJ
  [distinctness "l4_conversion_progress597";
   GSYM (distinctness "l4_conversion_progress597");
   injectivity "l4_conversion_progress597"];;

let l4_khints_dis974 = end_itlist CONJ
  [distinctness "l4_khints493";
   GSYM (distinctness "l4_khints493");
   injectivity "l4_khints493"];;

(* 6a. Quick checks (`l4_core_quick596`) *)
let l4_core_quick_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_quick596 rec fuel g t s = L4KAccept491 (SOME T) ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hq")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hq" MP_TAC THEN REWRITE_TAC [l4_core_quick596] THEN
  COND_CASES_TAC THENL
  [DISCH_TAC THEN MATCH_MP_TAC l4_vtr_expr_core_alpha_eq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [(* L4KSort447, L4KSort447 *)
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a:l4_klevel447`;`t':l4_vexpr961`] l4_vtr_expr_inv_sort973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a':l4_klevel447`;`s':l4_vexpr961`] l4_vtr_expr_inv_sort973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `v':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vlevel_equiv961 u' v'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_klevel_equiv_sound_vlevel973 THEN
    MAP_EVERY EXISTS_TAC [`fuel:num`;`ps:l4_name list`;`a:l4_klevel447`;`a':l4_klevel447`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VSort961 u'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VSort961 v'` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLSucc961 u')` THEN
    MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC []];
   (* L4KLam447, L4KLam447 *)
   DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 (LABEL_TAC "H1") MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ok2:bool` (CONJUNCTS_THEN2 (LABEL_TAC "H2") MP_TAC)) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_kbinder447`;
                  `a2:l4_kexpr447`;`a3:l4_kexpr447`;`t':l4_vexpr961`] l4_vtr_expr_inv_lam973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `da':l4_vexpr961` (X_CHOOSE_THEN `ba':l4_vexpr961`
     (X_CHOOSE_THEN `ty_t:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0':l4_name`;`a1':l4_kbinder447`;
                  `a2':l4_kexpr447`;`a3':l4_kexpr447`;`s':l4_vexpr961`] l4_vtr_expr_inv_lam973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dc':l4_vexpr961` (X_CHOOSE_THEN `bc':l4_vexpr961`
     (X_CHOOSE_THEN `ty_s:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 da' /\ l4_vtr_expr973 env venv ps l a2' dc' /\
                 l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l da') a3 ba' /\
                 l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dc') a3' bc'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da' dc'`
     (X_CHOOSE_TAC `tac:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THENL
   [
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a2:l4_kexpr447`;`da':l4_vexpr961`;`a2':l4_kexpr447`;`dc':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da'` THEN
   REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `uA:l4_vlevel961`) THEN
   SUBGOAL_THEN `?u1. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 uA) tac (L4VSort961 u1)`
     (X_CHOOSE_TAC `u1:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`da':l4_vexpr961`;`da':l4_vexpr961`;`dc':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da' dc' (L4VSort961 uA)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tac:l4_vexpr961`;`u1:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `uA:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l da')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dc')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dc') (l4_vl_push_lam973 l da')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_push_lam974 THEN EXISTS_TAC `uA:l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l da') a3' bc'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_ctx973 THEN EXISTS_TAC `l4_vl_push_lam973 l dc'` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l da')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (l4_vl_push_lam973 l da')) ba' bc'`
     (X_CHOOSE_TAC `tbd:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THENL
   [
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`l4_kpush_binding532 g a2 NONE`;`l4_vl_push_lam973 l da'`;`a3:l4_kexpr447`;`ba':l4_vexpr961`;`a3':l4_kexpr447`;`bc':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VLam961 da' ba'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VLam961 dc' bc'` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 da' tbd` THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `uA:l4_vlevel961` THEN
    ASM_REWRITE_TAC []];
   (* L4KPi447, L4KPi447 *)
   DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 (LABEL_TAC "H1") MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ok2:bool` (CONJUNCTS_THEN2 (LABEL_TAC "H2") MP_TAC)) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_kbinder447`;
                  `a2:l4_kexpr447`;`a3:l4_kexpr447`;`t':l4_vexpr961`] l4_vtr_expr_inv_pi973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `da':l4_vexpr961` (X_CHOOSE_THEN `ba':l4_vexpr961`
     (X_CHOOSE_THEN `ty_t:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0':l4_name`;`a1':l4_kbinder447`;
                  `a2':l4_kexpr447`;`a3':l4_kexpr447`;`s':l4_vexpr961`] l4_vtr_expr_inv_pi973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dc':l4_vexpr961` (X_CHOOSE_THEN `bc':l4_vexpr961`
     (X_CHOOSE_THEN `ty_s:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 da' /\ l4_vtr_expr973 env venv ps l a2' dc' /\
                 l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l da') a3 ba' /\
                 l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dc') a3' bc'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da' dc'`
     (X_CHOOSE_TAC `tac:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THENL
   [
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a2:l4_kexpr447`;`da':l4_vexpr961`;`a2':l4_kexpr447`;`dc':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da'` THEN
   REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `uA:l4_vlevel961`) THEN
   SUBGOAL_THEN `?u1. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 uA) tac (L4VSort961 u1)`
     (X_CHOOSE_TAC `u1:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`da':l4_vexpr961`;`da':l4_vexpr961`;`dc':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da' dc' (L4VSort961 uA)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tac:l4_vexpr961`;`u1:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) da'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `uA:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l da')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dc')` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vl_ctx_defeq973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dc') (l4_vl_push_lam973 l da')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vl_ctx_defeq_push_lam974 THEN EXISTS_TAC `uA:l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l da') a3' bc'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_defeq_ctx973 THEN EXISTS_TAC `l4_vl_push_lam973 l dc'` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l da')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (l4_vl_push_lam973 l da')) ba' bc'`
     (X_CHOOSE_TAC `tbd:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THENL
   [
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`l4_kpush_binding532 g a2 NONE`;`l4_vl_push_lam973 l da'`;`a3:l4_kexpr447`;`ba':l4_vexpr961`;`a3':l4_kexpr447`;`bc':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?vB. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS da' (l4_vl_ctx973 l)) ba' (L4VSort961 vB)`
     (X_CHOOSE_TAC `vB:l4_vlevel961`) THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `da':l4_vexpr961`;`ba':l4_vexpr961`;`da':l4_vexpr961`;`ba':l4_vexpr961`]
      l4_vis_defeq_u_forallE_inv972) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_refl973 THEN
     EXISTS_TAC `ty_t:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC)];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (CONS da' (l4_vl_ctx973 l))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_vctx_wf966]; ALL_TAC] THEN
   SUBGOAL_THEN `?u2. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS da' (l4_vl_ctx973 l)) (L4VSort961 vB) tbd (L4VSort961 u2)`
     (X_CHOOSE_TAC `u2:l4_vlevel961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
    MAP_EVERY EXISTS_TAC [`ba':l4_vexpr961`;`ba':l4_vexpr961`;`bc':l4_vexpr961`] THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (CONS da' (l4_vl_ctx973 l)) ba' bc' (L4VSort961 vB)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
    MAP_EVERY EXISTS_TAC [`tbd:l4_vexpr961`;`u2:l4_vlevel961`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VForallE961 da' ba'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VForallE961 dc' bc'` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VSort961 (L4VLIMax961 uA vB)` THEN
    MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC []];
   (* L4KNatLit447, L4KNatLit447 *)
   DISCH_THEN SUBST_ALL_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KNatLit447 a'`] THEN
   ASM_REWRITE_TAC [];
   (* L4KStrLit447, L4KStrLit447 *)
   DISCH_THEN SUBST_ALL_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KStrLit447 a'`] THEN
   ASM_REWRITE_TAC [];
   (* L4KMData447, L4KMData447 *)
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_kexpr447`;`t':l4_vexpr961`;`a':l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_inv_mdata974 THEN
   ASM_REWRITE_TAC []]);;

(* 6b. True shortcut (`l4_core_true_shortcut597`) *)
let l4_core_is_true_eq974 = prove
 (`!e. l4_core_is_true597 e ==> e = L4KConst447 l4_core_true_name533 []`,
  GEN_TAC THEN REWRITE_TAC [l4_core_is_true597] THEN
  l4_subst_cases_tac974 (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  l4_subst_cases_tac974 (ISPEC `a1:l4_klevel447 list` list_CASES) THEN
  REWRITE_TAC [l4_conv_dis974] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let l4_core_true_shortcut_sound974 = prove
 (`!env venv ps chk rec g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_true_shortcut597 rec env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hsc")) THEN
  REMOVE_THEN "Hsc" MP_TAC THEN REWRITE_TAC [l4_core_true_shortcut597] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP l4_core_is_true_eq974) STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `tn:l4_kexpr447`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o MATCH_MP l4_core_is_true_eq974))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l tn t'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `t:l4_kexpr447`;`t':l4_vexpr961`;`tn:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
  MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KConst447 l4_core_true_name533 []`] THEN
  ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
  [l4_ctx_wf_tac974;
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l tn t'` THEN ASM_REWRITE_TAC [];
   UNDISCH_TAC `l4_vtr_expr973 env venv ps l s s'` THEN ASM_REWRITE_TAC []]);;

(* 6c. Proof irrelevance (`l4_core_proof_irrel596`) *)
let l4_core_proof_irrel_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_proof_irrel596 rec fuel g t s = L4KAccept491 (SOME T) ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hpi")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hpi" MP_TAC THEN REWRITE_TAC [l4_core_proof_irrel596;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `su:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `is_p:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `sty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun h ->
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`t':l4_vexpr961`;`ty:l4_kexpr447`] h) THEN
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`s:l4_kexpr447`;`s':l4_vexpr961`;`sty:l4_kexpr447`] h)) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `sty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `ty:l4_kexpr447`;`ty':l4_vexpr961`;`su:l4_klevel447`]
    l4_sort_of_sound_typed974) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `su':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' (L4VSort961 L4VLZero961)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`L4VSort961 su'`;`L4VLSucc961 su'`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN ASM_REWRITE_TAC [l4_vlevel_wf961] THEN
   MATCH_MP_TAC l4_klevel_equiv_sound_vlevel973 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`ps:l4_name list`;`su:l4_klevel447`;`L4KZero447`] THEN
   ASM_REWRITE_TAC [l4_tr_l967];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' sty'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`ty:l4_kexpr447`;`ty':l4_vexpr961`;`sty:l4_kexpr447`;`sty':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) s' ty'` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `sty':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty':l4_vexpr961` THEN
  MATCH_MP_TAC l4_vis_defeq_proof_irrel961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]);;

(* 6d. Nat offset (`l4_core_offset596`) *)
let l4_core_offset_sound974 = prove
 (`!env venv ps chk rec g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_offset596 rec env g t s = L4KAccept491 (SOME T) ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hoff")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_has_primitives973 env venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hoff" MP_TAC THEN REWRITE_TAC [l4_core_offset596] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  ABBREV_TAC
    `pred_of = \e. match e with
       | L4KNatLit447 n -> if n = 0 then NONE else SOME (L4KNatLit447 (n - 1))
       | L4KApp447 (L4KConst447 n []) a -> if n = l4_core_succ_name533 then SOME a else NONE
       | _ -> NONE` THEN
  ABBREV_TAC
    `is_zero = \e. match e with
       | L4KNatLit447 n -> n = 0
       | L4KConst447 n [] -> n = l4_core_zero_name533
       | _ -> F` THEN
  REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
  SUBGOAL_THEN
    `!e e'. l4_vtr_expr973 env venv ps l e e' /\ is_zero e ==>
            l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 0) e'`
    (LABEL_TAC "Hzero_s") THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "is_zero" THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   l4_subst_cases_tac974 (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THENL
   [l4_subst_cases_tac974 (ISPEC `a1:l4_klevel447 list` list_CASES) THEN
    REWRITE_TAC [l4_conv_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`l4_core_zero_name533`;`[]:l4_klevel447 list`;`e':l4_vexpr961`]
      l4_vtr_expr_inv_const973) THEN
    ASM_REWRITE_TAC [l4_tr_ls967;l4_conv_dis974] THEN
    DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list` (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `us':l4_vlevel961 list = []` SUBST_ALL_TAC THENL
    [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [l4_nat_lit973]];
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`0`;`e':l4_vexpr961`] l4_vtr_expr_inv_natlit974) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (L4VConst961 l4_core_succ_name533 []) (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973)`
    (LABEL_TAC "Hsucc") THENL
  [SUBGOAL_THEN
     `l4_venv_lookup_const961 venv l4_core_succ_name533
        (L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973))` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_has_primitives973 env venv` THEN REWRITE_TAC [l4_has_primitives973] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `l4_core_succ_name533`;
                  `L4VConstant961 0 (L4VForallE961 l4_vnat_ty973 l4_vnat_ty973)`;
                  `[]:l4_vlevel961 list`] l4_vhas_type_const973) THEN
   ASM_REWRITE_TAC [l4_vc_uvars961;l4_vc_type961;LENGTH;ALL;l4_vnat_ty973;l4_vinstL961;MAP];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!e e' p. l4_vtr_expr973 env venv ps l e e' /\ pred_of e = SOME p ==>
              ?p'. l4_vtr_expr973 env venv ps l p p' /\
                   l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) p' l4_vnat_ty973 /\
                   l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
                     (L4VApp961 (L4VConst961 l4_core_succ_name533 []) p') e'`
    (LABEL_TAC "Hpred_s") THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "pred_of" THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   l4_subst_cases_tac974 (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THENL
   [(* L4KApp447 *)
    l4_subst_cases_tac974 (SPEC `a0:l4_kexpr447` (cases "l4_kexpr447")) THEN
    REWRITE_TAC [l4_conv_dis974] THEN
    l4_subst_cases_tac974 (ISPEC `a1':l4_klevel447 list` list_CASES) THEN
    REWRITE_TAC [l4_conv_dis974] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`L4KConst447 l4_core_succ_name533 []`;`p:l4_kexpr447`;`e':l4_vexpr961`]
      l4_vtr_expr_inv_app973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `f':l4_vexpr961` (X_CHOOSE_THEN `p':l4_vexpr961`
      (X_CHOOSE_THEN `ty_app:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KConst447 l4_core_succ_name533 []) f' /\
                  l4_vtr_expr973 env venv ps l p p'` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`l4_core_succ_name533`;`[]:l4_klevel447 list`;`f':l4_vexpr961`]
      l4_vtr_expr_inv_const973) THEN
    ASM_REWRITE_TAC [l4_tr_ls967;l4_conv_dis974] THEN
    DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list` (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `us':l4_vlevel961 list = []` SUBST_ALL_TAC THENL
    [ASM_REWRITE_TAC []; ALL_TAC] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `[p':l4_vexpr961]`;`[p':l4_vexpr961]`;
                   `f':l4_vexpr961`;`L4VConst961 l4_core_succ_name533 []`;`ty_app:l4_vexpr961`]
      l4_vapps_defeq_congr_l974) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_vapps962;ALL2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
      MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                     `f':l4_vexpr961`;`p':l4_vexpr961`;`ty_app:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `da:l4_vexpr961` (X_CHOOSE_THEN `ba:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
      MATCH_MP_TAC l4_vis_defeq_u_refl973 THEN EXISTS_TAC `da:l4_vexpr961` THEN ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [l4_vapps962] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `ts:l4_vexpr961`) (LABEL_TAC "Hsa_eq")) THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `L4VConst961 l4_core_succ_name533 []`;`p':l4_vexpr961`;`ts:l4_vexpr961`]
      l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `da1:l4_vexpr961` (X_CHOOSE_THEN `ba1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `da1:l4_vexpr961`;`ba1:l4_vexpr961`;`l4_vnat_ty973`;`l4_vnat_ty973`]
      l4_vis_defeq_u_forallE_inv972) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_uniq_u972 THEN
     MAP_EVERY EXISTS_TAC [`L4VConst961 l4_core_succ_name533 []`;
                           `L4VConst961 l4_core_succ_name533 []`;
                           `L4VConst961 l4_core_succ_name533 []`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `u1:l4_vlevel961`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`da1:l4_vexpr961`;`u1:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961];
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VApp961 f' p'` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
    (* L4KNatLit447 *)
    COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l:l4_vl_ctx_rec973`;`a:num`;`e':l4_vexpr961`] l4_vtr_expr_inv_natlit974) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_nat_lit973 (a - 1)) l4_vnat_ty973`
      ASSUME_TAC THENL
    [MATCH_MP_TAC l4_nat_lit_has_type973 THEN EXISTS_TAC `env:l4_kdeclaration493 list` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    EXISTS_TAC `l4_nat_lit973 (a - 1)` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN
     ASM_REWRITE_TAC [];
     SUBGOAL_THEN `L4VApp961 (L4VConst961 l4_core_succ_name533 []) (l4_nat_lit973 (a - 1)) = l4_nat_lit973 a`
       (fun th -> ASM_REWRITE_TAC [th]) THEN
     SUBGOAL_THEN `a = SUC (a - 1)` (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th] THEN REWRITE_TAC [l4_nat_lit973]) THEN
     ASM_ARITH_TAC]];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [DISCH_TAC THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_nat_lit973 0` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN USE_THEN "Hzero_s" MATCH_MP_TAC THEN
    EXISTS_TAC `t:l4_kexpr447` THEN ASM_REWRITE_TAC [];
    USE_THEN "Hzero_s" MATCH_MP_TAC THEN EXISTS_TAC `s:l4_kexpr447` THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MP_TAC (ISPEC `(pred_of:l4_kexpr447->(l4_kexpr447)option) t` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `a:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
  MP_TAC (ISPEC `(pred_of:l4_kexpr447->(l4_kexpr447)option) s` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `b:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
  REMOVE_THEN "Hpred_s" (fun h ->
    MP_TAC (SPECL [`t:l4_kexpr447`;`t':l4_vexpr961`;`a:l4_kexpr447`] h) THEN
    MP_TAC (SPECL [`s:l4_kexpr447`;`s':l4_vexpr961`;`b:l4_kexpr447`] h)) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `b':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `a':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' b'`
    (X_CHOOSE_TAC `tab:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THENL
  [
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_kexpr447`;`a':l4_vexpr961`;`b:l4_kexpr447`;`b':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?u. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) l4_vnat_ty973 tab (L4VSort961 u)`
    (X_CHOOSE_TAC `u:l4_vlevel961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
   MAP_EVERY EXISTS_TAC [`a':l4_vexpr961`;`a':l4_vexpr961`;`b':l4_vexpr961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) a' b' l4_vnat_ty973`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`tab:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
       (L4VApp961 (L4VConst961 l4_core_succ_name533 []) a')
       (L4VApp961 (L4VConst961 l4_core_succ_name533 []) b')` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinst0961 l4_vnat_ty973 a'` THEN
   MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `l4_vnat_ty973` THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
  EXISTS_TAC `L4VApp961 (L4VConst961 l4_core_succ_name533 []) a'` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `L4VApp961 (L4VConst961 l4_core_succ_name533 []) b'` THEN
   ASM_REWRITE_TAC []]);;

(* 6e. Same head & argument list comparisons *)
let l4_core_same_head_sound974 = prove
 (`!env venv ps fuel l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_vl_ctx_wf973 venv (LENGTH ps) l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_same_head595 fuel t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hsh")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hsh" MP_TAC THEN REWRITE_TAC [l4_core_same_head595] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [(* L4KBVar447 *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KBVar447 a'`] THEN ASM_REWRITE_TAC [];
   (* L4KFVar447 *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KFVar447 a'`] THEN ASM_REWRITE_TAC [];
   (* L4KConst447 *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0':l4_name`;`a1:l4_klevel447 list`;`t':l4_vexpr961`]
     l4_vtr_expr_inv_const973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list` (X_CHOOSE_THEN `ci1:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0':l4_name`;`a1':l4_klevel447 list`;`s':l4_vexpr961`]
     l4_vtr_expr_inv_const973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `vs':l4_vlevel961 list` (X_CHOOSE_THEN `ci2:l4_vconstant961` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `ci1:l4_vconstant961 = ci2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`a0':l4_name`] THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `ALL2 l4_vlevel_equiv961 us' vs'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_klevels_equiv_sound_vlevels973 THEN
    MAP_EVERY EXISTS_TAC [`a1:l4_klevel447 list`;`fuel:num`;`ps:l4_name list`;`a1':l4_klevel447 list`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VConst961 a0' us'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VConst961 a0' vs'` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci2)` THEN
    MATCH_MP_TAC l4_vis_defeq_const961 THEN ASM_REWRITE_TAC []]]);;

let l4_core_compare_args_sound974 = prove
 (`!xs env venv ps chk rec g l ys xs' ys'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   ALL2 (l4_vtr_expr973 env venv ps l) xs xs' /\
   ALL2 (l4_vtr_expr973 env venv ps l) ys ys' /\
   l4_core_compare_args595 xs rec g ys = L4KAccept491 T ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l)) xs' ys'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `ys:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y:l4_kexpr447` (X_CHOOSE_THEN `ys_tl:l4_kexpr447 list` SUBST_ALL_TAC))) THEN
  MP_TAC (ISPEC `xs':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x':l4_vexpr961` (X_CHOOSE_THEN `xs'_tl:l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  MP_TAC (ISPEC `ys':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y':l4_vexpr961` (X_CHOOSE_THEN `ys'_tl:l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC [l4_core_compare_args595;ALL2;l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`h:l4_kexpr447`;`x':l4_vexpr961`;`y:l4_kexpr447`;`y':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;
                         `rec:l4_kmethods543`;`g:l4_kcontext532`;`ys_tl:l4_kexpr447 list`] THEN
   ASM_REWRITE_TAC []]);;

let l4_core_compare_args_both_sound974 = prove
 (`!xs env venv ps chk rec g l ys xs' ys'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   ALL2 (l4_vtr_expr973 env venv ps l) xs xs' /\
   ALL2 (l4_vtr_expr973 env venv ps l) ys ys' /\
   l4_core_compare_args_filtered595 xs T rec env g ys = L4KAccept491 T /\
   l4_core_compare_args_filtered595 xs F rec env g ys = L4KAccept491 T ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l)) xs' ys'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `ys:l4_kexpr447 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y:l4_kexpr447` (X_CHOOSE_THEN `ys_tl:l4_kexpr447 list` SUBST_ALL_TAC))) THEN
  MP_TAC (ISPEC `xs':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x':l4_vexpr961` (X_CHOOSE_THEN `xs'_tl:l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  MP_TAC (ISPEC `ys':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y':l4_vexpr961` (X_CHOOSE_THEN `ys'_tl:l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC [l4_core_compare_args_filtered595;ALL2;l4_conv_dis974] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "H2")) THEN
  REMOVE_THEN "H2" (fun h2 -> POP_ASSUM (LABEL_TAC "H1") THEN LABEL_TAC "H2" h2) THEN
  ASM_CASES_TAC `l4_core_is_cheap_arg595 env h /\ l4_core_is_cheap_arg595 env y` THENL
  [REMOVE_THEN "H1" MP_TAC THEN REMOVE_THEN "H2" MP_TAC THEN
   ASM_REWRITE_TAC [l4_kr_bind_accept967] THEN DISCH_TAC THEN
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`h:l4_kexpr447`;`x':l4_vexpr961`;`y:l4_kexpr447`;`y':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;
                          `rec:l4_kmethods543`;`g:l4_kcontext532`;`ys_tl:l4_kexpr447 list`] THEN
    ASM_REWRITE_TAC []];
   REMOVE_THEN "H2" MP_TAC THEN REMOVE_THEN "H1" MP_TAC THEN
   ASM_REWRITE_TAC [l4_kr_bind_accept967] THEN DISCH_TAC THEN
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`h:l4_kexpr447`;`x':l4_vexpr961`;`y:l4_kexpr447`;`y':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;
                          `rec:l4_kmethods543`;`g:l4_kcontext532`;`ys_tl:l4_kexpr447 list`] THEN
    ASM_REWRITE_TAC []]]);;

let l4_core_compare_args_cheap_first_sound974 = prove
 (`!env venv ps chk rec g l xs ys xs' ys'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   ALL2 (l4_vtr_expr973 env venv ps l) xs xs' /\
   ALL2 (l4_vtr_expr973 env venv ps l) ys ys' /\
   l4_core_compare_args_cheap_first595 rec env g xs ys = L4KAccept491 T ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l)) xs' ys'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_compare_args_cheap_first595;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  MATCH_MP_TAC l4_core_compare_args_both_sound974 THEN
  MAP_EVERY EXISTS_TAC [`xs:l4_kexpr447 list`;`env:l4_kdeclaration493 list`;
                        `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`ys:l4_kexpr447 list`] THEN
  ASM_REWRITE_TAC []);;

let l4_all2_append974 = prove
 (`!(R:A->B->bool) xs1 xs2 ys1 ys2.
   ALL2 R xs1 ys1 /\ ALL2 R xs2 ys2 ==> ALL2 R (APPEND xs1 xs2) (APPEND ys1 ys2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  l4_subst_cases_tac974 (ISPEC `ys1:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_all2_reverse974 = prove
 (`!(R:A->B->bool) xs ys. ALL2 R xs ys ==> ALL2 R (REVERSE xs) (REVERSE ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  l4_subst_cases_tac974 (ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC [ALL2;REVERSE] THEN STRIP_TAC THEN
  MATCH_MP_TAC l4_all2_append974 THEN ASM_REWRITE_TAC [ALL2] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

(* 6f. Speculative congruence (`l4_core_congruent_apps595`, `l4_core_delta_congruent595`) *)
let l4_core_congruent_apps_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_congruent_apps595 rec fuel g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hc")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hc" MP_TAC THEN REWRITE_TAC [l4_core_congruent_apps595] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  ABBREV_TAC `tf = FST (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
  ABBREV_TAC `ta = SND (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
  ABBREV_TAC `sf = FST (l4_ksplit_app489 (L4KApp447 a0' a1'))` THEN
  ABBREV_TAC `sa = SND (l4_ksplit_app489 (L4KApp447 a0' a1'))` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 ta tf = L4KApp447 a0 a1 /\
                l4_kapply_exprs489 sa sf = L4KApp447 a0' a1'` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["tf";"ta";"sf";"sa"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `same:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 (SUBST_ALL_TAC o EQT_INTRO) ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 ta tf) t'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `tf':l4_vexpr961` (X_CHOOSE_THEN `ta':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 sa sf) s'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `sf':l4_vexpr961` (X_CHOOSE_THEN `sa':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tf' sf'` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_core_same_head_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`fuel:num`;`tf:l4_kexpr447`;`sf:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)) (REVERSE ta') (REVERSE sa')`
    (MP_TAC o MATCH_MP l4_all2_reverse974) THENL
  [MATCH_MP_TAC l4_core_compare_args_sound974 THEN
   MAP_EVERY EXISTS_TAC [`REVERSE (ta:l4_kexpr447 list)`;`env:l4_kdeclaration493 list`;
                         `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`REVERSE (sa:l4_kexpr447 list)`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_all2_reverse974 THEN
   MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [REVERSE_REVERSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?ty_t. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 ta' tf') ty_t`
    (X_CHOOSE_TAC `ty_t:l4_vexpr961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `t':l4_vexpr961` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                 `ta':l4_vexpr961 list`;`sa':l4_vexpr961 list`;
                 `tf':l4_vexpr961`;`sf':l4_vexpr961`;`ty_t:l4_vexpr961`]
    l4_vapps_defeq_congr_l974) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 ta' tf'` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 sa' sf'` THEN
   ASM_REWRITE_TAC []]);;

let l4_core_delta_congruent_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_delta_congruent595 rec fuel env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hdc")) THEN
  REMOVE_THEN "Hdc" MP_TAC THEN REWRITE_TAC [l4_core_delta_congruent595] THEN
  MP_TAC (ISPEC `l4_core_delta_info538 env t` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `dt:l4_kdeclaration493` (fun th -> REWRITE_TAC [th;l4_conv_dis974]))) THEN
  MP_TAC (ISPEC `l4_core_delta_info538 env s` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `ds:l4_kdeclaration493` (fun th -> REWRITE_TAC [th;l4_conv_dis974]))) THEN
  MP_TAC (SPEC `l4_keffective_hints493 dt` (cases "l4_khints493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
    (fun th ->
       if is_exists (concl th) then
         X_CHOOSE_THEN `ht:num` (fun h -> REWRITE_TAC [h;l4_khints_dis974;l4_conv_dis974]) th
       else REWRITE_TAC [th;l4_khints_dis974;l4_conv_dis974])) THEN
  MP_TAC (SPEC `l4_keffective_hints493 ds` (cases "l4_khints493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
    (fun th ->
       if is_exists (concl th) then
         X_CHOOSE_THEN `hs:num` (fun h -> REWRITE_TAC [h;l4_khints_dis974;l4_conv_dis974]) th
       else REWRITE_TAC [th;l4_khints_dis974;l4_conv_dis974])) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  MATCH_MP_TAC l4_core_congruent_apps_sound974 THEN
  MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                        `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
  ASM_REWRITE_TAC []);;

(* 6g. Opposite projection unfolding *)
let l4_core_try_unfold_proj_app_sound974 = prove
 (`!env venv ps chk rec g l e e' e1.
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_try_unfold_proj_app596 rec g e = L4KAccept491 (SOME e1) ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hu")) THEN
  REMOVE_THEN "Hu" MP_TAC THEN REWRITE_TAC [l4_core_try_unfold_proj_app596] THEN
  l4_subst_cases_tac974 (SPEC `FST (l4_ksplit_app489 e)` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MATCH_MP_TAC o SPECL [`F`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                    `e:l4_kexpr447`;`e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC []);;

let l4_core_opposite_projection_sound974 = prove
 (`!env venv ps chk rec g l t s t' s' tn sn.
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_opposite_projection596 rec env g t s = L4KAccept491 (SOME (tn, sn)) ==>
   l4_vtr_expr973 env venv ps l tn t' /\ l4_vtr_expr973 env venv ps l sn s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hop")) THEN
  REMOVE_THEN "Hop" MP_TAC THEN REWRITE_TAC [l4_core_opposite_projection596] THEN
  MP_TAC (ISPEC `l4_core_delta_info538 env t` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `dt:l4_kdeclaration493` (fun th -> REWRITE_TAC [th;l4_conv_dis974]))) THEN
  MP_TAC (ISPEC `l4_core_delta_info538 env s` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `ds:l4_kdeclaration493` (fun th -> REWRITE_TAC [th;l4_conv_dis974]))) THEN
  REWRITE_TAC [l4_kr_bind_accept967] THENL
  [(* NONE, SOME ds *)
   DISCH_THEN (X_CHOOSE_THEN `red:(l4_kexpr447)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   l4_subst_cases_tac974 (ISPEC `red:(l4_kexpr447)option` (cases "option")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_try_unfold_proj_app_sound974 THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`t:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   (* SOME dt, NONE *)
   DISCH_THEN (X_CHOOSE_THEN `red:(l4_kexpr447)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   l4_subst_cases_tac974 (ISPEC `red:(l4_kexpr447)option` (cases "option")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_try_unfold_proj_app_sound974 THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []]);;

(* 6h. Lazy delta loop (`l4_core_lazy_delta597`) *)
let l4_core_lazy_delta_sound974 = prove
 (`!rounds env venv ps chk rec fuel g l t s t' s' prog.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_lazy_delta597 rounds rec fuel env ps g t s = L4KAccept491 prog ==>
   match prog with
   | L4ConversionDone597 T -> l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'
   | L4ConversionDone597 F -> T
   | L4ConversionStuck597 tn sn ->
       l4_vtr_expr973 env venv ps l tn t' /\ l4_vtr_expr973 env venv ps l sn s'`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_core_lazy_delta597;l4_conv_dis974] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hld")) THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hld" MP_TAC THEN REWRITE_TAC [l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
  (* 1. core_quick *)
  DISCH_THEN (X_CHOOSE_THEN `quick:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `quick:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [ALL_TAC;
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
   DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `a:bool` BOOL_CASES_AX) THEN REWRITE_TAC [l4_conversion_progress_dis974] THEN
   MATCH_MP_TAC l4_core_quick_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 2. core_offset *)
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `offset:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `offset:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [ALL_TAC;
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
   DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `a:bool` BOOL_CASES_AX) THEN REWRITE_TAC [l4_conversion_progress_dis974] THEN
   MATCH_MP_TAC l4_core_offset_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 3. reduce_nat t *)
  ABBREV_TAC
    `elig = l4_pair_probe_guard543
      (l4_nat_probe_head543 env (l4_ksplit_app489 t))
      (l4_nat_probe_head543 env (l4_ksplit_app489 s))
      (\ignored. l4_nat_probe_allowed543 (l4_method_mode543 rec) t s)` THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `tn:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hnt") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `tn:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN
   DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `ok:bool` BOOL_CASES_AX) THEN REWRITE_TAC [l4_conversion_progress_dis974] THEN
   REMOVE_THEN "Hnt" MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`a:l4_kexpr447`;`t':l4_vexpr961`;`s:l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_reduce_nat_sound974 THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 4. reduce_nat s *)
  DISCH_THEN (X_CHOOSE_THEN `sn:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hns") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `sn:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN
   DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `ok:bool` BOOL_CASES_AX) THEN REWRITE_TAC [l4_conversion_progress_dis974] THEN
   REMOVE_THEN "Hns" MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`t':l4_vexpr961`;`a:l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_reduce_nat_sound974 THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 5. reduce_native t, s *)
  DISCH_THEN (X_CHOOSE_THEN `ntv_t:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hntv") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `ntv_t:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   MP_TAC (SPECL [`t:l4_kexpr447`;`a:l4_kexpr447`] l4_core_reduce_native_sound974) THEN
   ASM_REWRITE_TAC []] THEN
  DISCH_THEN (X_CHOOSE_THEN `ntv_s:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hnsv") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `ntv_s:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   MP_TAC (SPECL [`s:l4_kexpr447`;`a:l4_kexpr447`] l4_core_reduce_native_sound974) THEN
   ASM_REWRITE_TAC []] THEN
  (* 6. delta_congruent *)
  DISCH_THEN (X_CHOOSE_THEN `same:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [DISCH_THEN (SUBST_ALL_TAC o SYM) THEN REWRITE_TAC [l4_conversion_progress_dis974] THEN
   MATCH_MP_TAC l4_core_delta_congruent_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  (* 7. opposite_projection *)
  DISCH_THEN (X_CHOOSE_THEN `proj:(l4_kexpr447#l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hop") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `proj:(l4_kexpr447#l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                  `t:l4_kexpr447`;`s:l4_kexpr447`;`t':l4_vexpr961`;`s':l4_vexpr961`;
                  `FST (a:l4_kexpr447#l4_kexpr447)`;`SND (a:l4_kexpr447#l4_kexpr447)`]
     l4_core_opposite_projection_sound974) THEN
   ASM_REWRITE_TAC [PAIR] THEN STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;
                         `FST (a:l4_kexpr447#l4_kexpr447)`;`SND (a:l4_kexpr447#l4_kexpr447)`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 8. unfold sides *)
  ABBREV_TAC `sides = l4_core_delta_sides538 env t s` THEN
  DISCH_THEN (X_CHOOSE_THEN `td:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Htd")
    (X_CHOOSE_THEN `sd:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hsd") MP_TAC)))) THEN
  SUBGOAL_THEN `!e. td = SOME e ==> l4_vtr_expr973 env venv ps l e t'` (LABEL_TAC "Htd_tr") THENL
  [GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "Htd" MP_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `t:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `!e. sd = SOME e ==> l4_vtr_expr973 env venv ps l e s'` (LABEL_TAC "Hsd_tr") THENL
  [GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "Hsd" MP_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `s:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  l4_subst_cases_tac974 (ISPEC `td:(l4_kexpr447)option` (cases "option")) THEN
  l4_subst_cases_tac974 (ISPEC `sd:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [(* NONE, NONE *)
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [l4_conversion_progress_dis974];
   (* NONE, SOME a *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Heq_t1")
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
   REMOVE_THEN "Heq_t1" (SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s1:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`s':l4_vexpr961`;`s1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN USE_THEN "Hsd_tr" MATCH_MP_TAC THEN REFL_TAC;
   (* SOME a, NONE *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Heq_s1") ASSUME_TAC)))) THEN
   REMOVE_THEN "Heq_s1" (SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t1:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`t':l4_vexpr961`;`t1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN USE_THEN "Htd_tr" MATCH_MP_TAC THEN REFL_TAC;
   (* SOME a, SOME a' *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t1:l4_kexpr447`;`s1:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `a:l4_kexpr447`;`t':l4_vexpr961`;`t1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN USE_THEN "Htd_tr" MATCH_MP_TAC THEN REFL_TAC;
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `a':l4_kexpr447`;`s':l4_vexpr961`;`s1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN USE_THEN "Hsd_tr" MATCH_MP_TAC THEN REFL_TAC]]);;

(* 6i. Lazy delta projection loop (`l4_core_lazy_delta_proj597`) *)
let l4_core_lazy_delta_proj_sound974 = prove
 (`!rounds env venv ps chk rec fuel g l owner1 owner2 idx te' se' pv1 pv2 fty1 fty2 t s.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner1 idx te' pv1 fty1 /\
   l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner2 idx se' pv2 fty2 /\
   l4_vtr_expr973 env venv ps l t te' /\
   l4_vtr_expr973 env venv ps l s se' /\
   l4_core_lazy_delta_proj597 rounds rec fuel env ps g idx t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) pv1 pv2`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_core_lazy_delta_proj597;l4_conv_dis974] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hlp")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hlp" MP_TAC THEN REWRITE_TAC [l4_kr_bind_accept967;LET_DEF;LET_END_DEF] THEN
  (* 1. core_quick *)
  DISCH_THEN (X_CHOOSE_THEN `quick:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `quick:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [ALL_TAC;
   l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `l4_vl_ctx973 l`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                  `te':l4_vexpr961`;`se':l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                  `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_quick_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN ASM_REWRITE_TAC []]] THEN
  (* 2. delta_congruent *)
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `same:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [TRY DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `l4_vl_ctx973 l`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                  `te':l4_vexpr961`;`se':l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                  `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_core_delta_congruent_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  (* 3. opposite_projection *)
  DISCH_THEN (X_CHOOSE_THEN `proj:(l4_kexpr447#l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hop") MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `proj:(l4_kexpr447#l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [ALL_TAC;
   DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                  `t:l4_kexpr447`;`s:l4_kexpr447`;`te':l4_vexpr961`;`se':l4_vexpr961`;
                  `FST (a:l4_kexpr447#l4_kexpr447)`;`SND (a:l4_kexpr447#l4_kexpr447)`]
     l4_core_opposite_projection_sound974) THEN
   ASM_REWRITE_TAC [PAIR] THEN STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                         `te':l4_vexpr961`;`se':l4_vexpr961`;`fty1:l4_vexpr961`;`fty2:l4_vexpr961`;
                         `FST (a:l4_kexpr447#l4_kexpr447)`;`SND (a:l4_kexpr447#l4_kexpr447)`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 4. unfold sides *)
  ABBREV_TAC `sides = l4_core_delta_sides538 env t s` THEN
  DISCH_THEN (X_CHOOSE_THEN `td:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Htd")
    (X_CHOOSE_THEN `sd:(l4_kexpr447)option` (CONJUNCTS_THEN2 (LABEL_TAC "Hsd") MP_TAC)))) THEN
  SUBGOAL_THEN `!e. td = SOME e ==> l4_vtr_expr973 env venv ps l e te'` (LABEL_TAC "Htd_tr") THENL
  [GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "Htd" MP_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `t:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `!e. sd = SOME e ==> l4_vtr_expr973 env venv ps l e se'` (LABEL_TAC "Hsd_tr") THENL
  [GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "Hsd" MP_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_unfold_sound974 THEN EXISTS_TAC `s:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  l4_subst_cases_tac974 (ISPEC `td:(l4_kexpr447)option` (cases "option")) THEN
  l4_subst_cases_tac974 (ISPEC `sd:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [(* NONE, NONE: try core_reduce_proj_core595 on both *)
   MP_TAC (ISPEC `l4_core_reduce_proj_core595 env idx t` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_conv_dis974])
     (X_CHOOSE_THEN `tf:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
   MP_TAC (ISPEC `l4_core_reduce_proj_core595 env idx s` (cases "option")) THEN
   DISCH_THEN (DISJ_CASES_THEN2
     (fun th -> REWRITE_TAC [th;l4_conv_dis974])
     (X_CHOOSE_THEN `sf:l4_kexpr447` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
   DISCH_TAC THENL
   [(* NONE, NONE *)
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_ctx973 l`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                   `te':l4_vexpr961`;`se':l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                   `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`te':l4_vexpr961`;`s:l4_kexpr447`;`se':l4_vexpr961`]) THEN
     ASM_REWRITE_TAC [];
     STRIP_TAC THEN ASM_REWRITE_TAC []];
    (* NONE, SOME sf *)
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_ctx973 l`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                   `te':l4_vexpr961`;`se':l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                   `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`te':l4_vexpr961`;`s:l4_kexpr447`;`se':l4_vexpr961`]) THEN
     ASM_REWRITE_TAC [];
     STRIP_TAC THEN ASM_REWRITE_TAC []];
    (* SOME tf, NONE *)
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                   `l4_vl_ctx973 l`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                   `te':l4_vexpr961`;`se':l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                   `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`te':l4_vexpr961`;`s:l4_kexpr447`;`se':l4_vexpr961`]) THEN
     ASM_REWRITE_TAC [];
     STRIP_TAC THEN ASM_REWRITE_TAC []];
    (* SOME tf, SOME sf *)
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`l:l4_vl_ctx_rec973`;
                   `owner1:l4_name`;`idx:num`;`t:l4_kexpr447`;`te':l4_vexpr961`;
                   `pv1:l4_vexpr961`;`fty1:l4_vexpr961`;`tf:l4_kexpr447`]
      l4_core_reduce_proj_core_sound974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `tf':l4_vexpr961` STRIP_ASSUME_TAC) THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`l:l4_vl_ctx_rec973`;
                   `owner2:l4_name`;`idx:num`;`s:l4_kexpr447`;`se':l4_vexpr961`;
                   `pv2:l4_vexpr961`;`fty2:l4_vexpr961`;`sf:l4_kexpr447`]
      l4_core_reduce_proj_core_sound974) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `sf':l4_vexpr961` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tf' sf'` ASSUME_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`tf:l4_kexpr447`;`tf':l4_vexpr961`;`sf:l4_kexpr447`;`sf':l4_vexpr961`]) THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `tf':l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
    EXISTS_TAC `sf':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
   (* NONE, SOME a *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Heq_t1")
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
   REMOVE_THEN "Heq_t1" (SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                         `te':l4_vexpr961`;`se':l4_vexpr961`;`fty1:l4_vexpr961`;`fty2:l4_vexpr961`;
                         `t:l4_kexpr447`;`s1:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`se':l4_vexpr961`;`s1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN USE_THEN "Hsd_tr" MATCH_MP_TAC THEN REFL_TAC;
   (* SOME a, NONE *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 (LABEL_TAC "Heq_s1") ASSUME_TAC)))) THEN
   REMOVE_THEN "Heq_s1" (SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                         `te':l4_vexpr961`;`se':l4_vexpr961`;`fty1:l4_vexpr961`;`fty2:l4_vexpr961`;
                         `t1:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`te':l4_vexpr961`;`t1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [] THEN USE_THEN "Htd_tr" MATCH_MP_TAC THEN REFL_TAC;
   (* SOME a, SOME a' *)
   DISCH_THEN (X_CHOOSE_THEN `t1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `s1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`owner1:l4_name`;`owner2:l4_name`;`idx:num`;
                         `te':l4_vexpr961`;`se':l4_vexpr961`;`fty1:l4_vexpr961`;`fty2:l4_vexpr961`;
                         `t1:l4_kexpr447`;`s1:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `a:l4_kexpr447`;`te':l4_vexpr961`;`t1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN USE_THEN "Htd_tr" MATCH_MP_TAC THEN REFL_TAC;
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf_core974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `a':l4_kexpr447`;`se':l4_vexpr961`;`s1:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN USE_THEN "Hsd_tr" MATCH_MP_TAC THEN REFL_TAC]]);;
(* ========================================================================= *)
(* SECTION 6b: ETA, HEADS, STRUCTURE ETA, UNIT-LIKE, STRING EXPANSION,       *)
(*             FALLBACK, FINISH CONVERSION, AND DEFEQ_STEP SOUNDNESS         *)
(* Mirrors rocq/VerifyTypeChecker.v Section 6j-6n (lines 4332-5175).         *)
(* ========================================================================= *)

(* Small helpers for BVar 0 and eta expansion *)
let l4_vhas_type_bvar0_974 = prove
 (`!venv uvars g dom'.
   l4_vhas_type961 venv uvars (CONS dom' g) (L4VBVar961 0) (l4_vlift961 dom')`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_bvar961 THEN REWRITE_TAC [l4_vlookup_RULES961]);;

let l4_vtr_expr_bvar0_push_lam974 = prove
 (`!env venv ps l dom'.
   l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') (L4KBVar447 0) (L4VBVar961 0)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
  MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `l4_vlift961 dom'` THEN
  REWRITE_TAC [l4_vl_bvar973;l4_vl_push_lam973;l4_vl_bound973;l4_vl_lookup_bound973;
               l4_vl_ctx_push_lam973;l4_vlift961;ONE;l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_bvar961 THEN
  REWRITE_TAC [GSYM ONE;GSYM l4_vlift961;l4_vlookup_RULES961]);;

let l4_all2_map_lift_lam974 = prove
 (`!args env venv ps l dom' args'.
   l4_venv_closed966 venv /\
   ALL2 (l4_vtr_expr973 env venv ps l) args args' ==>
   ALL2 (l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom'))
     (MAP (\a. l4_klift447 a 1 0) args) (MAP l4_vlift961 args')`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `args':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x':l4_vexpr961` (X_CHOOSE_THEN `xs':l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC [ALL2;MAP] THEN STRIP_TAC THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_lift_lam973 THEN ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_all2_vtr_s_refl_u974 = prove
 (`!xs env venv ps l xs'.
   ALL2 (l4_vtr_expr_s973 env venv ps l) xs xs' ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l)) xs' xs'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `xs':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x':l4_vexpr961` (X_CHOOSE_THEN `r':l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC [ALL2] THEN STRIP_TAC THEN CONJ_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`h:l4_kexpr447`;`x':l4_vexpr961`] l4_vtr_expr_s_has_type973) THEN
   ASM_REWRITE_TAC [l4_vis_defeq_u961;l4_vhas_type961];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`] THEN ASM_REWRITE_TAC []]);;

let l4_core_inductive_inv974 = prove
 (`!env own info.
   l4_core_inductive532 env own = SOME info ==>
   ?d_ind. l4_kfind_decl493 env own = SOME d_ind /\
           l4_kdecl_kind493 d_ind = L4KDInductive493 info`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_inductive532] THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env own` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
    (fun th ->
       if is_exists (concl th) then
         let v, _ = dest_exists (concl th) in
         X_CHOOSE_THEN (mk_var ("kd", type_of v)) (fun h -> ASSUME_TAC h THEN REWRITE_TAC [h;l4_conv_dis974]) th
       else REWRITE_TAC [th;l4_conv_dis974])) THEN
  DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `d:l4_kdeclaration493` THEN ASM_REWRITE_TAC []);;

let l4_core_constructor_inv974 = prove
 (`!env ctor c.
   l4_core_constructor532 env ctor = SOME c ==>
   ?d_ctor. l4_kfind_decl493 env ctor = SOME d_ctor /\
            l4_kdecl_kind493 d_ctor = L4KDConstructor493 c`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_constructor532] THEN
  MP_TAC (ISPEC `l4_kfind_decl493 env ctor` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th]))) THEN
  MP_TAC (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN
    (fun th ->
       if is_exists (concl th) then
         let v, _ = dest_exists (concl th) in
         X_CHOOSE_THEN (mk_var ("kd", type_of v)) (fun h -> ASSUME_TAC h THEN REWRITE_TAC [h;l4_conv_dis974]) th
       else REWRITE_TAC [th;l4_conv_dis974])) THEN
  DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `d:l4_kdeclaration493` THEN ASM_REWRITE_TAC []);;

(* 6j. Lambda eta (`l4_eta_compare595`, `l4_core_eta_expand_pis595`, `l4_core_eta_expand595`) *)
let l4_eta_compare_sound974 = prove
 (`!env venv ps chk rec g l nm bi dom body other t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l (L4KLam447 nm bi dom body) t' /\
   l4_vtr_expr973 env venv ps l other s' /\
   l4_eta_compare595 rec g dom body other = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Heta")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Heta" MP_TAC THEN REWRITE_TAC [l4_eta_compare595;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  l4_subst_cases_tac974 (SPEC `ty:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 (LABEL_TAC "Hdom_eq") MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`nm:l4_name`;`bi:l4_kbinder447`;
                 `dom:l4_kexpr447`;`body:l4_kexpr447`;`t':l4_vexpr961`] l4_vtr_expr_inv_lam973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961`
    (X_CHOOSE_THEN `ty_lam:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                              `other:l4_kexpr447`;`s':l4_vexpr961`;`ty0:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) ty'`
    (MP_TAC o MATCH_MP l4_vtr_expr_inv_pi973) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `ty0:l4_kexpr447`;`ty':l4_vexpr961`;`L4KPi447 a0 a1 a2 a3`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `dom2':l4_vexpr961` (X_CHOOSE_THEN `cod2':l4_vexpr961`
    (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l dom dom' /\
                l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') body body' /\
                l4_vtr_expr973 env venv ps l a2 dom2'` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom2'`
    (X_CHOOSE_TAC `td:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `dom:l4_kexpr447`;`dom':l4_vexpr961`;
                                     `a2:l4_kexpr447`;`dom2':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
  REWRITE_TAC [l4_vis_type961] THEN DISCH_THEN (X_CHOOSE_TAC `u1:l4_vlevel961`) THEN
  SUBGOAL_THEN `?u_eq. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VSort961 u1) td (L4VSort961 u_eq)`
    (X_CHOOSE_TAC `u_eq:l4_vlevel961`) THENL
  [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
   MAP_EVERY EXISTS_TAC [`dom':l4_vexpr961`;`dom':l4_vexpr961`;`dom2':l4_vexpr961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom' dom2' (L4VSort961 u1)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`td:l4_vexpr961`;`u_eq:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?v2. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom2' (l4_vl_ctx973 l)) cod2' (L4VSort961 v2)`
    (X_CHOOSE_TAC `v2:l4_vlevel961`) THENL
  [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `dom2':l4_vexpr961`;`cod2':l4_vexpr961`;`dom2':l4_vexpr961`;`cod2':l4_vexpr961`]
     l4_vis_defeq_u_forallE_inv972) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_refl973 THEN
    EXISTS_TAC `ty_pi:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC)];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) s' (L4VForallE961 dom' cod2')`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vhas_type961] THEN MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`L4VForallE961 dom2' cod2'`;`L4VLIMax961 u1 v2`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_forall961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_conv_u974 THEN
    EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vis_type961] THEN EXISTS_TAC `u1:l4_vlevel961` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g dom NONE) (l4_vl_push_lam973 l dom')`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom')` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') (l4_klift447 other 1 0) (l4_vlift961 s')`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_lift_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))
       (l4_vlift961 s') (L4VForallE961 (l4_vlift961 dom') (l4_vliftN961 cod2' 1 1))` ASSUME_TAC THENL
  [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`dom':l4_vexpr961`;
                  `s':l4_vexpr961`;`s':l4_vexpr961`;`L4VForallE961 dom' cod2'`] l4_vis_defeq_weak966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vlift961;l4_vliftN961;ARITH_RULE `SUC 0 = 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))
       (L4VApp961 (l4_vlift961 s') (L4VBVar961 0)) (l4_vinst0961 (l4_vliftN961 cod2' 1 1) (L4VBVar961 0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_app972 THEN EXISTS_TAC `l4_vlift961 dom'` THEN
   ASM_REWRITE_TAC [l4_vhas_type_bvar0_974];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom')
       (L4KApp447 (l4_klift447 other 1 0) (L4KBVar447 0))
       (L4VApp961 (l4_vlift961 s') (L4VBVar961 0))` ASSUME_TAC THENL
  [MP_TAC (SPECL [`[L4KBVar447 0]`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_vl_push_lam973 l dom'`;`l4_klift447 other 1 0`;`l4_vlift961 s'`;
                  `[L4VBVar961 0]`;`l4_vinst0961 (l4_vliftN961 cod2' 1 1) (L4VBVar961 0)`]
     l4_vtr_expr_kapply973) THEN
   ASM_REWRITE_TAC [l4_kapply_exprs489;l4_vapps962;ALL2;l4_vl_ctx_push_lam973;l4_vtr_expr_bvar0_push_lam974];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (l4_vl_push_lam973 l dom'))
       body' (L4VApp961 (l4_vlift961 s') (L4VBVar961 0))`
    (X_CHOOSE_TAC `tb:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`l4_kpush_binding532 g dom NONE`;`l4_vl_push_lam973 l dom'`;
      `body:l4_kexpr447`;`body':l4_vexpr961`;
      `L4KApp447 (l4_klift447 other 1 0) (L4KBVar447 0)`;
      `L4VApp961 (l4_vlift961 s') (L4VBVar961 0)`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VLam961 dom' body'` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `L4VLam961 dom' (L4VApp961 (l4_vlift961 s') (L4VBVar961 0))` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom' tb` THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u1:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom' cod2'` THEN
    MATCH_MP_TAC l4_vis_defeq_eta961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]]]);;

let l4_core_eta_expand_pis_sound974 = prove
 (`!eta_fuel env venv ps chk rec g l e ty args e' ty' args' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_vtr_expr973 env venv ps l ty ty' /\
   ALL2 (l4_vtr_expr973 env venv ps l) args args' /\
   l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) (l4_vapps962 args' e') ty' /\
   l4_core_eta_expand_pis595 eta_fuel rec g e ty args = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res (l4_vapps962 args' e')`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_core_eta_expand_pis595;l4_conv_dis974] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hexp")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hexp" MP_TAC THEN
  l4_subst_cases_tac974 (SPEC `ty:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  TRY (DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
       MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
       ASM_REWRITE_TAC []) THEN
  (* Only L4KPi447 a0 a1 a2 a3 remains *)
  DISCH_THEN (X_CHOOSE_THEN `body1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `rest:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))))) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_kbinder447`;
                 `a2:l4_kexpr447`;`a3:l4_kexpr447`;`ty':l4_vexpr961`] l4_vtr_expr_inv_pi973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961`
    (X_CHOOSE_THEN `ty_pi:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 dom' /\
                l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') a3 body'` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) (l4_vl_push_lam973 l dom')` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vl_ctx_wf_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') body1 body'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`l4_kpush_binding532 g a2 NONE`;`l4_vl_push_lam973 l dom'`;
                                     `a3:l4_kexpr447`;`body':l4_vexpr961`;`body1:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL2 (l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom'))
       (APPEND (MAP (\a. l4_klift447 a 1 0) args) [L4KBVar447 0])
       (APPEND (MAP l4_vlift961 args') [L4VBVar961 0])` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_all2_append974 THEN REWRITE_TAC [ALL2;l4_vtr_expr_bvar0_push_lam974] THEN
   MATCH_MP_TAC l4_all2_map_lift_lam974 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 args' e') (L4VForallE961 dom' body')`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vapps962 (APPEND (MAP l4_vlift961 args') [L4VBVar961 0]) (l4_vlift961 e') =
     L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0)` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vapps_append962;l4_vapps962;l4_vlift961;l4_vliftN_vapps962] THEN
   REWRITE_TAC [GSYM l4_vlift961;ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (CONS dom' (l4_vl_ctx973 l))
       (l4_vapps962 (APPEND (MAP l4_vlift961 args') [L4VBVar961 0]) (l4_vlift961 e')) body'` ASSUME_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`dom':l4_vexpr961`;
                  `l4_vapps962 args' e'`;`l4_vapps962 args' e'`;`L4VForallE961 dom' body'`]
     l4_vis_defeq_weak966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vlift961;l4_vliftN961;ARITH_RULE `SUC 0 = 1`] THEN
   DISCH_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`CONS dom' (l4_vl_ctx973 l)`;
                  `l4_vliftN961 (l4_vapps962 args' e') 1 0`;`L4VBVar961 0`;
                  `l4_vliftN961 dom' 1 0`;`l4_vliftN961 body' 1 1`] l4_vhas_type_app972) THEN
   ASM_REWRITE_TAC [GSYM l4_vlift961;l4_vhas_type_bvar0_974;l4_vinst0961;
                    REWRITE_RULE [ARITH_RULE `SUC 0 = 1`] (SPECL [`body':l4_vexpr961`;`0`] l4_vinst_vliftN_bvar0966)];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') rest
       (L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0))` ASSUME_TAC THENL
  [SUBST1_TAC (SYM (ASSUME `l4_vapps962 (APPEND (MAP l4_vlift961 args') [L4VBVar961 0]) (l4_vlift961 e') = L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0)`)) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC
     [`chk:bool`;`rec:l4_kmethods543`;`l4_kpush_binding532 g a2 NONE`;
      `l4_klift447 e 1 0`;`body1:l4_kexpr447`;
      `APPEND (MAP (\a. l4_klift447 a 1 0) args) [L4KBVar447 0]`;`body':l4_vexpr961`] THEN
   REWRITE_TAC [l4_vl_ctx_push_lam973] THEN REPEAT CONJ_TAC THEN
   TRY (FIRST_ASSUM ACCEPT_TAC) THEN
   MATCH_MP_TAC l4_vtr_expr_lift_lam973 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
  DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961` o REWRITE_RULE [l4_vis_type961]) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') rest (L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0))` THEN
  DISCH_THEN (X_CHOOSE_THEN `r0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `tr:l4_vexpr961`)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THEN
  REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `L4VLam961 dom' r0` THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `L4VForallE961 dom' tr` THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN CONJ_TAC THENL
   [EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
    EXISTS_TAC `L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0)` THEN
    ASM_REWRITE_TAC []];
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
   EXISTS_TAC `L4VLam961 dom' (L4VApp961 (l4_vlift961 (l4_vapps962 args' e')) (L4VBVar961 0))` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom' tr` THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN EXISTS_TAC `u:l4_vlevel961` THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961];
    REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `L4VForallE961 dom' body'` THEN
    MATCH_MP_TAC l4_vis_defeq_eta961 THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]]]);;

let l4_core_eta_expand_atom_sound974 = prove
 (`!eta_fuel env venv ps chk rec g l e e' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_eta_expand_atom595 eta_fuel rec g e = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res e'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hexp")) THEN
  REMOVE_THEN "Hexp" MP_TAC THEN REWRITE_TAC [l4_core_eta_expand_atom595;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  l4_subst_cases_tac974 (SPEC `ty:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  TRY (DISCH_THEN (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [] THEN NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_type974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                              `e:l4_kexpr447`;`e':l4_vexpr961`;`ty0:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KPi447 a0 a1 a2 a3) ty'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `ty0:l4_kexpr447`;`ty':l4_vexpr961`;`L4KPi447 a0 a1 a2 a3`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`eta_fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `e:l4_kexpr447`;`L4KPi447 a0 a1 a2 a3`;`[]:l4_kexpr447 list`;
                 `e':l4_vexpr961`;`ty':l4_vexpr961`;`[]:l4_vexpr961 list`;`res:l4_kexpr447`]
    l4_core_eta_expand_pis_sound974) THEN
  ASM_REWRITE_TAC [ALL2;l4_vapps962]);;

let l4_core_eta_expand_sound974 = prove
 (`!e eta_fuel env venv ps chk rec g l e' res.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_core_eta_expand595 e eta_fuel rec g = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res e'`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [(* BVar *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* FVar *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* MVar *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* Sort *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* Const *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* App *) REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_eta_expand595] THEN MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* Lam *)
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "IHb")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595;l4_kr_bind_accept967;l4_conv_dis974] THEN
   DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
     (X_CHOOSE_THEN `b1:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)))) THEN
   SUBGOAL_THEN
     `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
      l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
      l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
     STRIP_ASSUME_TAC THENL
   [l4_ctx_wf_tac974; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1:l4_kbinder447`;
                  `a2:l4_kexpr447`;`a3:l4_kexpr447`;`e':l4_vexpr961`] l4_vtr_expr_inv_lam973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dom':l4_vexpr961` (X_CHOOSE_THEN `body':l4_vexpr961`
     (X_CHOOSE_THEN `ty_lam:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a2 dom' /\
                 l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') a3 body'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (l4_kpush_binding532 g a2 NONE) (l4_vl_push_lam973 l dom')`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vtr_ctx_push_lam973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps (l4_vl_push_lam973 l dom') b1 body'` MP_TAC THENL
   [REMOVE_THEN "IHb" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`eta_fuel:num`;`chk:bool`;`rec:l4_kmethods543`;`l4_kpush_binding532 g a2 NONE`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `r0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_TAC `tr:l4_vexpr961`)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961;l4_vl_ctx_push_lam973]) THEN
   UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) dom'` THEN
   DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961` o REWRITE_RULE [l4_vis_type961]) THEN
   REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `L4VLam961 dom' r0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `L4VForallE961 dom' tr` THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN CONJ_TAC THENL
    [EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vhas_type_lam972 THEN EXISTS_TAC `u:l4_vlevel961` THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
     EXISTS_TAC `body':l4_vexpr961` THEN ASM_REWRITE_TAC []];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `L4VLam961 dom' body'` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [l4_vis_defeq_u961] THEN
    EXISTS_TAC `L4VForallE961 dom' tr` THEN MATCH_MP_TAC l4_vis_defeq_lam961 THEN
    EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961]];
   (* Pi *) REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_eta_expand595] THEN MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* Let *) REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_eta_expand595] THEN MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* NatLit *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* StrLit *) REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_eta_expand595] THEN
   MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* Proj *) REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_eta_expand595] THEN MESON_TAC [l4_core_eta_expand_atom_sound974];
   (* MData *) REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_eta_expand595] THEN MESON_TAC [l4_core_eta_expand_atom_sound974]]);;

(* 6k. Head comparison (`l4_compare_heads595`) *)
let l4_compare_heads_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_compare_heads595 rec fuel env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hch")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hch" MP_TAC THEN REWRITE_TAC [l4_compare_heads595] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  (* Discharge t = L4KLam447 without splitting s *)
  TRY (DISCH_TAC THEN MATCH_MP_TAC l4_eta_compare_sound974 THEN
       MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                             `g:l4_kcontext532`;`a0:l4_name`;`a1:l4_kbinder447`;
                             `a2:l4_kexpr447`;`a3:l4_kexpr447`;`s:l4_kexpr447`] THEN
       ASM_REWRITE_TAC [] THEN NO_TAC) THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  (* Discharge all (non-Lam, L4KLam447) pairs uniformly *)
  TRY (DISCH_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC l4_eta_compare_sound974 THEN
       MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                             `g:l4_kcontext532`] THEN
       FIRST_ASSUM (fun hs ->
         let fs, argss = strip_comb (concl hs) in
         if is_const fs && fst (dest_const fs) = "l4_vtr_expr973" && last argss = `s':l4_vexpr961` then
           let lf, largs = strip_comb (el 4 argss) in
           if is_const lf && fst (dest_const lf) = "L4KLam447" then
             MAP_EVERY EXISTS_TAC largs THEN
             FIRST_ASSUM (fun ht ->
               let ft, argst = strip_comb (concl ht) in
               if is_const ft && fst (dest_const ft) = "l4_vtr_expr973" && last argst = `t':l4_vexpr961`
               then EXISTS_TAC (el 4 argst) THEN ASM_REWRITE_TAC []
               else NO_TAC)
           else NO_TAC
         else NO_TAC) THEN NO_TAC) THENL
  [(* BVar, BVar *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KBVar447 a'`] THEN ASM_REWRITE_TAC [];
   (* FVar, FVar *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KFVar447 a'`] THEN ASM_REWRITE_TAC [];
   (* Const, Const *)
   DISCH_TAC THEN MATCH_MP_TAC l4_core_same_head_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`fuel:num`;
                         `L4KConst447 a0 a1`;`L4KConst447 a0' a1'`] THEN
   ASM_REWRITE_TAC [];
   (* App, App *)
   REWRITE_TAC [LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
   ABBREV_TAC `tf = FST (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
   ABBREV_TAC `ta = SND (l4_ksplit_app489 (L4KApp447 a0 a1))` THEN
   ABBREV_TAC `sf = FST (l4_ksplit_app489 (L4KApp447 a0' a1'))` THEN
   ABBREV_TAC `sa = SND (l4_ksplit_app489 (L4KApp447 a0' a1'))` THEN
   SUBGOAL_THEN `l4_kapply_exprs489 ta tf = L4KApp447 a0 a1 /\
                 l4_kapply_exprs489 sa sf = L4KApp447 a0' a1'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tf";"ta";"sf";"sa"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973];
    ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 ta tf) t'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `tf':l4_vexpr961` (X_CHOOSE_THEN `ta':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 sa sf) s'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `sf':l4_vexpr961` (X_CHOOSE_THEN `sa':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) tf' sf'` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `tf:l4_kexpr447`;`tf':l4_vexpr961`;
                                      `sf:l4_kexpr447`;`sf':l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)) ta' sa'`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_core_compare_args_cheap_first_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                          `g:l4_kcontext532`;`ta:l4_kexpr447 list`;`sa:l4_kexpr447 list`] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?ty_t. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 ta' tf') ty_t`
     (X_CHOOSE_TAC `ty_t:l4_vexpr961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `t':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `ta':l4_vexpr961 list`;`sa':l4_vexpr961 list`;
                  `tf':l4_vexpr961`;`sf':l4_vexpr961`;`ty_t:l4_vexpr961`]
     l4_vapps_defeq_congr_l974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 ta' tf'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 sa' sf'` THEN
    ASM_REWRITE_TAC []];
   (* Proj, Proj *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0:l4_name`;`a1':num`;`a2:l4_kexpr447`;`t':l4_vexpr961`]
     l4_vtr_expr_inv_proj974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a2_v:l4_vexpr961` (X_CHOOSE_THEN `pv1:l4_vexpr961`
     (X_CHOOSE_THEN `fty1:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a0':l4_name`;`a1':num`;`a2':l4_kexpr447`;`s':l4_vexpr961`]
     l4_vtr_expr_inv_proj974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a2'_v:l4_vexpr961` (X_CHOOSE_THEN `pv2:l4_vexpr961`
     (X_CHOOSE_THEN `fty2:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;
                  `l4_vl_ctx973 l`;`a0:l4_name`;`a0':l4_name`;`a1':num`;
                  `a2_v:l4_vexpr961`;`a2'_v:l4_vexpr961`;`pv1:l4_vexpr961`;`pv2:l4_vexpr961`;
                  `fty1:l4_vexpr961`;`fty2:l4_vexpr961`] l4_vtr_proj_congr973) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                      `a2:l4_kexpr447`;`a2_v:l4_vexpr961`;
                                      `a2':l4_kexpr447`;`a2'_v:l4_vexpr961`]) THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv2:l4_vexpr961` THEN
     ASM_REWRITE_TAC []]]]);;

(* 6l. Structure eta & unit-like eta *)
let l4_core_compare_fields_sound974 = prove
 (`!fields env venv ps chk rec g l owner us' params' val_e v' fields' start.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l val_e v' /\
   (!i. start <= i /\ i < start + LENGTH fields ==>
        ?fty. l4_vtr_proj973 env venv (LENGTH ps) (l4_vl_ctx973 l) owner i v'
                (l4_vproj_expr962 owner i us' params' v') fty) /\
   ALL2 (l4_vtr_expr973 env venv ps l) fields fields' /\
   l4_core_compare_fields595 fields rec g owner val_e start = L4KAccept491 T ==>
   ALL2 (l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l))
     (MAP (\i. l4_vproj_expr962 owner i us' params' v') (l4_seq973 start (LENGTH fields)))
     fields'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `fields':l4_vexpr961 list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `f':l4_vexpr961` (X_CHOOSE_THEN `rest':l4_vexpr961 list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC [l4_core_compare_fields595;ALL2;LENGTH;l4_seq973;MAP;l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `?fty. l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner start v'
              (l4_vproj_expr962 owner start us' params' v') fty`
     (X_CHOOSE_TAC `fty:l4_vexpr961`) THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `l4_vtr_expr973 env venv ps l (L4KProj447 owner start val_e)
        (l4_vproj_expr962 owner start us' params' v')` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vtr_expr973 env venv ps l val_e v'` THEN
    DISCH_THEN (X_CHOOSE_THEN `v0:l4_vexpr961` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `tv:l4_vexpr961` ASSUME_TAC)) o REWRITE_RULE [l4_vtr_expr973;l4_vis_defeq_u961]) THEN
    UNDISCH_TAC `l4_vtr_proj973 env venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) owner start v' (l4_vproj_expr962 owner start us' params' v') fty` THEN
    REWRITE_TAC [l4_vtr_proj973] THEN
    DISCH_THEN (X_CHOOSE_THEN `info0:l4_kinductive_data493` (X_CHOOSE_THEN `ctor0:l4_name`
      (X_CHOOSE_THEN `c0:l4_kconstructor_data493` (X_CHOOSE_THEN `d0:l4_kdeclaration493`
        (X_CHOOSE_THEN `us0:l4_vlevel961 list` (X_CHOOSE_THEN `ps0:l4_vexpr961 list`
          (X_CHOOSE_THEN `idxs0:l4_vexpr961 list` STRIP_ASSUME_TAC))))))) THEN
    SUBGOAL_THEN
      `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (L4VApp961 (l4_vapps962 ps0 (L4VConst961 (l4_proj_const_name962 owner start) us0)) v') fty`
      ASSUME_TAC THENL
    [REWRITE_TAC [GSYM l4_vproj_expr962] THEN
     SUBST1_TAC (SYM (ASSUME `l4_vproj_expr962 owner start us' params' v' = l4_vproj_expr962 owner start us0 ps0 v'`)) THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                   `l4_vapps962 ps0 (L4VConst961 (l4_proj_const_name962 owner start) us0)`;
                   `v':l4_vexpr961`;`fty:l4_vexpr961`] l4_vhas_type_app_inv970) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `ap:l4_vexpr961` (X_CHOOSE_THEN `bp:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?up. l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ap tv (L4VSort961 up)`
      (X_CHOOSE_TAC `up:l4_vlevel961`) THENL
    [MATCH_MP_TAC l4_vis_defeq_uniq_same972 THEN
     MAP_EVERY EXISTS_TAC [`v':l4_vexpr961`;`v':l4_vexpr961`;`v':l4_vexpr961`] THEN
     ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `v0:l4_vexpr961` THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l4_vis_defeq961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)
         (l4_vproj_expr962 owner start us0 ps0 v0)
         (l4_vproj_expr962 owner start us0 ps0 v') (l4_vinst0961 bp v0)` ASSUME_TAC THENL
    [REWRITE_TAC [l4_vproj_expr962] THEN MATCH_MP_TAC l4_vis_defeq_app961 THEN
     EXISTS_TAC `ap:l4_vexpr961` THEN ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
     MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`tv:l4_vexpr961`;`up:l4_vlevel961`] THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN
    EXISTS_TAC `l4_vproj_expr962 owner start us0 ps0 v0` THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
     MAP_EVERY EXISTS_TAC [`v0:l4_vexpr961`;`l4_vinst0961 bp v0`] THEN
     ASM_REWRITE_TAC [l4_vtr_proj973] THEN
     MAP_EVERY EXISTS_TAC
       [`info0:l4_kinductive_data493`;`ctor0:l4_name`;`c0:l4_kconstructor_data493`;
        `d0:l4_kdeclaration493`;`us0:l4_vlevel961 list`;
        `ps0:l4_vexpr961 list`;`idxs0:l4_vexpr961 list`] THEN
     REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THENL
     [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `v':l4_vexpr961` THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
      REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `tv:l4_vexpr961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vis_defeq_refl_l961 THEN
      EXISTS_TAC `l4_vproj_expr962 owner start us0 ps0 v'` THEN ASM_REWRITE_TAC []];
     EXISTS_TAC `l4_vinst0961 bp v0` THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
      `L4KProj447 owner start val_e`;`l4_vproj_expr962 owner start us' params' v'`;
      `h:l4_kexpr447`;`f':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`val_e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_core_structure_eta_sound974 = prove
 (`!env venv ps chk rec g l val_e constructed v' c'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l val_e v' /\
   l4_vtr_expr973 env venv ps l constructed c' /\
   l4_core_structure_eta595 rec env g val_e constructed = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) v' c'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hse")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hse" MP_TAC THEN REWRITE_TAC [l4_core_structure_eta595;LET_DEF;LET_END_DEF] THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 constructed)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 constructed)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 args head = constructed` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  MP_TAC (ISPEC `l4_core_constructor532 env a0` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `c:l4_kconstructor_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  FIRST_X_ASSUM (CONJUNCTS_THEN2 (LABEL_TAC "Hstruct") (LABEL_TAC "Hlen_args")) THEN
  DISCH_THEN (X_CHOOSE_THEN `vt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ct:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun h ->
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`val_e:l4_kexpr447`;`v':l4_vexpr961`;`vt:l4_kexpr447`] h) THEN
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`constructed:l4_kexpr447`;`c':l4_vexpr961`;`ct:l4_kexpr447`] h)) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ct':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `vt':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) vt' ct'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `vt:l4_kexpr447`;`vt':l4_vexpr961`;
                                     `ct:l4_kexpr447`;`ct':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) c'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961` (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN `LENGTH (args':l4_vexpr961 list) = l4_kctor_num_params493 c + l4_kctor_num_fields493 c`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `LENGTH (args:l4_kexpr447 list) = LENGTH (args':l4_vexpr961 list)`
     (fun th -> ASM_REWRITE_TAC [GSYM th]) THEN
   MATCH_MP_TAC l4_all2_length974 THEN EXISTS_TAC `l4_vtr_expr_s973 env venv ps l` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 args' (L4VConst961 a0 us')) ct'`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `c':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ctor_type_head973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;`c:l4_kconstructor_data493`;
     `us':l4_vlevel961 list`;`args':l4_vexpr961 list`;`ct':l4_vexpr961`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `info:l4_kinductive_data493` (X_CHOOSE_THEN `idxs:l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_kind_num_indices493 info = 0 /\ LENGTH (l4_kind_ctors493 info) = 1` STRIP_ASSUME_TAC THENL
  [USE_THEN "Hstruct" (MP_TAC o REWRITE_RULE [l4_core_structure532]) THEN ASM_REWRITE_TAC [l4_conv_dis974] THEN SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `idxs:l4_vexpr961 list = []` SUBST_ALL_TAC THENL
  [REWRITE_TAC [GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [APPEND_NIL]) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`l4_kctor_induct493 c`;`info:l4_kinductive_data493`]
    l4_core_inductive_inv974) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `d_ind:l4_kdeclaration493` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`a0:l4_name`;`c:l4_kconstructor_data493`]
    l4_core_constructor_inv974) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `d_ctor:l4_kdeclaration493` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_kind_ctors493 info = [a0]` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_shape973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`l4_kctor_induct493 c`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
                               `a0:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
   UNDISCH_TAC `LENGTH (l4_kind_ctors493 info) = 1` THEN UNDISCH_TAC `MEM (a0:l4_name) (l4_kind_ctors493 info)` THEN
   MP_TAC (ISPEC `l4_kind_ctors493 info` list_CASES) THEN
   DISCH_THEN (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC [th;MEM])
     (X_CHOOSE_THEN `c1:l4_name` (X_CHOOSE_THEN `cs:l4_name list` (fun th -> REWRITE_TAC [th;MEM;LENGTH])))) THEN
   MP_TAC (ISPEC `cs:l4_name list` list_CASES) THEN
   DISCH_THEN (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC [th;MEM;LENGTH] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [])
     (X_CHOOSE_THEN `c2:l4_name` (X_CHOOSE_THEN `cs2:l4_name list` (fun th -> REWRITE_TAC [th;LENGTH] THEN ARITH_TAC))));
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d_ctor)` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPECL [`a0:l4_name`;`d_ctor:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [l4_conv_dis974] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci2:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `ci:l4_vconstant961 = ci2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`a0:l4_name`] THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (l4_kdecl_params493 d_ctor)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) v'
       (l4_vapps962 (l4_kfirstn494 args' (l4_kctor_num_params493 c)) (L4VConst961 (l4_kctor_induct493 c) us'))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `vt':l4_vexpr961` THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `ct':l4_vexpr961` THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 c)) = l4_kind_num_params493 info`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `l4_kctor_num_params493 c <= LENGTH (args':l4_vexpr961 list)` (fun th ->
     MP_TAC (MATCH_MP l4_length_firstn973 th) THEN ASM_ARITH_TAC) THEN
   ASM_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_struct_eta973) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL
    [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`l4_kctor_induct493 c`;`info:l4_kinductive_data493`;
     `a0:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`;`us':l4_vlevel961 list`;
     `l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 c)`;`v':l4_vexpr961`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hprojs") (LABEL_TAC "Heta")) THEN
  SUBGOAL_THEN
    `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l))
       (MAP (\i. l4_vproj_expr962 (l4_kctor_induct493 c) i us'
                   (l4_kfirstn494 args' (l4_kctor_num_params493 c)) v')
         (l4_seq973 0 (l4_kctor_num_fields493 c)))
       (l4_skip550 args' (l4_kctor_num_params493 c))` ASSUME_TAC THENL
  [MP_TAC (SPECL
     [`l4_skip550 (args:l4_kexpr447 list) (l4_kctor_num_params493 c)`;
      `env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;`chk:bool`;`rec:l4_kmethods543`;
      `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`l4_kctor_induct493 c`;`us':l4_vlevel961 list`;
      `l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 c)`;`val_e:l4_kexpr447`;`v':l4_vexpr961`;
      `l4_skip550 (args':l4_vexpr961 list) (l4_kctor_num_params493 c)`;`0`]
     l4_core_compare_fields_sound974) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
    [REWRITE_TAC [l4_length_skip973] THEN GEN_TAC THEN STRIP_TAC THEN
     USE_THEN "Hprojs" MATCH_MP_TAC THEN ASM_ARITH_TAC;
     MATCH_MP_TAC l4_all2_skip973 THEN MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `LENGTH (l4_skip550 (args:l4_kexpr447 list) (l4_kctor_num_params493 c)) = l4_kctor_num_fields493 c`
      (fun th -> REWRITE_TAC [th]) THEN
    REWRITE_TAC [l4_length_skip973] THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l))
       (l4_kfirstn494 args' (l4_kctor_num_params493 c))
       (l4_kfirstn494 args' (l4_kctor_num_params493 c))` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_all2_firstn973 THEN MATCH_MP_TAC l4_all2_vtr_s_refl_u974 THEN
   MAP_EVERY EXISTS_TAC [`args:l4_kexpr447 list`;`env:l4_kdeclaration493 list`] THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l))
       (APPEND (l4_kfirstn494 args' (l4_kctor_num_params493 c))
         (MAP (\i. l4_vproj_expr962 (l4_kctor_induct493 c) i us'
                     (l4_kfirstn494 args' (l4_kctor_num_params493 c)) v')
           (l4_seq973 0 (l4_kctor_num_fields493 c))))
       args'` ASSUME_TAC THENL
  [GEN_REWRITE_TAC RAND_CONV [SYM (ISPECL [`args':l4_vexpr961 list`;`l4_kctor_num_params493 c`] l4_firstn_append_skip973)] THEN
   MATCH_MP_TAC l4_all2_append974 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (L4VConst961 a0 us') (L4VConst961 a0 us')`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN
   REWRITE_TAC [GSYM l4_vhas_type961] THEN MATCH_MP_TAC l4_vhas_type_const972 THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC (SPECL
    [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
     `APPEND (l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 c))
        (MAP (\i. l4_vproj_expr962 (l4_kctor_induct493 c) i us'
                    (l4_kfirstn494 args' (l4_kctor_num_params493 c)) v')
          (l4_seq973 0 (l4_kctor_num_fields493 c)))`;
     `args':l4_vexpr961 list`;`L4VConst961 a0 us'`;`L4VConst961 a0 us'`;
     `l4_vapps962 (l4_kfirstn494 args' (l4_kctor_num_params493 c)) (L4VConst961 (l4_kctor_induct493 c) us')`]
    l4_vapps_defeq_congr_l974) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
   MATCH_MP_TAC l4_vis_defeq_refl_r961 THEN EXISTS_TAC `v':l4_vexpr961` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Hcongr")) THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN
  EXISTS_TAC
    `l4_vapps962
       (APPEND (l4_kfirstn494 (args':l4_vexpr961 list) (l4_kctor_num_params493 c))
         (MAP (\i. l4_vproj_expr962 (l4_kctor_induct493 c) i us'
                     (l4_kfirstn494 args' (l4_kctor_num_params493 c)) v')
           (l4_seq973 0 (l4_kctor_num_fields493 c))))
       (L4VConst961 a0 us')` THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN
   EXISTS_TAC `l4_vapps962 (l4_kfirstn494 args' (l4_kctor_num_params493 c)) (L4VConst961 (l4_kctor_induct493 c) us')` THEN
   FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let l4_core_unit_like_sound974 = prove
 (`!env venv ps chk rec g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_unit_like595 rec env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hul")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hul" MP_TAC THEN REWRITE_TAC [l4_core_unit_like595;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty0:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  ABBREV_TAC `head = FST (l4_ksplit_app489 ty)` THEN
  ABBREV_TAC `args = SND (l4_ksplit_app489 ty)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 args head = ty` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["head";"args"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `head:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  FIRST_X_ASSUM (LABEL_TAC "Hstruct") THEN
  MP_TAC (ISPEC `l4_core_inductive532 env a0` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `info:l4_kinductive_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
  MP_TAC (ISPEC `l4_kind_ctors493 info` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `ctor:l4_name` (X_CHOOSE_THEN `cs:l4_name list`
      (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974])))) THEN
  MP_TAC (ISPEC `cs:l4_name list` list_CASES) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> SUBST_ALL_TAC th THEN REWRITE_TAC [l4_conv_dis974])
    (X_CHOOSE_THEN `c2:l4_name` (X_CHOOSE_THEN `cs2:l4_name list`
      (fun th -> REWRITE_TAC [th;l4_conv_dis974])))) THEN
  MP_TAC (ISPEC `l4_core_constructor532 env ctor` (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC [th;l4_conv_dis974])
    (X_CHOOSE_THEN `c:l4_kconstructor_data493` (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_conv_dis974]))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `sty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `chk:bool`;`rec:l4_kmethods543`] l4_fms_infer_typed974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun h ->
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`t':l4_vexpr961`;`ty0:l4_kexpr447`] h) THEN
    MP_TAC (SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`s:l4_kexpr447`;`s':l4_vexpr961`;`sty:l4_kexpr447`] h)) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `sty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l ty ty'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `ty0:l4_kexpr447`;`ty':l4_vexpr961`;`ty:l4_kexpr447`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) ty' sty'` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `ty:l4_kexpr447`;`ty':l4_vexpr961`;
                                     `sty:l4_kexpr447`;`sty':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 args (L4KConst447 a0 a1)) ty'`
    (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
  [ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `h':l4_vexpr961` (X_CHOOSE_THEN `args':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr_s973 env venv ps l (L4KConst447 a0 a1) h'` THEN
  l4_inv_vtr_s_goal974 THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) t' (l4_vapps962 args' (L4VConst961 a0 us'))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) s' (l4_vapps962 args' (L4VConst961 a0 us'))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `sty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `ty':l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_kind_num_indices493 info = 0` ASSUME_TAC THENL
  [USE_THEN "Hstruct" (MP_TAC o REWRITE_RULE [l4_core_structure532]) THEN ASM_REWRITE_TAC [l4_conv_dis974] THEN SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `?usort. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 args' (L4VConst961 a0 us')) (L4VSort961 usort)`
    (X_CHOOSE_TAC `usort:l4_vlevel961`) THENL
  [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `t':l4_vexpr961`;`t':l4_vexpr961`;`l4_vapps962 args' (L4VConst961 a0 us')`]
     l4_vis_defeq_is_type974) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vis_type961];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (args':l4_vexpr961 list) = l4_kind_num_params493 info` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_type_arity973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;
                               `info:l4_kinductive_data493`;`us':l4_vlevel961 list`;
                               `args':l4_vexpr961 list`;`usort:l4_vlevel961`]) THEN
   ASM_REWRITE_TAC [ADD_0];
   ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`a0:l4_name`;`info:l4_kinductive_data493`]
    l4_core_inductive_inv974) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `d_ind:l4_kdeclaration493` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`ctor:l4_name`;`c:l4_kconstructor_data493`]
    l4_core_constructor_inv974) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `d_ctor:l4_kdeclaration493` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `l4_kctor_num_params493 c = l4_kind_num_params493 info /\
     LENGTH (l4_kdecl_params493 d_ctor) = LENGTH (l4_kdecl_params493 d_ind)` STRIP_ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_ind_shape973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`a0:l4_name`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
                               `ctor:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d_ind)` ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPECL [`a0:l4_name`;`d_ind:l4_kdeclaration493`]) THEN
   ASM_REWRITE_TAC [l4_conv_dis974] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci2:l4_vconstant961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `ci:l4_vconstant961 = ci2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC l4_venv_wf_lookup_unique966 THEN
    MAP_EVERY EXISTS_TAC [`venv:l4_venv961`;`a0:l4_name`] THEN ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (us':l4_vlevel961 list) = LENGTH (l4_kdecl_params493 d_ctor)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_struct_eta973) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun h ->
    MP_TAC (SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;`info:l4_kinductive_data493`;
                   `ctor:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`;`us':l4_vlevel961 list`;
                   `args':l4_vexpr961 list`;`t':l4_vexpr961`] h) THEN
    MP_TAC (SPECL [`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;`a0:l4_name`;`info:l4_kinductive_data493`;
                   `ctor:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`;`us':l4_vlevel961 list`;
                   `args':l4_vexpr961 list`;`s':l4_vexpr961`] h)) THEN
  ASM_REWRITE_TAC [l4_seq973;MAP;APPEND_NIL] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Heta_s")) THEN
  DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Heta_t")) THEN
  REWRITE_TAC [l4_vis_defeq_u961] THEN
  EXISTS_TAC `l4_vapps962 args' (L4VConst961 a0 us')` THEN
  MATCH_MP_TAC l4_vis_defeq_trans961 THEN EXISTS_TAC `l4_vapps962 args' (L4VConst961 ctor us')` THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []);;

(* 6m. String literal expansion (`l4_core_try_string_expansion596`) *)
let l4_core_try_string_expansion_sound974 = prove
 (`!env venv ps chk rec g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_try_string_expansion596 rec g t s = L4KAccept491 (SOME T) ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hst")) THEN
  SUBGOAL_THEN `l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l` ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hst" MP_TAC THEN REWRITE_TAC [l4_core_try_string_expansion596;LET_DEF;LET_END_DEF] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [(* App, StrLit *)
   l4_subst_cases_tac974 (SPEC `a0:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   l4_subst_cases_tac974 (ISPEC `a1':l4_klevel447 list` list_CASES) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a:num list`;`s':l4_vexpr961`] l4_vtr_expr_inv_strlit974) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `sv:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l exp s'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `sv:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_core_expand_string974 THEN EXISTS_TAC `a:num list` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`exp:l4_kexpr447`;`s':l4_vexpr961`;
      `L4KApp447 (L4KConst447 a0' []) a1`;`t':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   (* StrLit, App *)
   l4_subst_cases_tac974 (SPEC `a0:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   l4_subst_cases_tac974 (ISPEC `a1':l4_klevel447 list` list_CASES) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `exp:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   REWRITE_TAC [l4_conv_dis974] THEN l4_subst_true_tac974 THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l:l4_vl_ctx_rec973`;`a:num list`;`t':l4_vexpr961`] l4_vtr_expr_inv_strlit974) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `sv:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l exp t'` ASSUME_TAC THENL
   [REWRITE_TAC [l4_vtr_expr973] THEN EXISTS_TAC `sv:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC l4_vtr_expr_s_core_expand_string974 THEN EXISTS_TAC `a:num list` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`exp:l4_kexpr447`;`t':l4_vexpr961`;
      `L4KApp447 (L4KConst447 a0' []) a1`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC []]);;

(* 6n. Fallback, post-WHNF comparison, finish conversion, and `l4_defeq_step597` *)
let l4_core_compare_fallback_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_compare_fallback596 rec fuel env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hfb")) THEN
  REMOVE_THEN "Hfb" MP_TAC THEN REWRITE_TAC [l4_core_compare_fallback596;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [TRY DISCH_TAC THEN MATCH_MP_TAC l4_compare_heads_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `ok2:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [TRY DISCH_TAC THEN MATCH_MP_TAC l4_core_structure_eta_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `ok3:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [TRY DISCH_TAC THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
   MATCH_MP_TAC l4_core_structure_eta_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`s:l4_kexpr447`;`t:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `exp:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `exp:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [DISCH_TAC THEN MATCH_MP_TAC l4_core_unit_like_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   l4_subst_true_tac974 THEN MATCH_MP_TAC l4_core_try_string_expansion_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []]);;

let l4_compare_after_whnf_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_compare_after_whnf596 rec fuel env g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hc")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hc" MP_TAC THEN REWRITE_TAC [l4_compare_after_whnf596] THEN
  COND_CASES_TAC THENL
  [TRY DISCH_TAC THEN MATCH_MP_TAC l4_vtr_expr_core_alpha_eq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(l4_kr_bind491 (l4_infer_method543 rec g t) (\ty.
        l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
          l4_kr_bind491 (l4_klevel_equiv555 fuel sort L4KZero447) (\is_prop.
            if is_prop then
              l4_kr_bind491 (l4_infer_method543 rec g s) (\sty. l4_defeq_method543 rec g ty sty)
            else l4_core_compare_fallback596 rec fuel env g t s))) = L4KAccept491 T) ==>
     l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) t' s'`
    (LABEL_TAC "Hpi_fb") THENL
  [REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `su:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `is_p:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [l4_kr_bind_accept967] THEN
    DISCH_THEN (X_CHOOSE_THEN `sty:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MATCH_MP_TAC l4_core_proof_irrel_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [l4_core_proof_irrel596;l4_kr_bind491];
    DISCH_TAC THEN MATCH_MP_TAC l4_core_compare_fallback_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `t:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  TRY (USE_THEN "Hpi_fb" (fun h -> DISCH_THEN (ACCEPT_TAC o MATCH_MP h)) THEN NO_TAC) THEN
  l4_subst_cases_tac974 (SPEC `s:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN
  TRY (USE_THEN "Hpi_fb" (fun h -> DISCH_THEN (ACCEPT_TAC o MATCH_MP h)) THEN NO_TAC) THENL
  [(* Sort, Sort *)
   DISCH_TAC THEN MATCH_MP_TAC l4_core_quick_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`L4KSort447 a`;`L4KSort447 a'`] THEN
   ASM_REWRITE_TAC [l4_core_quick596;l4_conv_dis974;l4_kr_bind491];
   (* Lam, Lam *)
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_quick_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;
                         `L4KLam447 a0 a1 a2 a3`;`L4KLam447 a0' a1' a2' a3'`] THEN
   ASM_REWRITE_TAC [l4_core_quick596;l4_conv_dis974;l4_kr_bind491];
   (* Pi, Pi *)
   REWRITE_TAC [l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THEN
   MATCH_MP_TAC l4_core_quick_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;
                         `L4KPi447 a0 a1 a2 a3`;`L4KPi447 a0' a1' a2' a3'`] THEN
   ASM_REWRITE_TAC [l4_core_quick596;l4_conv_dis974;l4_kr_bind491];
   (* NatLit, NatLit *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KNatLit447 a'`] THEN ASM_REWRITE_TAC [];
   (* StrLit, StrLit *)
   DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`L4KStrLit447 a'`] THEN ASM_REWRITE_TAC []]);;

let l4_core_finish_conversion_sound974 = prove
 (`!env venv ps chk rec fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps chk rec /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_core_finish_conversion597 rec fuel env ps g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hfc")) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  REMOVE_THEN "Hfc" MP_TAC THEN REWRITE_TAC [l4_core_finish_conversion597] THEN
  ABBREV_TAC
    `project = \e.
       let view = l4_ksplit_app489 e in
       match FST view with
       | L4KProj447 owner idx value ->
         l4_kr_bind491 (l4_core_reduce_projection550 rec env g owner idx value)
           (\field. L4KAccept491
             (match field with
              | NONE -> NONE
              | SOME f -> SOME (l4_kapply_exprs489 (SND view) f)))
       | _ -> L4KAccept491 NONE` THEN
  REWRITE_TAC [LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  ABBREV_TAC `th = FST (l4_ksplit_app489 t)` THEN
  ABBREV_TAC `ta = SND (l4_ksplit_app489 t)` THEN
  ABBREV_TAC `sh = FST (l4_ksplit_app489 s)` THEN
  ABBREV_TAC `sa = SND (l4_ksplit_app489 s)` THEN
  SUBGOAL_THEN `l4_kapply_exprs489 ta th = t /\ l4_kapply_exprs489 sa sh = s` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["th";"ta";"sh";"sa"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `lpok:bool` (CONJUNCTS_THEN2 (LABEL_TAC "Hlp") MP_TAC)) THEN
  COND_CASES_TAC THENL
  [(* Lazy delta projection succeeded *)
   POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN
   DISCH_THEN (K ALL_TAC) THEN REMOVE_THEN "Hlp" MP_TAC THEN
   l4_subst_cases_tac974 (SPEC `th:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   l4_subst_cases_tac974 (SPEC `sh:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "Hlen")) THEN
   DISCH_THEN (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
   POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 ta (L4KProj447 a0 a1' a2)) t'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `th':l4_vexpr961` (X_CHOOSE_THEN `ta':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 sa (L4KProj447 a0' a1' a2')) s'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `sh':l4_vexpr961` (X_CHOOSE_THEN `sa':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KProj447 a0 a1' a2) th'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_proj974) THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `te':l4_vexpr961` (X_CHOOSE_THEN `pv1:l4_vexpr961`
     (X_CHOOSE_THEN `fty1:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (L4KProj447 a0' a1' a2') sh'`
     (MP_TAC o MATCH_MP l4_vtr_expr_inv_proj974) THENL
   [MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `se':l4_vexpr961` (X_CHOOSE_THEN `pv2:l4_vexpr961`
     (X_CHOOSE_THEN `fty2:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) pv1 pv2` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_core_lazy_delta_proj_sound974 THEN
    MAP_EVERY EXISTS_TAC
      [`SUC fuel`;`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;`fuel:num`;
       `g:l4_kcontext532`;`a0:l4_name`;`a0':l4_name`;`a1':num`;`te':l4_vexpr961`;`se':l4_vexpr961`;
       `fty1:l4_vexpr961`;`fty2:l4_vexpr961`;`a2:l4_kexpr447`;`a2':l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) th' sh'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `pv2:l4_vexpr961` THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `ALL2 (l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)) ta' sa'`
     ASSUME_TAC THENL
   [MP_TAC (ISPEC `ta:l4_kexpr447 list` list_CASES) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `a0_t:l4_kexpr447` (X_CHOOSE_THEN `ta_r:l4_kexpr447 list` SUBST_ALL_TAC))) THENL
    [SUBGOAL_THEN `sa:l4_kexpr447 list = []` SUBST_ALL_TAC THENL
     [REWRITE_TAC [GSYM LENGTH_EQ_NIL] THEN USE_THEN "Hlen" MP_TAC THEN REWRITE_TAC [LENGTH] THEN ARITH_TAC;
      UNDISCH_TAC `ALL2 (l4_vtr_expr_s973 env venv ps l) [] ta'` THEN
      UNDISCH_TAC `ALL2 (l4_vtr_expr_s973 env venv ps l) [] sa'` THEN
      l4_subst_cases_tac974 (ISPEC `ta':l4_vexpr961 list` list_CASES) THEN
      l4_subst_cases_tac974 (ISPEC `sa':l4_vexpr961 list` list_CASES) THEN
      REWRITE_TAC [ALL2]];
     RULE_ASSUM_TAC (REWRITE_RULE [l4_conv_dis974]) THEN
     MATCH_MP_TAC l4_core_compare_args_cheap_first_sound974 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                           `g:l4_kcontext532`;`CONS (a0_t:l4_kexpr447) ta_r`;`sa:l4_kexpr447 list`] THEN
     ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
     MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   SUBGOAL_THEN `?ty_t. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 ta' th') ty_t`
     (X_CHOOSE_TAC `ty_t:l4_vexpr961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `t':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`l4_vl_ctx973 l`;
                  `ta':l4_vexpr961 list`;`sa':l4_vexpr961 list`;
                  `th':l4_vexpr961`;`sh':l4_vexpr961`;`ty_t:l4_vexpr961`]
     l4_vapps_defeq_congr_l974) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 ta' th'` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `l4_vapps962 sa' sh'` THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  (* Full projection reduction or compare_after_whnf *)
  SUBGOAL_THEN
    `!e e' e1. l4_vtr_expr973 env venv ps l e e' /\ project e = L4KAccept491 (SOME e1) ==>
               l4_vtr_expr973 env venv ps l e1 e'` (LABEL_TAC "Hproj_s") THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "project" THEN
   REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ABBREV_TAC `eh = FST (l4_ksplit_app489 e)` THEN
   ABBREV_TAC `ea = SND (l4_ksplit_app489 e)` THEN
   SUBGOAL_THEN `l4_kapply_exprs489 ea eh = e` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eh";"ea"] THEN REWRITE_TAC [l4_ksplit_app_reconstruct973]; ALL_TAC] THEN
   l4_subst_cases_tac974 (SPEC `eh:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `fld:(l4_kexpr447)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   l4_subst_cases_tac974 (ISPEC `fld:(l4_kexpr447)option` (cases "option")) THEN
   REWRITE_TAC [l4_conv_dis974] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l (l4_kapply_exprs489 ea (L4KProj447 a0 a1 a2)) e'`
     (MP_TAC o MATCH_MP l4_vtr_expr_kapply_inv973) THENL
   [ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `eh':l4_vexpr961` (X_CHOOSE_THEN `ea':l4_vexpr961 list` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv ps l a eh'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_core_reduce_projection_with_sound974 THEN
    MAP_EVERY EXISTS_TAC [`chk:bool`;`rec:l4_kmethods543`;`l4_whnf_method543 rec`;
                          `g:l4_kcontext532`;`a0:l4_name`;`a1:num`;`a2:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [GSYM l4_core_reduce_projection550] THEN CONJ_TAC THENL
    [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                    `chk:bool`;`rec:l4_kmethods543`] l4_fms_whnf974) THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_defeq_r973 THEN EXISTS_TAC `l4_vapps962 ea' eh'` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `?ty_e. l4_vhas_type961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) (l4_vapps962 ea' eh') ty_e`
     (X_CHOOSE_TAC `ty_e:l4_vexpr961`) THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_l973 THEN EXISTS_TAC `e':l4_vexpr961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC l4_vtr_expr_kapply973 THEN EXISTS_TAC `ty_e:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_all2_vtr_s_to_vtr974 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `tp:(l4_kexpr447)option` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `sp:(l4_kexpr447)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  l4_subst_cases_tac974 (ISPEC `tp:(l4_kexpr447)option` (cases "option")) THEN
  l4_subst_cases_tac974 (ISPEC `sp:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THEN DISCH_TAC THENL
  [(* NONE, NONE *)
   MATCH_MP_TAC l4_compare_after_whnf_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`chk:bool`;`rec:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   (* NONE, SOME a *)
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `t:l4_kexpr447`;`t':l4_vexpr961`;
                                     `a:l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN REMOVE_THEN "Hproj_s" MATCH_MP_TAC THEN
   EXISTS_TAC `s:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   (* SOME a, NONE *)
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`t':l4_vexpr961`;
                                     `s:l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN REMOVE_THEN "Hproj_s" MATCH_MP_TAC THEN
   EXISTS_TAC `t:l4_kexpr447` THEN ASM_REWRITE_TAC [];
   (* SOME a, SOME a' *)
   MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `chk:bool`;`rec:l4_kmethods543`] l4_fms_defeq974) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                     `a:l4_kexpr447`;`t':l4_vexpr961`;
                                     `a':l4_kexpr447`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
   [USE_THEN "Hproj_s" MATCH_MP_TAC THEN EXISTS_TAC `t:l4_kexpr447` THEN ASM_REWRITE_TAC [];
    USE_THEN "Hproj_s" MATCH_MP_TAC THEN EXISTS_TAC `s:l4_kexpr447` THEN ASM_REWRITE_TAC []]]);;

let l4_defeq_step_sound974 = prove
 (`!env venv ps methods fuel g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_full_methods_sound974 env venv ps T methods /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_defeq_step597 methods fuel env ps g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) (LABEL_TAC "Hd")) THEN
  SUBGOAL_THEN `l4_full_methods_sound974 env venv ps F (l4_inference_only543 methods)` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_full_methods_sound_inference_only974 THEN EXISTS_TAC `T` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REMOVE_THEN "Hd" MP_TAC THEN REWRITE_TAC [l4_defeq_step597;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  ABBREV_TAC `rec0 = l4_inference_only543 methods` THEN
  (* 1. core_quick *)
  DISCH_THEN (X_CHOOSE_THEN `quick:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `quick:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [ALL_TAC;
   l4_subst_true_tac974 THEN MATCH_MP_TAC l4_core_quick_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`F`;`rec0:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 2. core_true_shortcut *)
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `sc:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974;l4_kr_bind_accept967] THENL
  [TRY DISCH_TAC THEN MATCH_MP_TAC l4_core_true_shortcut_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`F`;`rec0:l4_kmethods543`;
                         `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  (* 3. core_proof_irrel *)
  DISCH_THEN (X_CHOOSE_THEN `irrel:(bool)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (ISPEC `irrel:(bool)option` (cases "option")) THEN
  REWRITE_TAC [l4_conv_dis974] THENL
  [ALL_TAC;
   l4_subst_true_tac974 THEN MATCH_MP_TAC l4_core_proof_irrel_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`F`;`rec0:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []] THEN
  (* 4. whnf_core + lazy_delta + finish_conversion *)
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `tn:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `sn:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `prog:l4_conversion_progress597` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l tn t' /\ l4_vtr_expr973 env venv ps l sn s'`
    STRIP_ASSUME_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `F`;`rec0:l4_kmethods543`] l4_fms_whnf_core974) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                       `t:l4_kexpr447`;`t':l4_vexpr961`;`tn:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [];
    FIRST_ASSUM (MATCH_MP_TAC o SPECL [`T`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                       `s:l4_kexpr447`;`s':l4_vexpr961`;`sn:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MP_TAC (SPECL [`SUC fuel`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `F`;`rec0:l4_kmethods543`;`fuel:num`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `tn:l4_kexpr447`;`sn:l4_kexpr447`;`t':l4_vexpr961`;`s':l4_vexpr961`;
                 `prog:l4_conversion_progress597`] l4_core_lazy_delta_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  l4_subst_cases_tac974 (SPEC `prog:l4_conversion_progress597` (cases "l4_conversion_progress597")) THEN
  REWRITE_TAC [l4_conversion_progress_dis974;l4_conv_dis974] THENL
  [DISCH_THEN (LABEL_TAC "Hprog") THEN l4_subst_true_tac974 THEN
   REMOVE_THEN "Hprog" MP_TAC THEN REWRITE_TAC [l4_conversion_progress_dis974];
   STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC l4_core_finish_conversion_sound974 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`F`;`rec0:l4_kmethods543`;
                         `fuel:num`;`g:l4_kcontext532`;`a0:l4_kexpr447`;`a1:l4_kexpr447`] THEN
   ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 7. Master Fuel Induction, Public Entry Points, & FuelConfig Wrappers      *)
(* ========================================================================= *)

let l4_checker_mode_sound974 = prove
 (`!fuel env venv ps mode.
   l4_venv_sound973 env venv ==>
   l4_full_methods_sound974 env venv ps T (l4_checker_mode597 fuel mode env ps)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
  [REWRITE_TAC [l4_checker_mode597;l4_full_methods_sound974;
                l4_infer_method543;l4_infer_type_method543;
                l4_whnf_method543;l4_whnf_core_method543;
                l4_defeq_method543;l4_eager_defeq_method543;l4_conv_dis974];
   SUBGOAL_THEN `l4_full_methods_sound974 env venv ps T (l4_checker_mode597 fuel mode env ps)`
     (LABEL_TAC "Hrec") THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_full_methods_sound974 env venv ps T (l4_checker_mode597 fuel L4EagerReduction543 env ps)`
     (LABEL_TAC "Heager") THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   REWRITE_TAC [l4_checker_mode597;l4_full_methods_sound974;
                l4_infer_method543;l4_infer_type_method543;
                l4_whnf_method543;l4_whnf_core_method543;
                l4_defeq_method543;l4_eager_defeq_method543] THEN
   REPEAT CONJ_TAC THENL
   [(* fms_infer *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_infer_step_sound_true974 THEN
    MAP_EVERY EXISTS_TAC [`l4_checker_mode597 fuel mode env ps`;`fuel:num`;`g:l4_kcontext532`] THEN
    ASM_REWRITE_TAC [];
    (* fms_infer_typed *)
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`e:l4_kexpr447`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_checker_mode597 fuel mode env ps`;`fuel:num`;`g:l4_kcontext532`;
                   `l:l4_vl_ctx_rec973`;`ty:l4_kexpr447`] l4_infer_step_sound_true974) THEN
    ASM_REWRITE_TAC [l4_vtr_typing973] THEN
    DISCH_THEN (X_CHOOSE_THEN `e1:l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
       l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
       l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
      STRIP_ASSUME_TAC THENL
    [l4_ctx_wf_tac974; ALL_TAC] THEN
    MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e1:l4_vexpr961` THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vtr_expr_uniq973 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`e:l4_kexpr447`] THEN ASM_REWRITE_TAC [];
    (* fms_infer_type *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_infer_step_sound_false974 THEN
    MAP_EVERY EXISTS_TAC [`e:l4_kexpr447`;`T`;`l4_checker_mode597 fuel mode env ps`;`fuel:num`;`g:l4_kcontext532`] THEN
    ASM_REWRITE_TAC [];
    (* fms_whnf_core *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_whnf_core_step_sound974 THEN
    MAP_EVERY EXISTS_TAC [`l4_checker_mode597 fuel mode env ps`;`fuel:num`;`cheap:bool`;
                          `g:l4_kcontext532`;`e:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    (* fms_whnf *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_whnf_loop_sound974 THEN
    MAP_EVERY EXISTS_TAC [`l4_whnf_round_limit543 mode`;`l4_checker_mode597 fuel mode env ps`;
                          `fuel:num`;`g:l4_kcontext532`;`e:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    (* fms_defeq *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_defeq_step_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`l4_checker_mode597 fuel mode env ps`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC [];
    (* fms_eager_defeq *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_defeq_step_sound974 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`l4_checker_mode597 fuel L4EagerReduction543 env ps`;
                          `fuel:num`;`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] THEN
    ASM_REWRITE_TAC []]]);;

let l4_checker_sound974 = prove
 (`!fuel env venv ps.
   l4_venv_sound973 env venv ==>
   l4_full_methods_sound974 env venv ps T (l4_checker597 fuel env ps)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_checker597] THEN
  MATCH_MP_TAC l4_checker_mode_sound974 THEN ASM_REWRITE_TAC []);;

let l4_infer_full_sound974 = prove
 (`!fuel env venv ps g l e ty.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_infer597 fuel env ps g e = L4KAccept491 ty ==>
   ?e' ty'.
     l4_vtr_expr973 env venv ps l e e' /\
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `T`;`l4_checker597 fuel env ps`] l4_fms_infer974) THEN
  ANTS_TAC THENL [MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`e:l4_kexpr447`;`ty:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC [GSYM l4_infer597;l4_vtr_typing973]);;

let l4_infer_full_sound_typed974 = prove
 (`!fuel env venv ps g l e e' ty.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_infer597 fuel env ps g e = L4KAccept491 ty ==>
   ?ty'.
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `T`;`l4_checker597 fuel env ps`] l4_fms_infer_typed974) THEN
  ANTS_TAC THENL [MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`e:l4_kexpr447`;
                              `e':l4_vexpr961`;`ty:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC [GSYM l4_infer597]);;

let l4_whnf_full_sound974 = prove
 (`!fuel env venv ps g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf597 fuel env ps g e = L4KAccept491 e1 ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_whnf597] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `T`;`l4_checker597 fuel env ps`] l4_fms_whnf974) THEN
  ANTS_TAC THENL [MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`e:l4_kexpr447`;
                                    `e':l4_vexpr961`;`e1:l4_kexpr447`]) THEN
  ASM_REWRITE_TAC []);;

let l4_defeq_full_sound974 = prove
 (`!fuel env venv ps g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_defeq597 fuel env ps g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_defeq597] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `T`;`l4_checker597 fuel env ps`] l4_fms_defeq974) THEN
  ANTS_TAC THENL [MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (MATCH_MP_TAC o SPECL [`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                                    `t:l4_kexpr447`;`t':l4_vexpr961`;
                                    `s:l4_kexpr447`;`s':l4_vexpr961`]) THEN
  ASM_REWRITE_TAC []);;

let l4_check_full_sound974 = prove
 (`!fuel env venv ps g l e ty.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_check597 fuel env ps g e ty = L4KAccept491 one ==>
   ?e' ty' u'.
     l4_vtr_expr973 env venv ps l e e' /\
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' (L4VSort961 u') /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check597;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `su:l4_klevel447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `et:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `ok:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN
  SUBGOAL_THEN
    `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv /\
     l4_vl_ctx_wf973 venv (LENGTH (ps:l4_name list)) l /\
     l4_vctx_wf966 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l)`
    STRIP_ASSUME_TAC THENL
  [l4_ctx_wf_tac974; ALL_TAC] THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_checker597 fuel env ps`;`g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;
                 `ty:l4_kexpr447`;`su:l4_klevel447`] l4_sort_of_sound_checking974) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`e:l4_kexpr447`;`et:l4_kexpr447`]
    l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `e':l4_vexpr961` (X_CHOOSE_THEN `et':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) et' ty'` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_defeq_full_sound974 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`env:l4_kdeclaration493 list`;`g:l4_kcontext532`;
                         `et:l4_kexpr447`;`ty:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`ty':l4_vexpr961`;`u':l4_vlevel961`] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `et':l4_vexpr961` THEN ASM_REWRITE_TAC []);;

let l4_check_defeq_full_sound974 = prove
 (`!fuel env venv ps g l t s.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_check_defeq597 fuel env ps g t s = L4KAccept491 one ==>
   ?t' s' ty.
     l4_vtr_expr973 env venv ps l t t' /\
     l4_vtr_expr973 env venv ps l s s' /\
     l4_vis_defeq961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s' ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_defeq597;l4_kr_bind_accept967] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `tt:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `st:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `ok1:bool` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 MP_TAC
            (X_CHOOSE_THEN `ok2:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN
  DISCH_THEN (K ALL_TAC) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`t:l4_kexpr447`;`tt:l4_kexpr447`]
    l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `t':l4_vexpr961` (X_CHOOSE_THEN `tt':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `g:l4_kcontext532`;`l:l4_vl_ctx_rec973`;`s:l4_kexpr447`;`st:l4_kexpr447`]
    l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `s':l4_vexpr961` (X_CHOOSE_THEN `st':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 l) t' s'`
    (X_CHOOSE_TAC `ty:l4_vexpr961` o REWRITE_RULE [l4_vis_defeq_u961]) THENL
  [MATCH_MP_TAC l4_defeq_full_sound974 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`env:l4_kdeclaration493 list`;`g:l4_kcontext532`;
                         `t:l4_kexpr447`;`s:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [];
   MAP_EVERY EXISTS_TAC [`t':l4_vexpr961`;`s':l4_vexpr961`;`ty:l4_vexpr961`] THEN ASM_REWRITE_TAC []]);;

(* FuelConfig entry-point wrappers *)

let l4_infer_with_config_sound974 = prove
 (`!cfg env venv ps g l e ty.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_infer_with_config965 cfg env ps g e = L4KAccept491 ty ==>
   ?e' ty'.
     l4_vtr_expr973 env venv ps l e e' /\
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_infer_with_config965] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  MESON_TAC [l4_infer_full_sound974]);;

let l4_whnf_with_config_sound974 = prove
 (`!cfg env venv ps g l e e' e1.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_whnf_with_config965 cfg env ps g e = L4KAccept491 e1 ==>
   l4_vtr_expr973 env venv ps l e1 e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_whnf_with_config965] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  MESON_TAC [l4_whnf_full_sound974]);;

let l4_defeq_with_config_sound974 = prove
 (`!cfg env venv ps g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   l4_defeq_with_config965 cfg env ps g t s = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_defeq_with_config965] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN
  MESON_TAC [l4_defeq_full_sound974]);;

let l4_eta_expand_with_config_sound974 = prove
 (`!cfg env venv ps g l e e' res.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l e e' /\
   l4_eta_expand_with_config965 cfg env ps g e = L4KAccept491 res ==>
   l4_vtr_expr973 env venv ps l res e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_eta_expand_with_config965] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_conv_dis974] THEN STRIP_TAC THEN
  MATCH_MP_TAC l4_core_eta_expand_sound974 THEN
  MAP_EVERY EXISTS_TAC [`e:l4_kexpr447`;`l4_fc_eta_expand965 cfg`;`T`;
                        `l4_checker597 (l4_fc_rec_depth965 cfg) env ps`;`g:l4_kcontext532`] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC []);;

let l4_check_with_config_sound974 = prove
 (`!cfg env venv ps g l e ty.
   l4_venv_sound973 env venv /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_check_with_config965 cfg env ps g e ty = L4KAccept491 one ==>
   ?e' ty' u'.
     l4_vtr_expr973 env venv ps l e e' /\
     l4_vtr_expr973 env venv ps l ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) ty' (L4VSort961 u') /\
     l4_vhas_type961 venv (LENGTH ps) (l4_vl_ctx973 l) e' ty'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_with_config965;l4_infer_with_config965;l4_defeq_with_config965] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_conv_dis974;GSYM l4_check597] THEN
  MESON_TAC [l4_check_full_sound974]);;

(* ========================================================================= *)
(* 8. Unconditional `l4_tr_e967`-Fragment Corollaries                        *)
(* ========================================================================= *)

let l4_vtr_expr_of_tr_e_lams974 = prove
 (`!env venv ps g e e' ty.
   l4_venv_wf966 venv /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_tr_e967 ps e = SOME e' /\
   l4_vhas_type961 venv (LENGTH ps) g e' ty ==>
   l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) e e'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_to_vtr_expr973 THEN
  MATCH_MP_TAC l4_vtr_expr_s_of_tr_e973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
  ASM_REWRITE_TAC []);;

let l4_defeq_types_sound_unconditional974 = prove
 (`!fuel env venv ps mode bs g a b av bv.
   l4_venv_sound973 env venv /\
   l4_tr_bctx967 ps bs g /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_defeq_method543 (l4_checker_mode597 fuel mode env ps) (L4KContext532 bs []) a b = L4KAccept491 T /\
   l4_tr_e967 ps a = SOME av /\
   l4_tr_e967 ps b = SOME bv /\
   l4_vis_type961 venv (LENGTH ps) g av /\
   l4_vis_type961 venv (LENGTH ps) g bv ==>
   ?u. l4_vis_defeq961 venv (LENGTH ps) g av bv (L4VSort961 u)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vis_type961] THEN
  DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_TAC `uB:l4_vlevel961`)) THEN
  POP_ASSUM (fun hB -> POP_ASSUM (X_CHOOSE_TAC `uA:l4_vlevel961`) THEN ASSUME_TAC hB) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (L4KContext532 bs []) (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_of_tr_bctx973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
    `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) a av /\
     l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) b bv` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC l4_vtr_expr_of_tr_e_lams974 THENL
   [EXISTS_TAC `L4VSort961 uA` THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `L4VSort961 uB` THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) (l4_vl_ctx973 (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))) av bv`
    MP_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `T`;`l4_checker_mode597 fuel mode env ps`] l4_fms_defeq974) THEN
   ANTS_TAC THENL [MATCH_MP_TAC l4_checker_mode_sound974 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL
     [`L4KContext532 bs []`;`L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;
      `a:l4_kexpr447`;`av:l4_vexpr961`;`b:l4_kexpr447`;`bv:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [l4_vis_defeq_u961;l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
               MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973] THEN
  DISCH_THEN (X_CHOOSE_TAC `ty:l4_vexpr961`) THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`g:l4_vexpr961 list`;
                 `av:l4_vexpr961`;`av:l4_vexpr961`;`bv:l4_vexpr961`;
                 `L4VSort961 uA`;`ty:l4_vexpr961`] l4_vis_defeq_uniq_same972) THEN
  ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
  DISCH_THEN (X_CHOOSE_TAC `us:l4_vlevel961`) THEN
  EXISTS_TAC `uA:l4_vlevel961` THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`ty:l4_vexpr961`;`us:l4_vlevel961`] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_symm961 THEN ASM_REWRITE_TAC []);;

let l4_infer_sound_tr_e_unconditional974 = prove
 (`!fuel env venv ps bs g e ty e'.
   l4_venv_sound973 env venv /\
   l4_tr_bctx967 ps bs g /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_infer597 fuel env ps (L4KContext532 bs []) e = L4KAccept491 ty /\
   l4_tr_e967 ps e = SOME e' ==>
   ?ty'.
     l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) g e' ty'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (L4KContext532 bs []) (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_of_tr_bctx973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `L4KContext532 bs []`;`L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;
                 `e:l4_kexpr447`;`ty:l4_kexpr447`] l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `e1:l4_vexpr961` (X_CHOOSE_THEN `ty':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) e e1` THEN
  DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
  SUBGOAL_THEN `e0:l4_vexpr961 = e'` SUBST_ALL_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
     l4_vtr_expr_s_eq_tr_e973) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973];
   ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                                MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973]) THEN
  EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e1:l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []);;

let l4_check_sound_tr_e_unconditional974 = prove
 (`!fuel env venv ps bs g e ty e' ty'.
   l4_venv_sound973 env venv /\
   l4_tr_bctx967 ps bs g /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_check597 fuel env ps (L4KContext532 bs []) e ty = L4KAccept491 one /\
   l4_tr_e967 ps e = SOME e' /\
   l4_tr_e967 ps ty = SOME ty' ==>
   l4_vhas_type961 venv (LENGTH ps) g e' ty'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (L4KContext532 bs []) (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_of_tr_bctx973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `L4KContext532 bs []`;`L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;
                 `e:l4_kexpr447`;`ty:l4_kexpr447`] l4_check_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `e1:l4_vexpr961` (X_CHOOSE_THEN `ty1:l4_vexpr961`
    (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) e e1` THEN
  DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) ty ty1` THEN
  DISCH_THEN (X_CHOOSE_THEN `t0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
  SUBGOAL_THEN `e0:l4_vexpr961 = e' /\ t0:l4_vexpr961 = ty'` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
  [CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;`e:l4_kexpr447`;`e0:l4_vexpr961`]
      l4_vtr_expr_s_eq_tr_e973);
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;`ty:l4_kexpr447`;`t0:l4_vexpr961`]
      l4_vtr_expr_s_eq_tr_e973)] THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973];
   ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                                MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973]) THEN
  MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty1:l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `e1:l4_vexpr961` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []]);;

let l4_check_defeq_sound_tr_e_unconditional974 = prove
 (`!fuel env venv ps bs g t s t' s'.
   l4_venv_sound973 env venv /\
   l4_tr_bctx967 ps bs g /\
   l4_vctx_wf966 venv (LENGTH ps) g /\
   l4_check_defeq597 fuel env ps (L4KContext532 bs []) t s = L4KAccept491 one /\
   l4_tr_e967 ps t = SOME t' /\
   l4_tr_e967 ps s = SOME s' ==>
   ?ty. l4_vis_defeq961 venv (LENGTH ps) g t' s' ty`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vtr_ctx973 env venv ps (L4KContext532 bs []) (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vtr_ctx_of_tr_bctx973 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `L4KContext532 bs []`;`L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;
                 `t:l4_kexpr447`;`s:l4_kexpr447`] l4_check_defeq_full_sound974) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `t1:l4_vexpr961` (X_CHOOSE_THEN `s1:l4_vexpr961`
    (X_CHOOSE_THEN `ty:l4_vexpr961` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) t t1` THEN
  DISCH_THEN (X_CHOOSE_THEN `t0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv ps (L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)) s s1` THEN
  DISCH_THEN (X_CHOOSE_THEN `s0:l4_vexpr961` STRIP_ASSUME_TAC o REWRITE_RULE [l4_vtr_expr973]) THEN
  SUBGOAL_THEN `t0:l4_vexpr961 = t' /\ s0:l4_vexpr961 = s'` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
  [CONJ_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;`t:l4_kexpr447`;`t0:l4_vexpr961`]
      l4_vtr_expr_s_eq_tr_e973);
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `L4VLCtx973 [] (l4_vl_of_ctx_lams973 g)`;`s:l4_kexpr447`;`s0:l4_vexpr961`]
      l4_vtr_expr_s_eq_tr_e973)] THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `g:l4_vexpr961 list` THEN ASM_REWRITE_TAC [l4_vl_free973;l4_vl_bound973];
   ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vl_ctx973;l4_vl_bound973;l4_vl_free973;l4_vl_free_ctx973;
                                MAP;l4_vlentries_to_ctx973;APPEND_NIL;l4_vlentries_to_ctx_of_lams973]) THEN
  SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) g t' s'`
    (ACCEPT_TAC o REWRITE_RULE [l4_vis_defeq_u961]) THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `t1:l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vis_defeq_u_trans972 THEN EXISTS_TAC `s1:l4_vexpr961` THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_vis_defeq_u961] THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 9. Composing with `equiv_manager964.ml` (DefEq Cache & EquivManager)      *)
(* ========================================================================= *)

let l4_cached_defeq_full_sound974 = prove
 (`!fuel env venv ps g cache l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_cache_sound_for964 fuel env ps cache /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' /\
   SND (l4_cached_defeq964 fuel env ps g cache t s) = L4KAccept491 T ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC l4_defeq_full_sound974 THEN
  MAP_EVERY EXISTS_TAC [`fuel:num`;`env:l4_kdeclaration493 list`;`g:l4_kcontext532`;
                        `t:l4_kexpr447`;`s:l4_kexpr447`] THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`ps:l4_name list`;
                 `g:l4_kcontext532`;`cache:((l4_defeq_cache_key964) # bool) list`;
                 `t:l4_kexpr447`;`s:l4_kexpr447`] l4_cached_defeq_refines_uncached964) THEN
  ASM_MESON_TAC []);;

let l4_sem_defeq_rel974 = new_definition
 `l4_sem_defeq_rel974 env venv ps g t s <=>
   !l t' s'.
     l4_vtr_ctx973 env venv ps g l /\
     l4_vtr_expr973 env venv ps l t t' /\
     l4_vtr_expr973 env venv ps l s s' ==>
     l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`;;

let l4_em_is_equiv_ro_vis_defeq_u974 = prove
 (`!env venv ps m g l t s t' s'.
   l4_venv_sound973 env venv /\
   l4_em_sound_for964 (l4_sem_defeq_rel974 env venv ps) m /\
   l4_em_is_equiv_ro964 m g t s /\
   l4_vtr_ctx973 env venv ps g l /\
   l4_vtr_expr973 env venv ps l t t' /\
   l4_vtr_expr973 env venv ps l s s' ==>
   l4_vis_defeq_u961 venv (LENGTH ps) (l4_vl_ctx973 l) t' s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`l4_sem_defeq_rel974 env venv ps`;`m:l4_equiv_manager964`;
                  `g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`]
    l4_em_is_equiv_ro_sound964) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_sem_defeq_rel974] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC l4_vtr_expr_core_alpha_eq973 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`a:l4_kexpr447`;`b:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [] THEN l4_ctx_wf_tac974;
   REWRITE_TAC [l4_sem_defeq_rel974] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`l:l4_vl_ctx_rec973`;`t':l4_vexpr961`;`s':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC []]);;
