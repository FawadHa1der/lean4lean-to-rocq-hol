(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end environment & admission soundness of the executable HOL Light v3
   kernel (`ordinary_admission607.ml`, `ordinary_admission620.ml`,
   `safety_admission624.ml`, `quotient_admission608.ml`,
   `quotient_transaction963.ml`, `inductive_safety633.ml`, `fuel_config965.ml`,
   `file_driver642.ml`) against `l4_venv_wf966`, `l4_venv_sound973`, and
   `env_decl_theory971.ml`.

   Direct 1-to-1 port of `rocq/VerifyEnvironment.v`. Zero new axioms. *)

needs "hol/verify_typechecker974.ml";;
needs "hol/file_driver642.ml";;
needs "hol/quotient_transaction963.ml";;
needs "hol/primitive_properties620.ml";;

(* ========================================================================= *)
(* 1. Environment Extension & Monotonicity for `VTrExpr` / `VEnvSound`       *)
(* ========================================================================= *)

let l4_env_dis975 = end_itlist CONJ
  [l4_conv_dis974;
   distinctness "l4_input_decl607"; injectivity "l4_input_decl607";
   distinctness "l4_input_safety607";
   distinctness "l4_file_decl642"; injectivity "l4_file_decl642";
   distinctness "l4_file_batch642"; injectivity "l4_file_batch642"];;

let l4_opt_cases_keep975 tm v =
  MP_TAC (ISPEC tm (cases "option")) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_env_dis975])
    (X_CHOOSE_THEN v (fun th -> ASSUME_TAC th THEN REWRITE_TAC [th;l4_env_dis975])));;

let l4_env_extends975 = new_definition
 `l4_env_extends975 env1 env2 <=>
   (!n d. l4_kfind_decl493 env1 n = SOME d ==> l4_kfind_decl493 env2 n = SOME d) /\
   (l4_core_nat_ready533 env1 ==> l4_core_nat_ready533 env2) /\
   (l4_core_bool_ready533 env1 ==> l4_core_bool_ready533 env2) /\
   (l4_core_string_ready533 env1 ==> l4_core_string_ready533 env2)`;;

let l4_kfind_decl_cons_fresh975 = prove
 (`!env d n d0.
   l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
   l4_kfind_decl493 env n = SOME d0 ==>
   l4_kfind_decl493 (CONS d env) n = SOME d0`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_kfind_decl493] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `l4_kfind_decl493 env n = SOME d0` THEN
  ASM_REWRITE_TAC [l4_env_dis975]);;

let l4_core_inductive_extends975 = prove
 (`!env1 env2 owner info.
   (!n d. l4_kfind_decl493 env1 n = SOME d ==> l4_kfind_decl493 env2 n = SOME d) /\
   l4_core_inductive532 env1 owner = SOME info ==>
   l4_core_inductive532 env2 owner = SOME info`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_inductive532] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env1 owner` `a:l4_kdeclaration493` THEN
  SUBGOAL_THEN `l4_kfind_decl493 env2 owner = SOME a`
    (fun th -> REWRITE_TAC [th] THEN DISCH_THEN ACCEPT_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_core_constructor_extends975 = prove
 (`!env1 env2 cn ci.
   (!n d. l4_kfind_decl493 env1 n = SOME d ==> l4_kfind_decl493 env2 n = SOME d) /\
   l4_core_constructor532 env1 cn = SOME ci ==>
   l4_core_constructor532 env2 cn = SOME ci`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_constructor532] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env1 cn` `a:l4_kdeclaration493` THEN
  SUBGOAL_THEN `l4_kfind_decl493 env2 cn = SOME a`
    (fun th -> REWRITE_TAC [th] THEN DISCH_THEN ACCEPT_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_core_ctor_shape_extends975 = prove
 (`!env1 env2 n parent idx flds ty.
   (!m d. l4_kfind_decl493 env1 m = SOME d ==> l4_kfind_decl493 env2 m = SOME d) /\
   l4_core_ctor_shape533 env1 n parent idx flds ty ==>
   l4_core_ctor_shape533 env2 n parent idx flds ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_ctor_shape533] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env1 n` `a:l4_kdeclaration493` THEN
  SUBGOAL_THEN `l4_kfind_decl493 env2 n = SOME a`
    (fun th -> REWRITE_TAC [th] THEN DISCH_THEN ACCEPT_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_env_extends_cons_fresh975 = prove
 (`!env d.
   l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE ==>
   l4_env_extends975 env (CONS d env)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n d0. l4_kfind_decl493 env n = SOME d0 ==> l4_kfind_decl493 (CONS d env) n = SOME d0`
    (LABEL_TAC "Hfind") THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_kfind_decl_cons_fresh975 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_nat_ready533 env ==> l4_core_nat_ready533 (CONS d env)` (LABEL_TAC "Hnat") THENL
  [REWRITE_TAC [l4_core_nat_ready533] THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_nat_name533` `a:l4_kdeclaration493` THEN
   SUBGOAL_THEN `l4_kfind_decl493 (CONS d env) l4_core_nat_name533 = SOME a`
     (fun th -> REWRITE_TAC [th]) THENL
   [USE_THEN "Hfind" MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_core_ctor_shape_extends975 THEN
   EXISTS_TAC `env:l4_kdeclaration493 list` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_bool_ready533 env ==> l4_core_bool_ready533 (CONS d env)` (LABEL_TAC "Hbool") THENL
  [REWRITE_TAC [l4_core_bool_ready533] THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_bool_name533` `a:l4_kdeclaration493` THEN
   SUBGOAL_THEN `l4_kfind_decl493 (CONS d env) l4_core_bool_name533 = SOME a`
     (fun th -> REWRITE_TAC [th]) THENL
   [USE_THEN "Hfind" MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   CONJ_TAC THEN MATCH_MP_TAC l4_core_ctor_shape_extends975 THEN
   EXISTS_TAC `env:l4_kdeclaration493 list` THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [l4_env_extends975] THEN ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [l4_core_string_ready533] THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_char_of_nat533` `a:l4_kdeclaration493` THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_string_of_list533` `a':l4_kdeclaration493` THEN
  SUBGOAL_THEN `l4_kfind_decl493 (CONS d env) l4_core_char_of_nat533 = SOME a /\
                l4_kfind_decl493 (CONS d env) l4_core_string_of_list533 = SOME a'`
    (fun th -> REWRITE_TAC [th]) THENL
  [CONJ_TAC THEN USE_THEN "Hfind" MATCH_MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a'` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  REPEAT (fun (asl,w) ->
    match find_terms (fun t -> is_var t && type_of t = `:l4_kprimitive493`) w with
    | v::_ -> (l4_subst_cases_tac974 (SPEC v (cases "l4_kprimitive493")) THEN
               REWRITE_TAC [l4_env_dis975]) (asl,w)
    | [] -> FAIL_TAC "no prim" (asl,w)) THEN
  ASM_REWRITE_TAC []);;

let l4_vtr_proj_extend_env975 = prove
 (`!env1 env2 venv1 venv2 uvars g owner idx sv pv fty.
   l4_env_extends975 env1 env2 /\
   l4_venv_ordered961 venv1 venv2 /\
   l4_vtr_proj973 env1 venv1 uvars g owner idx sv pv fty ==>
   l4_vtr_proj973 env2 venv2 uvars g owner idx sv pv fty`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_env_extends975;l4_vtr_proj973] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
     `d:l4_kdeclaration493`;`us:l4_vlevel961 list`;`params:l4_vexpr961 list`;
     `indices:l4_vexpr961 list`] THEN
  ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_core_inductive_extends975;l4_venv_ordered_preserve_vhas_type961]);;

let l4_vtr_expr_s_extend_env975 = prove
 (`!env1 venv1 ps l e e'.
   l4_vtr_expr_s973 env1 venv1 ps l e e' ==>
   (!env2 venv2.
     l4_env_extends975 env1 env2 /\
     l4_venv_ordered961 venv1 venv2 ==>
     l4_vtr_expr_s973 env2 venv2 ps l e e')`,
  MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
  [(* BVar *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vhas_type961];
   (* FVar *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vhas_type961];
   (* Sort *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
   (* Const *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN
   ASM_MESON_TAC [l4_venv_ordered_const973];
   (* App *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vhas_type961];
   (* Lam *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966;l4_venv_ordered_preserve_vhas_type961];
   (* Pi *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966;l4_venv_ordered_preserve_vhas_type961];
   (* Let *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
   MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`val':l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_venv_ordered_preserve_vis_type966;l4_venv_ordered_preserve_vhas_type961];
   (* Proj *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
   MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`fty:l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_vtr_proj_extend_env975];
   (* NatLit *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN
   ASM_MESON_TAC [l4_env_extends975;l4_venv_ordered_preserve_vhas_type961];
   (* StrLit *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN
   ASM_MESON_TAC [l4_env_extends975;l4_venv_ordered_preserve_vhas_type961];
   (* MData *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_MESON_TAC []]);;

let l4_vtr_expr_extend_env975 = prove
 (`!env1 env2 venv1 venv2 ps l e e'.
   l4_env_extends975 env1 env2 /\
   l4_venv_ordered961 venv1 venv2 /\
   l4_vtr_expr973 env1 venv1 ps l e e' ==>
   l4_vtr_expr973 env2 venv2 ps l e e'`,
  REWRITE_TAC [l4_vtr_expr973;l4_vis_defeq_u961] THEN
  MESON_TAC [l4_vtr_expr_s_extend_env975;l4_venv_ordered_preserve_vis_defeq961]);;

let l4_vtr_ctx_empty975 = prove
 (`!env venv ps.
   l4_vtr_ctx973 env venv ps l4_kempty_context532 l4_vl_empty973`,
  REWRITE_TAC [l4_vtr_ctx973;l4_kempty_context532;l4_vl_empty973;
               l4_kcontext_free532;l4_kcontext_bound532;l4_vl_free973;l4_vl_bound973;
               l4_vtr_free_nil973;l4_vtr_bound_nil973]);;

let l4_vl_ctx_empty975 = prove
 (`l4_vl_ctx973 l4_vl_empty973 = []`,
  REWRITE_TAC [l4_vl_ctx973;l4_vl_empty973;l4_vl_bound973;l4_vl_free973;
               l4_vl_free_ctx973;l4_vlentries_to_ctx973;MAP;APPEND]);;

(* ========================================================================= *)
(* 2. Checking Helpers (`check_header`, `check_proposition`, `check_value`)  *)
(* ========================================================================= *)

let l4_check_header_sound975 = prove
 (`!fuel env venv n ps ty.
   l4_venv_sound973 env venv /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one ==>
   l4_kfind_decl493 env n = NONE /\
   l4_names_unique437 ps /\
   l4_kscoped447 ty 0 /\
   ?ty' u'.
     l4_vtr_expr973 env venv ps l4_vl_empty973 ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) [] ty' (L4VSort961 u') /\
     l4_vconstant_wf966 venv (L4VConstant961 (LENGTH ps) ty')`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_header607] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973]; ALL_TAC] THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env n` `a:l4_kdeclaration493` THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `inf_e:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  l4_subst_cases_tac974 (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_kempty_context532`;`l4_vl_empty973`;`ty:l4_kexpr447`;`inf_e:l4_kexpr447`]
    l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [l4_vtr_ctx_empty975;l4_vl_ctx_empty975] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` (X_CHOOSE_THEN `inf_e':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l4_vl_empty973 (L4KSort447 a) inf_e'`
    (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
  [MATCH_MP_TAC l4_whnf_full_sound974 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`l4_kempty_context532`;`inf_e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [l4_vtr_ctx_empty975];
   ALL_TAC] THEN
  REWRITE_TAC [l4_vl_ctx_empty975] THEN
  DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) [] ty' (L4VSort961 u')` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `inf_e':l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vctx_wf966] THEN
   MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [l4_vctx_wf966];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u':l4_vlevel961`] THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN ASM_REWRITE_TAC [l4_vis_type961] THEN
  EXISTS_TAC `u':l4_vlevel961` THEN ASM_REWRITE_TAC []);;

let l4_check_proposition_sound975 = prove
 (`!fuel env venv ps ty.
   l4_venv_sound973 env venv /\
   l4_check_proposition607 fuel env ps ty = L4KAccept491 one ==>
   ?ty'.
     l4_vtr_expr973 env venv ps l4_vl_empty973 ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) [] ty' (L4VSort961 L4VLZero961)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_proposition607;l4_kr_bind_accept967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `inf_e:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `red:l4_kexpr447` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_defeq_injectivity972 venv` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_ves_inj973]; ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `red:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `isz:bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_kempty_context532`;`l4_vl_empty973`;`ty:l4_kexpr447`;`inf_e:l4_kexpr447`]
    l4_infer_full_sound974) THEN
  ASM_REWRITE_TAC [l4_vtr_ctx_empty975;l4_vl_ctx_empty975] THEN
  DISCH_THEN (X_CHOOSE_THEN `ty':l4_vexpr961` (X_CHOOSE_THEN `inf_e':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `l4_vtr_expr973 env venv ps l4_vl_empty973 (L4KSort447 a) inf_e'`
    (MP_TAC o MATCH_MP l4_vtr_expr_inv_sort973) THENL
  [MATCH_MP_TAC l4_whnf_full_sound974 THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`l4_kempty_context532`;`inf_e:l4_kexpr447`] THEN
   ASM_REWRITE_TAC [l4_vtr_ctx_empty975];
   ALL_TAC] THEN
  REWRITE_TAC [l4_vl_ctx_empty975] THEN
  DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) [] ty' (L4VSort961 u')` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `inf_e':l4_vexpr961` THEN
   ASM_REWRITE_TAC [l4_vctx_wf966] THEN
   MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN ASM_REWRITE_TAC [l4_vctx_wf966];
   ALL_TAC] THEN
  EXISTS_TAC `ty':l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`L4VSort961 u'`;`L4VLSucc961 u'`] THEN
  ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_sort961 THEN
  ASM_REWRITE_TAC [l4_vlevel_wf961] THEN
  MATCH_MP_TAC l4_klevel_equiv_sound_vlevel973 THEN
  MAP_EVERY EXISTS_TAC [`fuel:num`;`ps:l4_name list`;`a:l4_klevel447`;`L4KZero447`] THEN
  ASM_REWRITE_TAC [l4_tr_l967]);;

let l4_check_value_sound975 = prove
 (`!fuel env venv ps ty val_e.
   l4_venv_sound973 env venv /\
   l4_check_value624 fuel env ps ty val_e = L4KAccept491 one ==>
   l4_kscoped447 val_e 0 /\
   ?val' ty' u'.
     l4_vtr_expr973 env venv ps l4_vl_empty973 val_e val' /\
     l4_vtr_expr973 env venv ps l4_vl_empty973 ty ty' /\
     l4_vhas_type961 venv (LENGTH ps) [] ty' (L4VSort961 u') /\
     l4_vhas_type961 venv (LENGTH ps) [] val' ty'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_value624] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `l4_kempty_context532`;`l4_vl_empty973`;`val_e:l4_kexpr447`;`ty:l4_kexpr447`]
    l4_check_full_sound974) THEN
  ASM_REWRITE_TAC [l4_vtr_ctx_empty975;l4_vl_ctx_empty975]);;

(* ========================================================================= *)
(* 3. Primitive Verification Soundness (`primitive_admission620.ml`)         *)
(* ========================================================================= *)

let l4_primitive_check_equations_accepts975 = prove
 (`!eqs steps fuel env.
   l4_primitive_check_equations620 eqs steps fuel env = L4KAccept491 one ==>
   ALL (\eq. l4_check_defeq597 fuel env [] (l4_primitive_context619 eq)
               (l4_primitive_lhs619 eq) (l4_primitive_rhs619 eq) = L4KAccept491 one) eqs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_primitive_check_equations620;ALL] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `l4_check_defeq597 fuel env [] (l4_primitive_context619 h)
                  (l4_primitive_lhs619 h) (l4_primitive_rhs619 h) = L4KAccept491 u1` THEN
   STRUCT_CASES_TAC (SPEC `u1:1` one) THEN REWRITE_TAC [];
   FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `steps - 1` THEN ASM_REWRITE_TAC []]);;

let l4_primitive_check_equations_sound975 = prove
 (`!eqs steps fuel env venv.
   l4_venv_sound973 env venv /\
   l4_primitive_check_equations620 eqs steps fuel env = L4KAccept491 one ==>
   ALL (\eq. !l. l4_vtr_ctx973 env venv [] (l4_primitive_context619 eq) l ==>
                 ?lhs' rhs' ty.
                   l4_vtr_expr973 env venv [] l (l4_primitive_lhs619 eq) lhs' /\
                   l4_vtr_expr973 env venv [] l (l4_primitive_rhs619 eq) rhs' /\
                   l4_vis_defeq961 venv 0 (l4_vl_ctx973 l) lhs' rhs' ty) eqs`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`eqs:l4_primitive_equation619 list`;`steps:num`;`fuel:num`;
                 `env:l4_kdeclaration493 list`] l4_primitive_check_equations_accepts975) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`[]:l4_name list`;
                 `l4_primitive_context619 x`;`l:l4_vl_ctx_rec973`;
                 `l4_primitive_lhs619 x`;`l4_primitive_rhs619 x`] l4_check_defeq_full_sound974) THEN
  ASM_SIMP_TAC [LENGTH]);;

let l4_primitive_ensure_type_sound975 = prove
 (`!fuel env venv e.
   l4_venv_sound973 env venv /\
   l4_primitive_ensure_type620 fuel env e = L4KAccept491 one ==>
   ?e' u'.
     l4_vtr_expr973 env venv [] l4_vl_empty973 e e' /\
     l4_vhas_type961 venv 0 [] e' (L4VSort961 u')`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_primitive_ensure_type620;l4_kr_bind_accept967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:l4_klevel447` ASSUME_TAC)) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`[]:l4_name list`;
                 `l4_checker597 fuel env []`;`l4_kempty_context532`;`l4_vl_empty973`;
                 `e:l4_kexpr447`;`u:l4_klevel447`] l4_sort_of_sound_checking974) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_vtr_ctx_empty975] THEN MATCH_MP_TAC l4_checker_sound974 THEN ASM_REWRITE_TAC [];
   REWRITE_TAC [LENGTH;l4_vl_ctx_empty975] THEN MESON_TAC []]);;

let l4_classify_primitive_sound975 = prove
 (`!fuel env venv n ps ty body op.
   l4_venv_sound973 env venv /\
   l4_classify_primitive620 fuel env n ps ty body = L4KAccept491 (SOME op) ==>
   l4_primitive_lookup619 n = SOME op /\
   l4_kfind_decl493 env n = NONE /\
   ps = [] /\
   ((~l4_primitive_is_text620 op /\
     l4_primitive_check_nat_equations620 fuel env op body = L4KAccept491 one) \/
    (l4_primitive_is_text620 op /\
     l4_primitive_check_text_interface620 fuel env op = L4KAccept491 one))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_classify_primitive620] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  l4_opt_cases_keep975 `l4_primitive_lookup619 n` `op0:l4_kprimitive493` THENL
  [COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975]; ALL_TAC] THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env n` `d0:l4_kdeclaration493` THEN
  REWRITE_TAC [l4_kr_bind491;l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_kr_bind491;l4_env_dis975] THEN
  REWRITE_TAC [l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `u3:1` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u4:1` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u5:1` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC [GSYM LENGTH_EQ_NIL] THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (SPEC `u5:1` one) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC []);;

(* ========================================================================= *)
(* 4. Core Declaration Admission (`ordinary_admission607/620` -> `VEnvSound`) *)
(* ========================================================================= *)

let l4_venv_names_aligned975 = new_definition
 `l4_venv_names_aligned975 env venv <=>
   !n. l4_kfind_decl493 env n = NONE ==> ~l4_venv_contains971 venv n`;;

let l4_venv_names_aligned_empty975 = prove
 (`l4_venv_names_aligned975 [] l4_venv_empty961`,
  REWRITE_TAC [l4_venv_names_aligned975;l4_venv_contains971;l4_venv_empty961;
               l4_venv_lookup_const961;l4_venv_consts_list961;MEM]);;

let l4_checked_constant_sound_aligned975 = prove
 (`!fuel env venv n ps ty body kind next.
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_checked_constant607 fuel env n ps ty body kind = L4KAccept491 next ==>
   let d = L4KDeclaration493 n ps ty body kind L4KHintOpaque493 in
   next = CONS d env /\
   l4_kfind_decl493 env n = NONE /\
   ?ci venv'.
     l4_vc_uvars961 ci = LENGTH ps /\
     l4_vtr_expr973 env venv ps l4_vl_empty973 ty (l4_vc_type961 ci) /\
     l4_vtr_expr973 next venv' ps l4_vl_empty973 ty (l4_vc_type961 ci) /\
     l4_vis_type961 venv' (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) /\
     l4_vclosedN961 (l4_vc_type961 ci) 0 /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     l4_venv_lookup_const961 venv' n ci /\
     l4_venv_names_aligned975 next venv' /\
     (match body with
      | NONE -> (!df. l4_venv_has_defeq961 venv' df <=> l4_venv_has_defeq961 venv df)
      | SOME val_e ->
          ?val'.
            l4_vtr_expr973 env venv ps l4_vl_empty973 val_e val' /\
            l4_vtr_expr973 next venv' ps l4_vl_empty973 val_e val' /\
            l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] val' (l4_vc_type961 ci) /\
            l4_vclosedN961 val' 0 /\
            (match kind with
             | L4KDDefinition493 ->
                 l4_venv_has_defeq961 venv'
                   (L4VDefEq961 (l4_vc_uvars961 ci)
                     (L4VConst961 n (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                     val' (l4_vc_type961 ci))
             | L4KDTheorem493 ->
                 l4_venv_has_defeq961 venv'
                   (L4VDefEq961 (l4_vc_uvars961 ci)
                     (L4VConst961 n (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                     val' (l4_vc_type961 ci))
             | L4KDPrimitive493 p ->
                 l4_venv_has_defeq961 venv'
                   (L4VDefEq961 (l4_vc_uvars961 ci)
                     (L4VConst961 n (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                     val' (l4_vc_type961 ci))
             | _ -> (!df. l4_venv_has_defeq961 venv' df <=> l4_venv_has_defeq961 venv df)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_checked_constant607;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Halign")
    (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hhdr")
      (X_CHOOSE_THEN `u2:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hbody") MP_TAC)))))) THEN
  REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973]; ALL_TAC] THEN
  REMOVE_THEN "Hhdr" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u1:1` one) THEN DISCH_TAC THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                 `n:l4_name`;`ps:l4_name list`;`ty:l4_kexpr447`] l4_check_header_sound975) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hfresh")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ty':l4_vexpr961` (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `~l4_venv_contains971 venv n` ASSUME_TAC THENL
  [USE_THEN "Halign" (MATCH_MP_TAC o REWRITE_RULE [l4_venv_names_aligned975]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  ABBREV_TAC `ci = L4VConstant961 (LENGTH (ps:l4_name list)) ty'` THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`n:l4_name`;`ci:l4_vconstant961`] l4_venv_add_const_eq_none971) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `venv1:l4_venv961`) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv1 /\ l4_venv_ordered961 venv venv1 /\
                l4_venv_lookup_const961 venv1 n ci` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_add_const_self971]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_vclosedN961 ty' 0` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_vconstant_wf966 venv ci` THEN EXPAND_TAC "ci" THEN
   REWRITE_TAC [l4_vconstant_wf966;l4_vc_type961] THEN MESON_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_env_extends975 env (CONS (L4KDeclaration493 n ps ty body kind L4KHintOpaque493) env)`
    (LABEL_TAC "Hext") THENL
  [MATCH_MP_TAC l4_env_extends_cons_fresh975 THEN ASM_REWRITE_TAC [l4_kdecl_name493]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_names_aligned975 (CONS (L4KDeclaration493 n ps ty body kind L4KHintOpaque493) env) venv1`
    (LABEL_TAC "Halign1") THENL
  [REWRITE_TAC [l4_venv_names_aligned975;l4_kfind_decl493;l4_kdecl_name493;l4_venv_contains971] THEN
   GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
   DISCH_THEN (X_CHOOSE_TAC `c0:l4_vconstant961`) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`n:l4_name`;`ci:l4_vconstant961`;`venv1:l4_venv961`;
                  `n':l4_name`;`c0:l4_vconstant961`] l4_venv_add_const_lookup971) THEN
   ASM_REWRITE_TAC [] THEN
   USE_THEN "Halign" (MP_TAC o SPEC `n':l4_name` o REWRITE_RULE [l4_venv_names_aligned975;l4_venv_contains971]) THEN
   ASM_MESON_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  REMOVE_THEN "Hbody" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u2:1` one) THEN
  l4_subst_cases_tac974 (ISPEC `body:(l4_kexpr447)option` (cases "option")) THEN
  REWRITE_TAC [l4_env_dis975] THENL
  [(* NONE *)
   MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`venv1:l4_venv961`] THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (ps:l4_name list) /\ l4_vc_type961 ci = ty'`
     (fun th -> REWRITE_TAC [th]) THENL
   [EXPAND_TAC "ci" THEN REWRITE_TAC [l4_vc_uvars961;l4_vc_type961]; ALL_TAC] THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `u':l4_vlevel961` THEN
    MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [];
    GEN_TAC THEN MATCH_MP_TAC l4_venv_add_const_has_defeq971 THEN
    MAP_EVERY EXISTS_TAC [`n:l4_name`;`ci:l4_vconstant961`] THEN ASM_REWRITE_TAC []];
   (* SOME val_e *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                  `l4_kempty_context532`;`l4_vl_empty973`;`a:l4_kexpr447`;`ty:l4_kexpr447`]
     l4_check_full_sound974) THEN
   ASM_REWRITE_TAC [l4_vtr_ctx_empty975;l4_vl_ctx_empty975] THEN
   DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `ty2':l4_vexpr961`
     (X_CHOOSE_THEN `u2':l4_vlevel961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (ps:l4_name list)) [] ty2' ty'` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                   `l4_vl_empty973`;`ty:l4_kexpr447`;`ty2':l4_vexpr961`;`ty':l4_vexpr961`]
      l4_vtr_expr_uniq973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_empty975;l4_vl_ctx_wf_empty973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (ps:l4_name list)) [] val' ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty2':l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv1 (LENGTH (ps:l4_name list)) [] val' ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vclosedN961 val' 0` ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`[]:l4_vexpr961 list`;
                   `val':l4_vexpr961`;`val':l4_vexpr961`;`ty':l4_vexpr961`] l4_vis_defeq_closedN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vctx_closed966;LENGTH] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (ps:l4_name list) /\ l4_vc_type961 ci = ty'`
     (LABEL_TAC "Hci_eq") THENL
   [EXPAND_TAC "ci" THEN REWRITE_TAC [l4_vc_uvars961;l4_vc_type961]; ALL_TAC] THEN
   SUBGOAL_THEN
     `?venv2.
        l4_venv_ordered961 venv venv2 /\
        l4_venv_wf966 venv2 /\
        l4_venv_lookup_const961 venv2 n ci /\
        l4_venv_names_aligned975 (CONS (L4KDeclaration493 n ps ty (SOME a) kind L4KHintOpaque493) env) venv2 /\
        l4_vhas_type961 venv2 (LENGTH ps) [] val' ty' /\
        l4_venv_has_defeq961 venv2
          (L4VDefEq961 (LENGTH ps) (L4VConst961 n (l4_vlevel_params966 (LENGTH ps))) val' ty')`
     (LABEL_TAC "Hv2_ex") THENL
   [ABBREV_TAC `dv = L4VDefVal971 n ci val'` THEN
    SUBGOAL_THEN `l4_vdefeq_wf966 venv1 (l4_vdv_to_defeq971 dv)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_vdef_val_to_defeq_wf971 THEN EXPAND_TAC "dv" THEN
     ASM_REWRITE_TAC [l4_vdv_name971;l4_vdv_const971;l4_vdef_val_wf971;l4_vdv_uvars971;
                      l4_vdv_type971;l4_vdv_value971];
     ALL_TAC] THEN
    EXISTS_TAC `l4_venv_add_defeq971 venv1 (l4_vdv_to_defeq971 dv)` THEN
    SUBGOAL_THEN `l4_venv_wf966 (l4_venv_add_defeq971 venv1 (l4_vdv_to_defeq971 dv)) /\
                  l4_venv_ordered961 venv1 (l4_venv_add_defeq971 venv1 (l4_vdv_to_defeq971 dv))`
      STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC l4_venv_add_defeq_wf971 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_venv_ordered_trans961 THEN EXISTS_TAC `venv1:l4_venv961` THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [l4_venv_add_defeq_lookup971];
     REWRITE_TAC [l4_venv_names_aligned975;l4_venv_contains971;l4_venv_add_defeq_lookup971] THEN
     USE_THEN "Halign1" (ACCEPT_TAC o REWRITE_RULE [l4_venv_names_aligned975;l4_venv_contains971]);
     MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv1:l4_venv961` THEN
     ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`venv1:l4_venv961`;`l4_vdv_to_defeq971 dv`] l4_venv_add_defeq_self971) THEN
     EXPAND_TAC "dv" THEN
     ASM_REWRITE_TAC [l4_vdv_to_defeq971;l4_vdv_uvars971;l4_vdv_name971;l4_vdv_const971;
                      l4_vdv_value971;l4_vdv_type971]];
    ALL_TAC] THEN
   l4_subst_cases_tac974 (SPEC `kind:l4_kdecl_kind493` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975] THEN
   TRY (MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`venv1:l4_venv961`] THEN
        ASM_REWRITE_TAC [l4_vis_type961] THEN REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
         MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
         EXISTS_TAC `u':l4_vlevel961` THEN
         MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN
         ASM_REWRITE_TAC [];
         EXISTS_TAC `val':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
          MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
          GEN_TAC THEN MATCH_MP_TAC l4_venv_add_const_has_defeq971 THEN
          MAP_EVERY EXISTS_TAC [`n:l4_name`;`ci:l4_vconstant961`] THEN ASM_REWRITE_TAC []]] THEN NO_TAC) THEN
   (REMOVE_THEN "Hv2_ex" (X_CHOOSE_THEN `venv2:l4_venv961` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`venv2:l4_venv961`] THEN
    ASM_REWRITE_TAC [l4_vis_type961] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
     EXISTS_TAC `u':l4_vlevel961` THEN
     MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN
     ASM_REWRITE_TAC [];
     EXISTS_TAC `val':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC []])]);;

let l4_admit620_sound975 = prove
 (`!fuel env venv input next.
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_admit620 fuel env input = L4KAccept491 next ==>
   ?d ci venv'.
     next = CONS d env /\
     l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
     l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d) /\
     l4_vtr_expr973 next venv' (l4_kdecl_params493 d) l4_vl_empty973 (l4_kdecl_type493 d) (l4_vc_type961 ci) /\
     l4_vis_type961 venv' (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) /\
     l4_vclosedN961 (l4_vc_type961 ci) 0 /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     l4_venv_lookup_const961 venv' (l4_kdecl_name493 d) ci /\
     l4_venv_names_aligned975 next venv' /\
     (match (l4_kdecl_kind493 d, l4_kdecl_value493 d) with
      | (L4KDDefinition493, SOME val_e) ->
          ?val'.
            l4_vtr_expr973 next venv' (l4_kdecl_params493 d) l4_vl_empty973 val_e val' /\
            l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] val' (l4_vc_type961 ci) /\
            l4_vclosedN961 val' 0 /\
            l4_venv_has_defeq961 venv'
              (L4VDefEq961 (l4_vc_uvars961 ci)
                (L4VConst961 (l4_kdecl_name493 d) (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                val' (l4_vc_type961 ci))
      | (L4KDTheorem493, SOME val_e) ->
          ?val'.
            l4_vtr_expr973 next venv' (l4_kdecl_params493 d) l4_vl_empty973 val_e val' /\
            l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] val' (l4_vc_type961 ci) /\
            l4_vclosedN961 val' 0 /\
            l4_venv_has_defeq961 venv'
              (L4VDefEq961 (l4_vc_uvars961 ci)
                (L4VConst961 (l4_kdecl_name493 d) (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                val' (l4_vc_type961 ci)) /\
            l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) (L4VSort961 L4VLZero961)
      | (L4KDPrimitive493 p, SOME val_e) ->
          ?val'.
            l4_vtr_expr973 next venv' (l4_kdecl_params493 d) l4_vl_empty973 val_e val' /\
            l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] val' (l4_vc_type961 ci) /\
            l4_vclosedN961 val' 0 /\
            l4_venv_has_defeq961 venv'
              (L4VDefEq961 (l4_vc_uvars961 ci)
                (L4VConst961 (l4_kdecl_name493 d) (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                val' (l4_vc_type961 ci))
      | _ -> T)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Halign") MP_TAC)) THEN
  SUBGOAL_THEN `l4_venv_wf966 venv /\ l4_venv_closed966 venv /\ l4_defeq_injectivity972 venv`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_ves_wf973;l4_venv_wf_closed966;l4_ves_inj973]; ALL_TAC] THEN
  REWRITE_TAC [l4_admit620;l4_admit_basic607] THEN
  l4_subst_cases_tac974 (SPEC `input:l4_input_decl607` (cases "l4_input_decl607")) THEN
  REWRITE_TAC [l4_env_dis975] THENL
  [(* InputAxiom *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `a0:l4_name`;`a1:l4_name list`;`a2:l4_kexpr447`;
                  `NONE:(l4_kexpr447)option`;`L4KDAssumption493`;`next:l4_kdeclaration493 list`]
     l4_checked_constant_sound_aligned975) THEN
   ASM_REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hnext") (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `venv':l4_venv961` STRIP_ASSUME_TAC)))) THEN
   REMOVE_THEN "Hnext" SUBST_ALL_TAC THEN
   MAP_EVERY EXISTS_TAC
     [`L4KDeclaration493 a0 a1 a2 NONE L4KDAssumption493 L4KHintOpaque493`;
      `ci:l4_vconstant961`;`venv':l4_venv961`] THEN
   ASM_REWRITE_TAC [l4_kdecl_name493;l4_kdecl_params493;l4_kdecl_type493;
                    l4_kdecl_value493;l4_kdecl_kind493;l4_env_dis975];
   (* InputDefinition *)
   l4_subst_cases_tac974 (SPEC `a5:l4_input_safety607` (cases "l4_input_safety607")) THEN
   REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hhdr")
     (X_CHOOSE_THEN `u2:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hsc")
       (X_CHOOSE_THEN `u3:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hchk")
         (X_CHOOSE_THEN `prim:(l4_kprimitive493)option` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))))) THEN
   REWRITE_TAC [LET_DEF;LET_END_DEF;l4_env_dis975] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
   REMOVE_THEN "Hhdr" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u1:1` one) THEN DISCH_TAC THEN
   REMOVE_THEN "Hchk" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u3:1` one) THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `a1:l4_name`;`a2:l4_name list`;`a3:l4_kexpr447`] l4_check_header_sound975) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hfresh")
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `ty':l4_vexpr961` (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC))))) THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`a2:l4_name list`;
                  `l4_kempty_context532`;`l4_vl_empty973`;`a4:l4_kexpr447`;`a3:l4_kexpr447`]
     l4_check_full_sound974) THEN
   ASM_REWRITE_TAC [l4_vtr_ctx_empty975;l4_vl_ctx_empty975] THEN
   DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` (X_CHOOSE_THEN `ty2':l4_vexpr961`
     (X_CHOOSE_THEN `u2':l4_vlevel961` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (a2:l4_name list)) [] ty2' ty'` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`a2:l4_name list`;
                   `l4_vl_empty973`;`a3:l4_kexpr447`;`ty2':l4_vexpr961`;`ty':l4_vexpr961`]
      l4_vtr_expr_uniq973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_empty975;l4_vl_ctx_wf_empty973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (a2:l4_name list)) [] val' ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vhas_type_conv_u974 THEN EXISTS_TAC `ty2':l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vclosedN961 val' 0` ASSUME_TAC THENL
   [MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (a2:l4_name list)`;`[]:l4_vexpr961 list`;
                   `val':l4_vexpr961`;`val':l4_vexpr961`;`ty':l4_vexpr961`] l4_vis_defeq_closedN966) THEN
    ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vctx_closed966;LENGTH] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `~l4_venv_contains971 venv a1` ASSUME_TAC THENL
   [USE_THEN "Halign" (MATCH_MP_TAC o REWRITE_RULE [l4_venv_names_aligned975]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   ABBREV_TAC `ci = L4VConstant961 (LENGTH (a2:l4_name list)) ty'` THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`a1:l4_name`;`ci:l4_vconstant961`] l4_venv_add_const_eq_none971) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `venv1:l4_venv961`) THEN
   SUBGOAL_THEN `l4_venv_wf966 venv1 /\ l4_venv_ordered961 venv venv1 /\
                 l4_venv_lookup_const961 venv1 a1 ci` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_add_const_self971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv1 (LENGTH (a2:l4_name list)) [] val' ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vclosedN961 ty' 0` ASSUME_TAC THENL
   [UNDISCH_TAC `l4_vconstant_wf966 venv ci` THEN EXPAND_TAC "ci" THEN
    REWRITE_TAC [l4_vconstant_wf966;l4_vc_type961] THEN MESON_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vc_uvars961 ci = LENGTH (a2:l4_name list) /\ l4_vc_type961 ci = ty'`
     STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ci" THEN REWRITE_TAC [l4_vc_uvars961;l4_vc_type961]; ALL_TAC] THEN
   ABBREV_TAC `dv = L4VDefVal971 a1 ci val'` THEN
   ABBREV_TAC `venv2 = l4_venv_add_defeq971 venv1 (l4_vdv_to_defeq971 dv)` THEN
   SUBGOAL_THEN `l4_vdefeq_wf966 venv1 (l4_vdv_to_defeq971 dv)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vdef_val_to_defeq_wf971 THEN EXPAND_TAC "dv" THEN
    ASM_REWRITE_TAC [l4_vdv_name971;l4_vdv_const971;l4_vdef_val_wf971;l4_vdv_uvars971;
                     l4_vdv_type971;l4_vdv_value971];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 venv2 /\ l4_venv_ordered961 venv1 venv2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "venv2" THEN MATCH_MP_TAC l4_venv_add_defeq_wf971 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_ordered961 venv venv2` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_venv_ordered_trans961 THEN EXISTS_TAC `venv1:l4_venv961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ABBREV_TAC `knd = (match prim with SOME op -> L4KDPrimitive493 op | NONE -> L4KDDefinition493)` THEN
   ABBREV_TAC `d = L4KDeclaration493 a1 a2 a3 (SOME a4) knd a0` THEN
   SUBGOAL_THEN `l4_env_extends975 env (CONS d env)` (LABEL_TAC "Hext") THENL
   [MATCH_MP_TAC l4_env_extends_cons_fresh975 THEN EXPAND_TAC "d" THEN ASM_REWRITE_TAC [l4_kdecl_name493];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`d:l4_kdeclaration493`;`ci:l4_vconstant961`;`venv2:l4_venv961`] THEN
   SUBGOAL_THEN `l4_kdecl_name493 d = a1 /\ l4_kdecl_params493 d = a2 /\
                 l4_kdecl_type493 d = a3 /\ l4_kdecl_value493 d = SOME a4 /\
                 l4_kdecl_kind493 d = knd`
     (fun th -> REWRITE_TAC [th]) THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC [l4_kdecl_name493;l4_kdecl_params493;l4_kdecl_type493;
                                     l4_kdecl_value493;l4_kdecl_kind493];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [l4_vis_type961] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
    MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
    EXISTS_TAC `u':l4_vlevel961` THEN
    MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv:l4_venv961` THEN
    ASM_REWRITE_TAC [];
    EXPAND_TAC "venv2" THEN ASM_REWRITE_TAC [l4_venv_add_defeq_lookup971];
    REWRITE_TAC [l4_venv_names_aligned975;l4_kfind_decl493;l4_venv_contains971] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC [l4_kdecl_name493] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
    DISCH_THEN (X_CHOOSE_TAC `c0:l4_vconstant961`) THEN
    UNDISCH_TAC `l4_venv_lookup_const961 venv2 n c0` THEN
    EXPAND_TAC "venv2" THEN REWRITE_TAC [l4_venv_add_defeq_lookup971] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`venv:l4_venv961`;`a1:l4_name`;`ci:l4_vconstant961`;`venv1:l4_venv961`;
                   `n:l4_name`;`c0:l4_vconstant961`] l4_venv_add_const_lookup971) THEN
    ASM_REWRITE_TAC [] THEN
    USE_THEN "Halign" (MP_TAC o SPEC `n:l4_name` o REWRITE_RULE [l4_venv_names_aligned975;l4_venv_contains971]) THEN
    ASM_MESON_TAC [];
    EXPAND_TAC "knd" THEN
    l4_subst_cases_tac974 (ISPEC `prim:(l4_kprimitive493)option` (cases "option")) THEN
    (REWRITE_TAC [l4_env_dis975] THEN EXISTS_TAC `val':l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
      MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN EXISTS_TAC `venv1:l4_venv961` THEN
      ASM_REWRITE_TAC [];
      EXPAND_TAC "venv2" THEN
      MP_TAC (SPECL [`venv1:l4_venv961`;`l4_vdv_to_defeq971 dv`] l4_venv_add_defeq_self971) THEN
      EXPAND_TAC "dv" THEN
      ASM_REWRITE_TAC [l4_vdv_to_defeq971;l4_vdv_uvars971;l4_vdv_name971;l4_vdv_const971;
                       l4_vdv_value971;l4_vdv_type971]])];
   (* InputTheorem *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `u2:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hprop") ASSUME_TAC)))) THEN
   REMOVE_THEN "Hprop" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u2:1` one) THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `a0:l4_name`;`a1:l4_name list`;`a2:l4_kexpr447`;
                  `SOME (a3:l4_kexpr447)`;`L4KDTheorem493`;`next:l4_kdeclaration493 list`]
     l4_checked_constant_sound_aligned975) THEN
   ASM_REWRITE_TAC [LET_DEF;LET_END_DEF;l4_env_dis975] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hnext") (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `venv':l4_venv961` STRIP_ASSUME_TAC)))) THEN
   REMOVE_THEN "Hnext" SUBST_ALL_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `a1:l4_name list`;`a2:l4_kexpr447`] l4_check_proposition_sound975) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `typ':l4_vexpr961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_vis_defeq_u961 venv (LENGTH (a1:l4_name list)) [] typ' (l4_vc_type961 ci)` ASSUME_TAC THENL
   [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`a1:l4_name list`;
                   `l4_vl_empty973`;`a2:l4_kexpr447`;`typ':l4_vexpr961`;`l4_vc_type961 ci`]
      l4_vtr_expr_uniq973) THEN
    ASM_REWRITE_TAC [l4_vl_ctx_empty975;l4_vl_ctx_wf_empty973];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv (LENGTH (a1:l4_name list)) [] (l4_vc_type961 ci) (L4VSort961 L4VLZero961)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vis_defeq_u_has_type_right974 THEN EXISTS_TAC `typ':l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_vctx_wf966];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vhas_type961 venv' (l4_vc_uvars961 ci) [] (l4_vc_type961 ci) (L4VSort961 L4VLZero961)`
     ASSUME_TAC THENL
   [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_venv_ordered_preserve_vhas_type961 THEN
    EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC
     [`L4KDeclaration493 a0 a1 a2 (SOME a3) L4KDTheorem493 L4KHintOpaque493`;
      `ci:l4_vconstant961`;`venv':l4_venv961`] THEN
   REWRITE_TAC [l4_kdecl_name493;l4_kdecl_params493;l4_kdecl_type493;
                l4_kdecl_value493;l4_kdecl_kind493;l4_env_dis975] THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
   EXISTS_TAC `val':l4_vexpr961` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   (* InputOpaque *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `a0:l4_name`;`a1:l4_name list`;`a2:l4_kexpr447`;
                  `SOME (a3:l4_kexpr447)`;`L4KDOpaque493`;`next:l4_kdeclaration493 list`]
     l4_checked_constant_sound_aligned975) THEN
   ASM_REWRITE_TAC [LET_DEF;LET_END_DEF] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hnext") (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `venv':l4_venv961` STRIP_ASSUME_TAC)))) THEN
   REMOVE_THEN "Hnext" SUBST_ALL_TAC THEN
   MAP_EVERY EXISTS_TAC
     [`L4KDeclaration493 a0 a1 a2 (SOME a3) L4KDOpaque493 L4KHintOpaque493`;
      `ci:l4_vconstant961`;`venv':l4_venv961`] THEN
   ASM_REWRITE_TAC [l4_kdecl_name493;l4_kdecl_params493;l4_kdecl_type493;
                    l4_kdecl_value493;l4_kdecl_kind493;l4_env_dis975]]);;

(* Pure-constant environments *)
let l4_pure_const_env975 = new_definition
 `l4_pure_const_env975 env <=>
   !n d. l4_kfind_decl493 env n = SOME d ==>
     (match l4_kdecl_kind493 d with
      | L4KDAssumption493 -> T
      | L4KDDefinition493 -> T
      | L4KDTheorem493 -> T
      | L4KDOpaque493 -> T
      | L4KDUnsupported493 -> T
      | L4KDUnsafe493 r -> T
      | L4KDPartial493 -> T
      | _ -> F)`;;

let l4_pure_const_env_empty975 = prove
 (`l4_pure_const_env975 []`,
  REWRITE_TAC [l4_pure_const_env975;l4_kfind_decl493;l4_env_dis975]);;

let l4_pure_const_env_no_ind975 = prove
 (`!env owner. l4_pure_const_env975 env ==> l4_core_inductive532 env owner = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_pure_const_env975;l4_core_inductive532] THEN
  DISCH_THEN (MP_TAC o SPEC `owner:l4_name`) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env owner` `a:l4_kdeclaration493` THEN
  DISCH_THEN (MP_TAC o SPEC `a:l4_kdeclaration493`) THEN REWRITE_TAC [] THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975]);;

let l4_pure_const_env_no_ctor975 = prove
 (`!env cn. l4_pure_const_env975 env ==> l4_core_constructor532 env cn = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_pure_const_env975;l4_core_constructor532] THEN
  DISCH_THEN (MP_TAC o SPEC `cn:l4_name`) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env cn` `a:l4_kdeclaration493` THEN
  DISCH_THEN (MP_TAC o SPEC `a:l4_kdeclaration493`) THEN REWRITE_TAC [] THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975]);;

let l4_pure_const_env_prims975 = prove
 (`!env venv. l4_pure_const_env975 env ==> l4_has_primitives973 env venv`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~l4_core_nat_ready533 env /\ ~l4_core_bool_ready533 env /\ ~l4_core_string_ready533 env`
    (fun th -> REWRITE_TAC [l4_has_primitives973;th]) THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [l4_core_nat_ready533] THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_nat_name533` `a:l4_kdeclaration493` THEN
   FIRST_ASSUM (MP_TAC o SPECL [`l4_core_nat_name533`;`a:l4_kdeclaration493`] o
                REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975];
   REWRITE_TAC [l4_core_bool_ready533] THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_bool_name533` `a:l4_kdeclaration493` THEN
   FIRST_ASSUM (MP_TAC o SPECL [`l4_core_bool_name533`;`a:l4_kdeclaration493`] o
                REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975];
   REWRITE_TAC [l4_core_string_ready533] THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_char_of_nat533` `a:l4_kdeclaration493` THEN
   l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_string_of_list533` `a':l4_kdeclaration493` THEN
   FIRST_ASSUM (MP_TAC o SPECL [`l4_core_char_of_nat533`;`a:l4_kdeclaration493`] o
                REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975]]);;

let l4_venv_sound_pure_admit975 = prove
 (`!fuel env venv input next.
   l4_pure_const_env975 env /\
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_admit620 fuel env input = L4KAccept491 next /\
   (!hints n ps ty body.
     input = L4InputDefinition607 hints n ps ty body L4InputSafe607 ==>
     l4_classify_primitive620 fuel env n ps ty body = L4KAccept491 NONE) ==>
   ?venv'.
     l4_pure_const_env975 next /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     l4_venv_names_aligned975 next venv' /\
     (l4_defeq_injectivity972 venv' ==> l4_venv_sound973 next venv')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hpure")
    (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
      (CONJUNCTS_THEN2 (LABEL_TAC "Halign")
        (CONJUNCTS_THEN2 (LABEL_TAC "Hadm") (LABEL_TAC "Hnoprim"))))) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                 `input:l4_input_decl607`;`next:l4_kdeclaration493 list`] l4_admit620_sound975) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `d:l4_kdeclaration493` (X_CHOOSE_THEN `ci:l4_vconstant961`
    (X_CHOOSE_THEN `venv':l4_venv961` (CONJUNCTS_THEN2 (LABEL_TAC "Hnext")
      (CONJUNCTS_THEN2 (LABEL_TAC "Hfresh")
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 ASSUME_TAC
                (CONJUNCTS_THEN2 (LABEL_TAC "Hord")
                  (CONJUNCTS_THEN2 (LABEL_TAC "Hwf'")
                    (CONJUNCTS_THEN2 ASSUME_TAC
                      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hval")))))))))))))) THEN
  REMOVE_THEN "Hnext" SUBST_ALL_TAC THEN
  SUBGOAL_THEN
    `match l4_kdecl_kind493 d with
     | L4KDAssumption493 -> T
     | L4KDDefinition493 -> T
     | L4KDTheorem493 -> T
     | L4KDOpaque493 -> T
     | L4KDUnsupported493 -> T
     | L4KDUnsafe493 r -> T
     | L4KDPartial493 -> T
     | _ -> F` (LABEL_TAC "Hdk_pure") THENL
  [REMOVE_THEN "Hadm" MP_TAC THEN REWRITE_TAC [l4_admit620;l4_admit_basic607;l4_checked_constant607] THEN
   l4_subst_cases_tac974 (SPEC `input:l4_input_decl607` (cases "l4_input_decl607")) THEN
   REWRITE_TAC [l4_env_dis975] THENL
   [(* Axiom *)
    COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_kdecl_kind493;l4_env_dis975];
    (* Definition *)
    l4_subst_cases_tac974 (SPEC `a5:l4_input_safety607` (cases "l4_input_safety607")) THEN
    REWRITE_TAC [l4_env_dis975] THEN
    SUBGOAL_THEN `l4_classify_primitive620 fuel env a1 a2 a3 a4 = L4KAccept491 NONE`
      (fun th -> REWRITE_TAC [th;l4_kr_bind491;l4_kr_bind_accept967;l4_env_dis975;LET_DEF;LET_END_DEF]) THENL
    [USE_THEN "Hnoprim" (fun th -> MATCH_MP_TAC th THEN MESON_TAC []); ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_kdecl_kind493;l4_env_dis975];
    (* Theorem *)
    COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_kdecl_kind493;l4_env_dis975];
    (* Opaque *)
    COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
    COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [l4_kdecl_kind493;l4_env_dis975]];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_pure_const_env975 (CONS d env)` (LABEL_TAC "Hpure'") THENL
  [REWRITE_TAC [l4_pure_const_env975;l4_kfind_decl493] THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_pure_const_env975]];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_env_extends975 env (CONS d env)` (LABEL_TAC "Hext") THENL
  [MATCH_MP_TAC l4_env_extends_cons_fresh975 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  EXISTS_TAC `venv':l4_venv961` THEN ASM_REWRITE_TAC [] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(!owner. l4_core_inductive532 (CONS d env) owner = NONE) /\
                (!cn. l4_core_constructor532 (CONS d env) cn = NONE)` (LABEL_TAC "Hno_ic") THENL
  [ASM_MESON_TAC [l4_pure_const_env_no_ind975;l4_pure_const_env_no_ctor975]; ALL_TAC] THEN
  REWRITE_TAC [l4_venv_sound973;l4_vind_head_inj973] THEN
  ASM_REWRITE_TAC [l4_env_dis975] THEN
  REPEAT CONJ_TAC THENL
  [(* HasPrimitives *)
   MATCH_MP_TAC l4_pure_const_env_prims975 THEN ASM_REWRITE_TAC [];
   (* ves_constants *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_kfind_decl493] THEN COND_CASES_TAC THEN
   REWRITE_TAC [l4_env_dis975] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975] THEN EXISTS_TAC `ci:l4_vconstant961` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_constants973) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`]) THEN
    ASM_REWRITE_TAC [] THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d'` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975] THEN
    (DISCH_THEN (X_CHOOSE_THEN `ci0:l4_vconstant961` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `ci0:l4_vconstant961` THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
      MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
      MATCH_MP_TAC l4_venv_ordered_preserve_vis_type966 THEN EXISTS_TAC `venv:l4_venv961` THEN
      ASM_REWRITE_TAC []])];
   (* ves_delta *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_kfind_decl493] THEN COND_CASES_TAC THEN
   REWRITE_TAC [l4_env_dis975] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hdd") (CONJUNCTS_THEN2 (LABEL_TAC "Hkind") (LABEL_TAC "Hve"))) THEN
    REMOVE_THEN "Hdd" (SUBST_ALL_TAC o SYM) THEN
    REMOVE_THEN "Hkind" (DISJ_CASES_THEN2 (LABEL_TAC "Hk")
      (DISJ_CASES_THEN2 (LABEL_TAC "Hk") (X_CHOOSE_THEN `p:l4_kprimitive493` (LABEL_TAC "Hk")))) THEN
    (USE_THEN "Hk" (fun hk -> USE_THEN "Hve" (fun hv ->
       REMOVE_THEN "Hval" (MP_TAC o REWRITE_RULE [hk;hv;l4_env_dis975]))) THEN
     DISCH_THEN (X_CHOOSE_THEN `val':l4_vexpr961` STRIP_ASSUME_TAC) THEN
     MP_TAC (REWRITE_RULE [l4_vdf_uvars961;l4_vdf_lhs961;l4_vdf_rhs961;l4_vdf_type961]
       (SPECL [`venv':l4_venv961`;
               `L4VDefEq961 (l4_vc_uvars961 ci)
                  (L4VConst961 (l4_kdecl_name493 d) (l4_vlevel_params966 (l4_vc_uvars961 ci)))
                  val' (l4_vc_type961 ci)`] l4_vis_defeq_extra0966)) THEN
     ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
     MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`val':l4_vexpr961`] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] l4_ves_delta973) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`;`val_e:l4_kexpr447`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `ci0:l4_vconstant961` (X_CHOOSE_THEN `val':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ci0:l4_vconstant961`;`val':l4_vexpr961`] THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
    [MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`venv:l4_venv961`;`l4_vc_uvars961 ci0`;`[]:l4_vexpr961 list`;
                    `L4VConst961 n (l4_vlevel_params966 (l4_vc_uvars961 ci0))`;
                    `val':l4_vexpr961`;`l4_vc_type961 ci0`] l4_venv_ordered_preserve_vis_defeq961) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]];
   (* ves_quot_red *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hpure'" (MP_TAC o SPECL [`cn:l4_name`;`cd:l4_kdeclaration493`] o REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [l4_env_dis975];
   (* ves_recursor_rhs *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hpure'" (MP_TAC o SPECL [`rname:l4_name`;`d':l4_kdeclaration493`] o REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [l4_env_dis975];
   (* ves_ind_shape *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hpure'" (MP_TAC o SPECL [`own:l4_name`;`d_ind:l4_kdeclaration493`] o REWRITE_RULE [l4_pure_const_env975]) THEN
   ASM_REWRITE_TAC [l4_env_dis975]]);;

(* ========================================================================= *)
(* 5. Safety Isolation (`safety_admission624.ml` & `inductive_safety633.ml`) *)
(* ========================================================================= *)

let l4_is_restricted_kind975 = new_definition
 `l4_is_restricted_kind975 k <=>
   match k with
   | L4KDUnsafe493 r -> T
   | L4KDPartial493 -> T
   | _ -> F`;;

let l4_kfind_decl_cons_restricted_ind975 = prove
 (`!env d owner.
   l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
   l4_is_restricted_kind975 (l4_kdecl_kind493 d) ==>
   l4_core_inductive532 (CONS d env) owner = l4_core_inductive532 env owner`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_inductive532;l4_kfind_decl493;l4_is_restricted_kind975] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `match l4_kdecl_kind493 d with L4KDUnsafe493 r -> T | L4KDPartial493 -> T | _ -> F` THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975]);;

let l4_kfind_decl_cons_restricted_ctor975 = prove
 (`!env d cn.
   l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
   l4_is_restricted_kind975 (l4_kdecl_kind493 d) ==>
   l4_core_constructor532 (CONS d env) cn = l4_core_constructor532 env cn`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_constructor532;l4_kfind_decl493;l4_is_restricted_kind975] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `match l4_kdecl_kind493 d with L4KDUnsafe493 r -> T | L4KDPartial493 -> T | _ -> F` THEN
  l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975]);;

let l4_venv_sound_prepend_restricted975 = prove
 (`!env venv d.
   l4_venv_sound973 env venv /\
   l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
   l4_is_restricted_kind975 (l4_kdecl_kind493 d) ==>
   l4_venv_sound973 (CONS d env) venv`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
    (CONJUNCTS_THEN2 (LABEL_TAC "Hfresh") (LABEL_TAC "Hres"))) THEN
  SUBGOAL_THEN `l4_env_extends975 env (CONS d env)` (LABEL_TAC "Hext") THENL
  [MATCH_MP_TAC l4_env_extends_cons_fresh975 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `!owner. l4_core_inductive532 (CONS d env) owner = l4_core_inductive532 env owner`
    (LABEL_TAC "Hind_eq") THENL
  [GEN_TAC THEN MATCH_MP_TAC l4_kfind_decl_cons_restricted_ind975 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `!cn. l4_core_constructor532 (CONS d env) cn = l4_core_constructor532 env cn`
    (LABEL_TAC "Hctor_eq") THENL
  [GEN_TAC THEN MATCH_MP_TAC l4_kfind_decl_cons_restricted_ctor975 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `!n p i f ty. l4_core_ctor_shape533 (CONS d env) n p i f ty <=>
                             l4_core_ctor_shape533 env n p i f ty` (LABEL_TAC "Hcs_eq") THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_ctor_shape533;l4_kfind_decl493] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
   USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_nat_ready533 (CONS d env) <=> l4_core_nat_ready533 env` (LABEL_TAC "Hnat_eq") THENL
  [REWRITE_TAC [l4_core_nat_ready533;l4_kfind_decl493] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975];
    l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_nat_name533` `d0:l4_kdeclaration493` THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d0` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975] THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_bool_ready533 (CONS d env) <=> l4_core_bool_ready533 env` (LABEL_TAC "Hbool_eq") THENL
  [REWRITE_TAC [l4_core_bool_ready533;l4_kfind_decl493] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975];
    l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_bool_name533` `d0:l4_kdeclaration493` THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d0` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975] THEN ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_core_string_ready533 (CONS d env) <=> l4_core_string_ready533 env` (LABEL_TAC "Hstr_eq") THENL
  [REWRITE_TAC [l4_core_string_ready533;l4_kfind_decl493] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
    l4_opt_cases_keep975
      `if l4_core_string_of_list533 = l4_kdecl_name493 d then SOME d
       else l4_kfind_decl493 env l4_core_string_of_list533` `ds:l4_kdeclaration493` THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975];
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_char_of_nat533` `dc:l4_kdeclaration493` THEN
     USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
     l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
     REWRITE_TAC [l4_env_dis975] THEN
     l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 dc` (cases "l4_kdecl_kind493")) THEN
     REWRITE_TAC [l4_env_dis975];
     l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_char_of_nat533` `dc:l4_kdeclaration493` THEN
     l4_opt_cases_keep975 `l4_kfind_decl493 env l4_core_string_of_list533` `ds:l4_kdeclaration493` THEN
     l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 dc` (cases "l4_kdecl_kind493")) THEN
     REWRITE_TAC [l4_env_dis975] THEN
     l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 ds` (cases "l4_kdecl_kind493")) THEN
     REWRITE_TAC [l4_env_dis975] THEN
     REPEAT (fun (asl,w) ->
       match find_terms (fun t -> is_var t && type_of t = `:l4_kprimitive493`) w with
       | v::_ -> (l4_subst_cases_tac974 (SPEC v (cases "l4_kprimitive493")) THEN
                  REWRITE_TAC [l4_env_dis975]) (asl,w)
       | [] -> FAIL_TAC "no prim" (asl,w)) THEN
     ASM_REWRITE_TAC []]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!owner. l4_core_structure532 (CONS d env) owner <=> l4_core_structure532 env owner`
    (LABEL_TAC "Hstruct_eq") THENL
  [GEN_TAC THEN ASM_REWRITE_TAC [l4_core_structure532]; ALL_TAC] THEN
  SUBGOAL_THEN `!n d0. l4_kfind_decl493 (CONS d env) n = SOME d0 /\
                       ~l4_is_restricted_kind975 (l4_kdecl_kind493 d0) ==>
                       l4_kfind_decl493 env n = SOME d0` (LABEL_TAC "Hfind_nonres") THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_kfind_decl493] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN ASM_MESON_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `!ps l e e'. l4_vtr_expr_s973 (CONS d env) venv ps l e e' ==>
                            l4_vtr_expr_s973 env venv ps l e e'` (LABEL_TAC "Htr_s_back") THENL
  [SUBGOAL_THEN `!env0 venv0 ps l e e'.
                  l4_vtr_expr_s973 env0 venv0 ps l e e' ==>
                  env0 = CONS d env /\ venv0 = venv ==>
                  l4_vtr_expr_s973 env venv ps l e e'`
     (fun th -> MESON_TAC [th]) THEN
   MATCH_MP_TAC l4_vtr_expr_s_INDUCT973 THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_bvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_fvar973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_sort973 THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_const973 THEN EXISTS_TAC `ci:l4_vconstant961` THEN ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_app973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_SIMP_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_lam973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_SIMP_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_pi973 THEN EXISTS_TAC `ty:l4_vexpr961` THEN ASM_SIMP_TAC [];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_let973 THEN
    MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`val':l4_vexpr961`] THEN ASM_SIMP_TAC [];
    (* Proj *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_expr_s_proj973 THEN
    MAP_EVERY EXISTS_TAC [`sv:l4_vexpr961`;`fty:l4_vexpr961`] THEN CONJ_TAC THENL
    [ASM_SIMP_TAC []; ALL_TAC] THEN
    FIRST_X_ASSUM (fun th -> if fst (strip_comb (concl th)) = `l4_vtr_proj973` then MP_TAC th else fail ()) THEN
    ASM_REWRITE_TAC [l4_vtr_proj973] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`info:l4_kinductive_data493`;`ctor:l4_name`;`c:l4_kconstructor_data493`;
       `d':l4_kdeclaration493`;`us:l4_vlevel961 list`;`params:l4_vexpr961 list`;
       `indices:l4_vexpr961 list`] THEN
    ASM_REWRITE_TAC [] THEN
    USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    (* NatLit *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_natlit973 THEN
    USE_THEN "Hnat_eq" (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h])) THEN ASM_REWRITE_TAC [];
    (* StrLit *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_strlit973 THEN
    USE_THEN "Hstr_eq" (fun h -> RULE_ASSUM_TAC (REWRITE_RULE [h])) THEN ASM_REWRITE_TAC [];
    (* MData *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC l4_vtr_expr_s_mdata973 THEN ASM_SIMP_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `!ps l e e'. l4_vtr_expr973 (CONS d env) venv ps l e e' ==>
                            l4_vtr_expr973 env venv ps l e e'` (LABEL_TAC "Htr_back") THENL
  [REWRITE_TAC [l4_vtr_expr973] THEN REPEAT STRIP_TAC THEN
   EXISTS_TAC `e0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
   USE_THEN "Htr_s_back" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!uvars g owner us ps0 sv mp skip idx ty fty.
                  l4_vproj_telescope973 (CONS d env) venv uvars g owner us ps0 sv mp skip idx ty fty ==>
                  l4_vproj_telescope973 env venv uvars g owner us ps0 sv mp skip idx ty fty`
    (LABEL_TAC "Hpt_back") THENL
  [SUBGOAL_THEN `!env0 venv0 uvars g owner us ps0 sv mp skip idx ty fty.
                  l4_vproj_telescope973 env0 venv0 uvars g owner us ps0 sv mp skip idx ty fty ==>
                  env0 = CONS d env /\ venv0 = venv ==>
                  l4_vproj_telescope973 env venv uvars g owner us ps0 sv mp skip idx ty fty`
     (fun th -> REPEAT STRIP_TAC THEN
                MP_TAC (SPECL [`CONS (d:l4_kdeclaration493) env`;`venv:l4_venv961`;`uvars:num`;
                               `g:l4_vexpr961 list`;`owner:l4_name`;`us:l4_vlevel961 list`;
                               `ps0:l4_vexpr961 list`;`sv:l4_vexpr961`;`mp:bool`;
                               `skip:num`;`idx:num`;`ty:l4_vexpr961`;`fty:l4_vexpr961`] th) THEN
                ASM_REWRITE_TAC []) THEN
   MATCH_MP_TAC l4_vproj_telescope_INDUCT973 THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
    MATCH_MP_TAC l4_vpt_zero973 THEN EXISTS_TAC `body:l4_vexpr961` THEN ASM_REWRITE_TAC [];
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
    MATCH_MP_TAC l4_vpt_succ973 THEN MAP_EVERY EXISTS_TAC [`dom:l4_vexpr961`;`body:l4_vexpr961`] THEN
    ASM_SIMP_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `!uvars g owner idx sv pv fty.
                  l4_vtr_proj973 env venv uvars g owner idx sv pv fty ==>
                  l4_vtr_proj973 (CONS d env) venv uvars g owner idx sv pv fty` (LABEL_TAC "Hproj_fwd") THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vtr_proj_extend_env975 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN
   ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   ALL_TAC] THEN
  REWRITE_TAC [l4_venv_sound973;l4_vind_head_inj973] THEN
  REPEAT CONJ_TAC THENL
  [(* 1. wf *)
   USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   (* 2. inj *)
   USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_inj973);
   (* 3. ind_inj *)
   ASM_REWRITE_TAC [] THEN
   USE_THEN "Hves" (ACCEPT_TAC o REWRITE_RULE [l4_vind_head_inj973] o MATCH_MP l4_ves_ind_inj973);
   (* 4. has_primitives *)
   REWRITE_TAC [l4_has_primitives973] THEN ASM_REWRITE_TAC [] THEN
   USE_THEN "Hves" (STRIP_ASSUME_TAC o REWRITE_RULE [l4_has_primitives973] o MATCH_MP l4_ves_prims973) THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`;`a:num`]) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
     DISCH_THEN ACCEPT_TAC];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`;`op:l4_kprimitive493`;
                                  `a:num`;`b:num`;`res:l4_vexpr961`;`rty:l4_vexpr961`]) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
     DISCH_THEN ACCEPT_TAC]];
   (* 5. ves_constants *)
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_kfind_decl493] THEN COND_CASES_TAC THEN
   REWRITE_TAC [l4_env_dis975] THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN
    USE_THEN "Hres" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975];
    DISCH_TAC THEN
    USE_THEN "Hves" (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`] o MATCH_MP l4_ves_constants973) THEN
    ASM_REWRITE_TAC [] THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d'` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975] THEN
    (DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `ci:l4_vconstant961` THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
     MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
     MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN
     ASM_REWRITE_TAC [l4_venv_ordered_refl961])];
   (* 6. ves_delta *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hf") (CONJUNCTS_THEN2 (LABEL_TAC "Hk") (LABEL_TAC "Hv"))) THEN
   SUBGOAL_THEN `l4_kfind_decl493 env n = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975] THEN
    USE_THEN "Hk" (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC [th;l4_env_dis975])
      (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC [th;l4_env_dis975])
        (X_CHOOSE_THEN `p:l4_kprimitive493` (fun th -> REWRITE_TAC [th;l4_env_dis975]))));
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`n:l4_name`;`d':l4_kdeclaration493`;`val_e:l4_kexpr447`] o
                    MATCH_MP l4_ves_delta973) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` (X_CHOOSE_THEN `val':l4_vexpr961` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`ci:l4_vconstant961`;`val':l4_vexpr961`] THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
   MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN
   ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   (* 7. ves_quot_red *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Hf")
     (CONJUNCTS_THEN2 (LABEL_TAC "Hk") (CONJUNCTS_THEN2 (LABEL_TAC "Hfc")
       (CONJUNCTS_THEN2 (LABEL_TAC "Hkc") (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
   SUBGOAL_THEN `l4_kfind_decl493 env n = SOME d' /\ l4_kfind_decl493 env cn = SOME cd` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975] THEN
    USE_THEN "Hk" (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC [CONJUNCT1 th;l4_env_dis975])
      (fun th -> REWRITE_TAC [CONJUNCT1 th;l4_env_dis975]));
    ALL_TAC] THEN
   USE_THEN "Hves" (MATCH_MP_TAC o MATCH_MP l4_ves_quot_red973) THEN
   MAP_EVERY EXISTS_TAC [`d':l4_kdeclaration493`;`cn:l4_name`;`cd:l4_kdeclaration493`;
                         `cus:l4_vlevel961 list`;`a1:l4_vexpr961`;`a2:l4_vexpr961`] THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   (* 8. ves_recursor_iota *)
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Hf")
     (CONJUNCTS_THEN2 (LABEL_TAC "Hk") STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `l4_kfind_decl493 env rname = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_vtr_expr973 env venv (l4_kdecl_params493 d') l4_vl_empty973 (l4_krule_rhs493 rule) rhs_v`
     ASSUME_TAC THENL
   [USE_THEN "Htr_back" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`g:l4_vexpr961 list`;`rname:l4_name`;`d':l4_kdeclaration493`;
      `info:l4_krecursor_data493`;`rus:l4_vlevel961 list`;`args:l4_vexpr961 list`;
      `maj:l4_vexpr961`;`own:l4_name`;`cn:l4_name`;`ci:l4_kconstructor_data493`;
      `cus:l4_vlevel961 list`;`fs:l4_vexpr961 list`;`rule:l4_krecursor_rule493`;
      `rhs_v:l4_vexpr961`] o MATCH_MP l4_ves_recursor_iota973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hctor_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN
      TRY (FIRST_ASSUM ACCEPT_TAC) THEN EXISTS_TAC `ty:l4_vexpr961` THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 9. ves_recursor_rhs *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env rname = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`rname:l4_name`;`d':l4_kdeclaration493`;`info:l4_krecursor_data493`;
                                    `rule:l4_krecursor_rule493`] o MATCH_MP l4_ves_recursor_rhs973) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_TAC `rhs_v:l4_vexpr961`) THEN EXISTS_TAC `rhs_v:l4_vexpr961` THEN
   MATCH_MP_TAC l4_vtr_expr_extend_env975 THEN
   MAP_EVERY EXISTS_TAC [`env:l4_kdeclaration493 list`;`venv:l4_venv961`] THEN
   ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   (* 10. ves_recursor_k_fields *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env rname = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`rname:l4_name`;`d':l4_kdeclaration493`;`info:l4_krecursor_data493`;
                                    `own:l4_name`;`oinfo:l4_kinductive_data493`;`ctor:l4_name`;
                                    `ci:l4_kconstructor_data493`] o MATCH_MP l4_ves_recursor_k_fields973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h1 -> USE_THEN "Hctor_eq" (fun h2 ->
      REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h1;GSYM h2] THEN FIRST_ASSUM ACCEPT_TAC));
    DISCH_THEN ACCEPT_TAC];
   (* 11. ves_proj_const *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env ctor = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`own:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
                                    `c:l4_kconstructor_data493`;`d':l4_kdeclaration493`;`idx:num`] o
                    MATCH_MP l4_ves_proj_const973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 12. ves_proj_iota *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env ctor = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`g:l4_vexpr961 list`;`own:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
      `c:l4_kconstructor_data493`;`d':l4_kdeclaration493`;`idx:num`;`us:l4_vlevel961 list`;
      `cus:l4_vlevel961 list`;`params:l4_vexpr961 list`;`idxs:l4_vexpr961 list`;
      `fields:l4_vexpr961 list`;`fval:l4_vexpr961`;`sv:l4_vexpr961`] o MATCH_MP l4_ves_proj_iota973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN
      TRY (FIRST_ASSUM ACCEPT_TAC) THEN EXISTS_TAC `fty:l4_vexpr961` THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 13. ves_proj_telescope *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env ctor = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`g:l4_vexpr961 list`;`own:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
      `c:l4_kconstructor_data493`;`d':l4_kdeclaration493`;`ci_c:l4_vconstant961`;`idx:num`;
      `us:l4_vlevel961 list`;`params:l4_vexpr961 list`;`idxs:l4_vexpr961 list`;
      `sv:l4_vexpr961`;`usort:l4_vlevel961`;`typ:l4_vexpr961`;`fty:l4_vexpr961`;`mp:bool`] o
     MATCH_MP l4_ves_proj_telescope973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN
      TRY (FIRST_ASSUM ACCEPT_TAC) THEN USE_THEN "Hpt_back" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 14. ves_struct_eta *)
   REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env ctor = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`g:l4_vexpr961 list`;`own:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
      `c:l4_kconstructor_data493`;`d':l4_kdeclaration493`;`us:l4_vlevel961 list`;
      `params:l4_vexpr961 list`;`sv:l4_vexpr961`] o MATCH_MP l4_ves_struct_eta973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h1 -> USE_THEN "Hstruct_eq" (fun h2 ->
      REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h1;GSYM h2] THEN FIRST_ASSUM ACCEPT_TAC));
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hps") ASSUME_TAC) THEN
    CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN
     USE_THEN "Hps" (MP_TAC o SPEC `i:num`) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_TAC `fty:l4_vexpr961`) THEN EXISTS_TAC `fty:l4_vexpr961` THEN
     USE_THEN "Hproj_fwd" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
     FIRST_ASSUM ACCEPT_TAC]];
   (* 15. ves_ctor_type_head *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`uvars:num`;`g:l4_vexpr961 list`;`cn:l4_name`;
                                    `ci:l4_kconstructor_data493`;`cus:l4_vlevel961 list`;
                                    `args:l4_vexpr961 list`;`t:l4_vexpr961`] o
                    MATCH_MP l4_ves_ctor_type_head973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hctor_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN FIRST_ASSUM ACCEPT_TAC);
    USE_THEN "Hind_eq" (fun h -> REWRITE_TAC [h])];
   (* 16. ves_ind_shape *)
   REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env own = SOME d_ind /\ l4_kfind_decl493 env ctor = SOME d_ctor`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`own:l4_name`;`info:l4_kinductive_data493`;`d_ind:l4_kdeclaration493`;
                                    `ctor:l4_name`;`c:l4_kconstructor_data493`;`d_ctor:l4_kdeclaration493`] o
                    MATCH_MP l4_ves_ind_shape973) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
   (* 17. ves_ind_type_arity *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hves" (MP_TAC o SPECL [`uvars:num`;`g:l4_vexpr961 list`;`own:l4_name`;
                                    `info:l4_kinductive_data493`;`us:l4_vlevel961 list`;
                                    `args:l4_vexpr961 list`;`usort:l4_vlevel961`] o
                    MATCH_MP l4_ves_ind_type_arity973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 18. ves_ctor_params_wf *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `l4_kfind_decl493 env ctor = SOME d'` ASSUME_TAC THENL
   [USE_THEN "Hfind_nonres" MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_is_restricted_kind975;l4_env_dis975];
    ALL_TAC] THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`g:l4_vexpr961 list`;`own:l4_name`;`info:l4_kinductive_data493`;`ctor:l4_name`;
      `c:l4_kconstructor_data493`;`d':l4_kdeclaration493`;`us:l4_vlevel961 list`;
      `params:l4_vexpr961 list`;`idxs:l4_vexpr961 list`;`t:l4_vexpr961`] o
     MATCH_MP l4_ves_ctor_params_wf973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC];
   (* 19. ves_ind_weakN *)
   REPEAT STRIP_TAC THEN
   USE_THEN "Hves" (MP_TAC o SPECL
     [`uvars:num`;`n:num`;`k:num`;`g:l4_vexpr961 list`;`g':l4_vexpr961 list`;`own:l4_name`;
      `info:l4_kinductive_data493`;`t0:l4_vexpr961`;`us:l4_vlevel961 list`;`args:l4_vexpr961 list`] o
     MATCH_MP l4_ves_ind_weakN973) THEN
   ANTS_TAC THENL
   [USE_THEN "Hind_eq" (fun h -> REPEAT CONJ_TAC THEN REWRITE_TAC [GSYM h] THEN FIRST_ASSUM ACCEPT_TAC);
    DISCH_THEN ACCEPT_TAC]]);;

let l4_kfind_decl_safety_env_none975 = prove
 (`!mode env n.
   l4_kfind_decl493 (l4_safety_environment624 mode env) n = NONE ==>
   l4_kfind_decl493 env n = NONE`,
  GEN_TAC THEN REWRITE_TAC [l4_safety_environment624] THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC [MAP;l4_kfind_decl493;l4_checking_view624;
               LET_DEF;LET_END_DEF;l4_kdecl_name493] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let l4_check_header_fresh975 = prove
 (`!fuel env n ps ty u.
   l4_check_header607 fuel env n ps ty = L4KAccept491 u ==>
   l4_kfind_decl493 env n = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_header607] THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env n` `d0:l4_kdeclaration493`);;

let l4_admit_extended_restricted_sound975 = prove
 (`!fuel env venv input next.
   l4_venv_sound973 env venv /\
   (match input with
    | L4InputAxiom607 n ps ty T -> T
    | L4InputDefinition607 hints n ps ty val_e L4InputUnsafe607 -> T
    | L4InputDefinition607 hints n ps ty val_e L4InputPartial607 -> T
    | L4InputOpaque607 n ps ty val_e T -> T
    | _ -> F) /\
   l4_admit_extended624 fuel env input = L4KAccept491 next ==>
   l4_venv_sound973 next venv /\ l4_venv_wf966 venv`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves") (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  l4_subst_cases_tac974 (SPEC `input:l4_input_decl607` (cases "l4_input_decl607")) THEN
  REWRITE_TAC [l4_admit_extended624;l4_env_dis975] THENL
  [(* InputAxiom *)
   BOOL_CASES_TAC `a3:bool` THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_venv_sound_prepend_restricted975 THEN
    ASM_REWRITE_TAC [l4_restricted_constant624;l4_kdecl_name493;l4_kdecl_kind493;
                     l4_is_restricted_kind975;l4_env_dis975] THEN
    MATCH_MP_TAC l4_kfind_decl_safety_env_none975 THEN EXISTS_TAC `L4InputUnsafe607` THEN
    MATCH_MP_TAC l4_check_header_fresh975 THEN ASM_MESON_TAC [];
    USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973)];
   (* InputDefinition *)
   l4_subst_cases_tac974 (SPEC `a5:l4_input_safety607` (cases "l4_input_safety607")) THEN
   REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THENL
   [(* Partial *)
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_venv_sound_prepend_restricted975 THEN
     ASM_REWRITE_TAC [l4_restricted_definition624;l4_kdecl_name493;l4_kdecl_kind493;
                      l4_is_restricted_kind975;l4_env_dis975] THEN
     MATCH_MP_TAC l4_check_header_fresh975 THEN ASM_MESON_TAC [];
     USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973)];
    (* Unsafe *)
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
    [MATCH_MP_TAC l4_venv_sound_prepend_restricted975 THEN
     ASM_REWRITE_TAC [l4_restricted_definition624;l4_kdecl_name493;l4_kdecl_kind493;
                      l4_is_restricted_kind975;l4_env_dis975] THEN
     MATCH_MP_TAC l4_kfind_decl_safety_env_none975 THEN EXISTS_TAC `L4InputUnsafe607` THEN
     MATCH_MP_TAC l4_check_header_fresh975 THEN ASM_MESON_TAC [];
     USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973)]];
   (* InputOpaque *)
   BOOL_CASES_TAC `a4:bool` THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
   STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_venv_sound_prepend_restricted975 THEN
    ASM_REWRITE_TAC [l4_restricted_constant624;l4_kdecl_name493;l4_kdecl_kind493;
                     l4_is_restricted_kind975;l4_env_dis975] THEN
    MATCH_MP_TAC l4_check_header_fresh975 THEN ASM_MESON_TAC [];
    USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973)]]);;

let l4_kfind_decl_append_fresh975 = prove
 (`!rest env n.
   l4_kfind_decl493 env n = NONE /\
   ~MEM n (MAP l4_kdecl_name493 rest) ==>
   l4_kfind_decl493 (APPEND rest env) n = NONE`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [APPEND;MAP;MEM;DE_MORGAN_THM;l4_kfind_decl493] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);;

let l4_venv_sound_prepend_restricted_list975 = prove
 (`!ds env venv.
   l4_venv_sound973 env venv /\
   ALL (\d. l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
            l4_is_restricted_kind975 (l4_kdecl_kind493 d)) ds /\
   l4_names_unique437 (MAP l4_kdecl_name493 ds) ==>
   l4_venv_sound973 (APPEND ds env) venv`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [APPEND;ALL;MAP;l4_names_unique437;l4_name_mem437] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC l4_venv_sound_prepend_restricted975 THEN ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
   MATCH_MP_TAC l4_kfind_decl_append_fresh975 THEN ASM_REWRITE_TAC []]);;

let l4_check_mutual_headers_names975 = prove
 (`!inputs fuel view ps mode phs.
   l4_check_mutual_headers624 inputs fuel view ps mode = L4KAccept491 phs ==>
   ALL (\inp.
     match inp with
     | L4InputDefinition607 hints n qs ty val_e s ->
         l4_safety_eqb624 s mode /\ l4_kfind_decl493 view n = NONE
     | _ -> F) inputs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_check_mutual_headers624;ALL] THEN
  l4_subst_cases_tac974 (SPEC `h:l4_input_decl607` (cases "l4_input_decl607")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_check_header_fresh975 THEN ASM_MESON_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []]);;

let l4_check_mutual_values_generated975 = prove
 (`!inputs fuel view view0 mode gen.
   ~(mode = L4InputSafe607) /\
   ALL (\inp.
     match inp with
     | L4InputDefinition607 hints n qs ty val_e s ->
         l4_safety_eqb624 s mode /\ l4_kfind_decl493 view0 n = NONE
     | _ -> F) inputs /\
   l4_check_mutual_values624 inputs fuel view = L4KAccept491 gen ==>
   MAP l4_kdecl_name493 gen = MAP l4_mutual_name624 inputs /\
   ALL (\d. l4_kfind_decl493 view0 (l4_kdecl_name493 d) = NONE /\
            l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_check_mutual_values624;ALL;MAP;l4_env_dis975] THENL
  [STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN REWRITE_TAC [MAP;ALL];
   ALL_TAC] THEN
  l4_subst_cases_tac974 (SPEC `h:l4_input_decl607` (cases "l4_input_decl607")) THEN
  REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
    `MAP l4_kdecl_name493 x' = MAP l4_mutual_name624 t /\
     ALL (\d. l4_kfind_decl493 view0 (l4_kdecl_name493 d) = NONE /\
              l4_is_restricted_kind975 (l4_kdecl_kind493 d)) x'`
    STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`fuel:num`;`view:l4_kdeclaration493 list`;`mode:l4_input_safety607`] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [MAP;ALL;l4_restricted_definition624;l4_kdecl_name493;
                   l4_kdecl_kind493;l4_mutual_name624] THEN
  UNDISCH_TAC `l4_safety_eqb624 a5 mode` THEN REWRITE_TAC [l4_safety_eqb624] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(mode = L4InputSafe607)` THEN
  l4_subst_cases_tac974 (SPEC `mode:l4_input_safety607` (cases "l4_input_safety607")) THEN
  REWRITE_TAC [l4_safety_kind624;l4_is_restricted_kind975;l4_env_dis975]);;

let l4_admit_mutual_sound975 = prove
 (`!fuel env venv inputs next.
   l4_venv_sound973 env venv /\
   l4_admit_mutual624 fuel env inputs = L4KAccept491 next ==>
   l4_venv_sound973 next venv /\ l4_venv_wf966 venv /\
   (?gen. next = APPEND gen env /\
          ALL (\d. l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves") MP_TAC) THEN
  REWRITE_TAC [l4_admit_mutual624] THEN
  l4_subst_cases_tac974 (ISPEC `inputs:l4_input_decl607 list` (cases "list")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  l4_subst_cases_tac974 (SPEC `a0:l4_input_decl607` (cases "l4_input_decl607")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `phs:l4_kdeclaration493 list` (CONJUNCTS_THEN2 (LABEL_TAC "Hhdr")
    (X_CHOOSE_THEN `gen:l4_kdeclaration493 list` (CONJUNCTS_THEN2 (LABEL_TAC "Hvals") MP_TAC)))) THEN
  REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
    `ALL (\inp.
       match inp with
       | L4InputDefinition607 hints n qs ty val_e s ->
           l4_safety_eqb624 s a5 /\
           l4_kfind_decl493 (l4_safety_environment624 a5 env) n = NONE
       | _ -> F) (CONS (L4InputDefinition607 a0' a1' a2 a3 a4 a5) a1)` (LABEL_TAC "Hhdr_all") THENL
  [MATCH_MP_TAC l4_check_mutual_headers_names975 THEN ASM_MESON_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
    `MAP l4_kdecl_name493 gen = MAP l4_mutual_name624 (CONS (L4InputDefinition607 a0' a1' a2 a3 a4 a5) a1) /\
     ALL (\d. l4_kfind_decl493 (l4_safety_environment624 a5 env) (l4_kdecl_name493 d) = NONE /\
              l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC l4_check_mutual_values_generated975 THEN
   MAP_EVERY EXISTS_TAC
     [`fuel:num`;`APPEND phs (l4_safety_environment624 a5 env)`;`a5:l4_input_safety607`] THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `~l4_safety_eqb624 a5 L4InputSafe607` THEN REWRITE_TAC [l4_safety_eqb624];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC l4_venv_sound_prepend_restricted_list975 THEN ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `ALL (\d. l4_kfind_decl493 (l4_safety_environment624 a5 env) (l4_kdecl_name493 d) = NONE /\
                         l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen` THEN
   REWRITE_TAC [GSYM ALL_MEM] THEN MESON_TAC [l4_kfind_decl_safety_env_none975];
   USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   EXISTS_TAC `gen:l4_kdeclaration493 list` THEN REWRITE_TAC [] THEN
   UNDISCH_TAC `ALL (\d. l4_kfind_decl493 (l4_safety_environment624 a5 env) (l4_kdecl_name493 d) = NONE /\
                         l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen` THEN
   REWRITE_TAC [GSYM ALL_MEM] THEN MESON_TAC []]);;

let l4_admit_inductive_extended_unsafe_sound975 = prove
 (`!fuel env venv types ctors recs next.
   l4_venv_sound973 env venv /\
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KAccept491 next ==>
   l4_venv_wf966 venv /\
   (?added. next = APPEND added env /\
            ALL (\d. match l4_kdecl_kind493 d with L4KDUnsafe493 r -> T | _ -> F) added)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC [l4_admit_inductive_extended633;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `chk:l4_kdeclaration493 list` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL
  [USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   EXISTS_TAC `MAP l4_mark_unsafe_inductive633
                 (FILTER (\d. match l4_kfind_decl493 env (l4_kdecl_name493 d) with
                              | NONE -> T | SOME old -> F) chk)` THEN
   REWRITE_TAC [GSYM ALL_MEM;MEM_MAP] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [l4_mark_unsafe_inductive633;l4_kdecl_kind493;l4_env_dis975]]);;

(* ========================================================================= *)
(* 6. Quotient Admission Soundness (`quotient_admission608` <-> `971`)       *)
(* ========================================================================= *)

let l4_q_names_eq975 = prove
 (`l4_q_eq_name608 = l4_eq_name971 /\
   l4_q_name608 = l4_quot_name971 /\
   l4_q_mk_name608 = l4_quot_mk_name971 /\
   l4_q_lift_name608 = l4_quot_lift_name971 /\
   l4_q_ind_name608 = l4_quot_ind_name971`,
  REWRITE_TAC [l4_q_eq_name608;l4_eq_name971;l4_q_name608;l4_quot_name971;
               l4_q_mk_name608;l4_quot_mk_name971;l4_q_lift_name608;l4_quot_lift_name971;
               l4_q_ind_name608;l4_quot_ind_name971]);;

let l4_kexpr_eqb_tr_e975 = prove
 (`!e1 e2 ps. l4_kexpr_eqb480 e1 e2 ==> l4_tr_e967 ps e1 = l4_tr_e967 ps e2`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  TRY (REWRITE_TAC [l4_kexpr_eqb480] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC THEN NO_TAC) THENL
  [(* Const *)
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [];
   (* App *)
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   (* Lam *)
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   (* Pi *)
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975] THEN
   COND_CASES_TAC THEN REWRITE_TAC [] THEN DISCH_TAC THEN
   ASM_MESON_TAC [];
   (* Let *)
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975];
   (* Proj *)
   DISCH_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975];
   (* MData *)
   DISCH_TAC THEN REPEAT GEN_TAC THEN
   l4_subst_cases_tac974 (SPEC `e2:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [l4_kexpr_eqb480;l4_tr_e967;l4_env_dis975] THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let l4_keep_cases_tac975 th =
  REPEAT_TCL DISJ_CASES_THEN
    (REPEAT_TCL CHOOSE_THEN (fun h -> ASSUME_TAC h THEN SUBST1_TAC h)) th;;

let l4_quot_compute_tac975 =
  REWRITE_TAC [l4_quotient_eq_type608;l4_canonical_quotient608;
               l4_kdecl_params493;l4_kdecl_type493;
               l4_q_local608;l4_kinitial_state491;l4_kind_fresh491;
               l4_klocal_expr489;l4_klocal_id489;l4_klocal_user489;
               l4_klocal_binder489;l4_klocal_type489;l4_q_arrow608;
               l4_kapply_exprs489;l4_kclose_pi489;l4_kabstract_local489;
               l4_klift447;l4_kind_id491;l4_env_dis975;
               LET_DEF;LET_END_DEF;FST;SND;
               injectivity "l4_name";distinctness "l4_name";
               CONS_11;NOT_CONS_NIL;GSYM NOT_CONS_NIL;
               l4_eq_vconst971;l4_quot_vconst971;l4_quot_mk_vconst971;
               l4_quot_lift_vconst971;l4_quot_ind_vconst971;
               l4_rel_vtype971;l4_quot_sanity_vtype971;l4_vc_type961;
               l4_q_names_eq975] THEN
  REPEAT (CHANGED_TAC
    (CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC [l4_kclose_pi489;l4_kapply_exprs489;l4_q_arrow608;
                  l4_kabstract_local489;l4_klift447;
                  injectivity "l4_name";distinctness "l4_name";
                  CONS_11;NOT_CONS_NIL;GSYM NOT_CONS_NIL])) THEN
  REWRITE_TAC [l4_tr_e967;l4_tr_l967;l4_tr_ls967;l4_index_of_name967;
               l4_opt_map967;l4_opt_map2967;
               injectivity "l4_name";distinctness "l4_name";
               CONS_11;NOT_CONS_NIL;GSYM NOT_CONS_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC [l4_tr_e967;l4_tr_l967;l4_tr_ls967;l4_index_of_name967;
               l4_opt_map967;l4_opt_map2967];;

let l4_tr_e_quotient_eq_type975 = prove
 (`!u. l4_tr_e967 [u] (l4_quotient_eq_type608 (L4KParam447 u)) =
       SOME (l4_vc_type961 l4_eq_vconst971)`,
  GEN_TAC THEN l4_quot_compute_tac975);;

let l4_tr_e_canonical_quotient_qtype975 = prove
 (`l4_tr_e967 (l4_kdecl_params493 (l4_canonical_quotient608 L4KQType493))
              (l4_kdecl_type493 (l4_canonical_quotient608 L4KQType493)) =
   SOME (l4_vc_type961 l4_quot_vconst971)`,
  l4_quot_compute_tac975);;

let l4_tr_e_canonical_quotient_qctor975 = prove
 (`l4_tr_e967 (l4_kdecl_params493 (l4_canonical_quotient608 L4KQCtor493))
              (l4_kdecl_type493 (l4_canonical_quotient608 L4KQCtor493)) =
   SOME (l4_vc_type961 l4_quot_mk_vconst971)`,
  l4_quot_compute_tac975);;

let l4_tr_e_canonical_quotient_qlift975 = prove
 (`l4_tr_e967 (l4_kdecl_params493 (l4_canonical_quotient608 L4KQLift493))
              (l4_kdecl_type493 (l4_canonical_quotient608 L4KQLift493)) =
   SOME (l4_vc_type961 l4_quot_lift_vconst971)`,
  l4_quot_compute_tac975);;

let l4_tr_e_canonical_quotient_qind975 = prove
 (`l4_tr_e967 (l4_kdecl_params493 (l4_canonical_quotient608 L4KQInd493))
              (l4_kdecl_type493 (l4_canonical_quotient608 L4KQInd493)) =
   SOME (l4_vc_type961 l4_quot_ind_vconst971)`,
  l4_quot_compute_tac975);;

let l4_quotient_check_eq_sound975 = prove
 (`!env venv.
   l4_venv_sound973 env venv /\
   l4_quotient_check_eq608 env = L4KAccept491 one ==>
   ?d info u ci.
     l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
     l4_kdecl_kind493 d = L4KDInductive493 info /\
     l4_kdecl_params493 d = [u] /\
     l4_venv_lookup_const961 venv l4_q_eq_name608 ci /\
     l4_vc_uvars961 ci = 1 /\
     l4_vis_defeq_u961 venv 1 [] (l4_vc_type961 ci) (l4_vc_type961 l4_eq_vconst971)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_quotient_check_eq608] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves") MP_TAC) THEN
  l4_opt_cases_keep975 `l4_kfind_decl493 env l4_q_eq_name608` `d:l4_kdeclaration493` THEN
  l4_keep_cases_tac975 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  l4_keep_cases_tac975 (ISPEC `l4_kdecl_params493 d` (cases "list")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  l4_subst_cases_tac974 (ISPEC `a1:l4_name list` (cases "list")) THEN
  REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE []) THEN
  USE_THEN "Hves" (MP_TAC o SPECL [`l4_q_eq_name608`;`d:l4_kdeclaration493`] o
                   MATCH_MP l4_ves_constants973) THEN
  ASM_REWRITE_TAC [l4_env_dis975;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d:l4_kdeclaration493`;`a:l4_kinductive_data493`;`a0:l4_name`;`ci:l4_vconstant961`] THEN
  ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `l4_vtr_expr973 env venv [a0] l4_vl_empty973 (l4_kdecl_type493 d) (l4_vc_type961 ci)` THEN
  REWRITE_TAC [l4_vtr_expr973;l4_vl_ctx_empty975;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN (X_CHOOSE_THEN `e0:l4_vexpr961` (CONJUNCTS_THEN2 (LABEL_TAC "Hes") (LABEL_TAC "H01"))) THEN
  SUBGOAL_THEN `l4_tr_e967 [a0] (l4_kdecl_type493 d) = SOME (l4_vc_type961 l4_eq_vconst971)` ASSUME_TAC THENL
  [TRANS_TAC EQ_TRANS `l4_tr_e967 [a0] (l4_quotient_eq_type608 (L4KParam447 a0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_kexpr_eqb_tr_e975 THEN ASM_REWRITE_TAC [];
    REWRITE_TAC [l4_tr_e_quotient_eq_type975]];
   ALL_TAC] THEN
  SUBGOAL_THEN `e0 = l4_vc_type961 l4_eq_vconst971` SUBST_ALL_TAC THENL
  [MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`[a0:l4_name]`;
                  `l4_vl_empty973`;`l4_kdecl_type493 d`;`e0:l4_vexpr961`] l4_vtr_expr_s_eq_tr_e973) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MATCH_MP_TAC o SPECL [`[]:l4_vexpr961 list`;`l4_vc_type961 l4_eq_vconst971`]) THEN
   ASM_REWRITE_TAC [l4_vl_empty973;l4_vl_free973;l4_vl_bound973;l4_vl_of_ctx_lams973];
   ALL_TAC] THEN
  MATCH_MP_TAC l4_vis_defeq_u_symm972 THEN
  ASM_REWRITE_TAC [l4_vctx_wf966] THEN
  USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973));;

let l4_quot_names_distinct975 = prove
 (`~(l4_quot_name971 = l4_quot_mk_name971) /\
   ~(l4_quot_name971 = l4_quot_lift_name971) /\
   ~(l4_quot_name971 = l4_quot_ind_name971) /\
   ~(l4_quot_mk_name971 = l4_quot_lift_name971) /\
   ~(l4_quot_mk_name971 = l4_quot_ind_name971) /\
   ~(l4_quot_lift_name971 = l4_quot_ind_name971)`,
  REWRITE_TAC [l4_quot_name971;l4_quot_mk_name971;l4_quot_lift_name971;l4_quot_ind_name971;
               distinctness "l4_name";injectivity "l4_name";CONS_11;NOT_CONS_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let l4_exists_add_quot975 = prove
 (`!venv.
   ~l4_venv_contains971 venv l4_quot_name971 /\
   ~l4_venv_contains971 venv l4_quot_mk_name971 /\
   ~l4_venv_contains971 venv l4_quot_lift_name971 /\
   ~l4_venv_contains971 venv l4_quot_ind_name971 ==>
   ?venv_q. l4_venv_add_quot971 venv = SOME venv_q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_venv_add_quot_inv971] THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`l4_quot_name971`;`l4_quot_vconst971`] l4_venv_add_const_eq_none971) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `e1:l4_venv961`) THEN
  SUBGOAL_THEN `~l4_venv_contains971 e1 l4_quot_mk_name971 /\
                ~l4_venv_contains971 e1 l4_quot_lift_name971 /\
                ~l4_venv_contains971 e1 l4_quot_ind_name971` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC [l4_venv_contains971] THEN
   ASM_MESON_TAC [l4_venv_add_const_lookup971;l4_venv_contains971;l4_quot_names_distinct975];
   ALL_TAC] THEN
  MP_TAC (SPECL [`e1:l4_venv961`;`l4_quot_mk_name971`;`l4_quot_mk_vconst971`] l4_venv_add_const_eq_none971) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `e2:l4_venv961`) THEN
  SUBGOAL_THEN `~l4_venv_contains971 e2 l4_quot_lift_name971 /\
                ~l4_venv_contains971 e2 l4_quot_ind_name971` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC [l4_venv_contains971] THEN
   ASM_MESON_TAC [l4_venv_add_const_lookup971;l4_venv_contains971;l4_quot_names_distinct975];
   ALL_TAC] THEN
  MP_TAC (SPECL [`e2:l4_venv961`;`l4_quot_lift_name971`;`l4_quot_lift_vconst971`] l4_venv_add_const_eq_none971) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `e3:l4_venv961`) THEN
  SUBGOAL_THEN `~l4_venv_contains971 e3 l4_quot_ind_name971` ASSUME_TAC THENL
  [REWRITE_TAC [l4_venv_contains971] THEN
   ASM_MESON_TAC [l4_venv_add_const_lookup971;l4_venv_contains971;l4_quot_names_distinct975];
   ALL_TAC] THEN
  MP_TAC (SPECL [`e3:l4_venv961`;`l4_quot_ind_name971`;`l4_quot_ind_vconst971`] l4_venv_add_const_eq_none971) THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `e4:l4_venv961`) THEN
  MAP_EVERY EXISTS_TAC [`l4_venv_add_defeq971 e4 l4_quot_vdefeq971`;
                        `e1:l4_venv961`;`e2:l4_venv961`;`e3:l4_venv961`;`e4:l4_venv961`] THEN
  ASM_REWRITE_TAC []);;

let l4_admit_quotient_sound975 = prove
 (`!fuel env venv n ps ty kind next.
   l4_venv_sound973 env venv /\
   l4_admit_quotient608 fuel env n ps ty kind = L4KAccept491 next ==>
   let generated = l4_canonical_quotient608 kind in
   next = CONS generated env /\
   l4_kfind_decl493 env n = NONE /\
   n = l4_kdecl_name493 generated /\
   LENGTH ps = LENGTH (l4_kdecl_params493 generated) /\
   (?ty' u'.
      l4_vtr_expr973 env venv ps l4_vl_empty973 ty ty' /\
      l4_vhas_type961 venv (LENGTH ps) [] ty' (L4VSort961 u') /\
      l4_vconstant_wf966 venv (L4VConstant961 (LENGTH ps) ty')) /\
   (l4_vquot_ready971 venv /\
    ~l4_venv_contains971 venv l4_quot_name971 /\
    ~l4_venv_contains971 venv l4_quot_mk_name971 /\
    ~l4_venv_contains971 venv l4_quot_lift_name971 /\
    ~l4_venv_contains971 venv l4_quot_ind_name971 ==>
    ?venv_q.
      l4_venv_add_quot971 venv = SOME venv_q /\
      l4_venv_ordered961 venv venv_q /\
      l4_venv_wf966 venv_q /\
      l4_venv_lookup_const961 venv_q l4_quot_name971 l4_quot_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_mk_name971 l4_quot_mk_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_lift_name971 l4_quot_lift_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_ind_name971 l4_quot_ind_vconst971 /\
      l4_venv_has_defeq961 venv_q l4_quot_vdefeq971)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_admit_quotient608;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
    (X_CHOOSE_THEN `u1:1` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u2:1` (CONJUNCTS_THEN2 (LABEL_TAC "Hhdr") MP_TAC))))) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  REMOVE_THEN "Hhdr" MP_TAC THEN STRUCT_CASES_TAC (SPEC `u2:1` one) THEN DISCH_TAC THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                 `n:l4_name`;`ps:l4_name list`;`ty:l4_kexpr447`] l4_check_header_sound975) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`ty':l4_vexpr961`;`u':l4_vlevel961`] THEN ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `venv:l4_venv961` l4_exists_add_quot975) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_TAC `venv_q:l4_venv961`) THEN EXISTS_TAC `venv_q:l4_venv961` THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`venv_q:l4_venv961`] l4_add_quot_wf971) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`venv_q:l4_venv961`] l4_add_quot_objs971) THEN
   ASM_REWRITE_TAC [] THEN
   USE_THEN "Hves" (fun th -> REWRITE_TAC [MATCH_MP l4_ves_wf973 th]) THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_initialize_quotient_sound975 = prove
 (`!env venv next_st.
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_vquot_ready971 venv /\
   l4_initialize_quotient963 (env, F) = L4KAccept491 next_st ==>
   next_st = (APPEND l4_canonical_quotient_block963 env, T) /\
   (?venv_q.
      l4_venv_add_quot971 venv = SOME venv_q /\
      l4_venv_ordered961 venv venv_q /\
      l4_venv_wf966 venv_q /\
      l4_venv_lookup_const961 venv_q l4_quot_name971 l4_quot_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_mk_name971 l4_quot_mk_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_lift_name971 l4_quot_lift_vconst971 /\
      l4_venv_lookup_const961 venv_q l4_quot_ind_name971 l4_quot_ind_vconst971 /\
      l4_venv_has_defeq961 venv_q l4_quot_vdefeq971)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
    (CONJUNCTS_THEN2 (LABEL_TAC "Halign") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hinit")))) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC l4_quot_tx_no_partial_commit963 THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "Hinit" MP_TAC THEN
  REWRITE_TAC [l4_initialize_quotient963;FST;SND;l4_kr_bind_accept967] THEN
  DISCH_THEN (X_CHOOSE_THEN `u:1` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN (K ALL_TAC) THEN
  UNDISCH_TAC `l4_quot_names_fresh963 env l4_quot_tx_names963` THEN
  REWRITE_TAC [l4_quot_tx_names963;l4_quot_names_fresh963;l4_canonical_quotient608;
               l4_kdecl_name493;LET_DEF;LET_END_DEF;FST;SND;l4_env_dis975;l4_q_names_eq975] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `~l4_venv_contains971 venv l4_quot_name971 /\
     ~l4_venv_contains971 venv l4_quot_mk_name971 /\
     ~l4_venv_contains971 venv l4_quot_lift_name971 /\
     ~l4_venv_contains971 venv l4_quot_ind_name971` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN USE_THEN "Halign" (MATCH_MP_TAC o REWRITE_RULE [l4_venv_names_aligned975]) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPEC `venv:l4_venv961` l4_exists_add_quot975) THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_TAC `venv_q:l4_venv961`) THEN EXISTS_TAC `venv_q:l4_venv961` THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`venv_q:l4_venv961`] l4_add_quot_wf971) THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`venv_q:l4_venv961`] l4_add_quot_objs971) THEN
  ASM_REWRITE_TAC [] THEN
  USE_THEN "Hves" (fun th -> REWRITE_TAC [MATCH_MP l4_ves_wf973 th]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(* ========================================================================= *)
(* 7. Inductive Admission Bridge (`env_decl_theory971.ml`)                   *)
(* ========================================================================= *)

let l4_venv_add_const_vals_le975 = prove
 (`!cvs env env'.
   l4_venv_add_const_vals971 env cvs = SOME env' ==> l4_venv_ordered961 env env'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_const_vals971;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_venv_ordered_refl961];
   REWRITE_TAC [l4_venv_add_const_vals971;l4_opt_bind_eq_some971] THEN BETA_TAC THEN
   STRIP_TAC THEN ASM_MESON_TAC [l4_venv_add_const_le971;l4_venv_ordered_trans961]]);;

let l4_venv_add_const_vals_lookup975 = prove
 (`!cvs env env' cv.
   l4_venv_add_const_vals971 env cvs = SOME env' /\ MEM cv cvs ==>
   l4_venv_lookup_const961 env' (l4_vcv_name971 cv) (l4_vcv_const971 cv)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MEM] THEN
  REWRITE_TAC [l4_venv_add_const_vals971;l4_opt_bind_eq_some971] THEN BETA_TAC THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `x:l4_venv961` THEN CONJ_TAC THENL
   [MATCH_MP_TAC l4_venv_add_const_vals_le975 THEN EXISTS_TAC `t:l4_vconst_val971 list` THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_venv_add_const_self971 THEN EXISTS_TAC `env:l4_venv961` THEN ASM_REWRITE_TAC []];
   FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:l4_venv961` THEN ASM_REWRITE_TAC []]);;

let l4_venv_add_raw_defeqs_has975 = prove
 (`!dfs env df.
   MEM df dfs ==> l4_venv_has_defeq961 (l4_venv_add_raw_defeqs971 env dfs) df`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MEM;l4_venv_add_raw_defeqs971] THEN
  DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
  [SUBGOAL_THEN `!ds e d. l4_venv_has_defeq961 e d ==>
                          l4_venv_has_defeq961 (l4_venv_add_raw_defeqs971 e ds) d`
     (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC [l4_venv_add_defeq_self971]) THEN
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_raw_defeqs971] THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_venv_add_defeq_has_defeq971];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_venv_add_raw_defeqs_lookup975 = prove
 (`!dfs env n c.
   l4_venv_lookup_const961 (l4_venv_add_raw_defeqs971 env dfs) n c <=>
   l4_venv_lookup_const961 env n c`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC [l4_venv_add_raw_defeqs971;l4_venv_add_defeq_lookup971]);;

let l4_declarative_inductive_admit_sound975 = prove
 (`!env venv decl.
   l4_venv_sound973 env venv /\
   l4_vinduct_decl_wf971 venv decl ==>
   ?venv'.
     l4_venv_add_induct971 venv decl = SOME venv' /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     (!cv. MEM cv (APPEND (l4_vinduct_type_cvs971 decl)
                    (APPEND (l4_vinduct_ctor_cvs971 decl) (l4_vid_recs971 decl))) ==>
           l4_venv_lookup_const961 venv' (l4_vcv_name971 cv) (l4_vcv_const971 cv)) /\
     (!df. MEM df (l4_vid_iotas971 decl) ==> l4_venv_has_defeq961 venv' df)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hves") (LABEL_TAC "Hdwf")) THEN
  USE_THEN "Hdwf" (MP_TAC o REWRITE_RULE [l4_vinduct_decl_wf971]) THEN
  STRIP_TAC THEN
  ABBREV_TAC `venv' = l4_venv_add_raw_defeqs971 env3 (l4_vid_iotas971 decl)` THEN
  SUBGOAL_THEN `l4_venv_add_induct971 venv decl = SOME venv'` (LABEL_TAC "Hadd") THENL
  [EXPAND_TAC "venv'" THEN
   ASM_REWRITE_TAC [l4_venv_add_induct971;l4_opt_bind971;l4_opt_map971];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 venv' /\ l4_venv_ordered961 venv venv'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC l4_add_induct_wf971 THEN
   EXISTS_TAC `decl:l4_vinduct_decl971` THEN
   ASM_REWRITE_TAC [] THEN USE_THEN "Hves" (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_ordered961 env1 env2 /\ l4_venv_ordered961 env2 env3` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC l4_venv_add_const_vals_le975 THENL
   [EXISTS_TAC `l4_vinduct_ctor_cvs971 decl` THEN FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `l4_vid_recs971 decl` THEN FIRST_ASSUM ACCEPT_TAC];
   ALL_TAC] THEN
  EXISTS_TAC `venv':l4_venv961` THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [X_GEN_TAC `cv:l4_vconst_val971` THEN REWRITE_TAC [MEM_APPEND] THEN EXPAND_TAC "venv'" THEN
   REWRITE_TAC [l4_venv_add_raw_defeqs_lookup975] THEN
   STRIP_TAC THENL
   [SUBGOAL_THEN `l4_venv_lookup_const961 env1 (l4_vcv_name971 cv) (l4_vcv_const971 cv)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_venv_add_const_vals_lookup975 THEN
     MAP_EVERY EXISTS_TAC [`l4_vinduct_type_cvs971 decl`;`venv:l4_venv961`] THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `env2:l4_venv961` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `env1:l4_venv961` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    SUBGOAL_THEN `l4_venv_lookup_const961 env2 (l4_vcv_name971 cv) (l4_vcv_const971 cv)` ASSUME_TAC THENL
    [MATCH_MP_TAC l4_venv_add_const_vals_lookup975 THEN
     MAP_EVERY EXISTS_TAC [`l4_vinduct_ctor_cvs971 decl`;`env1:l4_venv961`] THEN ASM_REWRITE_TAC [];
     MATCH_MP_TAC l4_venv_ordered_const973 THEN EXISTS_TAC `env2:l4_venv961` THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC l4_venv_add_const_vals_lookup975 THEN
    MAP_EVERY EXISTS_TAC [`l4_vid_recs971 decl`;`env2:l4_venv961`] THEN ASM_REWRITE_TAC []];
   X_GEN_TAC `df:l4_vdefeq961` THEN DISCH_TAC THEN EXPAND_TAC "venv'" THEN
   MATCH_MP_TAC l4_venv_add_raw_defeqs_has975 THEN ASM_REWRITE_TAC []]);;

(* ========================================================================= *)
(* 8. End-to-End Declarations Stream, FuelConfig, & File Driver Soundness    *)
(* ========================================================================= *)

let l4_admit_extended_restricted_pure_step975 = prove
 (`!fuel env venv input mid.
   l4_pure_const_env975 env /\
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   (match input with
    | L4InputAxiom607 n ps ty T -> T
    | L4InputDefinition607 hints n ps ty val_e L4InputUnsafe607 -> T
    | L4InputDefinition607 hints n ps ty val_e L4InputPartial607 -> T
    | L4InputOpaque607 n ps ty val_e T -> T
    | _ -> F) /\
   l4_admit_extended624 fuel env input = L4KAccept491 mid ==>
   l4_pure_const_env975 mid /\
   l4_venv_ordered961 venv venv /\
   l4_venv_wf966 venv /\
   l4_venv_sound973 mid venv /\
   l4_venv_names_aligned975 mid venv`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hpure") (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
    (CONJUNCTS_THEN2 (LABEL_TAC "Halign") (CONJUNCTS_THEN2 (LABEL_TAC "Hres") (LABEL_TAC "Hadm"))))) THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                 `input:l4_input_decl607`;`mid:l4_kdeclaration493 list`]
    l4_admit_extended_restricted_sound975) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?d. mid = CONS d env /\ l4_is_restricted_kind975 (l4_kdecl_kind493 d)`
    (X_CHOOSE_THEN `d:l4_kdeclaration493` (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "Hrk"))) THENL
  [REMOVE_THEN "Hadm" MP_TAC THEN REMOVE_THEN "Hres" MP_TAC THEN
   l4_subst_cases_tac974 (SPEC `input:l4_input_decl607` (cases "l4_input_decl607")) THEN
   REWRITE_TAC [l4_admit_extended624;l4_env_dis975] THENL
   [BOOL_CASES_TAC `a3:bool` THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    EXISTS_TAC `l4_restricted_constant624 a0 a1 a2 NONE (L4KDUnsafe493 L4KDAssumption493)` THEN
    REWRITE_TAC [l4_restricted_constant624;l4_kdecl_kind493;l4_is_restricted_kind975;l4_env_dis975];
    l4_subst_cases_tac974 (SPEC `a5:l4_input_safety607` (cases "l4_input_safety607")) THEN
    REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THENL
    [STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     EXISTS_TAC `l4_restricted_definition624 a0 a1 a2 a3 a4 L4KDPartial493` THEN
     REWRITE_TAC [l4_restricted_definition624;l4_kdecl_kind493;l4_is_restricted_kind975;l4_env_dis975];
     STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     EXISTS_TAC `l4_restricted_definition624 a0 a1 a2 a3 a4 (L4KDUnsafe493 L4KDDefinition493)` THEN
     REWRITE_TAC [l4_restricted_definition624;l4_kdecl_kind493;l4_is_restricted_kind975;l4_env_dis975]];
    BOOL_CASES_TAC `a4:bool` THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF;l4_kr_bind_accept967] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [l4_env_dis975]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    EXISTS_TAC `l4_restricted_constant624 a0 a1 a2 (SOME a3) (L4KDUnsafe493 L4KDOpaque493)` THEN
    REWRITE_TAC [l4_restricted_constant624;l4_kdecl_kind493;l4_is_restricted_kind975;l4_env_dis975]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [l4_venv_ordered_refl961] THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_pure_const_env975;l4_kfind_decl493] THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN
    USE_THEN "Hrk" (MP_TAC o REWRITE_RULE [l4_is_restricted_kind975]) THEN
    l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 d` (cases "l4_kdecl_kind493")) THEN
    REWRITE_TAC [l4_env_dis975];
    USE_THEN "Hpure" (MATCH_ACCEPT_TAC o REWRITE_RULE [l4_pure_const_env975])];
   REWRITE_TAC [l4_venv_names_aligned975;l4_kfind_decl493] THEN GEN_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
   USE_THEN "Halign" (MATCH_ACCEPT_TAC o REWRITE_RULE [l4_venv_names_aligned975])]);;


let l4_pure_input_decl975 = new_definition
 `l4_pure_input_decl975 fuel input <=>
   match input with
   | L4InputDefinition607 hints n ps ty body L4InputSafe607 ->
       !env. l4_classify_primitive620 fuel env n ps ty body = L4KAccept491 NONE
   | _ -> T`;;

let l4_check_declarations620_pure_sound975 = prove
 (`!inputs fuel.
   (!v. l4_venv_wf966 v ==> l4_defeq_injectivity972 v) /\
   ALL (l4_pure_input_decl975 fuel) inputs ==>
   !env venv final.
     l4_pure_const_env975 env /\
     l4_venv_sound973 env venv /\
     l4_venv_names_aligned975 env venv /\
     l4_check_declarations620 inputs fuel env = L4KAccept491 final ==>
     ?venv'.
       l4_pure_const_env975 final /\
       l4_venv_ordered961 venv venv' /\
       l4_venv_wf966 venv' /\
       l4_venv_sound973 final venv' /\
       l4_venv_names_aligned975 final venv'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL;l4_check_declarations620;l4_kr_bind_accept967;l4_env_dis975] THEN
  BETA_TAC THENL
  [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
   EXISTS_TAC `venv:l4_venv961` THEN
   ASM_REWRITE_TAC [l4_venv_ordered_refl961] THEN
   FIRST_ASSUM (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hinj_all") (CONJUNCTS_THEN2 (LABEL_TAC "Hh") (LABEL_TAC "Ht"))) THEN
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hpure") (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
     (CONJUNCTS_THEN2 (LABEL_TAC "Halign")
       (X_CHOOSE_THEN `mid:l4_kdeclaration493 list` (CONJUNCTS_THEN2 (LABEL_TAC "Hadm") (LABEL_TAC "Hrest")))))) THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `h:l4_input_decl607`;`mid:l4_kdeclaration493 list`] l4_venv_sound_pure_admit975) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    USE_THEN "Hh" (MP_TAC o REWRITE_RULE [l4_pure_input_decl975]) THEN
    ASM_REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `venv1:l4_venv961` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `l4_venv_sound973 mid venv1` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN USE_THEN "Hinj_all" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`fuel:num`]) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`mid:l4_kdeclaration493 list`;`venv1:l4_venv961`;
                               `final:l4_kdeclaration493 list`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `venv2:l4_venv961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `venv2:l4_venv961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_venv_ordered_trans961 THEN EXISTS_TAC `venv1:l4_venv961` THEN
   ASM_REWRITE_TAC []]);;

let l4_check_declarations620_from_empty_sound975 = prove
 (`!inputs fuel final.
   (!v. l4_venv_wf966 v ==> l4_defeq_injectivity972 v) /\
   ALL (l4_pure_input_decl975 fuel) inputs /\
   l4_check_declarations620 inputs fuel [] = L4KAccept491 final ==>
   ?venv'. l4_venv_wf966 venv' /\ l4_venv_sound973 final venv'`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`inputs:l4_input_decl607 list`;`fuel:num`] l4_check_declarations620_pure_sound975) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`[]:l4_kdeclaration493 list`;`l4_venv_empty961`;`final:l4_kdeclaration493 list`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_pure_const_env_empty975;l4_venv_names_aligned_empty975] THEN
   MATCH_MP_TAC l4_venv_sound_empty973 THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [l4_venv_empty_wf966];
   MESON_TAC []]);;

let l4_admit_basic_with_config_sound975 = prove
 (`!cfg env venv input next.
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_admit_basic_with_config965 cfg env input = L4KAccept491 next ==>
   ?d ci venv'.
     next = CONS d env /\
     l4_kfind_decl493 env (l4_kdecl_name493 d) = NONE /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     l4_venv_lookup_const961 venv' (l4_kdecl_name493 d) ci /\
     l4_venv_names_aligned975 next venv'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_admit_basic_with_config965] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
  SUBGOAL_THEN `l4_admit620 (l4_fc_rec_depth965 cfg) env input = L4KAccept491 next` ASSUME_TAC THENL
  [UNDISCH_TAC `l4_admit_basic607 (l4_fc_rec_depth965 cfg) env input = L4KAccept491 next` THEN
   REWRITE_TAC [l4_admit620] THEN
   l4_subst_cases_tac974 (SPEC `input:l4_input_decl607` (cases "l4_input_decl607")) THEN
   REWRITE_TAC [l4_admit_basic607;l4_env_dis975];
   ALL_TAC] THEN
  MP_TAC (SPECL [`l4_fc_rec_depth965 cfg`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                 `input:l4_input_decl607`;`next:l4_kdeclaration493 list`] l4_admit620_sound975) THEN
  ASM_REWRITE_TAC [] THEN MESON_TAC []);;

let l4_file_pure_batch975 = new_definition
 `l4_file_pure_batch975 fuel (rows:(num # l4_file_decl642) list) batch <=>
   match batch with
   | L4FileSingle642 i ->
       i < LENGTH rows /\
       (match SND (EL i rows) with
        | L4FileOrdinary642 input all -> l4_pure_input_decl975 fuel input
        | _ -> F)
   | L4FileMutual642 leader indices -> T`;;

let l4_pure_const_env_append_restricted975 = prove
 (`!gen env.
   l4_pure_const_env975 env /\
   ALL (\d. l4_is_restricted_kind975 (l4_kdecl_kind493 d)) gen ==>
   l4_pure_const_env975 (APPEND gen env)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [APPEND;ALL] THEN BETA_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC [l4_pure_const_env975;l4_kfind_decl493] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THENL
  [DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_TAC `l4_is_restricted_kind975 (l4_kdecl_kind493 h)` THEN
   REWRITE_TAC [l4_is_restricted_kind975] THEN
   l4_subst_cases_tac974 (SPEC `l4_kdecl_kind493 h` (cases "l4_kdecl_kind493")) THEN
   REWRITE_TAC [l4_env_dis975];
   SUBGOAL_THEN `l4_pure_const_env975 (APPEND t env)`
     (fun th -> MATCH_ACCEPT_TAC (REWRITE_RULE [l4_pure_const_env975] th)) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_venv_names_aligned_append975 = prove
 (`!gen env venv.
   l4_venv_names_aligned975 env venv ==>
   l4_venv_names_aligned975 (APPEND gen env) venv`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC [l4_venv_names_aligned975;l4_kfind_decl493] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  SUBGOAL_THEN `l4_venv_names_aligned975 (APPEND t env) venv`
    (MATCH_ACCEPT_TAC o SPEC `n:l4_name` o REWRITE_RULE [l4_venv_names_aligned975]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let l4_file_check_batch_pure_sound975 = prove
 (`!fuel env venv rows batch next.
   (!v. l4_venv_wf966 v ==> l4_defeq_injectivity972 v) /\
   l4_file_pure_batch975 fuel rows batch /\
   l4_pure_const_env975 env /\
   l4_venv_sound973 env venv /\
   l4_venv_names_aligned975 env venv /\
   l4_file_check_batch642 fuel env rows batch = L4KAccept491 next ==>
   ?venv'.
     l4_pure_const_env975 next /\
     l4_venv_ordered961 venv venv' /\
     l4_venv_wf966 venv' /\
     l4_venv_sound973 next venv' /\
     l4_venv_names_aligned975 next venv'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Hinj_all") (CONJUNCTS_THEN2 (LABEL_TAC "Hpb")
    (CONJUNCTS_THEN2 (LABEL_TAC "Hpure") (CONJUNCTS_THEN2 (LABEL_TAC "Hves")
      (CONJUNCTS_THEN2 (LABEL_TAC "Halign") (LABEL_TAC "Hstep")))))) THEN
  REMOVE_THEN "Hstep" MP_TAC THEN REMOVE_THEN "Hpb" MP_TAC THEN
  l4_subst_cases_tac974 (SPEC `batch:l4_file_batch642` (cases "l4_file_batch642")) THEN
  REWRITE_TAC [l4_file_pure_batch975;l4_file_check_batch642;l4_env_dis975] THENL
  [(* L4FileSingle642 *)
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [l4_file_admit_single642] THEN
   DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
   UNDISCH_TAC `match SND (EL a (rows:(num # l4_file_decl642) list)) with L4FileOrdinary642 input all -> l4_pure_input_decl975 fuel input | _ -> F` THEN
   l4_keep_cases_tac975 (SPEC `SND (EL a (rows:(num # l4_file_decl642) list))` (cases "l4_file_decl642")) THEN
   REWRITE_TAC [l4_env_dis975] THEN
   DISCH_THEN (LABEL_TAC "Hp_in") THEN DISCH_THEN (LABEL_TAC "Hext_adm") THEN
   SUBGOAL_THEN
     `((match a0 with
        | L4InputAxiom607 n ps ty T -> T
        | L4InputDefinition607 hints n ps ty val_e L4InputUnsafe607 -> T
        | L4InputDefinition607 hints n ps ty val_e L4InputPartial607 -> T
        | L4InputOpaque607 n ps ty val_e T -> T
        | _ -> F) \/
       l4_admit_extended624 fuel env a0 = l4_admit620 fuel env a0)`
     (DISJ_CASES_THEN ASSUME_TAC) THENL
   [l4_subst_cases_tac974 (SPEC `a0:l4_input_decl607` (cases "l4_input_decl607")) THEN
    REWRITE_TAC [l4_admit_extended624;l4_env_dis975] THENL
    [BOOL_CASES_TAC `a3:bool` THEN REWRITE_TAC [l4_env_dis975];
     l4_subst_cases_tac974 (SPEC `a5:l4_input_safety607` (cases "l4_input_safety607")) THEN
     REWRITE_TAC [l4_env_dis975];
     BOOL_CASES_TAC `a4:bool` THEN REWRITE_TAC [l4_env_dis975]];
    (* Restricted step *)
    EXISTS_TAC `venv:l4_venv961` THEN
    MATCH_MP_TAC l4_admit_extended_restricted_pure_step975 THEN
    MAP_EVERY EXISTS_TAC [`fuel:num`;`env:l4_kdeclaration493 list`;`a0:l4_input_decl607`] THEN
    ASM_REWRITE_TAC [];
    (* Safe ordinary step *)
    MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                   `a0:l4_input_decl607`;`next:l4_kdeclaration493 list`] l4_venv_sound_pure_admit975) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [USE_THEN "Hext_adm" (fun h1 -> FIRST_ASSUM (fun h2 -> ACCEPT_TAC (REWRITE_RULE [h2] h1)));
      REPEAT STRIP_TAC THEN USE_THEN "Hp_in" (MP_TAC o REWRITE_RULE [l4_pure_input_decl975]) THEN
      ASM_REWRITE_TAC [l4_env_dis975] THEN DISCH_THEN MATCH_ACCEPT_TAC];
     DISCH_THEN (X_CHOOSE_THEN `venv1:l4_venv961` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `venv1:l4_venv961` THEN ASM_REWRITE_TAC [] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN USE_THEN "Hinj_all" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
   (* L4FileMutual642 *)
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;LET_DEF;LET_END_DEF] THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975;l4_kr_bind_accept967] THEN
   DISCH_THEN (X_CHOOSE_THEN `members:l4_file_decl642 list` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `inputs:l4_input_decl607 list` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
   COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `inputs:l4_input_decl607 list`;`next:l4_kdeclaration493 list`] l4_admit_mutual_sound975) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [l4_venv_ordered_refl961] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_pure_const_env_append_restricted975 THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC l4_venv_names_aligned_append975 THEN ASM_REWRITE_TAC []]]);;

let l4_file_check_batches_pure_sound975 = prove
 (`!batches fuel rows.
   (!v. l4_venv_wf966 v ==> l4_defeq_injectivity972 v) /\
   ALL (l4_file_pure_batch975 fuel rows) batches ==>
   !env venv final.
     l4_pure_const_env975 env /\
     l4_venv_sound973 env venv /\
     l4_venv_names_aligned975 env venv /\
     l4_file_check_batches642 batches fuel env rows = L4KAccept491 final ==>
     ?venv'.
       l4_pure_const_env975 final /\
       l4_venv_ordered961 venv venv' /\
       l4_venv_wf966 venv' /\
       l4_venv_sound973 final venv' /\
       l4_venv_names_aligned975 final venv'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL;l4_file_check_batches642;l4_kr_bind_accept967;l4_env_dis975] THEN
  BETA_TAC THENL
  [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
   EXISTS_TAC `venv:l4_venv961` THEN ASM_REWRITE_TAC [l4_venv_ordered_refl961] THEN
   FIRST_ASSUM (ACCEPT_TAC o MATCH_MP l4_ves_wf973);
   STRIP_TAC THEN REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `mid:l4_kdeclaration493 list` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
   MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`venv:l4_venv961`;
                  `rows:(num # l4_file_decl642) list`;`h:l4_file_batch642`;
                  `mid:l4_kdeclaration493 list`] l4_file_check_batch_pure_sound975) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `venv1:l4_venv961` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`fuel:num`;`rows:(num # l4_file_decl642) list`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`mid:l4_kdeclaration493 list`;`venv1:l4_venv961`;
                               `final:l4_kdeclaration493 list`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN `venv2:l4_venv961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `venv2:l4_venv961` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_venv_ordered_trans961 THEN EXISTS_TAC `venv1:l4_venv961` THEN ASM_REWRITE_TAC []]);;

let l4_check_file_pure_sound975 = prove
 (`!fuel input batches final.
   (!v. l4_venv_wf966 v ==> l4_defeq_injectivity972 v) /\
   ALL (l4_file_pure_batch975 fuel (l4_file_rows642 input)) batches /\
   l4_check_file642 fuel input batches = L4KAccept491 final ==>
   ?venv'. l4_venv_wf966 venv' /\ l4_venv_sound973 final venv'`,
  REPEAT GEN_TAC THEN
  l4_subst_cases_tac974 (SPEC `input:l4_file_input642` (cases "l4_file_input642")) THEN
  REWRITE_TAC [l4_file_rows642;l4_check_file642] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_env_dis975] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`batches:l4_file_batch642 list`;`fuel:num`;
                 `a6:(num # l4_file_decl642) list`] l4_file_check_batches_pure_sound975) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPECL [`[]:l4_kdeclaration493 list`;`l4_venv_empty961`;`final:l4_kdeclaration493 list`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [l4_pure_const_env_empty975;l4_venv_names_aligned_empty975] THEN
   MATCH_MP_TAC l4_venv_sound_empty973 THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [l4_venv_empty_wf966];
   MESON_TAC []]);;
