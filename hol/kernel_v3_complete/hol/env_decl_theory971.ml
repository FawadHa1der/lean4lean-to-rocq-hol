(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   HOL Light port of:
   1. Lean4Lean/Theory/VEnv.lean (addConst, addDefEq, contains) and
      Lean4Lean/Theory/VDecl.lean (VConstVal, VDefVal, VInductiveType,
      VInductDecl, VDecl).
   2. Lean4Lean/Theory/Typing/Meta.lean: kernel-checked syntax-directed
      type synthesizer (l4_synth_vhas_type971) over closed/concrete VExprs.
   3. Lean4Lean/Theory/Quot.lean & Lean4Lean/Theory/Typing/QuotLemmas.lean:
      exact semantic constants Eq, Quot, Quot.mk, Quot.lift, Quot.ind,
      quotDefEq, QuotReady, addQuot, l4_add_quot_wf971, lookup theorems, and
      definitional Quotient induction computation l4_quot_ind_iota_defeq971
      derived from l4_vis_defeq_proof_irrel961.
   4. Lean4Lean/Theory/Inductive.lean & InductiveLemmas.lean: constructive
      4-stage semantic inductive declarations (types, constructors, recursors,
      and iota defeqs) and l4_add_induct_wf971 with zero axioms.
   5. Lean4Lean/Theory/Typing/{Env,EnvLemmas}.lean: addConsts, addDefEqs,
      l4_vdecl_wf971, l4_venv_wf_prime971, l4_venv_decls_wf971,
      l4_venv_decls_wf_to_venv_wf971, and unconditional non-vacuity building
      constructive Eq + Quot from l4_venv_empty961.

   Zero new axioms, zero unsound theorem constructors. *)

needs "hol/strong_typing970.ml";;

(* ========================================================================= *)
(* 1. Option Monadic Helpers & Functional VEnv Extension (VEnv.lean)         *)
(* ========================================================================= *)

let l4_opt_map971 = new_recursive_definition option_RECURSION
 `(l4_opt_map971 (f:A->B) NONE = NONE) /\
  (l4_opt_map971 f (SOME x) = SOME (f x))`;;

let l4_opt_bind971 = new_recursive_definition option_RECURSION
 `(l4_opt_bind971 NONE (f:A->B option) = NONE) /\
  (l4_opt_bind971 (SOME x) f = f x)`;;

let l4_opt_bind_eq_some971 = prove
 (`!m (f:A->B option) y.
   l4_opt_bind971 m f = SOME y <=> ?x. m = SOME x /\ f x = SOME y`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `m:A option` (cases "option")) THEN
  REWRITE_TAC [l4_opt_bind971;distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_venv_eta971 = prove
 (`!env. L4VEnv961 (l4_venv_consts_list961 env) (l4_venv_defeqs_list961 env) = env`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `env:l4_venv961` (cases "l4_venv961")) THEN
  REWRITE_TAC [l4_venv_consts_list961;l4_venv_defeqs_list961]);;

let l4_venv_contains971 = new_definition
 `l4_venv_contains971 env name <=> ?ci. l4_venv_lookup_const961 env name ci`;;

let l4_venv_add_const971 = new_definition
 `l4_venv_add_const971 env name ci =
   if l4_venv_contains971 env name then NONE
   else SOME (L4VEnv961 (CONS (name,ci) (l4_venv_consts_list961 env))
                        (l4_venv_defeqs_list961 env))`;;

let l4_venv_add_defeq971 = new_definition
 `l4_venv_add_defeq971 env df =
   L4VEnv961 (l4_venv_consts_list961 env)
             (CONS df (l4_venv_defeqs_list961 env))`;;

let l4_venv_add_const_eq_some971 = prove
 (`!env name ci env'.
   l4_venv_add_const971 env name ci = SOME env' <=>
   ~l4_venv_contains971 env name /\
   env' = L4VEnv961 (CONS (name,ci) (l4_venv_consts_list961 env))
                    (l4_venv_defeqs_list961 env)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_const971] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_venv_add_const_eq_none971 = prove
 (`!env name ci.
   ~l4_venv_contains971 env name ==>
   ?env'. l4_venv_add_const971 env name ci = SOME env'`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [l4_venv_add_const_eq_some971] THEN
  MESON_TAC []);;

let l4_venv_add_const_lookup971 = prove
 (`!env name ci env' n c.
   l4_venv_add_const971 env name ci = SOME env' ==>
   (l4_venv_lookup_const961 env' n c <=>
    (n = name /\ c = ci) \/ l4_venv_lookup_const961 env n c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_const_eq_some971] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM;PAIR_EQ]);;

let l4_venv_add_const_has_defeq971 = prove
 (`!env name ci env' df.
   l4_venv_add_const971 env name ci = SOME env' ==>
   (l4_venv_has_defeq961 env' df <=> l4_venv_has_defeq961 env df)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_const_eq_some971] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_venv_has_defeq961;l4_venv_defeqs_list961]);;

let l4_venv_add_const_self971 = prove
 (`!env name ci env'.
   l4_venv_add_const971 env name ci = SOME env' ==>
   l4_venv_lookup_const961 env' name ci`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_venv961`;`name:l4_name`;`ci:l4_vconstant961`;
                 `env':l4_venv961`;`name:l4_name`;`ci:l4_vconstant961`]
    l4_venv_add_const_lookup971) THEN
  ASM_SIMP_TAC []);;

let l4_venv_add_const_le971 = prove
 (`!env name ci env'.
   l4_venv_add_const971 env name ci = SOME env' ==>
   l4_venv_ordered961 env env'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_venv_ordered961] THEN
  ASM_MESON_TAC [l4_venv_add_const_lookup971;l4_venv_add_const_has_defeq971]);;

let l4_venv_add_const_wf971 = prove
 (`!env name ci env'.
   l4_venv_wf966 env /\
   l4_vconstant_wf966 env ci /\
   l4_venv_add_const971 env name ci = SOME env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `env:l4_venv961` (cases "l4_venv961")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_venv_add_const_eq_some971;l4_venv_contains971;
               l4_venv_consts_list961;l4_venv_defeqs_list961] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [l4_venv_cons_const_ordered966] THEN
  MATCH_MP_TAC l4_venv_wf_const966 THEN ASM_REWRITE_TAC []);;

let l4_venv_add_defeq_lookup971 = prove
 (`!env df n c.
   l4_venv_lookup_const961 (l4_venv_add_defeq971 env df) n c <=>
   l4_venv_lookup_const961 env n c`,
  REWRITE_TAC [l4_venv_add_defeq971;l4_venv_lookup_const961;l4_venv_consts_list961]);;

let l4_venv_add_defeq_has_defeq971 = prove
 (`!env df d.
   l4_venv_has_defeq961 (l4_venv_add_defeq971 env df) d <=>
   d = df \/ l4_venv_has_defeq961 env d`,
  REWRITE_TAC [l4_venv_add_defeq971;l4_venv_has_defeq961;l4_venv_defeqs_list961;MEM]);;

let l4_venv_add_defeq_self971 = prove
 (`!env df. l4_venv_has_defeq961 (l4_venv_add_defeq971 env df) df`,
  REWRITE_TAC [l4_venv_add_defeq_has_defeq971]);;

let l4_venv_add_defeq_le971 = prove
 (`!env df. l4_venv_ordered961 env (l4_venv_add_defeq971 env df)`,
  REWRITE_TAC [l4_venv_ordered961;l4_venv_add_defeq_lookup971;
               l4_venv_add_defeq_has_defeq971] THEN
  MESON_TAC []);;

let l4_venv_add_defeq_wf971 = prove
 (`!env df.
   l4_venv_wf966 env /\ l4_vdefeq_wf966 env df ==>
   l4_venv_wf966 (l4_venv_add_defeq971 env df) /\
   l4_venv_ordered961 env (l4_venv_add_defeq971 env df)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `env:l4_venv961` (cases "l4_venv961")) THEN
  GEN_TAC THEN REWRITE_TAC [l4_venv_add_defeq971;l4_venv_consts_list961;
                            l4_venv_defeqs_list961;l4_venv_cons_defeq_ordered966] THEN
  STRIP_TAC THEN MATCH_MP_TAC l4_venv_wf_defeq966 THEN ASM_REWRITE_TAC []);;

let l4_vconstant_wf_of_is_type971 = prove
 (`!env uvars ty.
   l4_venv_wf966 env /\ l4_vis_type961 env uvars [] ty ==>
   l4_vconstant_wf966 env (L4VConstant961 uvars ty)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vconstant_wf966;l4_vc_uvars961;l4_vc_type961;
               l4_vis_type961;l4_vhas_type961] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [EXISTS_TAC `u:l4_vlevel961` THEN ASM_REWRITE_TAC [];
   MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                  `ty:l4_vexpr961`;`ty:l4_vexpr961`;`L4VSort961 u`]
     l4_vis_defeq_closedN966) THEN
   ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vctx_closed966;LENGTH]]);;

let l4_vconstant_wf_mono971 = prove
 (`!env1 env2 ci.
   l4_venv_ordered961 env1 env2 /\ l4_vconstant_wf966 env1 ci ==>
   l4_vconstant_wf966 env2 ci`,
  REWRITE_TAC [l4_vconstant_wf966] THEN
  MESON_TAC [l4_venv_ordered_preserve_vis_type966]);;

let l4_vdefeq_wf_of_has_type971 = prove
 (`!env uvars lhs rhs ty.
   l4_venv_wf966 env /\
   l4_vhas_type961 env uvars [] lhs ty /\
   l4_vhas_type961 env uvars [] rhs ty ==>
   l4_vdefeq_wf966 env (L4VDefEq961 uvars lhs rhs ty)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vdefeq_wf966;l4_vdf_uvars961;l4_vdf_lhs961;
               l4_vdf_rhs961;l4_vdf_type961;l4_vhas_type961] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `lhs:l4_vexpr961`;`lhs:l4_vexpr961`;`ty:l4_vexpr961`]
    l4_vis_defeq_closedN966) THEN
  MP_TAC (SPECL [`env:l4_venv961`;`uvars:num`;`[]:l4_vexpr961 list`;
                 `rhs:l4_vexpr961`;`rhs:l4_vexpr961`;`ty:l4_vexpr961`]
    l4_vis_defeq_closedN966) THEN
  ASM_SIMP_TAC [l4_venv_wf_closed966;l4_vctx_closed966;LENGTH]);;

let l4_vdefeq_wf_mono971 = prove
 (`!env1 env2 df.
   l4_venv_ordered961 env1 env2 /\ l4_vdefeq_wf966 env1 df ==>
   l4_vdefeq_wf966 env2 df`,
  REWRITE_TAC [l4_vdefeq_wf966] THEN
  MESON_TAC [l4_venv_ordered_preserve_vhas_type961]);;

(* ========================================================================= *)
(* 2. Kernel-Checked Syntax-Directed Type Synthesizer (Typing/Meta.lean)     *)
(* ========================================================================= *)

let l4_vctx_lookup_opt971 = new_recursive_definition list_RECURSION
 `(l4_vctx_lookup_opt971 [] (i:num) = (NONE : l4_vexpr961 option)) /\
  (l4_vctx_lookup_opt971 (CONS a g) i =
    if i = 0 then SOME (l4_vlift961 a)
    else l4_opt_map971 l4_vlift961 (l4_vctx_lookup_opt971 g (i - 1)))`;;

let l4_vlookup_of_opt971 = prove
 (`!g i ty. l4_vctx_lookup_opt971 g i = SOME ty ==> l4_vlookup961 g i ty`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [l4_vctx_lookup_opt971;distinctness "option";FORALL_SIMP];
   INDUCT_TAC THEN GEN_TAC THEN
   REWRITE_TAC [l4_vctx_lookup_opt971;NOT_SUC;SUC_SUB1;injectivity "option"] THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_vlookup_RULES961];
    MP_TAC (ISPEC `l4_vctx_lookup_opt971 t i` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [l4_opt_map971;distinctness "option";injectivity "option"] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]);;

let l4_vhas_type_sort971 = prove
 (`!env uvars g u.
   l4_vlevel_wf961 uvars u ==>
   l4_vhas_type961 env uvars g (L4VSort961 u) (L4VSort961 (L4VLSucc961 u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_sort961 THEN
  ASM_REWRITE_TAC [l4_vlevel_equiv_refl961]);;

let l4_vhas_type_bvar971 = prove
 (`!env uvars g i ty.
   l4_vlookup961 g i ty ==> l4_vhas_type961 env uvars g (L4VBVar961 i) ty`,
  REWRITE_TAC [l4_vhas_type961;l4_vis_defeq_bvar961]);;

let l4_all2_vlevel_equiv_refl_list971 = prove
 (`!ls. ALL2 l4_vlevel_equiv961 ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]);;

let l4_vhas_type_const971 = prove
 (`!env uvars g c ci ls.
   l4_venv_lookup_const961 env c ci /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = l4_vc_uvars961 ci ==>
   l4_vhas_type961 env uvars g (L4VConst961 c ls) (l4_vinstL961 ls (l4_vc_type961 ci))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_const961 THEN
  ASM_REWRITE_TAC [l4_all2_vlevel_equiv_refl_list971]);;

let l4_vhas_type_app971 = prove
 (`!env uvars g f a dom cod.
   l4_vhas_type961 env uvars g f (L4VForallE961 dom cod) /\
   l4_vhas_type961 env uvars g a dom ==>
   l4_vhas_type961 env uvars g (L4VApp961 f a) (l4_vinst0961 cod a)`,
  REWRITE_TAC [l4_vhas_type961;l4_vis_defeq_app961]);;

let l4_vhas_type_lam971 = prove
 (`!env uvars g dom body u cod.
   l4_vhas_type961 env uvars g dom (L4VSort961 u) /\
   l4_vhas_type961 env uvars (CONS dom g) body cod ==>
   l4_vhas_type961 env uvars g (L4VLam961 dom body) (L4VForallE961 dom cod)`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_lam961]);;

let l4_vhas_type_forall971 = prove
 (`!env uvars g dom cod u v.
   l4_vhas_type961 env uvars g dom (L4VSort961 u) /\
   l4_vhas_type961 env uvars (CONS dom g) cod (L4VSort961 v) ==>
   l4_vhas_type961 env uvars g (L4VForallE961 dom cod) (L4VSort961 (L4VLIMax961 u v))`,
  REWRITE_TAC [l4_vhas_type961] THEN MESON_TAC [l4_vis_defeq_forall961]);;

let l4_vis_type_of_has_type_sort971 = prove
 (`!env uvars g ty u.
   l4_vhas_type961 env uvars g ty (L4VSort961 u) ==> l4_vis_type961 env uvars g ty`,
  REWRITE_TAC [l4_vis_type961] THEN MESON_TAC []);;

(* Kernel-checked bottom-up type synthesizer for concrete de Bruijn terms *)
let l4_eval_vexpr_conv971 extra_defs =
  let step =
    REWRITE_CONV
      ([l4_vctx_lookup_opt971;l4_opt_map971;
        l4_vinst0961;l4_vinst961;l4_vinst_var961;
        l4_vlift961;l4_vliftN961;l4_vlift_var961;
        l4_vinstL961;l4_vlevel_inst961;l4_vnth_level961;
        l4_vc_uvars961;l4_vc_type961;
        l4_vdf_uvars961;l4_vdf_lhs961;l4_vdf_rhs961;l4_vdf_type961;
        MAP;LENGTH;ALL;l4_vlevel_wf961] @ extra_defs) THENC
    DEPTH_CONV NUM_RED_CONV in
  REPEATC (CHANGED_CONV step);;

let l4_synth_vhas_type971 extra_defs lookup_thms env_tm uvars_tm g0_tm e0_tm =
  let eval_c = l4_eval_vexpr_conv971 extra_defs in
  let cons_tm = `CONS:l4_vexpr961->l4_vexpr961 list->l4_vexpr961 list` in
  let all_wf_tm =
    mk_comb (`ALL:(l4_vlevel961->bool)->l4_vlevel961 list->bool`,
             mk_comb (`l4_vlevel_wf961`, uvars_tm)) in
  let rec synth g_tm e_tm =
    let hd_tm, args = strip_comb e_tm in
    let cname = fst (dest_const hd_tm) in
    match (cname, args) with
    | ("L4VSort961", [u]) ->
        let wf_th = EQT_ELIM (eval_c (list_mk_comb (`l4_vlevel_wf961`, [uvars_tm; u]))) in
        MP (SPECL [env_tm; uvars_tm; g_tm; u] l4_vhas_type_sort971) wf_th
    | ("L4VBVar961", [i]) ->
        let eq_th = eval_c (list_mk_comb (`l4_vctx_lookup_opt971`, [g_tm; i])) in
        let ty = rand (rand (concl eq_th)) in
        let lk_th = MP (SPECL [g_tm; i; ty] l4_vlookup_of_opt971) eq_th in
        MP (SPECL [env_tm; uvars_tm; g_tm; i; ty] l4_vhas_type_bvar971) lk_th
    | ("L4VConst961", [c; ls]) ->
        let lk_th =
          List.find (fun th ->
            let _, [_; c'; _] = strip_comb (concl th) in c' = c) lookup_thms in
        let _, [_; _; ci] = strip_comb (concl lk_th) in
        let wf_ls_th = EQT_ELIM (eval_c (mk_comb (all_wf_tm, ls))) in
        let len_th =
          EQT_ELIM (eval_c (mk_eq (mk_comb (`LENGTH:l4_vlevel961 list->num`, ls),
                                   mk_comb (`l4_vc_uvars961`, ci)))) in
        let raw_th =
          MP (SPECL [env_tm; uvars_tm; g_tm; c; ci; ls] l4_vhas_type_const971)
             (CONJ lk_th (CONJ wf_ls_th len_th)) in
        CONV_RULE (RAND_CONV eval_c) raw_th
    | ("L4VApp961", [f; a]) ->
        let th_f = synth g_tm f in
        let th_a = synth g_tm a in
        let _, [dom; cod] = strip_comb (rand (concl th_f)) in
        let raw_th =
          MP (SPECL [env_tm; uvars_tm; g_tm; f; a; dom; cod] l4_vhas_type_app971)
             (CONJ th_f th_a) in
        CONV_RULE (RAND_CONV eval_c) raw_th
    | ("L4VLam961", [dom; body]) ->
        let th_dom = synth g_tm dom in
        let u = rand (rand (concl th_dom)) in
        let g' = list_mk_comb (cons_tm, [dom; g_tm]) in
        let th_body = synth g' body in
        let cod = rand (concl th_body) in
        MP (SPECL [env_tm; uvars_tm; g_tm; dom; body; u; cod] l4_vhas_type_lam971)
           (CONJ th_dom th_body)
    | ("L4VForallE961", [dom; cod]) ->
        let th_dom = synth g_tm dom in
        let u = rand (rand (concl th_dom)) in
        let g' = list_mk_comb (cons_tm, [dom; g_tm]) in
        let th_cod = synth g' cod in
        let v = rand (rand (concl th_cod)) in
        MP (SPECL [env_tm; uvars_tm; g_tm; dom; cod; u; v] l4_vhas_type_forall971)
           (CONJ th_dom th_cod)
    | _ -> failwith ("l4_synth_vhas_type971: unexpected constructor " ^ cname) in
  let e_eq = eval_c e0_tm in
  let th_norm = synth g0_tm (rand (concl e_eq)) in
  CONV_RULE (LAND_CONV (K (SYM e_eq))) th_norm;;

(* ========================================================================= *)
(* 3. Semantic Declarations (Lean4Lean/Theory/VDecl.lean)                    *)
(* ========================================================================= *)

let l4_vconst_val_INDUCT971,l4_vconst_val_RECURSION971 = define_type
 "l4_vconst_val971 = L4VConstVal971 l4_name l4_vconstant961";;

let l4_vcv_name971 = new_recursive_definition l4_vconst_val_RECURSION971
 `l4_vcv_name971 (L4VConstVal971 n ci) = n`;;

let l4_vcv_const971 = new_recursive_definition l4_vconst_val_RECURSION971
 `l4_vcv_const971 (L4VConstVal971 n ci) = ci`;;

let l4_vcv_uvars971 = new_definition
 `l4_vcv_uvars971 cv = l4_vc_uvars961 (l4_vcv_const971 cv)`;;

let l4_vcv_type971 = new_definition
 `l4_vcv_type971 cv = l4_vc_type961 (l4_vcv_const971 cv)`;;

let l4_vconst_val_wf971 = new_definition
 `l4_vconst_val_wf971 env cv <=> l4_vconstant_wf966 env (l4_vcv_const971 cv)`;;

let l4_vdef_val_INDUCT971,l4_vdef_val_RECURSION971 = define_type
 "l4_vdef_val971 = L4VDefVal971 l4_name l4_vconstant961 l4_vexpr961";;

let l4_vdv_name971 = new_recursive_definition l4_vdef_val_RECURSION971
 `l4_vdv_name971 (L4VDefVal971 n ci v) = n`;;

let l4_vdv_const971 = new_recursive_definition l4_vdef_val_RECURSION971
 `l4_vdv_const971 (L4VDefVal971 n ci v) = ci`;;

let l4_vdv_value971 = new_recursive_definition l4_vdef_val_RECURSION971
 `l4_vdv_value971 (L4VDefVal971 n ci v) = v`;;

let l4_vdv_to_const_val971 = new_definition
 `l4_vdv_to_const_val971 dv = L4VConstVal971 (l4_vdv_name971 dv) (l4_vdv_const971 dv)`;;

let l4_vdv_uvars971 = new_definition
 `l4_vdv_uvars971 dv = l4_vc_uvars961 (l4_vdv_const971 dv)`;;

let l4_vdv_type971 = new_definition
 `l4_vdv_type971 dv = l4_vc_type961 (l4_vdv_const971 dv)`;;

let l4_vdv_to_defeq971 = new_definition
 `l4_vdv_to_defeq971 dv =
   L4VDefEq961 (l4_vdv_uvars971 dv)
     (L4VConst961 (l4_vdv_name971 dv) (l4_vlevel_params966 (l4_vdv_uvars971 dv)))
     (l4_vdv_value971 dv)
     (l4_vdv_type971 dv)`;;

let l4_vdef_val_wf971 = new_definition
 `l4_vdef_val_wf971 env dv <=>
   l4_vhas_type961 env (l4_vdv_uvars971 dv) [] (l4_vdv_value971 dv) (l4_vdv_type971 dv)`;;

let l4_vdef_val_wf_mono971 = prove
 (`!env1 env2 dv.
   l4_venv_ordered961 env1 env2 /\ l4_vdef_val_wf971 env1 dv ==>
   l4_vdef_val_wf971 env2 dv`,
  REWRITE_TAC [l4_vdef_val_wf971] THEN
  MESON_TAC [l4_venv_ordered_preserve_vhas_type961]);;

let l4_vdef_val_wf_to_const_wf971 = prove
 (`!env dv.
   l4_venv_wf966 env /\ l4_vdef_val_wf971 env dv ==>
   l4_vconstant_wf966 env (l4_vdv_const971 dv)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `dv:l4_vdef_val971` (cases "l4_vdef_val971")) THEN
  STRUCT_CASES_TAC (SPEC `a1:l4_vconstant961` (cases "l4_vconstant961")) THEN
  REWRITE_TAC [l4_vdef_val_wf971;l4_vdv_const971;l4_vdv_uvars971;l4_vdv_type971;
               l4_vdv_value971;l4_vc_uvars961;l4_vc_type961;l4_vhas_type961] THEN
  STRIP_TAC THEN MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`env:l4_venv961`;`a0':num`;`[]:l4_vexpr961 list`;
                 `a2:l4_vexpr961`;`a2:l4_vexpr961`;`a1':l4_vexpr961`]
    l4_vis_defeq_is_type966) THEN
  ASM_SIMP_TAC [l4_vctx_wf966]);;

let l4_vdef_val_to_defeq_wf971 = prove
 (`!env dv.
   l4_venv_wf966 env /\
   l4_venv_lookup_const961 env (l4_vdv_name971 dv) (l4_vdv_const971 dv) /\
   l4_vdef_val_wf971 env dv ==>
   l4_vdefeq_wf966 env (l4_vdv_to_defeq971 dv)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [l4_vdv_to_defeq971] THEN
  MATCH_MP_TAC l4_vdefeq_wf_of_has_type971 THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_vdef_val_wf971]) THEN
  ASM_REWRITE_TAC [l4_vdv_uvars971;l4_vdv_type971] THEN
  MATCH_MP_TAC l4_vhas_type_const0966 THEN ASM_REWRITE_TAC []);;

let l4_vinductive_type_INDUCT971,l4_vinductive_type_RECURSION971 = define_type
 "l4_vinductive_type971 =
    L4VInductiveType971 l4_vconst_val971 (l4_vconst_val971 list)";;

let l4_vit_type971 = new_recursive_definition l4_vinductive_type_RECURSION971
 `l4_vit_type971 (L4VInductiveType971 cv ctors) = cv`;;

let l4_vit_ctors971 = new_recursive_definition l4_vinductive_type_RECURSION971
 `l4_vit_ctors971 (L4VInductiveType971 cv ctors) = ctors`;;

let l4_vinduct_decl_INDUCT971,l4_vinduct_decl_RECURSION971 = define_type
 "l4_vinduct_decl971 =
    L4VInductDecl971 num num (l4_vinductive_type971 list)
                     (l4_vconst_val971 list) (l4_vdefeq961 list)";;

let l4_vid_uvars971 = new_recursive_definition l4_vinduct_decl_RECURSION971
 `l4_vid_uvars971 (L4VInductDecl971 u np tys recs iotas) = u`;;
let l4_vid_nparams971 = new_recursive_definition l4_vinduct_decl_RECURSION971
 `l4_vid_nparams971 (L4VInductDecl971 u np tys recs iotas) = np`;;
let l4_vid_types971 = new_recursive_definition l4_vinduct_decl_RECURSION971
 `l4_vid_types971 (L4VInductDecl971 u np tys recs iotas) = tys`;;
let l4_vid_recs971 = new_recursive_definition l4_vinduct_decl_RECURSION971
 `l4_vid_recs971 (L4VInductDecl971 u np tys recs iotas) = recs`;;
let l4_vid_iotas971 = new_recursive_definition l4_vinduct_decl_RECURSION971
 `l4_vid_iotas971 (L4VInductDecl971 u np tys recs iotas) = iotas`;;

let l4_vdecl_INDUCT971,l4_vdecl_RECURSION971 = define_type
 "l4_vdecl971 = L4VDAxiom971 l4_vconst_val971
              | L4VDDef971 l4_vdef_val971
              | L4VDOpaque971 l4_vdef_val971
              | L4VDExample971 l4_vdef_val971
              | L4VDQuot971
              | L4VDInduct971 l4_vinduct_decl971
              | L4VDMutualDef971 (l4_vdef_val971 list)";;

(* ========================================================================= *)
(* 4. Semantic Quotients & Proof-Irrelevant Quot.ind Iota (Quot.lean)        *)
(* ========================================================================= *)

let l4_eq_name971 = new_definition
 `l4_eq_name971 = L4String L4Anonymous [69;113]`;;

let l4_quot_name971 = new_definition
 `l4_quot_name971 = L4String L4Anonymous [81;117;111;116]`;;

let l4_quot_mk_name971 = new_definition
 `l4_quot_mk_name971 = L4String l4_quot_name971 [109;107]`;;

let l4_quot_lift_name971 = new_definition
 `l4_quot_lift_name971 = L4String l4_quot_name971 [108;105;102;116]`;;

let l4_quot_ind_name971 = new_definition
 `l4_quot_ind_name971 = L4String l4_quot_name971 [105;110;100]`;;

(* Relation telescope type r : BVar 0 -> BVar 0 -> Prop under [alpha : Sort u0] *)
let l4_rel_vtype971 = new_definition
 `l4_rel_vtype971 =
   L4VForallE961 (L4VBVar961 0)
     (L4VForallE961 (L4VBVar961 1) (L4VSort961 L4VLZero961))`;;

(* @Eq.{u0} : {alpha : Sort u0} -> alpha -> alpha -> Prop *)
let l4_eq_vconst971 = new_definition
 `l4_eq_vconst971 =
   L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLParam961 0)) l4_rel_vtype971)`;;

(* @Quot.{u0} : {alpha : Sort u0} -> (alpha -> alpha -> Prop) -> Sort u0 *)
let l4_quot_vconst971 = new_definition
 `l4_quot_vconst971 =
   L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 l4_rel_vtype971 (L4VSort961 (L4VLParam961 0))))`;;

(* @Quot.mk.{u0} : {alpha : Sort u0} -> (r : alpha -> alpha -> Prop) -> alpha -> @Quot.{u0} alpha r *)
let l4_quot_mk_vconst971 = new_definition
 `l4_quot_mk_vconst971 =
   L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 l4_rel_vtype971
         (L4VForallE961 (L4VBVar961 1)
           (L4VApp961
             (L4VApp961 (L4VConst961 l4_quot_name971 [L4VLParam961 0]) (L4VBVar961 2))
             (L4VBVar961 1)))))`;;

(* Sanity hypothesis type in [f; beta; r; alpha]:
   forall (a b : alpha), r a b -> @Eq.{u1} beta (f a) (f b) *)
let l4_quot_sanity_vtype971 = new_definition
 `l4_quot_sanity_vtype971 =
   L4VForallE961 (L4VBVar961 3)
     (L4VForallE961 (L4VBVar961 4)
       (L4VForallE961
         (L4VApp961 (L4VApp961 (L4VBVar961 4) (L4VBVar961 1)) (L4VBVar961 0))
         (L4VApp961
           (L4VApp961
             (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 1]) (L4VBVar961 4))
             (L4VApp961 (L4VBVar961 3) (L4VBVar961 2)))
           (L4VApp961 (L4VBVar961 3) (L4VBVar961 1)))))`;;

(* @Quot.lift.{u0, u1} *)
let l4_quot_lift_vconst971 = new_definition
 `l4_quot_lift_vconst971 =
   L4VConstant961 2
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 l4_rel_vtype971
         (L4VForallE961 (L4VSort961 (L4VLParam961 1))
           (L4VForallE961 (L4VForallE961 (L4VBVar961 2) (L4VBVar961 1))
             (L4VForallE961 l4_quot_sanity_vtype971
               (L4VForallE961
                 (L4VApp961
                   (L4VApp961 (L4VConst961 l4_quot_name971 [L4VLParam961 0]) (L4VBVar961 4))
                   (L4VBVar961 3))
                 (L4VBVar961 3)))))))`;;

(* @Quot.ind.{u0} *)
let l4_quot_ind_vconst971 = new_definition
 `l4_quot_ind_vconst971 =
   L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 l4_rel_vtype971
         (L4VForallE961
           (L4VForallE961
             (L4VApp961
               (L4VApp961 (L4VConst961 l4_quot_name971 [L4VLParam961 0]) (L4VBVar961 1))
               (L4VBVar961 0))
             (L4VSort961 L4VLZero961))
           (L4VForallE961
             (L4VForallE961 (L4VBVar961 2)
               (L4VApp961 (L4VBVar961 1)
                 (L4VApp961
                   (L4VApp961
                     (L4VApp961 (L4VConst961 l4_quot_mk_name971 [L4VLParam961 0]) (L4VBVar961 3))
                     (L4VBVar961 2))
                   (L4VBVar961 0))))
             (L4VForallE961
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_quot_name971 [L4VLParam961 0]) (L4VBVar961 3))
                 (L4VBVar961 2))
               (L4VApp961 (L4VBVar961 2) (L4VBVar961 0)))))))`;;

(* quotDefEq : fun alpha r beta f c a => @Quot.lift alpha r beta f c (@Quot.mk alpha r a) == f a *)
let l4_quot_vdefeq971 = new_definition
 `l4_quot_vdefeq971 =
   L4VDefEq961 2
     (L4VLam961 (L4VSort961 (L4VLParam961 0))
       (L4VLam961 l4_rel_vtype971
         (L4VLam961 (L4VSort961 (L4VLParam961 1))
           (L4VLam961 (L4VForallE961 (L4VBVar961 2) (L4VBVar961 1))
             (L4VLam961 l4_quot_sanity_vtype971
               (L4VLam961 (L4VBVar961 4)
                 (L4VApp961
                   (L4VApp961
                     (L4VApp961
                       (L4VApp961
                         (L4VApp961
                           (L4VApp961
                             (L4VConst961 l4_quot_lift_name971 [L4VLParam961 0; L4VLParam961 1])
                             (L4VBVar961 5))
                           (L4VBVar961 4))
                         (L4VBVar961 3))
                       (L4VBVar961 2))
                     (L4VBVar961 1))
                   (L4VApp961
                     (L4VApp961
                       (L4VApp961 (L4VConst961 l4_quot_mk_name971 [L4VLParam961 0]) (L4VBVar961 5))
                       (L4VBVar961 4))
                     (L4VBVar961 0)))))))))
     (L4VLam961 (L4VSort961 (L4VLParam961 0))
       (L4VLam961 l4_rel_vtype971
         (L4VLam961 (L4VSort961 (L4VLParam961 1))
           (L4VLam961 (L4VForallE961 (L4VBVar961 2) (L4VBVar961 1))
             (L4VLam961 l4_quot_sanity_vtype971
               (L4VLam961 (L4VBVar961 4)
                 (L4VApp961 (L4VBVar961 2) (L4VBVar961 0))))))))
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 l4_rel_vtype971
         (L4VForallE961 (L4VSort961 (L4VLParam961 1))
           (L4VForallE961 (L4VForallE961 (L4VBVar961 2) (L4VBVar961 1))
             (L4VForallE961 l4_quot_sanity_vtype971
               (L4VForallE961 (L4VBVar961 4) (L4VBVar961 3)))))))`;;

let l4_vquot_ready971 = new_definition
 `l4_vquot_ready971 env <=> l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971`;;

let l4_venv_add_quot971 = new_definition
 `l4_venv_add_quot971 env =
   l4_opt_bind971 (l4_venv_add_const971 env l4_quot_name971 l4_quot_vconst971) (\e1.
   l4_opt_bind971 (l4_venv_add_const971 e1 l4_quot_mk_name971 l4_quot_mk_vconst971) (\e2.
   l4_opt_bind971 (l4_venv_add_const971 e2 l4_quot_lift_name971 l4_quot_lift_vconst971) (\e3.
   l4_opt_map971 (\e4. l4_venv_add_defeq971 e4 l4_quot_vdefeq971)
                 (l4_venv_add_const971 e3 l4_quot_ind_name971 l4_quot_ind_vconst971))))`;;

let l4_quot_extra_defs971 =
  [l4_rel_vtype971;l4_quot_sanity_vtype971;
   l4_eq_vconst971;l4_quot_vconst971;l4_quot_mk_vconst971;
   l4_quot_lift_vconst971;l4_quot_ind_vconst971;l4_quot_vdefeq971];;

let l4_eq_vconst_is_type971 = prove
 (`!env. l4_vis_type961 env 1 [] (l4_vc_type961 l4_eq_vconst971)`,
  GEN_TAC THEN
  let th = l4_synth_vhas_type971 l4_quot_extra_defs971 []
             `env:l4_venv961` `1` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_eq_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_quot_vconst_is_type971 = prove
 (`!env. l4_vis_type961 env 1 [] (l4_vc_type961 l4_quot_vconst971)`,
  GEN_TAC THEN
  let th = l4_synth_vhas_type971 l4_quot_extra_defs971 []
             `env:l4_venv961` `1` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_quot_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_quot_mk_vconst_is_type971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 ==>
   l4_vis_type961 env 1 [] (l4_vc_type961 l4_quot_mk_vconst971)`,
  GEN_TAC THEN DISCH_TAC THEN
  let lk_q = ASSUME `l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971` in
  let th = l4_synth_vhas_type971 l4_quot_extra_defs971 [lk_q]
             `env:l4_venv961` `1` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_quot_mk_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_quot_lift_vconst_is_type971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 ==>
   l4_vis_type961 env 2 [] (l4_vc_type961 l4_quot_lift_vconst971)`,
  GEN_TAC THEN STRIP_TAC THEN
  let lk_eq = ASSUME `l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971` in
  let lk_q = ASSUME `l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971` in
  let th = l4_synth_vhas_type971 l4_quot_extra_defs971 [lk_eq; lk_q]
             `env:l4_venv961` `2` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_quot_lift_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_quot_ind_vconst_is_type971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971 ==>
   l4_vis_type961 env 1 [] (l4_vc_type961 l4_quot_ind_vconst971)`,
  GEN_TAC THEN STRIP_TAC THEN
  let lk_q = ASSUME `l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971` in
  let lk_mk = ASSUME `l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971` in
  let th = l4_synth_vhas_type971 l4_quot_extra_defs971 [lk_q; lk_mk]
             `env:l4_venv961` `1` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_quot_ind_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_quot_vdefeq_has_types971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_lift_name971 l4_quot_lift_vconst971 ==>
   l4_vhas_type961 env 2 [] (l4_vdf_lhs961 l4_quot_vdefeq971) (l4_vdf_type961 l4_quot_vdefeq971) /\
   l4_vhas_type961 env 2 [] (l4_vdf_rhs961 l4_quot_vdefeq971) (l4_vdf_type961 l4_quot_vdefeq971)`,
  GEN_TAC THEN STRIP_TAC THEN
  let lk_eq = ASSUME `l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971` in
  let lk_q = ASSUME `l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971` in
  let lk_mk = ASSUME `l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971` in
  let lk_lift = ASSUME `l4_venv_lookup_const961 env l4_quot_lift_name971 l4_quot_lift_vconst971` in
  let lks = [lk_eq; lk_q; lk_mk; lk_lift] in
  let ty_eq = l4_eval_vexpr_conv971 l4_quot_extra_defs971 `l4_vdf_type961 l4_quot_vdefeq971` in
  let th_lhs =
    CONV_RULE (RAND_CONV (K (SYM ty_eq)))
      (l4_synth_vhas_type971 l4_quot_extra_defs971 lks
         `env:l4_venv961` `2` `[]:l4_vexpr961 list` `l4_vdf_lhs961 l4_quot_vdefeq971`) in
  let th_rhs =
    CONV_RULE (RAND_CONV (K (SYM ty_eq)))
      (l4_synth_vhas_type971 l4_quot_extra_defs971 lks
         `env:l4_venv961` `2` `[]:l4_vexpr961 list` `l4_vdf_rhs961 l4_quot_vdefeq971`) in
  ACCEPT_TAC (CONJ th_lhs th_rhs));;

let l4_opt_map_eq_some971 = prove
 (`!(f:A->B) m y. l4_opt_map971 f m = SOME y <=> ?x. m = SOME x /\ y = f x`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `m:A option` (cases "option")) THEN
  REWRITE_TAC [l4_opt_map971;distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_venv_add_quot_inv971 = prove
 (`!env env'.
   l4_venv_add_quot971 env = SOME env' <=>
   ?e1 e2 e3 e4.
     l4_venv_add_const971 env l4_quot_name971 l4_quot_vconst971 = SOME e1 /\
     l4_venv_add_const971 e1 l4_quot_mk_name971 l4_quot_mk_vconst971 = SOME e2 /\
     l4_venv_add_const971 e2 l4_quot_lift_name971 l4_quot_lift_vconst971 = SOME e3 /\
     l4_venv_add_const971 e3 l4_quot_ind_name971 l4_quot_ind_vconst971 = SOME e4 /\
     env' = l4_venv_add_defeq971 e4 l4_quot_vdefeq971`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_quot971;l4_opt_bind_eq_some971] THEN
  BETA_TAC THEN REWRITE_TAC [l4_opt_bind_eq_some971] THEN
  BETA_TAC THEN REWRITE_TAC [l4_opt_bind_eq_some971] THEN
  BETA_TAC THEN REWRITE_TAC [l4_opt_map_eq_some971] THEN
  BETA_TAC THEN MESON_TAC []);;

let l4_add_quot_objs971 = prove
 (`!env env'.
   l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_ordered961 env env' /\
   l4_venv_lookup_const961 env' l4_quot_name971 l4_quot_vconst971 /\
   l4_venv_lookup_const961 env' l4_quot_mk_name971 l4_quot_mk_vconst971 /\
   l4_venv_lookup_const961 env' l4_quot_lift_name971 l4_quot_lift_vconst971 /\
   l4_venv_lookup_const961 env' l4_quot_ind_name971 l4_quot_ind_vconst971 /\
   l4_venv_has_defeq961 env' l4_quot_vdefeq971`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_venv_add_quot_inv971] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l4_venv_ordered961 env e1 /\
                l4_venv_ordered961 e1 e2 /\
                l4_venv_ordered961 e2 e3 /\
                l4_venv_ordered961 e3 e4` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_le971]; ALL_TAC] THEN
  ASM_REWRITE_TAC [l4_venv_add_defeq_self971;l4_venv_add_defeq_lookup971] THEN
  ASM_MESON_TAC [l4_venv_ordered_trans961;l4_venv_add_defeq_le971;
                 l4_venv_add_const_self971;l4_venv_ordered961]);;

let l4_add_quot_quot971 = prove
 (`!env env'. l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_lookup_const961 env' l4_quot_name971 l4_quot_vconst971`,
  MESON_TAC [l4_add_quot_objs971]);;

let l4_add_quot_mk971 = prove
 (`!env env'. l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_lookup_const961 env' l4_quot_mk_name971 l4_quot_mk_vconst971`,
  MESON_TAC [l4_add_quot_objs971]);;

let l4_add_quot_lift971 = prove
 (`!env env'. l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_lookup_const961 env' l4_quot_lift_name971 l4_quot_lift_vconst971`,
  MESON_TAC [l4_add_quot_objs971]);;

let l4_add_quot_ind971 = prove
 (`!env env'. l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_lookup_const961 env' l4_quot_ind_name971 l4_quot_ind_vconst971`,
  MESON_TAC [l4_add_quot_objs971]);;

let l4_add_quot_defeq971 = prove
 (`!env env'. l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_has_defeq961 env' l4_quot_vdefeq971`,
  MESON_TAC [l4_add_quot_objs971]);;

let l4_vconstant_eta971 = prove
 (`!ci. L4VConstant961 (l4_vc_uvars961 ci) (l4_vc_type961 ci) = ci`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `ci:l4_vconstant961` (cases "l4_vconstant961")) THEN
  REWRITE_TAC [l4_vc_uvars961;l4_vc_type961]);;

let l4_vdefeq_eta971 = prove
 (`!df. L4VDefEq961 (l4_vdf_uvars961 df) (l4_vdf_lhs961 df) (l4_vdf_rhs961 df) (l4_vdf_type961 df) = df`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `df:l4_vdefeq961` (cases "l4_vdefeq961")) THEN
  REWRITE_TAC [l4_vdf_uvars961;l4_vdf_lhs961;l4_vdf_rhs961;l4_vdf_type961]);;

let l4_add_quot_wf971 = prove
 (`!env env'.
   l4_venv_wf966 env /\
   l4_vquot_ready971 env /\
   l4_venv_add_quot971 env = SOME env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vquot_ready971;l4_venv_add_quot_inv971] THEN
  STRIP_TAC THEN
  (* Step 1: e1 *)
  SUBGOAL_THEN `l4_vconstant_wf966 env l4_quot_vconst971` ASSUME_TAC THENL
  [SUBST1_TAC (SYM (SPEC `l4_quot_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_quot_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_quot_vconst971;l4_quot_vconst_is_type971];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e1 /\ l4_venv_ordered961 env e1 /\
                l4_venv_lookup_const961 e1 l4_quot_name971 l4_quot_vconst971 /\
                l4_venv_lookup_const961 e1 l4_eq_name971 l4_eq_vconst971`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_add_const_self971;l4_venv_ordered961];
   ALL_TAC] THEN
  (* Step 2: e2 *)
  SUBGOAL_THEN `l4_vconstant_wf966 e1 l4_quot_mk_vconst971` ASSUME_TAC THENL
  [SUBST1_TAC (SYM (SPEC `l4_quot_mk_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_quot_mk_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_quot_mk_vconst971] THEN
   MATCH_MP_TAC l4_quot_mk_vconst_is_type971 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e2 /\ l4_venv_ordered961 e1 e2 /\
                l4_venv_lookup_const961 e2 l4_quot_mk_name971 l4_quot_mk_vconst971 /\
                l4_venv_lookup_const961 e2 l4_quot_name971 l4_quot_vconst971 /\
                l4_venv_lookup_const961 e2 l4_eq_name971 l4_eq_vconst971`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_add_const_self971;l4_venv_ordered961];
   ALL_TAC] THEN
  (* Step 3: e3 *)
  SUBGOAL_THEN `l4_vconstant_wf966 e2 l4_quot_lift_vconst971` ASSUME_TAC THENL
  [SUBST1_TAC (SYM (SPEC `l4_quot_lift_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_quot_lift_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_quot_lift_vconst971] THEN
   MATCH_MP_TAC l4_quot_lift_vconst_is_type971 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e3 /\ l4_venv_ordered961 e2 e3 /\
                l4_venv_lookup_const961 e3 l4_quot_lift_name971 l4_quot_lift_vconst971 /\
                l4_venv_lookup_const961 e3 l4_quot_mk_name971 l4_quot_mk_vconst971 /\
                l4_venv_lookup_const961 e3 l4_quot_name971 l4_quot_vconst971 /\
                l4_venv_lookup_const961 e3 l4_eq_name971 l4_eq_vconst971`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_add_const_self971;l4_venv_ordered961];
   ALL_TAC] THEN
  (* Step 4: e4 *)
  SUBGOAL_THEN `l4_vconstant_wf966 e3 l4_quot_ind_vconst971` ASSUME_TAC THENL
  [SUBST1_TAC (SYM (SPEC `l4_quot_ind_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_quot_ind_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_quot_ind_vconst971] THEN
   MATCH_MP_TAC l4_quot_ind_vconst_is_type971 THEN ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e4 /\ l4_venv_ordered961 e3 e4 /\
                l4_venv_lookup_const961 e4 l4_quot_lift_name971 l4_quot_lift_vconst971 /\
                l4_venv_lookup_const961 e4 l4_quot_mk_name971 l4_quot_mk_vconst971 /\
                l4_venv_lookup_const961 e4 l4_quot_name971 l4_quot_vconst971 /\
                l4_venv_lookup_const961 e4 l4_eq_name971 l4_eq_vconst971`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC [l4_venv_add_const_wf971;l4_venv_ordered961];
   ALL_TAC] THEN
  (* Step 5: defeq *)
  SUBGOAL_THEN `l4_vdefeq_wf966 e4 l4_quot_vdefeq971` ASSUME_TAC THENL
  [MP_TAC (SPEC `e4:l4_venv961` l4_quot_vdefeq_has_types971) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   SUBST1_TAC (SYM (SPEC `l4_quot_vdefeq971` l4_vdefeq_eta971)) THEN
   MATCH_MP_TAC l4_vdefeq_wf_of_has_type971 THEN
   ASM_REWRITE_TAC [l4_quot_vdefeq971;l4_vdf_uvars961] THEN
   ASM_REWRITE_TAC [GSYM l4_quot_vdefeq971];
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`e4:l4_venv961`;`l4_quot_vdefeq971`] l4_venv_add_defeq_wf971) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   ASM_MESON_TAC [l4_venv_ordered_trans961]]);;

(* General de Bruijn unshifting lemma for open telescope instantiation *)
let l4_vinst_vliftN_mid_ind971 = prove
 (`!e c n k v.
   c <= k /\ k <= c + n ==>
   l4_vinst961 (l4_vliftN961 e (SUC n) c) v k = l4_vliftN961 e n c`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vinst961;FORALL_SIMP] THEN REPEAT CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`i:num`;`c:num`;`n:num`;`k:num`;`v:l4_vexpr961`] THEN
   STRIP_TAC THEN REWRITE_TAC [l4_vlift_var961;l4_vinst_var961] THEN
   ASM_CASES_TAC `i < c` THEN ASM_REWRITE_TAC [] THENL
   [SUBGOAL_THEN `i < k` (fun th -> REWRITE_TAC [th]) THEN ASM_ARITH_TAC;
    REWRITE_TAC [l4_vinst_var961] THEN
    SUBGOAL_THEN `~(SUC n + i < k) /\ ~(SUC n + i = k) /\ (SUC n + i) - 1 = n + i`
      (fun th -> REWRITE_TAC [th]) THEN ASM_ARITH_TAC];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN ASM_MESON_TAC [];
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   REPEAT STRIP_TAC THEN REWRITE_TAC [injectivity "l4_vexpr961"] THEN CONJ_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let l4_vinst_vliftN_zero_le971 = prove
 (`!e n k v.
   k <= n ==> l4_vinst961 (l4_vliftN961 e (SUC n) 0) v k = l4_vliftN961 e n 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC l4_vinst_vliftN_mid_ind971 THEN ASM_ARITH_TAC);;

(* Definitional Quotient.ind computation rule derived via proof irrelevance *)
let l4_quot_ind_iota_defeq971 = prove
 (`!env uvars g u alpha r beta h a.
   l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971 /\
   l4_venv_lookup_const961 env l4_quot_ind_name971 l4_quot_ind_vconst971 /\
   l4_vlevel_wf961 uvars u /\
   l4_vhas_type961 env uvars g alpha (L4VSort961 u) /\
   l4_vhas_type961 env uvars g r
     (L4VForallE961 alpha (L4VForallE961 (l4_vlift961 alpha) (L4VSort961 L4VLZero961))) /\
   l4_vhas_type961 env uvars g beta
     (L4VForallE961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_name971 [u]) alpha) r)
                    (L4VSort961 L4VLZero961)) /\
   l4_vhas_type961 env uvars g h
     (L4VForallE961 alpha
       (L4VApp961 (l4_vlift961 beta)
         (L4VApp961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_mk_name971 [u])
           (l4_vlift961 alpha)) (l4_vlift961 r)) (L4VBVar961 0)))) /\
   l4_vhas_type961 env uvars g a alpha ==>
   l4_vis_defeq961 env uvars g
     (L4VApp961
       (L4VApp961
         (L4VApp961
           (L4VApp961
             (L4VApp961 (L4VConst961 l4_quot_ind_name971 [u]) alpha)
             r)
           beta)
         h)
       (L4VApp961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_mk_name971 [u]) alpha) r) a))
     (L4VApp961 h a)
     (L4VApp961 beta
       (L4VApp961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_mk_name971 [u]) alpha) r) a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (fun (asl,w as gl) ->
    let mk_zero_le n k =
      let arith_th = ARITH_RULE
        (mk_conj (mk_binop `(<=):num->num->bool` (mk_small_numeral k) (mk_small_numeral n),
                  mk_eq (mk_small_numeral (n + 1), mk_comb (`SUC`, mk_small_numeral n)))) in
      let le_th, eq_th = CONJ_PAIR arith_th in
      let raw = GEN_ALL (MP (SPECL [`e:l4_vexpr961`; mk_small_numeral n; mk_small_numeral k; `v:l4_vexpr961`]
                               l4_vinst_vliftN_zero_le971) le_th) in
      REWRITE_RULE [SYM eq_th] raw in
    let rws =
      [mk_zero_le 0 0; mk_zero_le 1 0; mk_zero_le 1 1;
       mk_zero_le 2 0; mk_zero_le 2 1; mk_zero_le 2 2; l4_vliftN_zero961] in
    let norm_open_conv =
      REPEATC (CHANGED_CONV
        (REWRITE_CONV ([l4_vinst0961;l4_vinst961;l4_vinst_var961;l4_vlift961;l4_vliftN_zero961] @ rws) THENC
         DEPTH_CONV NUM_RED_CONV THENC
         REWRITE_CONV rws)) in
    let app_step th arg_tm arg_th =
      let arg_th' = CONV_RULE (RAND_CONV norm_open_conv) arg_th in
      let th' = CONV_RULE (RAND_CONV norm_open_conv) th in
      let _, [dom'; cod'] = strip_comb (rand (concl th')) in
      let raw =
        MP (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                   rand (rator (concl th'));arg_tm;dom';cod'] l4_vhas_type_app971)
           (CONJ th' arg_th') in
      CONV_RULE (RAND_CONV norm_open_conv) raw in
    let find_as tm = snd (List.find (fun (_,th) -> concl th = tm) asl) in
    let th_alpha = find_as `l4_vhas_type961 env uvars g alpha (L4VSort961 u)` in
    let th_r = find_as `l4_vhas_type961 env uvars g r (L4VForallE961 alpha (L4VForallE961 (l4_vlift961 alpha) (L4VSort961 L4VLZero961)))` in
    let th_beta = find_as `l4_vhas_type961 env uvars g beta (L4VForallE961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_name971 [u]) alpha) r) (L4VSort961 L4VLZero961))` in
    let th_h = find_as `l4_vhas_type961 env uvars g h (L4VForallE961 alpha (L4VApp961 (l4_vlift961 beta) (L4VApp961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_mk_name971 [u]) (l4_vlift961 alpha)) (l4_vlift961 r)) (L4VBVar961 0))))` in
    let th_a = find_as `l4_vhas_type961 env uvars g a alpha` in
    let const_inst c_tm ci_tm c_def =
      let lk = find_as (list_mk_comb (`l4_venv_lookup_const961`, [`env:l4_venv961`; c_tm; ci_tm])) in
      let wf_ls = EQT_ELIM (REWRITE_CONV [ALL; snd (List.find (fun (_,th) -> concl th = `l4_vlevel_wf961 uvars u`) asl)]
                              `ALL (l4_vlevel_wf961 uvars) [u]`) in
      let len_ls = EQT_ELIM ((REWRITE_CONV [LENGTH; c_def; l4_vc_uvars961] THENC DEPTH_CONV NUM_RED_CONV)
                               (mk_eq (`LENGTH [u:l4_vlevel961]`, mk_comb (`l4_vc_uvars961`, ci_tm)))) in
      let raw = MP (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;c_tm;ci_tm;`[u:l4_vlevel961]`]
                      l4_vhas_type_const971) (CONJ lk (CONJ wf_ls len_ls)) in
      CONV_RULE (RAND_CONV (REWRITE_CONV [c_def;l4_rel_vtype971;l4_vc_type961;l4_vinstL961;MAP;l4_vlevel_inst961;l4_vnth_level961] THENC
                            DEPTH_CONV NUM_RED_CONV THENC norm_open_conv)) raw in
    let th_mk0 = const_inst `l4_quot_mk_name971` `l4_quot_mk_vconst971` l4_quot_mk_vconst971 in
    let th_mk_a = app_step (app_step (app_step th_mk0 `alpha:l4_vexpr961` th_alpha) `r:l4_vexpr961` th_r) `a:l4_vexpr961` th_a in
    let mk_a_tm = `L4VApp961 (L4VApp961 (L4VApp961 (L4VConst961 l4_quot_mk_name971 [u]) alpha) r) a` in
    let th_beta_mk = app_step th_beta mk_a_tm th_mk_a in
    let th_h_a = app_step th_h `a:l4_vexpr961` th_a in
    let th_ind0 = const_inst `l4_quot_ind_name971` `l4_quot_ind_vconst971` l4_quot_ind_vconst971 in
    let th_lhs = app_step (app_step (app_step (app_step (app_step th_ind0 `alpha:l4_vexpr961` th_alpha)
                   `r:l4_vexpr961` th_r) `beta:l4_vexpr961` th_beta) `h:l4_vexpr961` th_h) mk_a_tm th_mk_a in
    let [d_prop; d_lhs; d_rhs] =
      List.map (REWRITE_RULE [l4_vhas_type961]) [th_beta_mk; th_lhs; th_h_a] in
    let res = MP (SPECL [`env:l4_venv961`;`uvars:num`;`g:l4_vexpr961 list`;
                         rand (concl d_lhs); rand (rator (concl d_lhs)); rand (rator (concl d_rhs))]
                    l4_vis_defeq_proof_irrel961)
                 (CONJ d_prop (CONJ d_lhs d_rhs)) in
    ACCEPT_TAC res gl));;

(* ========================================================================= *)
(* 5. Constructive Semantic Inductives (Inductive.lean & InductiveLemmas)    *)
(* ========================================================================= *)

let l4_venv_add_const_vals971 = new_recursive_definition list_RECURSION
 `(l4_venv_add_const_vals971 env [] = SOME env) /\
  (l4_venv_add_const_vals971 env (CONS cv cvs) =
    l4_opt_bind971
      (l4_venv_add_const971 env (l4_vcv_name971 cv) (l4_vcv_const971 cv))
      (\env1. l4_venv_add_const_vals971 env1 cvs))`;;

let l4_venv_add_raw_defeqs971 = new_recursive_definition list_RECURSION
 `(l4_venv_add_raw_defeqs971 env [] = env) /\
  (l4_venv_add_raw_defeqs971 env (CONS df dfs) =
    l4_venv_add_raw_defeqs971 (l4_venv_add_defeq971 env df) dfs)`;;

let l4_venv_add_const_vals_wf971 = prove
 (`!cvs env env'.
   l4_venv_wf966 env /\
   (!cv. MEM cv cvs ==> l4_vconst_val_wf971 env cv) /\
   l4_venv_add_const_vals971 env cvs = SOME env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_const_vals971;injectivity "option"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   REWRITE_TAC [l4_venv_add_const_vals971;l4_opt_bind_eq_some971;MEM] THEN
   BETA_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vconstant_wf966 env (l4_vcv_const971 h)` ASSUME_TAC THENL
   [REWRITE_TAC [GSYM l4_vconst_val_wf971] THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 x /\ l4_venv_ordered961 env x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_const_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 env' /\ l4_venv_ordered961 x env'` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [l4_vconst_val_wf971] THEN
    X_GEN_TAC `cv:l4_vconst_val971` THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_vconstant_wf_mono971 THEN EXISTS_TAC `env:l4_venv961` THEN
    ASM_REWRITE_TAC [GSYM l4_vconst_val_wf971] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_venv_ordered_trans961]]]);;

let l4_venv_add_raw_defeqs_wf971 = prove
 (`!dfs env.
   l4_venv_wf966 env /\
   (!df. MEM df dfs ==> l4_vdefeq_wf966 env df) ==>
   l4_venv_wf966 (l4_venv_add_raw_defeqs971 env dfs) /\
   l4_venv_ordered961 env (l4_venv_add_raw_defeqs971 env dfs)`,
  LIST_INDUCT_TAC THEN GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_raw_defeqs971;l4_venv_ordered_refl961] THEN SIMP_TAC [];
   REWRITE_TAC [l4_venv_add_raw_defeqs971;MEM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vdefeq_wf966 env h` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 (l4_venv_add_defeq971 env h) /\
                 l4_venv_ordered961 env (l4_venv_add_defeq971 env h)`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_defeq_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 (l4_venv_add_raw_defeqs971 (l4_venv_add_defeq971 env h) t) /\
                 l4_venv_ordered961 (l4_venv_add_defeq971 env h)
                   (l4_venv_add_raw_defeqs971 (l4_venv_add_defeq971 env h) t)`
     STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC `df:l4_vdefeq961` THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_vdefeq_wf_mono971 THEN EXISTS_TAC `env:l4_venv961` THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_venv_ordered_trans961]]]);;

let l4_flat971 = new_recursive_definition list_RECURSION
 `(l4_flat971 [] = ([]:A list)) /\
  (l4_flat971 (CONS xs xss) = APPEND xs (l4_flat971 xss))`;;

let l4_vinduct_type_cvs971 = new_definition
 `l4_vinduct_type_cvs971 decl = MAP l4_vit_type971 (l4_vid_types971 decl)`;;

let l4_vinduct_ctor_cvs971 = new_definition
 `l4_vinduct_ctor_cvs971 decl = l4_flat971 (MAP l4_vit_ctors971 (l4_vid_types971 decl))`;;

let l4_venv_add_induct971 = new_definition
 `l4_venv_add_induct971 env decl =
   l4_opt_bind971 (l4_venv_add_const_vals971 env (l4_vinduct_type_cvs971 decl)) (\env1.
   l4_opt_bind971 (l4_venv_add_const_vals971 env1 (l4_vinduct_ctor_cvs971 decl)) (\env2.
   l4_opt_map971 (\env3. l4_venv_add_raw_defeqs971 env3 (l4_vid_iotas971 decl))
                 (l4_venv_add_const_vals971 env2 (l4_vid_recs971 decl))))`;;

(* Constructive staged inductive well-formedness:
   1. Inductive type formers are well-typed in env with uvars = decl.uvars;
   2. Constructors are well-typed in env1 (after adding all inductive types) with uvars = decl.uvars;
   3. Recursors are well-typed in env2 (after adding types and constructors);
   4. Iota reduction equations are well-typed in env3 (after adding recursors). *)
let l4_vinduct_decl_wf971 = new_definition
 `l4_vinduct_decl_wf971 env decl <=>
   ~((l4_vid_types971 decl) = []) /\
   (!cv. MEM cv (l4_vinduct_type_cvs971 decl) ==>
         l4_vcv_uvars971 cv = l4_vid_uvars971 decl /\ l4_vconst_val_wf971 env cv) /\
   (?env1 env2 env3.
      l4_venv_add_const_vals971 env (l4_vinduct_type_cvs971 decl) = SOME env1 /\
      (!cv. MEM cv (l4_vinduct_ctor_cvs971 decl) ==>
            l4_vcv_uvars971 cv = l4_vid_uvars971 decl /\ l4_vconst_val_wf971 env1 cv) /\
      l4_venv_add_const_vals971 env1 (l4_vinduct_ctor_cvs971 decl) = SOME env2 /\
      (!cv. MEM cv (l4_vid_recs971 decl) ==> l4_vconst_val_wf971 env2 cv) /\
      l4_venv_add_const_vals971 env2 (l4_vid_recs971 decl) = SOME env3 /\
      (!df. MEM df (l4_vid_iotas971 decl) ==> l4_vdefeq_wf966 env3 df))`;;

let l4_add_induct_wf971 = prove
 (`!env decl env'.
   l4_venv_wf966 env /\
   l4_vinduct_decl_wf971 env decl /\
   l4_venv_add_induct971 env decl = SOME env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_vinduct_decl_wf971;l4_venv_add_induct971;l4_opt_bind_eq_some971] THEN
  BETA_TAC THEN REWRITE_TAC [l4_opt_bind_eq_some971] THEN
  BETA_TAC THEN REWRITE_TAC [l4_opt_map_eq_some971] THEN
  BETA_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x:l4_venv961 = env1` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `x':l4_venv961 = env2` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `x'':l4_venv961 = env3` SUBST_ALL_TAC THENL
  [ASM_MESON_TAC [injectivity "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 env1 /\ l4_venv_ordered961 env env1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC l4_venv_add_const_vals_wf971 THEN
   EXISTS_TAC `l4_vinduct_type_cvs971 decl` THEN ASM_SIMP_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 env2 /\ l4_venv_ordered961 env1 env2` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC l4_venv_add_const_vals_wf971 THEN
   EXISTS_TAC `l4_vinduct_ctor_cvs971 decl` THEN ASM_SIMP_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 env3 /\ l4_venv_ordered961 env2 env3` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC l4_venv_add_const_vals_wf971 THEN
   EXISTS_TAC `l4_vid_recs971 decl` THEN ASM_SIMP_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (SPECL [`l4_vid_iotas971 decl`;`env3:l4_venv961`] l4_venv_add_raw_defeqs_wf971) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  ASM_MESON_TAC [l4_venv_ordered_trans961]);;

(* ========================================================================= *)
(* 6. Block Extensions & Environment Declaration Traces (Env & EnvLemmas)    *)
(* ========================================================================= *)

let l4_venv_add_consts971 = new_recursive_definition list_RECURSION
 `(l4_venv_add_consts971 env [] = SOME env) /\
  (l4_venv_add_consts971 env (CONS dv dvs) =
    l4_opt_bind971
      (l4_venv_add_const971 env (l4_vdv_name971 dv) (l4_vdv_const971 dv))
      (\env1. l4_venv_add_consts971 env1 dvs))`;;

let l4_venv_add_defeqs971 = new_recursive_definition list_RECURSION
 `(l4_venv_add_defeqs971 env [] = env) /\
  (l4_venv_add_defeqs971 env (CONS dv dvs) =
    l4_venv_add_defeqs971 (l4_venv_add_defeq971 env (l4_vdv_to_defeq971 dv)) dvs)`;;

let l4_nodup971 = new_recursive_definition list_RECURSION
 `(l4_nodup971 ([]:A list) <=> T) /\
  (l4_nodup971 (CONS x xs) <=> ~MEM x xs /\ l4_nodup971 xs)`;;

let l4_venv_add_consts_le971 = prove
 (`!dvs env env'.
   l4_venv_add_consts971 env dvs = SOME env' ==> l4_venv_ordered961 env env'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_consts971;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [l4_venv_ordered_refl961];
   REWRITE_TAC [l4_venv_add_consts971;l4_opt_bind_eq_some971] THEN BETA_TAC THEN
   STRIP_TAC THEN
   ASM_MESON_TAC [l4_venv_add_const_le971;l4_venv_ordered_trans961]]);;

let l4_venv_exists_add_consts971 = prove
 (`!dvs env.
   (!dv. MEM dv dvs ==> ~l4_venv_contains971 env (l4_vdv_name971 dv)) /\
   l4_nodup971 (MAP l4_vdv_name971 dvs) ==>
   ?env'. l4_venv_add_consts971 env dvs = SOME env'`,
  LIST_INDUCT_TAC THEN GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_consts971] THEN MESON_TAC [];
   REWRITE_TAC [MEM;MAP;l4_nodup971;MEM_MAP] THEN STRIP_TAC THEN
   SUBGOAL_THEN `~l4_venv_contains971 env (l4_vdv_name971 h)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []; ALL_TAC] THEN
   MP_TAC (SPECL [`env:l4_venv961`;`l4_vdv_name971 h`;`l4_vdv_const971 h`]
     l4_venv_add_const_eq_none971) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC `env1:l4_venv961`) THEN
   SUBGOAL_THEN `?env2. l4_venv_add_consts971 env1 t = SOME env2`
     (X_CHOOSE_TAC `env2:l4_venv961`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [MEM_MAP] THEN
    X_GEN_TAC `dv:l4_vdef_val971` THEN DISCH_TAC THEN
    REWRITE_TAC [l4_venv_contains971] THEN
    DISCH_THEN (X_CHOOSE_TAC `c0:l4_vconstant961`) THEN
    MP_TAC (SPECL [`env:l4_venv961`;`l4_vdv_name971 h`;`l4_vdv_const971 h`;
                   `env1:l4_venv961`;`l4_vdv_name971 dv`;`c0:l4_vconstant961`]
      l4_venv_add_const_lookup971) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
    [ASM_MESON_TAC [];
     ASM_MESON_TAC [l4_venv_contains971]];
    EXISTS_TAC `env2:l4_venv961` THEN
    ASM_REWRITE_TAC [l4_venv_add_consts971;l4_opt_bind971]]]);;

let l4_venv_add_consts_congr971 = prove
 (`!dvs1 dvs2 env.
   ALL2 (\a b. l4_vdv_to_const_val971 a = l4_vdv_to_const_val971 b) dvs1 dvs2 ==>
   l4_venv_add_consts971 env dvs1 = l4_venv_add_consts971 env dvs2`,
  REWRITE_TAC [l4_vdv_to_const_val971;injectivity "l4_vconst_val971"] THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dvs2:l4_vdef_val971 list` list_CASES) THEN
   REWRITE_TAC [ALL2;l4_venv_add_consts971];
   REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dvs2:l4_vdef_val971 list` list_CASES) THENL
   [REWRITE_TAC [ALL2];
    REWRITE_TAC [ALL2;l4_venv_add_consts971] THEN BETA_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (ISPEC `l4_venv_add_const971 env (l4_vdv_name971 h') (l4_vdv_const971 h')`
      (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [l4_opt_bind971] THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]);;

let l4_venv_add_consts_wf971 = prove
 (`!dvs env env'.
   l4_venv_wf966 env /\
   (!dv. MEM dv dvs ==> l4_vconstant_wf966 env (l4_vdv_const971 dv)) /\
   l4_venv_add_consts971 env dvs = SOME env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_consts971;injectivity "option"] THEN
   STRIP_TAC THEN l4_subst_vars_tac966 THEN ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   REWRITE_TAC [l4_venv_add_consts971;l4_opt_bind_eq_some971;MEM] THEN
   BETA_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vconstant_wf966 env (l4_vdv_const971 h)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 x /\ l4_venv_ordered961 env x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_const_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 env' /\ l4_venv_ordered961 x env'` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC `dv:l4_vdef_val971` THEN DISCH_TAC THEN
    MATCH_MP_TAC l4_vconstant_wf_mono971 THEN EXISTS_TAC `env:l4_venv961` THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
    ASM_MESON_TAC [l4_venv_ordered_trans961]]]);;

let l4_venv_add_consts_constants971 = prove
 (`!dvs env env' dv.
   l4_venv_add_consts971 env dvs = SOME env' /\ MEM dv dvs ==>
   l4_venv_lookup_const961 env' (l4_vdv_name971 dv) (l4_vdv_const971 dv)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC [MEM];
   REWRITE_TAC [l4_venv_add_consts971;l4_opt_bind_eq_some971;MEM] THEN
   BETA_TAC THEN STRIP_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_const_self971;l4_venv_add_consts_le971;l4_venv_ordered961];
    ASM_MESON_TAC []]]);;

let l4_venv_add_defeqs_le971 = prove
 (`!dvs env. l4_venv_ordered961 env (l4_venv_add_defeqs971 env dvs)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC [l4_venv_add_defeqs971;l4_venv_ordered_refl961] THEN
  ASM_MESON_TAC [l4_venv_add_defeq_le971;l4_venv_ordered_trans961]);;

let l4_venv_add_defeqs_wf971 = prove
 (`!dvs env.
   l4_venv_wf966 env /\
   (!dv. MEM dv dvs ==> l4_venv_lookup_const961 env (l4_vdv_name971 dv) (l4_vdv_const971 dv)) /\
   (!dv. MEM dv dvs ==> l4_vdef_val_wf971 env dv) ==>
   l4_venv_wf966 (l4_venv_add_defeqs971 env dvs) /\
   l4_venv_ordered961 env (l4_venv_add_defeqs971 env dvs)`,
  LIST_INDUCT_TAC THEN GEN_TAC THENL
  [REWRITE_TAC [l4_venv_add_defeqs971;l4_venv_ordered_refl961] THEN SIMP_TAC [];
   REWRITE_TAC [l4_venv_add_defeqs971;MEM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_vdefeq_wf966 env (l4_vdv_to_defeq971 h)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vdef_val_to_defeq_wf971 THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 (l4_venv_add_defeq971 env (l4_vdv_to_defeq971 h)) /\
                 l4_venv_ordered961 env (l4_venv_add_defeq971 env (l4_vdv_to_defeq971 h))`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_defeq_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 (l4_venv_add_defeqs971 (l4_venv_add_defeq971 env (l4_vdv_to_defeq971 h)) t)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `l4_venv_add_defeq971 env (l4_vdv_to_defeq971 h)`) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [l4_venv_add_defeq_lookup971] THEN CONJ_TAC THENL
     [X_GEN_TAC `dv:l4_vdef_val971` THEN DISCH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
      X_GEN_TAC `dv:l4_vdef_val971` THEN DISCH_TAC THEN
      MATCH_MP_TAC l4_vdef_val_wf_mono971 THEN EXISTS_TAC `env:l4_venv961` THEN
      ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []];
     SIMP_TAC []];
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [l4_venv_add_defeqs_le971;l4_venv_ordered_trans961]]]);;

(* Inductive VDecl.WF : VEnv -> VDecl -> VEnv -> Prop (Env.lean:18-46) *)
let l4_vdecl_wf_RULES971,l4_vdecl_wf_INDUCT971,l4_vdecl_wf_CASES971 =
  new_inductive_definition
 `(!env cv env'.
     l4_vconst_val_wf971 env cv /\
     l4_venv_add_const971 env (l4_vcv_name971 cv) (l4_vcv_const971 cv) = SOME env' ==>
     l4_vdecl_wf971 env (L4VDAxiom971 cv) env') /\
  (!env dv env'.
     l4_vdef_val_wf971 env dv /\
     l4_venv_add_const971 env (l4_vdv_name971 dv) (l4_vdv_const971 dv) = SOME env' ==>
     l4_vdecl_wf971 env (L4VDDef971 dv) (l4_venv_add_defeq971 env' (l4_vdv_to_defeq971 dv))) /\
  (!env dvs env'.
     (!dv. MEM dv dvs ==> l4_vconstant_wf966 env (l4_vdv_const971 dv)) /\
     l4_venv_add_consts971 env dvs = SOME env' /\
     (!dv. MEM dv dvs ==> l4_vdef_val_wf971 env' dv) ==>
     l4_vdecl_wf971 env (L4VDMutualDef971 dvs) (l4_venv_add_defeqs971 env' dvs)) /\
  (!env dv env'.
     l4_vdef_val_wf971 env dv /\
     l4_venv_add_const971 env (l4_vdv_name971 dv) (l4_vdv_const971 dv) = SOME env' ==>
     l4_vdecl_wf971 env (L4VDOpaque971 dv) env') /\
  (!env dv.
     l4_vdef_val_wf971 env dv ==>
     l4_vdecl_wf971 env (L4VDExample971 dv) env) /\
  (!env env'.
     l4_vquot_ready971 env /\
     l4_venv_add_quot971 env = SOME env' ==>
     l4_vdecl_wf971 env L4VDQuot971 env') /\
  (!env decl env'.
     l4_vinduct_decl_wf971 env decl /\
     l4_venv_add_induct971 env decl = SOME env' ==>
     l4_vdecl_wf971 env (L4VDInduct971 decl) env')`;;

let [l4_vdecl_wf_axiom971;
     l4_vdecl_wf_def971;
     l4_vdecl_wf_mutual_def971;
     l4_vdecl_wf_opaque971;
     l4_vdecl_wf_example971;
     l4_vdecl_wf_quot971;
     l4_vdecl_wf_induct971] = CONJUNCTS l4_vdecl_wf_RULES971;;

let l4_vdecl_wf_preserves_wf_ind971 = prove
 (`!env d env'.
   l4_vdecl_wf971 env d env' ==>
   l4_venv_wf966 env ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  MATCH_MP_TAC l4_vdecl_wf_INDUCT971 THEN REPEAT CONJ_TAC THENL
  [(* axiom *)
   REWRITE_TAC [l4_vconst_val_wf971] THEN MESON_TAC [l4_venv_add_const_wf971];
   (* def *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_vconstant_wf966 env (l4_vdv_const971 dv)` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_vdef_val_wf_to_const_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_venv_wf966 env' /\ l4_venv_ordered961 env env'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_const_wf971]; ALL_TAC] THEN
   SUBGOAL_THEN `l4_vdefeq_wf966 env' (l4_vdv_to_defeq971 dv)` ASSUME_TAC THENL
   [MATCH_MP_TAC l4_vdef_val_to_defeq_wf971 THEN
    ASM_MESON_TAC [l4_venv_add_const_self971;l4_vdef_val_wf_mono971];
    ASM_MESON_TAC [l4_venv_add_defeq_wf971;l4_venv_ordered_trans961]];
   (* mutualDef *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 env' /\ l4_venv_ordered961 env env'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_consts_wf971]; ALL_TAC] THEN
   MP_TAC (SPECL [`dvs:l4_vdef_val971 list`;`env':l4_venv961`] l4_venv_add_defeqs_wf971) THEN
   ANTS_TAC THENL
   [ASM_MESON_TAC [l4_venv_add_consts_constants971];
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [l4_venv_ordered_trans961]];
   (* opaque *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
   ASM_MESON_TAC [l4_vdef_val_wf_to_const_wf971;l4_venv_add_const_wf971];
   (* example *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [l4_venv_ordered_refl961];
   (* quot *)
   MESON_TAC [l4_add_quot_wf971];
   (* induct *)
   MESON_TAC [l4_add_induct_wf971]]);;

let l4_vdecl_wf_preserves_wf971 = prove
 (`!env d env'.
   l4_venv_wf966 env /\ l4_vdecl_wf971 env d env' ==>
   l4_venv_wf966 env' /\ l4_venv_ordered961 env env'`,
  MESON_TAC [l4_vdecl_wf_preserves_wf_ind971]);;

let l4_venv_wf_prime_RULES971,l4_venv_wf_prime_INDUCT971,l4_venv_wf_prime_CASES971 =
  new_inductive_definition
 `(l4_venv_wf_prime971 [] l4_venv_empty961) /\
  (!env d ds env'.
     l4_vdecl_wf971 env d env' /\
     l4_venv_wf_prime971 ds env ==>
     l4_venv_wf_prime971 (CONS d ds) env')`;;

let l4_venv_wf_prime_empty971, l4_venv_wf_prime_decl971 =
  match CONJUNCTS l4_venv_wf_prime_RULES971 with
  | [c1;c2] -> (c1,c2)
  | _ -> failwith "l4_venv_wf_prime_RULES971: unexpected arity";;

let l4_venv_decls_wf971 = new_definition
 `l4_venv_decls_wf971 env <=> ?ds. l4_venv_wf_prime971 ds env`;;

let l4_venv_wf_prime_to_venv_wf971 = prove
 (`!ds env. l4_venv_wf_prime971 ds env ==> l4_venv_wf966 env`,
  MATCH_MP_TAC l4_venv_wf_prime_INDUCT971 THEN
  REWRITE_TAC [l4_venv_empty_wf966] THEN
  MESON_TAC [l4_vdecl_wf_preserves_wf971]);;

let l4_venv_decls_wf_to_venv_wf971 = prove
 (`!env. l4_venv_decls_wf971 env ==> l4_venv_wf966 env`,
  REWRITE_TAC [l4_venv_decls_wf971] THEN MESON_TAC [l4_venv_wf_prime_to_venv_wf971]);;

(* ========================================================================= *)
(* 7. Constructive Non-Vacuity: Eq Inductive + Quot on l4_venv_empty961      *)
(* ========================================================================= *)

let l4_eq_refl_name971 = new_definition
 `l4_eq_refl_name971 = L4String l4_eq_name971 [114;101;102;108]`;;

let l4_eq_rec_name971 = new_definition
 `l4_eq_rec_name971 = L4String l4_eq_name971 [114;101;99]`;;

let l4_eq_refl_vconst971 = new_definition
 `l4_eq_refl_vconst971 =
   L4VConstant961 1
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 (L4VBVar961 0)
         (L4VApp961
           (L4VApp961
             (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 1))
             (L4VBVar961 0))
           (L4VBVar961 0))))`;;

let l4_eq_rec_vconst971 = new_definition
 `l4_eq_rec_vconst971 =
   L4VConstant961 2
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 (L4VBVar961 0)
         (L4VForallE961
           (L4VForallE961 (L4VBVar961 1)
             (L4VForallE961
               (L4VApp961
                 (L4VApp961
                   (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 2))
                   (L4VBVar961 1))
                 (L4VBVar961 0))
               (L4VSort961 (L4VLParam961 1))))
           (L4VForallE961
             (L4VApp961
               (L4VApp961 (L4VBVar961 0) (L4VBVar961 1))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 2))
                 (L4VBVar961 1)))
             (L4VForallE961 (L4VBVar961 3)
               (L4VForallE961
                 (L4VApp961
                   (L4VApp961
                     (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 4))
                     (L4VBVar961 3))
                   (L4VBVar961 0))
                 (L4VApp961 (L4VApp961 (L4VBVar961 3) (L4VBVar961 1)) (L4VBVar961 0))))))))`;;

let l4_eq_iota_vdefeq971 = new_definition
 `l4_eq_iota_vdefeq971 =
   L4VDefEq961 2
     (L4VLam961 (L4VSort961 (L4VLParam961 0))
       (L4VLam961 (L4VBVar961 0)
         (L4VLam961
           (L4VForallE961 (L4VBVar961 1)
             (L4VForallE961
               (L4VApp961
                 (L4VApp961
                   (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 2))
                   (L4VBVar961 1))
                 (L4VBVar961 0))
               (L4VSort961 (L4VLParam961 1))))
           (L4VLam961
             (L4VApp961
               (L4VApp961 (L4VBVar961 0) (L4VBVar961 1))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 2))
                 (L4VBVar961 1)))
             (L4VApp961
               (L4VApp961
                 (L4VApp961
                   (L4VApp961
                     (L4VApp961
                       (L4VApp961
                         (L4VConst961 l4_eq_rec_name971 [L4VLParam961 0; L4VLParam961 1])
                         (L4VBVar961 3))
                       (L4VBVar961 2))
                     (L4VBVar961 1))
                   (L4VBVar961 0))
                 (L4VBVar961 2))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 3))
                 (L4VBVar961 2)))))))
     (L4VLam961 (L4VSort961 (L4VLParam961 0))
       (L4VLam961 (L4VBVar961 0)
         (L4VLam961
           (L4VForallE961 (L4VBVar961 1)
             (L4VForallE961
               (L4VApp961
                 (L4VApp961
                   (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 2))
                   (L4VBVar961 1))
                 (L4VBVar961 0))
               (L4VSort961 (L4VLParam961 1))))
           (L4VLam961
             (L4VApp961
               (L4VApp961 (L4VBVar961 0) (L4VBVar961 1))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 2))
                 (L4VBVar961 1)))
             (L4VBVar961 0)))))
     (L4VForallE961 (L4VSort961 (L4VLParam961 0))
       (L4VForallE961 (L4VBVar961 0)
         (L4VForallE961
           (L4VForallE961 (L4VBVar961 1)
             (L4VForallE961
               (L4VApp961
                 (L4VApp961
                   (L4VApp961 (L4VConst961 l4_eq_name971 [L4VLParam961 0]) (L4VBVar961 2))
                   (L4VBVar961 1))
                 (L4VBVar961 0))
               (L4VSort961 (L4VLParam961 1))))
           (L4VForallE961
             (L4VApp961
               (L4VApp961 (L4VBVar961 0) (L4VBVar961 1))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 2))
                 (L4VBVar961 1)))
             (L4VApp961
               (L4VApp961 (L4VBVar961 1) (L4VBVar961 2))
               (L4VApp961
                 (L4VApp961 (L4VConst961 l4_eq_refl_name971 [L4VLParam961 0]) (L4VBVar961 3))
                 (L4VBVar961 2)))))))`;;

let l4_eq_induct_decl971 = new_definition
 `l4_eq_induct_decl971 =
   L4VInductDecl971 1 2
     [L4VInductiveType971
        (L4VConstVal971 l4_eq_name971 l4_eq_vconst971)
        [L4VConstVal971 l4_eq_refl_name971 l4_eq_refl_vconst971]]
     [L4VConstVal971 l4_eq_rec_name971 l4_eq_rec_vconst971]
     [l4_eq_iota_vdefeq971]`;;

let l4_eq_induct_extra_defs971 =
  [l4_rel_vtype971;l4_eq_vconst971;l4_eq_refl_vconst971;
   l4_eq_rec_vconst971;l4_eq_iota_vdefeq971];;

let l4_eq_refl_vconst_is_type971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 ==>
   l4_vis_type961 env 1 [] (l4_vc_type961 l4_eq_refl_vconst971)`,
  GEN_TAC THEN DISCH_TAC THEN
  let lk_eq = ASSUME `l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971` in
  let th = l4_synth_vhas_type971 l4_eq_induct_extra_defs971 [lk_eq]
             `env:l4_venv961` `1` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_eq_refl_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_eq_rec_vconst_is_type971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 /\
   l4_venv_lookup_const961 env l4_eq_refl_name971 l4_eq_refl_vconst971 ==>
   l4_vis_type961 env 2 [] (l4_vc_type961 l4_eq_rec_vconst971)`,
  GEN_TAC THEN STRIP_TAC THEN
  let lk_eq = ASSUME `l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971` in
  let lk_rf = ASSUME `l4_venv_lookup_const961 env l4_eq_refl_name971 l4_eq_refl_vconst971` in
  let th = l4_synth_vhas_type971 l4_eq_induct_extra_defs971 [lk_eq; lk_rf]
             `env:l4_venv961` `2` `[]:l4_vexpr961 list`
             `l4_vc_type961 l4_eq_rec_vconst971` in
  ACCEPT_TAC (MATCH_MP l4_vis_type_of_has_type_sort971 th));;

let l4_eq_iota_vdefeq_has_types971 = prove
 (`!env.
   l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 /\
   l4_venv_lookup_const961 env l4_eq_refl_name971 l4_eq_refl_vconst971 /\
   l4_venv_lookup_const961 env l4_eq_rec_name971 l4_eq_rec_vconst971 ==>
   l4_vhas_type961 env 2 [] (l4_vdf_lhs961 l4_eq_iota_vdefeq971) (l4_vdf_type961 l4_eq_iota_vdefeq971) /\
   l4_vhas_type961 env 2 [] (l4_vdf_rhs961 l4_eq_iota_vdefeq971) (l4_vdf_type961 l4_eq_iota_vdefeq971)`,
  GEN_TAC THEN STRIP_TAC THEN
  let lk_eq = ASSUME `l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971` in
  let lk_rf = ASSUME `l4_venv_lookup_const961 env l4_eq_refl_name971 l4_eq_refl_vconst971` in
  let lk_rc = ASSUME `l4_venv_lookup_const961 env l4_eq_rec_name971 l4_eq_rec_vconst971` in
  let lks = [lk_eq; lk_rf; lk_rc] in
  let ty_eq = l4_eval_vexpr_conv971 l4_eq_induct_extra_defs971 `l4_vdf_type961 l4_eq_iota_vdefeq971` in
  let th_lhs =
    CONV_RULE (RAND_CONV (K (SYM ty_eq)))
      (l4_synth_vhas_type971 l4_eq_induct_extra_defs971 lks
         `env:l4_venv961` `2` `[]:l4_vexpr961 list` `l4_vdf_lhs961 l4_eq_iota_vdefeq971`) in
  let th_rhs =
    CONV_RULE (RAND_CONV (K (SYM ty_eq)))
      (l4_synth_vhas_type971 l4_eq_induct_extra_defs971 lks
         `env:l4_venv961` `2` `[]:l4_vexpr961 list` `l4_vdf_rhs961 l4_eq_iota_vdefeq971`) in
  ACCEPT_TAC (CONJ th_lhs th_rhs));;

let l4_names_distinct_helper971 = prove
 (`~(l4_eq_refl_name971 = l4_eq_name971) /\
   ~(l4_eq_rec_name971 = l4_eq_name971) /\
   ~(l4_eq_rec_name971 = l4_eq_refl_name971) /\
   ~(l4_quot_name971 = l4_eq_name971) /\
   ~(l4_quot_name971 = l4_eq_refl_name971) /\
   ~(l4_quot_name971 = l4_eq_rec_name971) /\
   ~(l4_quot_mk_name971 = l4_eq_name971) /\
   ~(l4_quot_mk_name971 = l4_eq_refl_name971) /\
   ~(l4_quot_mk_name971 = l4_eq_rec_name971) /\
   ~(l4_quot_mk_name971 = l4_quot_name971) /\
   ~(l4_quot_lift_name971 = l4_eq_name971) /\
   ~(l4_quot_lift_name971 = l4_eq_refl_name971) /\
   ~(l4_quot_lift_name971 = l4_eq_rec_name971) /\
   ~(l4_quot_lift_name971 = l4_quot_name971) /\
   ~(l4_quot_lift_name971 = l4_quot_mk_name971) /\
   ~(l4_quot_ind_name971 = l4_eq_name971) /\
   ~(l4_quot_ind_name971 = l4_eq_refl_name971) /\
   ~(l4_quot_ind_name971 = l4_eq_rec_name971) /\
   ~(l4_quot_ind_name971 = l4_quot_name971) /\
   ~(l4_quot_ind_name971 = l4_quot_mk_name971) /\
   ~(l4_quot_ind_name971 = l4_quot_lift_name971)`,
  REWRITE_TAC [l4_eq_refl_name971;l4_eq_rec_name971;
               l4_quot_mk_name971;l4_quot_lift_name971;l4_quot_ind_name971;
               l4_eq_name971;l4_quot_name971;
               distinctness "l4_name";injectivity "l4_name";
               NOT_CONS_NIL;injectivity "list"] THEN
  CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC []);;

let l4_eq_quot_nonvacuous971 = prove
 (`?env.
    l4_venv_decls_wf971 env /\
    l4_venv_wf966 env /\
    l4_venv_lookup_const961 env l4_eq_name971 l4_eq_vconst971 /\
    l4_venv_lookup_const961 env l4_quot_name971 l4_quot_vconst971 /\
    l4_venv_lookup_const961 env l4_quot_mk_name971 l4_quot_mk_vconst971 /\
    l4_venv_lookup_const961 env l4_quot_lift_name971 l4_quot_lift_vconst971 /\
    l4_venv_lookup_const961 env l4_quot_ind_name971 l4_quot_ind_vconst971 /\
    l4_venv_has_defeq961 env l4_quot_vdefeq971 /\
    l4_venv_has_defeq961 env l4_eq_iota_vdefeq971`,
  ABBREV_TAC `e1 = L4VEnv961 [(l4_eq_name971, l4_eq_vconst971)] []` THEN
  ABBREV_TAC `e2 = L4VEnv961 [(l4_eq_refl_name971, l4_eq_refl_vconst971);
                              (l4_eq_name971, l4_eq_vconst971)] []` THEN
  ABBREV_TAC `e3 = L4VEnv961 [(l4_eq_rec_name971, l4_eq_rec_vconst971);
                              (l4_eq_refl_name971, l4_eq_refl_vconst971);
                              (l4_eq_name971, l4_eq_vconst971)] []` THEN
  ABBREV_TAC `env_eq = L4VEnv961 [(l4_eq_rec_name971, l4_eq_rec_vconst971);
                                  (l4_eq_refl_name971, l4_eq_refl_vconst971);
                                  (l4_eq_name971, l4_eq_vconst971)]
                                 [l4_eq_iota_vdefeq971]` THEN
  SUBGOAL_THEN
    `l4_venv_add_const_vals971 l4_venv_empty961 (l4_vinduct_type_cvs971 l4_eq_induct_decl971) = SOME e1 /\
     l4_venv_add_const_vals971 e1 (l4_vinduct_ctor_cvs971 l4_eq_induct_decl971) = SOME e2 /\
     l4_venv_add_const_vals971 e2 (l4_vid_recs971 l4_eq_induct_decl971) = SOME e3 /\
     l4_venv_add_induct971 l4_venv_empty961 l4_eq_induct_decl971 = SOME env_eq`
    STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["e1";"e2";"e3";"env_eq"] THEN
   REWRITE_TAC [l4_venv_empty961;l4_eq_induct_decl971;l4_vinduct_type_cvs971;
                l4_vinduct_ctor_cvs971;l4_vid_types971;l4_vid_recs971;l4_vid_iotas971;
                MAP;l4_flat971;APPEND;l4_vit_type971;l4_vit_ctors971;
                l4_venv_add_induct971;l4_venv_add_const_vals971;l4_vcv_name971;l4_vcv_const971;
                l4_venv_add_const971;l4_venv_contains971;l4_venv_lookup_const961;
                l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;PAIR_EQ;
                l4_names_distinct_helper971;EXISTS_SIMP;
                l4_opt_bind971;l4_opt_map971;l4_venv_add_raw_defeqs971;l4_venv_add_defeq971] THEN
   BETA_TAC THEN
   REWRITE_TAC [l4_venv_add_const_vals971;l4_vcv_name971;l4_vcv_const971;
                l4_venv_add_const971;l4_venv_contains971;l4_venv_lookup_const961;
                l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;PAIR_EQ;
                l4_names_distinct_helper971;EXISTS_SIMP;
                l4_opt_bind971;l4_opt_map971;l4_venv_add_raw_defeqs971;l4_venv_add_defeq971] THEN
   BETA_TAC THEN
   REWRITE_TAC [l4_venv_add_const_vals971;l4_opt_bind971;l4_opt_map971;
                l4_venv_add_raw_defeqs971;l4_venv_add_defeq971;
                l4_venv_consts_list961;l4_venv_defeqs_list961];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vconst_val_wf971 l4_venv_empty961 (L4VConstVal971 l4_eq_name971 l4_eq_vconst971)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vconst_val_wf971;l4_vcv_const971] THEN
   SUBST1_TAC (SYM (SPEC `l4_eq_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   REWRITE_TAC [l4_venv_empty_wf966;l4_eq_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_eq_vconst971;l4_eq_vconst_is_type971];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e1` ASSUME_TAC THENL
  [MP_TAC (SPECL [`l4_vinduct_type_cvs971 l4_eq_induct_decl971`;`l4_venv_empty961`;`e1:l4_venv961`]
     l4_venv_add_const_vals_wf971) THEN
   ASM_REWRITE_TAC [l4_venv_empty_wf966;l4_eq_induct_decl971;l4_vinduct_type_cvs971;
                    l4_vid_types971;MAP;l4_vit_type971;MEM] THEN
   ANTS_TAC THENL [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []; SIMP_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vconst_val_wf971 e1 (L4VConstVal971 l4_eq_refl_name971 l4_eq_refl_vconst971)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vconst_val_wf971;l4_vcv_const971] THEN
   SUBST1_TAC (SYM (SPEC `l4_eq_refl_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_eq_refl_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_eq_refl_vconst971] THEN
   MATCH_MP_TAC l4_eq_refl_vconst_is_type971 THEN
   EXPAND_TAC "e1" THEN REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e2` ASSUME_TAC THENL
  [MP_TAC (SPECL [`l4_vinduct_ctor_cvs971 l4_eq_induct_decl971`;`e1:l4_venv961`;`e2:l4_venv961`]
     l4_venv_add_const_vals_wf971) THEN
   ASM_REWRITE_TAC [l4_eq_induct_decl971;l4_vinduct_ctor_cvs971;l4_vid_types971;
                    MAP;l4_flat971;APPEND;l4_vit_ctors971;MEM] THEN
   ANTS_TAC THENL [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []; SIMP_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vconst_val_wf971 e2 (L4VConstVal971 l4_eq_rec_name971 l4_eq_rec_vconst971)`
    ASSUME_TAC THENL
  [REWRITE_TAC [l4_vconst_val_wf971;l4_vcv_const971] THEN
   SUBST1_TAC (SYM (SPEC `l4_eq_rec_vconst971` l4_vconstant_eta971)) THEN
   MATCH_MP_TAC l4_vconstant_wf_of_is_type971 THEN
   ASM_REWRITE_TAC [l4_eq_rec_vconst971;l4_vc_uvars961] THEN
   REWRITE_TAC [GSYM l4_eq_rec_vconst971] THEN
   MATCH_MP_TAC l4_eq_rec_vconst_is_type971 THEN
   EXPAND_TAC "e2" THEN REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_venv_wf966 e3` ASSUME_TAC THENL
  [MP_TAC (SPECL [`l4_vid_recs971 l4_eq_induct_decl971`;`e2:l4_venv961`;`e3:l4_venv961`]
     l4_venv_add_const_vals_wf971) THEN
   ASM_REWRITE_TAC [l4_eq_induct_decl971;l4_vid_recs971;MEM] THEN
   ANTS_TAC THENL [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []; SIMP_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vdefeq_wf966 e3 l4_eq_iota_vdefeq971` ASSUME_TAC THENL
  [MP_TAC (SPEC `e3:l4_venv961` l4_eq_iota_vdefeq_has_types971) THEN
   ANTS_TAC THENL
   [EXPAND_TAC "e3" THEN REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM];
    STRIP_TAC THEN
    SUBST1_TAC (SYM (SPEC `l4_eq_iota_vdefeq971` l4_vdefeq_eta971)) THEN
    MATCH_MP_TAC l4_vdefeq_wf_of_has_type971 THEN
    ASM_REWRITE_TAC [l4_eq_iota_vdefeq971;l4_vdf_uvars961] THEN
    ASM_REWRITE_TAC [GSYM l4_eq_iota_vdefeq971]];
   ALL_TAC] THEN
  SUBGOAL_THEN `l4_vinduct_decl_wf971 l4_venv_empty961 l4_eq_induct_decl971` ASSUME_TAC THENL
  [REWRITE_TAC [l4_vinduct_decl_wf971] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC [l4_eq_induct_decl971;l4_vid_types971;NOT_CONS_NIL];
    GEN_TAC THEN REWRITE_TAC [l4_eq_induct_decl971;l4_vinduct_type_cvs971;
                              l4_vid_types971;l4_vid_uvars971;MAP;l4_vit_type971;MEM] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [l4_vcv_uvars971;l4_vcv_const971;l4_eq_vconst971;l4_vc_uvars961];
    MAP_EVERY EXISTS_TAC [`e1:l4_venv961`;`e2:l4_venv961`;`e3:l4_venv961`] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN REWRITE_TAC [l4_eq_induct_decl971;l4_vinduct_ctor_cvs971;
                               l4_vid_types971;l4_vid_uvars971;MAP;l4_flat971;
                               APPEND;l4_vit_ctors971;MEM] THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC [l4_vcv_uvars971;l4_vcv_const971;l4_eq_refl_vconst971;l4_vc_uvars961];
     GEN_TAC THEN REWRITE_TAC [l4_eq_induct_decl971;l4_vid_recs971;MEM] THEN
     DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [];
     GEN_TAC THEN REWRITE_TAC [l4_eq_induct_decl971;l4_vid_iotas971;MEM] THEN
     DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []]];
   ALL_TAC] THEN
  SUBGOAL_THEN `?env_q. l4_venv_add_quot971 env_eq = SOME env_q`
    (X_CHOOSE_TAC `env_q:l4_venv961`) THENL
  [EXPAND_TAC "env_eq" THEN
   REWRITE_TAC [l4_venv_add_quot971] THEN
   (let step1 =
      [l4_venv_add_const971;l4_venv_contains971;l4_venv_lookup_const961;
       l4_venv_consts_list961;l4_venv_defeqs_list961;MEM;PAIR_EQ;
       l4_names_distinct_helper971;GSYM l4_names_distinct_helper971;
       EXISTS_SIMP] in
    CONV_TAC (BINDER_CONV (LAND_CONV (LAND_CONV (REWRITE_CONV step1)))) THEN
    REWRITE_TAC [l4_opt_bind971] THEN BETA_TAC THEN
    CONV_TAC (BINDER_CONV (LAND_CONV (LAND_CONV (REWRITE_CONV step1)))) THEN
    REWRITE_TAC [l4_opt_bind971] THEN BETA_TAC THEN
    CONV_TAC (BINDER_CONV (LAND_CONV (LAND_CONV (REWRITE_CONV step1)))) THEN
    REWRITE_TAC [l4_opt_bind971] THEN BETA_TAC THEN
    CONV_TAC (BINDER_CONV (LAND_CONV (RAND_CONV (REWRITE_CONV step1)))) THEN
    REWRITE_TAC [l4_opt_map971;l4_venv_add_defeq971;
                 l4_venv_consts_list961;l4_venv_defeqs_list961;injectivity "option"] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [EXISTS_REFL]);
   ALL_TAC] THEN
  EXISTS_TAC `env_q:l4_venv961` THEN
  SUBGOAL_THEN `l4_venv_wf_prime971 [L4VDQuot971; L4VDInduct971 l4_eq_induct_decl971] env_q`
    ASSUME_TAC THENL
  [MATCH_MP_TAC l4_venv_wf_prime_decl971 THEN EXISTS_TAC `env_eq:l4_venv961` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC l4_vdecl_wf_quot971 THEN ASM_REWRITE_TAC [l4_vquot_ready971] THEN
    EXPAND_TAC "env_eq" THEN REWRITE_TAC [l4_venv_lookup_const961;l4_venv_consts_list961;MEM];
    MATCH_MP_TAC l4_venv_wf_prime_decl971 THEN EXISTS_TAC `l4_venv_empty961` THEN
    REWRITE_TAC [l4_venv_wf_prime_empty971] THEN
    MATCH_MP_TAC l4_vdecl_wf_induct971 THEN ASM_REWRITE_TAC []];
   SUBGOAL_THEN `l4_venv_decls_wf971 env_q` ASSUME_TAC THENL
   [REWRITE_TAC [l4_venv_decls_wf971] THEN
    EXISTS_TAC `[L4VDQuot971; L4VDInduct971 l4_eq_induct_decl971]` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`env_eq:l4_venv961`;`env_q:l4_venv961`] l4_add_quot_objs971) THEN
   ASM_SIMP_TAC [l4_venv_decls_wf_to_venv_wf971] THEN STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_lookup_const961 env_eq l4_eq_name971 l4_eq_vconst971 /\
                 l4_venv_has_defeq961 env_eq l4_eq_iota_vdefeq971`
     STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "env_eq" THEN
    REWRITE_TAC [l4_venv_lookup_const961;l4_venv_has_defeq961;
                 l4_venv_consts_list961;l4_venv_defeqs_list961;MEM];
    UNDISCH_TAC `l4_venv_ordered961 env_eq env_q` THEN
    REWRITE_TAC [l4_venv_ordered961] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [l4_venv_decls_wf_to_venv_wf971]]]);;
