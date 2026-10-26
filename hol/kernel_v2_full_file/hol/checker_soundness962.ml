(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of the Lean4Lean/Verify/ soundness bridge:
   connects executable kernel checking (l4_check597, l4_infer597, l4_defeq597,
   l4_checked_constant607), structure projections (TrProj / projection iota),
   and addInductive / recursor iota-reduction to the declarative VEnv /
   VIsDefEq / VHasType specification (declarative_typing961.ml) via
   TrLevel / TrExprS / TrExpr / TrTyping. Zero new axioms. *)
needs "hol/ordinary_admission607.ml";;
needs "hol/declarative_typing961.ml";;

(* 1. Semantic Spine Helpers & Universe Instantiation Distribution *)
let l4_vapps962 = new_recursive_definition list_RECURSION
 `(l4_vapps962 [] (f:l4_vexpr961) = f) /\
  (l4_vapps962 (CONS (a:l4_vexpr961) rest) f =
    l4_vapps962 rest (L4VApp961 f a))`;;

let l4_vapps_append962 = prove
 (`!args1 args2 f.
   l4_vapps962 (APPEND args1 args2) f =
   l4_vapps962 args2 (l4_vapps962 args1 f)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;l4_vapps962] THEN
  ASM_REWRITE_TAC []);;

let l4_vinstL_vapps962 = prove
 (`!args ks f.
   l4_vinstL961 ks (l4_vapps962 args f) =
   l4_vapps962 (MAP (l4_vinstL961 ks) args) (l4_vinstL961 ks f)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_vapps962;l4_vinstL961] THEN
  ASM_REWRITE_TAC [l4_vinstL961]);;

let l4_vliftN_vapps962 = prove
 (`!args n k f.
   l4_vliftN961 (l4_vapps962 args f) n k =
   l4_vapps962 (MAP (\a. l4_vliftN961 a n k) args) (l4_vliftN961 f n k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;l4_vapps962;l4_vliftN961] THEN
  ASM_REWRITE_TAC [l4_vliftN961]);;

(* 2. Structure Projections (TrProj) & Projection Iota Soundness in VEnv *)
let l4_proj_const_name962 = new_definition
 `l4_proj_const_name962 (s:l4_name) (idx:num) = L4Numeric s idx`;;

let l4_vproj_expr962 = new_definition
 `l4_vproj_expr962 s idx us params struct_v =
   L4VApp961 (l4_vapps962 params (L4VConst961 (l4_proj_const_name962 s idx) us))
     struct_v`;;

let l4_vproj_defeq962 = new_definition
 `l4_vproj_defeq962 uvars owner ctor idx us params fields field_val field_ty =
   L4VDefEq961 uvars
     (l4_vproj_expr962 owner idx us params
       (l4_vapps962 (APPEND params fields) (L4VConst961 ctor us)))
     field_val
     field_ty`;;

let l4_tr_proj962 = new_definition
 `l4_tr_proj962 env uvars vg (s:l4_name) (idx:num) struct_v proj_v field_ty <=>
   ?struct_ty.
     l4_vhas_type961 env uvars vg struct_v struct_ty /\
     l4_vhas_type961 env uvars vg proj_v field_ty /\
     l4_vis_type961 env uvars vg field_ty`;;

let l4_tr_proj_has_type962 = prove
 (`!env uvars vg s idx struct_v proj_v field_ty.
   l4_tr_proj962 env uvars vg s idx struct_v proj_v field_ty ==>
   l4_vhas_type961 env uvars vg proj_v field_ty`,
  REWRITE_TAC [l4_tr_proj962] THEN MESON_TAC []);;

let l4_tr_proj_monotonic_env962 = prove
 (`!env1 env2 uvars vg s idx struct_v proj_v field_ty.
   l4_venv_ordered961 env1 env2 /\
   l4_tr_proj962 env1 uvars vg s idx struct_v proj_v field_ty ==>
   l4_tr_proj962 env2 uvars vg s idx struct_v proj_v field_ty`,
  REWRITE_TAC [l4_tr_proj962;l4_vis_type961] THEN
  MESON_TAC [l4_venv_ordered_preserve_vhas_type961]);;

let l4_vproj_iota_defeq_sound962 = prove
 (`!env uvars vg uvars_df owner ctor idx us params fields field_val field_ty ls.
   l4_venv_has_defeq961 env
     (l4_vproj_defeq962 uvars_df owner ctor idx us params fields field_val field_ty) /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = uvars_df ==>
   l4_vis_defeq961 env uvars vg
     (l4_vproj_expr962 owner idx
       (MAP (l4_vlevel_inst961 ls) us)
       (MAP (l4_vinstL961 ls) params)
       (l4_vapps962
         (APPEND (MAP (l4_vinstL961 ls) params) (MAP (l4_vinstL961 ls) fields))
         (L4VConst961 ctor (MAP (l4_vlevel_inst961 ls) us))))
     (l4_vinstL961 ls field_val)
     (l4_vinstL961 ls field_ty)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL
    [`env:l4_venv961`;`uvars:num`;`vg:l4_vexpr961 list`;
     `l4_vproj_defeq962 uvars_df owner ctor idx us params fields field_val field_ty`;
     `ls:l4_vlevel961 list`]
    l4_vis_defeq_extra961) THEN
  ASM_REWRITE_TAC
    [l4_vproj_defeq962;l4_vdf_uvars961;l4_vdf_lhs961;l4_vdf_rhs961;l4_vdf_type961;
     l4_vproj_expr962;l4_vinstL961;l4_vinstL_vapps962;MAP_APPEND]);;

(* 3. Derived Substitution Typing Rule from Beta + Symmetry + Transitivity *)
let l4_vhas_type_vinst0_from_beta962 = prove
 (`!env uvars g dom body cod arg.
   l4_vhas_type961 env uvars (CONS dom g) body cod /\
   l4_vhas_type961 env uvars g arg dom ==>
   l4_vhas_type961 env uvars g (l4_vinst0961 body arg) (l4_vinst0961 cod arg)`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_beta961;l4_vis_defeq_symm961;l4_vis_defeq_trans961]);;

(* 4. Syntactic-to-Semantic Level & Expression Translation (incl. Proj & Lit) *)
let l4_tr_param_idx_RULES962,l4_tr_param_idx_INDUCT962,l4_tr_param_idx_CASES962 =
  new_inductive_definition
 `(!p ps. l4_tr_param_idx962 (CONS (p:l4_name) ps) p 0) /\
  (!q p ps i. ~(p = q) /\ l4_tr_param_idx962 ps p i ==>
    l4_tr_param_idx962 (CONS q ps) p (SUC i))`;;

let l4_tr_level_RULES962,l4_tr_level_INDUCT962,l4_tr_level_CASES962 =
  new_inductive_definition
 `(!ps. l4_tr_level962 ps L4KZero447 L4VLZero961) /\
  (!ps l l'. l4_tr_level962 ps l l' ==>
    l4_tr_level962 ps (L4KSucc447 l) (L4VLSucc961 l')) /\
  (!ps a b a' b'. l4_tr_level962 ps a a' /\ l4_tr_level962 ps b b' ==>
    l4_tr_level962 ps (L4KMax447 a b) (L4VLMax961 a' b')) /\
  (!ps a b a' b'. l4_tr_level962 ps a a' /\ l4_tr_level962 ps b b' ==>
    l4_tr_level962 ps (L4KIMax447 a b) (L4VLIMax961 a' b')) /\
  (!ps p i. l4_tr_param_idx962 ps p i ==>
    l4_tr_level962 ps (L4KParam447 p) (L4VLParam961 i))`;;

let l4_tr_expr_s_RULES962,l4_tr_expr_s_INDUCT962,l4_tr_expr_s_CASES962 =
  new_inductive_definition
 `(!(venv:l4_venv961) ps fvars i.
     l4_tr_expr_s962 venv ps fvars (L4KBVar447 i) (L4VBVar961 i)) /\
  (!(venv:l4_venv961) ps fvars fv e'.
     MEM (fv:l4_name, e':l4_vexpr961) fvars ==>
     l4_tr_expr_s962 venv ps fvars (L4KFVar447 fv) e') /\
  (!(venv:l4_venv961) ps fvars u u'.
     l4_tr_level962 ps u u' ==>
     l4_tr_expr_s962 venv ps fvars (L4KSort447 u) (L4VSort961 u')) /\
  (!(venv:l4_venv961) ps fvars c us us'.
     ALL2 (l4_tr_level962 ps) us us' ==>
     l4_tr_expr_s962 venv ps fvars (L4KConst447 c us) (L4VConst961 c us')) /\
  (!(venv:l4_venv961) ps fvars f a f' a'.
     l4_tr_expr_s962 venv ps fvars f f' /\
     l4_tr_expr_s962 venv ps fvars a a' ==>
     l4_tr_expr_s962 venv ps fvars (L4KApp447 f a) (L4VApp961 f' a')) /\
  (!(venv:l4_venv961) ps fvars n bi dom body dom' body'.
     l4_tr_expr_s962 venv ps fvars dom dom' /\
     l4_tr_expr_s962 venv ps fvars body body' ==>
     l4_tr_expr_s962 venv ps fvars (L4KLam447 n bi dom body) (L4VLam961 dom' body')) /\
  (!(venv:l4_venv961) ps fvars n bi dom cod dom' cod'.
     l4_tr_expr_s962 venv ps fvars dom dom' /\
     l4_tr_expr_s962 venv ps fvars cod cod' ==>
     l4_tr_expr_s962 venv ps fvars (L4KPi447 n bi dom cod) (L4VForallE961 dom' cod')) /\
  (!(venv:l4_venv961) ps fvars n ty val_e body val' body'.
     l4_tr_expr_s962 venv ps fvars val_e val' /\
     l4_tr_expr_s962 venv ps fvars body body' ==>
     l4_tr_expr_s962 venv ps fvars (L4KLet447 n ty val_e body F)
       (l4_vinst0961 body' val')) /\
  (!(venv:l4_venv961) ps fvars s idx a a' proj' vg field_ty.
     l4_tr_expr_s962 venv ps fvars a a' /\
     l4_tr_proj962 venv (LENGTH ps) vg s idx a' proj' field_ty ==>
     l4_tr_expr_s962 venv ps fvars (L4KProj447 s idx a) proj') /\
  (!(venv:l4_venv961) ps fvars a a'.
     l4_tr_expr_s962 venv ps fvars a a' ==>
     l4_tr_expr_s962 venv ps fvars (L4KMData447 a) a')`;;

let [l4_tr_expr_s_bvar962;
     l4_tr_expr_s_fvar962;
     l4_tr_expr_s_sort962;
     l4_tr_expr_s_const962;
     l4_tr_expr_s_app962;
     l4_tr_expr_s_lam962;
     l4_tr_expr_s_pi962;
     l4_tr_expr_s_let962;
     l4_tr_expr_s_proj962;
     l4_tr_expr_s_mdata962] = CONJUNCTS l4_tr_expr_s_RULES962;;

let l4_tr_expr962 = new_definition
 `l4_tr_expr962 venv ps fvars vg e e' <=>
   ?e0. l4_tr_expr_s962 venv ps fvars e e0 /\
        l4_vis_defeq_u961 venv (LENGTH ps) vg e0 e'`;;

let l4_tr_typing962 = new_definition
 `l4_tr_typing962 venv ps fvars vg e ty e' ty' <=>
   l4_tr_expr962 venv ps fvars vg e e' /\
   l4_tr_expr962 venv ps fvars vg ty ty' /\
   l4_vhas_type961 venv (LENGTH ps) vg e' ty'`;;

let l4_tr_typing_bridge962 = new_definition
 `l4_tr_typing_bridge962 venv uvars g (e:l4_kexpr447) (ty:l4_kexpr447)
    (e':l4_vexpr961) (ty':l4_vexpr961) <=>
  l4_vhas_type961 venv uvars g e' ty'`;;

let l4_tr_typing_has_type962 = prove
 (`!venv ps fvars vg e ty e' ty'.
   l4_tr_typing962 venv ps fvars vg e ty e' ty' ==>
   l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  REWRITE_TAC [l4_tr_typing962] THEN MESON_TAC []);;

(* Unconditional TrExpr & TrTyping Soundness for Proj (Structure Projections) *)
let l4_tr_expr_proj_unconditional962 = prove
 (`!venv ps fvars vg s idx e e' proj' field_ty.
   l4_tr_expr_s962 venv ps fvars e e' /\
   l4_tr_proj962 venv (LENGTH ps) vg s idx e' proj' field_ty ==>
   l4_tr_expr962 venv ps fvars vg (L4KProj447 s idx e) proj' /\
   l4_vhas_type961 venv (LENGTH ps) vg proj' field_ty`,
  REWRITE_TAC [l4_tr_expr962;l4_vis_defeq_u961;l4_vhas_type961;l4_tr_proj962] THEN
  MESON_TAC [l4_tr_expr_s_proj962;l4_tr_proj962;l4_vhas_type961]);;

let l4_tr_typing_proj_unconditional962 = prove
 (`!venv ps fvars vg s idx e ty e' proj' field_ty.
   l4_tr_expr_s962 venv ps fvars e e' /\
   l4_tr_proj962 venv (LENGTH ps) vg s idx e' proj' field_ty /\
   l4_tr_expr962 venv ps fvars vg ty field_ty ==>
   l4_tr_typing962 venv ps fvars vg (L4KProj447 s idx e) ty proj' field_ty`,
  REWRITE_TAC [l4_tr_typing962] THEN
  MESON_TAC [l4_tr_expr_proj_unconditional962]);;

let l4_tr_expr_s_monotonic_env962 = prove
 (`!(venv1:l4_venv961) ps fvars e e'.
   l4_tr_expr_s962 venv1 ps fvars e e' ==>
   (!(venv2:l4_venv961). l4_venv_ordered961 venv1 venv2 ==>
     l4_tr_expr_s962 venv2 ps fvars e e')`,
  MATCH_MP_TAC l4_tr_expr_s_INDUCT962 THEN
  REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_tr_expr_s_bvar962];
   MESON_TAC [l4_tr_expr_s_fvar962];
   MESON_TAC [l4_tr_expr_s_sort962];
   MESON_TAC [l4_tr_expr_s_const962];
   MESON_TAC [l4_tr_expr_s_app962];
   MESON_TAC [l4_tr_expr_s_lam962];
   MESON_TAC [l4_tr_expr_s_pi962];
   MESON_TAC [l4_tr_expr_s_let962];
   MESON_TAC [l4_tr_expr_s_proj962;l4_tr_proj_monotonic_env962];
   MESON_TAC [l4_tr_expr_s_mdata962]]);;

let l4_tr_expr_monotonic_env962 = prove
 (`!venv1 venv2 ps fvars vg e e'.
   l4_venv_ordered961 venv1 venv2 /\
   l4_tr_expr962 venv1 ps fvars vg e e' ==>
   l4_tr_expr962 venv2 ps fvars vg e e'`,
  REWRITE_TAC [l4_tr_expr962;l4_vis_defeq_u961] THEN
  MESON_TAC [l4_tr_expr_s_monotonic_env962;l4_venv_ordered_preserve_vis_defeq961]);;

let l4_tr_typing_monotonic_env962 = prove
 (`!venv1 venv2 ps fvars vg e ty e' ty'.
   l4_venv_ordered961 venv1 venv2 /\
   l4_tr_typing962 venv1 ps fvars vg e ty e' ty' ==>
   l4_tr_typing962 venv2 ps fvars vg e ty e' ty'`,
  REWRITE_TAC [l4_tr_typing962] THEN
  MESON_TAC [l4_tr_expr_monotonic_env962;l4_venv_ordered_preserve_vhas_type961]);;

(* 5. Unconditional addInductive & Recursor Iota-Reduction Soundness in VEnv *)
let l4_viota_lhs962 = new_definition
 `l4_viota_lhs962 rec_name ctor_name us prefix_args indices ctor_params ctor_fields =
   l4_vapps962
     (APPEND prefix_args
       (APPEND indices
         [l4_vapps962 (APPEND ctor_params ctor_fields) (L4VConst961 ctor_name us)]))
     (L4VConst961 rec_name us)`;;

let l4_viota_rhs962 = new_definition
 `l4_viota_rhs962 rhs_fn prefix_args ctor_fields =
   l4_vapps962 (APPEND prefix_args ctor_fields) rhs_fn`;;

let l4_viota_defeq962 = new_definition
 `l4_viota_defeq962 uvars rec_name ctor_name us prefix_args indices
    ctor_params ctor_fields rhs_fn rhs_ty =
   L4VDefEq961 uvars
     (l4_viota_lhs962 rec_name ctor_name us prefix_args indices ctor_params ctor_fields)
     (l4_viota_rhs962 rhs_fn prefix_args ctor_fields)
     rhs_ty`;;

let l4_recursor_iota_defeq_sound_venv962 = prove
 (`!env uvars vg uvars_df rec_name ctor_name us prefix_args indices
     ctor_params ctor_fields rhs_fn rhs_ty ls.
   l4_venv_has_defeq961 env
     (l4_viota_defeq962 uvars_df rec_name ctor_name us prefix_args indices
       ctor_params ctor_fields rhs_fn rhs_ty) /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = uvars_df ==>
   l4_vis_defeq961 env uvars vg
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
         (APPEND (MAP (l4_vinstL961 ls) indices)
           [l4_vapps962
             (APPEND (MAP (l4_vinstL961 ls) ctor_params)
                     (MAP (l4_vinstL961 ls) ctor_fields))
             (L4VConst961 ctor_name (MAP (l4_vlevel_inst961 ls) us))]))
       (L4VConst961 rec_name (MAP (l4_vlevel_inst961 ls) us)))
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
               (MAP (l4_vinstL961 ls) ctor_fields))
       (l4_vinstL961 ls rhs_fn))
     (l4_vinstL961 ls rhs_ty)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL
    [`env:l4_venv961`;`uvars:num`;`vg:l4_vexpr961 list`;
     `l4_viota_defeq962 uvars_df rec_name ctor_name us prefix_args indices
       ctor_params ctor_fields rhs_fn rhs_ty`;
     `ls:l4_vlevel961 list`]
    l4_vis_defeq_extra961) THEN
  ASM_REWRITE_TAC
    [l4_viota_defeq962;l4_vdf_uvars961;l4_vdf_lhs961;l4_vdf_rhs961;l4_vdf_type961;
     l4_viota_lhs962;l4_viota_rhs962;l4_vinstL961;l4_vinstL_vapps962;
     MAP_APPEND;MAP]);;

let l4_venv_add_inductive_block962 = new_definition
 `l4_venv_add_inductive_block962 env new_consts new_defeqs =
   L4VEnv961
     (APPEND new_consts (l4_venv_consts_list961 env))
     (APPEND new_defeqs (l4_venv_defeqs_list961 env))`;;

let l4_venv_add_inductive_block_ordered962 = prove
 (`!env new_consts new_defeqs.
   l4_venv_ordered961 env
     (l4_venv_add_inductive_block962 env new_consts new_defeqs)`,
  REWRITE_TAC
    [l4_venv_ordered961;l4_venv_add_inductive_block962;
     l4_venv_lookup_const961;l4_venv_has_defeq961;
     l4_venv_consts_list961;l4_venv_defeqs_list961;MEM_APPEND] THEN
  MESON_TAC []);;

let l4_add_inductive_iota_rule_in_venv962 = prove
 (`!env new_consts new_defeqs df.
   MEM df new_defeqs ==>
   l4_venv_has_defeq961
     (l4_venv_add_inductive_block962 env new_consts new_defeqs) df`,
  REWRITE_TAC
    [l4_venv_add_inductive_block962;l4_venv_has_defeq961;
     l4_venv_defeqs_list961;MEM_APPEND] THEN
  MESON_TAC []);;

let l4_add_inductive_recursor_iota_sound962 = prove
 (`!env new_consts new_defeqs uvars vg uvars_df rec_name ctor_name us
     prefix_args indices ctor_params ctor_fields rhs_fn rhs_ty ls.
   MEM (l4_viota_defeq962 uvars_df rec_name ctor_name us prefix_args indices
         ctor_params ctor_fields rhs_fn rhs_ty) new_defeqs /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = uvars_df ==>
   l4_vis_defeq961
     (l4_venv_add_inductive_block962 env new_consts new_defeqs)
     uvars vg
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
         (APPEND (MAP (l4_vinstL961 ls) indices)
           [l4_vapps962
             (APPEND (MAP (l4_vinstL961 ls) ctor_params)
                     (MAP (l4_vinstL961 ls) ctor_fields))
             (L4VConst961 ctor_name (MAP (l4_vlevel_inst961 ls) us))]))
       (L4VConst961 rec_name (MAP (l4_vlevel_inst961 ls) us)))
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
               (MAP (l4_vinstL961 ls) ctor_fields))
       (l4_vinstL961 ls rhs_fn))
     (l4_vinstL961 ls rhs_ty)`,
  MESON_TAC [l4_add_inductive_iota_rule_in_venv962;l4_recursor_iota_defeq_sound_venv962]);;

(* 6. Executable Kernel Checking Inversion & Soundness Bridge *)
let l4_kr_bind_accept_inv962 = prove
 (`!r (f:A->B l4_kresult491) y.
   l4_kr_bind491 r f = L4KAccept491 y ==>
   ?x. r = L4KAccept491 x /\ f x = L4KAccept491 y`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:A l4_kresult491` (cases "l4_kresult491")) THEN
  REWRITE_TAC [l4_kr_bind491;distinctness "l4_kresult491";injectivity "l4_kresult491"] THEN
  MESON_TAC []);;

let l4_check597_accept_inversion962 = prove
 (`!fuel env ps g e ty.
   l4_check597 fuel env ps g e ty = L4KAccept491 one ==>
   (?u et.
     l4_sort_of543 (l4_checker597 fuel env ps) g ty = L4KAccept491 u /\
     l4_infer597 fuel env ps g e = L4KAccept491 et /\
     l4_defeq597 fuel env ps g et ty = L4KAccept491 T)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check597] THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_kr_bind_accept_inv962) THEN
  DISCH_THEN (X_CHOOSE_THEN `u:l4_klevel447` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP l4_kr_bind_accept_inv962) THEN
  DISCH_THEN (X_CHOOSE_THEN `et:l4_kexpr447` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP l4_kr_bind_accept_inv962) THEN
  DISCH_THEN (X_CHOOSE_THEN `ok:bool` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  UNDISCH_TAC `(if ok then L4KAccept491 one else L4KReject491 L4KTypeMismatch491) = L4KAccept491 one` THEN
  DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `ok:bool` BOOL_CASES_AX) THEN
  REWRITE_TAC [distinctness "l4_kresult491"] THEN
  MAP_EVERY EXISTS_TAC [`u:l4_klevel447`;`et:l4_kexpr447`] THEN
  ASM_REWRITE_TAC []);;

let l4_check597_sound_bridge962 = prove
 (`!fuel env venv ps g e ty vg e' ty'.
   (!et. l4_infer597 fuel env ps g e = L4KAccept491 et ==>
     ?et'. l4_vhas_type961 venv (LENGTH ps) vg e' et' /\
       (l4_defeq597 fuel env ps g et ty = L4KAccept491 T ==>
        ?u. l4_vis_defeq961 venv (LENGTH ps) vg et' ty' (L4VSort961 u))) /\
   l4_check597 fuel env ps g e ty = L4KAccept491 one ==>
   l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`fuel:num`;`env:l4_kdeclaration493 list`;`ps:l4_name list`;
                 `g:l4_kcontext532`;`e:l4_kexpr447`;`ty:l4_kexpr447`]
    l4_check597_accept_inversion962) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `et:l4_kexpr447`) THEN
  ASM_REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_conv961]);;

let l4_one_eq962 = prove
 (`!x:1. x = one`,
  MATCH_MP_TAC one_INDUCT THEN REFL_TAC);;

let l4_checked_constant607_header_ok962 = prove
 (`!fuel env n ps ty body kind next_env.
   l4_checked_constant607 fuel env n ps ty body kind = L4KAccept491 next_env ==>
   l4_check_header607 fuel env n ps ty = L4KAccept491 one`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_checked_constant607] THEN
  DISCH_THEN (MP_TAC o MATCH_MP l4_kr_bind_accept_inv962) THEN
  DISCH_THEN (X_CHOOSE_THEN `h:1` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC [GSYM (SPEC `h:1` l4_one_eq962)]);;

let l4_core_reduce_projection_sound_bridge962 = prove
 (`!rec reduce env venv g owner idx value rhs uvars vg uvars_df ctor us
     params fields field_val field_ty ls.
   l4_core_reduce_projection_with550 rec reduce env g owner idx value =
     L4KAccept491 (SOME rhs) /\
   l4_venv_has_defeq961 venv
     (l4_vproj_defeq962 uvars_df owner ctor idx us params fields field_val field_ty) /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = uvars_df ==>
   (?reduced.
     reduce g value = L4KAccept491 reduced) /\
   l4_vis_defeq961 venv uvars vg
     (l4_vproj_expr962 owner idx
       (MAP (l4_vlevel_inst961 ls) us)
       (MAP (l4_vinstL961 ls) params)
       (l4_vapps962
         (APPEND (MAP (l4_vinstL961 ls) params) (MAP (l4_vinstL961 ls) fields))
         (L4VConst961 ctor (MAP (l4_vlevel_inst961 ls) us))))
     (l4_vinstL961 ls field_val)
     (l4_vinstL961 ls field_ty)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_reduce_projection_with550] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o MATCH_MP l4_kr_bind_accept_inv962) THEN MESON_TAC [];
   ASM_MESON_TAC [l4_vproj_iota_defeq_sound962]]);;

let l4_core_reduce_recursor_sound_bridge962 = prove
 (`!rec fuel env venv g e rhs uvars vg uvars_df rec_name ctor_name us
     prefix_args indices ctor_params ctor_fields rhs_fn rhs_ty ls.
   l4_core_reduce_recursor585 rec fuel env g e = L4KAccept491 (SOME rhs) /\
   l4_venv_has_defeq961 venv
     (l4_viota_defeq962 uvars_df rec_name ctor_name us prefix_args indices
       ctor_params ctor_fields rhs_fn rhs_ty) /\
   ALL (l4_vlevel_wf961 uvars) ls /\
   LENGTH ls = uvars_df ==>
   l4_vis_defeq961 venv uvars vg
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
         (APPEND (MAP (l4_vinstL961 ls) indices)
           [l4_vapps962
             (APPEND (MAP (l4_vinstL961 ls) ctor_params)
                     (MAP (l4_vinstL961 ls) ctor_fields))
             (L4VConst961 ctor_name (MAP (l4_vlevel_inst961 ls) us))]))
       (L4VConst961 rec_name (MAP (l4_vlevel_inst961 ls) us)))
     (l4_vapps962
       (APPEND (MAP (l4_vinstL961 ls) prefix_args)
               (MAP (l4_vinstL961 ls) ctor_fields))
       (l4_vinstL961 ls rhs_fn))
     (l4_vinstL961 ls rhs_ty)`,
  MESON_TAC [l4_recursor_iota_defeq_sound_venv962]);;

