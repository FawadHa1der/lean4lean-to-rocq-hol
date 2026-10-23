(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of the Lean4Lean/Verify/ soundness bridge:
   connects executable kernel checking (l4_check597, l4_infer597, l4_defeq597,
   l4_checked_constant607) to the declarative VEnv / VIsDefEq / VHasType
   specification (declarative_typing961.ml) via TrLevel / TrExprS / TrExpr /
   TrTyping. Zero new axioms. *)
needs "hol/ordinary_admission607.ml";;
needs "hol/declarative_typing961.ml";;

(* 1. Derived Substitution Typing Rule from Beta + Symmetry + Transitivity *)
let l4_vhas_type_vinst0_from_beta962 = prove
 (`!env uvars g dom body cod arg.
   l4_vhas_type961 env uvars (CONS dom g) body cod /\
   l4_vhas_type961 env uvars g arg dom ==>
   l4_vhas_type961 env uvars g (l4_vinst0961 body arg) (l4_vinst0961 cod arg)`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_beta961;l4_vis_defeq_symm961;l4_vis_defeq_trans961]);;

(* 2. Syntactic-to-Semantic Level & Expression Translation (Lean4Lean/Verify/Typing/Lemmas.lean) *)
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

let l4_tr_expr_s_monotonic_env962 = prove
 (`!(venv1:l4_venv961) ps fvars e e'.
   l4_tr_expr_s962 venv1 ps fvars e e' ==>
   (!(venv2:l4_venv961). l4_tr_expr_s962 venv2 ps fvars e e')`,
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

(* 3. Executable Kernel Checking Inversion & Soundness Bridge *)
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
