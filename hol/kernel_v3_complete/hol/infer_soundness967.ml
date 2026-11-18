(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   STATUS: Non-circular relative soundness of executable type inference
   (l4_infer_step586 in inference586.ml, l4_infer597 in kernel_checker597.ml)
   with respect to declarative typing (l4_vis_defeq961 / l4_vhas_type961 in
   declarative_typing961.ml), mirroring Lean4Lean/Verify/TypeChecker/InferType.lean
   and rocq/InferSoundness.v.

   Unlike checker_soundness962.ml (whose bridge hypothesis l4_tr_typing_bridge962
   already assumes l4_vhas_type961 for the inferred term), nothing here is
   assumed about l4_infer_step586 itself:
   - l4_tr_e967 is a pure syntactic functional translation (l4_kexpr447 ->
     l4_vexpr961 option) with no typing baked in.
   - l4_methods_sound967 constrains only the WHNF and conversion callbacks
     (l4_whnf_method543, l4_defeq_method543, l4_eager_defeq_method543); the
     inference recursion itself is proved sound by structural induction on e.
   - l4_kernel_env_syntactic_bridge967 relates l4_kfind_decl493 to a well-formed
     l4_venv961 (l4_venv_wf966) via syntactic translation of constant types.

   Fragment & open obligation: covers bound variables, sorts, constants,
   application, lambda, Pi, and metadata in checking mode over ordinary bound
   contexts (l4_tr_bctx967). Free variables, let, literals, and projections
   return NONE under l4_tr_e967. Discharging l4_checker_methods_sound967 for the
   concrete fuelled l4_checker597 remains open (see GAP_ANALYSIS.md); non-vacuity
   of the theorem is established unconditionally via l4_syntactic_methods967
   using the real kernel alpha-equality fastpath l4_core_alpha_eq538.
   Zero new axioms. *)

needs "hol/kernel_checker597.ml";;
needs "hol/typing_lemmas966.ml";;

(* ========================================================================= *)
(* 1. Option & Result Combinators and Inversion Equivalences                 *)
(* ========================================================================= *)

let l4_opt_map967 = new_recursive_definition option_RECURSION
 `(l4_opt_map967 (f:A->B) NONE = NONE) /\
  (l4_opt_map967 f (SOME x) = SOME (f x))`;;

let l4_opt_map2967 = new_recursive_definition option_RECURSION
 `(l4_opt_map2967 (f:A->B->C) NONE y = NONE) /\
  (l4_opt_map2967 f (SOME x) y = l4_opt_map967 (f x) y)`;;

let l4_opt_map_eq_some967 = prove
 (`!(f:A->B) ox y.
   l4_opt_map967 f ox = SOME y <=> ?x. ox = SOME x /\ y = f x`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ox:A option` (cases "option")) THEN
  REWRITE_TAC [l4_opt_map967;distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_opt_map2_eq_some967 = prove
 (`!(f:A->B->C) ox oy z.
   l4_opt_map2967 f ox oy = SOME z <=>
   ?x y. ox = SOME x /\ oy = SOME y /\ z = f x y`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ox:A option` (cases "option")) THEN
  REWRITE_TAC [l4_opt_map2967;l4_opt_map_eq_some967;distinctness "option";injectivity "option"] THEN
  MESON_TAC []);;

let l4_kr_bind_accept967 = prove
 (`!r (f:A->B l4_kresult491) y.
   l4_kr_bind491 r f = L4KAccept491 y <=>
   ?x. r = L4KAccept491 x /\ f x = L4KAccept491 y`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:A l4_kresult491` (cases "l4_kresult491")) THEN
  REWRITE_TAC [l4_kr_bind491;distinctness "l4_kresult491";injectivity "l4_kresult491"] THEN
  MESON_TAC []);;

let l4_if_accept967 = prove
 (`!b (x:A) err y.
   (if b then L4KAccept491 x else L4KReject491 err) = L4KAccept491 y <=>
   b /\ x = y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491"]);;

let l4_match_sort_accept967 = prove
 (`!e err v.
   (match e with
    | L4KSort447 u -> L4KAccept491 u
    | _ -> L4KReject491 err) = L4KAccept491 v <=>
   e = L4KSort447 v`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491";
               distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  MESON_TAC []);;

let l4_match_sort_one_accept967 = prove
 (`!e err v.
   (match e with
    | L4KSort447 u -> L4KAccept491 one
    | _ -> L4KReject491 err) = L4KAccept491 v <=>
   ?u. e = L4KSort447 u /\ v = one`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491";
               distinctness "l4_kexpr447";injectivity "l4_kexpr447"] THEN
  MESON_TAC []);;

let l4_match_pi_accept967 = prove
 (`!e (f:l4_name->l4_kbinder447->l4_kexpr447->l4_kexpr447->A l4_kresult491) err y.
   (match e with
    | L4KPi447 n bi dom body -> f n bi dom body
    | _ -> L4KReject491 err) = L4KAccept491 y <=>
   ?n bi dom body. e = L4KPi447 n bi dom body /\ f n bi dom body = L4KAccept491 y`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `e:l4_kexpr447` (cases "l4_kexpr447")) THEN
  REWRITE_TAC [distinctness "l4_kresult491";distinctness "l4_kexpr447";
               injectivity "l4_kexpr447"] THEN
  MESON_TAC []);;

(* ========================================================================= *)
(* 2. Syntactic Functional Translation of Levels and Expressions             *)
(* ========================================================================= *)

let l4_index_of_name967 = new_recursive_definition list_RECURSION
 `(l4_index_of_name967 ([]:l4_name list) (n:l4_name) = NONE) /\
  (l4_index_of_name967 (CONS p ps) n =
    if p = n then SOME 0
    else l4_opt_map967 SUC (l4_index_of_name967 ps n))`;;

let l4_tr_l967 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_tr_l967 ps L4KZero447 = SOME L4VLZero961) /\
  (l4_tr_l967 ps (L4KSucc447 u) = l4_opt_map967 L4VLSucc961 (l4_tr_l967 ps u)) /\
  (l4_tr_l967 ps (L4KMax447 a b) =
    l4_opt_map2967 (\a' b'. L4VLMax961 a' b') (l4_tr_l967 ps a) (l4_tr_l967 ps b)) /\
  (l4_tr_l967 ps (L4KIMax447 a b) =
    l4_opt_map2967 (\a' b'. L4VLIMax961 a' b') (l4_tr_l967 ps a) (l4_tr_l967 ps b)) /\
  (l4_tr_l967 ps (L4KParam447 n) =
    l4_opt_map967 L4VLParam961 (l4_index_of_name967 ps n)) /\
  (l4_tr_l967 ps (L4KLevelMVar447 n) = NONE)`;;

let l4_tr_ls967 = new_recursive_definition list_RECURSION
 `(l4_tr_ls967 ps ([]:l4_klevel447 list) = SOME ([]:l4_vlevel961 list)) /\
  (l4_tr_ls967 ps (CONS u us) =
    l4_opt_map2967 CONS (l4_tr_l967 ps u) (l4_tr_ls967 ps us))`;;

let l4_tr_e967 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_tr_e967 ps (L4KBVar447 i) = SOME (L4VBVar961 i)) /\
  (l4_tr_e967 ps (L4KFVar447 n) = NONE) /\
  (l4_tr_e967 ps (L4KMVar447 n) = NONE) /\
  (l4_tr_e967 ps (L4KSort447 u) = l4_opt_map967 L4VSort961 (l4_tr_l967 ps u)) /\
  (l4_tr_e967 ps (L4KConst447 c us) =
    l4_opt_map967 (L4VConst961 c) (l4_tr_ls967 ps us)) /\
  (l4_tr_e967 ps (L4KApp447 f a) =
    l4_opt_map2967 (\f' a'. L4VApp961 f' a') (l4_tr_e967 ps f) (l4_tr_e967 ps a)) /\
  (l4_tr_e967 ps (L4KLam447 nm bi dom body) =
    l4_opt_map2967 (\dom' body'. L4VLam961 dom' body')
      (l4_tr_e967 ps dom) (l4_tr_e967 ps body)) /\
  (l4_tr_e967 ps (L4KPi447 nm bi dom body) =
    l4_opt_map2967 (\dom' body'. L4VForallE961 dom' body')
      (l4_tr_e967 ps dom) (l4_tr_e967 ps body)) /\
  (l4_tr_e967 ps (L4KLet447 nm ty val_e body nd) = NONE) /\
  (l4_tr_e967 ps (L4KNatLit447 m) = NONE) /\
  (l4_tr_e967 ps (L4KStrLit447 bytes) = NONE) /\
  (l4_tr_e967 ps (L4KProj447 s idx a) = NONE) /\
  (l4_tr_e967 ps (L4KMData447 a) = l4_tr_e967 ps a)`;;

(* ========================================================================= *)
(* 3. Commutation with Lifting, Substitution, and Universe Instantiation     *)
(* ========================================================================= *)

let l4_tr_e_lift967 = prove
 (`!e ps n k e'.
   l4_tr_e967 ps e = SOME e' ==>
   l4_tr_e967 ps (l4_klift447 e n k) = SOME (l4_vliftN961 e' n k)`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [l4_tr_e967;l4_vliftN961;l4_vlift_var961;injectivity "option";injectivity "l4_vexpr961"] THEN
   COND_CASES_TAC THEN ARITH_TAC;
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_klift447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vliftN961] THEN ASM_MESON_TAC [];
   REWRITE_TAC [l4_tr_e967;l4_klift447] THEN MESON_TAC []]);;

let l4_tr_e_subst967 = prove
 (`!e ps k v e' v'.
   l4_tr_e967 ps e = SOME e' /\ l4_tr_e967 ps v = SOME v' ==>
   l4_tr_e967 ps (l4_ksubst447 e k v) = SOME (l4_vinst961 e' v' k)`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;injectivity "option"] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
   REWRITE_TAC [l4_vinst961;l4_vinst_var961] THEN
   REPEAT COND_CASES_TAC THEN REWRITE_TAC [l4_tr_e967] THEN
   TRY ASM_ARITH_TAC THEN ASM_MESON_TAC [l4_tr_e_lift967];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst447;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinst961] THEN ASM_MESON_TAC [];
   REWRITE_TAC [l4_tr_e967;l4_ksubst447] THEN MESON_TAC []]);;

let l4_tr_e_inst967 = prove
 (`!ps body value body' value'.
   l4_tr_e967 ps body = SOME body' /\ l4_tr_e967 ps value = SOME value' ==>
   l4_tr_e967 ps (l4_kinst447 body value) = SOME (l4_vinst0961 body' value')`,
  REWRITE_TAC [l4_kinst447;l4_vinst0961;l4_tr_e_subst967]);;

let l4_index_of_name_lt967 = prove
 (`!ps n i. l4_index_of_name967 ps n = SOME i ==> i < LENGTH ps`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_index_of_name967;LENGTH;distinctness "option"] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN ARITH_TAC;
   REWRITE_TAC [l4_opt_map_eq_some967] THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`n:l4_name`;`x:num`]) THEN
   ASM_REWRITE_TAC [] THEN ARITH_TAC]);;

let l4_mem_index_of_name967 = prove
 (`!ps n. MEM n ps ==> ?i. l4_index_of_name967 ps n = SOME i /\ i < LENGTH ps`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [MEM;l4_index_of_name967;LENGTH] THEN
  COND_CASES_TAC THENL
  [DISCH_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC [injectivity "option"] THEN ARITH_TAC;
   STRIP_TAC THENL
   [ASM_MESON_TAC [];
    FIRST_X_ASSUM (MP_TAC o SPEC `n:l4_name`) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC j` THEN ASM_REWRITE_TAC [l4_opt_map967] THEN ASM_ARITH_TAC]]);;

let l4_tr_ls_length967 = prove
 (`!us ps us'. l4_tr_ls967 ps us = SOME us' ==> LENGTH us' = LENGTH us`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_tr_ls967;l4_opt_map2_eq_some967;injectivity "option"] THENL
  [DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [LENGTH];
   STRIP_TAC THEN ASM_MESON_TAC [LENGTH]]);;

let l4_lookup_level_tr967 = prove
 (`!params us ps us' n i.
   l4_index_of_name967 params n = SOME i /\
   LENGTH us = LENGTH params /\
   l4_tr_ls967 ps us = SOME us' ==>
   l4_tr_l967 ps (l4_klookup_level488 params us n) = SOME (l4_vnth_level961 us' i)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_index_of_name967;distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `us:l4_klevel447 list` (cases "list")) THEN
  REWRITE_TAC [LENGTH;NOT_SUC;SUC_INJ;l4_klookup_level488;NULL;HD;TL;
               l4_tr_ls967;l4_opt_map2_eq_some967] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [l4_vnth_level961];
   REWRITE_TAC [l4_opt_map_eq_some967] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [l4_vnth_level961;NOT_SUC;SUC_SUB1] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

let l4_some_eq967 = prove
 (`!(x:A) y. SOME x = SOME y <=> y = x`,
  REWRITE_TAC [injectivity "option"] THEN MESON_TAC []);;

let l4_accept_eq967 = prove
 (`!(x:A) y. L4KAccept491 x = L4KAccept491 y <=> y = x`,
  REWRITE_TAC [injectivity "l4_kresult491"] THEN MESON_TAC []);;

let l4_tr_l_subst967 = prove
 (`!u ps params us us' v.
   LENGTH us = LENGTH params /\
   l4_tr_ls967 ps us = SOME us' /\
   l4_tr_l967 params u = SOME v ==>
   l4_tr_l967 ps (l4_ksubst_level488 params us u) = SOME (l4_vlevel_inst961 us' v)`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_l967;l4_ksubst_level488;l4_some_eq967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlevel_inst961];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_l967;l4_ksubst_level488;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlevel_inst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_l967;l4_ksubst_level488;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlevel_inst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_l967;l4_ksubst_level488;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlevel_inst961] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_l967;l4_ksubst_level488;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vlevel_inst961] THEN
   MATCH_MP_TAC l4_lookup_level_tr967 THEN ASM_REWRITE_TAC [];
   SIMP_TAC [l4_tr_l967;distinctness "option";l4_forall_t966]]);;

let l4_tr_ls_subst967 = prove
 (`!vs ps params us us' vs'.
   LENGTH us = LENGTH params /\
   l4_tr_ls967 ps us = SOME us' /\
   l4_tr_ls967 params vs = SOME vs' ==>
   l4_tr_ls967 ps (MAP (l4_ksubst_level488 params us) vs) =
   SOME (MAP (l4_vlevel_inst961 us') vs')`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [MAP;l4_tr_ls967;l4_opt_map2_eq_some967;l4_some_eq967] THENL
  [STRIP_TAC THEN ASM_REWRITE_TAC [MAP];
   STRIP_TAC THEN ASM_REWRITE_TAC [MAP] THEN
   SUBGOAL_THEN `l4_tr_l967 ps (l4_ksubst_level488 params us h) =
                 SOME (l4_vlevel_inst961 us' x)` SUBST1_TAC THENL
   [MATCH_MP_TAC l4_tr_l_subst967 THEN ASM_REWRITE_TAC [];
    SUBGOAL_THEN `l4_tr_ls967 ps (MAP (l4_ksubst_level488 params us) t) =
                  SOME (MAP (l4_vlevel_inst961 us') y)` SUBST1_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
     MESON_TAC []]]]);;

let l4_tr_e_subst_levels967 = prove
 (`!e ps params us us' e'.
   LENGTH us = LENGTH params /\
   l4_tr_ls967 ps us = SOME us' /\
   l4_tr_e967 params e = SOME e' ==>
   l4_tr_e967 ps (l4_ksubst_levels488 params us e) = SOME (l4_vinstL961 us' e')`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_some_eq967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961] THEN
   EXISTS_TAC `l4_vlevel_inst961 us' x` THEN REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_tr_l_subst967 THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961] THEN
   EXISTS_TAC `MAP (l4_vlevel_inst961 us') x` THEN REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_tr_ls_subst967 THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961] THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 us' x`;`l4_vinstL961 us' y`] THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961] THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 us' x`;`l4_vinstL961 us' y`] THEN
   ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [l4_vinstL961] THEN
   MAP_EVERY EXISTS_TAC [`l4_vinstL961 us' x`;`l4_vinstL961 us' y`] THEN
   ASM_MESON_TAC [];
   REWRITE_TAC [l4_tr_e967;l4_ksubst_levels488] THEN MESON_TAC []]);;

let l4_ksubst_level_nil967 = prove
 (`!u us. l4_ksubst_level488 [] us u = u`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_level488;l4_klookup_level488] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_map_ksubst_level_nil967 = prove
 (`!vs us. MAP (l4_ksubst_level488 [] us) vs = vs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;l4_ksubst_level_nil967]);;

let l4_ksubst_levels_nil967 = prove
 (`!e us. l4_ksubst_levels488 [] us e = e`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REWRITE_TAC [l4_ksubst_levels488;l4_ksubst_level_nil967;l4_map_ksubst_level_nil967] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let l4_if_nil_ksubst_levels967 = prove
 (`!params us e.
   (if params = [] then e else l4_ksubst_levels488 params us e) =
   l4_ksubst_levels488 params us e`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [l4_ksubst_levels_nil967]);;

let l4_level_wf_tr_l967 = prove
 (`!u ps.
   l4_level_wf528 ps u ==>
   ?u'. l4_tr_l967 ps u = SOME u' /\ l4_vlevel_wf961 (LENGTH ps) u'`,
  MATCH_MP_TAC l4_klevel_INDUCT447 THEN
  REWRITE_TAC [l4_level_wf528;l4_tr_l967;l4_name_mem437] THEN
  REPEAT CONJ_TAC THENL
  [GEN_TAC THEN EXISTS_TAC `L4VLZero961` THEN REWRITE_TAC [l4_vlevel_wf961];
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ps:l4_name list`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VLSucc961 u'` THEN ASM_REWRITE_TAC [l4_opt_map967;l4_vlevel_wf961];
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ps:l4_name list`) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ps:l4_name list`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `b':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VLMax961 a' b'` THEN
   ASM_REWRITE_TAC [l4_opt_map2967;l4_opt_map967;l4_vlevel_wf961];
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ps:l4_name list`) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ps:l4_name list`) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `a':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `b':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VLIMax961 a' b'` THEN
   ASM_REWRITE_TAC [l4_opt_map2967;l4_opt_map967;l4_vlevel_wf961];
   REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP l4_mem_index_of_name967) THEN
   DISCH_THEN (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VLParam961 i` THEN ASM_REWRITE_TAC [l4_opt_map967;l4_vlevel_wf961]]);;

let l4_check_level_tr_l967 = prove
 (`!ps u x.
   l4_check_level528 ps u = L4KAccept491 x ==>
   ?u'. l4_tr_l967 ps u = SOME u' /\ l4_vlevel_wf961 (LENGTH ps) u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_level528] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [distinctness "l4_kresult491"]) THEN
  ASM_SIMP_TAC [l4_level_wf_tr_l967]);;

let l4_check_levels_tr_ls967 = prove
 (`!us ps x.
   l4_check_levels528 ps us = L4KAccept491 x ==>
   ?us'. l4_tr_ls967 ps us = SOME us' /\ ALL (l4_vlevel_wf961 (LENGTH ps)) us'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_check_levels528;l4_tr_ls967;l4_kr_bind_accept967] THENL
  [DISCH_TAC THEN EXISTS_TAC `[]:l4_vlevel961 list` THEN REWRITE_TAC [ALL];
   DISCH_THEN (X_CHOOSE_THEN `y:1` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`ps:l4_name list`;`h:l4_klevel447`;`y:1`] l4_check_level_tr_l967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `u':l4_vlevel961` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`ps:l4_name list`;`x:1`]) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `CONS (u':l4_vlevel961) us'` THEN
   ASM_REWRITE_TAC [l4_opt_map2967;l4_opt_map967;ALL]]);;

(* ========================================================================= *)
(* 4. Bound Context Translation                                              *)
(* ========================================================================= *)

let l4_tr_bctx_RULES967,l4_tr_bctx_INDUCT967,l4_tr_bctx_CASES967 =
  new_inductive_definition
 `(!ps. l4_tr_bctx967 ps [] []) /\
  (!ps ty bs ty' g.
     l4_tr_e967 ps ty = SOME ty' /\ l4_tr_bctx967 ps bs g ==>
     l4_tr_bctx967 ps (CONS (L4KBinding491 ty NONE) bs) (CONS ty' g))`;;

let l4_tr_bctx_nil967,l4_tr_bctx_cons967 = CONJ_PAIR l4_tr_bctx_RULES967;;

let l4_tr_bctx_lookup967 = prove
 (`!ps bs g.
   l4_tr_bctx967 ps bs g ==>
   (!i b. l4_nth_error550 bs i = SOME b ==>
     ?ty'. l4_tr_e967 ps (l4_kbinding_type532 b) = SOME ty' /\
           l4_vlookup961 g i (l4_vliftN961 ty' (SUC i) 0))`,
  MATCH_MP_TAC l4_tr_bctx_INDUCT967 THEN CONJ_TAC THENL
  [REWRITE_TAC [l4_nth_error550;distinctness "option";l4_forall_t966];
   REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC [l4_nth_error550;l4_some_eq967] THEN
    DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `ty':l4_vexpr961` THEN
    ASM_REWRITE_TAC [l4_kbinding_type532;ARITH_RULE `SUC 0 = 1`;
                     GSYM l4_vlift961;l4_vlookup_RULES961];
    REWRITE_TAC [l4_nth_error550;NOT_SUC;SUC_SUB1] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`b:l4_kbinding491`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `t0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t0:l4_vexpr961` THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `l4_vliftN961 t0 (SUC (SUC i)) 0 =
                  l4_vlift961 (l4_vliftN961 t0 (SUC i) 0)` SUBST1_TAC THENL
    [REWRITE_TAC [l4_vlift961;l4_vliftN_comp966;ARITH_RULE `1 + SUC i = SUC (SUC i)`];
     MATCH_MP_TAC (CONJUNCT2 l4_vlookup_RULES961) THEN ASM_REWRITE_TAC []]]]);;

(* ========================================================================= *)
(* 5. Syntactic Environment Bridge and Oracle Specifications                 *)
(* ========================================================================= *)

let l4_decl_kind_supported967 = new_recursive_definition l4_kdecl_kind_RECURSION493
 `(l4_decl_kind_supported967 L4KDAssumption493 <=> T) /\
  (l4_decl_kind_supported967 L4KDDefinition493 <=> T) /\
  (l4_decl_kind_supported967 L4KDTheorem493 <=> T) /\
  (l4_decl_kind_supported967 L4KDOpaque493 <=> T) /\
  (l4_decl_kind_supported967 L4KDUnsupported493 <=> F) /\
  (l4_decl_kind_supported967 (L4KDInductive493 ind) <=> T) /\
  (l4_decl_kind_supported967 (L4KDConstructor493 ctor) <=> T) /\
  (l4_decl_kind_supported967 (L4KDRecursor493 recd) <=> T) /\
  (l4_decl_kind_supported967 (L4KDPrimitive493 p) <=> T) /\
  (l4_decl_kind_supported967 (L4KDQuotient493 q) <=> T) /\
  (l4_decl_kind_supported967 (L4KDUnsafe493 role) <=> F) /\
  (l4_decl_kind_supported967 L4KDPartial493 <=> F)`;;

let l4_kernel_env_syntactic_bridge967 = new_definition
 `l4_kernel_env_syntactic_bridge967 (env:l4_kdeclaration493 list) (venv:l4_venv961) <=>
   l4_venv_wf966 venv /\
   (!n d.
      l4_kfind_decl493 env n = SOME d /\
      l4_decl_kind_supported967 (l4_kdecl_kind493 d) ==>
      ?ci. l4_venv_lookup_const961 venv n ci /\
           l4_vc_uvars961 ci = LENGTH (l4_kdecl_params493 d) /\
           l4_tr_e967 (l4_kdecl_params493 d) (l4_kdecl_type493 d) =
             SOME (l4_vc_type961 ci))`;;

let l4_whnf_sound967 = new_definition
 `l4_whnf_sound967 venv ps (whnf:l4_kcontext532->l4_kexpr447->l4_kexpr447 l4_kresult491) <=>
   !g vg t t' t_v v_ty.
     l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
     l4_vctx_wf966 venv (LENGTH ps) vg /\
     whnf g t = L4KAccept491 t' /\
     l4_tr_e967 ps t = SOME t_v /\
     l4_vhas_type961 venv (LENGTH ps) vg t_v v_ty ==>
     ?t_v'. l4_tr_e967 ps t' = SOME t_v' /\
            l4_vis_defeq961 venv (LENGTH ps) vg t_v t_v' v_ty`;;

let l4_defeq_types_sound967 = new_definition
 `l4_defeq_types_sound967 venv ps
    (deq:l4_kcontext532->l4_kexpr447->l4_kexpr447->bool l4_kresult491) <=>
   !g vg a b a_v b_v.
     l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
     l4_vctx_wf966 venv (LENGTH ps) vg /\
     deq g a b = L4KAccept491 T /\
     l4_tr_e967 ps a = SOME a_v /\
     l4_tr_e967 ps b = SOME b_v /\
     l4_vis_type961 venv (LENGTH ps) vg a_v /\
     l4_vis_type961 venv (LENGTH ps) vg b_v ==>
     ?u. l4_vis_defeq961 venv (LENGTH ps) vg a_v b_v (L4VSort961 u)`;;

let l4_methods_sound967 = new_definition
 `l4_methods_sound967 venv ps rec <=>
   l4_whnf_sound967 venv ps (l4_whnf_method543 rec) /\
   l4_defeq_types_sound967 venv ps (l4_defeq_method543 rec) /\
   l4_defeq_types_sound967 venv ps (l4_eager_defeq_method543 rec)`;;

let l4_application_type_defeq_sound967 = prove
 (`!venv ps rec g vg arg dom aty dom_v aty_v.
   l4_methods_sound967 venv ps rec /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_application_type_defeq543 rec g arg dom aty = L4KAccept491 T /\
   l4_tr_e967 ps dom = SOME dom_v /\
   l4_tr_e967 ps aty = SOME aty_v /\
   l4_vis_type961 venv (LENGTH ps) vg dom_v /\
   l4_vis_type961 venv (LENGTH ps) vg aty_v ==>
   ?u. l4_vis_defeq961 venv (LENGTH ps) vg dom_v aty_v (L4VSort961 u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_methods_sound967;l4_application_type_defeq543] THEN
  COND_CASES_TAC THEN REWRITE_TAC [l4_defeq_types_sound967] THEN MESON_TAC []);;

(* ========================================================================= *)
(* 6. Non-Circular Soundness of l4_infer_step586                             *)
(* ========================================================================= *)

let l4_whnf_retype967 = prove
 (`!venv ps rec g vg e_v t t_v t'.
   l4_venv_wf966 venv /\
   l4_methods_sound967 venv ps rec /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_vhas_type961 venv (LENGTH ps) vg e_v t_v /\
   l4_tr_e967 ps t = SOME t_v /\
   l4_whnf_method543 rec g t = L4KAccept491 t' ==>
   ?t_v'. l4_tr_e967 ps t' = SOME t_v' /\
          l4_vhas_type961 venv (LENGTH ps) vg e_v t_v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`vg:l4_vexpr961 list`;
                 `e_v:l4_vexpr961`;`e_v:l4_vexpr961`;`t_v:l4_vexpr961`]
    l4_vis_defeq_is_type966) THEN
  ASM_REWRITE_TAC [GSYM l4_vhas_type961;l4_vis_type961] THEN
  DISCH_THEN (X_CHOOSE_TAC `w:l4_vlevel961`) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [l4_methods_sound967]) THEN
  UNDISCH_TAC `l4_whnf_sound967 venv ps (l4_whnf_method543 rec) /\
               l4_defeq_types_sound967 venv ps (l4_defeq_method543 rec) /\
               l4_defeq_types_sound967 venv ps (l4_eager_defeq_method543 rec)` THEN
  REWRITE_TAC [l4_whnf_sound967] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL
    [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`t:l4_kexpr447`;`t':l4_kexpr447`;
     `t_v:l4_vexpr961`;`L4VSort961 w`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `t_v':l4_vexpr961` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t_v':l4_vexpr961` THEN ASM_REWRITE_TAC [l4_vhas_type961] THEN
  MATCH_MP_TAC l4_vis_defeq_conv961 THEN
  MAP_EVERY EXISTS_TAC [`t_v:l4_vexpr961`;`w:l4_vlevel961`] THEN
  ASM_REWRITE_TAC [GSYM l4_vhas_type961]);;

let l4_get_constant_accept967 = prove
 (`!env ps n us d.
   l4_get_constant528 env ps n us = L4KAccept491 d ==>
   l4_kfind_decl493 env n = SOME d /\
   l4_decl_kind_supported967 (l4_kdecl_kind493 d) /\
   LENGTH (l4_kdecl_params493 d) = LENGTH us /\
   ?x. l4_check_levels528 ps us = L4KAccept491 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_get_constant528] THEN
  STRUCT_CASES_TAC (ISPEC `l4_kfind_decl493 env n` (cases "option")) THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "option"] THEN
  MP_TAC (SPEC `l4_kdecl_kind493 a` (cases "l4_kdecl_kind493")) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_decl_kind_supported967;distinctness "l4_kresult491";
                   distinctness "l4_kdecl_kind493";injectivity "l4_kdecl_kind493"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [distinctness "l4_kresult491";l4_kr_bind_accept967;l4_accept_eq967] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [l4_decl_kind_supported967] THEN ASM_MESON_TAC []);;

let l4_all2_vlevel_equiv_refl967 = prove
 (`!ls. ALL2 l4_vlevel_equiv961 ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2;l4_vlevel_equiv_refl961]);;

let l4_infer_const_sound967 = prove
 (`!env venv ps rec fuel g vg c us ty e'.
   l4_kernel_env_syntactic_bridge967 env venv /\
   l4_infer_step586 (L4KConst447 c us) rec fuel env ps T g = L4KAccept491 ty /\
   l4_tr_e967 ps (L4KConst447 c us) = SOME e' ==>
   ?ty'. l4_tr_e967 ps ty = SOME ty' /\
         l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_accept_eq967;
               l4_if_nil_ksubst_levels967;l4_tr_e967;l4_opt_map_eq_some967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:l4_kdeclaration493` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `us':l4_vlevel961 list` STRIP_ASSUME_TAC))) THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`ps:l4_name list`;`c:l4_name`;
                 `us:l4_klevel447 list`;`d:l4_kdeclaration493`] l4_get_constant_accept967) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`us:l4_klevel447 list`;`ps:l4_name list`;`x:1`] l4_check_levels_tr_ls967) THEN
  ASM_REWRITE_TAC [injectivity "option"] THEN
  DISCH_THEN (X_CHOOSE_THEN `us2:l4_vlevel961 list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `l4_kernel_env_syntactic_bridge967 env venv` THEN
  REWRITE_TAC [l4_kernel_env_syntactic_bridge967] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPECL [`c:l4_name`;`d:l4_kdeclaration493`])) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ci:l4_vconstant961` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l4_vinstL961 us' (l4_vc_type961 ci)` THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_tr_e_subst_levels967 THEN ASM_REWRITE_TAC [];
   REWRITE_TAC [l4_vhas_type961] THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC l4_vis_defeq_const961 THEN
   MP_TAC (SPECL [`us:l4_klevel447 list`;`ps:l4_name list`;`us':l4_vlevel961 list`]
     l4_tr_ls_length967) THEN
   ASM_REWRITE_TAC [l4_all2_vlevel_equiv_refl967] THEN
   ASM_MESON_TAC []]);;

let l4_kcontext_bound_push967 = prove
 (`!g ty val_opt.
   l4_kcontext_bound532 (l4_kpush_binding532 g ty val_opt) =
   CONS (L4KBinding491 ty val_opt) (l4_kcontext_bound532 g)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `g:l4_kcontext532` (cases "l4_kcontext532")) THEN
  REWRITE_TAC [l4_kpush_binding532;l4_kcontext_bound532]);;

let l4_infer_step_sound967 = prove
 (`!env venv ps rec fuel e g vg ty e'.
   l4_kernel_env_syntactic_bridge967 env venv /\
   l4_methods_sound967 venv ps rec /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_infer_step586 e rec fuel env ps T g = L4KAccept491 ty /\
   l4_tr_e967 ps e = SOME e' ==>
   ?ty'. l4_tr_e967 ps ty = SOME ty' /\
         l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN
  REPEAT CONJ_TAC THEN
  TRY (SIMP_TAC [l4_tr_e967;distinctness "option";l4_forall_t966] THEN NO_TAC) THENL
  [(* 1. BVar *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586;l4_tr_e967;l4_some_eq967] THEN
   MP_TAC (ISPEC `l4_nth_error550 (l4_kcontext_bound532 g) a` (cases "option")) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [distinctness "l4_kresult491";l4_accept_eq967] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`ps:l4_name list`;`l4_kcontext_bound532 g`;`vg:l4_vexpr961 list`]
     l4_tr_bctx_lookup967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`a:num`;`a':l4_kbinding491`]) THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `t0:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `l4_vliftN961 t0 (SUC a) 0` THEN
   ASM_REWRITE_TAC [l4_vhas_type961] THEN
   ASM_MESON_TAC [l4_tr_e_lift967;l4_vis_defeq_bvar961];
   (* 2. Sort *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_accept_eq967;
                l4_tr_e967;l4_opt_map_eq_some967] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`ps:l4_name list`;`a:l4_klevel447`;`x:1`] l4_check_level_tr_l967) THEN
   ASM_REWRITE_TAC [injectivity "option"] THEN
   DISCH_THEN (X_CHOOSE_THEN `u2:l4_vlevel961` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `L4VSort961 (L4VLSucc961 x')` THEN
   ASM_REWRITE_TAC [l4_tr_e967;l4_tr_l967;l4_opt_map967;l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_sort961 THEN
   ASM_MESON_TAC [l4_vlevel_equiv_refl961];
   (* 3. Const *)
   MESON_TAC [l4_infer_const_sound967];
   (* 4. App *)
   MAP_EVERY X_GEN_TAC [`fn:l4_kexpr447`;`arg:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHfn") (LABEL_TAC "IHarg")) THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_match_pi_accept967;
                l4_if_accept967;l4_accept_eq967;
                l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_kernel_env_syntactic_bridge967]; ALL_TAC] THEN
   REMOVE_THEN "IHfn" (MP_TAC o SPECL
     [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x:l4_kexpr447`;`x''''':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `ft_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`ps:l4_name list`;`rec:l4_kmethods543`;
                  `g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x''''':l4_vexpr961`;
                  `x:l4_kexpr447`;`ft_v:l4_vexpr961`;`x':l4_kexpr447`]
     l4_whnf_retype967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `pi_v:l4_vexpr961`
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `dom_v:l4_vexpr961`
         (X_CHOOSE_THEN `cod_v:l4_vexpr961` STRIP_ASSUME_TAC) o
        REWRITE_RULE [l4_tr_e967;l4_opt_map2_eq_some967])
       ASSUME_TAC)) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`vg:l4_vexpr961 list`;
                  `x''''':l4_vexpr961`;`x''''':l4_vexpr961`;`pi_v:l4_vexpr961`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`vg:l4_vexpr961 list`;
                  `dom_v:l4_vexpr961`;`cod_v:l4_vexpr961`]
     l4_vis_type_forall_inv966) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   REMOVE_THEN "IHarg" (MP_TAC o SPECL
     [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x''':l4_kexpr447`;`y:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `aty_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`LENGTH (ps:l4_name list)`;`vg:l4_vexpr961 list`;
                  `y:l4_vexpr961`;`y:l4_vexpr961`;`aty_v:l4_vexpr961`]
     l4_vis_defeq_is_type966) THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`ps:l4_name list`;`rec:l4_kmethods543`;
                  `g:l4_kcontext532`;`vg:l4_vexpr961 list`;`arg:l4_kexpr447`;
                  `domain:l4_kexpr447`;`x''':l4_kexpr447`;`dom_v:l4_vexpr961`;`aty_v:l4_vexpr961`]
     l4_application_type_defeq_sound967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_TAC `u_conv:l4_vlevel961`) THEN
   EXISTS_TAC `l4_vinst0961 cod_v y` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [l4_tr_e_inst967];
    ASM_REWRITE_TAC [l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_app961 THEN EXISTS_TAC `dom_v:l4_vexpr961` THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC [l4_vhas_type961];
     MATCH_MP_TAC l4_vis_defeq_conv961 THEN
     MAP_EVERY EXISTS_TAC [`aty_v:l4_vexpr961`;`u_conv:l4_vlevel961`] THEN
     ASM_MESON_TAC [l4_vis_defeq_symm961;l4_vhas_type961]]];
   (* 5. Lam *)
   MAP_EVERY X_GEN_TAC [`nm:l4_name`;`bi:l4_kbinder447`;`dom:l4_kexpr447`;`body:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHdom") (LABEL_TAC "IHbody")) THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586;l4_kr_bind_accept967;l4_match_sort_one_accept967;
                l4_accept_eq967;l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_kernel_env_syntactic_bridge967]; ALL_TAC] THEN
   REMOVE_THEN "IHdom" (MP_TAC o SPECL
     [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x':l4_kexpr447`;`x'''':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dt_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`ps:l4_name list`;`rec:l4_kmethods543`;
                  `g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x'''':l4_vexpr961`;
                  `x':l4_kexpr447`;`dt_v:l4_vexpr961`;`x'':l4_kexpr447`]
     l4_whnf_retype967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `s0_v:l4_vexpr961`
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `u0':l4_vlevel961` STRIP_ASSUME_TAC o
        REWRITE_RULE [l4_tr_e967;l4_opt_map_eq_some967])
       ASSUME_TAC)) THEN
   REMOVE_THEN "IHbody" (MP_TAC o SPECL
     [`l4_kpush_binding532 g dom NONE`;`CONS (x'''':l4_vexpr961) vg`;
      `x''':l4_kexpr447`;`y:l4_vexpr961`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [l4_kcontext_bound_push967;l4_vctx_wf966;l4_vis_type961] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_tr_bctx_cons967 THEN ASM_REWRITE_TAC [];
     ASM_MESON_TAC []];
    DISCH_THEN (X_CHOOSE_THEN `bt_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `L4VForallE961 x'''' bt_v` THEN
    ASM_REWRITE_TAC [l4_tr_e967;l4_opt_map2967;l4_opt_map967;l4_vhas_type961] THEN
    MATCH_MP_TAC l4_vis_defeq_lam961 THEN
    EXISTS_TAC `u0':l4_vlevel961` THEN ASM_MESON_TAC [l4_vhas_type961]];
   (* 6. Pi *)
   MAP_EVERY X_GEN_TAC [`nm:l4_name`;`bi:l4_kbinder447`;`dom:l4_kexpr447`;`body:l4_kexpr447`] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHdom") (LABEL_TAC "IHbody")) THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_infer_step586;LET_DEF;LET_END_DEF;l4_kr_bind_accept967;
                l4_match_sort_accept967;l4_accept_eq967;
                l4_tr_e967;l4_opt_map2_eq_some967] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l4_venv_wf966 venv` ASSUME_TAC THENL
   [ASM_MESON_TAC [l4_kernel_env_syntactic_bridge967]; ALL_TAC] THEN
   REMOVE_THEN "IHdom" (MP_TAC o SPECL
     [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x:l4_kexpr447`;`x'''''':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `dt_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`ps:l4_name list`;`rec:l4_kmethods543`;
                  `g:l4_kcontext532`;`vg:l4_vexpr961 list`;`x'''''':l4_vexpr961`;
                  `x:l4_kexpr447`;`dt_v:l4_vexpr961`;`x':l4_kexpr447`]
     l4_whnf_retype967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `s0_v:l4_vexpr961`
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `u0':l4_vlevel961` STRIP_ASSUME_TAC o
        REWRITE_RULE [l4_tr_e967;l4_opt_map_eq_some967])
       ASSUME_TAC)) THEN
   SUBGOAL_THEN `l4_tr_bctx967 ps (l4_kcontext_bound532 (l4_kpush_binding532 g dom NONE))
                   (CONS x'''''' vg) /\
                 l4_vctx_wf966 venv (LENGTH ps) (CONS x'''''' vg)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC [l4_kcontext_bound_push967;l4_vctx_wf966;l4_vis_type961] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC l4_tr_bctx_cons967 THEN ASM_REWRITE_TAC [];
     ASM_MESON_TAC []];
    ALL_TAC] THEN
   REMOVE_THEN "IHbody" (MP_TAC o SPECL
     [`l4_kpush_binding532 g dom NONE`;`CONS (x'''''':l4_vexpr961) vg`;
      `x''':l4_kexpr447`;`y:l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `bt_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
   MP_TAC (SPECL [`venv:l4_venv961`;`ps:l4_name list`;`rec:l4_kmethods543`;
                  `l4_kpush_binding532 g dom NONE`;`CONS (x'''''':l4_vexpr961) vg`;
                  `y:l4_vexpr961`;`x''':l4_kexpr447`;`bt_v:l4_vexpr961`;`x'''':l4_kexpr447`]
     l4_whnf_retype967) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `s1_v:l4_vexpr961`
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `v0':l4_vlevel961` STRIP_ASSUME_TAC o
        REWRITE_RULE [l4_tr_e967;l4_opt_map_eq_some967])
       ASSUME_TAC)) THEN
   EXISTS_TAC `L4VSort961 (L4VLIMax961 u0' v0')` THEN
   ASM_REWRITE_TAC [l4_tr_e967;l4_tr_l967;l4_opt_map2967;l4_opt_map967;l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_forall961 THEN
   ASM_MESON_TAC [l4_vhas_type961];
   (* 7. MData *)
   REWRITE_TAC [l4_infer_step586;l4_tr_e967] THEN MESON_TAC []]);;

let l4_check_step_sound967 = prove
 (`!env venv ps rec fuel g vg e ty et e' ty'.
   l4_kernel_env_syntactic_bridge967 env venv /\
   l4_methods_sound967 venv ps rec /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_infer_step586 e rec fuel env ps T g = L4KAccept491 et /\
   l4_defeq_method543 rec g et ty = L4KAccept491 T /\
   l4_tr_e967 ps e = SOME e' /\
   l4_tr_e967 ps ty = SOME ty' /\
   l4_vis_type961 venv (LENGTH ps) vg ty' ==>
   l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:l4_kdeclaration493 list`;`venv:l4_venv961`;`ps:l4_name list`;
                 `rec:l4_kmethods543`;`fuel:num`;`e:l4_kexpr447`;
                 `g:l4_kcontext532`;`vg:l4_vexpr961 list`;`et:l4_kexpr447`;`e':l4_vexpr961`]
    l4_infer_step_sound967) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `et_v:l4_vexpr961` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l4_vis_type961 venv (LENGTH (ps:l4_name list)) vg et_v` ASSUME_TAC THENL
  [MATCH_MP_TAC l4_vis_defeq_is_type966 THEN
   MAP_EVERY EXISTS_TAC [`e':l4_vexpr961`;`e':l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_kernel_env_syntactic_bridge967;l4_vhas_type961];
   UNDISCH_TAC `l4_methods_sound967 venv ps rec` THEN
   REWRITE_TAC [l4_methods_sound967;l4_defeq_types_sound967] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (K ALL_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL
     [`g:l4_kcontext532`;`vg:l4_vexpr961 list`;`et:l4_kexpr447`;`ty:l4_kexpr447`;
      `et_v:l4_vexpr961`;`ty':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_TAC `u:l4_vlevel961`) THEN
   REWRITE_TAC [l4_vhas_type961] THEN
   MATCH_MP_TAC l4_vis_defeq_conv961 THEN
   MAP_EVERY EXISTS_TAC [`et_v:l4_vexpr961`;`u:l4_vlevel961`] THEN
   ASM_REWRITE_TAC [GSYM l4_vhas_type961]]);;

(* ========================================================================= *)
(* 7. Public l4_infer597 Entry Point & Open CheckerMethodsSound Obligation   *)
(* ========================================================================= *)

(* Undischarged obligation: concrete fuelled l4_checker597 satisfies the
   oracle specification at every fuel depth. *)
let l4_checker_methods_sound967 = new_definition
 `l4_checker_methods_sound967 env venv ps <=>
   !n. l4_methods_sound967 venv ps (l4_checker597 n env ps)`;;

let l4_infer_sound967 = prove
 (`!fuel env venv ps g vg e ty e'.
   l4_kernel_env_syntactic_bridge967 env venv /\
   l4_checker_methods_sound967 env venv ps /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_infer597 fuel env ps g e = L4KAccept491 ty /\
   l4_tr_e967 ps e = SOME e' ==>
   ?ty'. l4_tr_e967 ps ty = SOME ty' /\
         l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  INDUCT_TAC THEN
  REWRITE_TAC [l4_infer597;l4_checker597;l4_checker_mode597;l4_infer_method543;
               distinctness "l4_kresult491";l4_forall_t966] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_checker_methods_sound967;GSYM l4_checker597] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC l4_infer_step_sound967 THEN
  MAP_EVERY EXISTS_TAC
    [`env:l4_kdeclaration493 list`;`l4_checker597 fuel env ps`;
     `fuel:num`;`e:l4_kexpr447`;`g:l4_kcontext532`] THEN
  ASM_REWRITE_TAC []);;

(* ========================================================================= *)
(* 8. Non-Vacuity Witness: Executable Syntactic Methods (l4_core_alpha_eq538)*)
(* ========================================================================= *)

let l4_core_alpha_tr_e967 = prove
 (`!a ps budget b.
   FST (l4_core_alpha538 budget a b) ==> l4_tr_e967 ps a = l4_tr_e967 ps b`,
  MATCH_MP_TAC l4_kexpr_INDUCT447 THEN REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   REWRITE_TAC [l4_tr_e967] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   REWRITE_TAC [l4_tr_e967] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN
   REWRITE_TAC [l4_tr_e967] THEN ASM_MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;LET_DEF;LET_END_DEF;l4_tr_e967];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN REWRITE_TAC [l4_core_alpha538] THEN
   COND_CASES_TAC THEN REWRITE_TAC [FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC [];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;l4_tr_e967];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [l4_core_alpha538] THEN COND_CASES_TAC THEN REWRITE_TAC [FST] THEN
   STRUCT_CASES_TAC (SPEC `b:l4_kexpr447` (cases "l4_kexpr447")) THEN
   REWRITE_TAC [FST;l4_tr_e967] THEN ASM_MESON_TAC []]);;

let l4_syntactic_methods967 = new_definition
 `l4_syntactic_methods967 =
   L4KMethods543
     (\g e. L4KDecline491 L4KUnsupportedExpression491)
     (\g e. L4KDecline491 L4KUnsupportedExpression491)
     (\g e. L4KAccept491 e)
     (\cheap g e. L4KAccept491 e)
     (\g a b. L4KAccept491 (l4_core_alpha_eq538 a b))
     L4NormalReduction543
     (\g a b. L4KAccept491 (l4_core_alpha_eq538 a b))`;;

let l4_syntactic_defeq_sound967 = prove
 (`!venv ps.
   l4_defeq_types_sound967 venv ps (\g a b. L4KAccept491 (l4_core_alpha_eq538 a b))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_defeq_types_sound967;l4_core_alpha_eq538;injectivity "l4_kresult491"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`a:l4_kexpr447`;`ps:l4_name list`;`256`;`b:l4_kexpr447`]
    l4_core_alpha_tr_e967) THEN
  ASM_REWRITE_TAC [injectivity "option"] THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `l4_vis_type961 venv (LENGTH (ps:l4_name list)) vg a_v` THEN
  REWRITE_TAC [l4_vis_type961;l4_vhas_type961]);;

let l4_syntactic_methods_sound967 = prove
 (`!venv ps. l4_methods_sound967 venv ps l4_syntactic_methods967`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_methods_sound967;l4_syntactic_methods967;
               l4_whnf_method543;l4_defeq_method543;l4_eager_defeq_method543;
               l4_syntactic_defeq_sound967;l4_whnf_sound967;
               injectivity "l4_kresult491";l4_vhas_type961] THEN
  MESON_TAC []);;

let l4_syntactic_infer_sound967 = prove
 (`!env venv ps fuel g vg e ty e'.
   l4_kernel_env_syntactic_bridge967 env venv /\
   l4_tr_bctx967 ps (l4_kcontext_bound532 g) vg /\
   l4_vctx_wf966 venv (LENGTH ps) vg /\
   l4_infer_step586 e l4_syntactic_methods967 fuel env ps T g = L4KAccept491 ty /\
   l4_tr_e967 ps e = SOME e' ==>
   ?ty'. l4_tr_e967 ps ty = SOME ty' /\
         l4_vhas_type961 venv (LENGTH ps) vg e' ty'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC l4_infer_step_sound967 THEN
  MAP_EVERY EXISTS_TAC
    [`env:l4_kdeclaration493 list`;`l4_syntactic_methods967`;
     `fuel:num`;`e:l4_kexpr447`;`g:l4_kcontext532`] THEN
  ASM_REWRITE_TAC [l4_syntactic_methods_sound967]);;
