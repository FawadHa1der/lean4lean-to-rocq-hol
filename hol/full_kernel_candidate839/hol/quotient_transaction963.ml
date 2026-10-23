(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of Lean4Lean/Quot.lean atomic addQuot / quotInit
   transaction state machine and flag soundness invariant. Zero new axioms. *)
needs "hol/quotient_admission608.ml";;

let l4_quot_tx_names963 = new_definition
 `l4_quot_tx_names963 =
   [l4_kdecl_name493 (l4_canonical_quotient608 L4KQType493);
    l4_kdecl_name493 (l4_canonical_quotient608 L4KQCtor493);
    l4_kdecl_name493 (l4_canonical_quotient608 L4KQLift493);
    l4_kdecl_name493 (l4_canonical_quotient608 L4KQInd493)]`;;

let l4_quot_names_fresh963 = new_recursive_definition list_RECURSION
 `(l4_quot_names_fresh963 env [] <=> T) /\
  (l4_quot_names_fresh963 env (CONS n rest) <=>
    l4_kfind_decl493 env n = NONE /\ l4_quot_names_fresh963 env rest)`;;

let l4_canonical_quotient_block963 = new_definition
 `l4_canonical_quotient_block963 =
   [l4_canonical_quotient608 L4KQInd493;
    l4_canonical_quotient608 L4KQLift493;
    l4_canonical_quotient608 L4KQCtor493;
    l4_canonical_quotient608 L4KQType493]`;;

let l4_quot_tx_initial963 = new_definition
 `l4_quot_tx_initial963 : (l4_kdeclaration493 list) # bool = ([], F)`;;

let l4_initialize_quotient963 = new_definition
 `l4_initialize_quotient963 (st : (l4_kdeclaration493 list) # bool) =
   if SND st then L4KAccept491 st else
   l4_kr_bind491 (l4_quotient_check_eq608 (FST st)) (\eq_ok.
     if l4_quot_names_fresh963 (FST st) l4_quot_tx_names963 then
       L4KAccept491 (APPEND l4_canonical_quotient_block963 (FST st), T)
     else L4KReject491 L4KDuplicateDeclaration491)`;;

let l4_quot_flag_sound963 = new_definition
 `l4_quot_flag_sound963 (st : (l4_kdeclaration493 list) # bool) <=>
   (SND st ==>
    !kind. l4_kfind_decl493 (FST st) (l4_kdecl_name493 (l4_canonical_quotient608 kind)) =
           SOME (l4_canonical_quotient608 kind))`;;

let l4_quot_tx_initialized_noop963 = prove
 (`!env. l4_initialize_quotient963 (env, T) = L4KAccept491 (env, T)`,
  REWRITE_TAC [l4_initialize_quotient963;SND]);;

let l4_quot_tx_eq_error_precedes_names963 = prove
 (`!env reason.
   l4_quotient_check_eq608 env = L4KReject491 reason ==>
   l4_initialize_quotient963 (env, F) = L4KReject491 reason`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_initialize_quotient963;FST;SND;l4_kr_bind491]);;

let l4_quot_tx_collision_rejects963 = prove
 (`!env.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   ~l4_quot_names_fresh963 env l4_quot_tx_names963 ==>
   l4_initialize_quotient963 (env, F) = L4KReject491 L4KDuplicateDeclaration491`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_initialize_quotient963;FST;SND;l4_kr_bind491]);;

let l4_quot_tx_success963 = prove
 (`!env.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_quot_names_fresh963 env l4_quot_tx_names963 ==>
   l4_initialize_quotient963 (env, F) =
     L4KAccept491 (APPEND l4_canonical_quotient_block963 env, T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_initialize_quotient963;FST;SND;l4_kr_bind491]);;

let l4_quot_tx_no_partial_commit963 = prove
 (`!env next_st.
   l4_initialize_quotient963 (env, F) = L4KAccept491 next_st ==>
   next_st = (APPEND l4_canonical_quotient_block963 env, T)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_initialize_quotient963;FST;SND] THEN
  STRUCT_CASES_TAC (ISPEC `l4_quotient_check_eq608 env` (cases "l4_kresult491")) THEN
  REWRITE_TAC [l4_kr_bind491;distinctness "l4_kresult491"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [distinctness "l4_kresult491";injectivity "l4_kresult491"] THEN
  MESON_TAC []);;

let l4_quot_tx_sets_flag963 = prove
 (`!st next_st.
   l4_initialize_quotient963 st = L4KAccept491 next_st ==> SND next_st`,
  REWRITE_TAC [FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  BOOL_CASES_TAC `p2:bool` THENL
  [REWRITE_TAC [l4_quot_tx_initialized_noop963;injectivity "l4_kresult491";PAIR_EQ] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [SND];
   DISCH_THEN (MP_TAC o MATCH_MP l4_quot_tx_no_partial_commit963) THEN
   REWRITE_TAC [PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC [SND]]);;

let l4_quot_tx_idempotent963 = prove
 (`!st next_st.
   l4_initialize_quotient963 st = L4KAccept491 next_st ==>
   l4_initialize_quotient963 next_st = L4KAccept491 next_st`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP l4_quot_tx_sets_flag963) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC [l4_initialize_quotient963]);;

let l4_quot_initial_flag_sound963 = prove
 (`l4_quot_flag_sound963 l4_quot_tx_initial963`,
  REWRITE_TAC [l4_quot_flag_sound963;l4_quot_tx_initial963;SND]);;
