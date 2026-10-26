(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Focused operational regressions. ALL SCRIPTS UNCOMPILED / NOT RUN.
   No test method record is an admitted or public checker. *)
needs "hol/whnf_control_properties594.ml";;

let l4_whnf_reg_meta594 = prove
 (`!rec fuel env ps cheap g n.
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KMVar447 n) =
     L4KReject491 L4KMetaVariable491`,
  REWRITE_TAC [l4_whnf_core_step594]);;
let l4_whnf_reg_bound_missing594 = prove
 (`!rec fuel env ps cheap free i.
   l4_whnf_core_step594 rec fuel env ps cheap (L4KContext532 [] free) (L4KBVar447 i) =
     L4KReject491 L4KLooseBoundVariable491`,
  REWRITE_TAC [l4_whnf_core_step594;l4_kcontext_bound532;l4_nth_error550]);;
let l4_whnf_reg_bound_assumption594 = prove
 (`!rec fuel env ps cheap bound free ty.
   l4_whnf_core_step594 rec fuel env ps cheap
     (L4KContext532 (CONS (L4KBinding491 ty NONE) bound) free) (L4KBVar447 0) =
     L4KAccept491 (L4KBVar447 0)`,
  REWRITE_TAC [l4_whnf_core_step594;l4_kcontext_bound532;l4_nth_error550;l4_kbinding_value532]);;
let l4_whnf_reg_free_missing594 = prove
 (`!rec fuel env ps cheap bound n.
   l4_whnf_core_step594 rec fuel env ps cheap (L4KContext532 bound []) (L4KFVar447 n) =
     L4KReject491 L4KUnknownFreeVariable491`,
  REWRITE_TAC [l4_whnf_core_step594;l4_kcontext_free532;l4_kfind_free532]);;
let l4_whnf_reg_let_and_metadata594 = prove
 (`!rec fuel env ps cheap g n ty v body nd.
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KLet447 n ty v body nd) =
     l4_whnf_core_method543 rec cheap g (l4_kinst447 body v) /\
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KMData447 body) =
     l4_whnf_core_method543 rec cheap g body`,
  REWRITE_TAC [l4_whnf_core_step594]);;
let l4_whnf_reg_inert_forms594 = prove
 (`!rec fuel env ps cheap g n bi domain body k.
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KLam447 n bi domain body) =
     L4KAccept491 (L4KLam447 n bi domain body) /\
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KPi447 n bi domain body) =
     L4KAccept491 (L4KPi447 n bi domain body) /\
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KNatLit447 k) =
     L4KAccept491 (L4KNatLit447 k)`,
  REWRITE_TAC [l4_whnf_core_step594]);;
let l4_whnf_reg_sort_meta_first594 = prove
 (`!rec fuel env ps cheap g n m.
   l4_whnf_core_step594 rec fuel env ps cheap g
     (L4KSort447 (L4KMax447 (L4KParam447 n) (L4KLevelMVar447 m))) =
     L4KReject491 L4KMetaVariable491`,
  REWRITE_TAC [l4_whnf_core_step594;l4_check_level528;l4_klevel_meta447;l4_kr_bind491]);;
let l4_whnf_reg_unknown_before_universe594 = prove
 (`!rec fuel env ps cheap g n m.
   l4_kfind_decl493 env n = NONE ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KConst447 n [L4KLevelMVar447 m]) =
     L4KReject491 L4KUnknownConstant491`,
  SIMP_TAC [l4_whnf_core_step594;l4_get_constant528;l4_kr_bind491]);;
let l4_whnf_reg_unsupported_declines594 = prove
 (`!rec fuel env ps cheap g n us d.
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDUnsupported493 ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KConst447 n us) =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_whnf_core_step594;l4_get_constant528;l4_kr_bind491]);;
let l4_whnf_reg_nonbyte_string594 = prove
 (`!rec fuel env ps cheap g.
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KStrLit447 [65;256]) =
     L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_whnf_core_step594;l4_core_expand_string539;
    l4_core_utf8_539;l4_core_utf8_scan539;
    l4_core_cont539;l4_core_append_digit539;l4_core_digit539] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [l4_kr_bind491]);;

let l4_whnf_reg_cheap_projection_reject594 = prove
 (`!rec fuel env ps g owner idx value reason.
   l4_whnf_core_method543 rec T g value = L4KReject491 reason ==>
   l4_whnf_core_step594 rec fuel env ps T g (L4KProj447 owner idx value) =
     L4KReject491 reason`,
  SIMP_TAC [l4_whnf_core_step594;l4_core_reduce_projection_with550;l4_kr_bind491]);;
let l4_whnf_reg_full_projection_decline594 = prove
 (`!rec fuel env ps g owner idx value reason.
   l4_whnf_method543 rec g value = L4KDecline491 reason ==>
   l4_whnf_core_step594 rec fuel env ps F g (L4KProj447 owner idx value) =
     L4KDecline491 reason`,
  SIMP_TAC [l4_whnf_core_step594;l4_core_reduce_projection_with550;l4_kr_bind491]);;
let l4_whnf_reg_cheap_string_uses_full594 = prove
 (`!rec fuel env ps g owner idx value bytes expanded reason.
   l4_whnf_core_method543 rec T g value = L4KAccept491 (L4KStrLit447 bytes) /\
   l4_core_expand_string539 bytes = L4KAccept491 expanded /\
   l4_whnf_method543 rec g expanded = L4KReject491 reason ==>
   l4_whnf_core_step594 rec fuel env ps T g (L4KProj447 owner idx value) =
     L4KReject491 reason`,
  SIMP_TAC [l4_whnf_core_step594;l4_core_reduce_projection_with550;l4_kr_bind491]);;

(* No Nat reducer or delta result is assumed: core leaves this rebuilt head. *)
let l4_whnf_reg_core_keeps_delta594 = prove
 (`!rec fuel env ps cheap g f a head args n us.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KAccept491 (L4KConst447 n us) /\
   l4_core_reduce_quotient550 rec env g (l4_kapply_exprs489 args (L4KConst447 n us)) =
     L4KAccept491 NONE /\
   l4_core_reduce_recursor585 rec fuel env g (l4_kapply_exprs489 args (L4KConst447 n us)) =
     L4KAccept491 NONE ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) =
     L4KAccept491 (l4_kapply_exprs489 args (L4KConst447 n us))`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_whnf_reg_delta_error594 = prove
 (`!rec fuel env ps g e n us reason.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KConst447 n us) /\
   ~(n = l4_core_zero_name533 /\ l4_core_nat_ready533 env) /\
   l4_core_unfold528 env ps (L4KConst447 n us) = L4KReject491 reason ==>
   l4_whnf_step594 rec fuel env ps g e = L4KReject491 reason /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KReject491 reason`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_finish_whnf_unfold594;l4_kr_bind491]);;
let l4_whnf_reg_last_continue_exhausts594 = prove
 (`!rec fuel env ps g e next.
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfContinue543 next) ==>
   l4_whnf_loop594 (SUC 0) rec fuel env ps g e = L4KDecline491 L4KOutOfFuel491`,
  SIMP_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_kr_bind491]);;
let l4_whnf_reg_two_rounds_same_methods594 = prove
 (`!rec fuel env ps g e next value.
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfContinue543 next) /\
   l4_whnf_round_step594 rec fuel env ps g next = L4KAccept491 (L4WhnfDone543 value) ==>
   l4_whnf_loop594 (SUC (SUC 0)) rec fuel env ps g e = L4KAccept491 value`,
  SIMP_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_kr_bind491]);;
let l4_whnf_reg_loop_decline594 = prove
 (`!rounds rec fuel env ps g e reason.
   l4_whnf_round_step594 rec fuel env ps g e = L4KDecline491 reason ==>
   l4_whnf_loop594 (SUC rounds) rec fuel env ps g e = L4KDecline491 reason`,
  SIMP_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_kr_bind491]);;
