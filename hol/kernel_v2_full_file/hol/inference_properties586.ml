(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational equations. ALL UNCOMPILED; no soundness claim. *)
needs "hol/inference586.ml";;

let l4_infer_meta586 = prove
 (`!n rec fuel env ps checking g.
   l4_infer_step586 (L4KMVar447 n) rec fuel env ps checking g =
   L4KReject491 L4KMetaVariable491`, REWRITE_TAC [l4_infer_step586]);;

let l4_infer_missing_bound586 = prove
 (`!i rec fuel env ps checking g.
   l4_nth_error550 (l4_kcontext_bound532 g) i = NONE ==>
   l4_infer_step586 (L4KBVar447 i) rec fuel env ps checking g =
   L4KReject491 L4KLooseBoundVariable491`, SIMP_TAC [l4_infer_step586]);;

let l4_infer_bound_lift586 = prove
 (`!i b rec fuel env ps checking g.
   l4_nth_error550 (l4_kcontext_bound532 g) i = SOME b ==>
   l4_infer_step586 (L4KBVar447 i) rec fuel env ps checking g =
   L4KAccept491 (l4_klift447 (l4_kbinding_type532 b) (SUC i) 0)`,
  SIMP_TAC [l4_infer_step586]);;

let l4_infer_missing_free586 = prove
 (`!n rec fuel env ps checking g.
   l4_kfind_free532 n (l4_kcontext_free532 g) = NONE ==>
   l4_infer_step586 (L4KFVar447 n) rec fuel env ps checking g =
   L4KReject491 L4KUnknownFreeVariable491`, SIMP_TAC [l4_infer_step586]);;

let l4_infer_metadata586 = prove
 (`!e rec fuel env ps checking g.
   l4_infer_step586 (L4KMData447 e) rec fuel env ps checking g =
   l4_infer_step586 e rec fuel env ps checking g`, REWRITE_TAC [l4_infer_step586]);;

let l4_infer_sort_success586 = prove
 (`!u rec fuel env ps checking g.
   l4_check_level528 ps u = L4KAccept491 one ==>
   l4_infer_step586 (L4KSort447 u) rec fuel env ps checking g =
   L4KAccept491 (L4KSort447 (L4KSucc447 u))`,
  SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_constant_decline586 = prove
 (`!n us rec fuel env ps checking g reason.
   l4_get_constant528 env ps n us = L4KDecline491 reason ==>
   l4_infer_step586 (L4KConst447 n us) rec fuel env ps checking g =
   L4KDecline491 reason`, SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_application_function_reject586 = prove
 (`!fn arg rec fuel env ps checking g reason.
   l4_infer_step586 fn rec fuel env ps checking g = L4KReject491 reason ==>
   l4_infer_step586 (L4KApp447 fn arg) rec fuel env ps checking g =
   L4KReject491 reason`, SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_application_whnf_decline586 = prove
 (`!fn arg ft rec fuel env ps checking g reason.
   l4_infer_step586 fn rec fuel env ps checking g = L4KAccept491 ft /\
   l4_whnf_method543 rec g ft = L4KDecline491 reason ==>
   l4_infer_step586 (L4KApp447 fn arg) rec fuel env ps checking g =
   L4KDecline491 reason`, SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_application_unchecked586 = prove
 (`!fn arg ft rec fuel env ps g n bi domain body.
   l4_infer_step586 fn rec fuel env ps F g = L4KAccept491 ft /\
   l4_whnf_method543 rec g ft = L4KAccept491 (L4KPi447 n bi domain body) ==>
   l4_infer_step586 (L4KApp447 fn arg) rec fuel env ps F g =
   L4KAccept491 (l4_kinst447 body arg)`,
  SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_checked_meta_argument586 = prove
 (`!fn ft meta rec fuel env ps g n bi domain body.
   l4_infer_step586 fn rec fuel env ps T g = L4KAccept491 ft /\
   l4_whnf_method543 rec g ft = L4KAccept491 (L4KPi447 n bi domain body) ==>
   l4_infer_step586 (L4KApp447 fn (L4KMVar447 meta)) rec fuel env ps T g =
   L4KReject491 L4KMetaVariable491`,
  SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_lambda_unchecked586 = prove
 (`!n bi domain body rec fuel env ps g bt.
   l4_infer_step586 body rec fuel env ps F (l4_kpush_binding532 g domain NONE) =
   L4KAccept491 bt ==>
   l4_infer_step586 (L4KLam447 n bi domain body) rec fuel env ps F g =
   L4KAccept491 (L4KPi447 n bi domain bt)`,
  SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_let_unchecked586 = prove
 (`!n ty value body nd rec fuel env ps g bt.
   l4_infer_step586 body rec fuel env ps F (l4_kpush_binding532 g ty (SOME value)) =
   L4KAccept491 bt ==>
   l4_infer_step586 (L4KLet447 n ty value body nd) rec fuel env ps F g =
   L4KAccept491 (l4_kinst447 bt value)`,
  SIMP_TAC [l4_infer_step586;l4_kr_bind491]);;

let l4_infer_nat_unsupported586 = prove
 (`!n rec fuel env ps checking g. ~l4_core_nat_ready533 env ==>
   l4_infer_step586 (L4KNatLit447 n) rec fuel env ps checking g =
   L4KDecline491 L4KUnsupportedExpression491`, SIMP_TAC [l4_infer_step586]);;

let l4_infer_projection_unavailable586 = prove
 (`!owner idx value rec fuel env ps checking g.
   l4_core_inductive532 env owner = NONE ==>
   l4_infer_step586 (L4KProj447 owner idx value) rec fuel env ps checking g =
   L4KDecline491 L4KUnsupportedExpression491`, SIMP_TAC [l4_infer_step586]);;
