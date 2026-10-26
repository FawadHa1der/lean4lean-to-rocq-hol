(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed core operational equations. ALL UNCOMPILED. *)
needs "hol/kernel_checker597.ml";;

let l4_lazy_delta_no_rounds597 = prove
 (`!rec fuel env ps g t s.
   l4_core_lazy_delta597 0 rec fuel env ps g t s = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_core_lazy_delta597]);;

let l4_lazy_delta_quick_false597 = prove
 (`!rounds rec fuel env ps g t s.
   l4_core_quick596 rec fuel g t s = L4KAccept491 (SOME F) ==>
   l4_core_lazy_delta597 (SUC rounds) rec fuel env ps g t s =
   L4KAccept491 (L4ConversionDone597 F)`,
  SIMP_TAC [l4_core_lazy_delta597;l4_kr_bind491]);;

let l4_lazy_delta_quick_decline597 = prove
 (`!rounds rec fuel env ps g t s reason.
   l4_core_quick596 rec fuel g t s = L4KDecline491 reason ==>
   l4_core_lazy_delta597 (SUC rounds) rec fuel env ps g t s = L4KDecline491 reason`,
  SIMP_TAC [l4_core_lazy_delta597;l4_kr_bind491]);;

let l4_lazy_delta_offset_false597 = prove
 (`!rounds rec fuel env ps g t s.
   l4_core_quick596 rec fuel g t s = L4KAccept491 NONE /\
   l4_core_offset596 rec env g t s = L4KAccept491 (SOME F) ==>
   l4_core_lazy_delta597 (SUC rounds) rec fuel env ps g t s =
   L4KAccept491 (L4ConversionDone597 F)`,
  SIMP_TAC [l4_core_lazy_delta597;l4_kr_bind491]);;

let l4_true_shortcut_wrong_right597 = prove
 (`!rec env g t s. ~l4_core_is_true597 s ==>
   l4_core_true_shortcut597 rec env g t s = L4KAccept491 F`,
  SIMP_TAC [l4_core_true_shortcut597]);;

let l4_defeq_quick_false597 = prove
 (`!methods fuel env ps g t s.
   l4_core_quick596 (l4_inference_only543 methods) fuel g t s =
   L4KAccept491 (SOME F) ==>
   l4_defeq_step597 methods fuel env ps g t s = L4KAccept491 F`,
  SIMP_TAC [l4_defeq_step597;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

(* A negative proof-irrelevance answer must not unfold either proof afterward.
   This is the control-flow boundary exercised by Arena irrelevance-refutes,
   not a claim that this conditional script runs or passes that Arena file. *)
let l4_defeq_irrelevance_false597 = prove
 (`!methods fuel env ps g t s.
   l4_core_quick596 (l4_inference_only543 methods) fuel g t s = L4KAccept491 NONE /\
   l4_core_true_shortcut597 (l4_inference_only543 methods) env g t s = L4KAccept491 F /\
   l4_core_proof_irrel596 (l4_inference_only543 methods) fuel g t s =
   L4KAccept491 (SOME F) ==>
   l4_defeq_step597 methods fuel env ps g t s = L4KAccept491 F`,
  SIMP_TAC [l4_defeq_step597;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_defeq_irrelevance_decline597 = prove
 (`!methods fuel env ps g t s reason.
   l4_core_quick596 (l4_inference_only543 methods) fuel g t s = L4KAccept491 NONE /\
   l4_core_true_shortcut597 (l4_inference_only543 methods) env g t s = L4KAccept491 F /\
   l4_core_proof_irrel596 (l4_inference_only543 methods) fuel g t s =
   L4KDecline491 reason ==>
   l4_defeq_step597 methods fuel env ps g t s = L4KDecline491 reason`,
  SIMP_TAC [l4_defeq_step597;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_checker_mode_preserves_mode597 = prove
 (`!fuel mode env ps.
   l4_method_mode543 (l4_checker_mode597 fuel mode env ps) = mode`,
  INDUCT_TAC THEN REWRITE_TAC [l4_checker_mode597;l4_method_mode543]);;

let l4_infer_no_fuel597 = prove
 (`!env ps g e. l4_infer597 0 env ps g e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_infer597;l4_checker597;l4_checker_mode597;l4_infer_method543]);;

let l4_whnf_no_fuel597 = prove
 (`!env ps g e. l4_whnf597 0 env ps g e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_whnf597]);;

let l4_defeq_no_fuel597 = prove
 (`!env ps g t s. l4_defeq597 0 env ps g t s = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_defeq597]);;

let l4_check_no_fuel597 = prove
 (`!env ps g e ty. l4_check597 0 env ps g e ty = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_check597;l4_sort_of543;l4_checker597;l4_checker_mode597;
    l4_infer_method543;l4_kr_bind491]);;

let l4_check_defeq_no_fuel597 = prove
 (`!env ps g t s. l4_check_defeq597 0 env ps g t s = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_check_defeq597;l4_infer_no_fuel597;l4_kr_bind491]);;

let l4_whnf_unsupported597 = prove
 (`!fuel env ps g e. ~(fuel = 0) /\ ~l4_core_supported533 env e ==>
   l4_whnf597 fuel env ps g e = L4KDecline491 L4KUnsupportedExpression491`,
  SIMP_TAC [l4_whnf597]);;

let l4_defeq_unsupported597 = prove
 (`!fuel env ps g t s. ~(fuel = 0) /\
   ~(l4_core_supported533 env t /\ l4_core_supported533 env s) ==>
   l4_defeq597 fuel env ps g t s = L4KDecline491 L4KUnsupportedExpression491`,
  SIMP_TAC [l4_defeq597]);;

let l4_check_false_conversion597 = prove
 (`!fuel env ps g e ty u et.
   l4_sort_of543 (l4_checker597 fuel env ps) g ty = L4KAccept491 u /\
   l4_infer597 fuel env ps g e = L4KAccept491 et /\
   l4_defeq597 fuel env ps g et ty = L4KAccept491 F ==>
   l4_check597 fuel env ps g e ty = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_check597;l4_kr_bind491]);;

let l4_check_true_conversion597 = prove
 (`!fuel env ps g e ty u et.
   l4_sort_of543 (l4_checker597 fuel env ps) g ty = L4KAccept491 u /\
   l4_infer597 fuel env ps g e = L4KAccept491 et /\
   l4_defeq597 fuel env ps g et ty = L4KAccept491 T ==>
   l4_check597 fuel env ps g e ty = L4KAccept491 one`,
  SIMP_TAC [l4_check597;l4_kr_bind491]);;

let l4_check_defeq_type_mismatch597 = prove
 (`!fuel env ps g t s tt st.
   l4_infer597 fuel env ps g t = L4KAccept491 tt /\
   l4_infer597 fuel env ps g s = L4KAccept491 st /\
   l4_defeq597 fuel env ps g tt st = L4KAccept491 F ==>
   l4_check_defeq597 fuel env ps g t s = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_check_defeq597;l4_kr_bind491]);;

let l4_check_defeq_term_mismatch597 = prove
 (`!fuel env ps g t s tt st.
   l4_infer597 fuel env ps g t = L4KAccept491 tt /\
   l4_infer597 fuel env ps g s = L4KAccept491 st /\
   l4_defeq597 fuel env ps g tt st = L4KAccept491 T /\
   l4_defeq597 fuel env ps g t s = L4KAccept491 F ==>
   l4_check_defeq597 fuel env ps g t s = L4KReject491 L4KNotDefinitionallyEqual491`,
  SIMP_TAC [l4_check_defeq597;l4_kr_bind491]);;
