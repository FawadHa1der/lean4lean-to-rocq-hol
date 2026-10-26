(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational equations only. ALL SCRIPTS UNCOMPILED.
   Callback soundness, declarative preservation and upstream adequacy remain open. *)
needs "hol/projection_typing577.ml";;
needs "hol/universe_properties562.ml";;

let l4_projection_verify_reject577 = prove
 (`!rec fuel g d reason. l4_sort_of543 rec g d = L4KReject491 reason ==>
   l4_projection_verify_prop577 rec fuel g d = L4KReject491 reason`,
  SIMP_TAC [l4_projection_verify_prop577;l4_kr_bind491]);;
let l4_projection_verify_decline577 = prove
 (`!rec fuel g d reason. l4_sort_of543 rec g d = L4KDecline491 reason ==>
   l4_projection_verify_prop577 rec fuel g d = L4KDecline491 reason`,
  SIMP_TAC [l4_projection_verify_prop577;l4_kr_bind491]);;
let l4_projection_verify_false577 = prove
 (`!rec fuel g d u. l4_sort_of543 rec g d = L4KAccept491 u /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 F ==>
   l4_projection_verify_prop577 rec fuel g d = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_projection_verify_prop577;l4_kr_bind491]);;
let l4_projection_verify_true577 = prove
 (`!rec fuel g d u. l4_sort_of543 rec g d = L4KAccept491 u /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 T ==>
   l4_projection_verify_prop577 rec fuel g d = L4KAccept491 one`,
  SIMP_TAC [l4_projection_verify_prop577;l4_kr_bind491]);;
let l4_projection_meta_before_fuel577 = prove
 (`!rec fuel g d u. l4_sort_of543 rec g d = L4KAccept491 u /\
   l4_klevel_meta447 u ==>
   l4_projection_verify_prop577 rec fuel g d = L4KReject491 L4KMetaVariable491`,
  SIMP_TAC [l4_projection_verify_prop577;l4_klevel_equiv555;
    l4_knormalize_level555;l4_kr_bind491]);;
let l4_projection_zero_fuel577 = prove
 (`!rec g d u. l4_sort_of543 rec g d = L4KAccept491 u /\
   ~l4_klevel_meta447 u ==>
   l4_projection_verify_prop577 rec 0 g d = L4KDecline491 L4KOutOfFuel491`,
  SIMP_TAC [l4_projection_verify_prop577;l4_klevel_equiv555;
    l4_knormalize_level555;l4_knormalize_aux555;l4_kr_bind491]);;
let l4_projection_selected_nonprop577 = prove
 (`!rec fuel g owner value idx ty user bi domain body.
   l4_whnf_method543 rec g ty = L4KAccept491 (L4KPi447 user bi domain body) ==>
   l4_core_projection_field577 0 rec fuel g owner value F idx ty = L4KAccept491 domain`,
  SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_selected_prop577 = prove
 (`!rec fuel g owner value idx ty user bi domain body.
   l4_whnf_method543 rec g ty = L4KAccept491 (L4KPi447 user bi domain body) ==>
   l4_core_projection_field577 0 rec fuel g owner value T idx ty =
     l4_kr_bind491 (l4_projection_verify_prop577 rec fuel g domain)
       (\ignored. L4KAccept491 domain)`,
  SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_skip_nondependent577 = prove
 (`!skip rec fuel g owner value maybe_prop idx ty user bi domain body.
   l4_whnf_method543 rec g ty = L4KAccept491 (L4KPi447 user bi domain body) /\
   ~l4_core_occurs532 0 body ==>
   l4_core_projection_field577 (SUC skip) rec fuel g owner value maybe_prop idx ty =
   l4_core_projection_field577 skip rec fuel g owner value maybe_prop (SUC idx)
     (l4_kinst447 body (L4KProj447 owner idx value))`,
  SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_skip_dependent_prop577 = prove
 (`!skip rec fuel g owner value idx ty user bi domain body.
   l4_whnf_method543 rec g ty = L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_core_occurs532 0 body ==>
   l4_core_projection_field577 (SUC skip) rec fuel g owner value T idx ty =
     l4_kr_bind491 (l4_projection_verify_prop577 rec fuel g domain)
       (\ignored. l4_core_projection_field577 skip rec fuel g owner value T
         (SUC idx) (l4_kinst447 body (L4KProj447 owner idx value)))`,
  SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_field_whnf_reject577 = prove
 (`!skip rec fuel g owner value maybe_prop idx ty reason.
   l4_whnf_method543 rec g ty = L4KReject491 reason ==>
   l4_core_projection_field577 skip rec fuel g owner value maybe_prop idx ty =
     L4KReject491 reason`,
  INDUCT_TAC THEN SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_field_whnf_decline577 = prove
 (`!skip rec fuel g owner value maybe_prop idx ty reason.
   l4_whnf_method543 rec g ty = L4KDecline491 reason ==>
   l4_core_projection_field577 skip rec fuel g owner value maybe_prop idx ty =
     L4KDecline491 reason`,
  INDUCT_TAC THEN SIMP_TAC [l4_core_projection_field577;l4_kr_bind491]);;
let l4_projection_infer_reject577 = prove
 (`!rec fuel env g owner idx value reason.
   l4_infer_method543 rec g value = L4KReject491 reason ==>
   l4_core_infer_projection577 rec fuel env g owner idx value = L4KReject491 reason`,
  SIMP_TAC [l4_core_infer_projection577;l4_kr_bind491]);;
let l4_projection_infer_decline577 = prove
 (`!rec fuel env g owner idx value reason.
   l4_infer_method543 rec g value = L4KDecline491 reason ==>
   l4_core_infer_projection577 rec fuel env g owner idx value = L4KDecline491 reason`,
  SIMP_TAC [l4_core_infer_projection577;l4_kr_bind491]);;
let l4_projection_inferred_whnf_reject577 = prove
 (`!rec fuel env g owner idx value ty reason.
   l4_infer_method543 rec g value = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KReject491 reason ==>
   l4_core_infer_projection577 rec fuel env g owner idx value = L4KReject491 reason`,
  SIMP_TAC [l4_core_infer_projection577;l4_kr_bind491]);;
let l4_projection_inferred_whnf_decline577 = prove
 (`!rec fuel env g owner idx value ty reason.
   l4_infer_method543 rec g value = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KDecline491 reason ==>
   l4_core_infer_projection577 rec fuel env g owner idx value = L4KDecline491 reason`,
  SIMP_TAC [l4_core_infer_projection577;l4_kr_bind491]);;
