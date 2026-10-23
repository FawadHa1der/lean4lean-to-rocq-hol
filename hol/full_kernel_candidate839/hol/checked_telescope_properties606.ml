(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Conditional equations of actual597 calls. ALL SCRIPTS UNCOMPILED.
   These are not assumed proof callbacks or typing/admission theorems. *)
needs "hol/checked_telescope606.ml";;

let l4_ind_sort_infer_reject606 = prove
 (`!fuel env ps state e reason.
   l4_infer597 fuel env ps (l4_kstate_context532 state) e = L4KReject491 reason ==>
   l4_ind_sort606 fuel env ps state e = L4KReject491 reason`,
  SIMP_TAC [l4_ind_sort606;l4_kr_bind491]);;

let l4_ind_sort_whnf_decline606 = prove
 (`!fuel env ps state e ty reason.
   l4_infer597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 ty /\
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KDecline491 reason ==>
   l4_ind_sort606 fuel env ps state e = L4KDecline491 reason`,
  SIMP_TAC [l4_ind_sort606;l4_kr_bind491]);;

let l4_ind_sort_success606 = prove
 (`!fuel env ps state e ty u.
   l4_infer597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 ty /\
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KAccept491 (L4KSort447 u) ==>
   l4_ind_sort606 fuel env ps state e = L4KAccept491 u`,
  SIMP_TAC [l4_ind_sort606;l4_kr_bind491]);;

let l4_ind_sort_expected_sort606 = prove
 (`!fuel env ps state e ty n.
   l4_infer597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 ty /\
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KAccept491 (L4KNatLit447 n) ==>
   l4_ind_sort606 fuel env ps state e = L4KReject491 L4KExpectedSort491`,
  SIMP_TAC [l4_ind_sort606;l4_kr_bind491]);;

let l4_checked_domain_fast606 = prove
 (`!fuel env ps state a.
   l4_kexpr_eqb480 a (l4_consume_type_annotations606 a) ==>
   l4_checked_domain606 fuel env ps state a = L4KAccept491 a`,
  SIMP_TAC [l4_checked_domain606;LET_DEF;LET_END_DEF]);;

let l4_checked_domain_false606 = prove
 (`!fuel env ps state a cleaned.
   l4_consume_type_annotations606 a = cleaned /\ ~l4_kexpr_eqb480 a cleaned /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) a cleaned = L4KAccept491 F ==>
   l4_checked_domain606 fuel env ps state a = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_checked_domain606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_checked_domain_reject606 = prove
 (`!fuel env ps state a cleaned reason.
   l4_consume_type_annotations606 a = cleaned /\ ~l4_kexpr_eqb480 a cleaned /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) a cleaned = L4KReject491 reason ==>
   l4_checked_domain606 fuel env ps state a = L4KReject491 reason`,
  SIMP_TAC [l4_checked_domain606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_checked_domain_decline606 = prove
 (`!fuel env ps state a cleaned reason.
   l4_consume_type_annotations606 a = cleaned /\ ~l4_kexpr_eqb480 a cleaned /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) a cleaned = L4KDecline491 reason ==>
   l4_checked_domain606 fuel env ps state a = L4KDecline491 reason`,
  SIMP_TAC [l4_checked_domain606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_checked_domain_true606 = prove
 (`!fuel env ps state a cleaned.
   l4_consume_type_annotations606 a = cleaned /\ ~l4_kexpr_eqb480 a cleaned /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) a cleaned = L4KAccept491 T ==>
   l4_checked_domain606 fuel env ps state a = L4KAccept491 cleaned`,
  SIMP_TAC [l4_checked_domain606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_open_telescope_whnf_reject606 = prove
 (`!depth fuel env ps state ty reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KReject491 reason ==>
   l4_open_telescope606 (SUC depth) fuel env ps state ty = L4KReject491 reason`,
  SIMP_TAC [l4_open_telescope606;l4_kr_bind491]);;

let l4_open_telescope_whnf_decline606 = prove
 (`!depth fuel env ps state ty reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KDecline491 reason ==>
   l4_open_telescope606 (SUC depth) fuel env ps state ty = L4KDecline491 reason`,
  SIMP_TAC [l4_open_telescope606;l4_kr_bind491]);;

let l4_open_telescope_end606 = prove
 (`!depth fuel env ps state ty u.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KAccept491 (L4KSort447 u) ==>
   l4_open_telescope606 (SUC depth) fuel env ps state ty =
     L4KAccept491 ([],(L4KSort447 u,state))`,
  SIMP_TAC [l4_open_telescope606;l4_kr_bind491]);;

let l4_open_telescope_domain_reject606 = prove
 (`!depth fuel env ps state ty user bi domain body reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_checked_domain606 fuel env ps state domain = L4KReject491 reason ==>
   l4_open_telescope606 (SUC depth) fuel env ps state ty = L4KReject491 reason`,
  SIMP_TAC [l4_open_telescope606;l4_kr_bind491]);;

let l4_open_telescope_pi606 = prove
 (`!depth fuel env ps state ty user bi domain body cleaned.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_checked_domain606 fuel env ps state domain = L4KAccept491 cleaned ==>
   l4_open_telescope606 (SUC depth) fuel env ps state ty =
     let fresh = l4_kind_fresh491 state user bi cleaned in
     l4_kr_bind491
       (l4_open_telescope606 depth fuel env ps (SND fresh)
         (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
       (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))`,
  SIMP_TAC [l4_open_telescope606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_open_parameters_whnf_decline606 = prove
 (`!count fuel env ps state ty reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KDecline491 reason ==>
   l4_open_parameters606 (SUC count) fuel env ps state ty = L4KDecline491 reason`,
  SIMP_TAC [l4_open_parameters606;l4_kr_bind491]);;

let l4_open_parameters_nonpi606 = prove
 (`!count fuel env ps state ty u.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KAccept491 (L4KSort447 u) ==>
   l4_open_parameters606 (SUC count) fuel env ps state ty = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_open_parameters606;l4_kr_bind491]);;

let l4_open_parameters_domain_decline606 = prove
 (`!count fuel env ps state ty user bi domain body reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_checked_domain606 fuel env ps state domain = L4KDecline491 reason ==>
   l4_open_parameters606 (SUC count) fuel env ps state ty = L4KDecline491 reason`,
  SIMP_TAC [l4_open_parameters606;l4_kr_bind491]);;

let l4_open_parameters_pi606 = prove
 (`!count fuel env ps state ty user bi domain body cleaned.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_checked_domain606 fuel env ps state domain = L4KAccept491 cleaned ==>
   l4_open_parameters606 (SUC count) fuel env ps state ty =
     let fresh = l4_kind_fresh491 state user bi cleaned in
     l4_kr_bind491
       (l4_open_parameters606 count fuel env ps (SND fresh)
         (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
       (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))`,
  SIMP_TAC [l4_open_parameters606;LET_DEF;LET_END_DEF;l4_kr_bind491]);;

let l4_apply_parameters_false606 = prove
 (`!x xs fuel env ps state ty user bi domain body.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) domain (l4_klocal_type489 x) =
     L4KAccept491 F ==>
   l4_apply_parameters606 (CONS x xs) fuel env ps state ty = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_apply_parameters606;l4_kr_bind491]);;

let l4_apply_parameters_decline606 = prove
 (`!x xs fuel env ps state ty user bi domain body reason.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) domain (l4_klocal_type489 x) =
     L4KDecline491 reason ==>
   l4_apply_parameters606 (CONS x xs) fuel env ps state ty = L4KDecline491 reason`,
  SIMP_TAC [l4_apply_parameters606;l4_kr_bind491]);;

let l4_apply_parameters_true606 = prove
 (`!x xs fuel env ps state ty user bi domain body.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty =
     L4KAccept491 (L4KPi447 user bi domain body) /\
   l4_defeq597 fuel env ps (l4_kstate_context532 state) domain (l4_klocal_type489 x) =
     L4KAccept491 T ==>
   l4_apply_parameters606 (CONS x xs) fuel env ps state ty =
     l4_apply_parameters606 xs fuel env ps state (l4_kinst447 body (l4_klocal_expr489 x))`,
  SIMP_TAC [l4_apply_parameters606;l4_kr_bind491]);;

let l4_apply_parameters_nonpi606 = prove
 (`!x xs fuel env ps state ty u.
   l4_whnf597 fuel env ps (l4_kstate_context532 state) ty = L4KAccept491 (L4KSort447 u) ==>
   l4_apply_parameters606 (CONS x xs) fuel env ps state ty = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_apply_parameters606;l4_kr_bind491]);;
