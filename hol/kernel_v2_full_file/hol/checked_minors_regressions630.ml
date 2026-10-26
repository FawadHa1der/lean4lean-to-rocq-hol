(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   ALL PROPOSED SCRIPTS UNCOMPILED / UNEXECUTED. No model/native tests run.
   Adversarial ordering and raw-admission boundaries of the actual functions. *)
needs "hol/checked_minors630.ml";;

let l4_recursive_args_zero_nonempty630 = prove
 (`!x fields env ps stats s.
   l4_build_recursive_args630 (CONS x fields) 0 env ps stats s = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_build_recursive_args630;l4_open_telescope606;l4_kr_bind491]);;

let l4_minors_zero_empty_params630 = prove
 (`!c ctors owner env ps stats motives s.
   l4_kstats_params516 stats = [] ==>
   l4_build_minors630 (CONS c ctors) owner 0 env ps stats motives s = L4KDecline491 L4KOutOfFuel491`,
  SIMP_TAC [l4_build_minors630;l4_apply_parameters606;l4_open_telescope606;l4_kr_bind491]);;

let l4_recursive_args_open_reject630 = prove
 (`!x fields fuel env ps stats s reason.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KReject491 reason ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s = L4KReject491 reason`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

let l4_recursive_args_open_decline630 = prove
 (`!x fields fuel env ps stats s reason.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KDecline491 reason ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

(* No premise about the current body's validity: the tail fails first. *)
let l4_recursive_args_tail_reject630 = prove
 (`!x fields fuel env ps stats s args body s1 reason.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KAccept491 (args,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KReject491 reason ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s = L4KReject491 reason`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

let l4_recursive_args_tail_decline630 = prove
 (`!x fields fuel env ps stats s args body s1 reason.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KAccept491 (args,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KDecline491 reason ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

(* owner and motives are unrestricted, including out-of-range/empty. *)
let l4_minors_parameter_reject_before_owner630 = prove
 (`!c ctors owner fuel env ps stats motives s reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KReject491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491]);;

let l4_minors_parameter_decline_before_owner630 = prove
 (`!c ctors owner fuel env ps stats motives s reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KDecline491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491]);;

let l4_minors_open_reject630 = prove
 (`!c ctors owner fuel env ps stats motives s ty reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KReject491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491]);;

let l4_minors_open_decline630 = prove
 (`!c ctors owner fuel env ps stats motives s ty reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KDecline491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491]);;

let l4_minors_recursive_reject630 = prove
 (`!c ctors owner fuel env ps stats motives s ty fields body s1 reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KAccept491 (fields,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KReject491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_minors_recursive_decline630 = prove
 (`!c ctors owner fuel env ps stats motives s ty fields body s1 reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KAccept491 (fields,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KDecline491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_minors_ih_reject630 = prove
 (`!c ctors owner fuel env ps stats motives s ty fields body s1 recursive s2 reason.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KAccept491 (fields,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KAccept491 (recursive,s2) /\
   l4_build_ihs521 recursive motives s2 = L4KReject491 reason ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_minors_owner_bound630 = prove
 (`!c ctors owner fuel env ps stats motives s ty fields body s1 recursive s2 ihs s3.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KAccept491 (fields,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KAccept491 (recursive,s2) /\
   l4_build_ihs521 recursive motives s2 = L4KAccept491 (ihs,s3) /\
   ~(owner < LENGTH motives) ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_all_minors_first_reject630 = prove
 (`!t types owner fuel env ps stats motives s reason.
   l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives s =
     L4KReject491 reason ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_all_minors630;l4_kr_bind491]);;

let l4_all_minors_first_decline630 = prove
 (`!t types owner fuel env ps stats motives s reason.
   l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives s =
     L4KDecline491 reason ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_all_minors630;l4_kr_bind491]);;

let l4_all_minors_tail_reject630 = prove
 (`!t types owner fuel env ps stats motives s first s1 reason.
   l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives s =
     L4KAccept491 (first,s1) /\
   l4_build_all_minors630 types (SUC owner) fuel env ps stats motives s1 = L4KReject491 reason ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s = L4KReject491 reason`,
  SIMP_TAC [l4_build_all_minors630;l4_kr_bind491]);;

let l4_all_minors_tail_decline630 = prove
 (`!t types owner fuel env ps stats motives s first s1 reason.
   l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives s =
     L4KAccept491 (first,s1) /\
   l4_build_all_minors630 types (SUC owner) fuel env ps stats motives s1 = L4KDecline491 reason ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s = L4KDecline491 reason`,
  SIMP_TAC [l4_build_all_minors630;l4_kr_bind491]);;
