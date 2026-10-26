(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   ALL PROPOSED SCRIPTS UNCOMPILED / UNEXECUTED.
   Premises concern actual606/521/630 results, not supplied verdict callbacks.
   Operational equations only: no admitted-environment or soundness claim. *)
needs "hol/checked_minors630.ml";;

let l4_recursive_args_empty630 = prove
 (`!fuel env ps stats s. l4_build_recursive_args630 [] fuel env ps stats s = L4KAccept491 ([],s)`,
  REWRITE_TAC [l4_build_recursive_args630]);;

let l4_minors_empty630 = prove
 (`!owner fuel env ps stats motives s.
   l4_build_minors630 [] owner fuel env ps stats motives s = L4KAccept491 ([],s)`,
  REWRITE_TAC [l4_build_minors630]);;

let l4_all_minors_empty630 = prove
 (`!owner fuel env ps stats motives s.
   l4_build_all_minors630 [] owner fuel env ps stats motives s = L4KAccept491 ([],s)`,
  REWRITE_TAC [l4_build_all_minors630]);;

let l4_recursive_args_skip_state630 = prove
 (`!x fields fuel env ps stats s args body s1 rest s2.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KAccept491 (args,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KAccept491 (rest,s2) /\
   l4_valid_ind_app521 stats body = NONE ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s = L4KAccept491 (rest,s2)`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

let l4_recursive_args_record630 = prove
 (`!x fields fuel env ps stats s args body s1 rest s2 i.
   l4_open_telescope606 fuel fuel env ps s (l4_klocal_type489 x) = L4KAccept491 (args,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KAccept491 (rest,s2) /\
   l4_valid_ind_app521 stats body = SOME i ==>
   l4_build_recursive_args630 (CONS x fields) fuel env ps stats s =
     L4KAccept491 (CONS (L4KIndRecursiveArg516 x args i (l4_ind_app_indices521 stats body)) rest,s2)`,
  SIMP_TAC [l4_build_recursive_args630;l4_kr_bind491]);;

(* The body has NO valid_ind_app premise: the original algorithm uses raw
   indices here. c is retained whole, including metadata, not reconstructed. *)
let l4_minors_construct630 = prove
 (`!c ctors owner fuel env ps stats motives s ty fields body s1 recursive s2 ihs s3 m minor s4 rest s5.
   l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps s (l4_kdecl_type493 c) = L4KAccept491 ty /\
   l4_open_telescope606 fuel fuel env ps s ty = L4KAccept491 (fields,(body,s1)) /\
   l4_build_recursive_args630 fields fuel env ps stats s1 = L4KAccept491 (recursive,s2) /\
   l4_build_ihs521 recursive motives s2 = L4KAccept491 (ihs,s3) /\
   owner < LENGTH motives /\ EL owner motives = m /\
   l4_kind_fresh491 s3 (l4_kdecl_name493 c) L4KDefault447
     (l4_kclose_pi489 fields (l4_kclose_pi489 ihs
       (L4KApp447
         (l4_kapply_exprs489 (l4_ind_app_indices521 stats body) (l4_klocal_expr489 (l4_kmotive_local516 m)))
         (l4_kapply_locals489 fields (l4_kapply_locals489 (l4_kstats_params516 stats)
           (L4KConst447 (l4_kdecl_name493 c) (l4_kstats_levels516 stats))))))) = (minor,s4) /\
   l4_build_minors630 ctors owner fuel env ps stats motives s4 = L4KAccept491 (rest,s5) ==>
   l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives s =
     L4KAccept491 (CONS (L4KIndMinor516 c owner minor fields recursive) rest,s5)`,
  SIMP_TAC [l4_build_minors630;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_all_minors_append630 = prove
 (`!t types owner fuel env ps stats motives s first s1 rest s2.
   l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives s =
     L4KAccept491 (first,s1) /\
   l4_build_all_minors630 types (SUC owner) fuel env ps stats motives s1 = L4KAccept491 (rest,s2) ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s =
     L4KAccept491 (APPEND first rest,s2)`,
  SIMP_TAC [l4_build_all_minors630;l4_kr_bind491]);;

let l4_all_minors_empty_ctor_advances_owner630 = prove
 (`!t types owner fuel env ps stats motives s rest s1.
   l4_kspec_ctors493 (l4_kchecked_spec516 t) = [] /\
   l4_build_all_minors630 types (SUC owner) fuel env ps stats motives s = L4KAccept491 (rest,s1) ==>
   l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives s = L4KAccept491 (rest,s1)`,
  SIMP_TAC [l4_build_all_minors630;l4_build_minors630;l4_kr_bind491;APPEND]);;
