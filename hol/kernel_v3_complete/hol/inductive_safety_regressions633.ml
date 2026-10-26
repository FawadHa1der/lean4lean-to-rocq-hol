(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED ADVERSARIAL/POSITIVE REGRESSIONS: ALL UNCOMPILED / NOT EXECUTED.
   Conditional accepted634 calls are hypotheses, never fabricated receipts. *)
needs "hol/inductive_safety_properties633.ml";;

let l4_inductive_empty_flag633 = prove
 (`~l4_inductive_input_unsafe633 []`,
  REWRITE_TAC [l4_inductive_input_unsafe633]);;

let l4_inductive_empty_delegates633 = prove
 (`!fuel env ctors recs. l4_admit_inductive_extended633 fuel env [] ctors recs =
   l4_admit_inductive_nested634 fuel env [] ctors recs`,
  REWRITE_TAC [l4_admit_inductive_extended633;l4_inductive_input_unsafe633]);;

let l4_inductive_wrapped_input_not_unwrapped633 = prove
 (`!n ps ty value info hints rest.
   ~l4_inductive_input_unsafe633
     (CONS (L4KDeclaration493 n ps ty value (L4KDUnsafe493 (L4KDInductive493 info)) hints) rest)`,
  REWRITE_TAC [l4_inductive_input_unsafe633;l4_kdecl_kind493]);;

let l4_inductive_noninductive_head_ignores_tail633 = prove
 (`!n ps ty value hints rest.
   ~l4_inductive_input_unsafe633
     (CONS (L4KDeclaration493 n ps ty value L4KDDefinition493 hints) rest)`,
  REWRITE_TAC [l4_inductive_input_unsafe633;l4_kdecl_kind493]);;

let l4_inductive_safe_head_ignores_tail633 = prove
 (`!n ps ty value np ni all ctors nn recursive reflexive hints rest.
   ~l4_inductive_input_unsafe633
     (CONS (L4KDeclaration493 n ps ty value
       (L4KDInductive493 (L4KInductiveData493 np ni all ctors nn recursive reflexive F)) hints) rest)`,
  REWRITE_TAC [l4_inductive_input_unsafe633;l4_kdecl_kind493;l4_kind_is_unsafe493]);;

let l4_inductive_nested_marker_not_collapsed633 = prove
 (`!n ps ty value kind hints.
   l4_kdecl_kind493 (l4_mark_unsafe_inductive633
     (L4KDeclaration493 n ps ty value (L4KDUnsafe493 kind) hints)) =
   L4KDUnsafe493 (L4KDUnsafe493 kind)`,
  REWRITE_TAC [l4_mark_unsafe_kind633;l4_kdecl_kind493]);;

let l4_inductive_original_tail_preserved633 = prove
 (`!fuel env types ctors recs new old.
   l4_inductive_input_unsafe633 types /\
   l4_kfind_decl493 env (l4_kdecl_name493 new) = NONE /\
   l4_kfind_decl493 env (l4_kdecl_name493 old) = SOME old /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KAccept491 [new;l4_checking_view624 L4InputUnsafe607 old] ==>
   l4_admit_inductive_extended633 fuel env types ctors recs =
     L4KAccept491 (CONS (l4_mark_unsafe_inductive633 new) env)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF;FILTER;MAP;APPEND;l4_checking_view624;l4_kdecl_name493]);;

let l4_inductive_filter_compares_names_not_records633 = prove
 (`!fuel env types ctors recs d old.
   l4_inductive_input_unsafe633 types /\
   l4_kfind_decl493 env (l4_kdecl_name493 d) = SOME old /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KAccept491 [d] ==>
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KAccept491 env`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF;FILTER;MAP;APPEND]);;

let l4_inductive_filtered_order_preserved633 = prove
 (`!fuel env types ctors recs a b old_decl previous.
   l4_inductive_input_unsafe633 types /\
   l4_kfind_decl493 env (l4_kdecl_name493 a) = NONE /\
   l4_kfind_decl493 env (l4_kdecl_name493 b) = NONE /\
   l4_kfind_decl493 env (l4_kdecl_name493 old_decl) = SOME previous /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KAccept491 [a;old_decl;b] ==>
   l4_admit_inductive_extended633 fuel env types ctors recs =
   L4KAccept491 (CONS (l4_mark_unsafe_inductive633 a)
     (CONS (l4_mark_unsafe_inductive633 b) env))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF;FILTER;MAP;APPEND]);;

let l4_inductive_no_wrapper_fuel_gate633 = prove
 (`!env types ctors recs.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 0 (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KReject491 L4KDuplicateDeclaration491 ==>
   l4_admit_inductive_extended633 0 env types ctors recs = L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_inductive_unsupported_decline_not_overridden633 = prove
 (`!fuel env types ctors recs.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KDecline491 L4KUnsupportedDeclaration491 ==>
   l4_admit_inductive_extended633 fuel env types ctors recs =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_inductive_safe_success_unmarked633 = prove
 (`!fuel env types ctors recs checked.
   ~l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KAccept491 checked ==>
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KAccept491 checked`,
  SIMP_TAC [l4_admit_inductive_extended633]);;
