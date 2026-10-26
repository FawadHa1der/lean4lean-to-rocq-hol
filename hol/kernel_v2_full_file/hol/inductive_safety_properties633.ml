(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED OPERATIONAL PROOFS: ALL UNCOMPILED / NOT EXECUTED.
   Conditional calls are the concrete634 admission, never a verdict oracle. *)
needs "hol/inductive_safety633.ml";;

let l4_mark_unsafe_payload633 = prove
 (`!d.
   l4_kdecl_name493 (l4_mark_unsafe_inductive633 d) = l4_kdecl_name493 d /\
   l4_kdecl_params493 (l4_mark_unsafe_inductive633 d) = l4_kdecl_params493 d /\
   l4_kdecl_type493 (l4_mark_unsafe_inductive633 d) = l4_kdecl_type493 d /\
   l4_kdecl_value493 (l4_mark_unsafe_inductive633 d) = l4_kdecl_value493 d /\
   l4_kdecl_hints493 (l4_mark_unsafe_inductive633 d) = l4_kdecl_hints493 d`,
  REWRITE_TAC [l4_mark_unsafe_inductive633;l4_kdecl_name493;l4_kdecl_params493;
    l4_kdecl_type493;l4_kdecl_value493;l4_kdecl_hints493]);;

let l4_mark_unsafe_kind633 = prove
 (`!d. l4_kdecl_kind493 (l4_mark_unsafe_inductive633 d) = L4KDUnsafe493 (l4_kdecl_kind493 d)`,
  REWRITE_TAC [l4_mark_unsafe_inductive633;l4_kdecl_kind493]);;

let l4_marked_inductive_safe_view633 = prove
 (`!d. l4_kdecl_kind493 (l4_checking_view624 L4InputSafe607 (l4_mark_unsafe_inductive633 d)) =
   L4KDUnsafe493 (l4_kdecl_kind493 d)`,
  REWRITE_TAC [l4_checking_view624;l4_mark_unsafe_inductive633;l4_kdecl_kind493;
    LET_DEF;LET_END_DEF]);;

let l4_marked_inductive_unsafe_view633 = prove
 (`!d. l4_kdecl_kind493 (l4_checking_view624 L4InputUnsafe607 (l4_mark_unsafe_inductive633 d)) =
   l4_kdecl_kind493 d`,
  REWRITE_TAC [l4_checking_view624;l4_mark_unsafe_inductive633;l4_kdecl_kind493;
    LET_DEF;LET_END_DEF]);;

let l4_marked_inductive_partial_view633 = prove
 (`!d. l4_kdecl_kind493 (l4_checking_view624 L4InputPartial607 (l4_mark_unsafe_inductive633 d)) =
   L4KDUnsafe493 (l4_kdecl_kind493 d)`,
  REWRITE_TAC [l4_checking_view624;l4_mark_unsafe_inductive633;l4_kdecl_kind493;
    LET_DEF;LET_END_DEF]);;

let l4_inductive_safe_delegation633 = prove
 (`!fuel env types ctors recs. ~l4_inductive_input_unsafe633 types ==>
   l4_admit_inductive_extended633 fuel env types ctors recs =
   l4_admit_inductive_nested634 fuel env types ctors recs`,
  SIMP_TAC [l4_admit_inductive_extended633]);;

let l4_inductive_unsafe_success633 = prove
 (`!fuel env types ctors recs checked.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KAccept491 checked ==>
   l4_admit_inductive_extended633 fuel env types ctors recs =
   L4KAccept491 (APPEND (MAP l4_mark_unsafe_inductive633
     (FILTER (\d. match l4_kfind_decl493 env (l4_kdecl_name493 d) with
                   | NONE -> T | SOME old -> F) checked)) env)`,
  SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_inductive_unsafe_reject633 = prove
 (`!fuel env types ctors recs reason.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KReject491 reason ==>
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_inductive_unsafe_decline633 = prove
 (`!fuel env types ctors recs reason.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KDecline491 reason ==>
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_marked_prefix_restricted633 = prove
 (`!ds. ALL (\d. ?kind. l4_kdecl_kind493 d = L4KDUnsafe493 kind)
   (MAP l4_mark_unsafe_inductive633 ds)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;ALL;l4_mark_unsafe_kind633] THEN MESON_TAC []);;

let l4_inductive_success_has_restricted_prefix633 = prove
 (`!fuel env types ctors recs checked.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
     types ctors recs = L4KAccept491 checked ==>
   ?additions.
     l4_admit_inductive_extended633 fuel env types ctors recs = L4KAccept491 (APPEND additions env) /\
     ALL (\d. ?kind. l4_kdecl_kind493 d = L4KDUnsafe493 kind) additions`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `MAP l4_mark_unsafe_inductive633
    (FILTER (\d. match l4_kfind_decl493 env (l4_kdecl_name493 d) with
                  | NONE -> T | SOME old -> F) checked)` THEN
  ASM_SIMP_TAC [l4_admit_inductive_extended633;l4_kr_bind491;LET_DEF;LET_END_DEF;
    l4_marked_prefix_restricted633]);;

let l4_inductive_input_flag633 = prove
 (`!n ps ty value np ni all ctors nn recursive reflexive unsafe hints rest.
   l4_inductive_input_unsafe633
     (CONS (L4KDeclaration493 n ps ty value
       (L4KDInductive493 (L4KInductiveData493 np ni all ctors nn recursive reflexive unsafe)) hints) rest)
   <=> unsafe`,
  REWRITE_TAC [l4_inductive_input_unsafe633;l4_kdecl_kind493;l4_kind_is_unsafe493]);;

let l4_inductive_mark_keeps_inner_metadata633 = prove
 (`!n ps ty value info hints.
   l4_kdecl_kind493 (l4_mark_unsafe_inductive633
     (L4KDeclaration493 n ps ty value (L4KDInductive493 info) hints)) =
   L4KDUnsafe493 (L4KDInductive493 info)`,
  REWRITE_TAC [l4_mark_unsafe_kind633;l4_kdecl_kind493]);;

let l4_inductive_marks_all_generated_roles633 = prove
 (`!n ps ty value ci ri hints.
   l4_kdecl_kind493 (l4_mark_unsafe_inductive633
     (L4KDeclaration493 n ps ty value (L4KDConstructor493 ci) hints)) =
       L4KDUnsafe493 (L4KDConstructor493 ci) /\
   l4_kdecl_kind493 (l4_mark_unsafe_inductive633
     (L4KDeclaration493 n ps ty value (L4KDRecursor493 ri) hints)) =
       L4KDUnsafe493 (L4KDRecursor493 ri)`,
  REWRITE_TAC [l4_mark_unsafe_kind633;l4_kdecl_kind493]);;

let l4_inductive_admission_result_cases633 = prove
 (`!r:(l4_kdeclaration493 list)l4_kresult491.
   (?checked. r = L4KAccept491 checked) \/
   (?reason. r = L4KReject491 reason) \/
   (?reason. r = L4KDecline491 reason)`,
  MATCH_MP_TAC l4_kresult_INDUCT491 THEN MESON_TAC []);;

(* Same accepted-output restriction statement as InductiveSafety.v42-48.
   Proposed result-case proof only; no assumption of nested admission success. *)
let l4_unsafe_inductive_admission_preserves_restrictions633 = prove
 (`!fuel env types ctors recs next.
   l4_inductive_input_unsafe633 types /\
   l4_admit_inductive_extended633 fuel env types ctors recs = L4KAccept491 next ==>
   ?additions. next = APPEND additions env /\
     ALL (\d. ?kind. l4_kdecl_kind493 d = L4KDUnsafe493 kind) additions`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC
    `l4_admit_inductive_nested634 fuel (l4_safety_environment624 L4InputUnsafe607 env)
       types ctors recs`
    l4_inductive_admission_result_cases633) THEN
  ASM_MESON_TAC [l4_inductive_success_has_restricted_prefix633;
    l4_inductive_unsafe_reject633;l4_inductive_unsafe_decline633;
    distinctness "l4_kresult491";injectivity "l4_kresult491"]);;
