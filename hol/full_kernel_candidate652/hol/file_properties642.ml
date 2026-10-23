(* SPDX-License-Identifier: Apache-2.0. ALL PROPOSED SCRIPTS UNCOMPILED.
   Operational boundary lemmas, not source parsing or Lean soundness proofs. *)
needs "hol/file_driver642.ml";;

let l4_file_empty_schedule642 = prove
 (`l4_file_schedule_rows642 [] = [] /\ l4_file_coverage642 0 []`,
  REWRITE_TAC [l4_file_schedule_rows642;l4_file_coverage642;LET_DEF;LET_END_DEF;
    LENGTH;ALL;l4_file_indices_unique642]);;

let l4_file_single_member642 = prove
 (`!i. l4_file_schedule_rows642 [L4FileSingle642 i] = [i]`,
  REWRITE_TAC [l4_file_schedule_rows642;l4_file_batch_members642;APPEND]);;

let l4_file_mutual_leader_not_extra_row642 = prove
 (`!leader members. l4_file_schedule_rows642 [L4FileMutual642 leader members] = members`,
  REWRITE_TAC [l4_file_schedule_rows642;l4_file_batch_members642;APPEND_NIL]);;

let l4_file_duplicate_plan_refused642 = prove
 (`!count i. ~l4_file_coverage642 count [L4FileSingle642 i;L4FileSingle642 i]`,
  REWRITE_TAC [l4_file_coverage642;l4_file_schedule_rows642;l4_file_batch_members642;
    LET_DEF;LET_END_DEF;APPEND;l4_file_indices_unique642;MEM]);;

let l4_file_out_of_range_plan_refused642 = prove
 (`!count. ~l4_file_coverage642 count [L4FileSingle642 count]`,
  REWRITE_TAC [l4_file_coverage642;l4_file_schedule_rows642;l4_file_batch_members642;
    LET_DEF;LET_END_DEF;APPEND;ALL;LT_REFL]);;

let l4_file_dropped_nonempty_input642 = prove
 (`!count. ~l4_file_coverage642 (SUC count) []`,
  REWRITE_TAC [l4_file_coverage642;l4_file_schedule_rows642;
    LET_DEF;LET_END_DEF;LENGTH;NOT_SUC]);;

let l4_file_zero_single642 = prove
 (`l4_file_coverage642 1 [L4FileSingle642 0]`,
  REWRITE_TAC [l4_file_coverage642;l4_file_schedule_rows642;l4_file_batch_members642;
    LET_DEF;LET_END_DEF;APPEND;ALL;LENGTH;l4_file_indices_unique642;MEM] THEN ARITH_TAC);;

let l4_file_empty_resolve642 = prove
 (`!rows. l4_file_resolve_members642 [] rows = L4KAccept491 []`,
  REWRITE_TAC [l4_file_resolve_members642]);;

let l4_file_bad_member_bounds642 = prove
 (`!i rest rows. ~(i < LENGTH rows) ==>
   l4_file_resolve_members642 (CONS i rest) rows = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_file_resolve_members642]);;

let l4_file_partial_must_group642 = prove
 (`!fuel env hints n ps ty value all.
   l4_file_admit_single642 fuel env
     (L4FileOrdinary642 (L4InputDefinition607 hints n ps ty value L4InputPartial607) all) =
   L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_file_admit_single642;l4_file_requires_mutual642]);;

let l4_file_multi_unsafe_must_group642 = prove
 (`!fuel env hints n ps ty value all. 1 < LENGTH all ==>
   l4_file_admit_single642 fuel env
     (L4FileOrdinary642 (L4InputDefinition607 hints n ps ty value L4InputUnsafe607) all) =
   L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_file_admit_single642;l4_file_requires_mutual642]);;

let l4_file_safe_definition_actual_admission642 = prove
 (`!fuel env hints n ps ty value all.
   l4_file_admit_single642 fuel env
     (L4FileOrdinary642 (L4InputDefinition607 hints n ps ty value L4InputSafe607) all) =
   l4_admit_extended624 fuel env (L4InputDefinition607 hints n ps ty value L4InputSafe607)`,
  REWRITE_TAC [l4_file_admit_single642;l4_file_requires_mutual642;
    distinctness "l4_input_safety607"]);;

let l4_file_quotient_actual_admission642 = prove
 (`!fuel env n ps ty kind.
   l4_file_admit_single642 fuel env (L4FileQuotient642 n ps ty kind) =
     l4_admit_quotient608 fuel env n ps ty kind`,
  REWRITE_TAC [l4_file_admit_single642;l4_file_requires_mutual642]);;

let l4_file_inductive_actual_admission642 = prove
 (`!fuel env types ctors recs.
   l4_file_admit_single642 fuel env (L4FileInductive642 types ctors recs) =
     l4_admit_inductive_extended633 fuel env types ctors recs`,
  REWRITE_TAC [l4_file_admit_single642;l4_file_requires_mutual642]);;

let l4_file_single_bounds642 = prove
 (`!fuel env rows i. ~(i < LENGTH rows) ==>
   l4_file_check_batch642 fuel env rows (L4FileSingle642 i) =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_file_check_batch642]);;

let l4_file_mutual_leader_required642 = prove
 (`!fuel env rows leader indices. ~MEM leader indices ==>
   l4_file_check_batch642 fuel env rows (L4FileMutual642 leader indices) =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_file_check_batch642]);;

let l4_file_batches_empty642 = prove
 (`!fuel env rows. l4_file_check_batches642 [] fuel env rows = L4KAccept491 env`,
  REWRITE_TAC [l4_file_check_batches642]);;

let l4_file_batch_reject_stops642 = prove
 (`!fuel env rows batch rest reason.
   l4_file_check_batch642 fuel env rows batch = L4KReject491 reason ==>
   l4_file_check_batches642 (CONS batch rest) fuel env rows = L4KReject491 reason`,
  SIMP_TAC [l4_file_check_batches642;l4_kr_bind491]);;

let l4_file_batch_decline_stops642 = prove
 (`!fuel env rows batch rest reason.
   l4_file_check_batch642 fuel env rows batch = L4KDecline491 reason ==>
   l4_file_check_batches642 (CONS batch rest) fuel env rows = L4KDecline491 reason`,
  SIMP_TAC [l4_file_check_batches642;l4_kr_bind491]);;

let l4_file_batch_threads_environment642 = prove
 (`!fuel env rows batch rest next.
   l4_file_check_batch642 fuel env rows batch = L4KAccept491 next ==>
   l4_file_check_batches642 (CONS batch rest) fuel env rows =
     l4_file_check_batches642 rest fuel next rows`,
  SIMP_TAC [l4_file_check_batches642;l4_kr_bind491]);;

let l4_file_unsupported_format642 = prove
 (`!fuel format lean hash nc lc ec rows batches. ~(format = [51;46;49;46;48]) ==>
   l4_check_file642 fuel (L4FileInput642 format lean hash nc lc ec rows) batches =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_check_file642]);;

let l4_file_duplicate_names_before_plan642 = prove
 (`!fuel lean hash nc lc ec rows batches.
   ~l4_names_unique437 (l4_kflatten516 (MAP (\row. l4_file_decl_names642 (SND row)) rows)) ==>
   l4_check_file642 fuel (L4FileInput642 [51;46;49;46;48] lean hash nc lc ec rows) batches =
     L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_check_file642]);;

let l4_file_accepted_requires_gates642 = prove
 (`!fuel format lean hash nc lc ec rows batches output.
   l4_check_file642 fuel (L4FileInput642 format lean hash nc lc ec rows) batches =
     L4KAccept491 output <=>
   format = [51;46;49;46;48] /\
   l4_names_unique437 (l4_kflatten516 (MAP (\row. l4_file_decl_names642 (SND row)) rows)) /\
   l4_file_coverage642 (LENGTH rows) batches /\
   l4_file_check_batches642 batches fuel [] rows = L4KAccept491 output`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_check_file642] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [distinctness "l4_kresult491"] THEN
  MESON_TAC []);;

let l4_file_observations_not_certified642 = prove
 (`!fuel format lean hash nc lc ec other_lean other_hash other_nc other_lc other_ec rows batches.
   l4_check_file642 fuel (L4FileInput642 format lean hash nc lc ec rows) batches =
   l4_check_file642 fuel
     (L4FileInput642 format other_lean other_hash other_nc other_lc other_ec rows) batches`,
  REWRITE_TAC [l4_check_file642]);;

let l4_file_empty_axiom_inventory642 = prove
 (`l4_file_axioms642 [] = []`,
  REWRITE_TAC [l4_file_axioms642]);;

let l4_file_axiom_inventory_keeps_claim642 = prove
 (`!line n ps ty unsafe all rest.
   l4_file_axioms642 (CONS (line,L4FileOrdinary642 (L4InputAxiom607 n ps ty unsafe) all) rest) =
   CONS (L4InputAxiom607 n ps ty unsafe) (l4_file_axioms642 rest)`,
  REWRITE_TAC [l4_file_axioms642;SND]);;
