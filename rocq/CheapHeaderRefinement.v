(* SPDX-License-Identifier: Apache-2.0
   Exact pre-change entry and preparation-boundary lemmas; test/proof root only. *)
From LeanPort Require Import Syntax Checker Declarations DagScope DagArena
  DagAdmission DagTheoremOpaque IndexedDagAdmission LookupIntegration RuntimeChecker
  CombinedAdmissionRefinement.

(* Exact pre-cheap-header indexed body, instantiated with the NEW repaired
   Checker. This is not the old pre-String frozen executable's semantics. *)
Definition before_header_indexed_admit hash kind budget fuel env n ps rows tr br : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) tr ;;
  body <- scope_ref (arena_scope arena) br ;;
  let lookup := prepare_lookup hash env in
  PreparedDag.in_arena lookup env kind budget fuel n ps arena tr br ty body.

Lemma before_header_indexed_refines hash kind budget fuel env n ps rows tr br :
  before_header_indexed_admit hash kind budget fuel env n ps rows tr br =
    linear_env_admit kind budget fuel env n ps rows tr br.
Proof.
  unfold before_header_indexed_admit, linear_env_admit.
  destruct kind; unfold DagAdmission.admit_dag_definition,
    DagTheoremOpaque.admit_dag_theorem, DagTheoremOpaque.admit_dag_opaque;
    destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) tr) eqn:Htype; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) br) eqn:Hbody; cbn [bind]; try reflexivity.
  all: apply PreparedDag.in_arena_refines; auto using prepare_lookup_correct;
    eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Definition before_header_guarded kind budget fuel env n ps rows tr br :=
  if RuntimeChecker.use_index fuel env
  then before_header_indexed_admit suffix_bitfold8 kind budget fuel env n ps rows tr br
  else linear_env_admit kind budget fuel env n ps rows tr br.

Theorem cheap_header_full_result_refines hash kind budget fuel env n ps rows tr br :
  indexed_admit hash kind budget fuel env n ps rows tr br =
    before_header_indexed_admit hash kind budget fuel env n ps rows tr br.
Proof. rewrite indexed_admit_refines, before_header_indexed_refines. reflexivity. Qed.

Theorem cheap_header_guarded_full_result_refines kind budget fuel env n ps rows tr br :
  indexed_dag_admit kind budget fuel env n ps rows tr br =
    before_header_guarded kind budget fuel env n ps rows tr br.
Proof.
  unfold indexed_dag_admit, before_header_guarded.
  destruct (RuntimeChecker.use_index fuel env); auto using cheap_header_full_result_refines.
Qed.

(* Arbitrary preparation functions are irrelevant on this branch, including
   the test-only counter callback. Decode and BOTH roots must already succeed. *)
Theorem early_reject_independent_of_preparation prepare kind budget fuel env n ps
    rows tr br arena ty body reason :
  arena_build empty_arena rows = Accept arena ->
  scope_ref (arena_scope arena) tr = Accept ty ->
  scope_ref (arena_scope arena) br = Accept body ->
  early_header_error kind env n ps ty = Some reason ->
  admit_with_preparation prepare kind budget fuel env n ps rows tr br = Reject reason.
Proof.
  intros Build Htype Hbody Error. unfold admit_with_preparation.
  rewrite Build. cbn [bind]. rewrite Htype. cbn [bind]. rewrite Hbody.
  cbn [bind]. rewrite Error. reflexivity.
Qed.

Print Assumptions cheap_header_full_result_refines.
Print Assumptions cheap_header_guarded_full_result_refines.
Print Assumptions early_reject_independent_of_preparation.
