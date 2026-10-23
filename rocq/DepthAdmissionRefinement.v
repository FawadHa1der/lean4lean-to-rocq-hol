(* SPDX-License-Identifier: Apache-2.0
   Direct equalities between depth and linear-cache algorithms instantiated
   with this tree's NEW ordinary Checker. Not old-executable equivalence. *)
From Stdlib Require Import List.
From LeanPort Require Import Syntax Checker DagScope DagArena
  DagMemo DagQuery DagInfer DagEntry DagAdmission DagTheoremOpaque
  ReferenceDagQuery ReferenceDagInfer ReferenceDagEntry ReferenceDagAdmission ReferenceDagTheoremOpaque.

Theorem recursive_query_refines budget checking q rec fuel env ps base arena :
  arena_ok arena ->
  DagInfer.run_memo_infer rec fuel env ps base arena budget checking q =
  ReferenceDagInfer.run_memo_infer rec fuel env ps base arena budget checking q.
Proof.
  intro Arena. rewrite DagInfer.run_memo_infer_refines by exact Arena.
  rewrite ReferenceDagInfer.run_memo_infer_refines by exact Arena.
  reflexivity.
Qed.

Theorem dag_inference_refines budget fuel env ps base rows root :
  DagEntry.dag_infer budget fuel env ps base rows root =
  ReferenceDagEntry.dag_infer budget fuel env ps base rows root.
Proof.
  rewrite DagEntry.dag_infer_refines, ReferenceDagEntry.dag_infer_refines.
  reflexivity.
Qed.

Theorem definition_admission_refines hints budget fuel env n ps rows tr br :
  DagAdmission.admit_dag_definition hints budget fuel env n ps rows tr br =
  ReferenceDagAdmission.admit_dag_definition hints budget fuel env n ps rows tr br.
Proof.
  rewrite DagAdmission.admit_dag_definition_refines,
    ReferenceDagAdmission.admit_dag_definition_refines. reflexivity.
Qed.

Theorem theorem_admission_refines budget fuel env n ps rows tr br :
  DagTheoremOpaque.admit_dag_theorem budget fuel env n ps rows tr br =
  ReferenceDagTheoremOpaque.admit_dag_theorem budget fuel env n ps rows tr br.
Proof.
  rewrite DagTheoremOpaque.admit_dag_theorem_refines,
    ReferenceDagTheoremOpaque.admit_dag_theorem_refines. reflexivity.
Qed.

Theorem opaque_admission_refines budget fuel env n ps rows tr br :
  DagTheoremOpaque.admit_dag_opaque budget fuel env n ps rows tr br =
  ReferenceDagTheoremOpaque.admit_dag_opaque budget fuel env n ps rows tr br.
Proof.
  rewrite DagTheoremOpaque.admit_dag_opaque_refines,
    ReferenceDagTheoremOpaque.admit_dag_opaque_refines. reflexivity.
Qed.

Print Assumptions recursive_query_refines.
Print Assumptions dag_inference_refines.
Print Assumptions definition_admission_refines.
Print Assumptions theorem_admission_refines.
Print Assumptions opaque_admission_refines.
