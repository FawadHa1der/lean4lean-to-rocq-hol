(* SPDX-License-Identifier: Apache-2.0
   Complete-result refinement against the NEW ordinary Checker semantics.
   ReferenceDag modules preserve the old linear-cache algorithms but import this
   tree's repaired Checker; they are NOT the old frozen executable semantics. *)
From Stdlib Require Import List.
From LeanPort Require Import Syntax Checker Declarations DagScope DagArena
  DagAdmission DagTheoremOpaque IndexedDagAdmission IndexedDagInfer
  LookupIntegration DagQuery ReferenceDagInfer ReferenceDagAdmission
  ReferenceDagTheoremOpaque DepthAdmissionRefinement.

Definition linear_cache_new_admit kind budget fuel env n ps rows tr br :=
  match kind with
  | DagDefinition hints => ReferenceDagAdmission.admit_dag_definition hints budget fuel env n ps rows tr br
  | DagTheorem => ReferenceDagTheoremOpaque.admit_dag_theorem budget fuel env n ps rows tr br
  | DagOpaque => ReferenceDagTheoremOpaque.admit_dag_opaque budget fuel env n ps rows tr br
  end.

Definition new_ordinary_decode_admit kind fuel env n ps rows tr br :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) tr ;;
  body <- scope_ref (arena_scope arena) br ;;
  Declarations.admit fuel env
    (match kind with
     | DagDefinition hints => InputDefinition hints n ps (scope_expr ty) (scope_expr body) InputSafe
     | DagTheorem => InputTheorem n ps (scope_expr ty) (scope_expr body)
     | DagOpaque => InputOpaque n ps (scope_expr ty) (scope_expr body) false
     end).

Lemma depth_to_linear_cache_new kind budget fuel env n ps rows tr br :
  linear_env_admit kind budget fuel env n ps rows tr br =
  linear_cache_new_admit kind budget fuel env n ps rows tr br.
Proof.
  destruct kind; unfold linear_env_admit, linear_cache_new_admit;
    auto using definition_admission_refines, theorem_admission_refines, opaque_admission_refines.
Qed.

Theorem combined_indexed_refines_linear_cache_new hash kind budget fuel env n ps rows tr br :
  indexed_admit hash kind budget fuel env n ps rows tr br =
  linear_cache_new_admit kind budget fuel env n ps rows tr br.
Proof. rewrite indexed_admit_refines. apply depth_to_linear_cache_new. Qed.

Theorem combined_guarded_refines_linear_cache_new kind budget fuel env n ps rows tr br :
  indexed_dag_admit kind budget fuel env n ps rows tr br =
  linear_cache_new_admit kind budget fuel env n ps rows tr br.
Proof. rewrite indexed_dag_admit_refines. apply depth_to_linear_cache_new. Qed.

Lemma linear_cache_new_refines_new_ordinary kind budget fuel env n ps rows tr br :
  linear_cache_new_admit kind budget fuel env n ps rows tr br =
  new_ordinary_decode_admit kind fuel env n ps rows tr br.
Proof.
  destruct kind; unfold linear_cache_new_admit;
    rewrite ?ReferenceDagAdmission.admit_dag_definition_refines,
      ?ReferenceDagTheoremOpaque.admit_dag_theorem_refines,
      ?ReferenceDagTheoremOpaque.admit_dag_opaque_refines; reflexivity.
Qed.

Theorem combined_guarded_refines_new_ordinary kind budget fuel env n ps rows tr br :
  indexed_dag_admit kind budget fuel env n ps rows tr br =
  new_ordinary_decode_admit kind fuel env n ps rows tr br.
Proof. rewrite combined_guarded_refines_linear_cache_new. apply linear_cache_new_refines_new_ordinary. Qed.

Theorem combined_indexed_refines_new_ordinary hash kind budget fuel env n ps rows tr br :
  indexed_admit hash kind budget fuel env n ps rows tr br =
  new_ordinary_decode_admit kind fuel env n ps rows tr br.
Proof. rewrite combined_indexed_refines_linear_cache_new. apply linear_cache_new_refines_new_ordinary. Qed.

Theorem combined_recursive_refines_linear_cache_new lookup rec fuel env ps base arena budget checking q :
  (forall n, lookup n = find_decl n env) -> arena_ok arena ->
  IndexedDagInfer.run_memo_infer lookup rec fuel env ps base arena budget checking q =
  ReferenceDagInfer.run_memo_infer rec fuel env ps base arena budget checking q.
Proof.
  intros Lookup Arena.
  rewrite IndexedDagInfer.run_memo_infer_refines by assumption.
  rewrite ReferenceDagInfer.run_memo_infer_refines by exact Arena. reflexivity.
Qed.

Print Assumptions combined_indexed_refines_linear_cache_new.
Print Assumptions combined_guarded_refines_linear_cache_new.
Print Assumptions combined_guarded_refines_new_ordinary.
Print Assumptions combined_indexed_refines_new_ordinary.
Print Assumptions combined_recursive_refines_linear_cache_new.
