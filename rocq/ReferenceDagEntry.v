(* SPDX-License-Identifier: Apache-2.0
   Private syntax-only entry boundary. Callers supply neither caches nor
   summaries. Successful decoding retains the existing checker semantics. *)
From Stdlib Require Import List PArith.BinPos.
From LeanPort Require Import Syntax Checker DagScope DagMemoReference DagArena ReferenceDagQuery ReferenceDagInfer.
Import ListNotations.
Set Implicit Arguments.

Definition dag_reference (fuel : nat) env ps base rows root : result expr :=
  arena <- arena_build empty_arena rows ;;
  entry <- scope_ref (arena_scope arena) root ;;
  infer fuel env ps base (scope_expr entry).

Definition dag_infer (budget fuel : nat) env ps base rows root : result expr :=
  arena <- arena_build empty_arena rows ;;
  entry <- scope_ref (arena_scope arena) root ;;
  match fuel with
  | 0 => Decline OutOfFuel
  | S n => run_memo_infer (checker n env ps) n env ps base arena
      budget true (root,[])
  end.

Theorem dag_infer_refines budget fuel env ps base rows root :
  dag_infer budget fuel env ps base rows root =
  dag_reference fuel env ps base rows root.
Proof.
  unfold dag_infer, dag_reference.
  destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) root) eqn:Root; cbn [bind]; try reflexivity.
  destruct fuel as [|n]; [reflexivity|].
  rewrite run_memo_infer_refines.
  - unfold step_eval. cbn [path_from bind]. rewrite Root. reflexivity.
  - eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Theorem dag_infer_decoded budget fuel env ps base rows root arena entry :
  arena_build empty_arena rows = Accept arena ->
  scope_ref (arena_scope arena) root = Accept entry ->
  dag_infer budget fuel env ps base rows root =
    infer fuel env ps base (scope_expr entry).
Proof.
  intros Build Root. rewrite dag_infer_refines. unfold dag_reference.
  rewrite Build. cbn [bind]. rewrite Root. reflexivity.
Qed.

Print Assumptions dag_infer_refines.
Print Assumptions dag_infer_decoded.
