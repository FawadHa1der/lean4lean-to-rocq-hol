(* SPDX-License-Identifier: Apache-2.0
   Mode-scoped scheduling and NEW complete-result refinement, not old/new parity. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax EagerPolicy Checker LookupCore LookupRefinement
  IndexedChecker DagScope DagArena DagQuery DagInfer ReferenceDagInfer
  IndexedDagInfer PreparedDagLookup GuardOrderRefinement.
Import ListNotations.

Lemma inference_only_keeps_mode rec : method_mode (inference_only rec) = method_mode rec.
Proof. reflexivity. Qed.
Lemma inference_only_keeps_override rec g t s :
  eager_defeq_method (inference_only rec) g t s = eager_defeq_method rec g t s.
Proof. reflexivity. Qed.
Lemma checker_captures_mode mode fuel env ps :
  method_mode (Checker.checker_mode mode fuel env ps) = mode.
Proof. destruct fuel; reflexivity. Qed.
Lemma eager_override_same_depth mode fuel env ps g t s :
  eager_defeq_method (Checker.checker_mode mode fuel env ps) g t s =
    defeq_method (Checker.checker_mode EagerReduction fuel env ps) g t s.
Proof. destruct fuel; reflexivity. Qed.
Lemma eager_override_zero mode env ps g t s :
  eager_defeq_method (Checker.checker_mode mode 0 env ps) g t s = Decline OutOfFuel.
Proof. reflexivity. Qed.
Lemma eager_override_uses_predecessor mode fuel env ps g t s :
  eager_defeq_method (Checker.checker_mode mode (S fuel) env ps) g t s =
    defeq_step (Checker.checker_mode EagerReduction fuel env ps) fuel env ps g t s.
Proof. reflexivity. Qed.

Lemma marked_application_order rec g a domain arg_type :
  is_eager_reduce_argument a = true ->
  application_type_defeq rec g a domain arg_type = eager_defeq_method rec g domain arg_type.
Proof. intro H. unfold application_type_defeq. rewrite H. reflexivity. Qed.
Lemma unmarked_application_order rec g a domain arg_type :
  is_eager_reduce_argument a = false ->
  application_type_defeq rec g a domain arg_type = defeq_method rec g domain arg_type.
Proof. intro H. unfold application_type_defeq. rewrite H. reflexivity. Qed.

Lemma normal_one_open_skips_both t s :
  has_external_local t = true \/ has_external_local s = true ->
  nat_probe_allowed NormalReduction t s = false.
Proof.
  unfold nat_probe_allowed. intros [H|H]; rewrite H; simpl;
    [reflexivity|apply Bool.andb_false_r].
Qed.
Lemma normal_true_open_skips rec env g t s :
  method_mode rec = NormalReduction -> has_external_local t = true ->
  core_true_shortcut rec env g t s = Accept false.
Proof.
  intros Hm Ht. rewrite guard_order_true_shortcut_exact.
  unfold stage3_true_shortcut, true_probe_allowed. rewrite Hm, Ht.
  reflexivity.
Qed.
Lemma true_shortcut_reject_priority rec fuel env ps g t s error :
  core_quick (inference_only rec) fuel g t s = Accept None ->
  core_true_shortcut (inference_only rec) env g t s = Reject error ->
  defeq_step rec fuel env ps g t s = Reject error.
Proof. intros Hq Hs. unfold defeq_step. rewrite Hq. cbn [bind]. rewrite Hs. reflexivity. Qed.
Lemma true_shortcut_decline_priority rec fuel env ps g t s reason :
  core_quick (inference_only rec) fuel g t s = Accept None ->
  core_true_shortcut (inference_only rec) env g t s = Decline reason ->
  defeq_step rec fuel env ps g t s = Decline reason.
Proof. intros Hq Hs. unfold defeq_step. rewrite Hq. cbn [bind]. rewrite Hs. reflexivity. Qed.
Lemma true_shortcut_false_falls_through rec fuel env ps g t s answer :
  core_quick (inference_only rec) fuel g t s = Accept None ->
  core_true_shortcut (inference_only rec) env g t s = Accept false ->
  core_proof_irrel (inference_only rec) fuel g t s = Accept (Some answer) ->
  defeq_step rec fuel env ps g t s = Accept answer.
Proof.
  intros Hq Hs Hi. unfold defeq_step. rewrite Hq. cbn [bind].
  rewrite Hs. cbn [bind]. rewrite Hi. reflexivity.
Qed.
Lemma nat_guard_skips_to_congruence rounds rec fuel env ps g t s error :
  core_quick rec fuel g t s = Accept None ->
  core_offset rec env g t s = Accept None ->
  nat_probe_allowed (method_mode rec) t s = false ->
  core_delta_congruent rec fuel env g t s = Reject error ->
  core_lazy_delta (S rounds) rec fuel env ps g t s = Reject error.
Proof.
  intros Hq Ho Hg Hc. rewrite guard_order_lazy_delta_exact.
  cbn [stage3_lazy_delta]. rewrite Hq. cbn [bind].
  rewrite Ho. cbn [bind]. rewrite Hg. cbn [bind]. rewrite Hc. reflexivity.
Qed.

Lemma step_eval_methods_equivalent a b fuel env ps base arena checking q :
  methods_equivalent a b ->
  step_eval a fuel env ps base arena checking q =
    step_eval b fuel env ps base arena checking q.
Proof.
  intro H. destruct q as [id path]. unfold step_eval.
  apply bind_pointwise; [reflexivity|intro g].
  apply bind_pointwise; [reflexivity|intro e].
  apply original_infer_step_methods. exact H.
Qed.

Theorem prepared_mode_dag_complete_result mode lookup method_fuel step_fuel env ps
    base arena budget checking q :
  (forall n, lookup n = find_decl n env) -> arena_ok arena ->
  IndexedDagInfer.run_memo_infer lookup
    (checker_with_lookup_mode mode method_fuel env lookup ps)
    step_fuel env ps base arena budget checking q =
  step_eval (Checker.checker_mode mode method_fuel env ps)
    step_fuel env ps base arena checking q.
Proof.
  intros Lookup Arena. rewrite IndexedDagInfer.run_memo_infer_refines by assumption.
  apply step_eval_methods_equivalent, checker_with_lookup_mode_refines. exact Lookup.
Qed.

Theorem ordinary_mode_dag_complete_result mode method_fuel step_fuel env ps
    base arena budget checking q : arena_ok arena ->
  DagInfer.run_memo_infer (Checker.checker_mode mode method_fuel env ps)
    step_fuel env ps base arena budget checking q =
  step_eval (Checker.checker_mode mode method_fuel env ps)
    step_fuel env ps base arena checking q.
Proof. apply DagInfer.run_memo_infer_refines. Qed.

Print Assumptions eager_override_same_depth.
Print Assumptions eager_override_zero.
Print Assumptions eager_override_uses_predecessor.
Print Assumptions nat_guard_skips_to_congruence.
Print Assumptions true_shortcut_false_falls_through.
Print Assumptions prepared_mode_dag_complete_result.
Print Assumptions ordinary_mode_dag_complete_result.
Print Assumptions checker_mode_lookup_refines.
