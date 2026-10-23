(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Semantics of the existing simultaneous universe instantiation operation. *)
From Stdlib Require Import List Bool Arith Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness UniverseCompleteness.
Import ListNotations.

Definition instantiated_assignment rho ps us n := level_eval rho (lookup_level ps us n).

Theorem subst_level_semantics rho ps us u :
  level_eval rho (subst_level ps us u) = level_eval (instantiated_assignment rho ps us) u.
Proof.
  induction u; simpl; try reflexivity; rewrite ?IHu, ?IHu1, ?IHu2; reflexivity.
Qed.

Theorem subst_level_preserves_inequality ps us u v :
  (forall rho, level_eval rho u <= level_eval rho v) ->
  forall rho, level_eval rho (subst_level ps us u) <= level_eval rho (subst_level ps us v).
Proof. intros H rho. rewrite !subst_level_semantics. apply H. Qed.

Theorem subst_level_preserves_equivalence ps us u v :
  (forall rho, level_eval rho u = level_eval rho v) ->
  forall rho, level_eval rho (subst_level ps us u) = level_eval rho (subst_level ps us v).
Proof. intros H rho. rewrite !subst_level_semantics. apply H. Qed.

Lemma lookup_level_meta_free ps us n :
  Forall (fun u => level_has_meta u = false) us -> level_has_meta (lookup_level ps us n) = false.
Proof.
  revert us. induction ps as [|p ps IH]; intros [|u us] H; simpl; try reflexivity.
  inversion H; subst. destruct (name_eqb p n); auto.
Qed.

Theorem subst_level_meta_free ps us u :
  level_has_meta u = false -> Forall (fun v => level_has_meta v = false) us ->
  level_has_meta (subst_level ps us u) = false.
Proof.
  induction u; simpl; intros H Hu; try reflexivity; try discriminate.
  - apply IHu; assumption.
  - apply orb_false_iff in H as [Ha Hb]. rewrite IHu1, IHu2; auto.
  - apply orb_false_iff in H as [Ha Hb]. rewrite IHu1, IHu2; auto.
  - apply lookup_level_meta_free; assumption.
Qed.

Lemma lookup_level_well_scoped ps us qs n :
  length ps = length us -> In n ps -> Forall (fun u => level_wf qs u = true) us ->
  level_wf qs (lookup_level ps us n) = true.
Proof.
  revert us. induction ps as [|p ps IH]; intros [|u us] Hlen Hn Hwf;
    simpl in Hlen, Hn |- *; try contradiction; try discriminate.
  inversion Hwf as [|? ? Hu Hus]; subst.
  destruct (name_eqb p n) eqn:Heq; [exact Hu|].
  apply IH; [lia| |exact Hus]. destruct Hn as [Heq'|Hn]; [|exact Hn].
  subst p. rewrite name_eqb_refl in Heq. discriminate.
Qed.

Theorem subst_level_well_scoped ps us qs u :
  length ps = length us -> level_wf ps u = true ->
  Forall (fun v => level_wf qs v = true) us ->
  level_wf qs (subst_level ps us u) = true.
Proof.
  intros Hlen. induction u; simpl; intros H Hu; try reflexivity; try discriminate.
  - apply IHu; assumption.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHu1, IHu2; auto.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHu1, IHu2; auto.
  - apply lookup_level_well_scoped; [exact Hlen|apply name_mem_spec; exact H|exact Hu].
Qed.

Theorem subst_level_comparison_accepts fuel next ps us u v :
  level_le fuel u v = Accept true ->
  level_has_meta u = false -> level_has_meta v = false ->
  Forall (fun w => level_has_meta w = false) us ->
  Nat.max (level_nodes (subst_level ps us u)) (level_nodes (subst_level ps us v)) <= next ->
  level_le next (subst_level ps us u) (subst_level ps us v) = Accept true.
Proof.
  intros Hle Hu Hv Hus Hfuel.
  destruct (level_comparisons_total_correct next (subst_level ps us u) (subst_level ps us v)
    (subst_level_meta_free _ _ _ Hu Hus) (subst_level_meta_free _ _ _ Hv Hus) Hfuel)
    as [[b [Hb Hiff]] _].
  assert (Hbtrue : b = true).
  { apply Hiff. apply subst_level_preserves_inequality. intros rho.
    exact (level_le_sound fuel rho u v Hle). }
  subst b. exact Hb.
Qed.

Theorem subst_level_equivalence_accepts fuel next ps us u v :
  level_equiv fuel u v = Accept true ->
  level_has_meta u = false -> level_has_meta v = false ->
  Forall (fun w => level_has_meta w = false) us ->
  Nat.max (level_nodes (subst_level ps us u)) (level_nodes (subst_level ps us v)) <= next ->
  level_equiv next (subst_level ps us u) (subst_level ps us v) = Accept true.
Proof.
  intros Heq Hu Hv Hus Hfuel.
  destruct (level_comparisons_total_correct next (subst_level ps us u) (subst_level ps us v)
    (subst_level_meta_free _ _ _ Hu Hus) (subst_level_meta_free _ _ _ Hv Hus) Hfuel)
    as [_ [b [Hb Hiff]]].
  assert (Hbtrue : b = true).
  { apply Hiff. apply subst_level_preserves_equivalence. intros rho.
    exact (level_equiv_sound fuel rho u v Heq). }
  subst b. exact Hb.
Qed.

Print Assumptions subst_level_semantics.
Print Assumptions subst_level_preserves_inequality.
Print Assumptions subst_level_preserves_equivalence.
Print Assumptions subst_level_meta_free.
Print Assumptions subst_level_well_scoped.
Print Assumptions subst_level_comparison_accepts.
Print Assumptions subst_level_equivalence_accepts.
