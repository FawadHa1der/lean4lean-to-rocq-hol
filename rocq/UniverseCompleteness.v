(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Completeness for the unchanged guarded universe comparison. *)
From Coq Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness.
Import ListNotations.

Definition sublevel_wf (s : sublevel) : Prop :=
  match s with
  | SubConst _ k => 0 < k
  | SubVar p n _ => In n p
  end.

Lemma const_atom_wf p k : Forall sublevel_wf (const_atom p k).
Proof. destruct k; simpl; constructor; [simpl; lia | constructor]. Qed.

Lemma guard_insert_member n p : In n (guard_insert n p).
Proof.
  unfold guard_insert. destruct (name_mem n p) eqn:H.
  - apply name_mem_spec. exact H.
  - simpl; auto.
Qed.

Theorem normalize_aux_wf fuel u p k ss :
  normalize_aux fuel u p k = Accept ss -> Forall sublevel_wf ss.
Proof.
  revert u p k ss. induction fuel as [|fuel IH]; intros u p k ss H;
    [discriminate|].
  destruct u as [|u|u v|u v|n|n]; simpl in H.
  - inversion H; subst. apply const_atom_wf.
  - eapply IH; eauto.
  - unfold combine_levels in H. split_normalization H. inversion H; subst.
    apply Forall_app; split; eapply IH; eauto.
  - destruct v as [|v|v w|v w|n|n]; simpl in H.
    + inversion H; subst. apply const_atom_wf.
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      apply Forall_app; split; eapply IH; eauto.
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      apply Forall_app; split; eapply IH; eauto.
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      apply Forall_app; split; eapply IH; eauto.
    + split_normalization H. inversion H; subst. apply Forall_app; split.
      * apply const_atom_wf.
      * constructor; [apply guard_insert_member | eapply IH; eauto].
    + discriminate.
  - inversion H; subst. apply Forall_app; split; [apply const_atom_wf|].
    constructor; [apply guard_insert_member | constructor].
  - discriminate.
Qed.

Theorem normalize_level_wf fuel u ss :
  normalize_level fuel u = Accept ss -> Forall sublevel_wf ss.
Proof.
  unfold normalize_level. destruct (level_has_meta u); [discriminate|].
  apply normalize_aux_wf.
Qed.

Definition supported (rho : name -> nat) (p : list name) : Prop :=
  forall n, rho n <> 0 <-> In n p.

Lemma supported_guard rho p q : supported rho p ->
  guard_holds rho q = guard_subset q p.
Proof.
  intros H. assert (He : guard_holds rho q = true <-> guard_subset q p = true).
  { unfold guard_holds, guard_subset. rewrite !forallb_forall.
    split; intros G n Hn.
    - apply name_mem_spec. apply H. specialize (G n Hn).
      apply negb_true_iff in G. apply Nat.eqb_neq in G. exact G.
    - apply negb_true_iff. apply Nat.eqb_neq. apply H.
      apply name_mem_spec. apply G. exact Hn. }
  destruct (guard_holds rho q), (guard_subset q p); intuition congruence.
Qed.

Definition unit_assignment (p : list name) (n : name) : nat :=
  if name_mem n p then 1 else 0.

Lemma unit_assignment_supported p : supported (unit_assignment p) p.
Proof.
  intros n. unfold unit_assignment. destruct (name_mem n p) eqn:H.
  - apply name_mem_spec in H. split; auto; lia.
  - split; [lia|]. intros Hin. apply name_mem_spec in Hin. congruence.
Qed.

Lemma guard_subset_refl p : guard_subset p p = true.
Proof. unfold guard_subset. apply forallb_forall. intros; apply name_mem_spec; assumption. Qed.

Lemma unit_assignment_member p n : In n p -> unit_assignment p n = 1.
Proof. intros H. apply name_mem_spec in H. unfold unit_assignment. rewrite H. reflexivity. Qed.

Lemma const_nondomination p k ys : 0 < k -> Forall sublevel_wf ys ->
  (forall y, In y ys -> sublevel_le (SubConst p k) y = false) ->
  sublevels_eval (unit_assignment p) ys < k.
Proof.
  intros Hk Hwf Hno. induction ys as [|y ys IH]; simpl; [lia|].
  inversion Hwf as [|? ? Hy Hys]; subst.
  assert (Ht : sublevels_eval (unit_assignment p) ys < k).
  { apply IH; [exact Hys|]. intros z Hz. apply Hno; simpl; auto. }
  apply Nat.max_lub_lt; [|exact Ht].
  specialize (Hno y (or_introl eq_refl)).
  destruct y as [q j|q n j]; simpl in Hno, Hy |- *;
    rewrite (supported_guard _ p q (unit_assignment_supported p)).
  - destruct (guard_subset q p); simpl in Hno |- *; [apply Nat.leb_gt in Hno|]; lia.
  - destruct (guard_subset q p) eqn:Hsub; simpl in Hno |- *; [|lia].
    assert (Hm : name_mem n q = true) by (apply name_mem_spec; exact Hy).
    rewrite Hm in Hno. simpl in Hno. apply Nat.leb_gt in Hno.
    assert (Hnp : In n p).
    { unfold guard_subset in Hsub. apply forallb_forall with (x:=n) in Hsub;
        [apply name_mem_spec; exact Hsub|exact Hy]. }
    rewrite (unit_assignment_member p n Hnp). lia.
Qed.

Definition sublevel_offset (s : sublevel) : nat :=
  match s with SubConst _ k | SubVar _ _ k => k end.

Fixpoint offset_bound (ys : list sublevel) : nat :=
  match ys with [] => 0 | y :: ys => Nat.max (S (sublevel_offset y)) (offset_bound ys) end.

Lemma offset_bound_member y ys : In y ys -> sublevel_offset y < offset_bound ys.
Proof.
  induction ys as [|z ys IH]; [simpl; tauto|]. intros [H|H].
  - subst z. change (S (sublevel_offset y) <= Nat.max (S (sublevel_offset y)) (offset_bound ys)).
    apply Nat.le_max_l.
  - change (S (sublevel_offset y) <= Nat.max (S (sublevel_offset z)) (offset_bound ys)).
    eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Definition spike_assignment p n big m :=
  if name_eqb m n then big else unit_assignment p m.

Lemma spike_assignment_same p n big : spike_assignment p n big n = big.
Proof. unfold spike_assignment. rewrite name_eqb_refl. reflexivity. Qed.

Lemma spike_assignment_supported p n big : In n p -> 0 < big ->
  supported (spike_assignment p n big) p.
Proof.
  intros Hn Hb m. unfold spike_assignment. destruct (name_eqb m n) eqn:Heq.
  - apply name_eqb_eq in Heq. subst. split; auto; lia.
  - apply unit_assignment_supported.
Qed.

Lemma var_nondomination p n k ys : In n p ->
  (forall y, In y ys -> sublevel_le (SubVar p n k) y = false) ->
  sublevels_eval (spike_assignment p n (S (offset_bound ys))) ys < S (offset_bound ys) + k.
Proof.
  intros Hn Hno. set (big := S (offset_bound ys)).
  assert (Hb : 0 < big) by (unfold big; lia).
  assert (Hsupport := spike_assignment_supported p n big Hn Hb).
  assert (Hbound : forall y, In y ys -> sublevel_offset y < big).
  { intros y Hy. pose proof (offset_bound_member y ys Hy). unfold big. lia. }
  assert (Hatom : forall y, In y ys -> sublevel_eval (spike_assignment p n big) y < big + k).
  { intros y Hy. specialize (Hno y Hy). specialize (Hbound y Hy).
    destruct y as [q j|q m j]; simpl in Hno, Hbound |- *;
      rewrite (supported_guard _ p q Hsupport).
    - destruct (guard_subset q p); lia.
    - destruct (guard_subset q p) eqn:Hsub; simpl in Hno |- *; [|lia].
      destruct (name_eqb n m) eqn:Hnm; simpl in Hno.
      + apply name_eqb_eq in Hnm. subst m. apply Nat.leb_gt in Hno.
        rewrite spike_assignment_same. lia.
      + unfold spike_assignment.
        assert (Hmn : name_eqb m n = false).
        { destruct (name_eqb m n) eqn:H; [|reflexivity].
          apply name_eqb_eq in H. subst. rewrite name_eqb_refl in Hnm. discriminate. }
        rewrite Hmn. unfold unit_assignment. destruct (name_mem m p);
          pose proof (offset_bound_member (SubVar q m j) ys Hy) as Hstrict;
          simpl in Hstrict; unfold big in *; lia. }
  (* Keep the valuation and its chosen spike fixed across the list. *)
  assert (Hlist : forall zs, (forall z, In z zs -> sublevel_eval (spike_assignment p n big) z < big + k) ->
    sublevels_eval (spike_assignment p n big) zs < big + k).
  { induction zs as [|z zs IH]; simpl; intros Hz; [lia|].
    apply Nat.max_lub_lt; [apply Hz; simpl; auto|apply IH; intros; apply Hz; simpl; auto]. }
  apply Hlist. exact Hatom.
Qed.

Definition atom_countervaluation (a : sublevel) (ys : list sublevel) : name -> nat :=
  match a with
  | SubConst p _ => unit_assignment p
  | SubVar p n _ => spike_assignment p n (S (offset_bound ys))
  end.

Theorem atom_countervaluation_correct a ys : sublevel_wf a -> Forall sublevel_wf ys ->
  (forall y, In y ys -> sublevel_le a y = false) ->
  sublevels_eval (atom_countervaluation a ys) ys < sublevel_eval (atom_countervaluation a ys) a.
Proof.
  intros Ha Hys Hno. destruct a as [p k|p n k]; simpl in Ha |- *.
  - rewrite (supported_guard _ p p (unit_assignment_supported p)), guard_subset_refl.
    apply const_nondomination; assumption.
  - rewrite (supported_guard _ p p (spike_assignment_supported p n (S (offset_bound ys)) Ha ltac:(lia))),
      guard_subset_refl, spike_assignment_same.
    apply var_nondomination; assumption.
Qed.

Lemma forallb_false_member {A : Type} (f : A -> bool) xs :
  forallb f xs = false -> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; simpl; [discriminate|].
  destruct (f x) eqn:Hx; simpl; intros H.
  - destruct (IH H) as [y [Hy Hf]]. exists y. split; [simpl; auto|exact Hf].
  - exists x. split; [simpl; auto|exact Hx].
Qed.

Lemma existsb_false_members {A : Type} (f : A -> bool) ys :
  existsb f ys = false -> forall y, In y ys -> f y = false.
Proof.
  intros H y Hy. destruct (f y) eqn:Hyf; [|reflexivity].
  assert (Htrue : existsb f ys = true).
  { apply existsb_exists. exists y. auto. }
  congruence.
Qed.

Theorem sublevels_le_false_witness xs ys :
  Forall sublevel_wf xs -> Forall sublevel_wf ys -> sublevels_le xs ys = false ->
  exists rho, sublevels_eval rho ys < sublevels_eval rho xs.
Proof.
  intros Hxs Hys Hno. unfold sublevels_le in Hno.
  apply forallb_false_member in Hno as [x [Hx Hnone]].
  pose proof (existsb_false_members _ _ Hnone) as Hbad.
  apply Forall_forall with (x:=x) in Hxs; [|exact Hx].
  pose proof (atom_countervaluation_correct x ys Hxs Hys Hbad) as Hlt.
  exists (atom_countervaluation x ys).
  pose proof (sublevel_member_bound (atom_countervaluation x ys) x xs Hx). lia.
Qed.

Theorem sublevels_le_complete xs ys :
  Forall sublevel_wf xs -> Forall sublevel_wf ys ->
  (forall rho, sublevels_eval rho xs <= sublevels_eval rho ys) -> sublevels_le xs ys = true.
Proof.
  intros Hxs Hys Hle. destruct (sublevels_le xs ys) eqn:H; [reflexivity|].
  destruct (sublevels_le_false_witness xs ys Hxs Hys H) as [rho Hbad].
  specialize (Hle rho). lia.
Qed.

Theorem level_le_false_witness fuel u v : level_le fuel u v = Accept false ->
  exists rho, level_eval rho v < level_eval rho u.
Proof.
  unfold level_le. destruct (normalize_level fuel u) as [xs|err|why] eqn:Hu; simpl; try discriminate.
  destruct (normalize_level fuel v) as [ys|err|why] eqn:Hv; simpl; try discriminate.
  intros H. injection H as H.
  destruct (sublevels_le_false_witness xs ys
    (normalize_level_wf _ _ _ Hu) (normalize_level_wf _ _ _ Hv) H) as [rho Hbad].
  exists rho. rewrite (normalize_level_sound _ _ _ _ Hu),
    (normalize_level_sound _ _ _ _ Hv) in Hbad. exact Hbad.
Qed.

Theorem level_le_decision_complete fuel u v b : level_le fuel u v = Accept b ->
  (b = true <-> forall rho, level_eval rho u <= level_eval rho v).
Proof.
  intros H. split.
  - intros Hb rho. subst b. apply (level_le_sound fuel rho _ _ H).
  - intros Hle. destruct b; [reflexivity|].
    destruct (level_le_false_witness _ _ _ H) as [rho Hbad]. specialize (Hle rho). lia.
Qed.

Theorem level_equiv_false_witness fuel u v : level_equiv fuel u v = Accept false ->
  exists rho, level_eval rho u <> level_eval rho v.
Proof.
  unfold level_equiv. destruct (normalize_level fuel u) as [xs|err|why] eqn:Hu; simpl; try discriminate.
  destruct (normalize_level fuel v) as [ys|err|why] eqn:Hv; simpl; try discriminate.
  intros H. injection H as H. apply andb_false_iff in H as [H|H].
  - destruct (sublevels_le_false_witness xs ys
      (normalize_level_wf _ _ _ Hu) (normalize_level_wf _ _ _ Hv) H) as [rho Hbad].
    exists rho. rewrite (normalize_level_sound _ _ _ _ Hu),
      (normalize_level_sound _ _ _ _ Hv) in Hbad. lia.
  - destruct (sublevels_le_false_witness ys xs
      (normalize_level_wf _ _ _ Hv) (normalize_level_wf _ _ _ Hu) H) as [rho Hbad].
    exists rho. rewrite (normalize_level_sound _ _ _ _ Hu),
      (normalize_level_sound _ _ _ _ Hv) in Hbad. lia.
Qed.

Theorem level_equiv_decision_complete fuel u v b : level_equiv fuel u v = Accept b ->
  (b = true <-> forall rho, level_eval rho u = level_eval rho v).
Proof.
  intros H. split.
  - intros Hb rho. subst b. apply (level_equiv_sound fuel rho _ _ H).
  - intros Heq. destruct b; [reflexivity|].
    destruct (level_equiv_false_witness _ _ _ H) as [rho Hbad]. specialize (Heq rho). contradiction.
Qed.

Theorem levels_equiv_false_witness fuel us vs : levels_equiv fuel us vs = Accept false ->
  exists rho, map (level_eval rho) us <> map (level_eval rho) vs.
Proof.
  revert vs. induction us as [|u us IH]; intros [|v vs]; simpl; try discriminate.
  - intros _. exists (fun _ => 0). discriminate.
  - intros _. exists (fun _ => 0). discriminate.
  - destruct (level_equiv fuel u v) as [b|err|why] eqn:Huv; simpl; try discriminate.
    destruct b.
    + intros H. destruct (IH _ H) as [rho Hbad]. exists rho. intros Hlist.
      injection Hlist as Hhead Htail. contradiction.
    + intros _. destruct (level_equiv_false_witness _ _ _ Huv) as [rho Hbad].
      exists rho. intros Hlist. injection Hlist as Hhead Htail. contradiction.
Qed.

Theorem levels_equiv_decision_complete fuel us vs b : levels_equiv fuel us vs = Accept b ->
  (b = true <-> forall rho, map (level_eval rho) us = map (level_eval rho) vs).
Proof.
  intros H. split.
  - intros Hb rho. subst b. apply (levels_equiv_sound fuel rho _ _ H).
  - intros Heq. destruct b; [reflexivity|].
    destruct (levels_equiv_false_witness _ _ _ H) as [rho Hbad]. specialize (Heq rho). contradiction.
Qed.

Theorem level_comparisons_total_correct fuel u v :
  level_has_meta u = false -> level_has_meta v = false ->
  Nat.max (level_nodes u) (level_nodes v) <= fuel ->
  (exists b, level_le fuel u v = Accept b /\
    (b = true <-> forall rho, level_eval rho u <= level_eval rho v)) /\
  (exists b, level_equiv fuel u v = Accept b /\
    (b = true <-> forall rho, level_eval rho u = level_eval rho v)).
Proof.
  intros Hu Hv Hfuel.
  destruct (level_comparisons_sufficient_fuel fuel u v Hu Hv Hfuel) as [[b Hb] [c Hc]].
  split.
  - exists b. split; [exact Hb|exact (level_le_decision_complete fuel u v b Hb)].
  - exists c. split; [exact Hc|exact (level_equiv_decision_complete fuel u v c Hc)].
Qed.

Print Assumptions normalize_aux_wf.
Print Assumptions normalize_level_wf.
Print Assumptions atom_countervaluation_correct.
Print Assumptions sublevels_le_false_witness.
Print Assumptions sublevels_le_complete.
Print Assumptions level_le_false_witness.
Print Assumptions level_le_decision_complete.
Print Assumptions level_equiv_false_witness.
Print Assumptions level_equiv_decision_complete.
Print Assumptions levels_equiv_false_witness.
Print Assumptions levels_equiv_decision_complete.
Print Assumptions level_comparisons_total_correct.
