(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Semantic soundness for the existing, unchanged universe normalizer. *)
From Coq Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes.
Import ListNotations.

Definition imax_nat (a b : nat) : nat :=
  match b with 0 => 0 | S n => Nat.max a (S n) end.

Lemma imax_max_right a b c :
  imax_nat a (Nat.max b c) = Nat.max (imax_nat a b) (imax_nat a c).
Proof.
  destruct b, c; unfold imax_nat; simpl; lia.
Qed.

Lemma imax_imax_right a b c :
  imax_nat a (imax_nat b c) = Nat.max (imax_nat a c) (imax_nat b c).
Proof.
  destruct c, b; unfold imax_nat; simpl; lia.
Qed.

Lemma sublevels_eval_app rho xs ys :
  sublevels_eval rho (xs ++ ys) =
  Nat.max (sublevels_eval rho xs) (sublevels_eval rho ys).
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH, Nat.max_assoc. reflexivity.
Qed.

Lemma const_atom_eval rho path k :
  sublevels_eval rho (const_atom path k) =
  if guard_holds rho path then k else 0.
Proof.
  destruct k; simpl; destruct (guard_holds rho path); simpl; lia.
Qed.

Lemma guard_insert_eval rho n path :
  guard_holds rho (guard_insert n path) =
  guard_holds rho path && negb (Nat.eqb (rho n) 0).
Proof.
  unfold guard_insert. destruct (name_mem n path) eqn:Hmem.
  - destruct (guard_holds rho path) eqn:Hguard; simpl; [|reflexivity].
    pose proof (guard_member_positive rho path n Hguard Hmem).
    symmetry. apply Bool.negb_true_iff. apply Nat.eqb_neq. lia.
  - unfold guard_holds. simpl. apply andb_comm.
Qed.

Ltac split_normalization H :=
  repeat match type of H with
  | context[normalize_aux ?f ?u ?p ?k] =>
      let E := fresh "Hnorm" in
      destruct (normalize_aux f u p k) eqn:E; simpl in H; try discriminate
  end.

Theorem normalize_aux_sound fuel rho u path k ss :
  normalize_aux fuel u path k = Accept ss ->
  sublevels_eval rho ss =
  if guard_holds rho path then level_eval rho u + k else 0.
Proof.
  revert u path k ss. induction fuel as [|fuel IH]; intros u path k ss H;
    [discriminate|].
  destruct u as [|u|u v|u v|n|n].
  - simpl in H. inversion H; subst. rewrite const_atom_eval. reflexivity.
  - simpl in H. rewrite (IH _ _ _ _ H). simpl. destruct (guard_holds rho path); lia.
  - simpl in H. unfold combine_levels in H. split_normalization H.
    inversion H; subst. rewrite sublevels_eval_app.
    rewrite (IH _ _ _ _ Hnorm), (IH _ _ _ _ Hnorm0).
    simpl. destruct (guard_holds rho path); [apply Nat.add_max_distr_r|reflexivity].
  - destruct v as [|v|v w|v w|n|n]; simpl in H.
    + inversion H; subst. rewrite const_atom_eval. reflexivity.
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      rewrite sublevels_eval_app, (IH _ _ _ _ Hnorm), (IH _ _ _ _ Hnorm0).
      simpl. destruct (guard_holds rho path); [|reflexivity].
      lia.
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      rewrite sublevels_eval_app, (IH _ _ _ _ Hnorm), (IH _ _ _ _ Hnorm0).
      change (Nat.max
        (if guard_holds rho path then imax_nat (level_eval rho u) (level_eval rho v) + k else 0)
        (if guard_holds rho path then imax_nat (level_eval rho u) (level_eval rho w) + k else 0) =
        if guard_holds rho path then imax_nat (level_eval rho u)
          (Nat.max (level_eval rho v) (level_eval rho w)) + k else 0).
      rewrite imax_max_right. destruct (guard_holds rho path);
        [apply Nat.add_max_distr_r|reflexivity].
    + unfold combine_levels in H. split_normalization H. inversion H; subst.
      rewrite sublevels_eval_app, (IH _ _ _ _ Hnorm), (IH _ _ _ _ Hnorm0).
      change (Nat.max
        (if guard_holds rho path then imax_nat (level_eval rho u) (level_eval rho w) + k else 0)
        (if guard_holds rho path then imax_nat (level_eval rho v) (level_eval rho w) + k else 0) =
        if guard_holds rho path then imax_nat (level_eval rho u)
          (imax_nat (level_eval rho v) (level_eval rho w)) + k else 0).
      rewrite imax_imax_right. destruct (guard_holds rho path);
        [apply Nat.add_max_distr_r|reflexivity].
    + split_normalization H. inversion H; subst. rewrite sublevels_eval_app,
        const_atom_eval. simpl. rewrite (IH _ _ _ _ Hnorm), guard_insert_eval.
      destruct (guard_holds rho path); simpl; [|reflexivity].
      destruct (rho n) as [|r]; simpl; [lia|].
      change (Nat.max k (Nat.max (S r + k) (level_eval rho u + k)) =
        Nat.max (level_eval rho u) (S r) + k).
      lia.
    + discriminate.
  - simpl in H. inversion H; subst. rewrite sublevels_eval_app, const_atom_eval.
    simpl. rewrite guard_insert_eval. destruct (guard_holds rho path); simpl; [|reflexivity].
    destruct (rho n); simpl; lia.
  - discriminate.
Qed.

Theorem normalize_level_sound fuel rho u ss :
  normalize_level fuel u = Accept ss ->
  sublevels_eval rho ss = level_eval rho u.
Proof.
  unfold normalize_level. destruct (level_has_meta u); [discriminate|].
  intros H. pose proof (normalize_aux_sound fuel rho u [] 0 ss H).
  simpl in H0. lia.
Qed.

Theorem level_le_sound fuel rho u v :
  level_le fuel u v = Accept true -> level_eval rho u <= level_eval rho v.
Proof.
  unfold level_le. destruct (normalize_level fuel u) eqn:Hu; simpl; try discriminate.
  destruct (normalize_level fuel v) eqn:Hv; simpl; try discriminate.
  intros H. injection H as H. apply (sublevels_le_sound rho) in H.
  rewrite (normalize_level_sound _ _ _ _ Hu),
    (normalize_level_sound _ _ _ _ Hv) in H. exact H.
Qed.

Theorem level_equiv_sound fuel rho u v :
  level_equiv fuel u v = Accept true -> level_eval rho u = level_eval rho v.
Proof.
  unfold level_equiv. destruct (normalize_level fuel u) eqn:Hu; simpl; try discriminate.
  destruct (normalize_level fuel v) eqn:Hv; simpl; try discriminate.
  intros H. injection H as H. apply andb_true_iff in H as [Huv Hvu].
  apply (sublevels_le_sound rho) in Huv. apply (sublevels_le_sound rho) in Hvu.
  rewrite (normalize_level_sound _ _ _ _ Hu),
    (normalize_level_sound _ _ _ _ Hv) in Huv, Hvu. lia.
Qed.

Theorem levels_equiv_sound fuel rho us vs :
  levels_equiv fuel us vs = Accept true ->
  map (level_eval rho) us = map (level_eval rho) vs.
Proof.
  revert vs. induction us as [|u us IH]; intros [|v vs]; simpl; try discriminate.
  - reflexivity.
  - destruct (level_equiv fuel u v) as [b|err|reason] eqn:Huv; simpl; try discriminate.
    destruct b; [|discriminate]. intros H. f_equal.
    + apply (level_equiv_sound fuel rho _ _ Huv).
    + apply IH. exact H.
Qed.

Fixpoint level_nodes (u : level) : nat :=
  match u with
  | LZero | LParam _ | LMVar _ => 1
  | LSucc v => S (level_nodes v)
  | LMax a b | LIMax a b => S (level_nodes a + level_nodes b)
  end.

Theorem normalize_aux_sufficient_fuel fuel u path k :
  level_has_meta u = false -> level_nodes u <= fuel ->
  exists ss, normalize_aux fuel u path k = Accept ss.
Proof.
  revert u path k. induction fuel as [|fuel IH]; intros u path k Hmeta Hsize.
  - destruct u; simpl in Hsize; lia.
  - destruct u as [|u|u v|u v|n|n]; simpl in Hmeta, Hsize.
    + exists (const_atom path k). reflexivity.
    + apply IH; [exact Hmeta|lia].
    + apply orb_false_iff in Hmeta as [Hu Hv].
      destruct (IH u path k Hu ltac:(lia)) as [xs Hx].
      destruct (IH v path k Hv ltac:(lia)) as [ys Hy].
      simpl. rewrite Hx, Hy. exists (xs ++ ys). reflexivity.
    + apply orb_false_iff in Hmeta as [Hu Hv].
      destruct v as [|v|v w|v w|n|n]; simpl in Hv, Hsize.
      * exists (const_atom path k). reflexivity.
      * destruct (IH u path k Hu ltac:(lia)) as [xs Hx].
        destruct (IH v path (S k) Hv ltac:(lia)) as [ys Hy].
        simpl. rewrite Hx, Hy. exists (xs ++ ys). reflexivity.
      * apply orb_false_iff in Hv as [Hv Hw].
        assert (Huv : level_has_meta (LIMax u v) = false) by
          (simpl; rewrite Hu, Hv; reflexivity).
        assert (Huw : level_has_meta (LIMax u w) = false) by
          (simpl; rewrite Hu, Hw; reflexivity).
        destruct (IH (LIMax u v) path k Huv ltac:(simpl; lia)) as [xs Hx].
        destruct (IH (LIMax u w) path k Huw ltac:(simpl; lia)) as [ys Hy].
        simpl. rewrite Hx, Hy. exists (xs ++ ys). reflexivity.
      * apply orb_false_iff in Hv as [Hv Hw].
        assert (Huw : level_has_meta (LIMax u w) = false) by
          (simpl; rewrite Hu, Hw; reflexivity).
        assert (Hvw : level_has_meta (LIMax v w) = false) by
          (simpl; rewrite Hv, Hw; reflexivity).
        destruct (IH (LIMax u w) path k Huw ltac:(simpl; lia)) as [xs Hx].
        destruct (IH (LIMax v w) path k Hvw ltac:(simpl; lia)) as [ys Hy].
        simpl. rewrite Hx, Hy. exists (xs ++ ys). reflexivity.
      * destruct (IH u (guard_insert n path) k Hu ltac:(lia)) as [xs Hx].
        simpl. rewrite Hx. eexists. reflexivity.
      * discriminate.
    + eexists. reflexivity.
    + discriminate.
Qed.

Theorem normalize_level_sufficient_fuel fuel u :
  level_has_meta u = false -> level_nodes u <= fuel ->
  exists ss, normalize_level fuel u = Accept ss.
Proof.
  intros Hmeta Hsize. unfold normalize_level. rewrite Hmeta.
  apply normalize_aux_sufficient_fuel; assumption.
Qed.

Theorem level_comparisons_sufficient_fuel fuel u v :
  level_has_meta u = false -> level_has_meta v = false ->
  Nat.max (level_nodes u) (level_nodes v) <= fuel ->
  (exists b, level_le fuel u v = Accept b) /\
  (exists b, level_equiv fuel u v = Accept b).
Proof.
  intros Hu Hv Hfuel.
  destruct (normalize_level_sufficient_fuel fuel u Hu ltac:(lia)) as [xs Hx].
  destruct (normalize_level_sufficient_fuel fuel v Hv ltac:(lia)) as [ys Hy].
  unfold level_le, level_equiv. rewrite Hx, Hy. simpl. split; eexists; reflexivity.
Qed.

Print Assumptions normalize_aux_sound.
Print Assumptions normalize_level_sound.
Print Assumptions level_le_sound.
Print Assumptions level_equiv_sound.
Print Assumptions levels_equiv_sound.
Print Assumptions normalize_aux_sufficient_fuel.
Print Assumptions normalize_level_sufficient_fuel.
Print Assumptions level_comparisons_sufficient_fuel.
