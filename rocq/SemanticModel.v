(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq formalization of Lean4Lean/Theory/VLevel.lean, VExpr.lean, VDecl.lean,
   and VEnv.lean: semantic universe levels, core de Bruijn expressions,
   lifting/instantiation algebra, and monotonic semantic environments. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness Checker.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Semantic Universe Levels (Lean4Lean/Theory/VLevel.lean)                *)
(* ========================================================================= *)

Inductive VLevel : Type :=
| VLZero : VLevel
| VLSucc : VLevel -> VLevel
| VLMax  : VLevel -> VLevel -> VLevel
| VLIMax : VLevel -> VLevel -> VLevel
| VLParam : nat -> VLevel.

Definition vlevel_imax_nat (a b : nat) : nat :=
  match b with
  | 0 => 0
  | S n => Nat.max a (S n)
  end.

Fixpoint vlevel_eval (ls : list nat) (u : VLevel) : nat :=
  match u with
  | VLZero => 0
  | VLSucc v => S (vlevel_eval ls v)
  | VLMax a b => Nat.max (vlevel_eval ls a) (vlevel_eval ls b)
  | VLIMax a b => vlevel_imax_nat (vlevel_eval ls a) (vlevel_eval ls b)
  | VLParam i => nth i ls 0
  end.

Fixpoint vlevel_wf (uvars : nat) (u : VLevel) : Prop :=
  match u with
  | VLZero => True
  | VLSucc v => vlevel_wf uvars v
  | VLMax a b | VLIMax a b => vlevel_wf uvars a /\ vlevel_wf uvars b
  | VLParam i => i < uvars
  end.

Definition vlevel_le (u v : VLevel) : Prop :=
  forall ls, vlevel_eval ls u <= vlevel_eval ls v.

Definition vlevel_equiv (u v : VLevel) : Prop :=
  forall ls, vlevel_eval ls u = vlevel_eval ls v.

Fixpoint vlevel_inst (ks : list VLevel) (u : VLevel) : VLevel :=
  match u with
  | VLZero => VLZero
  | VLSucc v => VLSucc (vlevel_inst ks v)
  | VLMax a b => VLMax (vlevel_inst ks a) (vlevel_inst ks b)
  | VLIMax a b => VLIMax (vlevel_inst ks a) (vlevel_inst ks b)
  | VLParam i => nth i ks VLZero
  end.

Lemma vlevel_le_refl u : vlevel_le u u.
Proof. intro ls. apply Nat.le_refl. Qed.

Lemma vlevel_le_trans u v w :
  vlevel_le u v -> vlevel_le v w -> vlevel_le u w.
Proof. intros H1 H2 ls. eapply Nat.le_trans; [apply H1 | apply H2]. Qed.

Lemma vlevel_equiv_refl u : vlevel_equiv u u.
Proof. intro ls. reflexivity. Qed.

Lemma vlevel_equiv_symm u v : vlevel_equiv u v -> vlevel_equiv v u.
Proof. intros H ls. symmetry. apply H. Qed.

Lemma vlevel_equiv_trans u v w :
  vlevel_equiv u v -> vlevel_equiv v w -> vlevel_equiv u w.
Proof. intros H1 H2 ls. transitivity (vlevel_eval ls v); [apply H1 | apply H2]. Qed.

Lemma vlevel_equiv_le_iff u v :
  vlevel_equiv u v <-> (vlevel_le u v /\ vlevel_le v u).
Proof.
  split.
  - intros H. split; intro ls; rewrite H; apply Nat.le_refl.
  - intros [H1 H2] ls. specialize (H1 ls). specialize (H2 ls). lia.
Qed.

Lemma vlevel_succ_congr u v :
  vlevel_equiv u v -> vlevel_equiv (VLSucc u) (VLSucc v).
Proof. intros H ls. simpl. f_equal. apply H. Qed.

Lemma vlevel_max_congr u1 u2 v1 v2 :
  vlevel_equiv u1 u2 -> vlevel_equiv v1 v2 ->
  vlevel_equiv (VLMax u1 v1) (VLMax u2 v2).
Proof. intros H1 H2 ls. simpl. rewrite (H1 ls), (H2 ls). reflexivity. Qed.

Lemma vlevel_imax_congr u1 u2 v1 v2 :
  vlevel_equiv u1 u2 -> vlevel_equiv v1 v2 ->
  vlevel_equiv (VLIMax u1 v1) (VLIMax u2 v2).
Proof. intros H1 H2 ls. simpl. rewrite (H1 ls), (H2 ls). reflexivity. Qed.

Lemma vlevel_inst_eval ls ks u :
  vlevel_eval ls (vlevel_inst ks u) = vlevel_eval (map (vlevel_eval ls) ks) u.
Proof.
  induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl.
  - reflexivity.
  - f_equal. exact IHv.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite <- (map_nth (vlevel_eval ls) ks VLZero i). reflexivity.
Qed.

Lemma vlevel_inst_congr ks1 ks2 u1 u2 :
  Forall2 vlevel_equiv ks1 ks2 ->
  vlevel_equiv u1 u2 ->
  vlevel_equiv (vlevel_inst ks1 u1) (vlevel_inst ks2 u2).
Proof.
  intros Hks Hu ls. rewrite !vlevel_inst_eval.
  assert (Hmap : map (vlevel_eval ls) ks1 = map (vlevel_eval ls) ks2).
  { induction Hks; simpl; [reflexivity|]. f_equal; [apply H | exact IHHks]. }
  rewrite Hmap. apply Hu.
Qed.

Lemma vlevel_wf_mono uvars1 uvars2 u :
  uvars1 <= uvars2 -> vlevel_wf uvars1 u -> vlevel_wf uvars2 u.
Proof.
  intros Hle. induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl; try tauto; lia.
Qed.

Lemma vlevel_inst_wf uvars ks u :
  Forall (vlevel_wf uvars) ks ->
  vlevel_wf (List.length ks) u ->
  vlevel_wf uvars (vlevel_inst ks u).
Proof.
  intros Hks. induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl; try tauto.
  intros Hi.
  destruct (nth_in_or_default i ks VLZero) as [Hin | Hdef].
  - rewrite Forall_forall in Hks. apply Hks. exact Hin.
  - rewrite Hdef. simpl. exact I.
Qed.

(* Translation from syntactic parameter list `ps` and `Syntax.level` to `VLevel` *)
Fixpoint index_of_name (ps : list name) (n : name) : option nat :=
  match ps with
  | [] => None
  | p :: rest =>
      if name_eqb n p then Some 0
      else option_map S (index_of_name rest n)
  end.

Fixpoint vlevel_of_level (ps : list name) (u : level) : option VLevel :=
  match u with
  | LZero => Some VLZero
  | LSucc v => option_map VLSucc (vlevel_of_level ps v)
  | LMax a b =>
      match vlevel_of_level ps a, vlevel_of_level ps b with
      | Some a', Some b' => Some (VLMax a' b')
      | _, _ => None
      end
  | LIMax a b =>
      match vlevel_of_level ps a, vlevel_of_level ps b with
      | Some a', Some b' => Some (VLIMax a' b')
      | _, _ => None
      end
  | LParam n => option_map VLParam (index_of_name ps n)
  | LMVar _ => None
  end.

Lemma index_of_name_lt ps n i :
  index_of_name ps n = Some i -> i < List.length ps.
Proof.
  revert i. induction ps as [|p rest IH]; intros i H; simpl in *.
  - discriminate.
  - destruct (name_eqb n p).
    + inversion H; subst. lia.
    + destruct (index_of_name rest n) as [j|] eqn:Hidx; simpl in H; try discriminate.
      inversion H; subst. specialize (IH j eq_refl). lia.
Qed.

Lemma vlevel_of_level_wf ps u u' :
  vlevel_of_level ps u = Some u' -> vlevel_wf (List.length ps) u'.
Proof.
  revert u'. induction u; intros u' H; simpl in *; try discriminate.
  - inversion H; subst. exact I.
  - destruct (vlevel_of_level ps u) as [v'|] eqn:Hv; simpl in H; try discriminate.
    inversion H; subst. simpl. eapply IHu; reflexivity.
  - destruct (vlevel_of_level ps u1) as [a'|] eqn:Ha;
    destruct (vlevel_of_level ps u2) as [b'|] eqn:Hb; try discriminate.
    inversion H; subst. simpl. split; [eapply IHu1 | eapply IHu2]; reflexivity.
  - destruct (vlevel_of_level ps u1) as [a'|] eqn:Ha;
    destruct (vlevel_of_level ps u2) as [b'|] eqn:Hb; try discriminate.
    inversion H; subst. simpl. split; [eapply IHu1 | eapply IHu2]; reflexivity.
  - destruct (index_of_name ps n) as [i|] eqn:Hi; simpl in H; try discriminate.
    inversion H; subst. simpl. eapply index_of_name_lt; exact Hi.
Qed.

Fixpoint env_rho_of_ls (ps : list name) (ls : list nat) (n : name) : nat :=
  match ps, ls with
  | p :: ps', x :: ls' => if name_eqb n p then x else env_rho_of_ls ps' ls' n
  | p :: ps', [] => if name_eqb n p then 0 else env_rho_of_ls ps' [] n
  | [], _ => 0
  end.

Lemma index_of_name_eval ps ls n i :
  index_of_name ps n = Some i ->
  nth i ls 0 = env_rho_of_ls ps ls n.
Proof.
  revert ls i. induction ps as [|p rest IH]; intros ls i H; simpl in *; [discriminate|].
  destruct (name_eqb n p) eqn:Heq.
  - inversion H; subst. destruct ls; reflexivity.
  - destruct (index_of_name rest n) as [j|] eqn:Hj; simpl in H; [|discriminate].
    inversion H; subst. destruct ls as [|x ls'].
    + rewrite <- (IH [] j eq_refl). destruct j; reflexivity.
    + simpl. apply IH. reflexivity.
Qed.

Theorem vlevel_of_level_eval ps ls u u' :
  vlevel_of_level ps u = Some u' ->
  vlevel_eval ls u' = level_eval (env_rho_of_ls ps ls) u.
Proof.
  revert u'. induction u; intros u' H; simpl in *; try discriminate.
  - inversion H; subst. reflexivity.
  - destruct (vlevel_of_level ps u) as [v'|] eqn:Hv; simpl in H; [|discriminate].
    inversion H; subst. simpl. f_equal. apply IHu. reflexivity.
  - destruct (vlevel_of_level ps u1) as [a'|] eqn:Ha;
    destruct (vlevel_of_level ps u2) as [b'|] eqn:Hb; try discriminate.
    inversion H; subst. simpl. rewrite (IHu1 a' eq_refl), (IHu2 b' eq_refl). reflexivity.
  - destruct (vlevel_of_level ps u1) as [a'|] eqn:Ha;
    destruct (vlevel_of_level ps u2) as [b'|] eqn:Hb; try discriminate.
    inversion H; subst. simpl. rewrite (IHu1 a' eq_refl), (IHu2 b' eq_refl). reflexivity.
  - destruct (index_of_name ps n) as [i|] eqn:Hi; simpl in H; [|discriminate].
    inversion H; subst. simpl. apply index_of_name_eval. exact Hi.
Qed.

Theorem check_level_sound_vlevel ps u :
  check_level ps u = Accept tt ->
  exists u', vlevel_of_level ps u = Some u' /\ vlevel_wf (List.length ps) u'.
Proof.
  unfold check_level, require.
  destruct (level_has_meta u) eqn:Hmeta; [discriminate|].
  destruct (level_wf ps u) eqn:Hwf; [|discriminate].
  intros _.
  assert (Hconv : exists u', vlevel_of_level ps u = Some u').
  { induction u; simpl in *.
    - exists VLZero. reflexivity.
    - destruct (IHu Hmeta Hwf) as [v' Hv']. rewrite Hv'. exists (VLSucc v'). reflexivity.
    - apply orb_false_iff in Hmeta as [Hm1 Hm2].
      apply andb_true_iff in Hwf as [Hw1 Hw2].
      destruct (IHu1 Hm1 Hw1) as [a' Ha'].
      destruct (IHu2 Hm2 Hw2) as [b' Hb'].
      rewrite Ha', Hb'. exists (VLMax a' b'). reflexivity.
    - apply orb_false_iff in Hmeta as [Hm1 Hm2].
      apply andb_true_iff in Hwf as [Hw1 Hw2].
      destruct (IHu1 Hm1 Hw1) as [a' Ha'].
      destruct (IHu2 Hm2 Hw2) as [b' Hb'].
      rewrite Ha', Hb'. exists (VLIMax a' b'). reflexivity.
    - clear Hmeta.
      assert (Hidx : exists i, index_of_name ps n = Some i).
      { clear -Hwf. induction ps as [|p rest IH]; simpl in *.
        - discriminate.
        - unfold name_mem in Hwf. simpl in Hwf.
          destruct (name_eqb n p) eqn:Heq.
          + exists 0. reflexivity.
          + simpl in Hwf. destruct (IH Hwf) as [j Hj]. rewrite Hj. exists (S j). reflexivity. }
      destruct Hidx as [i Hi]. rewrite Hi. exists (VLParam i). reflexivity.
    - discriminate. }
  destruct Hconv as [u' Hu'].
  exists u'. split; [exact Hu' | eapply vlevel_of_level_wf; exact Hu'].
Qed.

Theorem level_equiv_sound_vlevel fuel ps u v u' v' :
  vlevel_of_level ps u = Some u' ->
  vlevel_of_level ps v = Some v' ->
  level_equiv fuel u v = Accept true ->
  vlevel_equiv u' v'.
Proof.
  intros Hu Hv Heq ls.
  rewrite (vlevel_of_level_eval ps ls u Hu), (vlevel_of_level_eval ps ls v Hv).
  eapply level_equiv_sound. exact Heq.
Qed.

Theorem level_le_sound_vlevel fuel ps u v u' v' :
  vlevel_of_level ps u = Some u' ->
  vlevel_of_level ps v = Some v' ->
  level_le fuel u v = Accept true ->
  vlevel_le u' v'.
Proof.
  intros Hu Hv Hle ls.
  rewrite (vlevel_of_level_eval ps ls u Hu), (vlevel_of_level_eval ps ls v Hv).
  eapply level_le_sound. exact Hle.
Qed.

(* ========================================================================= *)
(* 2. Core Semantic Expressions (Lean4Lean/Theory/VExpr.lean)                *)
(* ========================================================================= *)

Inductive VExpr : Type :=
| VBVar    : nat -> VExpr
| VSort    : VLevel -> VExpr
| VConst   : name -> list VLevel -> VExpr
| VApp     : VExpr -> VExpr -> VExpr
| VLam     : VExpr -> VExpr -> VExpr
| VForallE : VExpr -> VExpr -> VExpr.

Definition vliftVar (n i k : nat) : nat :=
  if i <? k then i else n + i.

Fixpoint vliftN (n : nat) (k : nat) (e : VExpr) : VExpr :=
  match e with
  | VBVar i => VBVar (vliftVar n i k)
  | VSort u => VSort u
  | VConst c us => VConst c us
  | VApp f a => VApp (vliftN n k f) (vliftN n k a)
  | VLam A b => VLam (vliftN n k A) (vliftN n (S k) b)
  | VForallE A B => VForallE (vliftN n k A) (vliftN n (S k) B)
  end.

Definition vlift (e : VExpr) : VExpr := vliftN 1 0 e.

Definition vinstVar (i : nat) (e : VExpr) (k : nat) : VExpr :=
  if i <? k then VBVar i
  else if Nat.eqb i k then vliftN k 0 e
  else VBVar (pred i).

Fixpoint vinst (e : VExpr) (v : VExpr) (k : nat) : VExpr :=
  match e with
  | VBVar i => vinstVar i v k
  | VSort u => VSort u
  | VConst c us => VConst c us
  | VApp f a => VApp (vinst f v k) (vinst a v k)
  | VLam A b => VLam (vinst A v k) (vinst b v (S k))
  | VForallE A B => VForallE (vinst A v k) (vinst B v (S k))
  end.

Definition vinst0 (e v : VExpr) : VExpr := vinst e v 0.

Fixpoint vinstL (ks : list VLevel) (e : VExpr) : VExpr :=
  match e with
  | VBVar i => VBVar i
  | VSort u => VSort (vlevel_inst ks u)
  | VConst c us => VConst c (map (vlevel_inst ks) us)
  | VApp f a => VApp (vinstL ks f) (vinstL ks a)
  | VLam A b => VLam (vinstL ks A) (vinstL ks b)
  | VForallE A B => VForallE (vinstL ks A) (vinstL ks B)
  end.

Fixpoint vclosedN (k : nat) (e : VExpr) : Prop :=
  match e with
  | VBVar i => i < k
  | VSort _ | VConst _ _ => True
  | VApp f a => vclosedN k f /\ vclosedN k a
  | VLam A b | VForallE A b => vclosedN k A /\ vclosedN (S k) b
  end.

Definition vclosed (e : VExpr) : Prop := vclosedN 0 e.

Fixpoint vlevelWF (uvars : nat) (e : VExpr) : Prop :=
  match e with
  | VBVar _ => True
  | VSort u => vlevel_wf uvars u
  | VConst _ us => Forall (vlevel_wf uvars) us
  | VApp f a | VLam f a | VForallE f a => vlevelWF uvars f /\ vlevelWF uvars a
  end.

(* ========================================================================= *)
(* 3. Lifting, Instantiation, Scope & Universe Substitution Algebra          *)
(* ========================================================================= *)

Lemma vliftVar_zero i k : vliftVar 0 i k = i.
Proof. unfold vliftVar. destruct (i <? k); reflexivity. Qed.

Theorem vliftN_zero e : forall k, vliftN 0 k e = e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros k; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity).
  rewrite vliftVar_zero. reflexivity.
Qed.

Lemma vliftVar_comp n m i k :
  vliftVar m (vliftVar n i k) k = vliftVar (m + n) i k.
Proof.
  unfold vliftVar. destruct (i <? k) eqn:Hlt.
  - rewrite Hlt. reflexivity.
  - pose proof (proj1 (Nat.ltb_ge _ _) Hlt) as Hge.
    assert ((n + i <? k) = false) as Hlt2 by (apply Nat.ltb_ge; lia).
    rewrite Hlt2. lia.
Qed.

Theorem vliftN_comp e : forall n m k,
  vliftN m k (vliftN n k e) = vliftN (m + n) k e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 m k; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity).
  rewrite vliftVar_comp. reflexivity.
Qed.

Theorem vliftN_vliftN e : forall n m k1 k2,
  k1 <= k2 -> k2 <= n + k1 ->
  vliftN m k2 (vliftN n k1 e) = vliftN (m + n) k1 e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 m k1 k2 Hle1 Hle2; simpl; try reflexivity.
  - unfold vliftVar.
    destruct (idx <? k1) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as Hlt1.
      assert ((idx <? k2) = true) as H2 by (apply Nat.ltb_lt; lia).
      rewrite H2. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as Hge1.
      assert ((n0 + idx <? k2) = false) as H2 by (apply Nat.ltb_ge; lia).
      rewrite H2. f_equal. lia.
  - rewrite IHf, IHa by lia. reflexivity.
  - rewrite IHA, IHb by lia. reflexivity.
  - rewrite IHA, IHB by lia. reflexivity.
Qed.

Theorem vliftN_comm e : forall n1 n2 k1 k2,
  k2 <= k1 ->
  vliftN n1 (n2 + k1) (vliftN n2 k2 e) = vliftN n2 k2 (vliftN n1 k1 e).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n1 n2 k1 k2 Hle; simpl; try reflexivity.
  - unfold vliftVar.
    destruct (idx <? k2) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as Hlt1.
      assert ((idx <? n2 + k1) = true) as H2 by (apply Nat.ltb_lt; lia).
      assert ((idx <? k1) = true) as H3 by (apply Nat.ltb_lt; lia).
      rewrite H2, H3, H1. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as Hge1.
      destruct (idx <? k1) eqn:H2.
      * pose proof (proj1 (Nat.ltb_lt _ _) H2) as Hlt2.
        assert ((n2 + idx <? n2 + k1) = true) as H3 by (apply Nat.ltb_lt; lia).
        rewrite H3, H1. reflexivity.
      * pose proof (proj1 (Nat.ltb_ge _ _) H2) as Hge2.
        assert ((n2 + idx <? n2 + k1) = false) as H3 by (apply Nat.ltb_ge; lia).
        assert ((n1 + idx <? k2) = false) as H4 by (apply Nat.ltb_ge; lia).
        rewrite H3, H4. f_equal. lia.
  - rewrite IHf, IHa by lia. reflexivity.
  - rewrite IHA by lia.
    replace (S (n2 + k1)) with (n2 + S k1) by lia.
    rewrite IHb by lia. reflexivity.
  - rewrite IHA by lia.
    replace (S (n2 + k1)) with (n2 + S k1) by lia.
    rewrite IHB by lia. reflexivity.
Qed.

Theorem vinst_vliftN e : forall v n k,
  vinst (vliftN (S n) k e) v k = vliftN n k e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val n0 k; simpl; try reflexivity.
  - unfold vliftVar, vinstVar.
    destruct (idx <? k) eqn:Hlt.
    + rewrite Hlt. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) Hlt) as Hge.
      assert ((S n0 + idx <? k) = false) as H1 by (apply Nat.ltb_ge; lia).
      assert ((S n0 + idx =? k) = false) as H2 by (apply Nat.eqb_neq; lia).
      rewrite H1, H2. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. reflexivity.
  - rewrite IHA, IHB. reflexivity.
Qed.

Corollary vinst0_vlift e v : vinst0 (vlift e) v = e.
Proof.
  unfold vinst0, vlift. rewrite vinst_vliftN, vliftN_zero. reflexivity.
Qed.

Theorem vliftN_vinst_hi e : forall v n k j,
  j <= k ->
  vliftN n k (vinst e v j) = vinst (vliftN n (S k) e) (vliftN n (k - j) v) j.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val n0 k j Hle; simpl; try reflexivity.
  - unfold vinstVar, vliftVar.
    destruct (idx <? j) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as Hlt1.
      assert ((idx <? S k) = true) as H2 by (apply Nat.ltb_lt; lia).
      assert ((idx <? k) = true) as H3 by (apply Nat.ltb_lt; lia).
      rewrite H2. simpl. unfold vliftVar, vinstVar.
      rewrite H3, H1. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as Hge1.
      destruct (Nat.eqb idx j) eqn:H2.
      * pose proof (proj1 (Nat.eqb_eq _ _) H2) as Heq. subst idx.
        assert ((j <? S k) = true) as H3 by (apply Nat.ltb_lt; lia).
        rewrite H3. simpl. unfold vinstVar.
        rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        replace k with (j + (k - j)) at 1 by lia.
        apply vliftN_comm. lia.
      * pose proof (proj1 (Nat.eqb_neq _ _) H2) as Hneq.
        destruct (idx <? S k) eqn:H3.
        -- pose proof (proj1 (Nat.ltb_lt _ _) H3) as Hlt3.
           assert ((pred idx <? k) = true) as H6 by (apply Nat.ltb_lt; lia).
           simpl. unfold vliftVar, vinstVar.
           rewrite H1, H2, H6. reflexivity.
        -- pose proof (proj1 (Nat.ltb_ge _ _) H3) as Hge3.
           assert ((n0 + idx <? j) = false) as H4 by (apply Nat.ltb_ge; lia).
           assert ((n0 + idx =? j) = false) as H5 by (apply Nat.eqb_neq; lia).
           assert ((pred idx <? k) = false) as H6 by (apply Nat.ltb_ge; lia).
           simpl. unfold vliftVar, vinstVar.
           rewrite H4, H5, H6. f_equal. lia.
  - rewrite IHf, IHa by lia. reflexivity.
  - rewrite IHA by lia.
    rewrite (IHb val n0 (S k) (S j)) by lia.
    simpl. reflexivity.
  - rewrite IHA by lia.
    rewrite (IHB val n0 (S k) (S j)) by lia.
    simpl. reflexivity.
Qed.

Corollary vliftN_vinst0 e v n k :
  vliftN n k (vinst0 e v) = vinst0 (vliftN n (S k) e) (vliftN n k v).
Proof.
  unfold vinst0. rewrite vliftN_vinst_hi by lia.
  replace (k - 0) with k by lia. reflexivity.
Qed.

Theorem vliftN_vinst_lo e : forall v n k j,
  k <= j ->
  vliftN n k (vinst e v j) = vinst (vliftN n k e) v (n + j).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val n0 k j Hle; simpl; try reflexivity.
  - unfold vinstVar, vliftVar.
    destruct (idx <? j) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as Hlt1.
      destruct (idx <? k) eqn:H2.
      * pose proof (proj1 (Nat.ltb_lt _ _) H2) as Hlt2.
        assert ((idx <? n0 + j) = true) as H3 by (apply Nat.ltb_lt; lia).
        simpl. unfold vliftVar, vinstVar.
        rewrite H2, H3. reflexivity.
      * pose proof (proj1 (Nat.ltb_ge _ _) H2) as Hge2.
        assert ((n0 + idx <? n0 + j) = true) as H3 by (apply Nat.ltb_lt; lia).
        simpl. unfold vliftVar, vinstVar.
        rewrite H2, H3. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as Hge1.
      assert ((idx <? k) = false) as H2 by (apply Nat.ltb_ge; lia).
      rewrite H2.
      destruct (Nat.eqb idx j) eqn:H3.
      * pose proof (proj1 (Nat.eqb_eq _ _) H3) as Heq. subst idx.
        simpl. unfold vinstVar.
        assert ((n0 + j <? n0 + j) = false) as H4 by (apply Nat.ltb_ge; lia).
        assert ((n0 + j =? n0 + j) = true) as H5 by (apply Nat.eqb_eq; lia).
        rewrite H4, H5.
        rewrite vliftN_vliftN by lia. reflexivity.
      * pose proof (proj1 (Nat.eqb_neq _ _) H3) as Hneq.
        assert ((n0 + idx <? n0 + j) = false) as H4 by (apply Nat.ltb_ge; lia).
        assert ((n0 + idx =? n0 + j) = false) as H5 by (apply Nat.eqb_neq; lia).
        assert ((pred idx <? k) = false) as H6 by (apply Nat.ltb_ge; lia).
        simpl. unfold vliftVar, vinstVar.
        rewrite H4, H5, H6. f_equal. lia.
  - rewrite IHf, IHa by lia. reflexivity.
  - rewrite IHA by lia.
    replace (S (n0 + j)) with (n0 + S j) by lia.
    rewrite IHb by lia. reflexivity.
  - rewrite IHA by lia.
    replace (S (n0 + j)) with (n0 + S j) by lia.
    rewrite IHB by lia. reflexivity.
Qed.

Theorem vinst_vliftN_gen e : forall v n k0 k,
  k0 <= k -> k <= n + k0 ->
  vinst (vliftN (S n) k0 e) v k = vliftN n k0 e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val n0 k0 k Hle1 Hle2; simpl; try reflexivity.
  - unfold vliftVar, vinstVar.
    destruct (idx <? k0) eqn:Hlt.
    + pose proof (proj1 (Nat.ltb_lt _ _) Hlt) as Hlt0.
      assert ((idx <? k) = true) as Hlt_k by (apply Nat.ltb_lt; lia).
      rewrite Hlt_k. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) Hlt) as Hge0.
      assert ((S n0 + idx <? k) = false) as H1 by (apply Nat.ltb_ge; lia).
      assert ((S n0 + idx =? k) = false) as H2 by (apply Nat.eqb_neq; lia).
      rewrite H1, H2. reflexivity.
  - rewrite IHf, IHa by lia. reflexivity.
  - rewrite IHA, IHb by lia. reflexivity.
  - rewrite IHA, IHB by lia. reflexivity.
Qed.

Theorem vinst_vinst_hi e : forall u v k j,
  vinst (vinst e u k) v (j + k) =
  vinst (vinst e v (S (j + k))) (vinst u v j) k.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros u0 v0 k j; simpl; try reflexivity.
  - unfold vinstVar.
    destruct (idx <? k) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as Hlt1.
      assert ((idx <? j + k) = true) as H2 by (apply Nat.ltb_lt; lia).
      assert ((idx <? S (j + k)) = true) as H3 by (apply Nat.ltb_lt; lia).
      rewrite H3. simpl. unfold vinstVar.
      rewrite H2, H1. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as Hge1.
      destruct (Nat.eqb idx k) eqn:H2.
      * pose proof (proj1 (Nat.eqb_eq _ _) H2) as Heq. subst idx.
        assert ((k <? S (j + k)) = true) as H3 by (apply Nat.ltb_lt; lia).
        rewrite H3. simpl. unfold vinstVar.
        rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        replace (j + k) with (k + j) by lia.
        symmetry. apply vliftN_vinst_lo. lia.
      * pose proof (proj1 (Nat.eqb_neq _ _) H2) as Hneq.
        destruct (idx <? S (j + k)) eqn:H3.
        -- pose proof (proj1 (Nat.ltb_lt _ _) H3) as Hlt3.
           assert ((pred idx <? j + k) = true) as H4 by (apply Nat.ltb_lt; lia).
           simpl. unfold vinstVar.
           rewrite H4, H1, H2. reflexivity.
        -- pose proof (proj1 (Nat.ltb_ge _ _) H3) as Hge3.
           destruct (Nat.eqb idx (S (j + k))) eqn:H4.
           ++ pose proof (proj1 (Nat.eqb_eq _ _) H4) as Heq4. subst idx.
              simpl. unfold vinstVar.
              rewrite Nat.ltb_irrefl, Nat.eqb_refl.
              symmetry. apply vinst_vliftN_gen; lia.
           ++ pose proof (proj1 (Nat.eqb_neq _ _) H4) as Hneq4.
              assert ((pred idx <? j + k) = false) as H5 by (apply Nat.ltb_ge; lia).
              assert ((pred idx =? j + k) = false) as H6 by (apply Nat.eqb_neq; lia).
              assert ((pred idx <? k) = false) as H7 by (apply Nat.ltb_ge; lia).
              assert ((pred idx =? k) = false) as H8 by (apply Nat.eqb_neq; lia).
              simpl. unfold vinstVar.
              rewrite H5, H6, H7, H8. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA.
    replace (S (j + k)) with (j + S k) by lia.
    rewrite (IHb u0 v0 (S k) j). reflexivity.
  - rewrite IHA.
    replace (S (j + k)) with (j + S k) by lia.
    rewrite (IHB u0 v0 (S k) j). reflexivity.
Qed.

Corollary vinst0_vinst_hi e u v j :
  vinst (vinst0 e u) v j = vinst0 (vinst e v (S j)) (vinst u v j).
Proof.
  unfold vinst0.
  pose proof (vinst_vinst_hi e u v 0 j) as H.
  replace (j + 0) with j in H by lia.
  exact H.
Qed.

Corollary vinst0_vinst0 e u v :
  vinst0 (vinst0 e u) v = vinst0 (vinst e v 1) (vinst0 u v).
Proof.
  exact (vinst0_vinst_hi e u v 0).
Qed.

Theorem vclosedN_mono e : forall k1 k2,
  k1 <= k2 -> vclosedN k1 e -> vclosedN k2 e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros k1 k2 Hle Hc; simpl in *; try tauto; try lia.
  - destruct Hc as [H1 H2]. split; [eapply IHf | eapply IHa]; eauto.
  - destruct Hc as [H1 H2]. split; [eapply IHA; eauto | eapply IHb; [|exact H2]; lia].
  - destruct Hc as [H1 H2]. split; [eapply IHA; eauto | eapply IHB; [|exact H2]; lia].
Qed.

Theorem vclosedN_vliftN_eq e : forall n k,
  vclosedN k e -> vliftN n k e = e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 k Hc; simpl in *; try reflexivity.
  - unfold vliftVar.
    assert ((idx <? k) = true) as Hlt by (apply Nat.ltb_lt; lia).
    rewrite Hlt. reflexivity.
  - destruct Hc as [H1 H2]. rewrite (IHf n0 k H1), (IHa n0 k H2). reflexivity.
  - destruct Hc as [H1 H2]. rewrite (IHA n0 k H1), (IHb n0 (S k) H2). reflexivity.
  - destruct Hc as [H1 H2]. rewrite (IHA n0 k H1), (IHB n0 (S k) H2). reflexivity.
Qed.

Theorem vliftN_preserves_vclosedN e : forall n k d,
  k <= d -> vclosedN d e -> vclosedN (n + d) (vliftN n k e).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 k d Hle Hc; simpl in *; try tauto.
  - unfold vliftVar. destruct (idx <? k) eqn:Hlt.
    + pose proof (proj1 (Nat.ltb_lt _ _) Hlt). lia.
    + lia.
  - destruct Hc as [H1 H2]. split; auto.
  - destruct Hc as [H1 H2]. split; [apply IHA; auto |].
    replace (S (n0 + d)) with (n0 + S d) by lia.
    apply IHb; [lia | exact H2].
  - destruct Hc as [H1 H2]. split; [apply IHA; auto |].
    replace (S (n0 + d)) with (n0 + S d) by lia.
    apply IHB; [lia | exact H2].
Qed.

Theorem vinst_preserves_vclosedN e : forall v k d,
  k <= d ->
  vclosedN (S d) e ->
  vclosedN (d - k) v ->
  vclosedN d (vinst e v k).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val k d Hle Hce Hcv; simpl in *; try tauto.
  - unfold vinstVar.
    destruct (idx <? k) eqn:Hlt.
    + pose proof (proj1 (Nat.ltb_lt _ _) Hlt). simpl. lia.
    + pose proof (proj1 (Nat.ltb_ge _ _) Hlt).
      destruct (Nat.eqb idx k) eqn:Heq.
      * pose proof (proj1 (Nat.eqb_eq _ _) Heq). subst idx.
        replace d with (k + (d - k)) by lia.
        apply vliftN_preserves_vclosedN; [lia|].
        replace (k + (d - k) - k) with (d - k) by lia.
        exact Hcv.
      * pose proof (proj1 (Nat.eqb_neq _ _) Heq). simpl. lia.
  - destruct Hce as [H1 H2]. split; auto.
  - destruct Hce as [H1 H2]. split; [apply IHA; auto |].
    apply IHb; [lia | exact H2 |].
    replace (S d - S k) with (d - k) by lia. exact Hcv.
  - destruct Hce as [H1 H2]. split; [apply IHA; auto |].
    apply IHB; [lia | exact H2 |].
    replace (S d - S k) with (d - k) by lia. exact Hcv.
Qed.

Theorem vinstL_vliftN ks e : forall n k,
  vinstL ks (vliftN n k e) = vliftN n k (vinstL ks e).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 k; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity).
Qed.

Theorem vinstL_vinst ks e : forall v k,
  vinstL ks (vinst e v k) = vinst (vinstL ks e) (vinstL ks v) k.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val k; simpl; try reflexivity.
  - unfold vinstVar.
    destruct (idx <? k); [reflexivity|].
    destruct (Nat.eqb idx k); [apply vinstL_vliftN | reflexivity].
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. reflexivity.
  - rewrite IHA, IHB. reflexivity.
Qed.

Theorem vlevelWF_vliftN uvars e : forall n k,
  vlevelWF uvars (vliftN n k e) <-> vlevelWF uvars e.
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros n0 k; simpl; try tauto.
  - rewrite IHf, IHa. tauto.
  - rewrite IHA, IHb. tauto.
  - rewrite IHA, IHB. tauto.
Qed.

Theorem vlevelWF_vinst uvars e : forall v k,
  vlevelWF uvars e -> vlevelWF uvars v -> vlevelWF uvars (vinst e v k).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros val k He Hv; simpl in *; try tauto.
  - unfold vinstVar. destruct (idx <? k); [exact I|].
    destruct (Nat.eqb idx k); [apply vlevelWF_vliftN; exact Hv | exact I].
  - destruct He as [H1 H2]. split; auto.
  - destruct He as [H1 H2]. split; auto.
  - destruct He as [H1 H2]. split; auto.
Qed.

Theorem vlevelWF_vinstL uvars ks e :
  Forall (vlevel_wf uvars) ks ->
  vlevelWF (List.length ks) e ->
  vlevelWF uvars (vinstL ks e).
Proof.
  intros Hks.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    simpl; try tauto.
  - apply vlevel_inst_wf. exact Hks.
  - intros Hus. induction Hus; simpl; constructor.
    + apply vlevel_inst_wf; assumption.
    + exact IHHus.
Qed.

(* ========================================================================= *)
(* 4. Semantic Declarations and Environments (VDecl.lean / VEnv.lean)        *)
(* ========================================================================= *)

Record VConstant : Type := {
  vc_uvars : nat;
  vc_type  : VExpr
}.

Record VDefEq : Type := {
  vdf_uvars : nat;
  vdf_lhs   : VExpr;
  vdf_rhs   : VExpr;
  vdf_type  : VExpr
}.

Record VEnv : Type := {
  venv_constants : name -> option VConstant;
  venv_defeqs    : VDefEq -> Prop
}.

Definition venv_empty : VEnv := {|
  venv_constants := fun _ => None;
  venv_defeqs    := fun _ => False
|}.

Definition venv_contains (env : VEnv) (n : name) : Prop :=
  exists ci, venv_constants env n = Some ci.

Definition venv_add_const (env : VEnv) (n : name) (ci : VConstant) : option VEnv :=
  match venv_constants env n with
  | Some _ => None
  | None => Some {|
      venv_constants := fun m => if name_eqb m n then Some ci else venv_constants env m;
      venv_defeqs    := venv_defeqs env
    |}
  end.

Definition venv_add_defeq (env : VEnv) (df : VDefEq) : VEnv := {|
  venv_constants := venv_constants env;
  venv_defeqs    := fun x => x = df \/ venv_defeqs env x
|}.

Record venv_ordered (env1 env2 : VEnv) : Prop := {
  venv_ord_const : forall n ci,
    venv_constants env1 n = Some ci -> venv_constants env2 n = Some ci;
  venv_ord_defeq : forall df,
    venv_defeqs env1 df -> venv_defeqs env2 df
}.

Lemma venv_ordered_refl env : venv_ordered env env.
Proof. split; auto. Qed.

Lemma venv_ordered_trans env1 env2 env3 :
  venv_ordered env1 env2 -> venv_ordered env2 env3 -> venv_ordered env1 env3.
Proof.
  intros [Hc1 Hd1] [Hc2 Hd2]. split; auto.
Qed.

Lemma venv_add_const_ordered env n ci env' :
  venv_add_const env n ci = Some env' ->
  venv_ordered env env'.
Proof.
  unfold venv_add_const.
  destruct (venv_constants env n) eqn:Hfind; [discriminate|].
  intros H. inversion H; subst; clear H.
  split; simpl; auto.
  intros m cj Hm.
  destruct (name_eqb m n) eqn:Heq.
  - apply name_eqb_eq in Heq. subst m. congruence.
  - exact Hm.
Qed.

Lemma venv_add_const_lookup_self env n ci env' :
  venv_add_const env n ci = Some env' ->
  venv_constants env' n = Some ci.
Proof.
  unfold venv_add_const.
  destruct (venv_constants env n); [discriminate|].
  intros H. inversion H; subst; simpl.
  rewrite name_eqb_refl. reflexivity.
Qed.

Lemma venv_add_defeq_ordered env df :
  venv_ordered env (venv_add_defeq env df).
Proof.
  split; simpl; auto.
Qed.

Print Assumptions vlevel_of_level_eval.
Print Assumptions check_level_sound_vlevel.
Print Assumptions level_equiv_sound_vlevel.
Print Assumptions vliftN_vliftN.
Print Assumptions vliftN_comm.
Print Assumptions vliftN_vinst_hi.
Print Assumptions vliftN_vinst_lo.
Print Assumptions vinst_vinst_hi.
Print Assumptions vinst0_vinst_hi.
Print Assumptions vinst_vliftN.
Print Assumptions vinst_preserves_vclosedN.
Print Assumptions venv_add_const_ordered.
