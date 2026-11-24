(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/VExpr.lean (remaining lifting/unlifting/skipping
   and simultaneous substitution algebra) and Lean4Lean/Theory/Typing/Lemmas.lean
   (Ctx.Lift' and Ctx.SubstEq).
   100% constructive and axiom-free (no funext, no classical axioms). *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel
  DeclarativeTyping TypingLemmas.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Telescope Instantiation, Unlifting, and Skipping (VExpr.lean)          *)
(* ========================================================================= *)

Definition vdefault : VExpr := VSort VLZero.

Fixpoint vinsts (e : VExpr) (args : list VExpr) : VExpr :=
  match args with
  | [] => e
  | a :: rest => vinst0 (vinsts e rest) a
  end.

Lemma vinsts_nil e : vinsts e [] = e.
Proof. reflexivity. Qed.

Lemma vinsts_cons e a args : vinsts e (a :: args) = vinst0 (vinsts e args) a.
Proof. reflexivity. Qed.

Theorem vinsts_append e args1 args2 :
  vinsts e (args1 ++ args2) = vinsts (vinsts e args2) args1.
Proof.
  induction args1 as [|a rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma vinsts_sort u args : vinsts (VSort u) args = VSort u.
Proof.
  induction args as [|a rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma vinsts_const c us args : vinsts (VConst c us) args = VConst c us.
Proof.
  induction args as [|a rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma vinsts_app e1 e2 args :
  vinsts (VApp e1 e2) args = VApp (vinsts e1 args) (vinsts e2 args).
Proof.
  induction args as [|a rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma vinst_vliftN_one e v k :
  vinst (vliftN 1 k e) v k = e.
Proof.
  pose proof (@vinst_vliftN e v 0 k) as H.
  rewrite vliftN_zero in H. exact H.
Qed.

Fixpoint vunliftN (n k : nat) (e : VExpr) : VExpr :=
  match n with
  | 0 => e
  | S n' => vunliftN n' k (vinst e vdefault k)
  end.

Theorem vunliftN_vliftN n k e :
  vunliftN n k (vliftN n k e) = e.
Proof.
  revert k e.
  induction n as [|n IH]; intros k e; simpl.
  - rewrite vliftN_zero. reflexivity.
  - rewrite vinst_vliftN. apply IH.
Qed.

Theorem vliftN_inj n k e1 e2 :
  vliftN n k e1 = vliftN n k e2 <-> e1 = e2.
Proof.
  split; [|intros ->; reflexivity].
  intros H.
  rewrite <- (vunliftN_vliftN n k e1), H, vunliftN_vliftN.
  reflexivity.
Qed.

Theorem vliftVar_inj n k i1 i2 :
  vliftVar n i1 k = vliftVar n i2 k <-> i1 = i2.
Proof.
  split; [|intros ->; reflexivity].
  intros H.
  assert (He : vliftN n k (VBVar i1) = vliftN n k (VBVar i2)) by (simpl; congruence).
  apply vliftN_inj in He. inversion He; reflexivity.
Qed.

Theorem vunliftN_add n1 n2 k e :
  vunliftN (n1 + n2) k e = vunliftN n2 k (vunliftN n1 k e).
Proof.
  revert e.
  induction n1 as [|n1 IH]; intros e; simpl; [reflexivity | apply IH].
Qed.

Theorem vliftN_vunliftN_hi n1 n2 k1 k2 e :
  k2 <= k1 ->
  vliftN n1 k1 (vunliftN n2 k2 e) = vunliftN n2 k2 (vliftN n1 (k1 + n2) e).
Proof.
  intros Hle.
  revert k1 e Hle.
  induction n2 as [|n2 IH]; intros k1 e Hle; simpl.
  - replace (k1 + 0) with k1 by lia. reflexivity.
  - rewrite IH by exact Hle.
    f_equal.
    rewrite (@vliftN_vinst_hi e vdefault n1 (k1 + n2) k2 ltac:(lia)).
    replace (S (k1 + n2)) with (k1 + S n2) by lia.
    reflexivity.
Qed.

Definition VSkips (n k : nat) (e : VExpr) : Prop :=
  vliftN n k (vunliftN n k e) = e.

Theorem VSkips_vliftN n k e : VSkips n k (vliftN n k e).
Proof.
  unfold VSkips. rewrite vunliftN_vliftN. reflexivity.
Qed.

Theorem vskips_iff_exists n k e :
  VSkips n k e <-> exists e', e = vliftN n k e'.
Proof.
  split.
  - intros H. exists (vunliftN n k e). symmetry. exact H.
  - intros [e' ->]. apply VSkips_vliftN.
Qed.

Theorem VSkips_zero k e : VSkips 0 k e.
Proof.
  unfold VSkips. simpl. apply vliftN_zero.
Qed.

Theorem VSkips_of_vliftN_hi n1 n2 k1 k2 e :
  n2 + k2 <= k1 ->
  VSkips n2 k2 (vliftN n1 k1 e) ->
  VSkips n2 k2 e.
Proof.
  intros Hle Hsk. unfold VSkips in *.
  replace k1 with (n2 + (k1 - n2)) in Hsk by lia.
  pose proof (@vliftN_vunliftN_hi n1 n2 (k1 - n2) k2 e ltac:(lia)) as Hcomm1.
  replace (k1 - n2 + n2) with (n2 + (k1 - n2)) in Hcomm1 by lia.
  rewrite <- Hcomm1 in Hsk.
  pose proof (@vliftN_comm (vunliftN n2 k2 e) n1 n2 (k1 - n2) k2 ltac:(lia)) as Hcomm2.
  rewrite <- Hcomm2 in Hsk.
  apply vliftN_inj in Hsk. exact Hsk.
Qed.

Fixpoint VSkips' (n k : nat) (e : VExpr) : Prop :=
  match e with
  | VBVar i => i < k + n -> i < k
  | VSort _ | VConst _ _ => True
  | VApp f a => VSkips' n k f /\ VSkips' n k a
  | VLam A b | VForallE A b => VSkips' n k A /\ VSkips' n (S k) b
  end.

Theorem vskips_iff n k e :
  VSkips n k e <-> VSkips' n k e.
Proof.
  rewrite vskips_iff_exists.
  revert k.
  induction e as [i|u|c ls|f IHf a IHa|A IHA b IHb|A IHA B IHB]; intros k; simpl.
  - split.
    + intros [e' Heq]. destruct e'; simpl in Heq; try discriminate.
      injection Heq as Hi. unfold vliftVar in Hi.
      destruct (n0 <? k) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. subst i. intros _. exact Hlt.
      * apply Nat.ltb_ge in Hlt. lia.
    + intros H.
      destruct (lt_dec i (k + n)) as [Hlt | Hge].
      * pose proof (H Hlt) as Hik.
        exists (VBVar i). simpl. unfold vliftVar.
        apply Nat.ltb_lt in Hik. rewrite Hik. reflexivity.
      * exists (VBVar (i - n)). simpl. unfold vliftVar.
        assert (Hnlt : (i - n <? k) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hnlt. f_equal. lia.
  - split; [intros _; exact I | intros _; exists (VSort u); reflexivity].
  - split; [intros _; exact I | intros _; exists (VConst c ls); reflexivity].
  - rewrite <- IHf, <- IHa. split.
    + intros [e' Heq]. destruct e'; simpl in Heq; try discriminate.
      inversion Heq; subst. split; eexists; reflexivity.
    + intros [[f' ->] [a' ->]]. exists (VApp f' a'). reflexivity.
  - rewrite <- IHA, <- IHb. split.
    + intros [e' Heq]. destruct e'; simpl in Heq; try discriminate.
      inversion Heq; subst. split; eexists; reflexivity.
    + intros [[A' ->] [b' ->]]. exists (VLam A' b'). reflexivity.
  - rewrite <- IHA, <- IHB. split.
    + intros [e' Heq]. destruct e'; simpl in Heq; try discriminate.
      inversion Heq; subst. split; eexists; reflexivity.
    + intros [[A' ->] [B' ->]]. exists (VForallE A' B'). reflexivity.
Qed.

Theorem VSkips_of_vinstL ls n k e :
  VSkips n k (vinstL ls e) -> VSkips n k e.
Proof.
  rewrite !vskips_iff. revert k.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros k; simpl; try tauto.
  - intros [H1 H2]; split; [apply IHf | apply IHa]; assumption.
  - intros [H1 H2]; split; [apply IHA | apply IHb]; assumption.
  - intros [H1 H2]; split; [apply IHA | apply IHB]; assumption.
Qed.

Theorem of_vliftN_eq_vliftN n1 n2 k1 k2 e1 e2 :
  vliftN n1 (k1 + n2 + k2) e1 = vliftN n2 k2 e2 ->
  exists e', e1 = vliftN n2 k2 e' /\ e2 = vliftN n1 (k1 + k2) e'.
Proof.
  intros H.
  assert (Hsk : VSkips n2 k2 (vliftN n1 (k1 + n2 + k2) e1)).
  { rewrite H. apply VSkips_vliftN. }
  apply VSkips_of_vliftN_hi in Hsk; [|lia].
  apply vskips_iff_exists in Hsk as [e' ->].
  exists e'. split; [reflexivity |].
  apply (proj1 (vliftN_inj n2 k2 _ _)).
  rewrite <- H.
  replace (k1 + n2 + k2) with (n2 + (k1 + k2)) by lia.
  apply vliftN_comm. lia.
Qed.

Theorem of_vliftN_eq_vinstL ls n k e1 e2 :
  vliftN n k e1 = vinstL ls e2 ->
  exists e', e1 = vinstL ls e' /\ e2 = vliftN n k e'.
Proof.
  intros H.
  assert (Hsk : VSkips n k (vinstL ls e2)).
  { rewrite <- H. apply VSkips_vliftN. }
  apply VSkips_of_vinstL in Hsk.
  apply vskips_iff_exists in Hsk as [e' ->].
  exists e'. split; [|reflexivity].
  apply (proj1 (vliftN_inj n k _ _)).
  rewrite H, vinstL_vliftN. reflexivity.
Qed.

Theorem vinst_vinst_lo e1 e2 e3 k j :
  vinst (vinst e1 e2 (S (k + j))) e3 j =
  vinst (vinst e1 (vliftN 1 k e3) j) e2 (k + j).
Proof.
  revert j.
  induction e1 as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros j; simpl; try reflexivity.
  - unfold vinstVar.
    destruct (i <? S (k + j)) eqn:H1.
    + pose proof (proj1 (Nat.ltb_lt _ _) H1) as H1'.
      destruct (i <? j) eqn:H2.
      * pose proof (proj1 (Nat.ltb_lt _ _) H2) as H2'.
        simpl. unfold vinstVar.
        assert (H3 : (i <? k + j) = true) by (apply Nat.ltb_lt; lia).
        rewrite H2, H3. reflexivity.
      * pose proof (proj1 (Nat.ltb_ge _ _) H2) as H2'.
        destruct (Nat.eqb i j) eqn:H3.
        -- apply Nat.eqb_eq in H3. subst i.
           simpl. unfold vinstVar.
           rewrite Nat.ltb_irrefl, Nat.eqb_refl.
           pose proof (@vliftN_comm e3 1 j k 0 ltac:(lia)) as Hc.
           replace (j + k) with (k + j) in Hc by lia.
           rewrite <- Hc.
           symmetry. apply vinst_vliftN_one.
        -- pose proof (proj1 (Nat.eqb_neq _ _) H3) as H3'.
           simpl. unfold vinstVar.
           assert (H4 : (pred i <? k + j) = true) by (apply Nat.ltb_lt; lia).
           rewrite H2, H3, H4. reflexivity.
    + pose proof (proj1 (Nat.ltb_ge _ _) H1) as H1'.
      destruct (Nat.eqb i (S (k + j))) eqn:H2.
      * apply Nat.eqb_eq in H2. subst i.
        assert (H3 : (S (k + j) <? j) = false) by (apply Nat.ltb_ge; lia).
        assert (H4 : (S (k + j) =? j) = false) by (apply Nat.eqb_neq; lia).
        rewrite H3, H4. simpl. unfold vinstVar.
        rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        pose proof (@vliftN_vliftN e2 (k + j) 1 0 j ltac:(lia) ltac:(lia)) as Hl.
        replace (1 + (k + j)) with (S (k + j)) in Hl by lia.
        rewrite <- Hl. apply vinst_vliftN_one.
      * pose proof (proj1 (Nat.eqb_neq _ _) H2) as H2'.
        assert (H3 : (pred i <? j) = false) by (apply Nat.ltb_ge; lia).
        assert (H4 : (pred i =? j) = false) by (apply Nat.eqb_neq; lia).
        assert (H5 : (i <? j) = false) by (apply Nat.ltb_ge; lia).
        assert (H6 : (i =? j) = false) by (apply Nat.eqb_neq; lia).
        assert (H7 : (pred i <? k + j) = false) by (apply Nat.ltb_ge; lia).
        assert (H8 : (pred i =? k + j) = false) by (apply Nat.eqb_neq; lia).
        rewrite H5, H6. simpl. unfold vinstVar.
        rewrite H3, H4, H7, H8. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA.
    replace (S (k + j)) with (k + S j) by lia.
    rewrite (IHb (S j)). reflexivity.
  - rewrite IHA.
    replace (S (k + j)) with (k + S j) by lia.
    rewrite (IHB (S j)). reflexivity.
Qed.

(* ========================================================================= *)
(* 2. Structured Renamings VLift (VExpr.lean: inductive Lift)                *)
(* ========================================================================= *)

Inductive VLift : Type :=
| VLRefl : VLift
| VLSkip : VLift -> VLift
| VLCons : VLift -> VLift.

Fixpoint vlift_skipN (l : VLift) (n : nat) : VLift :=
  match n with
  | 0 => l
  | S n' => VLSkip (vlift_skipN l n')
  end.

Lemma vlift_skipN_one l : vlift_skipN l 1 = VLSkip l.
Proof. reflexivity. Qed.

Lemma vlift_skipN_skipN l n k :
  vlift_skipN (vlift_skipN l n) k = vlift_skipN l (n + k).
Proof.
  induction k as [|k IH]; simpl.
  - replace (n + 0) with n by lia. reflexivity.
  - replace (n + S k) with (S (n + k)) by lia. simpl. f_equal. exact IH.
Qed.

Fixpoint vlift_consN (l : VLift) (k : nat) : VLift :=
  match k with
  | 0 => l
  | S k' => VLCons (vlift_consN l k')
  end.

Lemma vlift_consN_consN l a b :
  vlift_consN (vlift_consN l a) b = vlift_consN l (a + b).
Proof.
  induction b as [|b IH]; simpl.
  - replace (a + 0) with a by lia. reflexivity.
  - replace (a + S b) with (S (a + b)) by lia. simpl. f_equal. exact IH.
Qed.

Fixpoint vlift_comp (l1 l2 : VLift) : VLift :=
  match l2 with
  | VLRefl => l1
  | VLSkip l2' => VLSkip (vlift_comp l1 l2')
  | VLCons l2' =>
      match l1 with
      | VLRefl => VLCons l2'
      | VLSkip l1' => VLSkip (vlift_comp l1' l2')
      | VLCons l1' => VLCons (vlift_comp l1' l2')
      end
  end.

Lemma vlift_refl_comp l : vlift_comp VLRefl l = l.
Proof.
  induction l as [|l IH|l IH]; simpl; try congruence.
Qed.

Lemma vlift_comp_refl l : vlift_comp l VLRefl = l.
Proof. reflexivity. Qed.

Lemma vlift_consN_comp l1 l2 n :
  vlift_consN (vlift_comp l1 l2) n =
  vlift_comp (vlift_consN l1 n) (vlift_consN l2 n).
Proof.
  induction n as [|n IH]; simpl; [reflexivity | congruence].
Qed.

Fixpoint vlift_dom (l : VLift) : nat :=
  match l with
  | VLRefl => 0
  | VLSkip l' => vlift_dom l'
  | VLCons l' => vlift_dom l' + 1
  end.

Fixpoint vlift_size (l : VLift) : nat :=
  match l with
  | VLRefl => 0
  | VLSkip l' => vlift_size l' + 1
  | VLCons l' => vlift_size l' + 1
  end.

Fixpoint vlift_depth (l : VLift) : nat :=
  match l with
  | VLRefl => 0
  | VLSkip l' => vlift_depth l' + 1
  | VLCons l' => vlift_depth l'
  end.

Lemma vlift_dom_add_depth l :
  vlift_dom l + vlift_depth l = vlift_size l.
Proof.
  induction l; simpl; lia.
Qed.

Lemma vlift_depth_comp l1 l2 :
  vlift_depth (vlift_comp l1 l2) = vlift_depth l1 + vlift_depth l2.
Proof.
  revert l1.
  induction l2 as [|l2 IH|l2 IH]; intros l1; simpl.
  - lia.
  - rewrite IH. lia.
  - destruct l1 as [|l1|l1]; simpl; rewrite ?IH; lia.
Qed.

Lemma vlift_depth_consN l n :
  vlift_depth (vlift_consN l n) = vlift_depth l.
Proof.
  induction n as [|n IH]; simpl; congruence.
Qed.

Lemma vlift_depth_skipN l n :
  vlift_depth (vlift_skipN l n) = vlift_depth l + n.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Lemma vlift_consN_skip_eq l k :
  vlift_consN (VLSkip l) k =
  vlift_comp (vlift_consN l k) (vlift_consN (VLSkip VLRefl) k).
Proof.
  rewrite <- vlift_consN_comp. reflexivity.
Qed.

Lemma vlift_depth_succ l n :
  vlift_depth l = S n ->
  exists l' k, vlift_depth l' = n /\ l = vlift_consN (VLSkip l') k.
Proof.
  induction l as [|l IH|l IH]; simpl; intros H.
  - discriminate.
  - exists l, 0. simpl. split; [lia | reflexivity].
  - destruct (IH H) as [l' [k [Hd ->]]].
    exists l', (S k). simpl. split; [exact Hd | reflexivity].
Qed.

Lemma vlift_depth_succ' l n :
  vlift_depth l = S n ->
  exists l' k, vlift_depth l' = n /\
    l = vlift_comp l' (vlift_consN (VLSkip VLRefl) k).
Proof.
  intros H. destruct (vlift_depth_succ H) as [l' [k [Hd ->]]].
  exists (vlift_consN l' k), k. split.
  - rewrite vlift_depth_consN. exact Hd.
  - apply vlift_consN_skip_eq.
Qed.

Lemma vlift_comp_skipN l1 l2 k :
  vlift_comp l1 (vlift_skipN l2 k) = vlift_skipN (vlift_comp l1 l2) k.
Proof.
  induction k as [|k IH]; simpl; congruence.
Qed.

Lemma vlift_skipN_comp_consN l1 l2 k :
  vlift_comp (vlift_skipN l1 k) (vlift_consN l2 k) =
  vlift_skipN (vlift_comp l1 l2) k.
Proof.
  induction k as [|k IH]; simpl; congruence.
Qed.

Fixpoint vlift_var (l : VLift) (n : nat) : nat :=
  match l, n with
  | VLRefl, i => i
  | VLSkip l', i => S (vlift_var l' i)
  | VLCons _, 0 => 0
  | VLCons l', S i => S (vlift_var l' i)
  end.

Theorem vlift_var_comp l1 l2 n :
  vlift_var (vlift_comp l1 l2) n = vlift_var l2 (vlift_var l1 n).
Proof.
  revert l1 n.
  induction l2 as [|l2 IH|l2 IH]; intros l1 n; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - destruct l1 as [|l1|l1]; simpl.
    + destruct n; reflexivity.
    + rewrite IH. reflexivity.
    + destruct n as [|n]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Theorem vlift_var_skipN l n i :
  vlift_var (vlift_skipN l n) i = n + vlift_var l i.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Theorem vlift_var_consN_skipN n k i :
  vlift_var (vlift_consN (vlift_skipN VLRefl n) k) i = vliftVar n i k.
Proof.
  revert i.
  induction k as [|k IH]; intros i.
  - simpl. rewrite vlift_var_skipN. simpl. unfold vliftVar. simpl. reflexivity.
  - destruct i as [|i]; simpl.
    + reflexivity.
    + rewrite IH. unfold vliftVar.
      replace (S i <? S k) with (i <? k) by reflexivity.
      destruct (i <? k); lia.
Qed.

Theorem vlift_var_depth_zero l n :
  vlift_depth l = 0 -> vlift_var l n = n.
Proof.
  revert n.
  induction l as [|l IH|l IH]; intros n Hd; simpl in *.
  - reflexivity.
  - lia.
  - destruct n as [|n]; [reflexivity | f_equal; apply IH; exact Hd].
Qed.

Theorem le_vlift_var l n :
  n <= vlift_var l n.
Proof.
  revert n.
  induction l as [|l IH|l IH]; intros n; simpl.
  - lia.
  - specialize (IH n). lia.
  - destruct n as [|n]; [lia | specialize (IH n); lia].
Qed.

Fixpoint vlift_inter (l1 l2 : VLift) : VLift :=
  match l1, l2 with
  | VLRefl, l => l
  | l, VLRefl => l
  | VLSkip a, VLSkip b | VLSkip a, VLCons b | VLCons a, VLSkip b =>
      VLSkip (vlift_inter a b)
  | VLCons a, VLCons b => VLCons (vlift_inter a b)
  end.

Lemma vlift_inter_self l : vlift_inter l l = l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma vlift_inter_comm l1 l2 : vlift_inter l1 l2 = vlift_inter l2 l1.
Proof.
  revert l2. induction l1; destruct l2; simpl; congruence.
Qed.

Fixpoint vlift_diff (l1 l2 : VLift) : VLift :=
  match l1, l2 with
  | VLRefl, _ => VLRefl
  | l, VLRefl => l
  | VLSkip a, VLSkip b | VLCons a, VLSkip b => vlift_diff a b
  | VLSkip a, VLCons b => VLSkip (vlift_diff a b)
  | VLCons a, VLCons b => VLCons (vlift_diff a b)
  end.

Lemma vlift_diff_comp l1 l2 :
  vlift_comp (vlift_diff l1 l2) l2 = vlift_inter l1 l2.
Proof.
  revert l2. induction l1; destruct l2; simpl; rewrite ?vlift_refl_comp; congruence.
Qed.

Fixpoint vlift_fixes (k : nat) (l : VLift) : Prop :=
  match k, l with
  | 0, _ => True
  | _, VLRefl => True
  | S _, VLSkip _ => False
  | S k', VLCons l' => vlift_fixes k' l'
  end.

Lemma vlift_fixes_zero l : vlift_fixes 0 l.
Proof. exact I. Qed.

Lemma vlift_fixes_var_eq k l i :
  vlift_fixes k l -> i < k -> vlift_var l i = i.
Proof.
  revert k i.
  induction l as [|l IH|l IH]; intros k i Hf Hlt; simpl.
  - reflexivity.
  - destruct k; [lia | contradiction].
  - destruct k as [|k]; [lia |].
    destruct i as [|i]; [reflexivity |].
    f_equal. apply (IH k i Hf). lia.
Qed.

(* Expression lifting along VLift *)

Fixpoint vlift' (l : VLift) (e : VExpr) : VExpr :=
  match e with
  | VBVar i => VBVar (vlift_var l i)
  | VSort u => VSort u
  | VConst c us => VConst c us
  | VApp f a => VApp (vlift' l f) (vlift' l a)
  | VLam A b => VLam (vlift' l A) (vlift' (VLCons l) b)
  | VForallE A B => VForallE (vlift' l A) (vlift' (VLCons l) B)
  end.

Theorem vlift'_consN_skipN n k e :
  vlift' (vlift_consN (vlift_skipN VLRefl n) k) e = vliftN n k e.
Proof.
  revert k.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros k; simpl; try reflexivity.
  - rewrite vlift_var_consN_skipN. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, <- (IHb (S k)). reflexivity.
  - rewrite IHA, <- (IHB (S k)). reflexivity.
Qed.

Theorem vlift'_comp l1 l2 e :
  vlift' (vlift_comp l1 l2) e = vlift' l2 (vlift' l1 e).
Proof.
  revert l1 l2.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros l1 l2; simpl; try reflexivity.
  - rewrite vlift_var_comp. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, <- (IHb (VLCons l1) (VLCons l2)). reflexivity.
  - rewrite IHA, <- (IHB (VLCons l1) (VLCons l2)). reflexivity.
Qed.

Theorem vlift'_depth_zero l e :
  vlift_depth l = 0 -> vlift' l e = e.
Proof.
  revert l.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros l Hd; simpl; try reflexivity.
  - rewrite vlift_var_depth_zero by exact Hd. reflexivity.
  - rewrite IHf, IHa by exact Hd. reflexivity.
  - rewrite IHA by exact Hd. rewrite (IHb (VLCons l)) by exact Hd. reflexivity.
  - rewrite IHA by exact Hd. rewrite (IHB (VLCons l)) by exact Hd. reflexivity.
Qed.

Lemma vlift'_refl e : vlift' VLRefl e = e.
Proof. apply vlift'_depth_zero. reflexivity. Qed.

Lemma vlift_eq_vlift' e : vlift e = vlift' (VLSkip VLRefl) e.
Proof.
  unfold vlift. rewrite <- vlift'_consN_skipN. reflexivity.
Qed.

Lemma vinstL_vlift' ks rho e :
  vinstL ks (vlift' rho e) = vlift' rho (vinstL ks e).
Proof.
  revert rho.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros rho; simpl; try congruence.
Qed.

Theorem vclosedN_vlift'_eq k rho e :
  vclosedN k e -> vlift_fixes k rho -> vlift' rho e = e.
Proof.
  revert k rho.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros k rho Hc Hf; simpl in *; try reflexivity.
  - rewrite (vlift_fixes_var_eq Hf Hc). reflexivity.
  - destruct Hc as [H1 H2]. rewrite (IHf k rho H1 Hf), (IHa k rho H2 Hf). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHA k rho H1 Hf), (IHb (S k) (VLCons rho) H2 Hf). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHA k rho H1 Hf), (IHB (S k) (VLCons rho) H2 Hf). reflexivity.
Qed.

(* ========================================================================= *)
(* 3. Simultaneous Substitutions VSubst := nat -> VExpr (VExpr.lean)         *)
(* ========================================================================= *)

Definition VSubst : Type := nat -> VExpr.

(* Pointwise equality on substitutions (eliminates any need for funext!). *)
Definition vsubst_eq (s1 s2 : VSubst) : Prop :=
  forall i, s1 i = s2 i.

Lemma vsubst_eq_refl s : vsubst_eq s s.
Proof. intros i. reflexivity. Qed.

Lemma vsubst_eq_symm s1 s2 : vsubst_eq s1 s2 -> vsubst_eq s2 s1.
Proof. intros H i. symmetry. apply H. Qed.

Lemma vsubst_eq_trans s1 s2 s3 :
  vsubst_eq s1 s2 -> vsubst_eq s2 s3 -> vsubst_eq s1 s3.
Proof. intros H1 H2 i. transitivity (s2 i); [apply H1 | apply H2]. Qed.

Definition vsubst_id : VSubst := VBVar.

Definition vsubst_head (s : VSubst) : VExpr := s 0.

Definition vsubst_tail (s : VSubst) : VSubst := fun n => s (S n).

Definition vsubst_cons (s : VSubst) (e : VExpr) : VSubst :=
  fun i => match i with
           | 0 => e
           | S j => s j
           end.

Definition vsubst_one (e : VExpr) : VSubst := vsubst_cons vsubst_id e.

Definition vsubst_lift (s : VSubst) : VSubst :=
  fun i => match i with
           | 0 => VBVar 0
           | S j => vlift (s j)
           end.

Fixpoint vsubst_liftN (k : nat) (s : VSubst) : VSubst :=
  match k with
  | 0 => s
  | S k' => vsubst_lift (vsubst_liftN k' s)
  end.

Fixpoint vsubst (s : VSubst) (e : VExpr) : VExpr :=
  match e with
  | VBVar i => s i
  | VSort u => VSort u
  | VConst c us => VConst c us
  | VApp f a => VApp (vsubst s f) (vsubst s a)
  | VLam A b => VLam (vsubst s A) (vsubst (vsubst_lift s) b)
  | VForallE A B => VForallE (vsubst s A) (vsubst (vsubst_lift s) B)
  end.

Lemma vsubst_lift_ext s1 s2 :
  vsubst_eq s1 s2 -> vsubst_eq (vsubst_lift s1) (vsubst_lift s2).
Proof.
  intros H [|i]; simpl; [reflexivity | f_equal; apply H].
Qed.

Theorem vsubst_ext s1 s2 e :
  vsubst_eq s1 s2 -> vsubst s1 e = vsubst s2 e.
Proof.
  revert s1 s2.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros s1 s2 Heq; simpl; try reflexivity.
  - apply Heq.
  - rewrite (IHf s1 s2 Heq), (IHa s1 s2 Heq). reflexivity.
  - rewrite (IHA s1 s2 Heq), (IHb _ _ (vsubst_lift_ext Heq)). reflexivity.
  - rewrite (IHA s1 s2 Heq), (IHB _ _ (vsubst_lift_ext Heq)). reflexivity.
Qed.

Definition vsubst_lift_r (s : VSubst) (rho : VLift) : VSubst :=
  fun x => vlift' rho (s x).

Definition vsubst_lift_l (rho : VLift) (s : VSubst) : VSubst :=
  fun x => s (vlift_var rho x).

Lemma vsubst_lift_l_lift s rho :
  vsubst_eq (vsubst_lift (vsubst_lift_l rho s))
            (vsubst_lift_l (VLCons rho) (vsubst_lift s)).
Proof.
  intros [|i]; reflexivity.
Qed.

Lemma vlift'_cons_vlift rho e :
  vlift' (VLCons rho) (vlift e) = vlift (vlift' rho e).
Proof.
  rewrite !vlift_eq_vlift', <- !vlift'_comp. simpl.
  rewrite vlift_refl_comp. reflexivity.
Qed.

Lemma vsubst_lift_r_lift s rho :
  vsubst_eq (vsubst_lift (vsubst_lift_r s rho))
            (vsubst_lift_r (vsubst_lift s) (VLCons rho)).
Proof.
  intros [|i]; unfold vsubst_lift, vsubst_lift_r; simpl.
  - reflexivity.
  - symmetry. apply vlift'_cons_vlift.
Qed.

Theorem vsubst_vlift' rho s e :
  vsubst s (vlift' rho e) = vsubst (vsubst_lift_l rho s) e.
Proof.
  revert rho s.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros rho s; simpl; try reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_lift_l_lift.
  - rewrite IHA, IHB. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_lift_l_lift.
Qed.

Theorem vlift'_vsubst rho s e :
  vlift' rho (vsubst s e) = vsubst (vsubst_lift_r s rho) e.
Proof.
  revert rho s.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros rho s; simpl; try reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_lift_r_lift.
  - rewrite IHA, IHB. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_lift_r_lift.
Qed.

Definition vsubst_comp (s1 s2 : VSubst) : VSubst :=
  fun x => vsubst s2 (s1 x).

Lemma vsubst_comp_lift s1 s2 :
  vsubst_eq (vsubst_lift (vsubst_comp s1 s2))
            (vsubst_comp (vsubst_lift s1) (vsubst_lift s2)).
Proof.
  intros [|i]; unfold vsubst_comp, vsubst_lift; simpl.
  - reflexivity.
  - rewrite !vlift_eq_vlift', vlift'_vsubst, vsubst_vlift'.
    apply vsubst_ext. intros j.
    unfold vsubst_lift_r, vsubst_lift_l, vsubst_lift; simpl.
    rewrite <- vlift_eq_vlift'. reflexivity.
Qed.

Theorem vsubst_comp_eq s1 s2 e :
  vsubst s2 (vsubst s1 e) = vsubst (vsubst_comp s1 s2) e.
Proof.
  revert s1 s2.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros s1 s2; simpl; try reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_comp_lift.
  - rewrite IHA, IHB. f_equal. apply vsubst_ext. apply vsubst_eq_symm. apply vsubst_comp_lift.
Qed.

Theorem vliftN_vsubst n k s e :
  vsubst s (vliftN n k e) =
  vsubst (vsubst_lift_l (vlift_consN (vlift_skipN VLRefl n) k) s) e.
Proof.
  rewrite <- vlift'_consN_skipN. apply vsubst_vlift'.
Qed.

Lemma vsubst_id_lift : vsubst_eq (vsubst_lift vsubst_id) vsubst_id.
Proof.
  intros [|i]; reflexivity.
Qed.

Theorem vsubst_id_eq e : vsubst vsubst_id e = e.
Proof.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    simpl; try reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, (vsubst_ext b vsubst_id_lift), IHb. reflexivity.
  - rewrite IHA, (vsubst_ext B vsubst_id_lift), IHB. reflexivity.
Qed.

Lemma vsubst_cons_head s e : vsubst_head (vsubst_cons s e) = e.
Proof. reflexivity. Qed.

Lemma vsubst_cons_tail s e : vsubst_eq (vsubst_tail (vsubst_cons s e)) s.
Proof. intros i. reflexivity. Qed.

Theorem vlift_vsubst s e :
  vsubst s (vlift e) = vsubst (vsubst_tail s) e.
Proof.
  rewrite vlift_eq_vlift', vsubst_vlift'. reflexivity.
Qed.

(* Left-inverse substitution for VLift, yielding injectivity of vlift' *)

Fixpoint vlift_inv (rho : VLift) : VSubst :=
  match rho with
  | VLRefl => vsubst_id
  | VLSkip rho' => vsubst_cons (vlift_inv rho') vdefault
  | VLCons rho' => vsubst_lift (vlift_inv rho')
  end.

Lemma vlift_l_inv_eq rho :
  vsubst_eq (vsubst_lift_l rho (vlift_inv rho)) vsubst_id.
Proof.
  induction rho as [|rho IH|rho IH]; intros i; unfold vsubst_lift_l in *; simpl.
  - reflexivity.
  - apply IH.
  - destruct i as [|i]; simpl; [reflexivity |].
    rewrite IH. reflexivity.
Qed.

Theorem vlift'_inj rho e1 e2 :
  vlift' rho e1 = vlift' rho e2 <-> e1 = e2.
Proof.
  split; [|intros ->; reflexivity].
  intros H.
  pose proof (f_equal (vsubst (vlift_inv rho)) H) as Hs.
  rewrite !vsubst_vlift' in Hs.
  rewrite (vsubst_ext e1 (vlift_l_inv_eq rho)),
          (vsubst_ext e2 (vlift_l_inv_eq rho)),
          !vsubst_id_eq in Hs.
  exact Hs.
Qed.

(* Commutation between vsubst and vinst / vlift / vclosedN / vinstL *)

Lemma vinstVar_eq_vsubst_liftN a k i :
  vinstVar i a k = vsubst_liftN k (vsubst_one a) i.
Proof.
  revert i.
  induction k as [|k IH]; intros i; simpl.
  - unfold vinstVar, vsubst_one, vsubst_cons, vsubst_id.
    destruct i as [|i]; simpl.
    + apply vliftN_zero.
    + reflexivity.
  - destruct i as [|i]; simpl.
    + reflexivity.
    + rewrite vinstVar_succ, IH. reflexivity.
Qed.

Theorem vinstN_eq_vsubst e a k :
  vinst e a k = vsubst (vsubst_liftN k (vsubst_one a)) e.
Proof.
  revert k.
  induction e as [i|u|c us|f IHf a' IHa|A IHA b IHb|A IHA B IHB];
    intros k; simpl; try reflexivity.
  - apply vinstVar_eq_vsubst_liftN.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, (IHb (S k)). reflexivity.
  - rewrite IHA, (IHB (S k)). reflexivity.
Qed.

Theorem vinst_eq_vsubst e a :
  vinst0 e a = vsubst (vsubst_one a) e.
Proof.
  apply (vinstN_eq_vsubst e a 0).
Qed.

Definition vsubst_fixes (s : VSubst) (n : nat) : Prop :=
  forall i, i < n -> s i = VBVar i.

Lemma vsubst_fixes_zero s : vsubst_fixes s 0.
Proof. intros i Hi; lia. Qed.

Lemma vsubst_fixes_lift s n :
  vsubst_fixes s n -> vsubst_fixes (vsubst_lift s) (S n).
Proof.
  intros Hf [|i] Hi; simpl.
  - reflexivity.
  - rewrite Hf by lia. reflexivity.
Qed.

Theorem vclosedN_vsubst_eq k s e :
  vclosedN k e -> vsubst_fixes s k -> vsubst s e = e.
Proof.
  revert k s.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros k s Hc Hf; simpl in *; try reflexivity.
  - apply Hf. exact Hc.
  - destruct Hc as [H1 H2]. rewrite (IHf k s H1 Hf), (IHa k s H2 Hf). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHA k s H1 Hf), (IHb (S k) _ H2 (vsubst_fixes_lift Hf)). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHA k s H1 Hf), (IHB (S k) _ H2 (vsubst_fixes_lift Hf)). reflexivity.
Qed.

Corollary vclosed_vsubst_eq s e :
  vclosed e -> vsubst s e = e.
Proof.
  intros Hc. apply (vclosedN_vsubst_eq Hc (vsubst_fixes_zero s)).
Qed.

Theorem vlift_vsubst_cons s t e :
  vsubst (vsubst_cons s t) (vlift e) = vsubst s e.
Proof.
  rewrite vlift_vsubst. apply vsubst_ext. apply vsubst_cons_tail.
Qed.

Theorem vlift_vsubst_lift s e :
  vsubst (vsubst_lift s) (vlift e) = vlift (vsubst s e).
Proof.
  rewrite vlift_eq_vlift', vsubst_vlift', vlift_eq_vlift', vlift'_vsubst.
  apply vsubst_ext. intros x.
  unfold vsubst_lift_l, vsubst_lift_r, vsubst_lift; simpl.
  rewrite vlift_eq_vlift'. reflexivity.
Qed.

Theorem vsubst_vinst s e a :
  vsubst s (vinst0 e a) = vinst0 (vsubst (vsubst_lift s) e) (vsubst s a).
Proof.
  rewrite !vinst_eq_vsubst, !vsubst_comp_eq.
  apply vsubst_ext. intros [|i]; unfold vsubst_comp, vsubst_one, vsubst_cons, vsubst_lift, vsubst_id; simpl.
  - reflexivity.
  - rewrite vlift_vsubst, vsubst_id_eq. reflexivity.
Qed.

Theorem vinst_vlift_cons s x e :
  vinst0 (vsubst (vsubst_lift s) e) x = vsubst (vsubst_cons s x) e.
Proof.
  rewrite vinst_eq_vsubst, vsubst_comp_eq.
  apply vsubst_ext. intros [|i]; unfold vsubst_comp, vsubst_lift, vsubst_one, vsubst_cons; simpl.
  - reflexivity.
  - rewrite vlift_vsubst, vsubst_id_eq. reflexivity.
Qed.

Theorem vlift'_vinst_hi rho e1 e2 :
  vlift' rho (vinst0 e1 e2) = vinst0 (vlift' (VLCons rho) e1) (vlift' rho e2).
Proof.
  rewrite !vinst_eq_vsubst, vlift'_vsubst, vsubst_vlift'.
  apply vsubst_ext. intros [|i];
    unfold vsubst_lift_r, vsubst_lift_l, vsubst_one, vsubst_cons, vsubst_id; simpl; reflexivity.
Qed.

Theorem vinstL_vsubst ks s e :
  vinstL ks (vsubst s e) = vsubst (fun i => vinstL ks (s i)) (vinstL ks e).
Proof.
  revert s.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros s; simpl; try reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHA, IHb. f_equal. apply vsubst_ext.
    intros [|j]; simpl; [reflexivity | unfold vlift; apply vinstL_vliftN].
  - rewrite IHA, IHB. f_equal. apply vsubst_ext.
    intros [|j]; simpl; [reflexivity | unfold vlift; apply vinstL_vliftN].
Qed.

(* ========================================================================= *)
(* 4. Structured Context Weakening VCtxLift' (Typing/Lemmas.lean)            *)
(* ========================================================================= *)

Inductive VCtxLift' : VLift -> list VExpr -> list VExpr -> Prop :=
| VCtxLift'_refl : forall G, VCtxLift' VLRefl G G
| VCtxLift'_skip : forall l G G' A,
    VCtxLift' l G G' ->
    VCtxLift' (VLSkip l) G (A :: G')
| VCtxLift'_cons : forall l G G' A,
    VCtxLift' l G G' ->
    VCtxLift' (VLCons l) (A :: G) (vlift' l A :: G').

Theorem VCtxLiftN_iff_VCtxLift' n k G G' :
  VCtxLiftN n k G G' <-> VCtxLift' (vlift_consN (vlift_skipN VLRefl n) k) G G'.
Proof.
  split.
  - intros H. induction H as [As G Hlen | k G G' A H IH].
    + subst n. induction As as [|B As IHAs]; simpl.
      * constructor.
      * constructor. exact IHAs.
    + simpl. rewrite <- vlift'_consN_skipN. constructor. exact IH.
  - revert G G'. induction k as [|k IH]; intros G G' H; simpl in H.
    + assert (Hex : exists As, G' = As ++ G /\ List.length As = n).
      { revert G' H. induction n as [|n IHn]; intros G' H; simpl in H.
        - inversion H; subst. exists []. split; reflexivity.
        - inversion H as [|l0 G0 G1 A H0 Heq1 Heq2 Heq3|]; subst.
          destruct (IHn G1 H0) as [As [-> <-]].
          exists (A :: As). split; reflexivity. }
      destruct Hex as [As [-> Hlen]]. constructor. exact Hlen.
    + inversion H as [| |l0 G0 G1 A H0 Heq1 Heq2 Heq3]; subst.
      rewrite vlift'_consN_skipN. constructor. apply IH. exact H0.
Qed.

Theorem VCtxLift'_comp l1 l2 G1 G2 G3 :
  VCtxLift' l1 G1 G2 ->
  VCtxLift' l2 G2 G3 ->
  VCtxLift' (vlift_comp l1 l2) G1 G3.
Proof.
  intros H1 H2. revert l1 G1 H1.
  induction H2 as [G2 | l2 G2 G3 A H2 IH | l2 G2 G3 A H2 IH]; intros l1 G1 H1; simpl.
  - exact H1.
  - constructor. apply IH. exact H1.
  - inversion H1 as [G0 Heq1 Heq2 | l0 G0 G2' B H0 Heq1 Heq2 | l0 G0 G2' B H0 Heq1 Heq2]; subst.
    + constructor. exact H2.
    + constructor. apply IH. exact H0.
    + rewrite <- vlift'_comp. constructor. apply IH. exact H0.
Qed.

Theorem VCtxLift'_of_cons_skip l k G1 G3 :
  VCtxLift' (vlift_consN (VLSkip l) k) G1 G3 ->
  exists G2, VCtxLift' (vlift_consN l k) G1 G2 /\ VCtxLiftN 1 k G2 G3.
Proof.
  revert G1 G3.
  induction k as [|k IH]; intros G1 G3 H; simpl in H.
  - inversion H as [|l0 G0 G2 A H0 Heq1 Heq2 Heq3|]; subst.
    exists G2. split; [exact H0 | apply VCtxLiftN_one].
  - inversion H as [| |l0 G0 G3' A H0 Heq1 Heq2 Heq3]; subst.
    destruct (IH G0 G3' H0) as [G2 [H1 H2]].
    exists (vlift' (vlift_consN l k) A :: G2). split.
    + simpl. constructor. exact H1.
    + rewrite vlift_consN_skip_eq, vlift'_comp.
      replace (vlift' (vlift_consN (VLSkip VLRefl) k) (vlift' (vlift_consN l k) A))
        with (vliftN 1 k (vlift' (vlift_consN l k) A)).
      2: { symmetry. exact (vlift'_consN_skipN 1 k _). }
      constructor. exact H2.
Qed.

Theorem VCtxLift'_depth_zero l G G' :
  vlift_depth l = 0 -> VCtxLift' l G G' -> G = G'.
Proof.
  intros Hd H. induction H as [G | l G G' A H IH | l G G' A H IH]; simpl in Hd.
  - reflexivity.
  - lia.
  - rewrite vlift'_depth_zero by exact Hd. f_equal. apply IH. exact Hd.
Qed.

Theorem VLookup_weak' rho G G' i A :
  VCtxLift' rho G G' ->
  VLookup G i A ->
  VLookup G' (vlift_var rho i) (vlift' rho A).
Proof.
  intros W. revert i A.
  induction W as [G | rho G G' B W IH | rho G G' B W IH]; intros i A Hlk; simpl.
  - rewrite vlift'_refl. exact Hlk.
  - pose proof (VLookupSucc B (IH i A Hlk)) as Hs.
    rewrite vlift_eq_vlift', <- vlift'_comp in Hs. exact Hs.
  - inversion Hlk as [A0 G0 Heq1 Heq2 | A0 G0 j B0 Hj Heq1 Heq2]; subst; simpl.
    + rewrite vlift'_cons_vlift. constructor.
    + rewrite vlift'_cons_vlift. constructor. apply IH. exact Hj.
Qed.

Theorem VLookup_weakU_inv rho G G' i A' :
  VCtxLift' rho G G' ->
  VLookup G' (vlift_var rho i) A' ->
  exists A, A' = vlift' rho A /\ VLookup G i A.
Proof.
  intros W. revert i A'.
  induction W as [G | rho G G' B W IH | rho G G' B W IH]; intros i A' Hlk; simpl in Hlk.
  - exists A'. rewrite vlift'_refl. auto.
  - inversion Hlk as [|B0 G0 j C Hj Heq1 Heq2]; subst.
    destruct (IH i C Hj) as [A [-> HA]].
    exists A. split; [|exact HA].
    rewrite vlift_eq_vlift', <- vlift'_comp. reflexivity.
  - destruct i as [|i]; simpl in Hlk.
    + inversion Hlk; subst.
      exists (vlift B). split; [symmetry; apply vlift'_cons_vlift | constructor].
    + inversion Hlk as [|B0 G0 j C Hj Heq1 Heq2]; subst.
      destruct (IH i C Hj) as [A [-> HA]].
      exists (vlift A). split; [symmetry; apply vlift'_cons_vlift | constructor; exact HA].
Qed.

Theorem VLookup_weak'_iff rho G G' i A :
  VCtxLift' rho G G' ->
  (VLookup G' (vlift_var rho i) (vlift' rho A) <-> VLookup G i A).
Proof.
  intros W. split.
  - intros H. destruct (VLookup_weakU_inv W H) as [A0 [Heq Hlk]].
    apply vlift'_inj in Heq. subst A0. exact Hlk.
  - apply VLookup_weak'. exact W.
Qed.

Theorem VLookup_weakN_iff n k G G' i A :
  VCtxLiftN n k G G' ->
  (VLookup G' (vliftVar n i k) (vliftN n k A) <-> VLookup G i A).
Proof.
  intros W.
  rewrite <- vlift_var_consN_skipN, <- vlift'_consN_skipN.
  apply VLookup_weak'_iff. apply VCtxLiftN_iff_VCtxLift'. exact W.
Qed.

Theorem VIsDefEq_weak' env U rho G G' e1 e2 A :
  VEnvClosed env ->
  VCtxLift' rho G G' ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U G' (vlift' rho e1) (vlift' rho e2) (vlift' rho A).
Proof.
  intros Hcl W H. revert rho G' W.
  induction H; intros rho G' W; simpl.
  - apply VDF_bvar. eapply VLookup_weak'; eassumption.
  - apply VDF_symm. apply IHVIsDefEq. exact W.
  - eapply VDF_trans; [apply IHVIsDefEq1 | apply IHVIsDefEq2]; exact W.
  - apply VDF_sortDF; assumption.
  - rewrite (@vclosedN_vlift'_eq 0 rho _ (closed_inst_const ls1 0 Hcl H) (vlift_fixes_zero rho)).
    eapply VDF_constDF; eassumption.
  - rewrite vlift'_vinst_hi.
    eapply VDF_appDF; [apply IHVIsDefEq1 | apply IHVIsDefEq2]; exact W.
  - eapply VDF_lamDF; [apply IHVIsDefEq1; exact W | apply IHVIsDefEq2; constructor; exact W].
  - eapply VDF_forallEDF; [apply IHVIsDefEq1; exact W | apply IHVIsDefEq2; constructor; exact W].
  - eapply VDF_defeqDF; [apply IHVIsDefEq1 | apply IHVIsDefEq2]; exact W.
  - rewrite !vlift'_vinst_hi.
    eapply VDF_beta; [apply IHVIsDefEq1; constructor; exact W | apply IHVIsDefEq2; exact W].
  - rewrite vlift'_cons_vlift.
    apply VDF_eta. apply IHVIsDefEq. exact W.
  - eapply VDF_proofIrrel; [apply IHVIsDefEq1 | apply IHVIsDefEq2 | apply IHVIsDefEq3]; exact W.
  - destruct (closed_inst_defeq ls 0 Hcl H) as [Hl [Hr Ht]].
    rewrite (@vclosedN_vlift'_eq 0 rho _ Hl (vlift_fixes_zero rho)),
            (@vclosedN_vlift'_eq 0 rho _ Hr (vlift_fixes_zero rho)),
            (@vclosedN_vlift'_eq 0 rho _ Ht (vlift_fixes_zero rho)).
    eapply VDF_extra; eassumption.
Qed.

Corollary VHasType_weak' env U rho G G' e A :
  VEnvClosed env -> VCtxLift' rho G G' ->
  VHasType env U G e A ->
  VHasType env U G' (vlift' rho e) (vlift' rho A).
Proof. apply VIsDefEq_weak'. Qed.

Corollary VIsType_weak' env U rho G G' A :
  VEnvClosed env -> VCtxLift' rho G G' ->
  VIsType env U G A ->
  VIsType env U G' (vlift' rho A).
Proof.
  intros Hcl W [u Hu]. exists u. exact (VIsDefEq_weak' Hcl W Hu).
Qed.

Corollary VIsDefEqU_weak' env U rho G G' e1 e2 :
  VEnvClosed env -> VCtxLift' rho G G' ->
  VIsDefEqU env U G e1 e2 ->
  VIsDefEqU env U G' (vlift' rho e1) (vlift' rho e2).
Proof.
  intros Hcl W [A HA]. exists (vlift' rho A). exact (VIsDefEq_weak' Hcl W HA).
Qed.

(* Context well-formedness preservation for VCtxInstN and VIsDefEqCtx *)

Theorem VCtxInstN_wf env U G0 e0 A0 k G1 G :
  VEnvClosed env ->
  VHasType env U G0 e0 A0 ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VCtxWF env U G1 ->
  VCtxWF env U G0 /\ VCtxWF env U G.
Proof.
  intros Hcl H0 W.
  induction W as [|k G1 G A W IH]; simpl.
  - intros [HG0 _]. split; exact HG0.
  - intros [HG1 HA]. destruct (IH HG1) as [HG0 HG].
    split; [exact HG0 |].
    split; [exact HG | exact (VIsType_instN Hcl W HA H0)].
Qed.

Theorem VIsDefEqCtx_wf env U G0 G1 G2 :
  VEnvClosed env ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VCtxWF env U G1.
Proof.
  intros Hcl HG0 W.
  induction W as [|G1 G2 A1 A2 u W IH HA]; simpl.
  - exact HG0.
  - split; [exact IH | exists u; exact (VIsDefEq_refl_l HA)].
Qed.

(* ========================================================================= *)
(* 5. Simultaneous Definitional-Equality Substitution VCtxSubstEq            *)
(* ========================================================================= *)

Inductive VCtxSubstEq (env : VEnv) (U : nat) (Delta : list VExpr) :
    VSubst -> VSubst -> list VExpr -> Prop :=
| VCtxSubstEq_nil : forall sigma1 sigma2,
    VCtxSubstEq env U Delta sigma1 sigma2 []
| VCtxSubstEq_cons : forall sigma1 sigma2 Gamma A u,
    VCtxSubstEq env U Delta (vsubst_tail sigma1) (vsubst_tail sigma2) Gamma ->
    VHasType env U Gamma A (VSort u) ->
    VIsDefEq env U Delta (vsubst_head sigma1) (vsubst_head sigma2)
             (vsubst (vsubst_tail sigma1) A) ->
    VCtxSubstEq env U Delta sigma1 sigma2 (A :: Gamma).

(* Pointwise extensionality of VCtxSubstEq (eliminating any need for funext!) *)
Theorem VCtxSubstEq_ext env U Delta s1 s1' s2 s2' Gamma :
  vsubst_eq s1 s1' ->
  vsubst_eq s2 s2' ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VCtxSubstEq env U Delta s1' s2' Gamma.
Proof.
  intros Heq1 Heq2 W. revert s1' s2' Heq1 Heq2.
  induction W as [s1 s2 | s1 s2 Gamma A u W IH HA Hhd]; intros s1' s2' Heq1 Heq2.
  - constructor.
  - eapply VCtxSubstEq_cons.
    + apply IH; intros i; unfold vsubst_tail; [apply Heq1 | apply Heq2].
    + exact HA.
    + unfold vsubst_head in *.
      rewrite <- (Heq1 0), <- (Heq2 0).
      rewrite <- (vsubst_ext A (s1 := vsubst_tail s1) (s2 := vsubst_tail s1')
                    (fun i => Heq1 (S i))).
      exact Hhd.
Qed.

Lemma VCtxSubstEq_cons_explicit env U Delta s1 s2 x y Gamma A u :
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VHasType env U Gamma A (VSort u) ->
  VIsDefEq env U Delta x y (vsubst s1 A) ->
  VCtxSubstEq env U Delta (vsubst_cons s1 x) (vsubst_cons s2 y) (A :: Gamma).
Proof.
  intros W HA Hxy.
  eapply VCtxSubstEq_cons.
  - eapply VCtxSubstEq_ext.
    + apply vsubst_eq_symm. apply vsubst_cons_tail.
    + apply vsubst_eq_symm. apply vsubst_cons_tail.
    + exact W.
  - exact HA.
  - simpl.
    rewrite (vsubst_ext A (vsubst_cons_tail s1 x)).
    exact Hxy.
Qed.

Theorem VCtxSubstEq_left env U Delta s1 s2 Gamma :
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VCtxSubstEq env U Delta s1 s1 Gamma.
Proof.
  induction 1 as [s1 s2 | s1 s2 Gamma A u W IH HA Hhd].
  - constructor.
  - eapply VCtxSubstEq_cons; [exact IH | exact HA | exact (VIsDefEq_refl_l Hhd)].
Qed.

Theorem VCtxSubstEq_lookup env U Delta s1 s2 Gamma i A :
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VLookup Gamma i A ->
  VIsDefEq env U Delta (s1 i) (s2 i) (vsubst s1 A).
Proof.
  intros W. revert i A.
  induction W as [s1 s2 | s1 s2 Gamma A u W IH HA Hhd]; intros i B Hlk.
  - inversion Hlk.
  - inversion Hlk as [A0 G0 Heq1 Heq2 | A0 G0 j B0 Hj Heq1 Heq2]; subst.
    + rewrite vlift_vsubst. exact Hhd.
    + rewrite vlift_vsubst. exact (IH j B0 Hj).
Qed.

Theorem VCtxSubstEq_skip env U Delta B s1 s2 Gamma :
  VEnvClosed env ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VCtxSubstEq env U (B :: Delta)
    (vsubst_lift_r s1 (VLSkip VLRefl))
    (vsubst_lift_r s2 (VLSkip VLRefl)) Gamma.
Proof.
  intros Hcl W.
  induction W as [s1 s2 | s1 s2 Gamma A u W IH HA Hhd].
  - constructor.
  - eapply VCtxSubstEq_cons.
    + exact IH.
    + exact HA.
    + unfold vsubst_head, vsubst_lift_r in *.
      change (vsubst_tail (fun x => vlift' (VLSkip VLRefl) (s1 x)))
        with (vsubst_lift_r (vsubst_tail s1) (VLSkip VLRefl)).
      rewrite <- vlift'_vsubst.
      apply (VIsDefEq_weak' Hcl (VCtxLift'_skip B (VCtxLift'_refl Delta)) Hhd).
Qed.

Theorem VCtxSubstEq_lift env U Delta s1 s2 Gamma A u :
  VEnvClosed env ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VHasType env U Gamma A (VSort u) ->
  VCtxSubstEq env U (vsubst s1 A :: Delta) (vsubst_lift s1) (vsubst_lift s2) (A :: Gamma).
Proof.
  intros Hcl W HA.
  assert (Htail1 : vsubst_eq (vsubst_lift_r s1 (VLSkip VLRefl)) (vsubst_tail (vsubst_lift s1))).
  { intros i. unfold vsubst_lift_r, vsubst_tail, vsubst_lift.
    rewrite vlift_eq_vlift'. reflexivity. }
  assert (Htail2 : vsubst_eq (vsubst_lift_r s2 (VLSkip VLRefl)) (vsubst_tail (vsubst_lift s2))).
  { intros i. unfold vsubst_lift_r, vsubst_tail, vsubst_lift.
    rewrite vlift_eq_vlift'. reflexivity. }
  eapply VCtxSubstEq_cons.
  - eapply VCtxSubstEq_ext; [exact Htail1 | exact Htail2 |].
    apply VCtxSubstEq_skip; [exact Hcl | exact W].
  - exact HA.
  - simpl.
    rewrite <- (vsubst_ext A Htail1), <- vlift'_vsubst, <- vlift_eq_vlift'.
    apply VDF_bvar. constructor.
Qed.

Theorem VCtxSubstEq_lift_at env U Delta s1 s2 Gamma A X u :
  VEnvClosed env ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VHasType env U Gamma A (VSort u) ->
  VIsDefEq env U Delta (vsubst s1 A) X (VSort u) ->
  VCtxSubstEq env U (X :: Delta) (vsubst_lift s1) (vsubst_lift s2) (A :: Gamma).
Proof.
  intros Hcl W HA HAX.
  assert (Htail1 : vsubst_eq (vsubst_lift_r s1 (VLSkip VLRefl)) (vsubst_tail (vsubst_lift s1))).
  { intros i. unfold vsubst_lift_r, vsubst_tail, vsubst_lift.
    rewrite vlift_eq_vlift'. reflexivity. }
  assert (Htail2 : vsubst_eq (vsubst_lift_r s2 (VLSkip VLRefl)) (vsubst_tail (vsubst_lift s2))).
  { intros i. unfold vsubst_lift_r, vsubst_tail, vsubst_lift.
    rewrite vlift_eq_vlift'. reflexivity. }
  eapply VCtxSubstEq_cons.
  - eapply VCtxSubstEq_ext; [exact Htail1 | exact Htail2 |].
    apply VCtxSubstEq_skip; [exact Hcl | exact W].
  - exact HA.
  - simpl.
    rewrite <- (vsubst_ext A Htail1), <- vlift'_vsubst, <- vlift_eq_vlift'.
    eapply VDF_defeqDF.
    + exact (VIsDefEq_weak X Hcl (VDF_symm HAX)).
    + apply VDF_bvar. constructor.
Qed.

Theorem VCtxSubstEq_wf env U Delta s1 s2 Gamma :
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VCtxWF env U Gamma.
Proof.
  induction 1 as [s1 s2 | s1 s2 Gamma A u W IH HA _]; simpl.
  - exact I.
  - split; [exact IH | exists u; exact HA].
Qed.

Theorem VCtxSubstEq_id env U Gamma :
  VEnvClosed env ->
  VCtxWF env U Gamma ->
  VCtxSubstEq env U Gamma vsubst_id vsubst_id Gamma.
Proof.
  intros Hcl.
  induction Gamma as [|A Gamma IH]; simpl.
  - intros _. constructor.
  - intros [HG [u HA]].
    assert (Htail : vsubst_eq (vsubst_lift_r vsubst_id (VLSkip VLRefl)) (vsubst_tail vsubst_id)).
    { intros i. reflexivity. }
    eapply VCtxSubstEq_cons.
    + eapply VCtxSubstEq_ext; [exact Htail | exact Htail |].
      apply VCtxSubstEq_skip; [exact Hcl | exact (IH HG)].
    + exact HA.
    + simpl.
      rewrite <- (vsubst_ext A Htail), <- vlift'_vsubst, vsubst_id_eq, <- vlift_eq_vlift'.
      apply VDF_bvar. constructor.
Qed.

(* ========================================================================= *)
(* Axiom Audit                                                               *)
(* ========================================================================= *)

Print Assumptions vliftN_inj.
Print Assumptions vskips_iff.
Print Assumptions vlift'_comp.
Print Assumptions vlift'_inj.
Print Assumptions vsubst_id_eq.
Print Assumptions vsubst_comp_eq.
Print Assumptions vclosedN_vsubst_eq.
Print Assumptions vlift_vsubst_cons.
Print Assumptions vlift_vsubst_lift.
Print Assumptions vsubst_vinst.
Print Assumptions vinst_vlift_cons.
Print Assumptions vinstL_vsubst.
Print Assumptions VCtxLiftN_iff_VCtxLift'.
Print Assumptions VIsDefEq_weak'.
Print Assumptions VCtxSubstEq_lookup.
Print Assumptions VCtxSubstEq_lift_at.
Print Assumptions VCtxSubstEq_wf.
Print Assumptions VCtxSubstEq_id.
