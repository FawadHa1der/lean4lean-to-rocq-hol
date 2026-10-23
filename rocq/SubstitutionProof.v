(* SPDX-License-Identifier: Apache-2.0
   Refinement of the batched, capture-avoiding substitution operation. *)
From Stdlib Require Import List Arith Bool Lia.
From LeanPort Require Import Syntax.
Import ListNotations.

Lemma subst_removes_protected_lift e : forall k cutoff value,
  subst (k + cutoff) value (lift (S k) cutoff e) = lift k cutoff e.
Proof.
  induction e; intros k cutoff value; simpl; try reflexivity;
    try (f_equal; auto).
  - destruct (cutoff <=? n) eqn:Hbound.
    + apply Nat.leb_le in Hbound.
      change (subst (k + cutoff) value (EBVar (S k + n)) = EBVar (k + n)).
      cbn [subst].
      assert ((S k + n =? k + cutoff) = false) as Hneq by
        (apply Nat.eqb_neq; lia).
      assert ((k + cutoff <? S k + n) = true) as Hlt by
        (apply Nat.ltb_lt; lia).
      rewrite Hneq, Hlt. reflexivity.
    + apply Nat.leb_gt in Hbound.
      change (subst (k + cutoff) value (EBVar n) = EBVar n).
      cbn [subst].
      assert ((n =? k + cutoff) = false) as Hneq by
        (apply Nat.eqb_neq; lia).
      assert ((k + cutoff <? n) = false) as Hlt by
        (apply Nat.ltb_ge; lia).
      rewrite Hneq, Hlt. reflexivity.
  - replace (S (k + cutoff)) with (k + S cutoff) by lia. auto.
  - replace (S (k + cutoff)) with (k + S cutoff) by lia. auto.
  - replace (S (k + cutoff)) with (k + S cutoff) by lia. auto.
Qed.

Lemma subst_many_cons e : forall index value values,
  subst_many index (value :: values) e =
    subst index value (subst_many (S index) values e).
Proof.
  induction e; intros index value values; simpl; try reflexivity;
    try (f_equal; auto).
  destruct (Nat.lt_trichotomy n index) as [Hlt | [Heq | Hgt]].
  - assert ((n <? index) = true) as A by (apply Nat.ltb_lt; lia).
    assert ((n <? S index) = true) as B by (apply Nat.ltb_lt; lia).
    rewrite A, B. cbn [subst].
    assert ((n =? index) = false) as C by (apply Nat.eqb_neq; lia).
    assert ((index <? n) = false) as D by (apply Nat.ltb_ge; lia).
    rewrite C, D. reflexivity.
  - subst n. rewrite Nat.ltb_irrefl, Nat.sub_diag.
    assert ((index <? S index) = true) as A by (apply Nat.ltb_lt; lia).
    rewrite A. cbn [nth_error subst]. rewrite Nat.eqb_refl. reflexivity.
  - assert ((n <? index) = false) as A by (apply Nat.ltb_ge; lia).
    assert ((n <? S index) = false) as B by (apply Nat.ltb_ge; lia).
    assert (n - index = S (n - S index)) as C by lia.
    rewrite A, B, C. cbn [nth_error].
    destruct (nth_error values (n - S index)) as [replacement|] eqn:Hnth.
    + rewrite <- (Nat.add_0_r index) at 2.
      rewrite subst_removes_protected_lift.
      destruct index; simpl; auto. symmetry. apply lift_zero.
    + apply nth_error_None in Hnth. cbn [subst].
      assert ((n - length values =? index) = false) as D by
        (apply Nat.eqb_neq; lia).
      assert ((index <? n - length values) = true) as E by
        (apply Nat.ltb_lt; lia).
      rewrite D, E. f_equal. lia.
Qed.

Fixpoint subst_sequential (index : nat) (values : list expr) (e : expr) : expr :=
  match values with
  | [] => e
  | value :: rest => subst index value (subst_sequential (S index) rest e)
  end.

Theorem subst_many_sequential values : forall index e,
  subst_many index values e = subst_sequential index values e.
Proof.
  induction values as [|value rest IH]; intros index e; simpl.
  - apply subst_many_nil.
  - rewrite subst_many_cons, IH. reflexivity.
Qed.

Theorem instantiate_many_sequential body values :
  instantiate_many body values = subst_sequential 0 values body.
Proof.
  destruct values as [|value rest]; [reflexivity|].
  apply subst_many_sequential.
Qed.

Print Assumptions subst_many_sequential.
Print Assumptions instantiate_many_sequential.
