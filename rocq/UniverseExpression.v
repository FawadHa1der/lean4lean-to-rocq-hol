(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Universe instantiation commutes with the actual term-binder operations. *)
From Stdlib Require Import List Bool Arith.
From LeanPort Require Import Syntax.
Import ListNotations.

Theorem subst_levels_lift ps us e : forall amount cutoff,
  subst_levels ps us (lift amount cutoff e) =
  lift amount cutoff (subst_levels ps us e).
Proof.
  induction e; intros amount cutoff; simpl; try reflexivity;
    f_equal; auto.
Qed.

Theorem subst_levels_subst ps us e : forall index value,
  subst_levels ps us (subst index value e) =
  subst index (subst_levels ps us value) (subst_levels ps us e).
Proof.
  induction e; intros index value; simpl; try reflexivity; try (f_equal; auto).
  destruct (n =? index); [destruct index; simpl; auto using subst_levels_lift|reflexivity].
Qed.

Theorem subst_levels_subst_many ps us e : forall index values,
  subst_levels ps us (subst_many index values e) =
  subst_many index (map (subst_levels ps us) values) (subst_levels ps us e).
Proof.
  induction e; intros index values; simpl; try reflexivity; try (f_equal; auto).
  destruct (n <? index); [reflexivity|].
  rewrite nth_error_map. destruct (nth_error values (n - index)); simpl.
  - destruct index; simpl; auto using subst_levels_lift.
  - rewrite map_length. reflexivity.
Qed.

Theorem subst_levels_instantiate ps us body value :
  subst_levels ps us (instantiate body value) =
  instantiate (subst_levels ps us body) (subst_levels ps us value).
Proof. apply subst_levels_subst. Qed.

Theorem subst_levels_instantiate_many ps us body values :
  subst_levels ps us (instantiate_many body values) =
  instantiate_many (subst_levels ps us body) (map (subst_levels ps us) values).
Proof.
  destruct values; [reflexivity|]. apply subst_levels_subst_many.
Qed.

Theorem subst_levels_scoped ps us e : forall depth,
  scoped depth (subst_levels ps us e) = scoped depth e.
Proof.
  induction e; intros depth; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; reflexivity.
Qed.

Print Assumptions subst_levels_lift.
Print Assumptions subst_levels_subst.
Print Assumptions subst_levels_subst_many.
Print Assumptions subst_levels_instantiate.
Print Assumptions subst_levels_instantiate_many.
Print Assumptions subst_levels_scoped.
