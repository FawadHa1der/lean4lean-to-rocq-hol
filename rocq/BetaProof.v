(* SPDX-License-Identifier: Apache-2.0
   Scope preservation for the visible-lambda batched beta reducer. *)
From Stdlib Require Import List Bool Arith Lia.
From LeanPort Require Import Syntax Checker SubstitutionProof.
Import ListNotations.

Lemma instantiate_many_preserves_scope body values depth :
  scoped (List.length values + depth) body = true ->
  Forall (fun value => scoped depth value = true) values ->
  scoped depth (instantiate_many body values) = true.
Proof.
  intros Hbody Hvalues. destruct values as [|value rest]; simpl in *; auto.
  exact (@subst_many_scoped body 0 (value :: rest) depth Hbody Hvalues).
Qed.

Lemma core_apps_preserves_scope args : forall head depth,
  scoped depth head = true ->
  Forall (fun arg => scoped depth arg = true) args ->
  scoped depth (core_apps head args) = true.
Proof.
  induction args as [|arg rest IH]; intros head depth Hhead Hargs; simpl; auto.
  inversion Hargs; subst. apply IH; auto. simpl. rewrite Hhead. assumption.
Qed.

Lemma core_beta_collect_preserves_scope args : forall head values depth,
  scoped (List.length values + depth) head = true ->
  Forall (fun arg => scoped depth arg = true) args ->
  Forall (fun value => scoped depth value = true) values ->
  scoped depth (core_beta_collect head args values) = true.
Proof.
  induction args as [|arg rest IH]; intros head values depth Hhead Hargs Hvalues.
  - destruct head; cbn [core_beta_collect]; apply instantiate_many_preserves_scope; assumption.
  - inversion Hargs as [|arg' rest' Harg Hrest]; subst.
    destruct head; cbn [core_beta_collect];
      try (apply core_apps_preserves_scope;
        [apply instantiate_many_preserves_scope; assumption | exact Hargs]).
    apply andb_true_iff in Hhead as [_ Hbody].
    apply IH; simpl; auto.
Qed.

Theorem core_beta_preserves_scope head args depth :
  scoped depth head = true ->
  Forall (fun arg => scoped depth arg = true) args ->
  scoped depth (core_beta head args) = true.
Proof.
  intros Hhead Hargs. unfold core_beta.
  apply core_beta_collect_preserves_scope; simpl; auto.
Qed.

Print Assumptions core_beta_preserves_scope.
