(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Verified positive and negative definitional-equality memoization and
   equivalence manager (corresponding to Lean4Lean's defeq/equiv_manager cache).
   Proves that consulting a sound positive/negative cache refines uncached
   definitional equality and preserves both acceptance and rejection verdicts. *)
From Stdlib Require Import List Bool Arith PeanoNat.
From LeanPort Require Import Syntax Checker SemanticModel DeclarativeTyping.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Positive & Negative Definitional-Equality Cache                        *)
(* ========================================================================= *)

Record defeq_cache_key : Type := {
  dck_context_depth : nat;
  dck_lhs : expr;
  dck_rhs : expr
}.

Definition defeq_cache_key_eqb (k1 k2 : defeq_cache_key) : bool :=
  Nat.eqb (dck_context_depth k1) (dck_context_depth k2) &&
  expr_eqb (dck_lhs k1) (dck_lhs k2) &&
  expr_eqb (dck_rhs k1) (dck_rhs k2).

Record defeq_cache_entry : Type := {
  dce_key     : defeq_cache_key;
  dce_verdict : bool (* true = positive DefEq hit; false = negative failure hit *)
}.

Definition defeq_cache := list defeq_cache_entry.

Fixpoint cache_lookup (k : defeq_cache_key) (cache : defeq_cache) : option bool :=
  match cache with
  | [] => None
  | entry :: rest =>
      if defeq_cache_key_eqb k (dce_key entry)
      then Some (dce_verdict entry)
      else cache_lookup k rest
  end.

Definition cache_insert (k : defeq_cache_key) (verdict : bool)
    (cache : defeq_cache) : defeq_cache :=
  {| dce_key := k; dce_verdict := verdict |} :: cache.

Definition key_of_query (g : context) (t s : expr) : defeq_cache_key := {|
  dck_context_depth := List.length (bound_context g);
  dck_lhs := t;
  dck_rhs := s
|}.

(* Cached definitional-equality wrapper that returns updated cache + result *)
Definition cached_defeq (fuel : nat) (env : environment) (ps : list name)
    (g : context) (cache : defeq_cache) (t s : expr)
    : defeq_cache * result bool :=
  let key := key_of_query g t s in
  match cache_lookup key cache with
  | Some verdict => (cache, Accept verdict)
  | None =>
      let res := defeq fuel env ps g t s in
      match res with
      | Accept verdict => (cache_insert key verdict cache, Accept verdict)
      | Reject err => (cache, Reject err)
      | Decline why => (cache, Decline why)
      end
  end.

(* ========================================================================= *)
(* 2. Cache Soundness Invariant & Exact Refinement Theorems                  *)
(* ========================================================================= *)

Definition cache_sound_for (fuel : nat) (env : environment) (ps : list name)
    (cache : defeq_cache) : Prop :=
  forall g t s verdict,
    cache_lookup (key_of_query g t s) cache = Some verdict ->
    defeq fuel env ps g t s = Accept verdict.

Lemma empty_cache_sound fuel env ps :
  cache_sound_for fuel env ps [].
Proof.
  intros g t s verdict H. simpl in H. discriminate.
Qed.

Theorem cached_defeq_refines_uncached fuel env ps g cache t s :
  cache_sound_for fuel env ps cache ->
  snd (cached_defeq fuel env ps g cache t s) = defeq fuel env ps g t s.
Proof.
  intros Hsound. unfold cached_defeq.
  destruct (cache_lookup (key_of_query g t s) cache) as [verdict|] eqn:Hlk.
  - simpl. symmetry. apply Hsound. exact Hlk.
  - destruct (defeq fuel env ps g t s); reflexivity.
Qed.

Theorem cached_defeq_preserves_positive_and_negative fuel env ps g cache t s verdict :
  cache_sound_for fuel env ps cache ->
  snd (cached_defeq fuel env ps g cache t s) = Accept verdict <->
  defeq fuel env ps g t s = Accept verdict.
Proof.
  intros Hsound.
  rewrite (@cached_defeq_refines_uncached fuel env ps g cache t s Hsound).
  tauto.
Qed.

(* Semantic soundness of positive cache hits with respect to VIsDefEqU *)
Definition positive_cache_semantically_sound (venv : VEnv) (uvars : nat)
    (interp : context -> expr -> VExpr -> Prop) (cache : defeq_cache) : Prop :=
  forall g t s t' s' G,
    List.length G = List.length (bound_context g) ->
    cache_lookup (key_of_query g t s) cache = Some true ->
    interp g t t' ->
    interp g s s' ->
    VIsDefEqU venv uvars G t' s'.

Theorem positive_cache_hit_sound venv uvars interp cache g t s t' s' G :
  positive_cache_semantically_sound venv uvars interp cache ->
  List.length G = List.length (bound_context g) ->
  cache_lookup (key_of_query g t s) cache = Some true ->
  interp g t t' ->
  interp g s s' ->
  VIsDefEqU venv uvars G t' s'.
Proof.
  intros Hsem Hlen Hlk Ht Hs.
  eapply Hsem; eassumption.
Qed.

Print Assumptions cached_defeq_refines_uncached.
Print Assumptions cached_defeq_preserves_positive_and_negative.
Print Assumptions positive_cache_hit_sound.
