(* SPDX-License-Identifier: Apache-2.0
   Lean4Lean 8223d223ed98661882e95d9d6a7126df7097cd76,
   FuelConfig.lean and TypeChecker.lean's local WHNF unfolding loop.
   Private candidate: these rounds are separate from the existing depth fuel. *)
From Stdlib Require Import Bool Arith.
From LeanPort Require Import Syntax EagerPolicy.

(* Ordinary extraction allocates each unary numeral once, not per WHNF call. *)
Definition normal_whnf_rounds : nat := 100000.
Definition eager_whnf_rounds : nat := 1000000.

Definition whnf_round_limit (mode : reduction_mode) : nat :=
  match mode with
  | NormalReduction => normal_whnf_rounds
  | EagerReduction => eager_whnf_rounds
  end.

Lemma whnf_round_limit_exact mode :
  whnf_round_limit mode =
    match mode with NormalReduction => 100000 | EagerReduction => 1000000 end.
Proof. destruct mode; reflexivity. Qed.

Inductive whnf_round : Type :=
| WhnfDone : expr -> whnf_round
| WhnfContinue : expr -> whnf_round.

Fixpoint run_whnf_rounds (rounds : nat) (step : expr -> result whnf_round)
    (e : expr) : result expr :=
  match rounds with
  | 0 => Decline OutOfFuel
  | S remaining =>
      round <- step e ;;
      match round with
      | WhnfDone value => Accept value
      | WhnfContinue value => run_whnf_rounds remaining step value
      end
  end.

Theorem run_whnf_rounds_extensional rounds left right :
  (forall e, left e = right e) ->
  forall e, run_whnf_rounds rounds left e = run_whnf_rounds rounds right e.
Proof.
  intros H. induction rounds as [|rounds IH]; intros e; simpl; [reflexivity|].
  rewrite H. destruct (right e) as [[value|value]|error|reason]; simpl;
    try reflexivity. apply IH.
Qed.

Theorem run_whnf_rounds_reject rounds step e error :
  step e = Reject error -> run_whnf_rounds (S rounds) step e = Reject error.
Proof. intros H; simpl; rewrite H; reflexivity. Qed.

Theorem run_whnf_rounds_decline rounds step e reason :
  step e = Decline reason -> run_whnf_rounds (S rounds) step e = Decline reason.
Proof. intros H; simpl; rewrite H; reflexivity. Qed.

Print Assumptions run_whnf_rounds_extensional.
