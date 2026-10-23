(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Multi-axis fuel configuration (Lean4Lean/FuelConfig.lean): separates
   WHNF, type-inference, definitional-equality, lazy-delta, and recursor
   reduction budgets, proves exact embedding of uniform fuel, and establishes
   fail-closed OutOfFuel behavior across all axes. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes WhnfPolicy Checker Declarations.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Multi-Axis FuelConfig Record (Lean4Lean/FuelConfig.lean)               *)
(* ========================================================================= *)

Record fuel_config : Type := {
  fc_whnf     : nat;
  fc_infer    : nat;
  fc_defeq    : nat;
  fc_delta    : nat;
  fc_recursor : nat
}.

Definition uniform_fuel_config (fuel : nat) : fuel_config := {|
  fc_whnf     := fuel;
  fc_infer    := fuel;
  fc_defeq    := fuel;
  fc_delta    := fuel;
  fc_recursor := fuel
|}.

Definition min_fuel_of_config (cfg : fuel_config) : nat :=
  Nat.min (fc_whnf cfg)
    (Nat.min (fc_infer cfg)
      (Nat.min (fc_defeq cfg)
        (Nat.min (fc_delta cfg) (fc_recursor cfg)))).

Definition max_fuel_of_config (cfg : fuel_config) : nat :=
  Nat.max (fc_whnf cfg)
    (Nat.max (fc_infer cfg)
      (Nat.max (fc_defeq cfg)
        (Nat.max (fc_delta cfg) (fc_recursor cfg)))).

Definition fuel_config_le (c1 c2 : fuel_config) : Prop :=
  fc_whnf c1 <= fc_whnf c2 /\
  fc_infer c1 <= fc_infer c2 /\
  fc_defeq c1 <= fc_defeq c2 /\
  fc_delta c1 <= fc_delta c2 /\
  fc_recursor c1 <= fc_recursor c2.

Lemma uniform_min_fuel fuel :
  min_fuel_of_config (uniform_fuel_config fuel) = fuel.
Proof.
  unfold min_fuel_of_config, uniform_fuel_config; simpl.
  rewrite !Nat.min_id. reflexivity.
Qed.

Lemma uniform_max_fuel fuel :
  max_fuel_of_config (uniform_fuel_config fuel) = fuel.
Proof.
  unfold max_fuel_of_config, uniform_fuel_config; simpl.
  rewrite !Nat.max_id. reflexivity.
Qed.

(* ========================================================================= *)
(* 2. Axis-Parameterized Kernel Operations                                   *)
(* ========================================================================= *)

Definition infer_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e : expr) : result expr :=
  match min_fuel_of_config cfg with
  | 0 => Decline OutOfFuel
  | _ => infer (fc_infer cfg) env ps g e
  end.

Definition whnf_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e : expr) : result expr :=
  match min_fuel_of_config cfg with
  | 0 => Decline OutOfFuel
  | _ => whnf (fc_whnf cfg) env ps g e
  end.

Definition defeq_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (t s : expr) : result bool :=
  match min_fuel_of_config cfg with
  | 0 => Decline OutOfFuel
  | _ => defeq (fc_defeq cfg) env ps g t s
  end.

Definition check_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e ty : expr) : result unit :=
  match min_fuel_of_config cfg with
  | 0 => Decline OutOfFuel
  | _ =>
      ignored <- sort_of (checker (fc_infer cfg) env ps) g ty ;;
      et <- infer_with_config cfg env ps g e ;;
      ok <- defeq_with_config cfg env ps g et ty ;;
      require ok TypeMismatch
  end.

Definition admit_with_config (cfg : fuel_config) (env : environment)
    (d : input_decl) : result environment :=
  match min_fuel_of_config cfg with
  | 0 => Decline OutOfFuel
  | k => admit k env d
  end.

(* ========================================================================= *)
(* 3. Uniform Embedding & Fail-Closed OutOfFuel Theorems                     *)
(* ========================================================================= *)

Theorem infer_uniform_config_eq fuel env ps g e :
  infer_with_config (uniform_fuel_config fuel) env ps g e =
  infer fuel env ps g e.
Proof.
  unfold infer_with_config. rewrite uniform_min_fuel.
  destruct fuel; reflexivity.
Qed.

Theorem whnf_uniform_config_eq fuel env ps g e :
  whnf_with_config (uniform_fuel_config fuel) env ps g e =
  whnf fuel env ps g e.
Proof.
  unfold whnf_with_config. rewrite uniform_min_fuel.
  destruct fuel; reflexivity.
Qed.

Theorem defeq_uniform_config_eq fuel env ps g t s :
  defeq_with_config (uniform_fuel_config fuel) env ps g t s =
  defeq fuel env ps g t s.
Proof.
  unfold defeq_with_config. rewrite uniform_min_fuel.
  destruct fuel; reflexivity.
Qed.

Theorem check_uniform_config_eq fuel env ps g e ty :
  check_with_config (uniform_fuel_config fuel) env ps g e ty =
  check fuel env ps g e ty.
Proof.
  unfold check_with_config, check. rewrite uniform_min_fuel.
  destruct fuel as [|fuel]; [reflexivity|].
  change (fc_infer (uniform_fuel_config (S fuel))) with (S fuel).
  destruct (sort_of (checker (S fuel) env ps) g ty); cbn [bind]; [|reflexivity..].
  rewrite infer_uniform_config_eq.
  destruct (infer (S fuel) env ps g e); cbn [bind]; [|reflexivity..].
  rewrite defeq_uniform_config_eq.
  reflexivity.
Qed.

Theorem admit_uniform_config_pos_eq fuel env d :
  0 < fuel ->
  admit_with_config (uniform_fuel_config fuel) env d =
  admit fuel env d.
Proof.
  intros Hpos. unfold admit_with_config. rewrite uniform_min_fuel.
  destruct fuel; [lia | reflexivity].
Qed.

Theorem config_zero_min_declines cfg env ps g e ty t s d :
  min_fuel_of_config cfg = 0 ->
  infer_with_config cfg env ps g e = Decline OutOfFuel /\
  whnf_with_config cfg env ps g e = Decline OutOfFuel /\
  defeq_with_config cfg env ps g t s = Decline OutOfFuel /\
  check_with_config cfg env ps g e ty = Decline OutOfFuel /\
  admit_with_config cfg env d = Decline OutOfFuel.
Proof.
  intros H0.
  unfold infer_with_config, whnf_with_config, defeq_with_config,
    check_with_config, admit_with_config.
  rewrite H0. repeat split; reflexivity.
Qed.

Theorem check_with_config_sound cfg env ps g e ty :
  check_with_config cfg env ps g e ty = Accept tt ->
  exists et,
    infer (fc_infer cfg) env ps g e = Accept et /\
    defeq (fc_defeq cfg) env ps g et ty = Accept true.
Proof.
  unfold check_with_config, infer_with_config, defeq_with_config.
  destruct (min_fuel_of_config cfg); [discriminate|].
  destruct (sort_of (checker (fc_infer cfg) env ps) g ty); simpl; try discriminate.
  destruct (infer (fc_infer cfg) env ps g e) as [et|err|why] eqn:Hinf; simpl; try discriminate.
  destruct (defeq (fc_defeq cfg) env ps g et ty) as [ok|err|why] eqn:Hdef; simpl; try discriminate.
  destruct ok; simpl; try discriminate.
  intros _. exists et. auto.
Qed.

Print Assumptions infer_uniform_config_eq.
Print Assumptions whnf_uniform_config_eq.
Print Assumptions defeq_uniform_config_eq.
Print Assumptions check_uniform_config_eq.
Print Assumptions admit_uniform_config_pos_eq.
Print Assumptions config_zero_min_declines.
Print Assumptions check_with_config_sound.
