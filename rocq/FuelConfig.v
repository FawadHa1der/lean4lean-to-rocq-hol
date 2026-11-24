(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Six-axis fuel configuration (Lean4Lean/FuelConfig.lean): separates
   WHNF, eager-WHNF, lazy-delta, eta-expansion, recursion-depth, and
   inductive-checking budgets, proves exact embedding of uniform fuel,
   and establishes fail-closed OutOfFuel behavior across all axes. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes WhnfPolicy Checker Declarations.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Six-Axis FuelConfig Record (Lean4Lean/FuelConfig.lean)                 *)
(* ========================================================================= *)

Record fuel_config : Type := {
  fc_whnf           : nat;
  fc_whnf_eager     : nat;
  fc_lazy_delta     : nat;
  fc_eta_expand     : nat;
  fc_rec_depth      : nat;
  fc_inductive_fuel : nat
}.

(* Upstream FuelConfig defaults (Lean4Lean/FuelConfig.lean:18-30).
   Reuses normal_whnf_rounds / eager_whnf_rounds so extraction allocates each
   large unary numeral once at module initialization. *)
Definition default_lazy_delta_rounds : nat := 1000.
Definition default_eta_expand_rounds : nat := 1000.
Definition default_rec_depth : nat := 50000.
Definition default_inductive_fuel : nat := 1000.

Definition default_fuel_config : fuel_config := {|
  fc_whnf           := normal_whnf_rounds;
  fc_whnf_eager     := eager_whnf_rounds;
  fc_lazy_delta     := default_lazy_delta_rounds;
  fc_eta_expand     := default_eta_expand_rounds;
  fc_rec_depth      := default_rec_depth;
  fc_inductive_fuel := default_inductive_fuel
|}.

Definition fuel_config_with_rec_depth (rec_depth : nat) : fuel_config := {|
  fc_whnf           := normal_whnf_rounds;
  fc_whnf_eager     := eager_whnf_rounds;
  fc_lazy_delta     := default_lazy_delta_rounds;
  fc_eta_expand     := default_eta_expand_rounds;
  fc_rec_depth      := rec_depth;
  fc_inductive_fuel := default_inductive_fuel
|}.

Definition uniform_fuel_config (fuel : nat) : fuel_config := {|
  fc_whnf           := fuel;
  fc_whnf_eager     := fuel;
  fc_lazy_delta     := fuel;
  fc_eta_expand     := fuel;
  fc_rec_depth      := fuel;
  fc_inductive_fuel := fuel
|}.

Definition min_fuel_of_config (cfg : fuel_config) : nat :=
  Nat.min (fc_whnf cfg)
    (Nat.min (fc_whnf_eager cfg)
      (Nat.min (fc_lazy_delta cfg)
        (Nat.min (fc_eta_expand cfg)
          (Nat.min (fc_rec_depth cfg) (fc_inductive_fuel cfg))))).

Definition max_fuel_of_config (cfg : fuel_config) : nat :=
  Nat.max (fc_whnf cfg)
    (Nat.max (fc_whnf_eager cfg)
      (Nat.max (fc_lazy_delta cfg)
        (Nat.max (fc_eta_expand cfg)
          (Nat.max (fc_rec_depth cfg) (fc_inductive_fuel cfg))))).

Definition fuel_config_le (c1 c2 : fuel_config) : Prop :=
  fc_whnf c1 <= fc_whnf c2 /\
  fc_whnf_eager c1 <= fc_whnf_eager c2 /\
  fc_lazy_delta c1 <= fc_lazy_delta c2 /\
  fc_eta_expand c1 <= fc_eta_expand c2 /\
  fc_rec_depth c1 <= fc_rec_depth c2 /\
  fc_inductive_fuel c1 <= fc_inductive_fuel c2.

Definition fuel_config_nonzero (cfg : fuel_config) : bool :=
  match fc_whnf cfg, fc_whnf_eager cfg, fc_lazy_delta cfg,
        fc_eta_expand cfg, fc_rec_depth cfg, fc_inductive_fuel cfg with
  | S _, S _, S _, S _, S _, S _ => true
  | _, _, _, _, _, _ => false
  end.

Lemma fuel_config_nonzero_iff cfg :
  fuel_config_nonzero cfg = true <-> 0 < min_fuel_of_config cfg.
Proof.
  unfold fuel_config_nonzero, min_fuel_of_config.
  rewrite !Nat.min_glb_lt_iff.
  destruct (fc_whnf cfg); [split; [discriminate | lia]|].
  destruct (fc_whnf_eager cfg); [split; [discriminate | lia]|].
  destruct (fc_lazy_delta cfg); [split; [discriminate | lia]|].
  destruct (fc_eta_expand cfg); [split; [discriminate | lia]|].
  destruct (fc_rec_depth cfg); [split; [discriminate | lia]|].
  destruct (fc_inductive_fuel cfg); [split; [discriminate | lia]|].
  split; intros _; repeat split; lia.
Qed.

Lemma fuel_config_nonzero_false_iff cfg :
  fuel_config_nonzero cfg = false <-> min_fuel_of_config cfg = 0.
Proof.
  destruct (fuel_config_nonzero cfg) eqn:Hz;
    [| split; [intros _| intro; reflexivity]].
  - split; [discriminate |].
    intro H0. pose proof (proj1 (fuel_config_nonzero_iff cfg) Hz) as Hlt. lia.
  - destruct (Nat.eq_dec (min_fuel_of_config cfg) 0) as [|Hne]; [assumption|].
    assert (Hpos : 0 < min_fuel_of_config cfg) by lia.
    apply (proj2 (fuel_config_nonzero_iff cfg)) in Hpos. congruence.
Qed.

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

Lemma uniform_fuel_config_nonzero fuel :
  fuel_config_nonzero (uniform_fuel_config fuel) =
    match fuel with 0 => false | S _ => true end.
Proof. destruct fuel; reflexivity. Qed.

Lemma of_uint_acc_pos d : forall acc, 0 < acc -> 0 < Nat.of_uint_acc d acc.
Proof.
  induction d; intros acc H; simpl; auto;
    apply IHd; rewrite Nat.tail_mul_spec; lia.
Qed.

Lemma of_uint_nonzero_pos d :
  match d with Decimal.D0 _ | Decimal.Nil => False | _ => True end ->
  0 < Nat.of_num_uint (Number.UIntDecimal d).
Proof.
  destruct d; intros H; try contradiction;
    cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc];
    apply of_uint_acc_pos; lia.
Qed.

Lemma default_fuel_config_positive :
  0 < min_fuel_of_config default_fuel_config.
Proof.
  unfold min_fuel_of_config, default_fuel_config.
  cbn [fc_whnf fc_whnf_eager fc_lazy_delta fc_eta_expand fc_rec_depth fc_inductive_fuel].
  unfold normal_whnf_rounds, eager_whnf_rounds,
    default_lazy_delta_rounds, default_eta_expand_rounds,
    default_rec_depth, default_inductive_fuel.
  rewrite !Nat.min_glb_lt_iff. repeat split;
    lazymatch goal with
    | |- 0 < Nat.of_num_uint (Number.UIntDecimal _) =>
        apply of_uint_nonzero_pos; exact I
    | _ => apply Nat.lt_0_succ
    end.
Qed.

(* ========================================================================= *)
(* 2. Axis-Parameterized Kernel Operations                                   *)
(* ========================================================================= *)

Definition infer_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e : expr) : result expr :=
  if fuel_config_nonzero cfg
  then infer (fc_rec_depth cfg) env ps g e
  else Decline OutOfFuel.

Definition whnf_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e : expr) : result expr :=
  if fuel_config_nonzero cfg
  then whnf (fc_rec_depth cfg) env ps g e
  else Decline OutOfFuel.

Definition defeq_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (t s : expr) : result bool :=
  if fuel_config_nonzero cfg
  then defeq (fc_rec_depth cfg) env ps g t s
  else Decline OutOfFuel.

Definition eta_expand_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e : expr) : result expr :=
  if fuel_config_nonzero cfg
  then core_eta_expand (fc_eta_expand cfg) (checker (fc_rec_depth cfg) env ps) g e
  else Decline OutOfFuel.

Definition check_with_config (cfg : fuel_config) (env : environment)
    (ps : list name) (g : context) (e ty : expr) : result unit :=
  if fuel_config_nonzero cfg then
    ignored <- sort_of (checker (fc_rec_depth cfg) env ps) g ty ;;
    et <- infer_with_config cfg env ps g e ;;
    ok <- defeq_with_config cfg env ps g et ty ;;
    require ok TypeMismatch
  else Decline OutOfFuel.

Definition admit_with_config (cfg : fuel_config) (env : environment)
    (d : input_decl) : result environment :=
  if fuel_config_nonzero cfg
  then admit (fc_rec_depth cfg) env d
  else Decline OutOfFuel.

(* ========================================================================= *)
(* 3. Uniform Embedding & Fail-Closed OutOfFuel Theorems                     *)
(* ========================================================================= *)

Theorem infer_uniform_config_eq fuel env ps g e :
  infer_with_config (uniform_fuel_config fuel) env ps g e =
  infer fuel env ps g e.
Proof.
  unfold infer_with_config. rewrite uniform_fuel_config_nonzero.
  destruct fuel; reflexivity.
Qed.

Theorem whnf_uniform_config_eq fuel env ps g e :
  whnf_with_config (uniform_fuel_config fuel) env ps g e =
  whnf fuel env ps g e.
Proof.
  unfold whnf_with_config. rewrite uniform_fuel_config_nonzero.
  destruct fuel; reflexivity.
Qed.

Theorem defeq_uniform_config_eq fuel env ps g t s :
  defeq_with_config (uniform_fuel_config fuel) env ps g t s =
  defeq fuel env ps g t s.
Proof.
  unfold defeq_with_config. rewrite uniform_fuel_config_nonzero.
  destruct fuel; reflexivity.
Qed.

Theorem check_uniform_config_eq fuel env ps g e ty :
  check_with_config (uniform_fuel_config fuel) env ps g e ty =
  check fuel env ps g e ty.
Proof.
  unfold check_with_config, check. rewrite uniform_fuel_config_nonzero.
  destruct fuel as [|fuel]; [reflexivity|].
  change (fc_rec_depth (uniform_fuel_config (S fuel))) with (S fuel).
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
  intros Hpos. unfold admit_with_config. rewrite uniform_fuel_config_nonzero.
  destruct fuel; [lia | reflexivity].
Qed.

Theorem config_zero_min_declines cfg env ps g e ty t s d :
  min_fuel_of_config cfg = 0 ->
  infer_with_config cfg env ps g e = Decline OutOfFuel /\
  whnf_with_config cfg env ps g e = Decline OutOfFuel /\
  defeq_with_config cfg env ps g t s = Decline OutOfFuel /\
  eta_expand_with_config cfg env ps g e = Decline OutOfFuel /\
  check_with_config cfg env ps g e ty = Decline OutOfFuel /\
  admit_with_config cfg env d = Decline OutOfFuel.
Proof.
  intros H0.
  apply (proj2 (fuel_config_nonzero_false_iff cfg)) in H0.
  unfold infer_with_config, whnf_with_config, defeq_with_config,
    eta_expand_with_config, check_with_config, admit_with_config.
  rewrite H0. repeat split; reflexivity.
Qed.

Theorem check_with_config_sound cfg env ps g e ty :
  check_with_config cfg env ps g e ty = Accept tt ->
  exists et,
    infer (fc_rec_depth cfg) env ps g e = Accept et /\
    defeq (fc_rec_depth cfg) env ps g et ty = Accept true.
Proof.
  unfold check_with_config, infer_with_config, defeq_with_config.
  destruct (fuel_config_nonzero cfg); [|discriminate].
  destruct (sort_of (checker (fc_rec_depth cfg) env ps) g ty); simpl; try discriminate.
  destruct (infer (fc_rec_depth cfg) env ps g e) as [et|err|why] eqn:Hinf; simpl; try discriminate.
  destruct (defeq (fc_rec_depth cfg) env ps g et ty) as [ok|err|why] eqn:Hdef; simpl; try discriminate.
  destruct ok; simpl; try discriminate.
  intros _. exists et. auto.
Qed.

Print Assumptions default_fuel_config_positive.
Print Assumptions infer_uniform_config_eq.
Print Assumptions whnf_uniform_config_eq.
Print Assumptions defeq_uniform_config_eq.
Print Assumptions check_uniform_config_eq.
Print Assumptions admit_uniform_config_pos_eq.
Print Assumptions config_zero_min_declines.
Print Assumptions check_with_config_sound.
