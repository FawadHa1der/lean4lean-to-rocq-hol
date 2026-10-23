(* SPDX-License-Identifier: Apache-2.0
   Frozen stage-three conversion control flow, with exact-result guard refinement.
   This reference is proof-only and is not selected by production extraction. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax EagerPolicy NatProbeDispatch Checker
  LookupCore LookupRefinement GuardOrderPlan.
Import ListNotations.

Lemma ordinary_left_guard_exact rec fuel env g t s eligible :
  (if pair_probe_guard
      (nat_probe_head find_decl core_succ_name env (core_spine t []))
      (nat_probe_head find_decl core_succ_name env (core_spine s [])) eligible
   then core_reduce_nat rec fuel env g t else Accept None) =
  (if eligible tt then core_reduce_nat rec fuel env g t else Accept None).
Proof. apply pair_probe_left_exact. apply ordinary_inactive_nat_probe. Qed.

Lemma ordinary_right_guard_exact rec fuel env g t s eligible :
  (if pair_probe_guard
      (nat_probe_head find_decl core_succ_name env (core_spine t []))
      (nat_probe_head find_decl core_succ_name env (core_spine s [])) eligible
   then core_reduce_nat rec fuel env g s else Accept None) =
  (if eligible tt then core_reduce_nat rec fuel env g s else Accept None).
Proof. apply pair_probe_right_exact. apply ordinary_inactive_nat_probe. Qed.

Fixpoint stage3_lazy_delta (rounds : nat) (rec : methods) (fuel : nat)
    (env : environment) (ps : list name) (g : context) (t s : expr)
    : result conversion_progress :=
  match rounds with
  | 0 => Decline OutOfFuel
  | S rounds =>
      quick <- core_quick rec fuel g t s ;;
      match quick with
      | Some ok => Accept (ConversionDone ok)
      | None =>
        offset <- core_offset rec env g t s ;;
        match offset with
        | Some ok => Accept (ConversionDone ok)
        | None =>
          let eligible := nat_probe_allowed (method_mode rec) t s in
          tn <- if eligible then core_reduce_nat rec fuel env g t else Accept None ;;
          match tn with
          | Some tn => ok <- defeq_method rec g tn s ;; Accept (ConversionDone ok)
          | None =>
            sn <- if eligible then core_reduce_nat rec fuel env g s else Accept None ;;
            match sn with
            | Some sn => ok <- defeq_method rec g t sn ;; Accept (ConversionDone ok)
            | None =>
            same <- core_delta_congruent rec fuel env g t s ;;
            if same then Accept (ConversionDone true) else
            projected <- core_opposite_projection rec env g t s ;;
            match projected with
            | Some (tn, sn) => stage3_lazy_delta rounds rec fuel env ps g tn sn
            | None =>
            let '(unfold_left, unfold_right) := core_delta_sides env t s in
            td <- if unfold_left then core_unfold env ps t else Accept None ;;
            sd <- if unfold_right then core_unfold env ps s else Accept None ;;
            match td, sd with
            | None, None => Accept (ConversionStuck t s)
            | _, _ =>
              tn <- match td with Some e => whnf_core_method rec true g e | None => Accept t end ;;
              sn <- match sd with Some e => whnf_core_method rec true g e | None => Accept s end ;;
              stage3_lazy_delta rounds rec fuel env ps g tn sn
            end
            end
            end
          end
        end
      end
  end.

Theorem guard_order_lazy_delta_exact rounds rec fuel env ps g t s :
  core_lazy_delta rounds rec fuel env ps g t s =
    stage3_lazy_delta rounds rec fuel env ps g t s.
Proof.
  revert t s. induction rounds; intros t s;
    cbn [core_lazy_delta stage3_lazy_delta]; try reflexivity.
  rewrite ordinary_left_guard_exact, ordinary_right_guard_exact.
  pointwise.
Qed.

Definition stage3_true_shortcut (rec : methods) (env : environment)
    (g : context) (t s : expr) : result bool :=
  if true_probe_allowed (method_mode rec) t && core_is_true s && core_bool_ready env
  then tn <- whnf_method rec g t ;; Accept (core_is_true tn)
  else Accept false.

Theorem guard_order_true_shortcut_exact rec env g t s :
  core_true_shortcut rec env g t s = stage3_true_shortcut rec env g t s.
Proof. unfold core_true_shortcut, stage3_true_shortcut. apply ordinary_true_guard_reorder. Qed.
#[local] Hint Resolve guard_order_lazy_delta_exact guard_order_true_shortcut_exact : lookup_refinement.

Definition stage3_defeq_step (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (g : context) (t s : expr) : result bool :=
  let rec := inference_only rec in
  quick <- core_quick rec fuel g t s ;;
  match quick with
  | Some ok => Accept ok
  | None =>
    shortcut <- stage3_true_shortcut rec env g t s ;;
    if shortcut then Accept true else
    irrelevant <- core_proof_irrel rec fuel g t s ;;
    match irrelevant with
    | Some ok => Accept ok
    | None =>
      tn <- whnf_core_method rec true g t ;;
      sn <- whnf_core_method rec true g s ;;
      progress <- stage3_lazy_delta (S fuel) rec fuel env ps g tn sn ;;
      match progress with
      | ConversionDone ok => Accept ok
      | ConversionStuck tn sn => core_finish_conversion rec fuel env g tn sn
      end
    end
  end.

Theorem guard_order_defeq_step_exact rec fuel env ps g t s :
  defeq_step rec fuel env ps g t s = stage3_defeq_step rec fuel env ps g t s.
Proof.
  unfold defeq_step, stage3_defeq_step.
  pointwise.
Qed.

Theorem accessor_guard_order_step_exact resolve env
    (lookup_correct : forall n, resolve n env = find_decl n env)
    a b fuel ps g t s : methods_equivalent a b ->
  Accessor.defeq_step resolve a fuel env ps g t s = stage3_defeq_step b fuel env ps g t s.
Proof.
  intro Hm. rewrite (defeq_step_refines resolve env lookup_correct a b fuel ps g t s Hm).
  apply guard_order_defeq_step_exact.
Qed.

Print Assumptions guard_order_lazy_delta_exact.
Print Assumptions guard_order_true_shortcut_exact.
Print Assumptions guard_order_defeq_step_exact.
Print Assumptions accessor_guard_order_step_exact.
