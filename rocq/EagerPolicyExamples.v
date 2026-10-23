(* SPDX-License-Identifier: Apache-2.0
   Small executable policy controls, independent of checker integration. *)
From Stdlib Require Import List String.
From LeanPort Require Import Syntax EagerPolicy.
Import ListNotations.

Definition policy_sort := ESort LZero.
Definition policy_hint := EConst eager_reduce_name [].
Definition policy_argument := EApp (EApp policy_hint policy_sort) (EBVar 0).

Example bound_body_is_external : has_external_local (EBVar 0) = true.
Proof. reflexivity. Qed.
Example high_bound_is_external : has_external_local (EBVar 42) = true.
Proof. reflexivity. Qed.
Example named_free_is_external : has_external_local (EFVar NameAnon) = true.
Proof. reflexivity. Qed.
Example identity_is_closed :
  has_external_local (ELam NameAnon BDefault policy_sort (EBVar 0)) = false.
Proof. reflexivity. Qed.
Example outer_reference_is_external :
  has_external_local (ELam NameAnon BDefault policy_sort (EBVar 1)) = true.
Proof. reflexivity. Qed.
Example binder_domain_uses_outer_depth :
  has_external_local (ELam NameAnon BDefault (EBVar 0) (EBVar 0)) = true.
Proof. reflexivity. Qed.
Example nested_binders_are_closed :
  has_external_local (ELam NameAnon BDefault policy_sort
    (ELam NameAnon BDefault policy_sort (EApp (EBVar 1) (EBVar 0)))) = false.
Proof. reflexivity. Qed.
Example nested_outer_reference_is_external :
  has_external_local (ELam NameAnon BDefault policy_sort
    (ELam NameAnon BDefault policy_sort (EBVar 2))) = true.
Proof. reflexivity. Qed.
Example dependent_pi_is_closed :
  has_external_local (EPi NameAnon BDefault policy_sort (EBVar 0)) = false.
Proof. reflexivity. Qed.
Example pi_domain_can_be_external :
  has_external_local (EPi NameAnon BDefault (EBVar 0) (EBVar 0)) = true.
Proof. reflexivity. Qed.
Example let_body_binds_one :
  has_external_local (ELet NameAnon policy_sort policy_sort (EBVar 0) false) = false.
Proof. reflexivity. Qed.
Example let_value_does_not_bind :
  has_external_local (ELet NameAnon policy_sort (EBVar 0) (EBVar 0) false) = true.
Proof. reflexivity. Qed.
Example let_type_does_not_bind :
  has_external_local (ELet NameAnon (EBVar 0) policy_sort (EBVar 0) true) = true.
Proof. reflexivity. Qed.
Example let_body_outer_is_external :
  has_external_local (ELet NameAnon policy_sort policy_sort (EBVar 1) true) = true.
Proof. reflexivity. Qed.
Example metadata_preserves_external : has_external_local (EMData (EBVar 0)) = true.
Proof. reflexivity. Qed.
Example projection_preserves_external :
  has_external_local (EProj NameAnon 0 (EFVar NameAnon)) = true.
Proof. reflexivity. Qed.
Example universe_parameter_is_not_expression_local :
  has_external_local (EConst NameAnon [LParam NameAnon]) = false.
Proof. reflexivity. Qed.
Example no_local_is_not_metavariable_validation :
  has_external_local (EMVar NameAnon) = false.
Proof. reflexivity. Qed.
Example explicit_fvar_under_binder_stays_external :
  has_external_local (ELam NameAnon BDefault policy_sort (EFVar NameAnon)) = true.
Proof. reflexivity. Qed.
Example closed_pair_normal_probes : nat_probe_allowed NormalReduction policy_sort policy_sort = true.
Proof. reflexivity. Qed.
Example normal_open_left_skips : nat_probe_allowed NormalReduction (EBVar 0) policy_sort = false.
Proof. reflexivity. Qed.
Example normal_open_right_skips : nat_probe_allowed NormalReduction policy_sort (EBVar 0) = false.
Proof. reflexivity. Qed.
Example eager_open_pair_probes : nat_probe_allowed EagerReduction (EBVar 0) (EFVar NameAnon) = true.
Proof. reflexivity. Qed.
Example normal_true_open_skips : true_probe_allowed NormalReduction (EBVar 0) = false.
Proof. reflexivity. Qed.
Example normal_true_closed_probes : true_probe_allowed NormalReduction policy_sort = true.
Proof. reflexivity. Qed.
Example eager_true_open_probes : true_probe_allowed EagerReduction (EBVar 0) = true.
Proof. reflexivity. Qed.
Example exact_hint_matches : is_eager_reduce_argument policy_argument = true.
Proof. reflexivity. Qed.
Example bare_hint_does_not_match : is_eager_reduce_argument policy_hint = false.
Proof. reflexivity. Qed.
Example partial_hint_does_not_match :
  is_eager_reduce_argument (EApp policy_hint policy_sort) = false.
Proof. reflexivity. Qed.
Example overapplied_hint_does_not_match :
  is_eager_reduce_argument (EApp policy_argument policy_sort) = false.
Proof. reflexivity. Qed.
Example metadata_wrapped_hint_does_not_match :
  is_eager_reduce_argument (EMData policy_argument) = false.
Proof. reflexivity. Qed.
Example same_short_name_is_not_same_name :
  is_eager_reduce_argument
    (EApp (EApp (EConst (NameStr (NameStr NameAnon "Other"%string)
      "eagerReduce"%string) []) policy_sort) policy_sort) = false.
Proof. reflexivity. Qed.
Example hint_detection_does_not_validate_universes :
  is_eager_reduce_argument
    (EApp (EApp (EConst eager_reduce_name [LMVar NameAnon]) policy_sort) policy_sort) = true.
Proof. reflexivity. Qed.

Print Assumptions identity_is_closed.
Print Assumptions let_value_does_not_bind.
Print Assumptions eager_open_pair_probes.
Print Assumptions hint_detection_does_not_validate_universes.
