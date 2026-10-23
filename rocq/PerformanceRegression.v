(* SPDX-License-Identifier: Apache-2.0
   Conversion-strategy regressions use ordinary well-typed kernel fixtures.
   Fuel is deliberately too small to evaluate the delayed definitions. *)
From Coq Require Import List Bool NArith String.
From LeanPort Require Import Syntax Universes Checker Regression ExtensionRegression.
Import ListNotations.
Open Scope string_scope.

Fixpoint perf_delay (n : nat) (value : expr) : expr :=
  match n with
  | 0 => value
  | S n => ELet NameAnon core_nat (ELit (LitNat 0))
      (perf_delay n (lift 1 0 value)) false
  end.
Definition perf_arrow := EPi NameAnon BDefault core_nat core_nat.
Definition perf_slow := nm "slow".
Definition perf_slow_opaque := ext_decl perf_slow perf_arrow DDefinition
  (Some (ELam NameAnon BDefault core_nat (perf_delay 80 (EBVar 0)))).
(* This fixture exercises the upstream equal-Regular congruence guard. *)
Definition perf_slow_decl :=
  {| decl_name := decl_name perf_slow_opaque; decl_params := [];
     decl_type := decl_type perf_slow_opaque; decl_value := decl_value perf_slow_opaque;
     decl_kind_of := DDefinition; decl_hints := HintRegular 0 |}.
Definition perf_env := perf_slow_decl :: ext_nat_env.
Definition perf_two := ELit (LitNat 2).
Definition perf_beta_two := EApp (ELam NameAnon BDefault core_nat (EBVar 0)) perf_two.
Definition perf_app (arg : expr) := EApp (EConst perf_slow []) arg.

Example conservative_whnf_preserves_definition :
  whnf_core_method (checker 24 perf_env []) true empty_context (perf_app perf_two) =
    Accept (perf_app perf_two).
Proof. vm_compute. reflexivity. Qed.
Example eager_evaluation_exhausts_fixture_fuel :
  whnf 24 perf_env [] empty_context (perf_app perf_two) = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example arguments_compared_before_delta :
  check_defeq 24 perf_env [] empty_context
    (perf_app perf_two) (perf_app perf_beta_two) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example opaque_hint_does_not_get_regular_congruence :
  check_defeq 24 (perf_slow_opaque :: ext_nat_env) [] empty_context
    (perf_app perf_two) (perf_app perf_beta_two) = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

Definition perf_discard := nm "discard".
Definition perf_discard_decl := ext_decl perf_discard perf_arrow DDefinition
  (Some (ELam NameAnon BDefault core_nat perf_two)).
Example failed_congruence_still_unfolds :
  check_defeq 24 (perf_discard_decl :: ext_nat_env) [] empty_context
    (EApp (EConst perf_discard []) (ELit (LitNat 0)))
    (EApp (EConst perf_discard []) (ELit (LitNat 1))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example erased_argument_is_not_evaluated_speculatively :
  check_defeq 24 (perf_discard_decl :: ext_nat_env) [] empty_context
    (EApp (EConst perf_discard []) (perf_delay 80 perf_two))
    (EApp (EConst perf_discard []) (ELit (LitNat 0))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition perf_prop := nm "PerfProp".
Definition perf_proof := nm "PerfProof".
Definition perf_slow_proof := nm "SlowProof".
Definition perf_proof_type := EConst perf_prop [].
Definition perf_proof_env :=
  List.app [ext_decl perf_slow_proof perf_proof_type DTheorem
     (Some (perf_delay 80 (EConst perf_proof [])));
   ext_decl perf_proof perf_proof_type DAssumption None;
   ext_decl perf_prop prop DAssumption None] ext_nat_env.
Example proof_irrelevance_precedes_evaluation :
  check_defeq 24 perf_proof_env [] empty_context
    (EConst perf_slow_proof []) (EConst perf_proof []) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example delayed_theorem_still_delta_unfolds :
  whnf 24 perf_proof_env [] empty_context (EConst perf_slow_proof []) = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

Fixpoint perf_succs (n : nat) : expr :=
  match n with
  | 0 => ELit (LitNat 0)
  | S n => EApp (EConst core_succ_name []) (perf_succs n)
  end.
Example structural_inference_does_not_spend_reduction_fuel :
  infer 8 ext_nat_env [] empty_context (perf_succs 1000) = Accept core_nat.
Proof. vm_compute. reflexivity. Qed.
Example checked_inference_still_checks_discarded_arguments :
  infer 24 (perf_discard_decl :: ext_nat_env) [] empty_context
    (EApp (EConst perf_discard []) prop) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example alpha_budget_failure_is_inconclusive :
  core_alpha 0 prop prop = (false, 0).
Proof. reflexivity. Qed.
Example alpha_compares_binder_names_irrelevantly :
  fst (core_alpha 3 (ELam (nm "x") BDefault prop (EBVar 0))
    (ELam (nm "y") BImplicit prop (EBVar 0))) = true.
Proof. reflexivity. Qed.
Example lazy_delta_fuel_exhaustion_declines :
  core_lazy_delta 0 (checker 24 perf_env []) 24 perf_env [] empty_context
    (perf_app perf_two) perf_two = Decline OutOfFuel.
Proof. reflexivity. Qed.

Definition perf_fnbox := nm "FnBox".
Definition perf_fnmk := NameStr perf_fnbox "mk".
Definition perf_fnind := ext_decl perf_fnbox type0
  (DInductive (ext_ind perf_fnbox [perf_fnmk] false)) None.
Definition perf_fnctor := ext_decl perf_fnmk
  (EPi NameAnon BDefault perf_arrow (EConst perf_fnbox []))
  (DConstructor (ext_ctor perf_fnbox 0 1)) None.
Definition perf_fnvalue := EApp (EConst perf_fnmk [])
  (ELam NameAnon BDefault core_nat (EBVar 0)).
Definition perf_fnalias := ext_decl (nm "FnAlias") (EConst perf_fnbox [])
  DDefinition (Some perf_fnvalue).
Definition perf_fnenv := perf_fnalias :: perf_fnctor :: perf_fnind :: ext_nat_env.
Definition perf_fnapp := EApp (EProj perf_fnbox 0 (EConst (nm "FnAlias") [])) perf_two.
Example full_projection_retry_at_application_head :
  check_defeq 64 perf_fnenv [] empty_context perf_fnapp perf_two = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition perf_peano := nm "Peano".
Definition perf_zero := NameNum perf_peano 0.
Definition perf_succ := NameNum perf_peano 1.
Definition perf_peano_type := EConst perf_peano [].
Definition perf_peano_env :=
  [ext_decl perf_succ (EPi NameAnon BDefault perf_peano_type perf_peano_type)
     (DConstructor (ext_ctor perf_peano 1 1)) None;
   ext_decl perf_zero perf_peano_type (DConstructor (ext_ctor perf_peano 0 0)) None;
   ext_decl perf_peano type0
     (DInductive (ext_ind perf_peano [perf_zero; perf_succ] true)) None].
Fixpoint perf_peano_numeral (n : nat) : expr :=
  match n with
  | 0 => EConst perf_zero []
  | S n => EApp (EConst perf_succ []) (perf_peano_numeral n)
  end.
Example rigid_heads_do_not_speculate_on_arguments :
  core_delta_congruent (checker 0 perf_peano_env []) 32 perf_peano_env empty_context
    (perf_peano_numeral 16) (perf_peano_numeral 17) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example constructor_mismatch_without_repeated_speculation :
  defeq 32 perf_peano_env [] empty_context
    (perf_peano_numeral 16) (perf_peano_numeral 17) = Accept false.
Proof. vm_compute. reflexivity. Qed.

Example simultaneous_values_are_innermost_first :
  instantiate_many (EApp (EBVar 1) (EBVar 0)) [EBVar 3; EBVar 5] =
    EApp (EBVar 5) (EBVar 3).
Proof. reflexivity. Qed.
Example simultaneous_outer_variable_is_lowered :
  instantiate_many (EBVar 4) [perf_two; perf_two] = EBVar 2.
Proof. reflexivity. Qed.
Example simultaneous_substitution_avoids_capture :
  instantiate_many (ELam NameAnon BDefault (EBVar 1)
    (EApp (EBVar 2) (EApp (EBVar 1) (EBVar 0)))) [EBVar 3; EBVar 5] =
  ELam NameAnon BDefault (EBVar 5) (EApp (EBVar 6) (EApp (EBVar 4) (EBVar 0))).
Proof. reflexivity. Qed.
Example simultaneous_substitution_respects_cutoff :
  subst_many 1 [perf_two; EBVar 2]
    (EApp (EBVar 0) (EApp (EBVar 2) (EBVar 4))) =
    EApp (EBVar 0) (EApp (EBVar 3) (EBVar 2)).
Proof. reflexivity. Qed.
Example simultaneous_metadata_projection_let :
  instantiate_many (EMData (EProj perf_fnbox 0
    (ELet NameAnon (EBVar 1) (EBVar 0) (EApp (EBVar 2) (EBVar 0)) false)))
    [perf_two; EBVar 0] =
    EMData (EProj perf_fnbox 0
      (ELet NameAnon (EBVar 0) perf_two (EApp (EBVar 1) (EBVar 0)) false)).
Proof. reflexivity. Qed.

Definition perf_batch_function := ELam NameAnon BDefault perf_arrow
  (ELam NameAnon BDefault core_nat (EApp (EBVar 1) (EBVar 0))).
Example batch_beta_consumes_visible_binders :
  core_beta perf_batch_function [EBVar 0; EBVar 1] = EApp (EBVar 0) (EBVar 1).
Proof. reflexivity. Qed.
Example batch_beta_leaves_generated_redex_for_whnf :
  core_beta (ELam NameAnon BDefault perf_arrow (EBVar 0))
    [ELam NameAnon BDefault core_nat (EBVar 0); perf_two] = perf_beta_two.
Proof. reflexivity. Qed.
Example batch_beta_open_arguments_do_not_capture :
  let g := push_binding empty_context core_nat None in
  whnf 12 ext_nat_env [] g
    (core_apps perf_batch_function [ELam NameAnon BDefault core_nat (EBVar 1); perf_two]) =
    Accept (EBVar 0).
Proof. vm_compute. reflexivity. Qed.

Definition performance_checks (_ : unit) : list bool :=
  [accepted (check_defeq 24 perf_env [] empty_context
     (perf_app perf_two) (perf_app perf_beta_two));
   declined (whnf 24 perf_env [] empty_context (perf_app perf_two));
   accepted (check_defeq 24 perf_proof_env [] empty_context
     (EConst perf_slow_proof []) (EConst perf_proof []));
   accepted (infer 8 ext_nat_env [] empty_context (perf_succs 1000));
   rejected (infer 24 (perf_discard_decl :: ext_nat_env) [] empty_context
     (EApp (EConst perf_discard []) prop));
   accepted (check_defeq 64 perf_fnenv [] empty_context perf_fnapp perf_two);
   match defeq 32 perf_peano_env [] empty_context
     (perf_peano_numeral 16) (perf_peano_numeral 17) with
   | Accept false => true | _ => false end;
   accepted (check_defeq 24 (perf_discard_decl :: ext_nat_env) [] empty_context
     (EApp (EConst perf_discard []) (perf_delay 80 perf_two))
     (EApp (EConst perf_discard []) (ELit (LitNat 0))));
   expr_eqb (core_beta perf_batch_function [EBVar 0; EBVar 1]) (EApp (EBVar 0) (EBVar 1));
   match whnf 12 ext_nat_env [] (push_binding empty_context core_nat None)
     (core_apps perf_batch_function [ELam NameAnon BDefault core_nat (EBVar 1); perf_two]) with
   | Accept e => expr_eqb e (EBVar 0) | _ => false end].
