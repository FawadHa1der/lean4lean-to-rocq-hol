(* SPDX-License-Identifier: Apache-2.0
   Computational examples, not assumptions about fixture validity. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Checker Primitives DagScope DagArena
  IndexedDagAdmission CombinedAdmissionRefinement LookupIntegration PreparedDagLookup
  RuntimeChecker MetadataFixtures MetadataCases.
Import ListNotations.
Module M := Metadata.
Module T := MetadataCases.

Example all_setup_admissions_succeed :
  map (fun r => r <- r ;; Accept (List.length r))
    [M.padded_env;M.nat_env;M.eq_env;M.structure_env;M.base_env;M.with_add] =
  [Accept 64;Accept 68;Accept 71;Accept 77;Accept 81;Accept 82].
Proof. vm_compute. reflexivity. Qed.

Example fixtures_have_genuine_index_and_dependent_fields :
  M.fixture_shape_checks = Accept true.
Proof. vm_compute. reflexivity. Qed.

Example all_positive_gates_use_the_index :
  Forall (fun c => (env <- T.case_env c ;; Accept (use_index M.fuel env)) = Accept true) T.positives.
Proof.
  repeat (apply Forall_cons; [vm_compute; reflexivity|]). constructor.
Qed.

Example positive_full_installations :
  Forall (fun c =>
    (env <- T.case_env c ;; T.forced 128 env c) = (env <- T.case_env c ;; T.expected env c) /\
    (env <- T.case_env c ;; T.guarded 128 env c) = (env <- T.case_env c ;; T.expected env c) /\
    (env <- T.case_env c ;; T.linear_cache_new 128 env c) = (env <- T.case_env c ;; T.expected env c) /\
    (env <- T.case_env c ;; T.ordinary env c) = (env <- T.case_env c ;; T.expected env c)) T.positives.
Proof.
  repeat (apply Forall_cons; [vm_compute; repeat split; reflexivity|]). constructor.
Qed.

Example quotes_retain_the_input :
  map T.check_decoded T.cases = repeat (Accept tt) 20.
Proof. vm_compute. reflexivity. Qed.

Example indexed_direct_reductions :
  Forall (fun item => let '(_,term,expected) := item in
    (env <- M.base_env ;;
      prepared_whnf (prepare_lookup (fun _ => 0%N) env) M.fuel env [] empty_context term) =
    Accept expected /\
    (env <- M.base_env ;;
      prepared_whnf (prepare_lookup suffix_bitfold8 env) M.fuel env [] empty_context term) =
    Accept expected /\
    (env <- M.base_env ;; Checker.whnf M.fuel env [] empty_context term) = Accept expected)
    T.reductions.
Proof.
  repeat (apply Forall_cons; [vm_compute; repeat split; reflexivity|]). constructor.
Qed.

Example authenticated_primitive_is_installed :
  (env <- M.with_add ;; primitive_authenticated M.fuel env PNatAdd) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example authenticated_primitive_reduces :
  (env <- M.with_add ;; prepared_whnf (prepare_lookup (fun _ => 0%N) env)
    M.fuel env [] empty_context M.add_value) = Accept (ELit (LitNat 2)) /\
  (env <- M.with_add ;; prepared_whnf (prepare_lookup suffix_bitfold8 env)
    M.fuel env [] empty_context M.add_value) = Accept (ELit (LitNat 2)) /\
  (env <- M.with_add ;; Checker.whnf M.fuel env [] empty_context M.add_value) =
    Accept (ELit (LitNat 2)).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example exact_negative_admission_payloads :
  map (fun c => env <- T.case_env c ;; T.forced 128 env c) T.negative_cases =
  [Reject NotDefinitionallyEqual;Reject UnknownConstant;Reject MalformedDeclaration;
   Reject UnknownConstant;Reject MalformedDeclaration;Decline UnsupportedExpression;
   Reject MalformedDeclaration;Reject TypeMismatch;Reject TypeMismatch;
   Reject TypeMismatch;Reject MalformedDeclaration].
Proof. vm_compute. reflexivity. Qed.

Example forged_constructor_fields_fail_admission :
  M.rejected_ctor_metadata = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example forged_recursor_rules_fail_admission :
  M.rejected_rec_metadata = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example forged_quotient_signature_fails_admission :
  M.rejected_quot_signature = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example missing_eq_dependency_fails_admission : M.missing_eq_quot = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.

Theorem fixture_routes_refine_full_results budget env c :
  T.forced budget env c = T.linear_cache_new budget env c /\
  T.guarded budget env c = T.linear_cache_new budget env c.
Proof.
  unfold T.forced, T.guarded, T.linear_cache_new.
  destruct (T.quote_pair (T.case_type c) (T.case_body c)) as [[tr br] rs].
  split; [apply combined_indexed_refines_linear_cache_new|apply combined_guarded_refines_linear_cache_new].
Qed.

Print Assumptions positive_full_installations.
Print Assumptions indexed_direct_reductions.
Print Assumptions fixture_routes_refine_full_results.
