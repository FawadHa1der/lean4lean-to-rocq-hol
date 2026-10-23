(* SPDX-License-Identifier: Apache-2.0
   Proposed regression SOURCE only: no computation/proof has been executed.
   Reuse the preserved761 checked Eq, collision, and partial-family fixtures. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker Declarations Quotient MetadataFixtures
  AdmissionDelta QuotientTransaction QuotientTransactionRegression
  QuotientTransactionDelta.
Import ListNotations.

Example delta_fixture_checks_eq_and_freshness :
  (env <- transaction_eq_fixture ;;
   _ <- quotient_check_eq env ;;
   Accept (quotient_names_fresh env quotient_transaction_names)) = Accept true.
Proof. vm_compute. reflexivity. Qed.

Example delta_first_payload_is_exact_block :
  (env <- transaction_eq_fixture ;; initialize_quotient_delta (env, false)) =
  Accept (canonical_quotient_block, true).
Proof. vm_compute. reflexivity. Qed.

Example delta_first_payload_order :
  (env <- transaction_eq_fixture ;;
   payload <- initialize_quotient_delta (env, false) ;;
   Accept (map decl_name (fst payload))) = Accept [q_ind_name; q_lift_name; q_mk_name; q_name].
Proof. vm_compute. reflexivity. Qed.

Example delta_first_payload_length_four :
  (env <- transaction_eq_fixture ;;
   payload <- initialize_quotient_delta (env, false) ;;
   Accept (List.length (fst payload))) = Accept 4.
Proof. vm_compute. reflexivity. Qed.

Example delta_repeat_payload_empty :
  (env <- transaction_eq_fixture ;;
   next <- quotient_delta_step (env, false) ;;
   initialize_quotient_delta next) = Accept ([], true).
Proof. vm_compute. reflexivity. Qed.

Example delta_repeat_preserves_complete_state :
  (env <- transaction_eq_fixture ;;
   next <- quotient_delta_step (env, false) ;; quotient_delta_step next) =
  (env <- transaction_eq_fixture ;; quotient_delta_step (env, false)).
Proof. vm_compute. reflexivity. Qed.

(* Counterexamples to routing the transaction through single_delta. These are
   intentionally wrong adapter outputs, not accepted new-interface behavior. *)
Example legacy_firstn_one_loses_three :
  (env <- transaction_eq_fixture ;;
   added <- single_delta (result_map fst (initialize_quotient (env, false))) ;;
   Accept (List.length added)) = Accept 1.
Proof. vm_compute. reflexivity. Qed.

Example legacy_firstn_one_copies_old_head_on_repeat :
  (env <- transaction_eq_fixture ;;
   next <- quotient_delta_step (env, false) ;;
   added <- single_delta (result_map fst (initialize_quotient next)) ;;
   Accept (List.length added)) = Accept 1.
Proof. vm_compute. reflexivity. Qed.

Example delta_missing_eq_has_no_payload :
  initialize_quotient_delta quotient_initial_state = Reject UnknownConstant.
Proof. reflexivity. Qed.

Example delta_missing_eq_keeps_state_and_flag :
  quotient_delta_transaction quotient_initial_state =
  (quotient_initial_state, Reject UnknownConstant).
Proof. reflexivity. Qed.

Example delta_each_collision_fixture_reachable :
  forallb (fun n => match transaction_axiom_collision n with
    | Accept _ => true | _ => false end) quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

Example delta_each_collision_has_no_payload :
  forallb (fun n => match (env <- transaction_axiom_collision n ;;
      initialize_quotient_delta (env, false)) with
    | Reject DuplicateDeclaration => true | _ => false end)
    quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

Example delta_collision_preserves_exact_state :
  (env <- transaction_axiom_collision q_name ;;
   Accept (quotient_delta_transaction (env, false))) =
  (env <- transaction_axiom_collision q_name ;;
   Accept ((env, false), (Reject DuplicateDeclaration : result unit))).
Proof. vm_compute. reflexivity. Qed.

Definition delta_partial_fixture : result environment :=
  env <- transaction_eq_fixture ;;
  let d := canonical_quotient QType in
  admit_quotient 256 env (decl_name d) (decl_params d) (decl_type d) QType.

Example delta_partial_fixture_reachable :
  (env <- transaction_eq_fixture ;;
   let d := canonical_quotient QType in
   next <- admit_quotient 256 env (decl_name d) (decl_params d) (decl_type d) QType ;;
   Accept (List.length next - List.length env)) = Accept 1.
Proof. vm_compute. reflexivity. Qed.

Example delta_partial_family_has_no_payload :
  (env <- delta_partial_fixture ;; initialize_quotient_delta (env, false)) =
  Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Definition delta_collision_without_eq : result environment :=
  Declarations.admit 256 [] (InputAxiom q_name [] (ESort LZero) false).

Example delta_error_order_fixture_reachable :
  (env <- delta_collision_without_eq ;; Accept (List.length env)) = Accept 1.
Proof. vm_compute. reflexivity. Qed.

Example delta_eq_failure_precedes_collision :
  (env <- delta_collision_without_eq ;; initialize_quotient_delta (env, false)) =
  Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.

(* The row API stays separate: a well-formed header is not necessarily the
   canonical quotient signature, and fuel decline must remain distinguishable. *)
Example delta_noncanonical_row_passes_general_header :
  (env <- transaction_eq_fixture ;;
   check_header 256 env q_name [Metadata.u_name] (ESort LZero)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Example delta_noncanonical_exported_row_still_rejected :
  (env <- transaction_eq_fixture ;;
   admit_quotient 256 env q_name [Metadata.u_name] (ESort LZero) QType) =
  Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Example delta_exported_header_fuel_decline_preserved :
  (env <- transaction_eq_fixture ;;
   let d := canonical_quotient QType in
   admit_quotient 0 env (decl_name d) (decl_params d) (decl_type d) QType) =
  Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions delta_first_payload_is_exact_block.
Print Assumptions delta_repeat_preserves_complete_state.
Print Assumptions delta_each_collision_has_no_payload.
Print Assumptions delta_collision_preserves_exact_state.
Print Assumptions delta_noncanonical_exported_row_still_rejected.
