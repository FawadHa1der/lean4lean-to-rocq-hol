(* SPDX-License-Identifier: Apache-2.0
   SOURCE-ONLY proposed regressions; no prover or computation has run.
   Fixture constructors are test-only and use checked environment results.
   They do not constitute a transport constructor or a full reachability proof. *)
From Stdlib Require Import List NArith Bool.
From LeanPort Require Import Syntax Quotient EnvironmentIndex RuntimeChecker PersistentIndex
  AdmissionDelta QuotientTransaction QuotientTransactionRegression
  QuotientTransactionDelta QuotientTransactionDeltaRegression QuotientPersistentIndex.
Import ListNotations.

Definition quotient_index_fixture (hash : name -> N)
    : result (quotient_indexed_state hash) :=
  env <- transaction_eq_fixture ;;
  Accept {| quotient_indexed_base := seed_state hash env;
            quotient_indexed_initialized := false |}.

Definition quotient_index_collision_fixture (n : name) : result quotient_runtime_state :=
  env <- transaction_axiom_collision n ;;
  Accept {| quotient_indexed_base := seed_state suffix_bitfold8 env;
            quotient_indexed_initialized := false |}.

Definition quotient_index_partial_fixture : result quotient_runtime_state :=
  env <- delta_partial_fixture ;;
  Accept {| quotient_indexed_base := seed_state suffix_bitfold8 env;
            quotient_indexed_initialized := false |}.

Definition quotient_index_kinds := [QType; QCtor; QLift; QInd].

Example index_fixture_passes_eq_and_freshness :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   _ <- quotient_check_eq (fst (quotient_indexed_project s)) ;;
   Accept (quotient_indexed_initialized s,
     quotient_names_fresh (fst (quotient_indexed_project s)) quotient_transaction_names)) =
  Accept (false, true).
Proof. vm_compute. reflexivity. Qed.

Example index_first_success_adds_four_and_sets_flag :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;;
   Accept (List.length (fst (quotient_indexed_project next)) -
     List.length (fst (quotient_indexed_project s)), quotient_indexed_initialized next)) =
  Accept (4, true).
Proof. vm_compute. reflexivity. Qed.

Example index_first_success_keeps_prefix_order :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;;
   Accept (map decl_name (firstn 4 (fst (quotient_indexed_project next))))) =
  Accept [q_ind_name; q_lift_name; q_mk_name; q_name].
Proof. vm_compute. reflexivity. Qed.

Example index_all_four_canonical_lookups :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;;
   Accept (map (fun kind => state_lookup (quotient_indexed_base next)
     (decl_name (canonical_quotient kind))) quotient_index_kinds)) =
  Accept (map (fun kind => Some (canonical_quotient kind)) quotient_index_kinds).
Proof. vm_compute. reflexivity. Qed.

Example index_constant_hash_keeps_all_four :
  (s <- quotient_index_fixture (fun _ => 0%N) ;;
   next <- quotient_indexed_step s ;;
   Accept (map (fun kind => state_lookup (quotient_indexed_base next)
     (decl_name (canonical_quotient kind))) quotient_index_kinds)) =
  Accept (map (fun kind => Some (canonical_quotient kind)) quotient_index_kinds).
Proof. vm_compute. reflexivity. Qed.

Example index_old_eq_lookup_positive_control :
  (s <- quotient_index_fixture (fun _ => 0%N) ;;
   Accept (match state_lookup (quotient_indexed_base s) q_eq_name with
     | Some _ => true | None => false end)) = Accept true.
Proof. vm_compute. reflexivity. Qed.

Example index_constant_hash_preserves_old_eq_lookup :
  (s <- quotient_index_fixture (fun _ => 0%N) ;;
   next <- quotient_indexed_step s ;;
   Accept (state_lookup (quotient_indexed_base next) q_eq_name)) =
  (s <- quotient_index_fixture (fun _ => 0%N) ;;
   Accept (state_lookup (quotient_indexed_base s) q_eq_name)).
Proof. vm_compute. reflexivity. Qed.

Example index_repeat_preserves_exact_index_data :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;; again <- quotient_indexed_step next ;;
   Accept (state_index (quotient_indexed_base again))) =
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;; Accept (state_index (quotient_indexed_base next))).
Proof. vm_compute. reflexivity. Qed.

Example index_repeat_preserves_environment_and_flag :
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;; again <- quotient_indexed_step next ;;
   Accept (quotient_indexed_project again)) =
  (s <- quotient_index_fixture suffix_bitfold8 ;;
   next <- quotient_indexed_step s ;; Accept (quotient_indexed_project next)).
Proof. vm_compute. reflexivity. Qed.

Example index_empty_missing_eq_rejects :
  quotient_indexed_step quotient_runtime_initial = Reject UnknownConstant.
Proof. reflexivity. Qed.

Example index_empty_failure_returns_exact_old_state :
  quotient_runtime_initialize quotient_runtime_initial =
  (quotient_runtime_initial, Reject UnknownConstant).
Proof. reflexivity. Qed.

Example index_all_collision_fixtures_reachable :
  forallb (fun n => match quotient_index_collision_fixture n with
    | Accept _ => true | _ => false end) quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

Example index_all_four_collisions_reject :
  forallb (fun n => match (s <- quotient_index_collision_fixture n ;;
      quotient_indexed_step s) with
    | Reject DuplicateDeclaration => true | _ => false end)
    quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

(* Quot.ind is the last freshness check: no earlier checked prefix is committed. *)
Example index_late_collision_returns_exact_old_record :
  (s <- quotient_index_collision_fixture q_ind_name ;;
   Accept (quotient_runtime_initialize s)) =
  (s <- quotient_index_collision_fixture q_ind_name ;;
   Accept (s, (Reject DuplicateDeclaration : result unit))).
Proof. vm_compute. reflexivity. Qed.

Example index_partial_family_positive_control :
  (s <- quotient_index_partial_fixture ;;
   Accept (quotient_indexed_initialized s,
     quotient_dependency (fst (quotient_indexed_project s)) QType)) = Accept (false, true).
Proof. vm_compute. reflexivity. Qed.

Example index_partial_family_rejects_without_fill_in :
  (s <- quotient_index_partial_fixture ;; quotient_indexed_step s) =
  Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions index_all_four_canonical_lookups.
Print Assumptions index_constant_hash_keeps_all_four.
Print Assumptions index_repeat_preserves_exact_index_data.
Print Assumptions index_late_collision_returns_exact_old_record.
