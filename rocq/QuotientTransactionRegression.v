(* SPDX-License-Identifier: Apache-2.0
   Proposed checked-prefix tests. NOT COMPILED OR EXECUTED. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker Declarations Quotient MetadataFixtures
  QuotientTransaction.
Import ListNotations.

Definition transaction_eq_fixture :=
  Metadata.checked_block [] [Metadata.u_name] 2 [Metadata.eq_spec].

Definition transaction_axiom_collision n : result environment :=
  env <- transaction_eq_fixture ;;
  Declarations.admit 256 env (InputAxiom n [] (ESort LZero) false).

Example transaction_checked_eq :
  (env <- transaction_eq_fixture ;; quotient_check_eq env) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Example transaction_ordinary_collisions_reachable :
  forallb (fun n => match transaction_axiom_collision n with
    | Accept _ => true | _ => false end) quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

Example transaction_all_four_collisions_rejected :
  forallb (fun n => match (env <- transaction_axiom_collision n ;;
      initialize_quotient (env, false)) with
    | Reject DuplicateDeclaration => true | _ => false end)
    quotient_transaction_names = true.
Proof. vm_compute. reflexivity. Qed.

Example transaction_adds_four_and_sets_flag :
  (env <- transaction_eq_fixture ;;
   next <- initialize_quotient (env, false) ;;
   Accept (snd next, List.length (fst next) - List.length env)) = Accept (true, 4).
Proof. vm_compute. reflexivity. Qed.

Example transaction_repeat_uses_flag :
  (env <- transaction_eq_fixture ;;
   next <- initialize_quotient (env, false) ;;
   repeated <- initialize_quotient next ;;
   Accept (snd repeated, List.length (fst repeated) - List.length env)) = Accept (true, 4).
Proof. vm_compute. reflexivity. Qed.

Example transaction_partial_family_reachable :
  (env <- transaction_eq_fixture ;;
   let d := canonical_quotient QType in
   partial <- admit_quotient 256 env (decl_name d) (decl_params d) (decl_type d) QType ;;
   Accept (List.length partial - List.length env)) = Accept 1.
Proof. vm_compute. reflexivity. Qed.

Example transaction_partial_family_rejected :
  (env <- transaction_eq_fixture ;;
   let d := canonical_quotient QType in
   partial <- admit_quotient 256 env (decl_name d) (decl_params d) (decl_type d) QType ;;
   initialize_quotient (partial, false)) = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Example transaction_missing_eq :
  initialize_quotient quotient_initial_state = Reject UnknownConstant.
Proof. reflexivity. Qed.

Print Assumptions transaction_all_four_collisions_rejected.
Print Assumptions transaction_adds_four_and_sets_flag.
