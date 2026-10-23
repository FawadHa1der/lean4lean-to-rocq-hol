(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String NArith.
From LeanPort Require Import Syntax Checker Declarations DagScope DagTheoremOpaque.
Import ListNotations.
Open Scope string_scope.

Definition p_name := NameStr NameAnon "TestP".
Definition h_name := NameStr NameAnon "testProof".
Definition new_name := NameStr NameAnon "dagValue".
Definition p_expr := EConst p_name [].
Definition h_expr := EConst h_name [].
Definition assumed n ty := {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := ty;
  decl_value := None; decl_kind_of := DAssumption |}.
Definition test_env := [assumed h_name p_expr; assumed p_name (ESort LZero)].
Definition test_rows :=
  [(1%positive,DSort LZero); (2%positive,DSort (LSucc LZero));
   (3%positive,DConst p_name []); (4%positive,DConst h_name []);
   (5%positive,DBVar 0); (6%positive,DMVar NameAnon);
   (7%positive,DSort (LParam NameAnon)); (8%positive,DFVar NameAnon);
   (9%positive,DLit (LitNat 1)); (10%positive,DProj NameAnon 0 4);
   (11%positive,DConst new_name [])].
Definition installed kind ty value := {| decl_hints := HintOpaque; decl_name := new_name; decl_params := [];
  decl_type := ty; decl_value := Some value; decl_kind_of := kind |}.

Example theorem_accepts :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 4 =
  Accept (installed DTheorem p_expr h_expr :: test_env).
Proof. vm_compute. reflexivity. Qed.
Example opaque_proof_accepts :
  admit_dag_opaque 32 16 test_env new_name [] test_rows 3 4 =
  Accept (installed DOpaque p_expr h_expr :: test_env).
Proof. vm_compute. reflexivity. Qed.
Example opaque_nonprop_accepts :
  admit_dag_opaque 32 16 [] new_name [] test_rows 2 1 =
  Accept [installed DOpaque (ESort (LSucc LZero)) (ESort LZero)].
Proof. vm_compute. reflexivity. Qed.
Example theorem_nonprop_rejects_even_well_typed_body :
  admit_dag_theorem 32 16 [] new_name [] test_rows 2 1 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example theorem_type_prop_itself_is_not_a_proposition :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 1 3 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example theorem_nonprop_guard_precedes_bad_body_scope :
  admit_dag_theorem 32 16 [] new_name [] test_rows 2 5 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example theorem_wrong_body_rejects :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 1 = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example opaque_wrong_body_rejects :
  admit_dag_opaque 32 16 [] new_name [] test_rows 1 1 = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example theorem_loose_type_rejects :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 5 4 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example opaque_loose_body_rejects :
  admit_dag_opaque 32 16 [] new_name [] test_rows 2 5 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example theorem_meta_body_rejects :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 6 = Reject MetaVariable.
Proof. vm_compute. reflexivity. Qed.
Example opaque_unknown_universe_rejects :
  admit_dag_opaque 32 16 [] new_name [] test_rows 7 1 = Reject UnknownUniverse.
Proof. vm_compute. reflexivity. Qed.
Example theorem_no_self_reference :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 11 = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example opaque_no_self_reference :
  admit_dag_opaque 32 16 test_env new_name [] test_rows 3 11 = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example theorem_missing_free_variable_rejects :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 8 = Reject UnknownFreeVariable.
Proof. vm_compute. reflexivity. Qed.
Example opaque_nontype_header_rejects :
  admit_dag_opaque 32 16 test_env new_name [] test_rows 4 4 = Reject ExpectedSort.
Proof. vm_compute. reflexivity. Qed.
Example theorem_unsupported_literal_declines :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 3 9 = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example opaque_unsupported_projection_declines :
  admit_dag_opaque 32 16 test_env new_name [] test_rows 3 10 = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example theorem_no_fuel_declines :
  admit_dag_theorem 32 0 test_env new_name [] test_rows 3 4 = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example opaque_no_fuel_declines :
  admit_dag_opaque 32 0 test_env new_name [] test_rows 3 4 = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example theorem_duplicate_precedes_no_fuel :
  admit_dag_theorem 32 0 test_env h_name [] test_rows 3 4 = Reject DuplicateDeclaration.
Proof. reflexivity. Qed.
Example opaque_duplicate_parameters_precede_no_fuel :
  admit_dag_opaque 32 0 [] new_name [NameAnon;NameAnon] test_rows 2 1 = Reject DuplicateUniverse.
Proof. reflexivity. Qed.
Example theorem_reserved_name_precedes_header :
  admit_dag_theorem 32 0 [assumed nat_name (ESort LZero)] nat_name [] test_rows 2 1 =
  Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example opaque_reserved_name_precedes_header :
  admit_dag_opaque 32 0 [] nat_name [] test_rows 2 1 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example theorem_zero_budget_accepts :
  admit_dag_theorem 0 16 test_env new_name [] test_rows 3 4 =
  Accept (installed DTheorem p_expr h_expr :: test_env).
Proof. vm_compute. reflexivity. Qed.
Example opaque_all_budgets_equal n m fuel env ps rows tr br :
  admit_dag_opaque n fuel env new_name ps rows tr br =
  admit_dag_opaque m fuel env new_name ps rows tr br.
Proof. rewrite !admit_dag_opaque_refines. reflexivity. Qed.
Example theorem_missing_type_root_rejects :
  admit_dag_theorem 32 16 test_env new_name [] test_rows 12 4 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example opaque_missing_body_root_rejects :
  admit_dag_opaque 32 16 test_env new_name [] test_rows 3 12 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example theorem_bad_rows_precede_reserved_name :
  admit_dag_theorem 32 0 [] nat_name [] [(1%positive,DMData 1)] 1 1 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example opaque_duplicate_id_rejects :
  admit_dag_opaque 32 16 [] new_name [] [(1%positive,DSort LZero);(1%positive,DSort LZero)] 1 1 =
  Reject DuplicateDeclaration.
Proof. reflexivity. Qed.
Example theorem_unfolds_at_pinned_reference :
  (env <- admit_dag_theorem 32 16 test_env new_name [] test_rows 3 4 ;;
   whnf 16 env [] empty_context (EConst new_name [])) = Accept h_expr.
Proof. vm_compute. reflexivity. Qed.
Example opaque_does_not_unfold :
  (env <- admit_dag_opaque 32 16 test_env new_name [] test_rows 3 4 ;;
   whnf 16 env [] empty_context (EConst new_name [])) = Accept (EConst new_name []).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions admit_dag_theorem_refines.
Print Assumptions admit_dag_opaque_refines.
