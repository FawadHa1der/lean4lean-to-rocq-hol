(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String NArith.
From LeanPort Require Import Syntax Checker DagScope DagTheoremOpaqueRegression
  IndexedDagAdmission RuntimeChecker.
Import ListNotations.
Open Scope string_scope.

(* Same suffix deliberately collides under the fixed hash; numeric parents
   remain distinct structured names. These are synthetic, not Arena claims. *)
Definition filler_name i := NameStr (NameNum NameAnon (N.of_nat i)) "same".
Definition padded := List.app
  (map (fun i => assumed (filler_name i) (ESort LZero)) (seq 0 62)) test_env.
Definition collide (_ : name) := 0%N.

Example guard_63_linear : use_index 16 (tl padded) = false.
Proof. vm_compute. reflexivity. Qed.
Example guard_64_indexed : use_index 16 padded = true.
Proof. vm_compute. reflexivity. Qed.
Example guard_no_fuel_linear : use_index 0 padded = false.
Proof. reflexivity. Qed.
Example indexed_theorem_accepts :
  indexed_admit_dag_theorem 32 16 padded new_name [] test_rows 3 4 =
  Accept (installed DTheorem p_expr h_expr :: padded).
Proof. vm_compute. reflexivity. Qed.
Example indexed_opaque_accepts :
  indexed_admit_dag_opaque 32 16 padded new_name [] test_rows 3 4 =
  Accept (installed DOpaque p_expr h_expr :: padded).
Proof. vm_compute. reflexivity. Qed.
Example indexed_definition_accepts :
  indexed_admit_dag_definition HintOpaque 32 16 padded new_name [] test_rows 3 4 =
  Accept (installed DDefinition p_expr h_expr :: padded).
Proof. vm_compute. reflexivity. Qed.
Example indexed_budget_zero_falls_back :
  indexed_admit_dag_theorem 0 16 padded new_name [] test_rows 3 4 =
  Accept (installed DTheorem p_expr h_expr :: padded).
Proof. vm_compute. reflexivity. Qed.
Example collision_hash_still_accepts :
  indexed_admit collide DagTheorem 32 16 padded new_name [] test_rows 3 4 =
  Accept (installed DTheorem p_expr h_expr :: padded).
Proof. vm_compute. reflexivity. Qed.
Example absent_constant_rejects :
  indexed_admit_dag_theorem 32 16 padded new_name [] test_rows 3 11 = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example shadowed_unsafe_rejects :
  indexed_admit_dag_theorem 32 16
    ({| decl_hints := HintOpaque; decl_name := h_name; decl_params := []; decl_type := p_expr;
        decl_value := None; decl_kind_of := DUnsafe DAssumption |} :: padded)
    new_name [] test_rows 3 4 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_before_fuel :
  indexed_admit_dag_theorem 32 0 padded h_name [] test_rows 3 4 = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example reserved_before_fuel :
  indexed_admit_dag_theorem 32 0 padded core_nat_name [] test_rows 3 4 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example body_mismatch_rejects :
  indexed_admit_dag_opaque 32 16 padded new_name [] test_rows 3 1 = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example nonproposition_rejects :
  indexed_admit_dag_theorem 32 16 padded new_name [] test_rows 2 1 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example absent_nat_gate_declines :
  indexed_admit_dag_opaque 32 16 padded new_name [] test_rows 3 9 = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_row_precedes_lookup :
  indexed_admit_dag_theorem 32 16 padded new_name []
    [(1%positive, DSort LZero); (1%positive, DSort LZero)] 1 1 = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions indexed_dag_admit_refines.
