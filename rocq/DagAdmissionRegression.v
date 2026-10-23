(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String NArith.
From LeanPort Require Import Syntax Checker Primitives Declarations DagScope DagArena DagAdmission.
Import ListNotations.
Open Scope string_scope.

Definition test_name := NameStr NameAnon "dagDefinition".
Definition test_rows :=
  [(1%positive,DSort LZero); (2%positive,DSort (LSucc LZero));
   (3%positive,DBVar 0); (4%positive,DLam NameAnon BDefault 1 3);
   (5%positive,DPi NameAnon BDefault 1 1);
   (6%positive,DMVar NameAnon); (7%positive,DSort (LParam NameAnon));
   (8%positive,DConst NameAnon [])].
Definition test_decl := {| decl_hints := HintOpaque; decl_name := test_name; decl_params := [];
  decl_type := ESort (LSucc LZero); decl_value := Some (ESort LZero);
  decl_kind_of := DDefinition |}.

Example definition_accepts :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 2 1 = Accept [test_decl].
Proof. vm_compute. reflexivity. Qed.
Example function_definition_accepts :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 5 4 =
  Accept [{| decl_hints := HintOpaque; decl_name := test_name; decl_params := [];
    decl_type := EPi NameAnon BDefault (ESort LZero) (ESort LZero);
    decl_value := Some (ELam NameAnon BDefault (ESort LZero) (EBVar 0));
    decl_kind_of := DDefinition |}].
Proof. vm_compute. reflexivity. Qed.
Example duplicate_precedes_zero_fuel :
  admit_dag_definition HintOpaque 32 0 [test_decl] test_name [] test_rows 2 1 = Reject DuplicateDeclaration.
Proof. reflexivity. Qed.
Example duplicate_universe_precedes_scope_and_fuel :
  admit_dag_definition HintOpaque 32 0 [] test_name [NameAnon;NameAnon] test_rows 3 1 = Reject DuplicateUniverse.
Proof. reflexivity. Qed.
Example header_scope_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 3 1 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example body_scope_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 2 3 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example unknown_universe_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 7 1 = Reject UnknownUniverse.
Proof. vm_compute. reflexivity. Qed.
Example unknown_constant_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 2 8 = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example meta_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 2 6 = Reject MetaVariable.
Proof. vm_compute. reflexivity. Qed.
Example wrong_body_type_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 1 1 = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example safe_reference_to_unsafe_rejects :
  admit_dag_definition HintOpaque 32 16
    [{| decl_hints := HintOpaque; decl_name := NameAnon; decl_params := []; decl_type := ESort (LSucc LZero);
        decl_value := Some (ESort LZero); decl_kind_of := DUnsafe DDefinition |}]
    test_name [] test_rows 2 8 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example fake_nat_shape_rejects :
  admit_dag_definition HintOpaque 32 16 [] core_nat_name [] test_rows 2 1 = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example fake_primitive_signature_preserves_classifier :
  admit_dag_definition HintOpaque 32 16 [] (primitive_name PNatAdd) [] test_rows 2 1 =
  decode_then_admit_definition HintOpaque 16 [] (primitive_name PNatAdd) [] test_rows 2 1.
Proof. apply admit_dag_definition_refines. Qed.
Example semantic_fuel_declines :
  admit_dag_definition HintOpaque 32 0 [] test_name [] test_rows 2 1 = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example optimization_budget_zero_does_not_decline :
  admit_dag_definition HintOpaque 0 16 [] test_name [] test_rows 2 1 = Accept [test_decl].
Proof. vm_compute. reflexivity. Qed.
Example absent_type_root_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 9 1 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example absent_body_root_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] test_rows 2 9 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example malformed_table_precedes_duplicate_header :
  admit_dag_definition HintOpaque 32 16 [test_decl] test_name []
    [(1%positive,DMData 1)] 1 1 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example duplicate_table_id_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name []
    [(1%positive,DSort LZero);(1%positive,DSort LZero)] 1 1 = Reject DuplicateDeclaration.
Proof. reflexivity. Qed.
Example missing_table_child_rejects :
  admit_dag_definition HintOpaque 32 16 [] test_name [] [(1%positive,DMData 2)] 1 1 =
  Reject MalformedDeclaration.
Proof. reflexivity. Qed.

Print Assumptions admit_dag_definition_refines.
