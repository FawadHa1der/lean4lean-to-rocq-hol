(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String.
From LeanPort Require Import Syntax Checker Declarations InductiveUtils Inductive
  NestedAdmission Safety InductiveSafety InductiveRegression.
Import ListNotations.
Open Scope string_scope.

Definition set_inductive_safety (unsafe : bool) (d : declaration) : declaration :=
  let kind := match decl_kind_of d with
  | DInductive i => DInductive {| ind_num_params := ind_num_params i;
      ind_num_indices := ind_num_indices i; ind_all := ind_all i;
      ind_ctors := ind_ctors i; ind_num_nested := ind_num_nested i;
      ind_is_rec := ind_is_rec i; ind_is_reflexive := ind_is_reflexive i;
      ind_is_unsafe := unsafe |}
  | DConstructor c => DConstructor {| ctor_induct := ctor_induct c;
      ctor_index := ctor_index c; ctor_num_params := ctor_num_params c;
      ctor_num_fields := ctor_num_fields c; ctor_is_unsafe := unsafe |}
  | DRecursor r => DRecursor {| rec_all := rec_all r; rec_num_params := rec_num_params r;
      rec_num_indices := rec_num_indices r; rec_num_motives := rec_num_motives r;
      rec_num_minors := rec_num_minors r; rec_rules := rec_rules r;
      rec_k := rec_k r; rec_is_unsafe := unsafe |}
  | k => k end in
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := decl_value d; decl_kind_of := kind |}.

Definition unsafe_empty := set_inductive_safety true empty_test_decl.
Definition unsafe_empty_rec := set_inductive_safety true (empty_rec false []).
Definition unsafe_empty_result :=
  admit_inductive_extended 100 [] [unsafe_empty] [] [unsafe_empty_rec].
Definition unsafe_empty_env := match unsafe_empty_result with
  | Accept env => env | _ => [] end.

Example unsafe_empty_accepted : admission_accepts unsafe_empty_result = true.
Proof. reflexivity. Qed.
Example unsafe_empty_installed_two_constants : List.length unsafe_empty_env = 2.
Proof. reflexivity. Qed.
Example safe_core_cannot_use_unsafe_inductive :
  admission_rejects (infer 100 unsafe_empty_env [] empty_context empty_test_type) = true.
Proof. reflexivity. Qed.
Example safe_core_cannot_use_unsafe_recursor :
  admission_rejects (infer 100 unsafe_empty_env [] empty_context
    (EConst (rec_name empty_test_name) [LZero])) = true.
Proof. reflexivity. Qed.
Example unsafe_view_can_use_unsafe_inductive :
  admission_accepts (infer 100 (safety_environment InputUnsafe unsafe_empty_env)
    [] empty_context empty_test_type) = true.
Proof. reflexivity. Qed.
Example partial_view_cannot_use_unsafe_inductive :
  admission_rejects (infer 100 (safety_environment InputPartial unsafe_empty_env)
    [] empty_context empty_test_type) = true.
Proof. reflexivity. Qed.
Example mixed_safety_inductive_rejected :
  admission_rejects (admit_inductive_extended 100 [] [unsafe_empty] [] [empty_rec false []]) = true.
Proof. reflexivity. Qed.
Example mixed_safety_recursor_rejected :
  admission_rejects (admit_inductive_extended 100 [] [empty_test_decl] [] [unsafe_empty_rec]) = true.
Proof. reflexivity. Qed.
Example unsafe_metadata_still_checked :
  admission_rejects (admit_inductive_extended 100 [] [unsafe_empty] []
    [set_inductive_safety true (empty_rec true [])]) = true.
Proof. reflexivity. Qed.
Example safe_axiom_cannot_reference_unsafe_inductive :
  admission_rejects (admit_extended 100 unsafe_empty_env
    (InputAxiom (NameStr NameAnon "unsafeLeak") [] empty_test_type false)) = true.
Proof. reflexivity. Qed.
Example unsafe_axiom_can_reference_unsafe_inductive :
  admission_accepts (admit_extended 100 unsafe_empty_env
    (InputAxiom (NameStr NameAnon "unsafeUse") [] empty_test_type true)) = true.
Proof. reflexivity. Qed.

Definition negative_name := NameStr NameAnon "Negative".
Definition negative_type := EConst negative_name [].
Definition negative_ctor_name := NameStr negative_name "mk".
Definition negative_decl (unsafe : bool) :=
  {| decl_hints := HintOpaque; decl_name := negative_name; decl_params := []; decl_type := ESort (LSucc LZero);
     decl_value := None; decl_kind_of := DInductive
       {| ind_num_params := 0; ind_num_indices := 0; ind_all := [negative_name];
          ind_ctors := [negative_ctor_name]; ind_num_nested := 0;
          ind_is_rec := true; ind_is_reflexive := true; ind_is_unsafe := unsafe |} |}.
Definition negative_ctor (unsafe : bool) :=
  {| decl_hints := HintOpaque; decl_name := negative_ctor_name; decl_params := [];
     decl_type := EPi NameAnon BDefault
       (EPi NameAnon BDefault negative_type negative_type) negative_type;
     decl_value := None; decl_kind_of := DConstructor
       {| ctor_induct := negative_name; ctor_index := 0; ctor_num_params := 0;
          ctor_num_fields := 1; ctor_is_unsafe := unsafe |} |}.
Definition negative_spec unsafe :=
  {| spec_decl := negative_decl unsafe; spec_ctors := [negative_ctor unsafe] |}.

Example negative_field_rejected_in_safe_mode :
  admission_rejects (derive_inductive 100 [] [] 0 [negative_spec false]) = true.
Proof. reflexivity. Qed.
Example negative_field_generated_in_unsafe_mode :
  admission_accepts (derive_inductive 100 [] [] 0 [negative_spec true]) = true.
Proof. reflexivity. Qed.

Print Assumptions unsafe_empty_accepted.
Print Assumptions safe_core_cannot_use_unsafe_inductive.
Print Assumptions negative_field_generated_in_unsafe_mode.
