(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String.
From LeanPort Require Import Syntax Declarations InductiveUtils Inductive.
Import ListNotations.
Open Scope string_scope.

Definition empty_test_name := NameStr NameAnon "Empty".
Definition empty_test_type := EConst empty_test_name [].
Definition empty_test_decl :=
  {| decl_hints := HintOpaque; decl_name := empty_test_name; decl_params := []; decl_type := ESort (LSucc LZero);
     decl_value := None;
     decl_kind_of := DInductive {| ind_num_params := 0; ind_num_indices := 0;
       ind_all := [empty_test_name]; ind_ctors := []; ind_num_nested := 0;
       ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |} |}.
Definition empty_test_u := NameStr NameAnon "u".
Definition empty_rec_type :=
  EPi NameAnon BDefault
    (EPi NameAnon BDefault empty_test_type (ESort (LParam empty_test_u)))
    (EPi NameAnon BDefault empty_test_type (EApp (EBVar 1) (EBVar 0))).
Definition empty_rec (k : bool) (rules : list recursor_rule) :=
  {| decl_hints := HintOpaque; decl_name := rec_name empty_test_name; decl_params := [empty_test_u];
     decl_type := empty_rec_type; decl_value := None;
     decl_kind_of := DRecursor {| rec_all := [empty_test_name];
       rec_num_params := 0; rec_num_indices := 0; rec_num_motives := 1; rec_num_minors := 0;
       rec_rules := rules; rec_k := k; rec_is_unsafe := false |} |}.
Definition admission_accepts {A} (r : result A) :=
  match r with Accept _ => true | _ => false end.
Definition admission_rejects {A} (r : result A) :=
  match r with Reject _ => true | _ => false end.

Example empty_inductive_accepted :
  admission_accepts (admit_inductive 100 [] [empty_test_decl] [] [empty_rec false []]) = true.
Proof. reflexivity. Qed.
Example empty_k_lie_rejected :
  admission_rejects (admit_inductive 100 [] [empty_test_decl] [] [empty_rec true []]) = true.
Proof. reflexivity. Qed.
Example empty_missing_rec_rejected :
  admission_rejects (admit_inductive 100 [] [empty_test_decl] [] []) = true.
Proof. reflexivity. Qed.
Example empty_forged_rule_rejected :
  admission_rejects (admit_inductive 100 [] [empty_test_decl] []
    [empty_rec false [{| rule_ctor := NameStr empty_test_name "impossible";
                       rule_nfields := 0; rule_rhs := ESort LZero |}]]) = true.
Proof. reflexivity. Qed.
Example empty_duplicate_type_rejected :
  admission_rejects (admit_inductive 100 [] [empty_test_decl;empty_test_decl] []
    [empty_rec false []]) = true.
Proof. reflexivity. Qed.
Example empty_extra_rec_rejected :
  admission_rejects (admit_inductive 100 [] [empty_test_decl] []
    [empty_rec false [];empty_rec false []]) = true.
Proof. reflexivity. Qed.
Example empty_existing_name_rejected :
  admission_rejects (admit_inductive 100 [empty_test_decl] [empty_test_decl] []
    [empty_rec false []]) = true.
Proof. reflexivity. Qed.
Example annotations_not_removed_under_pi :
  consume_type_annotations
    (EPi NameAnon BDefault (EApp (EConst (NameStr NameAnon "outParam") []) (ESort LZero))
      (ESort LZero)) =
    EPi NameAnon BDefault (EApp (EConst (NameStr NameAnon "outParam") []) (ESort LZero))
      (ESort LZero).
Proof. reflexivity. Qed.
Print Assumptions empty_inductive_accepted.
Print Assumptions empty_k_lie_rejected.

Definition opaque_former := NameStr NameAnon "OpaqueFormer".
Definition positive_test_type := ESort (LSucc LZero).
Definition opaque_former_environment :=
  match admit 100 [] (InputAxiom opaque_former []
    (EPi NameAnon BDefault positive_test_type positive_test_type) false) with
  | Accept env => env | _ => [] end.
Definition stuck_test_name := NameStr NameAnon "StuckField".
Definition stuck_test_ctor_name := NameStr stuck_test_name "mk".
Definition stuck_test_inductive :=
  {| decl_hints := HintOpaque; decl_name := stuck_test_name; decl_params := []; decl_type := positive_test_type;
     decl_value := None; decl_kind_of := DInductive
       {| ind_num_params := 0; ind_num_indices := 0; ind_all := [stuck_test_name];
          ind_ctors := [stuck_test_ctor_name]; ind_num_nested := 0;
          ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |} |}.
Definition stuck_test_spec (argument : expr) :=
  {| spec_decl := stuck_test_inductive; spec_ctors :=
       [{| decl_hints := HintOpaque; decl_name := stuck_test_ctor_name; decl_params := [];
           decl_type := EPi NameAnon BDefault (EApp (EConst opaque_former []) argument)
             (EConst stuck_test_name []); decl_value := None;
           decl_kind_of := DConstructor
             {| ctor_induct := stuck_test_name; ctor_index := 0; ctor_num_params := 0;
                ctor_num_fields := 1; ctor_is_unsafe := false |} |}] |}.
Example opaque_former_prior_environment_checked : List.length opaque_former_environment = 1.
Proof. reflexivity. Qed.
Example opaque_former_nonrecursive_field_is_valid :
  admission_accepts (derive_inductive 100 opaque_former_environment [] 0
    [stuck_test_spec (ESort LZero)]) = true.
Proof. reflexivity. Qed.
Example opaque_former_recursive_occurrence_is_rejected :
  derive_inductive 100 opaque_former_environment [] 0
    [stuck_test_spec (EConst stuck_test_name [])] = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Print Assumptions opaque_former_recursive_occurrence_is_rejected.
