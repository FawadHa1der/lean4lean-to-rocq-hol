(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Symbolic primitive validation and adversarial Gallina unit regressions.
   The Nat recursor fixture is kernel metadata, not a parsed declaration. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Universes Checker Primitives.
Import ListNotations.
Open Scope string_scope.

Definition pr_pi a b := EPi NameAnon BDefault a b.
Definition pr_lam a b := ELam NameAnon BDefault a b.
Definition pr_decl n ty kind value : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := ty;
     decl_kind_of := kind; decl_value := value |}.
Definition pr_ind n cs recursive : inductive_data :=
  {| ind_num_params := 0; ind_num_indices := 0; ind_all := [n];
     ind_ctors := cs; ind_num_nested := 0; ind_is_rec := recursive;
     ind_is_reflexive := false; ind_is_unsafe := false |}.
Definition pr_ctor n i fields : constructor_data :=
  {| ctor_induct := n; ctor_index := i; ctor_num_params := 0;
     ctor_num_fields := fields; ctor_is_unsafe := false |}.
Definition pr_type := ESort (LSucc LZero).
Definition pr_nat_env :=
  [pr_decl core_nat_name pr_type
     (DInductive (pr_ind core_nat_name [core_zero_name; core_succ_name] true)) None;
   pr_decl core_zero_name core_nat (DConstructor (pr_ctor core_nat_name 0 0)) None;
   pr_decl core_succ_name (pr_pi core_nat core_nat)
     (DConstructor (pr_ctor core_nat_name 1 1)) None].
Definition pr_rec_name := NameStr core_nat_name "rec".
Definition pr_motive_type := pr_pi core_nat pr_type.
Definition pr_step_type m := pr_pi core_nat
  (pr_pi (EApp (lift 1 0 m) (EBVar 0))
     (EApp (lift 2 0 m) (primitive_succ (EBVar 1)))).
Definition pr_rec_type := pr_pi pr_motive_type
  (pr_pi (EApp (EBVar 0) primitive_zero)
    (pr_pi (pr_step_type (EBVar 1))
      (pr_pi core_nat (EApp (EBVar 3) (EBVar 0))))).
Definition pr_rec_prefix b := pr_lam pr_motive_type
  (pr_lam (EApp (EBVar 0) primitive_zero)
    (pr_lam (pr_step_type (EBVar 1)) b)).
Definition pr_rec_data : recursor_data :=
  {| rec_all := [core_nat_name]; rec_num_params := 0; rec_num_indices := 0;
     rec_num_motives := 1; rec_num_minors := 2;
     rec_rules :=
       [{| rule_ctor := core_zero_name; rule_nfields := 0;
           rule_rhs := pr_rec_prefix (EBVar 1) |};
        {| rule_ctor := core_succ_name; rule_nfields := 1;
           rule_rhs := pr_rec_prefix (pr_lam core_nat
             (core_apps (EBVar 1) [EBVar 0;
                core_apps (EConst pr_rec_name [])
                  [EBVar 3; EBVar 2; EBVar 1; EBVar 0]])) |}];
     rec_k := false; rec_is_unsafe := false |}.
Definition pr_env := pr_decl pr_rec_name pr_rec_type
  (DRecursor pr_rec_data) None :: pr_nat_env.
Definition pr_fold ty z step n := core_apps (EConst pr_rec_name [])
  [pr_lam core_nat ty; z; step; n].
Definition pr_add := pr_lam core_nat (pr_lam core_nat
  (pr_fold core_nat (EBVar 1)
    (pr_lam core_nat (pr_lam core_nat (primitive_succ (EBVar 0)))) (EBVar 0))).
Definition pr_pred := pr_lam core_nat
  (pr_fold core_nat primitive_zero
    (pr_lam core_nat (pr_lam core_nat (EBVar 1))) (EBVar 0)).
Definition pr_fake_add := pr_lam core_nat (pr_lam core_nat (EBVar 1)).
Definition pr_zero_add := pr_lam core_nat (pr_lam core_nat primitive_zero).
Definition pr_classify env op body := classify_primitive 256 env
  (primitive_name op) [] (primitive_signature op) body.

Example primitive_fixture_add_is_typed :
  check 256 pr_env [] empty_context pr_add (primitive_signature PNatAdd) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_fixture_fake_add_is_typed :
  check 256 pr_env [] empty_context pr_fake_add (primitive_signature PNatAdd) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_add_equations_accept :
  pr_classify pr_env PNatAdd pr_add = Accept (Some PNatAdd).
Proof. vm_compute. reflexivity. Qed.
Example primitive_pred_equations_accept :
  pr_classify pr_env PNatPred pr_pred = Accept (Some PNatPred).
Proof. vm_compute. reflexivity. Qed.
Example primitive_add_projection_rejected :
  pr_classify pr_env PNatAdd pr_fake_add = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_add_constant_zero_rejected :
  pr_classify pr_env PNatAdd pr_zero_add = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_wrong_signature_rejected :
  classify_primitive 256 pr_env (primitive_name PNatAdd) []
    (pr_pi core_nat core_nat) pr_pred = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_universe_parameter_rejected :
  classify_primitive 256 pr_env (primitive_name PNatAdd) [core_name "u"]
    (primitive_signature PNatAdd) pr_add = Reject UniverseArity.
Proof. vm_compute. reflexivity. Qed.
Example primitive_nonreserved_is_none_without_fuel :
  classify_primitive 0 [] (core_name "userAdd") [] (ESort LZero) (EMVar NameAnon) =
    Accept None.
Proof. vm_compute. reflexivity. Qed.
Example primitive_symbolic_equations_need_fuel :
  classify_primitive 0 pr_env (primitive_name PNatAdd) []
    (primitive_signature PNatAdd) pr_add = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

Definition pr_install env op body : result environment :=
  _ <- check 256 env [] empty_context body (primitive_signature op) ;;
  classified <- pr_classify env op body ;;
  match classified with
  | Some actual => Accept (pr_decl (primitive_name op) (primitive_signature op)
      (DPrimitive actual) (Some body) :: env)
  | None => Reject MalformedDeclaration
  end.
Definition pr_sub := pr_lam core_nat (pr_lam core_nat
  (pr_fold core_nat (EBVar 1)
    (pr_lam core_nat (pr_lam core_nat (primitive_call PNatPred [EBVar 0]))) (EBVar 0))).
Definition pr_mul := pr_lam core_nat (pr_lam core_nat
  (pr_fold core_nat primitive_zero
    (pr_lam core_nat (pr_lam core_nat (primitive_call PNatAdd [EBVar 0; EBVar 3]))) (EBVar 0))).
Definition pr_pow := pr_lam core_nat (pr_lam core_nat
  (pr_fold core_nat primitive_one
    (pr_lam core_nat (pr_lam core_nat (primitive_call PNatMul [EBVar 0; EBVar 3]))) (EBVar 0))).
Definition pr_nat_function := pr_pi core_nat core_nat.
Definition pr_shift_left := pr_lam core_nat (pr_lam core_nat
  (EApp (pr_fold pr_nat_function (pr_lam core_nat (EBVar 0))
    (pr_lam core_nat (pr_lam pr_nat_function (pr_lam core_nat
      (EApp (EBVar 1) (primitive_call PNatMul [primitive_two; EBVar 0])))))
    (EBVar 0)) (EBVar 1))).
Definition pr_arithmetic_environment :=
  env <- pr_install pr_env PNatAdd pr_add ;;
  env <- pr_install env PNatPred pr_pred ;;
  env <- pr_install env PNatSub pr_sub ;;
  env <- pr_install env PNatMul pr_mul ;;
  env <- pr_install env PNatPow pr_pow ;;
  pr_install env PNatShiftLeft pr_shift_left.
Definition pr_accepted {A} (r : result A) :=
  match r with Accept _ => true | _ => false end.
Example primitive_arithmetic_chain_checks_types_and_equations :
  pr_accepted pr_arithmetic_environment = true.
Proof. vm_compute. reflexivity. Qed.
Example primitive_installed_metadata_enables_arithmetic :
  (env <- pr_arithmetic_environment ;;
   whnf 128 env [] empty_context
     (primitive_call PNatPow [ELit (LitNat 3); ELit (LitNat 4)])) =
    Accept (ELit (LitNat 81)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_subtraction_uses_authenticated_predecessor :
  (env <- pr_arithmetic_environment ;;
   whnf 128 env [] empty_context
     (primitive_call PNatSub [ELit (LitNat 2); ELit (LitNat 5)])) =
    Accept (ELit (LitNat 0)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_shift_left_equation_changes_the_first_argument :
  (env <- pr_arithmetic_environment ;;
   whnf 128 env [] empty_context
     (primitive_call PNatShiftLeft [ELit (LitNat 3); ELit (LitNat 5)])) =
    Accept (ELit (LitNat 96)).
Proof. vm_compute. reflexivity. Qed.

Definition pr_bool_env :=
  pr_decl core_bool_name pr_type
    (DInductive (pr_ind core_bool_name [core_false_name; core_true_name] false)) None ::
  pr_decl core_false_name primitive_bool (DConstructor (pr_ctor core_bool_name 0 0)) None ::
  pr_decl core_true_name primitive_bool (DConstructor (pr_ctor core_bool_name 1 0)) None :: pr_env.
Definition pr_nat_to_bool := pr_pi core_nat primitive_bool.
Definition pr_nat_boolean b0s := pr_lam core_nat (pr_lam core_nat
  (EApp (pr_fold pr_nat_to_bool
    (pr_lam core_nat (pr_fold primitive_bool primitive_true
      (pr_lam core_nat (pr_lam primitive_bool b0s)) (EBVar 0)))
    (pr_lam core_nat (pr_lam pr_nat_to_bool (pr_lam core_nat
      (pr_fold primitive_bool primitive_false
        (pr_lam core_nat (pr_lam primitive_bool (EApp (EBVar 3) (EBVar 1))))
        (EBVar 0))))) (EBVar 1)) (EBVar 0))).
Definition pr_beq := pr_nat_boolean primitive_false.
Definition pr_ble := pr_nat_boolean primitive_true.
Example primitive_beq_checks_all_four_cases :
  pr_accepted (pr_install pr_bool_env PNatBEq pr_beq) = true.
Proof. vm_compute. reflexivity. Qed.
Example primitive_ble_checks_all_four_cases :
  pr_accepted (pr_install pr_bool_env PNatBLE pr_ble) = true.
Proof. vm_compute. reflexivity. Qed.
Example primitive_beq_is_not_ble :
  pr_classify pr_bool_env PNatBLE pr_beq = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_always_true_is_not_beq :
  pr_classify pr_bool_env PNatBEq
    (pr_lam core_nat (pr_lam core_nat primitive_true)) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_always_false_is_not_ble :
  pr_classify pr_bool_env PNatBLE
    (pr_lam core_nat (pr_lam core_nat primitive_false)) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.

Definition pr_sample_impostor := pr_lam core_nat (pr_lam core_nat
  (pr_fold core_nat (EBVar 1)
    (pr_lam core_nat (pr_lam core_nat (primitive_succ (EBVar 3)))) (EBVar 0))).
Example primitive_impostor_is_well_typed :
  check 256 pr_env [] empty_context pr_sample_impostor (primitive_signature PNatAdd) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_impostor_agrees_on_small_samples :
  (check_defeq 256 pr_env [] empty_context
    (core_apps pr_sample_impostor [ELit (LitNat 7); ELit (LitNat 0)]) (ELit (LitNat 7)),
   check_defeq 256 pr_env [] empty_context
    (core_apps pr_sample_impostor [ELit (LitNat 7); ELit (LitNat 1)]) (ELit (LitNat 8))) =
    (Accept tt, Accept tt).
Proof. vm_compute. reflexivity. Qed.
Example primitive_impostor_fails_the_general_equation :
  pr_classify pr_env PNatAdd pr_sample_impostor = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_body_beta_zeta_equivalent_is_accepted :
  pr_classify pr_env PNatAdd
    (ELet NameAnon (primitive_signature PNatAdd) pr_add
      (EApp (pr_lam (primitive_signature PNatAdd) (EBVar 0)) (EBVar 0)) false) =
    Accept (Some PNatAdd).
Proof. vm_compute. reflexivity. Qed.
Example primitive_untrusted_dependency_name_rejected :
  pr_classify
    (pr_decl (primitive_name PNatAdd) (primitive_signature PNatAdd)
      DDefinition (Some pr_fake_add) :: pr_env) PNatMul pr_mul = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_missing_dependency_rejected :
  pr_classify pr_env PNatSub pr_sub = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_forged_dependency_kind_rejected :
  pr_classify
    (pr_decl (primitive_name PNatAdd) (primitive_signature PNatAdd)
      (DPrimitive PNatSub) (Some pr_fake_add) :: pr_env) PNatMul pr_mul = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_existing_metadata_cannot_certify_itself :
  pr_classify
    (pr_decl (primitive_name PNatAdd) (primitive_signature PNatAdd)
      (DPrimitive PNatAdd) (Some pr_fake_add) :: pr_env) PNatAdd
    (EConst (primitive_name PNatAdd) []) = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_missing_nat_metadata_rejected :
  pr_classify [] PNatAdd pr_add = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_probe_cannot_capture_loose_bound_variable :
  pr_classify pr_env PNatAdd (EBVar 0) = Reject LooseBoundVariable.
Proof. vm_compute. reflexivity. Qed.
Example primitive_probe_cannot_capture_free_variable :
  pr_classify pr_env PNatAdd (EFVar (core_name "x")) = Reject UnknownFreeVariable.
Proof. vm_compute. reflexivity. Qed.
Example primitive_metavariable_rejected :
  pr_classify pr_env PNatAdd (EMVar (core_name "x")) = Reject MetaVariable.
Proof. vm_compute. reflexivity. Qed.
Example primitive_unsupported_body_propagates_decline :
  pr_classify pr_env PNatAdd
    (pr_lam core_nat (pr_lam core_nat (EProj (core_name "Unknown") 0 (EBVar 0)))) =
    Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example primitive_complex_recursions_never_get_partial_certificates :
  map (fun op => pr_accepted (pr_classify pr_env op pr_fake_add))
    [PNatMod; PNatDiv; PNatGcd; PNatLAnd; PNatLOr; PNatXor] =
    repeat false 6.
Proof. vm_compute. reflexivity. Qed.
Example primitive_complex_wrong_signature_rejected_before_decline :
  classify_primitive 256 pr_env (primitive_name PNatDiv) [] core_nat primitive_zero =
    Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_is_reserved_and_requires_checked_dependencies :
  classify_primitive 256 pr_env primitive_bitwise_name []
    (primitive_arrow
      (primitive_arrow primitive_bool (primitive_arrow primitive_bool primitive_bool))
      (primitive_signature PNatAdd)) pr_fake_add = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Definition pr_annotated_add_type := pr_pi (EMData core_nat)
  (pr_pi (EMData core_nat) core_nat).
Example primitive_metadata_annotations_are_transparent :
  classify_primitive 256 pr_env (primitive_name PNatAdd) []
    pr_annotated_add_type pr_add = Accept (Some PNatAdd).
Proof. vm_compute. reflexivity. Qed.
Example primitive_annotated_dependency_keeps_its_certificate :
  pr_classify (pr_decl (primitive_name PNatAdd) pr_annotated_add_type
    (DPrimitive PNatAdd) (Some pr_add) :: pr_env) PNatMul pr_mul = Accept (Some PNatMul).
Proof. vm_compute. reflexivity. Qed.
Example primitive_inductive_names_are_not_ordinary_definitions :
  map (fun n => classify_primitive 256 [] n [] pr_type core_nat)
    [core_nat_name; core_zero_name; core_succ_name;
     core_bool_name; core_false_name; core_true_name] =
    repeat (Reject MalformedDeclaration) 6.
Proof. vm_compute. reflexivity. Qed.
Example primitive_nested_name_is_not_reserved :
  classify_primitive 0 [] (NameStr (core_name "Nat.add") "extra") [] core_nat primitive_zero =
    Accept None.
Proof. vm_compute. reflexivity. Qed.
Example primitive_flat_spelling_is_not_a_hierarchical_name :
  classify_primitive 0 [] (core_name "Nat.add") [] core_nat primitive_zero = Accept None.
Proof. vm_compute. reflexivity. Qed.
Example primitive_signature_fuel_exhaustion_is_not_rejection :
  primitive_check_signature 1 pr_annotated_add_type (primitive_signature PNatAdd) = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example primitive_equation_fuel_exhaustion_is_not_rejection :
  primitive_check_equations 4 0 pr_env
    [primitive_equation_at empty_context primitive_zero primitive_zero] = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example primitive_right_shift_cannot_use_unauthenticated_division :
  pr_classify (pr_decl (primitive_name PNatDiv) (primitive_signature PNatDiv)
    DDefinition (Some pr_fake_add) :: pr_env) PNatShiftRight pr_fake_add = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_right_shift_has_the_upstream_symbolic_equation :
  primitive_equations PNatShiftRight pr_fake_add = Some
    [primitive_equation_at primitive_x_context
       (core_apps pr_fake_add [EBVar 0; primitive_zero]) (EBVar 0);
     primitive_equation_at primitive_xy_context
       (core_apps pr_fake_add [EBVar 1; primitive_succ (EBVar 0)])
       (primitive_call PNatDiv [core_apps pr_fake_add [EBVar 1; EBVar 0]; primitive_two])].
Proof. reflexivity. Qed.

(* Interface-only text fixtures deliberately permit arbitrary representations,
   exactly as upstream's representation semantics permit. *)
Definition pr_char_env := pr_decl core_char_name pr_type DDefinition (Some core_nat) :: pr_env.
Definition pr_char_body := pr_lam core_nat (EBVar 0).
Definition pr_char_bad_body := pr_lam core_nat primitive_zero.
Example primitive_char_interface_is_checked :
  primitive_check_text_interface 128 pr_char_env PCharOfNat = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_char_body_gets_an_interface_certificate :
  (check 256 pr_char_env [] empty_context pr_char_body (primitive_signature PCharOfNat),
   pr_classify pr_char_env PCharOfNat pr_char_body) =
    (Accept tt, Accept (Some PCharOfNat)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_char_constant_representation_has_no_arithmetic_promise :
  (check 256 pr_char_env [] empty_context pr_char_bad_body (primitive_signature PCharOfNat),
   pr_classify pr_char_env PCharOfNat pr_char_bad_body) =
    (Accept tt, Accept (Some PCharOfNat)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_char_wrong_signature_rejects :
  classify_primitive 256 pr_char_env core_char_of_nat []
    (pr_pi core_nat core_nat) pr_char_body = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_char_nonsort_rejects :
  primitive_check_text_interface 256
    (pr_decl core_char_name core_nat DAssumption None :: pr_env)
    PCharOfNat = Reject ExpectedSort.
Proof. vm_compute. reflexivity. Qed.

Definition pr_universe_name := core_name "u".
Definition pr_universe := LParam pr_universe_name.
Definition pr_poly_decl n ty kind : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := [pr_universe_name]; decl_type := ty;
     decl_kind_of := kind; decl_value := None |}.
Definition pr_list_at a := EApp (EConst core_list_name [pr_universe]) a.
Definition pr_list_ind : inductive_data :=
  {| ind_num_params := 1; ind_num_indices := 0; ind_all := [core_list_name];
     ind_ctors := [NameStr core_list_name "nil"; NameStr core_list_name "cons"];
     ind_num_nested := 0; ind_is_rec := true; ind_is_reflexive := false;
     ind_is_unsafe := false |}.
Definition pr_list_ctor i fields : constructor_data :=
  {| ctor_induct := core_list_name; ctor_index := i; ctor_num_params := 1;
     ctor_num_fields := fields; ctor_is_unsafe := false |}.
Definition pr_list_decl := pr_poly_decl core_list_name
  (pr_pi (ESort (LSucc pr_universe)) (ESort (LSucc pr_universe))) (DInductive pr_list_ind).
Definition pr_nil_decl := pr_poly_decl (NameStr core_list_name "nil")
  (pr_pi (ESort (LSucc pr_universe)) (pr_list_at (EBVar 0)))
  (DConstructor (pr_list_ctor 0 0)).
Definition pr_cons_decl := pr_poly_decl (NameStr core_list_name "cons")
  (pr_pi (ESort (LSucc pr_universe))
    (pr_pi (EBVar 0) (pr_pi (pr_list_at (EBVar 1)) (pr_list_at (EBVar 2)))))
  (DConstructor (pr_list_ctor 1 2)).
Definition pr_text_env :=
  pr_decl core_string_name pr_type DDefinition (Some primitive_list_char) ::
  pr_list_decl :: pr_nil_decl :: pr_cons_decl :: pr_char_env.
Definition pr_string_body := pr_lam primitive_list_char (EBVar 0).
Definition pr_string_bad_body := pr_lam primitive_list_char
  (EApp (EConst (NameStr core_list_name "nil") [LZero]) primitive_char).
Example primitive_string_interface_checks_list_constructors :
  primitive_check_text_interface 256 pr_text_env PStringOfList = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_body_gets_an_interface_certificate :
  (check 256 pr_text_env [] empty_context pr_string_body (primitive_signature PStringOfList),
   pr_classify pr_text_env PStringOfList pr_string_body) =
    (Accept tt, Accept (Some PStringOfList)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_constant_representation_has_no_arithmetic_promise :
  (check 256 pr_text_env [] empty_context pr_string_bad_body (primitive_signature PStringOfList),
   pr_classify pr_text_env PStringOfList pr_string_bad_body) =
    (Accept tt, Accept (Some PStringOfList)).
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_wrong_signature_rejects :
  classify_primitive 256 pr_text_env core_string_of_list []
    (pr_pi core_nat primitive_string) pr_string_body = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_malformed_nil_rejects :
  primitive_check_text_interface 256
    (pr_poly_decl (NameStr core_list_name "nil")
      (pr_pi (ESort (LSucc pr_universe)) core_nat) DAssumption :: pr_text_env)
    PStringOfList = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_malformed_cons_rejects :
  primitive_check_text_interface 256
    (pr_poly_decl (NameStr core_list_name "cons")
      (pr_pi (ESort (LSucc pr_universe)) (pr_list_at (EBVar 0))) DAssumption :: pr_text_env)
    PStringOfList = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_string_constructor_universe_arity_rejects :
  primitive_check_text_interface 256
    (pr_decl (NameStr core_list_name "nil") primitive_list_char DAssumption None :: pr_text_env)
    PStringOfList = Reject UniverseArity.
Proof. vm_compute. reflexivity. Qed.

Definition pr_qbool_rec u motive z s b :=
  PQ.apps (PQ.const ["Bool";"rec"] [u]) [motive;z;s;b].
Definition pr_bool_motive := PQ.arrow PQ.bool (PQ.embed (ESort pr_universe)).
Definition pr_bool_rec_type := PQ.run (PQ.pi pr_bool_motive (fun m =>
  PQ.arrow (PQ.app m PQ.fal) (PQ.arrow (PQ.app m PQ.tru)
    (PQ.pi PQ.bool (fun b => PQ.app m b))))).
Definition pr_bool_rec_rule (positive : bool) := PQ.run (PQ.lam pr_bool_motive (fun m =>
  PQ.lam (PQ.app m PQ.fal) (fun z => PQ.lam (PQ.app m PQ.tru)
    (fun s => if positive then s else z)))).
Definition pr_bool_rec_decl := pr_poly_decl (primitive_path ["Bool";"rec"])
  pr_bool_rec_type (DRecursor
    {| rec_all := [core_bool_name]; rec_num_params := 0; rec_num_indices := 0;
       rec_num_motives := 1; rec_num_minors := 2; rec_k := false; rec_is_unsafe := false;
       rec_rules :=
         [{| rule_ctor := core_false_name; rule_nfields := 0; rule_rhs := pr_bool_rec_rule false |};
          {| rule_ctor := core_true_name; rule_nfields := 0; rule_rhs := pr_bool_rec_rule true |}] |}).
Definition pr_poly_definition parts ty body : declaration :=
  {| decl_hints := HintOpaque; decl_name := primitive_path parts; decl_params := [pr_universe_name];
     decl_type := PQ.run ty; decl_kind_of := DDefinition; decl_value := Some (PQ.run body) |}.
Definition pr_definition parts ty body :=
  pr_decl (primitive_path parts) (PQ.run ty) DDefinition (Some (PQ.run body)).
Definition pr_proof_constant parts ty :=
  pr_decl (primitive_path parts) (PQ.run ty) DAssumption None.
Definition pr_sortu := PQ.embed (ESort pr_universe).
Definition pr_qeq_u a x y := PQ.apps (PQ.const ["Eq"] [pr_universe]) [a;x;y].
Definition pr_eq_decl := pr_poly_decl (primitive_path ["Eq"])
  (PQ.run (PQ.pi pr_sortu (fun a => PQ.arrow a (PQ.arrow a PQ.prop))))
  (DInductive {| ind_num_params := 2; ind_num_indices := 1;
    ind_all := [primitive_path ["Eq"]]; ind_ctors := [primitive_path ["Eq";"refl"]];
    ind_num_nested := 0; ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |}).
Definition pr_refl_decl := pr_poly_decl (primitive_path ["Eq";"refl"])
  (PQ.run (PQ.pi pr_sortu (fun a => PQ.pi a (fun x => pr_qeq_u a x x))))
  (DConstructor {| ctor_induct := primitive_path ["Eq"]; ctor_index := 0;
    ctor_num_params := 2; ctor_num_fields := 0; ctor_is_unsafe := false |}).
Definition pr_false_decl := pr_decl (core_name "False") (ESort LZero)
  (DInductive (pr_ind (core_name "False") [] false)) None.
Definition pr_not_decl := pr_definition ["Not"] (PQ.arrow PQ.prop PQ.prop)
  (PQ.lam PQ.prop (fun p => PQ.arrow p (PQ.const ["False"] []))).
Definition pr_dec_decl := pr_decl (core_name "Decidable") (PQ.run (PQ.arrow PQ.prop PQ.type0))
  (DInductive {| ind_num_params := 1; ind_num_indices := 0;
    ind_all := [core_name "Decidable"];
    ind_ctors := [primitive_path ["Decidable";"isFalse"]; primitive_path ["Decidable";"isTrue"]];
    ind_num_nested := 0; ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |}) None.
Definition pr_dec_ctor (positive : bool) :=
  pr_decl (primitive_path ["Decidable";if positive then "isTrue" else "isFalse"])
    (PQ.run (PQ.pi PQ.prop (fun p => PQ.arrow (if positive then p else PQ.not p) (PQ.dec p))))
    (DConstructor {| ctor_induct := core_name "Decidable"; ctor_index := if positive then 1 else 0;
      ctor_num_params := 1; ctor_num_fields := 1; ctor_is_unsafe := false |}) None.
Definition pr_dec_motive p := PQ.arrow (PQ.dec p) pr_sortu.
Definition pr_dec_minor p m (positive : bool) := PQ.pi (if positive then p else PQ.not p)
  (fun h => PQ.app m (if positive then PQ.is_true p h else PQ.is_false p h)).
Definition pr_dec_rec_type := PQ.run (PQ.pi PQ.prop (fun p => PQ.pi (pr_dec_motive p) (fun m =>
  PQ.arrow (pr_dec_minor p m false) (PQ.arrow (pr_dec_minor p m true)
    (PQ.pi (PQ.dec p) (fun d => PQ.app m d)))))).
Definition pr_dec_rec_rule (positive : bool) := PQ.run (PQ.lam PQ.prop (fun p =>
  PQ.lam (pr_dec_motive p) (fun m => PQ.lam (pr_dec_minor p m false) (fun z =>
    PQ.lam (pr_dec_minor p m true) (fun s =>
      PQ.lam (if positive then p else PQ.not p) (fun h => PQ.app (if positive then s else z) h)))))).
Definition pr_dec_rec_decl := pr_poly_decl (primitive_path ["Decidable";"rec"])
  pr_dec_rec_type (DRecursor
    {| rec_all := [core_name "Decidable"]; rec_num_params := 1; rec_num_indices := 0;
       rec_num_motives := 1; rec_num_minors := 2; rec_k := false; rec_is_unsafe := false;
       rec_rules :=
         [{| rule_ctor := primitive_path ["Decidable";"isFalse"]; rule_nfields := 1;
             rule_rhs := pr_dec_rec_rule false |};
          {| rule_ctor := primitive_path ["Decidable";"isTrue"]; rule_nfields := 1;
             rule_rhs := pr_dec_rec_rule true |}] |}).
Definition pr_if_type (dependent : bool) := PQ.pi pr_sortu (fun a => PQ.pi PQ.prop (fun p =>
  PQ.arrow (PQ.dec p) (PQ.arrow (if dependent then PQ.arrow p a else a)
    (PQ.arrow (if dependent then PQ.arrow (PQ.not p) a else a) a)))).
Definition pr_if_body (dependent : bool) := PQ.lam pr_sortu (fun a => PQ.lam PQ.prop (fun p =>
  PQ.lam (PQ.dec p) (fun d => PQ.lam (if dependent then PQ.arrow p a else a) (fun t =>
    PQ.lam (if dependent then PQ.arrow (PQ.not p) a else a) (fun e =>
      PQ.apps (PQ.const ["Decidable";"rec"] [pr_universe])
        [p; PQ.lam (PQ.dec p) (fun _ => a);
         PQ.lam (PQ.not p) (fun h => if dependent then PQ.app e h else e);
         PQ.lam p (fun h => if dependent then PQ.app t h else t); d]))))).
Definition pr_ite_decl := pr_poly_definition ["ite"] (pr_if_type false) (pr_if_body false).
Definition pr_dite_decl := pr_poly_definition ["dite"] (pr_if_type true) (pr_if_body true).

(* These proof constants stand for valid typed theorems in a checked environment;
   tests exercise the computational reflection, not theorem admission. *)
Definition pr_no_confusion_type := pr_poly_definition ["Bool";"noConfusionType"]
  (PQ.arrow pr_sortu (PQ.arrow PQ.bool (PQ.arrow PQ.bool pr_sortu)))
  (PQ.lam pr_sortu (fun p => PQ.lam PQ.bool (fun a => PQ.lam PQ.bool (fun b =>
    let choice z t major := pr_qbool_rec (LSucc pr_universe) (PQ.lam PQ.bool (fun _ => pr_sortu)) z t major in
    choice (choice (PQ.arrow p p) p b) (choice p (PQ.arrow p p) b) a)))).
Definition pr_no_confusion_decl := pr_poly_decl (primitive_path ["Bool";"noConfusion"])
  (PQ.run (PQ.pi pr_sortu (fun p => PQ.pi PQ.bool (fun a => PQ.pi PQ.bool (fun b =>
    PQ.arrow (PQ.eq PQ.bool a b) (PQ.apps (PQ.const ["Bool";"noConfusionType"] [pr_universe]) [p;a;b]))))))
  DAssumption.
Definition pr_bool_dec_eq_body := PQ.lam PQ.bool (fun a =>
  let result a b := PQ.dec (PQ.eq PQ.bool a b) in
  let yes a := PQ.is_true (PQ.eq PQ.bool a a) (PQ.refl PQ.bool a) in
  let no a b := PQ.is_false (PQ.eq PQ.bool a b)
    (PQ.lam (PQ.eq PQ.bool a b) (fun h =>
      PQ.apps (PQ.const ["Bool";"noConfusion"] [LZero]) [PQ.const ["False"] [];a;b;h])) in
  pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (fun a => PQ.pi PQ.bool (result a)))
    (PQ.lam PQ.bool (fun b => pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (result PQ.fal))
      (yes PQ.fal) (no PQ.fal PQ.tru) b))
    (PQ.lam PQ.bool (fun b => pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (result PQ.tru))
      (no PQ.tru PQ.fal) (yes PQ.tru) b)) a).
Definition pr_bool_dec_eq_decl := pr_definition ["Bool";"decEq"]
  (PQ.pi PQ.bool (fun a => PQ.pi PQ.bool (fun b => PQ.dec (PQ.eq PQ.bool a b)))) pr_bool_dec_eq_body.
Definition pr_logic_env :=
  List.app [pr_bool_rec_decl; pr_eq_decl; pr_refl_decl; pr_false_decl; pr_not_decl;
   pr_dec_decl; pr_dec_ctor false; pr_dec_ctor true; pr_dec_rec_decl;
   pr_ite_decl; pr_dite_decl; pr_no_confusion_type; pr_no_confusion_decl; pr_bool_dec_eq_decl] pr_bool_env.

Example primitive_bool_decision_fixture_is_typed :
  check 512 pr_logic_env [] empty_context (PQ.run pr_bool_dec_eq_body)
    (decl_type pr_bool_dec_eq_decl) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bool_condition_checks_both_branches :
  primitive_check_condition 512 pr_logic_env PCBool true false = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_negated_truth_reflection_checks_ite_and_dite :
  primitive_check_reflection 512 pr_logic_env (primitive_reflection_make false) true true = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_false_equality_reflection_checks_ite_and_dite :
  primitive_check_reflection 512 pr_logic_env (primitive_reflection_make true) true true = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition pr_le_decl := pr_decl (primitive_path ["Nat";"le"])
  (PQ.run (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.prop)))
  (DInductive {| ind_num_params := 1; ind_num_indices := 1;
    ind_all := [primitive_path ["Nat";"le"]];
    ind_ctors := [primitive_path ["Nat";"le";"refl"];primitive_path ["Nat";"le";"step"]];
    ind_num_nested := 0; ind_is_rec := true; ind_is_reflexive := false; ind_is_unsafe := false |}) None.
Definition pr_le_ctor (step : bool) := pr_decl
  (primitive_path ["Nat";"le";if step then "step" else "refl"])
  (PQ.run (PQ.pi PQ.nat (fun n => if step then PQ.pi PQ.nat (fun m =>
    PQ.arrow (primitive_le n m) (primitive_le n (PQ.succ m))) else primitive_le n n)))
  (DConstructor {| ctor_induct := primitive_path ["Nat";"le"];
    ctor_index := if step then 1 else 0; ctor_num_params := 1;
    ctor_num_fields := if step then 2 else 0; ctor_is_unsafe := false |}) None.
Definition pr_nat_reflect_proof_type (eq_case positive : bool) :=
  PQ.pi PQ.nat (fun x => PQ.pi PQ.nat (fun y =>
    let p := PQ.apps (PQ.embed (primitive_condition_prop (if eq_case then PCNatEq else PCNatLE))) [x;y] in
    let b := PQ.call (if eq_case then PNatBEq else PNatBLE) [x;y] in
    PQ.arrow (if positive then PQ.eq PQ.bool b PQ.tru else
      if eq_case then PQ.eq PQ.bool b PQ.fal else PQ.not (PQ.eq PQ.bool b PQ.tru))
      (if positive then p else PQ.not p))).
Definition pr_nat_reflect_lemma (eq_case positive : bool) :=
  PQ.const ["Nat"; if eq_case then
      if positive then "eq_of_beq_eq_true" else "ne_of_beq_eq_false"
    else if positive then "le_of_ble_eq_true" else "not_le_of_not_ble_eq_true"] [].
Definition pr_nat_reflect_decl eq_case positive :=
  pr_decl (match PQ.run (pr_nat_reflect_lemma eq_case positive) with EConst n _ => n | _ => NameAnon end)
    (PQ.run (pr_nat_reflect_proof_type eq_case positive)) DAssumption None.
Definition pr_nat_dec_body (eq_case : bool) := PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
  let p := PQ.apps (PQ.embed (primitive_condition_prop (if eq_case then PCNatEq else PCNatLE))) [x;y] in
  let b := PQ.call (if eq_case then PNatBEq else PNatBLE) [x;y] in
  let yes h := PQ.is_true p (PQ.apps (pr_nat_reflect_lemma eq_case true) [x;y;h]) in
  let no h := PQ.is_false p (PQ.apps (pr_nat_reflect_lemma eq_case false) [x;y;h]) in
  if eq_case then PQ.app (pr_qbool_rec (LSucc LZero)
    (PQ.lam PQ.bool (fun b' => PQ.arrow (PQ.eq PQ.bool b b') (PQ.dec p)))
    (PQ.lam (PQ.eq PQ.bool b PQ.fal) no) (PQ.lam (PQ.eq PQ.bool b PQ.tru) yes) b)
    (PQ.refl PQ.bool b)
  else PQ.dite (PQ.dec p) (PQ.eq PQ.bool b PQ.tru) (PQ.bool_dec b) yes no)).
Definition pr_nat_dec_decl (eq_case : bool) := pr_definition
  ["Nat"; if eq_case then "decEq" else "decLe"]
  (PQ.pi PQ.nat (fun x => PQ.pi PQ.nat (fun y =>
    PQ.dec (PQ.apps (PQ.embed (primitive_condition_prop (if eq_case then PCNatEq else PCNatLE))) [x;y]))))
  (pr_nat_dec_body eq_case).
Definition pr_reflected_env : result environment :=
  env <- pr_install pr_logic_env PNatAdd pr_add ;;
  env <- pr_install env PNatPred pr_pred ;;
  env <- pr_install env PNatSub pr_sub ;;
  env <- pr_install env PNatBEq pr_beq ;;
  env <- pr_install env PNatBLE pr_ble ;;
  Accept (List.app [pr_le_decl; pr_le_ctor false; pr_le_ctor true;
    pr_nat_reflect_decl false true; pr_nat_reflect_decl false false;
    pr_nat_reflect_decl true true; pr_nat_reflect_decl true false;
    pr_nat_dec_decl false; pr_nat_dec_decl true] env).

Example primitive_nat_le_condition_reflects_authenticated_ble :
  (env <- pr_reflected_env ;; primitive_check_condition 512 env PCNatLE true true) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_nat_eq_condition_reflects_authenticated_beq :
  (env <- pr_reflected_env ;; primitive_check_condition 512 env PCNatEq true true) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition pr_fuel_lemma_type := PQ.pi PQ.nat (fun x => PQ.pi PQ.nat (fun y =>
  PQ.pi PQ.nat (fun t => PQ.arrow (primitive_le PQ.one y)
    (PQ.arrow (primitive_le y x) (PQ.arrow (primitive_le (PQ.succ x) (PQ.succ t))
      (primitive_le (PQ.succ (PQ.call PNatSub [x;y])) t)))))).
Definition pr_fuel_helpers :=
  [pr_proof_constant ["Nat";"lt_succ_self"]
     (PQ.pi PQ.nat (fun x => primitive_le (PQ.succ x) (PQ.succ x)));
   pr_proof_constant ["Nat";"div_rec_fuel_lemma"] pr_fuel_lemma_type;
   pr_proof_constant ["Nat";"not_succ_le_zero"]
     (PQ.pi PQ.nat (fun x => PQ.not (primitive_le (PQ.succ x) PQ.zero)));
   pr_poly_decl (primitive_path ["False";"elim"])
     (PQ.run (PQ.pi pr_sortu (fun a => PQ.arrow (PQ.const ["False"] []) a))) DAssumption].
Definition pr_go_body (modulo : bool) := PQ.run
  (PQ.lam PQ.nat (fun y => PQ.lam (primitive_le PQ.one y) (fun hy => PQ.lam PQ.nat (fun fuel =>
    let motive t := PQ.pi PQ.nat (fun x => PQ.arrow (primitive_le (PQ.succ x) t) PQ.nat) in
    PQ.apps (PQ.const ["Nat";"rec"] [])
      [PQ.lam PQ.nat motive;
       PQ.lam PQ.nat (fun x => PQ.lam (primitive_le (PQ.succ x) PQ.zero) (fun h =>
         PQ.apps (PQ.const ["False";"elim"] [LSucc LZero]) [PQ.nat;
           PQ.apps (PQ.const ["Nat";"not_succ_le_zero"] []) [x;h]]));
       PQ.lam PQ.nat (fun t => PQ.lam (motive t) (fun ih =>
         PQ.lam PQ.nat (fun x => PQ.lam (primitive_le (PQ.succ x) (PQ.succ t)) (fun h =>
           primitive_condition_dite PCNatLE [y;x]
             (fun hle =>
               let r := PQ.apps ih [PQ.call PNatSub [x;y];
                 PQ.apps (PQ.const ["Nat";"div_rec_fuel_lemma"] []) [x;y;t;hy;hle;h]] in
               if modulo then r else PQ.succ r)
             (fun _ => if modulo then x else PQ.zero)))));
       fuel])))).
Definition pr_go_decl modulo := pr_decl (primitive_go_name modulo) primitive_go_type
  DDefinition (Some (pr_go_body modulo)).
Definition pr_divmod_env := env <- pr_reflected_env ;;
  Accept (List.app (pr_go_decl true :: pr_go_decl false :: pr_fuel_helpers) env).
Definition pr_mod_body := PQ.run (PQ.lam PQ.nat (fun n => PQ.lam PQ.nat (fun m =>
  PQ.app (PQ.apps (PQ.const ["Nat";"rec"] [])
    [PQ.lam PQ.nat (fun _ => PQ.arrow PQ.nat PQ.nat);
     PQ.lam PQ.nat (fun _ => PQ.zero);
     PQ.lam PQ.nat (fun x => PQ.lam (PQ.arrow PQ.nat PQ.nat) (fun _ =>
       PQ.app (PQ.embed (primitive_fuel_top true)) x)); n]) m))).
Definition pr_div_body := primitive_fuel_top false.
Example primitive_modulo_go_fixture_is_typed :
  (env <- pr_divmod_env ;; check 512 env [] empty_context (pr_go_body true) primitive_go_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_division_go_fixture_is_typed :
  (env <- pr_divmod_env ;; check 512 env [] empty_context (pr_go_body false) primitive_go_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_modulo_validates_top_and_fuel_equations :
  (env <- pr_divmod_env ;; _ <- pr_install env PNatMod pr_mod_body ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_division_validates_top_and_fuel_equations :
  (env <- pr_divmod_env ;; _ <- pr_install env PNatDiv pr_div_body ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition pr_rejected {A} (r : result A) :=
  match r with Reject _ => true | _ => false end.
Definition pr_replace (d : declaration) (env : environment) :=
  d :: filter (fun old => negb (name_eqb (decl_name old) (decl_name d))) env.
Definition pr_constant_go := PQ.run (PQ.lam PQ.nat (fun y =>
  PQ.lam (primitive_le PQ.one y) (fun _ => PQ.lam PQ.nat (fun t =>
    PQ.lam PQ.nat (fun x => PQ.lam (primitive_le (PQ.succ x) t) (fun _ => PQ.zero)))))).
Example primitive_modulo_rejects_projection :
  (env <- pr_divmod_env ;; pr_classify env PNatMod pr_fake_add) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_division_rejects_constant :
  (env <- pr_divmod_env ;; pr_classify env PNatDiv pr_zero_add) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_false_go_is_well_typed :
  (env <- pr_divmod_env ;; check 256 env [] empty_context pr_constant_go primitive_go_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_modulo_top_equation_alone_is_insufficient :
  (env <- pr_divmod_env ;; pr_classify
    (pr_replace (pr_decl (primitive_go_name true) primitive_go_type DDefinition
      (Some pr_constant_go)) env) PNatMod pr_mod_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_division_top_equation_alone_is_insufficient :
  (env <- pr_divmod_env ;; pr_classify
    (pr_replace (pr_decl (primitive_go_name false) primitive_go_type DDefinition
      (Some pr_constant_go)) env) PNatDiv pr_div_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_division_cannot_use_modulo_step :
  (env <- pr_divmod_env ;; pr_classify
    (pr_replace (pr_decl (primitive_go_name false) primitive_go_type DDefinition
      (Some (pr_go_body true))) env) PNatDiv pr_div_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Definition pr_false_ite := pr_poly_definition ["ite"] (pr_if_type false)
  (PQ.lam pr_sortu (fun a => PQ.lam PQ.prop (fun p => PQ.lam (PQ.dec p) (fun _ =>
    PQ.lam a (fun t => PQ.lam a (fun _ => t)))))).
Example primitive_true_branch_only_does_not_authenticate_ite :
  primitive_check_condition 256 (pr_replace pr_false_ite pr_logic_env) PCBool true false =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_modulo_requires_certified_comparison :
  (env <- pr_divmod_env ;; pr_classify
    (pr_replace (pr_decl (primitive_name PNatBLE) (primitive_signature PNatBLE)
      DDefinition (Some pr_ble)) env) PNatMod pr_mod_body) = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Definition pr_shift_right := PQ.run (PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
  PQ.apps (PQ.const ["Nat";"rec"] []) [PQ.lam PQ.nat (fun _ => PQ.nat); x;
    PQ.lam PQ.nat (fun _ => PQ.lam PQ.nat (fun ih => PQ.call PNatDiv [ih;PQ.two])); y]))).
Definition pr_complete_divmod_env := env <- pr_divmod_env ;;
  env <- pr_install env PNatMod pr_mod_body ;; pr_install env PNatDiv pr_div_body.
Example primitive_right_shift_uses_classified_division :
  (env <- pr_complete_divmod_env ;; _ <- pr_install env PNatShiftRight pr_shift_right ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

(* A monomorphic instance of the compiler's packed Nat-measure recursion.
   Proof constants below stand for ordinary true arithmetic theorems in the
   already-checked object environment; they are not Rocq axioms. *)
Definition pr_pair := PQ.const ["PrimitivePair"] [].
Definition pr_pair_mk x y := PQ.apps (PQ.const ["PrimitivePair";"mk"] []) [x;y].
Definition pr_pair_proj i (p : PQ.term) : PQ.term :=
  fun depth => EProj (core_name "PrimitivePair") i (p depth).
Definition pr_pair_decls :=
  [pr_decl (core_name "PrimitivePair") pr_type
    (DInductive (pr_ind (core_name "PrimitivePair") [primitive_path ["PrimitivePair";"mk"]] false)) None;
   pr_decl (primitive_path ["PrimitivePair";"mk"])
     (PQ.run (PQ.arrow PQ.nat (PQ.arrow PQ.nat pr_pair)))
     (DConstructor (pr_ctor (core_name "PrimitivePair") 0 2)) None].
Definition pr_wf_motive alpha := PQ.arrow alpha PQ.type0.
Definition pr_wf_dom alpha motive meas x := PQ.pi alpha (fun y =>
  PQ.arrow (primitive_le (PQ.succ (PQ.app meas y)) (PQ.app meas x)) (PQ.app motive y)).
Definition pr_wf_functional alpha motive meas := PQ.pi alpha (fun x =>
  PQ.arrow (pr_wf_dom alpha motive meas x) (PQ.app motive x)).
Definition pr_wf_binders (k : PQ.term -> PQ.term -> PQ.term -> PQ.term -> PQ.term) :=
  PQ.lam PQ.type0 (fun alpha => PQ.lam (pr_wf_motive alpha) (fun motive =>
    PQ.lam (PQ.arrow alpha PQ.nat) (fun meas =>
      PQ.lam (pr_wf_functional alpha motive meas) (k alpha motive meas)))).
Definition pr_wf_type_binders (k : PQ.term -> PQ.term -> PQ.term -> PQ.term) :=
  PQ.pi PQ.type0 (fun alpha => PQ.pi (pr_wf_motive alpha) (fun motive =>
    PQ.pi (PQ.arrow alpha PQ.nat) (fun meas =>
      PQ.arrow (pr_wf_functional alpha motive meas) (k alpha motive meas)))).
Definition pr_wf_go_range alpha motive meas t := PQ.pi alpha (fun x =>
  PQ.arrow (primitive_le (PQ.succ (PQ.app meas x)) t) (PQ.app motive x)).
Definition pr_wf_go_type := pr_wf_type_binders (fun a m f =>
  PQ.pi PQ.nat (pr_wf_go_range a m f)).
Definition pr_wf_go_body := pr_wf_binders (fun a m f functional =>
  PQ.lam PQ.nat (fun t => PQ.apps (PQ.const ["Nat";"rec"] [])
    [PQ.lam PQ.nat (pr_wf_go_range a m f);
     PQ.lam a (fun x => PQ.lam (primitive_le (PQ.succ (PQ.app f x)) PQ.zero) (fun h =>
       PQ.apps (PQ.const ["False";"elim"] [LSucc LZero]) [PQ.app m x;
         PQ.apps (PQ.const ["Nat";"not_succ_le_zero"] []) [PQ.app f x;h]]));
     PQ.lam PQ.nat (fun t => PQ.lam (pr_wf_go_range a m f t) (fun ih =>
       PQ.lam a (fun x => PQ.lam (primitive_le (PQ.succ (PQ.app f x)) (PQ.succ t)) (fun h =>
         PQ.apps functional [x;PQ.lam a (fun y =>
           PQ.lam (primitive_le (PQ.succ (PQ.app f y)) (PQ.app f x)) (fun hy =>
             PQ.apps ih [y;PQ.apps (PQ.const ["PrimitiveWF";"decrease"] [])
               [PQ.app f x;PQ.app f y;t;hy;h]]))])))); t])).
Definition pr_wf_fix_type := pr_wf_type_binders (fun a m _ => PQ.pi a (PQ.app m)).
Definition pr_wf_fix_body := pr_wf_binders (fun a m f functional => PQ.lam a (fun x =>
  PQ.apps (PQ.const ["WellFounded";"Nat";"fix";"go"] [LSucc LZero;LSucc LZero])
    [a;m;f;functional;PQ.app (PQ.const ["WellFounded";"Nat";"eager"] []) (PQ.succ (PQ.app f x));
     x;PQ.app (PQ.const ["PrimitiveWF";"bound"] []) (PQ.app f x)])).
Definition pr_wf_definition parts ty body : declaration :=
  {| decl_hints := HintOpaque; decl_name := primitive_path parts; decl_params := [core_name "u";core_name "v"];
     decl_type := PQ.run ty; decl_value := Some (PQ.run body); decl_kind_of := DDefinition |}.
Definition pr_wf_go_decl := pr_wf_definition ["WellFounded";"Nat";"fix";"go"]
  pr_wf_go_type pr_wf_go_body.
Definition pr_wf_fix_decl := pr_wf_definition ["WellFounded";"Nat";"fix"]
  pr_wf_fix_type pr_wf_fix_body.
Definition pr_wf_helpers :=
  [pr_wf_go_decl;pr_wf_fix_decl;
   pr_definition ["WellFounded";"Nat";"eager"] (PQ.arrow PQ.nat PQ.nat)
     (PQ.lam PQ.nat (fun x => primitive_condition_ite PCBool PQ.nat [PQ.call PNatBEq [x;x]] x x));
   pr_proof_constant ["PrimitiveWF";"decrease"] (PQ.pi PQ.nat (fun x => PQ.pi PQ.nat (fun y =>
     PQ.pi PQ.nat (fun t => PQ.arrow (primitive_le (PQ.succ y) x)
       (PQ.arrow (primitive_le (PQ.succ x) (PQ.succ t)) (primitive_le (PQ.succ y) t))))));
   pr_proof_constant ["PrimitiveWF";"bound"] (PQ.pi PQ.nat (fun x =>
     primitive_le (PQ.succ x) (PQ.app (PQ.const ["WellFounded";"Nat";"eager"] []) (PQ.succ x))));
   pr_proof_constant ["Nat";"zero_lt_succ"] (PQ.pi PQ.nat (fun x => primitive_le PQ.one (PQ.succ x)));
   pr_proof_constant ["Nat";"mod_lt"] (PQ.pi PQ.nat (fun x => PQ.pi PQ.nat (fun y =>
     PQ.arrow (primitive_le PQ.one y) (primitive_le (PQ.succ (PQ.call PNatMod [x;y])) y))));
   pr_proof_constant ["Nat";"bitwise_rec_lemma"] (PQ.pi PQ.nat (fun n =>
     PQ.arrow (PQ.not (PQ.eq PQ.nat n PQ.zero)) (primitive_le (PQ.succ (PQ.call PNatDiv [n;PQ.two])) n)))].
Definition pr_wf_env := env <- pr_complete_divmod_env ;;
  Accept (List.app pr_pair_decls (List.app pr_wf_helpers env)).
Definition pr_pair_motive := PQ.lam pr_pair (fun _ => PQ.nat).
Definition pr_pair_measure := PQ.lam pr_pair (pr_pair_proj 0).
Definition pr_pair_dom p := pr_wf_dom pr_pair pr_pair_motive pr_pair_measure p.
Definition pr_wf_unary functional p :=
  PQ.apps (PQ.const ["WellFounded";"Nat";"fix"] [LSucc LZero;LSucc LZero])
    [pr_pair;pr_pair_motive;pr_pair_measure;functional;p].
Definition pr_gcd_functional := PQ.lam pr_pair (fun p => PQ.lam (pr_pair_dom p) (fun ih =>
  let n := pr_pair_proj 1 p in
  let motive m := PQ.arrow (pr_pair_dom (pr_pair_mk m n)) PQ.nat in
  PQ.app (PQ.apps (PQ.const ["Nat";"rec"] [])
    [PQ.lam PQ.nat motive;
     PQ.lam (pr_pair_dom (pr_pair_mk PQ.zero n)) (fun _ => n);
     PQ.lam PQ.nat (fun m => PQ.lam (motive m) (fun _ =>
       PQ.lam (pr_pair_dom (pr_pair_mk (PQ.succ m) n)) (fun ih =>
         PQ.apps ih [pr_pair_mk (PQ.call PNatMod [n;PQ.succ m]) (PQ.succ m);
           PQ.apps (PQ.const ["Nat";"mod_lt"] []) [n;PQ.succ m;
             PQ.app (PQ.const ["Nat";"zero_lt_succ"] []) m]])));
     pr_pair_proj 0 p]) ih)).
Definition pr_gcd_unary := pr_definition ["PrimitiveGcdUnary"] (PQ.arrow pr_pair PQ.nat)
  (PQ.lam pr_pair (pr_wf_unary pr_gcd_functional)).
Definition pr_gcd_body := PQ.run (PQ.lam PQ.nat (fun m => PQ.lam PQ.nat (fun n =>
  PQ.app (PQ.const ["PrimitiveGcdUnary"] []) (pr_pair_mk m n)))).
Definition pr_gcd_env := env <- pr_wf_env ;; Accept (pr_gcd_unary :: env).
Example primitive_well_founded_go_fixture_is_typed :
  (env <- pr_wf_env ;; check 512 env [] empty_context (PQ.run pr_wf_go_body) (PQ.run pr_wf_go_type)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_well_founded_fix_fixture_is_typed :
  (env <- pr_wf_env ;; check 512 env [] empty_context (PQ.run pr_wf_fix_body) (PQ.run pr_wf_fix_type)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_well_founded_go_symbolic_step :
  (env <- pr_wf_env ;; primitive_check_go 512 env InductiveUtils.initial_ind_state
    (PQ.run (PQ.const ["WellFounded";"Nat";"fix";"go"] [LSucc LZero;LSucc LZero]))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_gcd_functional_is_typed :
  (env <- pr_gcd_env ;; check 512 env [] empty_context (PQ.run pr_gcd_functional)
    (PQ.run (pr_wf_functional pr_pair pr_pair_motive pr_pair_measure))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_gcd_equations_use_an_arbitrary_induction_hypothesis :
  (env <- pr_gcd_env ;; _ <- pr_install env PNatGcd pr_gcd_body ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition pr_bitwise_functional (wrong_digit : bool) f :=
  PQ.lam pr_pair (fun p => PQ.lam (pr_pair_dom p) (fun ih =>
    let n := pr_pair_proj 0 p in let m := pr_pair_proj 1 p in
    let choose b x y := primitive_condition_ite PCBool PQ.nat [b] x y in
    primitive_condition_dite PCNatEq [n;PQ.zero]
      (fun _ => choose (PQ.apps f [PQ.fal;PQ.tru]) m PQ.zero)
      (fun hn => primitive_condition_ite PCNatEq PQ.nat [m;PQ.zero]
        (choose (PQ.apps f [PQ.tru;PQ.fal]) n PQ.zero)
        (let half_n := PQ.call PNatDiv [n;PQ.two] in
         let half_m := PQ.call PNatDiv [m;PQ.two] in
         let r := PQ.apps ih [pr_pair_mk half_n half_m;
           PQ.apps (PQ.const ["Nat";"bitwise_rec_lemma"] []) [n;hn]] in
         let doubled := PQ.call PNatAdd [r;r] in
         let odd x := primitive_condition_decide PCNatEq [PQ.call PNatMod [x;PQ.two];PQ.one] in
         choose (PQ.apps f [odd n;odd m])
           (PQ.call PNatAdd [doubled;if wrong_digit then PQ.two else PQ.one]) doubled)))).
Definition pr_bitwise_unary (wrong_digit : bool) := pr_definition ["PrimitiveBitwiseUnary"]
  (PQ.arrow (PQ.embed primitive_bool_operator_type) (PQ.arrow pr_pair PQ.nat))
  (PQ.lam (PQ.embed primitive_bool_operator_type) (fun f =>
    PQ.lam pr_pair (pr_wf_unary (pr_bitwise_functional wrong_digit f)))).
Definition pr_bitwise_body := PQ.run (PQ.lam (PQ.embed primitive_bool_operator_type) (fun f =>
  PQ.lam PQ.nat (fun n => PQ.lam PQ.nat (fun m =>
    PQ.apps (PQ.const ["PrimitiveBitwiseUnary"] []) [f;pr_pair_mk n m])))).
Definition pr_bitwise_type := PQ.run (PQ.arrow (PQ.embed primitive_bool_operator_type)
  (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.nat))).
Definition pr_bitwise_env := env <- pr_wf_env ;; Accept (pr_bitwise_unary false :: env).
Example primitive_bitwise_body_and_functional_are_typed :
  (env <- pr_bitwise_env ;;
   _ <- check 512 env [] empty_context (PQ.run (PQ.lam (PQ.embed primitive_bool_operator_type)
     (pr_bitwise_functional false)))
     (PQ.run (PQ.arrow (PQ.embed primitive_bool_operator_type)
       (pr_wf_functional pr_pair pr_pair_motive pr_pair_measure))) ;;
   check 512 env [] empty_context pr_bitwise_body pr_bitwise_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_equation_has_symbolic_operator_and_induction_hypothesis :
  (env <- pr_bitwise_env ;; primitive_check_bitwise 512 env pr_bitwise_body) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_wrong_output_bit_is_well_typed :
  (env <- pr_wf_env ;; check 512 env [] empty_context
    (PQ.run (PQ.lam (PQ.embed primitive_bool_operator_type) (pr_bitwise_functional true)))
    (PQ.run (PQ.arrow (PQ.embed primitive_bool_operator_type)
      (pr_wf_functional pr_pair pr_pair_motive pr_pair_measure)))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_wrong_output_bit_rejected :
  (env <- pr_wf_env ;; primitive_check_bitwise 512
    (pr_bitwise_unary true :: env) pr_bitwise_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Definition pr_gcd_impostor_functional := PQ.lam pr_pair (fun p =>
  PQ.lam (pr_pair_dom p) (fun _ => pr_pair_proj 1 p)).
Definition pr_gcd_impostor_unary := pr_definition ["PrimitiveGcdUnary"] (PQ.arrow pr_pair PQ.nat)
  (PQ.lam pr_pair (pr_wf_unary pr_gcd_impostor_functional)).
Example primitive_gcd_impostor_base_case_still_passes :
  (env <- pr_gcd_env ;;
   let env := pr_replace pr_gcd_impostor_unary env in
   p <- primitive_unfold_nat_well_founded 512 env InductiveUtils.initial_ind_state
     pr_gcd_body primitive_first_measure ;;
   let '(n,sn) := InductiveUtils.ind_fresh InductiveUtils.initial_ind_state NameAnon BDefault core_nat in
   primitive_run_probe 512 env sn p [primitive_zero;InductiveUtils.local_expr n]
     (fun _ => InductiveUtils.local_expr n)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_gcd_rejects_functional_that_ignores_ih :
  (env <- pr_gcd_env ;; pr_classify (pr_replace pr_gcd_impostor_unary env) PNatGcd pr_gcd_body) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Definition pr_gcd_captured_unary := pr_definition ["PrimitiveGcdUnary"] (PQ.arrow pr_pair PQ.nat)
  (PQ.lam pr_pair (fun p => pr_wf_unary
    (PQ.lam pr_pair (fun q => PQ.lam (pr_pair_dom q) (fun _ => pr_pair_proj 1 p))) p)).
Example primitive_well_founded_functional_must_not_capture_recursion_arguments :
  pr_rejected (env <- pr_gcd_env ;; pr_classify
    (pr_replace pr_gcd_captured_unary env) PNatGcd pr_gcd_body) = true.
Proof. vm_compute. reflexivity. Qed.
Definition pr_bool_and := PQ.run (PQ.lam PQ.bool (fun x => PQ.lam PQ.bool (fun y =>
  pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (fun _ => PQ.bool)) PQ.fal y x))).
Definition pr_bool_or := PQ.run (PQ.lam PQ.bool (fun x => PQ.lam PQ.bool (fun y =>
  pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (fun _ => PQ.bool)) y PQ.tru x))).
Definition pr_bool_xor := PQ.run (PQ.lam PQ.bool (fun x => PQ.lam PQ.bool (fun y =>
  pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (fun _ => PQ.bool)) y
    (pr_qbool_rec (LSucc LZero) (PQ.lam PQ.bool (fun _ => PQ.bool)) PQ.tru PQ.fal y) x))).
Example primitive_and_operator_equations :
  primitive_check_boolean_operator 256 pr_logic_env PNatLAnd pr_bool_and = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_or_operator_equations :
  primitive_check_boolean_operator 256 pr_logic_env PNatLOr pr_bool_or = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_xor_operator_equations :
  primitive_check_boolean_operator 256 pr_logic_env PNatXor pr_bool_xor = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_and_cannot_use_or :
  primitive_check_boolean_operator 256 pr_logic_env PNatLAnd pr_bool_or = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_xor_cannot_use_or :
  primitive_check_boolean_operator 256 pr_logic_env PNatXor pr_bool_or = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.

Example primitive_divmod_helper_fuel_exhaustion_is_a_decline :
  (env <- pr_divmod_env ;; primitive_check_fuel_rec 0 env true pr_mod_body) = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example primitive_well_founded_telescope_is_fuel_bounded :
  primitive_lambda_telescope 0 256 pr_env InductiveUtils.initial_ind_state pr_gcd_body =
    Decline OutOfFuel.
Proof. reflexivity. Qed.
Example primitive_unsupported_well_founded_form_is_not_authenticated :
  (env <- pr_gcd_env ;; pr_classify env PNatGcd pr_fake_add) = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_dependent_boolean_condition_is_explicitly_unsupported :
  primitive_check_condition 256 pr_logic_env PCBool true true = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
(* The pinned late String.ofList hook runs after delta unfolding. This fixture
   aliases String to recursive List, so structure eta cannot recover expansion. *)
Example primitive_text_literal_alias_misses_the_late_expansion_hook :
  (env <- pr_install pr_text_env PCharOfNat pr_char_body ;;
   env <- pr_install env PStringOfList pr_string_body ;;
   check_defeq 256 env [] empty_context (ELit (LitString "A"))
     (PQ.run (PQ.app (PQ.const ["String";"ofList"] [])
       (PQ.apps (PQ.const ["List";"cons"] [LZero])
         [PQ.embed primitive_char;PQ.call PCharOfNat [PQ.embed (ELit (LitNat 65))];
          PQ.app (PQ.const ["List";"nil"] [LZero]) (PQ.embed primitive_char)])))) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_text_gate_is_not_an_equation_certificate :
  primitive_is_text PCharOfNat = true /\ primitive_is_text PStringOfList = true /\
  primitive_equations PCharOfNat pr_char_body = None /\
  primitive_equations PStringOfList pr_string_body = None.
Proof. repeat split; reflexivity. Qed.

Definition pr_bitwise_instance_body operator :=
  EApp (EConst primitive_bitwise_name []) operator.
Definition pr_authenticated_bitwise_env := env <- pr_bitwise_env ;;
  pr_install env PNatBitwise pr_bitwise_body.
Definition pr_all_bitwise_env := env <- pr_authenticated_bitwise_env ;;
  env <- pr_install env PNatLAnd (pr_bitwise_instance_body pr_bool_and) ;;
  env <- pr_install env PNatLOr (pr_bitwise_instance_body pr_bool_or) ;;
  pr_install env PNatXor (pr_bitwise_instance_body pr_bool_xor).

Example primitive_bitwise_signature_is_the_higher_order_interface :
  primitive_signature PNatBitwise = pr_bitwise_type.
Proof. reflexivity. Qed.
Example primitive_every_kind_has_a_reserved_hierarchical_name :
  map (fun op => primitive_lookup (primitive_name op)) primitive_kinds =
    map (@Some primitive_kind) primitive_kinds /\ List.length primitive_kinds = 18.
Proof. split; reflexivity. Qed.
Example primitive_bitwise_classification_issues_its_distinct_metadata :
  (env <- pr_authenticated_bitwise_env ;; d <- get_constant env [] primitive_bitwise_name [] ;;
   Accept (decl_kind_of d)) = Accept (DPrimitive PNatBitwise).
Proof. vm_compute. reflexivity. Qed.
Example primitive_land_requires_typed_classified_bitwise :
  (env <- pr_authenticated_bitwise_env ;;
   _ <- pr_install env PNatLAnd (pr_bitwise_instance_body pr_bool_and) ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_lor_requires_typed_classified_bitwise :
  (env <- pr_authenticated_bitwise_env ;;
   _ <- pr_install env PNatLOr (pr_bitwise_instance_body pr_bool_or) ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_xor_requires_typed_classified_bitwise :
  (env <- pr_authenticated_bitwise_env ;;
   _ <- pr_install env PNatXor (pr_bitwise_instance_body pr_bool_xor) ;; Accept tt) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_acceleration_only_after_complete_equation_chain :
  (env <- pr_all_bitwise_env ;;
   a <- whnf 64 env [] empty_context (primitive_call PNatLAnd [ELit (LitNat 6); ELit (LitNat 10)]) ;;
   o <- whnf 64 env [] empty_context (primitive_call PNatLOr [ELit (LitNat 6); ELit (LitNat 10)]) ;;
   x <- whnf 64 env [] empty_context (primitive_call PNatXor [ELit (LitNat 6); ELit (LitNat 10)]) ;;
   Accept [a;o;x]) = Accept [ELit (LitNat 2);ELit (LitNat 14);ELit (LitNat 12)].
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_wrong_digit_cannot_obtain_metadata :
  (env <- pr_wf_env ;; pr_install (pr_bitwise_unary true :: env) PNatBitwise pr_bitwise_body) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_cannot_use_binary_nat_signature :
  classify_primitive 256 pr_env primitive_bitwise_name [] (primitive_signature PNatAdd) pr_fake_add =
    Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_cannot_have_universe_parameters :
  classify_primitive 256 pr_env primitive_bitwise_name [core_name "u"]
    (primitive_signature PNatBitwise) pr_bitwise_body = Reject UniverseArity.
Proof. vm_compute. reflexivity. Qed.
Definition pr_binary_bitwise_cases :=
  [(PNatLAnd,pr_bool_and);(PNatLOr,pr_bool_or);(PNatXor,pr_bool_xor)].
Definition pr_bitwise_instances env := map (fun c =>
  let '(op,operator) := c in pr_classify env op (pr_bitwise_instance_body operator))
  pr_binary_bitwise_cases.
Definition pr_forged_bitwise kind ty value := pr_decl primitive_bitwise_name ty kind value.
Example primitive_all_bitwise_instances_reject_name_type_only_dependency :
  (env <- pr_bitwise_env ;; Accept (pr_bitwise_instances
    (pr_forged_bitwise DDefinition pr_bitwise_type (Some pr_bitwise_body) :: env))) =
    Accept (repeat (Reject MalformedDeclaration) 3).
Proof. vm_compute. reflexivity. Qed.
Example primitive_all_bitwise_instances_reject_wrong_metadata_kind :
  (env <- pr_bitwise_env ;; Accept (pr_bitwise_instances
    (pr_forged_bitwise (DPrimitive PNatAdd) pr_bitwise_type (Some pr_bitwise_body) :: env))) =
    Accept (repeat (Reject MalformedDeclaration) 3).
Proof. vm_compute. reflexivity. Qed.
Example primitive_all_bitwise_instances_reject_wrong_dependency_signature :
  (env <- pr_bitwise_env ;; Accept (pr_bitwise_instances
    (pr_forged_bitwise (DPrimitive PNatBitwise) (primitive_signature PNatAdd)
      (Some pr_bitwise_body) :: env))) = Accept (repeat (Reject TypeMismatch) 3).
Proof. vm_compute. reflexivity. Qed.
Example primitive_all_bitwise_instances_require_a_retained_definition :
  (env <- pr_bitwise_env ;; Accept (pr_bitwise_instances
    (pr_forged_bitwise (DPrimitive PNatBitwise) pr_bitwise_type None :: env))) =
    Accept (repeat (Reject MalformedDeclaration) 3).
Proof. vm_compute. reflexivity. Qed.
Example primitive_land_wrong_boolean_equations_rejected :
  (env <- pr_authenticated_bitwise_env ;;
   pr_install env PNatLAnd (pr_bitwise_instance_body pr_bool_or)) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_lor_wrong_boolean_equations_rejected :
  (env <- pr_authenticated_bitwise_env ;;
   pr_install env PNatLOr (pr_bitwise_instance_body pr_bool_and)) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_xor_wrong_boolean_equations_rejected :
  (env <- pr_authenticated_bitwise_env ;;
   pr_install env PNatXor (pr_bitwise_instance_body pr_bool_or)) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_instances_require_the_canonical_head :
  (env <- pr_authenticated_bitwise_env ;;
   let alias := pr_decl (core_name "OtherBitwise") pr_bitwise_type DDefinition (Some pr_bitwise_body) in
   pr_install (alias :: env) PNatLAnd (EApp (EConst (core_name "OtherBitwise") []) pr_bool_and)) =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_instance_unknown_wrapper_declines :
  (env <- pr_authenticated_bitwise_env ;;
   pr_install env PNatLAnd (EMData (pr_bitwise_instance_body pr_bool_and))) =
    Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example primitive_bitwise_classifier_fuel_exhaustion_declines :
  classify_primitive 0 pr_env primitive_bitwise_name [] pr_bitwise_type pr_bitwise_body = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example primitive_bitwise_cannot_certify_itself_circularly :
  (env <- pr_authenticated_bitwise_env ;; pr_classify env PNatBitwise (EConst primitive_bitwise_name [])) =
    Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.
