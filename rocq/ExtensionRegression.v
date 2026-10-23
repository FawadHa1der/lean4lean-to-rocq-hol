(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Core reduction tests with explicit kernel metadata fixtures. Admission is
   tested separately by the parent; these fixtures are not parsed certificates. *)
From Coq Require Import List String Ascii NArith Bool.
From LeanPort Require Import Syntax Universes Checker Regression.
Import ListNotations.
Open Scope string_scope.

Definition ext_ctor (parent : name) (index fields : nat) : constructor_data :=
  {| ctor_induct := parent; ctor_index := index; ctor_num_params := 0;
     ctor_num_fields := fields; ctor_is_unsafe := false |}.
Definition ext_ind (n : name) (ctors : list name) (recursive : bool) : inductive_data :=
  {| ind_num_params := 0; ind_num_indices := 0; ind_all := [n]; ind_ctors := ctors;
     ind_num_nested := 0; ind_is_rec := recursive; ind_is_reflexive := false;
     ind_is_unsafe := false |}.
Definition ext_decl (n : name) (ty : expr) (kind : decl_kind) (value : option expr) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := ty;
     decl_value := value; decl_kind_of := kind |}.
Definition ext_nat_decl := ext_decl core_nat_name type0
  (DInductive (ext_ind core_nat_name [core_zero_name; core_succ_name] true)) None.
Definition ext_zero_decl := ext_decl core_zero_name core_nat
  (DConstructor (ext_ctor core_nat_name 0 0)) None.
Definition ext_succ_decl := ext_decl core_succ_name (EPi NameAnon BDefault core_nat core_nat)
  (DConstructor (ext_ctor core_nat_name 1 1)) None.
Definition ext_nat_env := [ext_succ_decl; ext_zero_decl; ext_nat_decl].

Definition ext_box_name := nm "Box".
Definition ext_box_mk := NameStr ext_box_name "mk".
Definition ext_box := EConst ext_box_name [].
Definition ext_box_decl := ext_decl ext_box_name type0
  (DInductive (ext_ind ext_box_name [ext_box_mk] false)) None.
Definition ext_box_ctor := ext_decl ext_box_mk (EPi NameAnon BDefault core_nat ext_box)
  (DConstructor (ext_ctor ext_box_name 0 1)) None.
Definition ext_box_env := ext_box_ctor :: ext_box_decl :: ext_nat_env.
Definition ext_box_value := EApp (EConst ext_box_mk []) (ELit (LitNat 42)).
Definition ext_box_ctx : context :=
  {| bound_context := []; free_context :=
     [(nm "b", {| binding_type := ext_box; binding_value := None |})] |}.

Definition ext_box_motive := EPi NameAnon BDefault ext_box type0.
Definition ext_box_minor := EPi NameAnon BDefault core_nat
  (EApp (EBVar 1) (EApp (EConst ext_box_mk []) (EBVar 0))).
Definition ext_box_rec_type := EPi NameAnon BDefault ext_box_motive
  (EPi NameAnon BDefault ext_box_minor
    (EPi NameAnon BDefault ext_box (EApp (EBVar 2) (EBVar 0)))).
Definition ext_box_rule := ELam NameAnon BDefault ext_box_motive
  (ELam NameAnon BDefault ext_box_minor
    (ELam NameAnon BDefault core_nat (EApp (EBVar 1) (EBVar 0)))).
Definition ext_box_rec_data : recursor_data :=
  {| rec_all := [ext_box_name]; rec_num_params := 0; rec_num_indices := 0;
     rec_num_motives := 1; rec_num_minors := 1;
     rec_rules := [{| rule_ctor := ext_box_mk; rule_nfields := 1; rule_rhs := ext_box_rule |}];
     rec_k := false; rec_is_unsafe := false |}.
Definition ext_box_rec_name := NameStr ext_box_name "rec".
Definition ext_box_rec_decl := ext_decl ext_box_rec_name ext_box_rec_type
  (DRecursor ext_box_rec_data) None.
Definition ext_rec_env := ext_box_rec_decl :: ext_box_env.
Definition ext_unbox (b : expr) := core_apps (EConst ext_box_rec_name [])
  [ELam NameAnon BDefault ext_box core_nat;
   ELam NameAnon BDefault core_nat (EBVar 0); b].

Example binary_literal_inference :
  infer 32 ext_nat_env [] empty_context
    (ELit (LitNat 184467440737095516160000000000000000000%N)) = Accept core_nat.
Proof. vm_compute. reflexivity. Qed.
Example binary_successor_no_machine_overflow :
  whnf 32 ext_nat_env [] empty_context
    (EApp (EConst core_succ_name []) (ELit (LitNat 184467440737095516160000000000000000000%N))) =
    Accept (ELit (LitNat 184467440737095516160000000000000000001%N)).
Proof. vm_compute. reflexivity. Qed.
Example binary_zero_constructor_equivalence :
  check_defeq 32 ext_nat_env [] empty_context (EConst core_zero_name []) (ELit (LitNat 0)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example malformed_nat_shape_does_not_enable_literals :
  infer 32 [ext_nat_decl] [] empty_context (ELit (LitNat 42)) = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example binary_add_unbounded :
  core_binary_nat 32 ext_nat_env PNatAdd 184467440737095516160000000000000000000 1 =
    Accept (Some (ELit (LitNat 184467440737095516160000000000000000001%N))).
Proof. vm_compute. reflexivity. Qed.
Example binary_div_zero : core_binary_nat 32 ext_nat_env PNatDiv 42 0 =
  Accept (Some (ELit (LitNat 0))).
Proof. vm_compute. reflexivity. Qed.
Example binary_mod_zero : core_binary_nat 32 ext_nat_env PNatMod 42 0 =
  Accept (Some (ELit (LitNat 42))).
Proof. vm_compute. reflexivity. Qed.
Example binary_sub_saturates : core_binary_nat 32 ext_nat_env PNatSub 2 3 =
  Accept (Some (ELit (LitNat 0))).
Proof. vm_compute. reflexivity. Qed.
Example binary_gcd : core_binary_nat 32 ext_nat_env PNatGcd 84 30 =
  Accept (Some (ELit (LitNat 6))).
Proof. vm_compute. reflexivity. Qed.
Example binary_bitwise : core_binary_nat 32 ext_nat_env PNatXor 42 15 =
  Accept (Some (ELit (LitNat 37))).
Proof. vm_compute. reflexivity. Qed.
Example bitwise_tag_has_no_binary_acceleration :
  core_binary_nat 32 ext_nat_env PNatBitwise 42 15 = Accept None.
Proof. reflexivity. Qed.
Example bitwise_tag_distinct_from_xor : primitive_kind_eqb PNatBitwise PNatXor = false.
Proof. reflexivity. Qed.
Example binary_large_exponent_declines : core_binary_nat 32 ext_nat_env PNatPow 2 1000000 =
  Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example binary_huge_right_shift_short_circuits :
  core_binary_nat 32 ext_nat_env PNatShiftRight 184467440737095516160000000000000000000
    184467440737095516160000000000000000000 = Accept (Some (ELit (LitNat 0))).
Proof. vm_compute. reflexivity. Qed.

Definition ext_fake_add := ext_decl (NameStr core_nat_name "add")
  (EPi NameAnon BDefault core_nat (EPi NameAnon BDefault core_nat core_nat))
  DDefinition (Some (ELam NameAnon BDefault core_nat
    (ELam NameAnon BDefault core_nat (EBVar 1)))).
Example name_alone_never_enables_arithmetic :
  whnf 32 (ext_fake_add :: ext_nat_env) [] empty_context
    (core_apps (EConst (NameStr core_nat_name "add") []) [ELit (LitNat 2); ELit (LitNat 3)]) =
    Accept (ELit (LitNat 2)).
Proof. vm_compute. reflexivity. Qed.
Definition ext_succ_alias := ext_decl (nm "succ_alias")
  (EPi NameAnon BDefault core_nat core_nat) DDefinition (Some (EConst core_succ_name [])).
Example delta_restarts_native_head_reduction :
  whnf 32 (ext_succ_alias :: ext_nat_env) [] empty_context
    (EApp (EConst (nm "succ_alias") []) (ELit (LitNat 42))) = Accept (ELit (LitNat 43)).
Proof. vm_compute. reflexivity. Qed.

Example projection_inference :
  infer 64 ext_box_env [] empty_context (EProj ext_box_name 0 ext_box_value) = Accept core_nat.
Proof. vm_compute. reflexivity. Qed.
Example projection_iota :
  whnf 32 ext_box_env [] empty_context (EProj ext_box_name 0 ext_box_value) = Accept (ELit (LitNat 42)).
Proof. vm_compute. reflexivity. Qed.
Example projection_bad_index_rejects :
  infer 32 ext_box_env [] empty_context (EProj ext_box_name 1 ext_box_value) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example projection_bad_owner_does_not_reduce :
  whnf 32 ext_box_env [] empty_context (EProj core_nat_name 0 ext_box_value) =
    Accept (EProj core_nat_name 0 ext_box_value).
Proof. vm_compute. reflexivity. Qed.
Example structure_eta_checked :
  check_defeq 128 ext_box_env [] ext_box_ctx (EFVar (nm "b"))
    (EApp (EConst ext_box_mk []) (EProj ext_box_name 0 (EFVar (nm "b")))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example constructor_recursor_iota :
  whnf 64 ext_rec_env [] empty_context (ext_unbox ext_box_value) = Accept (ELit (LitNat 42)).
Proof. vm_compute. reflexivity. Qed.
Example constructor_recursor_checked :
  check_defeq 128 ext_rec_env [] empty_context (ext_unbox ext_box_value) (ELit (LitNat 42)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example structure_recursor_eta :
  check_defeq 128 ext_rec_env [] ext_box_ctx (ext_unbox (EFVar (nm "b")))
    (EProj ext_box_name 0 (EFVar (nm "b"))) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

Definition ext_utf8_emoji := String (ascii_of_nat 240)
  (String (ascii_of_nat 159) (String (ascii_of_nat 152) (String (ascii_of_nat 128) EmptyString))).
Example utf8_ascii : core_utf8 "ab" = Some [97%N; 98%N].
Proof. vm_compute. reflexivity. Qed.
Example utf8_supplementary_scalar : core_utf8 ext_utf8_emoji = Some [128512%N].
Proof. vm_compute. reflexivity. Qed.
Example utf8_reject_overlong :
  core_utf8 (String (ascii_of_nat 192) (String (ascii_of_nat 128) EmptyString)) = None.
Proof. vm_compute. reflexivity. Qed.
Example utf8_reject_surrogate : core_utf8 (String (ascii_of_nat 237)
  (String (ascii_of_nat 160) (String (ascii_of_nat 128) EmptyString))) = None.
Proof. vm_compute. reflexivity. Qed.
Example string_expansion_preserves_codepoints : core_expand_string ext_utf8_emoji =
  Accept (EApp (EConst core_string_of_list []) (core_char_list [128512%N])).
Proof. vm_compute. reflexivity. Qed.
Example string_without_authenticated_primitives_declines :
  infer 32 ext_nat_env [] empty_context (ELit (LitString "x")) = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.

(* Layout-only fixtures exercise the internal reducer, not checked typing or
   admission of these headers. Canonical quotient admission belongs to Quotient.v. *)
Definition ext_q_name := nm "Quot".
Definition ext_q_mk := NameStr ext_q_name "mk".
Definition ext_q_lift := NameStr ext_q_name "lift".
Definition ext_q_ind := NameStr ext_q_name "ind".
Definition ext_q_env :=
  [ext_decl ext_q_mk prop (DQuotient QCtor) None;
   ext_decl ext_q_lift prop (DQuotient QLift) None;
   ext_decl ext_q_ind prop (DQuotient QInd) None].
Definition ext_q_value := core_apps (EConst ext_q_mk []) [type0; prop; prop].
Definition ext_q_function := ELam NameAnon BDefault type0 (EBVar 0).
Definition ext_q_lift_app := core_apps (EConst ext_q_lift [])
  [type0; prop; type0; ext_q_function; prop; ext_q_value].
Example quotient_lift_layout :
  core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context ext_q_lift_app =
    Accept (Some (EApp ext_q_function prop)).
Proof. vm_compute. reflexivity. Qed.
Example quotient_ind_layout :
  core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context
    (core_apps (EConst ext_q_ind []) [type0; prop; prop; ext_q_function; ext_q_value]) =
    Accept (Some (EApp ext_q_function prop)).
Proof. vm_compute. reflexivity. Qed.
Example quotient_reapplies_remaining_arguments :
  core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context
    (EApp ext_q_lift_app type0) = Accept (Some (EApp (EApp ext_q_function prop) type0)).
Proof. vm_compute. reflexivity. Qed.
Example quotient_partial_application_stays_stuck :
  core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context
    (core_apps (EConst ext_q_lift []) [type0; prop; type0; ext_q_function; prop]) = Accept None.
Proof. vm_compute. reflexivity. Qed.
Example quotient_name_without_tag_stays_stuck :
  core_reduce_quotient (checker 32 ext_q_env []) [] empty_context ext_q_lift_app = Accept None.
Proof. vm_compute. reflexivity. Qed.
Example quotient_constructor_wrong_arity_stays_stuck :
  core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context
    (core_apps (EConst ext_q_lift []) [type0; prop; type0; ext_q_function; prop;
      core_apps (EConst ext_q_mk []) [type0; prop]]) = Accept None.
Proof. vm_compute. reflexivity. Qed.

Definition ext_safety_name := nm "safety_test".
Definition ext_safety_decl kind := ext_decl ext_safety_name type0 kind (Some prop).
Definition ext_safety_term := EConst ext_safety_name [].
Example unsafe_definition_rejected_by_safe_inference :
  infer 32 [ext_safety_decl (DUnsafe DDefinition)] [] empty_context ext_safety_term =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example partial_definition_rejected_by_safe_inference :
  infer 32 [ext_safety_decl DPartial] [] empty_context ext_safety_term =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example unsafe_definition_never_delta_unfolds :
  whnf 32 [ext_safety_decl (DUnsafe DDefinition)] [] empty_context ext_safety_term =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example partial_definition_never_delta_unfolds :
  whnf 32 [ext_safety_decl DPartial] [] empty_context ext_safety_term =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example unsafe_role_does_not_bypass_checked_reflexivity :
  check_defeq 32 [ext_safety_decl (DUnsafe DTheorem)] [] empty_context
    ext_safety_term ext_safety_term = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_unsafe_role_rejected :
  get_constant [ext_safety_decl (DUnsafe (DUnsafe DOpaque))] [] ext_safety_name [] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example unwrapped_definition_retains_existing_behavior :
  whnf 32 [ext_safety_decl DDefinition] [] empty_context ext_safety_term = Accept prop.
Proof. vm_compute. reflexivity. Qed.

Definition extension_checks (_ : unit) : list bool :=
  [accepted (infer 32 ext_nat_env [] empty_context (ELit (LitNat 184467440737095516160000000000000000000%N)));
   accepted (check_defeq 32 ext_nat_env [] empty_context (EConst core_zero_name []) (ELit (LitNat 0)));
   accepted (check_defeq 128 ext_rec_env [] empty_context (ext_unbox ext_box_value) (ELit (LitNat 42)));
   accepted (check_defeq 128 ext_rec_env [] ext_box_ctx (ext_unbox (EFVar (nm "b")))
     (EProj ext_box_name 0 (EFVar (nm "b"))));
   accepted (check_defeq 128 ext_box_env [] ext_box_ctx (EFVar (nm "b"))
     (EApp (EConst ext_box_mk []) (EProj ext_box_name 0 (EFVar (nm "b")))));
   rejected (infer 32 ext_box_env [] empty_context (EProj ext_box_name 1 ext_box_value));
   match core_utf8 ext_utf8_emoji with Some [n] => N.eqb n 128512 | _ => false end;
   declined (core_binary_nat 32 ext_nat_env PNatPow 2 1000000);
   match core_reduce_quotient (checker 32 ext_q_env []) ext_q_env empty_context ext_q_lift_app with
   | Accept (Some e) => expr_eqb e (EApp ext_q_function prop) | _ => false end;
   match core_reduce_quotient (checker 32 ext_q_env []) [] empty_context ext_q_lift_app with
   | Accept None => true | _ => false end;
   rejected (infer 32 [ext_safety_decl (DUnsafe DDefinition)] [] empty_context ext_safety_term);
   rejected (whnf 32 [ext_safety_decl DPartial] [] empty_context ext_safety_term);
   match core_binary_nat 32 ext_nat_env PNatBitwise 42 15 with
   | Accept None => true | _ => false end].
Example extension_checks_all_true : forallb (fun b => b) (extension_checks tt) = true.
Proof. vm_compute. reflexivity. Qed.
