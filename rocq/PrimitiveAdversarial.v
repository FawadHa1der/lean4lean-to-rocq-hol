(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Independent bounded audit of primitive admission and trusted metadata.
   See docs/PRIMITIVE_AUDIT.md for fixture assumptions and findings. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Universes Checker InductiveUtils Primitives
  Declarations Safety PrimitiveRegression.
Import ListNotations.
Open Scope string_scope.

Definition pa_admit env op body := admit 512 env
  (InputDefinition HintOpaque (primitive_name op) [] (primitive_signature op) body InputSafe).
Definition pa_typed_decl env d :=
  match decl_value d with
  | Some body => check 512 env (decl_params d) empty_context body (decl_type d)
  | None => Reject MalformedDeclaration
  end.
Definition pa_expansion s := core_expand_string s.
Definition pa_compare_expansions env s t :=
  a <- pa_expansion s ;; b <- pa_expansion t ;; check_defeq 512 env [] empty_context a b.
Definition pa_text_env char_body string_body :=
  env <- pa_admit pr_text_env PCharOfNat char_body ;;
  pa_admit env PStringOfList string_body.

Example pa_text_positive_control_real_admission :
  pr_accepted (pa_text_env pr_char_body pr_string_body) = true.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_collapsed_representations_really_pass_admission :
  pr_accepted (pa_text_env pr_char_bad_body pr_string_bad_body) = true.
Proof. vm_compute. reflexivity. Qed.
Example pa_char_certificate_does_not_replace_its_body_by_a_codepoint :
  (env <- pa_text_env pr_char_bad_body pr_string_body ;;
   check_defeq 256 env [] empty_context
     (primitive_call PCharOfNat [ELit (LitNat 65)]) primitive_zero) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
(* A typed constant body is still retained, but mixed literal conversion does
   not broadly expand the literal after the String.ofList head has unfolded. *)
Example pa_string_literal_alias_does_not_broadly_expand :
  (env <- pa_text_env pr_char_body pr_string_bad_body ;;
   check_defeq 256 env [] empty_context (ELit (LitString "AB"))
     (EApp (EConst (NameStr core_list_name "nil") [LZero]) primitive_char)) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_tags_enable_no_binary_nat_acceleration :
  (env <- pa_text_env pr_char_bad_body pr_string_bad_body ;;
   a <- core_binary_nat 32 env PCharOfNat 65 66 ;;
   b <- core_binary_nat 32 env PStringOfList 65 66 ;; Accept (a,b)) = Accept (None,None).
Proof. vm_compute. reflexivity. Qed.
Example pa_text_identity_expansions_distinguish_codepoints :
  (env <- pa_text_env pr_char_body pr_string_body ;;
   pa_compare_expansions env "A" "B") = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_collapsed_char_expansions_are_convertible :
  (env <- pa_text_env pr_char_bad_body pr_string_body ;;
   pa_compare_expansions env "A" "B") = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_distinct_literal_fast_path_is_incomplete_for_collapsed_char :
  (env <- pa_text_env pr_char_bad_body pr_string_body ;;
   check_defeq 256 env [] empty_context (ELit (LitString "A")) (ELit (LitString "B"))) =
     Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_collapsed_string_expansions_are_convertible :
  (env <- pa_text_env pr_char_body pr_string_bad_body ;;
   pa_compare_expansions env "A" "") = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_distinct_literal_fast_path_is_incomplete_for_collapsed_string :
  (env <- pa_text_env pr_char_body pr_string_bad_body ;;
   check_defeq 256 env [] empty_context (ELit (LitString "A")) (ELit (LitString ""))) =
     Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.

Definition pa_collapsed_text_eq_env := env <- pa_text_env pr_char_bad_body pr_string_body ;;
  Accept (pr_eq_decl :: pr_refl_decl :: env).
Definition pa_literal_equality := PQ.run (PQ.eq (PQ.embed primitive_string)
  (PQ.embed (ELit (LitString "A"))) (PQ.embed (ELit (LitString "B")))).
Example pa_collapsed_text_literal_reflexivity_is_rejected_at_admission :
  (env <- pa_collapsed_text_eq_env ;;
   admit 512 env (InputTheorem (core_name "CollapsedTextLiteral") [] pa_literal_equality
     (PQ.run (PQ.refl (PQ.embed primitive_string) (PQ.embed (ELit (LitString "A"))))))) =
    Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
(* This alias representation no longer converts either literal to its explicit
   expansion. StringParityFixtures separately admits the full Eq environment. *)
Example pa_alias_proposition_rejects_expanded_reflexivity :
  (env <- pa_collapsed_text_eq_env ;; expansion <- pa_expansion "A" ;;
   admit 512 env (InputTheorem (core_name "CollapsedTextExpanded") [] pa_literal_equality
     (PQ.run (PQ.refl (PQ.embed primitive_string) (PQ.embed expansion))))) =
    Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.

(* This is a deliberate contract-violation probe, not an admission exploit. *)
Example pa_text_classifier_alone_relies_on_body_pretyping :
  classify_primitive 256 pr_char_env core_char_of_nat []
    (primitive_signature PCharOfNat) primitive_zero = Accept (Some PCharOfNat).
Proof. vm_compute. reflexivity. Qed.
Example pa_text_real_admission_rejects_the_untyped_body :
  pa_admit pr_char_env PCharOfNat primitive_zero = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example pa_text_reserved_unsafe_definition_cannot_skip_interface_checks :
  admit_extended 256 pr_char_env
    (InputDefinition HintOpaque core_char_of_nat [] (primitive_signature PCharOfNat)
      pr_char_body InputUnsafe) = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example pa_all_reserved_operations_reject_unsafe_tag_bypass :
  map (fun op => admit_extended 256 pr_text_env
    (InputDefinition HintOpaque (primitive_name op) [] (primitive_signature op) primitive_zero InputUnsafe))
    primitive_kinds = repeat (Reject MalformedDeclaration) 18.
Proof. vm_compute. reflexivity. Qed.

Definition pa_add_env := pa_admit pr_env PNatAdd pr_add.
Example pa_add_positive_control_retains_body_and_tag :
  (env <- pa_add_env ;; d <- get_constant env [] (primitive_name PNatAdd) [] ;;
   Accept (decl_kind_of d,decl_value d)) = Accept (DPrimitive PNatAdd,Some pr_add).
Proof. vm_compute. reflexivity. Qed.
Example pa_projection_add_is_typed_but_cannot_be_admitted :
  (check 256 pr_env [] empty_context pr_fake_add (primitive_signature PNatAdd),
   pa_admit pr_env PNatAdd pr_fake_add) = (Accept tt,Reject NotDefinitionallyEqual).
Proof. vm_compute. reflexivity. Qed.
Example pa_admission_cannot_overwrite_a_certified_body :
  (env <- pa_add_env ;; pa_admit env PNatAdd pr_fake_add) = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Definition pa_forged_add_env := pr_decl (primitive_name PNatAdd) (primitive_signature PNatAdd)
  (DPrimitive PNatAdd) (Some pr_fake_add) :: pr_env.
Example pa_forged_record_demonstrates_the_trusted_metadata_boundary :
  (primitive_authenticated 256 pa_forged_add_env PNatAdd,
   whnf 64 pa_forged_add_env [] empty_context (primitive_call PNatAdd [ELit (LitNat 1);ELit (LitNat 2)]),
   whnf 64 pa_forged_add_env [] empty_context (core_apps pr_fake_add [ELit (LitNat 1);ELit (LitNat 2)])) =
  (Accept tt,Accept (ELit (LitNat 3)),Accept (ELit (LitNat 1))).
Proof. vm_compute. reflexivity. Qed.
Example pa_internal_checked_constant_is_not_a_primitive_admission_api :
  checked_constant 256 pr_env (primitive_name PNatAdd) [] (primitive_signature PNatAdd)
    (Some pr_fake_add) (DPrimitive PNatAdd) = Accept pa_forged_add_env.
Proof. vm_compute. reflexivity. Qed.
Example pa_ordinary_alias_cannot_request_a_primitive_tag :
  (env <- admit 256 pr_env (InputDefinition HintOpaque (core_name "AliasAdd") []
    (primitive_signature PNatAdd) pr_fake_add InputSafe) ;;
   d <- get_constant env [] (core_name "AliasAdd") [] ;;
   value <- whnf 64 env [] empty_context
     (core_apps (EConst (core_name "AliasAdd") []) [ELit (LitNat 1);ELit (LitNat 2)]) ;;
   Accept (decl_kind_of d,value)) = Accept (DDefinition,ELit (LitNat 1)).
Proof. vm_compute. reflexivity. Qed.

Definition pa_gcd_positive := env <- pr_gcd_env ;; pa_admit env PNatGcd pr_gcd_body.
Definition pa_bitwise_positive := env <- pr_bitwise_env ;; pa_admit env PNatBitwise pr_bitwise_body.
Example pa_gcd_positive_control_passes_real_admission :
  pr_accepted pa_gcd_positive = true.
Proof. vm_compute. reflexivity. Qed.
Example pa_bitwise_positive_control_passes_real_admission :
  pr_accepted pa_bitwise_positive = true.
Proof. vm_compute. reflexivity. Qed.

Definition pa_second_measure := PQ.lam pr_pair (pr_pair_proj 1).
Definition pa_wrong_measure_unary := pr_definition ["PrimitiveGcdUnary"] (PQ.arrow pr_pair PQ.nat)
  (PQ.lam pr_pair (fun p =>
    let functional := PQ.lam pr_pair (fun q =>
      PQ.lam (pr_wf_dom pr_pair pr_pair_motive pa_second_measure q) (fun _ => pr_pair_proj 1 q)) in
    PQ.apps (PQ.const ["WellFounded";"Nat";"fix"] [LSucc LZero;LSucc LZero])
      [pr_pair;pr_pair_motive;pa_second_measure;functional;p])).
Example pa_wrong_measure_is_a_well_typed_definition :
  (env <- pr_wf_env ;; pa_typed_decl env pa_wrong_measure_unary) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_wrong_measure_cannot_get_gcd_metadata :
  (env <- pr_gcd_env ;; pa_admit (pr_replace pa_wrong_measure_unary env) PNatGcd pr_gcd_body) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.

Definition pa_successor_eager := pr_definition ["WellFounded";"Nat";"eager"]
  (PQ.arrow PQ.nat PQ.nat) (PQ.lam PQ.nat PQ.succ).
Example pa_wrong_eager_and_fix_are_still_well_typed :
  (env <- pr_gcd_env ;; let env := pr_replace pa_successor_eager env in
   _ <- pa_typed_decl env pa_successor_eager ;; pa_typed_decl env pr_wf_fix_decl) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_wrong_eager_cannot_authenticate_gcd :
  (env <- pr_gcd_env ;; pa_admit (pr_replace pa_successor_eager env) PNatGcd pr_gcd_body) =
    Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_gcd_capture_is_typed_before_symbolic_authentication :
  (env <- pr_gcd_env ;; pa_typed_decl env pr_gcd_captured_unary) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_gcd_functional_cannot_capture_the_opened_arguments :
  pr_rejected (env <- pr_gcd_env ;;
    pa_admit (pr_replace pr_gcd_captured_unary env) PNatGcd pr_gcd_body) = true.
Proof. vm_compute. reflexivity. Qed.
Example pa_gcd_ignoring_ih_is_typed_but_not_certified :
  (env <- pr_gcd_env ;; _ <- pa_typed_decl env pr_gcd_impostor_unary ;;
   pa_admit (pr_replace pr_gcd_impostor_unary env) PNatGcd pr_gcd_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_gcd_probe_does_not_accept_a_nat_as_decrease_proof :
  (env <- pr_gcd_env ;;
   p <- primitive_unfold_nat_well_founded 512 env initial_ind_state pr_gcd_body primitive_first_measure ;;
   let '(n,sn) := ind_fresh initial_ind_state NameAnon BDefault core_nat in
   primitive_run_probe 512 env sn p [primitive_one;local_expr n] (fun ih =>
     core_apps ih [core_apps (probe_pack p) [primitive_zero;primitive_one];primitive_zero])) =
       Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.

Definition pa_operator_body unary := PQ.run (PQ.lam (PQ.embed primitive_bool_operator_type) (fun f =>
  PQ.lam PQ.nat (fun n => PQ.lam PQ.nat (fun m =>
    PQ.apps (PQ.const [unary] []) [f;pr_pair_mk n m])))).
Definition pa_and_only_unary := pr_definition ["PrimitiveAndOnlyUnary"]
  (PQ.arrow (PQ.embed primitive_bool_operator_type) (PQ.arrow pr_pair PQ.nat))
  (PQ.lam (PQ.embed primitive_bool_operator_type) (fun _ =>
    PQ.lam pr_pair (pr_wf_unary (pr_bitwise_functional false (PQ.embed pr_bool_and))))).
Definition pa_and_only_body := pa_operator_body "PrimitiveAndOnlyUnary".
Definition pa_and_only_env := env <- pr_bitwise_env ;; Accept (pa_and_only_unary :: env).
Example pa_operator_impostor_is_well_typed :
  (env <- pa_and_only_env ;; _ <- pa_typed_decl env pa_and_only_unary ;;
   check 512 env [] empty_context pa_and_only_body pr_bitwise_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_operator_impostor_matches_the_entire_and_specialization :
  (env <- pa_and_only_env ;; check_defeq 512 env [] empty_context
    (EApp pa_and_only_body pr_bool_and) (EApp pr_bitwise_body pr_bool_and)) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_bitwise_requires_an_arbitrary_operator_not_one_specialization :
  (env <- pa_and_only_env ;; pa_admit env PNatBitwise pa_and_only_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.

Definition pa_wrong_tuple_functional f := PQ.lam pr_pair (fun p => PQ.lam (pr_pair_dom p) (fun ih =>
  let n := pr_pair_proj 0 p in let m := pr_pair_proj 1 p in
  let choose b x y := primitive_condition_ite PCBool PQ.nat [b] x y in
  primitive_condition_dite PCNatEq [n;PQ.zero]
    (fun _ => choose (PQ.apps f [PQ.fal;PQ.tru]) m PQ.zero)
    (fun hn => primitive_condition_ite PCNatEq PQ.nat [m;PQ.zero]
      (choose (PQ.apps f [PQ.tru;PQ.fal]) n PQ.zero)
      (let r := PQ.apps ih [pr_pair_mk (PQ.call PNatDiv [n;PQ.two]) PQ.zero;
         PQ.apps (PQ.const ["Nat";"bitwise_rec_lemma"] []) [n;hn]] in
       let rr := PQ.call PNatAdd [r;r] in
       let odd x := primitive_condition_decide PCNatEq [PQ.call PNatMod [x;PQ.two];PQ.one] in
       choose (PQ.apps f [odd n;odd m]) (PQ.call PNatAdd [rr;PQ.one]) rr)))).
Definition pa_wrong_tuple_unary := pr_definition ["PrimitiveWrongTupleUnary"]
  (PQ.arrow (PQ.embed primitive_bool_operator_type) (PQ.arrow pr_pair PQ.nat))
  (PQ.lam (PQ.embed primitive_bool_operator_type) (fun f =>
    PQ.lam pr_pair (pr_wf_unary (pa_wrong_tuple_functional f)))).
Definition pa_wrong_tuple_body := pa_operator_body "PrimitiveWrongTupleUnary".
Definition pa_wrong_tuple_env := env <- pr_bitwise_env ;; Accept (pa_wrong_tuple_unary :: env).
Example pa_wrong_recursive_tuple_is_well_typed_and_decreases :
  (env <- pa_wrong_tuple_env ;; _ <- pa_typed_decl env pa_wrong_tuple_unary ;;
   check 512 env [] empty_context pa_wrong_tuple_body pr_bitwise_type) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example pa_bitwise_probe_checks_both_recursive_tuple_coordinates :
  (env <- pa_wrong_tuple_env ;; pa_admit env PNatBitwise pa_wrong_tuple_body) = Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_bitwise_wrong_output_digit_is_typed_but_rejected :
  (env <- pr_bitwise_env ;; _ <- pa_typed_decl env (pr_bitwise_unary true) ;;
   pa_admit (pr_replace (pr_bitwise_unary true) env) PNatBitwise pr_bitwise_body) =
     Reject NotDefinitionallyEqual.
Proof. vm_compute. reflexivity. Qed.
Example pa_opaque_well_founded_wrapper_declines_instead_of_certifying :
  (env <- pr_gcd_env ;;
   let d := pr_decl (decl_name pr_gcd_unary) (decl_type pr_gcd_unary) DOpaque (decl_value pr_gcd_unary) in
   pa_admit (pr_replace d env) PNatGcd pr_gcd_body) = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example pa_low_fuel_cannot_turn_failure_into_a_certificate :
  classify_primitive 0 pr_env (primitive_name PNatBitwise) [] pr_bitwise_type pr_bitwise_body =
    Decline OutOfFuel.
Proof. reflexivity. Qed.

Theorem pa_admission_retains_exactly_the_classified_body
    hints fuel env n ps ty body env' d tail k :
  admit fuel env (InputDefinition hints n ps ty body InputSafe) = Accept env' ->
  env' = d :: tail -> decl_kind_of d = DPrimitive k ->
  tail = env /\ decl_name d = n /\ decl_params d = ps /\
  decl_type d = ty /\ decl_value d = Some body /\ decl_hints d = hints /\
  classify_primitive fuel env n ps ty body = Accept (Some k).
Proof.
  unfold admit.
  destruct (check_header fuel env n ps ty); cbn [bind]; try discriminate.
  destruct (require (scoped 0 body) MalformedDeclaration); cbn [bind]; try discriminate.
  destruct (check fuel env ps empty_context body ty); cbn [bind]; try discriminate.
  destruct (classify_primitive fuel env n ps ty body) as [kind|r|a] eqn:Hclass;
    cbn [bind]; try discriminate.
  destruct kind as [actual|]; intros H Henv Hkind;
    subst env'; inversion H; subst; cbn in Hkind; try discriminate.
  inversion Hkind; subst. repeat split; reflexivity.
Qed.
