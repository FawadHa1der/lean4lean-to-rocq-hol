(* SPDX-License-Identifier: Apache-2.0
   Policy/admission regressions, not an overall Lean typing theorem. *)
From Stdlib Require Import List String NArith.
From LeanPort Require Import Syntax EagerPolicy Checker Declarations Safety.
Import ListNotations.
Open Scope string_scope.

Definition hn s := NameStr NameAnon s.
Definition hp := ESort LZero.
Definition ht := ESort (LSucc LZero).
Definition huge_height := (2 ^ 256)%N.
Definition hd n h k body :=
  {| decl_name := hn n; decl_params := []; decl_type := ht;
     decl_value := body; decl_kind_of := k; decl_hints := h |}.
Definition hc n := EConst (hn n) [].
Definition pair_env h k :=
  [hd "left" h DDefinition (Some hp); hd "right" k DDefinition (Some ht)].
Definition sides h k := core_delta_sides (pair_env h k) (hc "left") (hc "right").

Example opaque_equal : hints_lt HintOpaque HintOpaque = false.
Proof. reflexivity. Qed.
Example abbrev_equal : hints_lt HintAbbrev HintAbbrev = false.
Proof. reflexivity. Qed.
Example regular_equal : hints_lt (HintRegular huge_height) (HintRegular huge_height) = false.
Proof. vm_compute. reflexivity. Qed.
Example opaque_below_regular : sides HintOpaque (HintRegular 0) = (false,true).
Proof. reflexivity. Qed.
Example regular_above_opaque : sides (HintRegular 0) HintOpaque = (true,false).
Proof. reflexivity. Qed.
Example abbrev_above_regular : sides HintAbbrev (HintRegular huge_height) = (true,false).
Proof. reflexivity. Qed.
Example regular_below_abbrev : sides (HintRegular huge_height) HintAbbrev = (false,true).
Proof. reflexivity. Qed.
Example larger_left : sides (HintRegular 2) (HintRegular 1) = (true,false).
Proof. reflexivity. Qed.
Example larger_right : sides (HintRegular 1) (HintRegular 2) = (false,true).
Proof. reflexivity. Qed.
Example equal_regular_both : sides (HintRegular huge_height) (HintRegular huge_height) = (true,true).
Proof. vm_compute. reflexivity. Qed.
Example equal_opaque_both : sides HintOpaque HintOpaque = (true,true).
Proof. reflexivity. Qed.
Example equal_abbrev_both : sides HintAbbrev HintAbbrev = (true,true).
Proof. reflexivity. Qed.
Example huge_not_wrapped : sides (HintRegular huge_height) (HintRegular 1) = (true,false).
Proof. vm_compute. reflexivity. Qed.
Example huge_adjacent_exact : sides (HintRegular huge_height) (HintRegular (N.succ huge_height)) = (false,true).
Proof. vm_compute. reflexivity. Qed.
Example absent_head : core_delta_info [] (hc "missing") = None.
Proof. reflexivity. Qed.
Example absent_body : core_delta_info [hd "left" HintAbbrev DDefinition None] (hc "left") = None.
Proof. reflexivity. Qed.
Example wrong_arity : core_delta_info (pair_env HintAbbrev HintOpaque)
  (EConst (hn "left") [LZero]) = None.
Proof. reflexivity. Qed.
Example opaque_hint_reducible : core_delta_head [hd "x" HintOpaque DDefinition (Some hp)] (hc "x") = true.
Proof. reflexivity. Qed.
Example theorem_reducible : core_delta_head [hd "x" HintAbbrev DTheorem (Some hp)] (hc "x") = true.
Proof. reflexivity. Qed.
Example theorem_hint_ignored : effective_hints (hd "x" HintAbbrev DTheorem (Some hp)) = HintOpaque.
Proof. reflexivity. Qed.
Example opaque_not_reducible : core_delta_info [hd "x" HintAbbrev DOpaque (Some hp)] (hc "x") = None.
Proof. reflexivity. Qed.
Example assumption_not_reducible : core_delta_info [hd "x" HintAbbrev DAssumption (Some hp)] (hc "x") = None.
Proof. reflexivity. Qed.
Example unsafe_not_reducible : core_delta_info [hd "x" HintAbbrev (DUnsafe DDefinition) (Some hp)] (hc "x") = None.
Proof. reflexivity. Qed.
Example partial_not_reducible : core_delta_info [hd "x" HintAbbrev DPartial (Some hp)] (hc "x") = None.
Proof. reflexivity. Qed.
Example primitive_keeps_hint : effective_hints (hd "x" HintAbbrev (DPrimitive PNatAdd) (Some hp)) = HintAbbrev.
Proof. reflexivity. Qed.
Example shadowed_hint : core_delta_sides
  (hd "left" HintOpaque DDefinition (Some hp) :: pair_env HintAbbrev (HintRegular 1))
  (hc "left") (hc "right") = (false,true).
Proof. reflexivity. Qed.
Example unsafe_view_keeps_hint : effective_hints
  (checking_view InputUnsafe (hd "x" HintAbbrev (DUnsafe DDefinition) (Some hp))) = HintAbbrev.
Proof. reflexivity. Qed.

(* Distinct test-only callback errors witness actual unfolding order. *)
Definition probe_methods : methods :=
  {| infer_method := fun _ _ => Accept ht;
     infer_type_method := fun _ _ => Accept ht;
     whnf_method := fun _ e => Accept e;
     whnf_core_method := fun _ _ e =>
       match e with ESort LZero => Reject ExpectedSort | _ => Reject ExpectedPi end;
     defeq_method := fun _ _ _ => Accept true;
     method_mode := NormalReduction;
     eager_defeq_method := fun _ _ _ => Accept true |}.
Example left_unfolded_alone : core_lazy_delta 1 probe_methods 32
  (pair_env HintAbbrev HintOpaque) [] empty_context (hc "left") (hc "right") = Reject ExpectedSort.
Proof. vm_compute. reflexivity. Qed.
Example right_unfolded_alone : core_lazy_delta 1 probe_methods 32
  (pair_env HintOpaque HintAbbrev) [] empty_context (hc "left") (hc "right") = Reject ExpectedPi.
Proof. vm_compute. reflexivity. Qed.

Definition identity h := hd "identity" h DDefinition (Some (ELam NameAnon BDefault ht (EBVar 0))).
Definition erased h := hd "erased" h DDefinition (Some (ELam NameAnon BDefault ht hp)).
Example regular_same_head : core_delta_congruent probe_methods 32 [identity (HintRegular 1)] empty_context
  (EApp (hc "identity") hp) (EApp (hc "identity") ht) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example opaque_same_head_no_speculation : core_delta_congruent probe_methods 32 [identity HintOpaque] empty_context
  (EApp (hc "identity") hp) (EApp (hc "identity") ht) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example abbrev_same_head_no_speculation : core_delta_congruent probe_methods 32 [identity HintAbbrev] empty_context
  (EApp (hc "identity") hp) (EApp (hc "identity") ht) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example erased_head_no_speculation : core_delta_congruent probe_methods 32 [erased (HintRegular 1)] empty_context
  (EApp (hc "erased") hp) (EApp (hc "erased") ht) = Accept false.
Proof. vm_compute. reflexivity. Qed.

Definition erased_input h := InputDefinition h (hn "erased") []
  (EPi NameAnon BDefault ht ht) (ELam NameAnon BDefault ht hp) InputSafe.
Definition with_erased h value := env <- admit 64 [] (erased_input h) ;;
  admit 64 env (InputDefinition h (hn "result") [] ht value InputSafe).
Definition accepted {A} (r : result A) := match r with Accept _ => true | _ => false end.
Example erased_baseline_accepts : accepted (with_erased (HintRegular huge_height) (EApp (hc "erased") hp)) = true.
Proof. vm_compute. reflexivity. Qed.
Example erased_bad_argument_rejected : with_erased (HintRegular huge_height)
  (EApp (hc "erased") ht) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example missing_argument_rejected : with_erased HintAbbrev
  (EApp (hc "erased") (hc "missing")) = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example opaque_hint_baseline_accepts : accepted (with_erased HintOpaque (EApp (hc "erased") hp)) = true.
Proof. vm_compute. reflexivity. Qed.
Example abbrev_hint_bad_argument_rejected : with_erased HintAbbrev
  (EApp (hc "erased") ht) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.

Theorem theorem_effective_hint_is_opaque n ps ty body hint :
  effective_hints {| decl_name := n; decl_params := ps; decl_type := ty;
    decl_value := body; decl_kind_of := DTheorem; decl_hints := hint |} = HintOpaque.
Proof. reflexivity. Qed.
Print Assumptions theorem_effective_hint_is_opaque.

(* Callback-order witnesses supplement the genuinely admitted native package
   fixture. These low-level probes do not assert typing for arbitrary callbacks. *)
Definition retry_projection := EProj (hn "Package") 0 (hc "package").
Definition retry_env := [hd "left" (HintRegular 1) DDefinition (Some hp)].
Definition retry_methods (answer : result expr) : methods :=
  {| infer_method := fun _ _ => Accept ht;
     infer_type_method := fun _ _ => Accept ht;
     whnf_method := fun _ e => Accept e;
     whnf_core_method := fun cheap _ _ => if cheap then Reject ExpectedSort else answer;
     defeq_method := fun _ _ _ => Accept false;
     method_mode := NormalReduction;
     eager_defeq_method := fun _ _ _ => Accept false |}.

Example retry_left_avoids_delta_body : core_lazy_delta 2 (retry_methods (Accept (hc "left")))
  32 retry_env [] empty_context (hc "left") retry_projection = Accept (ConversionDone true).
Proof. vm_compute. reflexivity. Qed.
Example retry_right_avoids_delta_body : core_lazy_delta 2 (retry_methods (Accept (hc "left")))
  32 retry_env [] empty_context retry_projection (hc "left") = Accept (ConversionDone true).
Proof. vm_compute. reflexivity. Qed.
Example retry_consumes_loop_round : core_lazy_delta 1 (retry_methods (Accept (hc "left")))
  32 retry_env [] empty_context (hc "left") retry_projection = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example retry_zero_rounds : core_lazy_delta 0 (retry_methods (Reject ExpectedPi))
  32 retry_env [] empty_context (hc "left") retry_projection = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example retry_unchanged_falls_back : core_lazy_delta 2 (retry_methods (Accept retry_projection))
  32 retry_env [] empty_context (hc "left") retry_projection = Reject ExpectedSort.
Proof. vm_compute. reflexivity. Qed.
Example retry_nonprojection_skips_callback : core_try_unfold_proj_app
  (retry_methods (Reject ExpectedPi)) empty_context (hc "left") = Accept None.
Proof. reflexivity. Qed.
Example retry_entire_application : core_try_unfold_proj_app
  (retry_methods (Accept (EApp (hc "left") hp))) empty_context
  (EApp retry_projection hp) = Accept (Some (EApp (hc "left") hp)).
Proof. reflexivity. Qed.
Example retry_two_delta_heads_skip : core_opposite_projection (retry_methods (Reject ExpectedPi))
  (pair_env HintOpaque HintOpaque) empty_context (hc "left") (hc "right") = Accept None.
Proof. reflexivity. Qed.
Example retry_no_delta_heads_skip : core_opposite_projection (retry_methods (Reject ExpectedPi))
  [] empty_context (hc "left") retry_projection = Accept None.
Proof. reflexivity. Qed.
Example retry_actual_opaque_skips : core_opposite_projection (retry_methods (Reject ExpectedPi))
  [hd "left" HintAbbrev DOpaque (Some hp)] empty_context (hc "left") retry_projection = Accept None.
Proof. reflexivity. Qed.
Example retry_opaque_hint_does_not_skip : core_opposite_projection (retry_methods (Reject ExpectedPi))
  [hd "left" HintOpaque DDefinition (Some hp)] empty_context (hc "left") retry_projection = Reject ExpectedPi.
Proof. reflexivity. Qed.
Example retry_unsafe_skips : core_opposite_projection (retry_methods (Reject ExpectedPi))
  [hd "left" HintAbbrev (DUnsafe DDefinition) (Some hp)] empty_context
  (hc "left") retry_projection = Accept None.
Proof. reflexivity. Qed.
Example retry_arity_skips : core_opposite_projection (retry_methods (Reject ExpectedPi))
  retry_env empty_context (EConst (hn "left") [LZero]) retry_projection = Accept None.
Proof. reflexivity. Qed.
Example retry_missing_value_skips : core_opposite_projection (retry_methods (Reject ExpectedPi))
  [hd "left" HintAbbrev DDefinition None] empty_context (hc "left") retry_projection = Accept None.
Proof. reflexivity. Qed.
Example retry_shadowed_opaque_skips : core_opposite_projection (retry_methods (Reject ExpectedPi))
  (hd "left" HintAbbrev DOpaque (Some hp) :: retry_env) empty_context
  (hc "left") retry_projection = Accept None.
Proof. reflexivity. Qed.

Theorem retry_reject_exact rec g e owner index value error :
  fst (core_spine e []) = EProj owner index value ->
  whnf_core_method rec false g e = Reject error ->
  core_try_unfold_proj_app rec g e = Reject error.
Proof. intros Hhead Hcallback. unfold core_try_unfold_proj_app. rewrite Hhead, Hcallback. reflexivity. Qed.
Theorem retry_decline_exact rec g e owner index value reason :
  fst (core_spine e []) = EProj owner index value ->
  whnf_core_method rec false g e = Decline reason ->
  core_try_unfold_proj_app rec g e = Decline reason.
Proof. intros Hhead Hcallback. unfold core_try_unfold_proj_app. rewrite Hhead, Hcallback. reflexivity. Qed.
Theorem retry_unchanged_exact rec g e owner index value reduced :
  fst (core_spine e []) = EProj owner index value ->
  whnf_core_method rec false g e = Accept reduced ->
  expr_eqb reduced e = true ->
  core_try_unfold_proj_app rec g e = Accept None.
Proof.
  intros Hhead Hcallback Heq. unfold core_try_unfold_proj_app.
  rewrite Hhead, Hcallback. cbn [bind]. rewrite Heq. reflexivity.
Qed.
Theorem retry_changed_exact rec g e owner index value reduced :
  fst (core_spine e []) = EProj owner index value ->
  whnf_core_method rec false g e = Accept reduced ->
  expr_eqb reduced e = false ->
  core_try_unfold_proj_app rec g e = Accept (Some reduced).
Proof.
  intros Hhead Hcallback Heq. unfold core_try_unfold_proj_app.
  rewrite Hhead, Hcallback. cbn [bind]. rewrite Heq. reflexivity.
Qed.
Print Assumptions retry_reject_exact.
Print Assumptions retry_decline_exact.
Print Assumptions retry_unchanged_exact.
Print Assumptions retry_changed_exact.

Definition retry_poly := {| decl_name := hn "left"; decl_params := [hn "u"];
  decl_type := ht; decl_value := Some hp; decl_kind_of := DDefinition;
  decl_hints := HintRegular 1 |}.
Definition retry_unknown_universe := EConst (hn "left") [LParam (hn "unknown")].
Example retry_header_does_not_validate_universes :
  core_delta_info [retry_poly] retry_unknown_universe = Some retry_poly.
Proof. reflexivity. Qed.
Example retry_unfold_would_reject_unknown_universe :
  core_unfold [retry_poly] [] retry_unknown_universe = Reject UnknownUniverse.
Proof. vm_compute. reflexivity. Qed.
Example retry_left_error_precedes_unfold_validation :
  core_lazy_delta 2 (retry_methods (Reject ExpectedPi)) 32 [retry_poly] [] empty_context
    retry_unknown_universe retry_projection = Reject ExpectedPi.
Proof. vm_compute. reflexivity. Qed.
Example retry_right_error_precedes_unfold_validation :
  core_lazy_delta 2 (retry_methods (Reject ExpectedPi)) 32 [retry_poly] [] empty_context
    retry_projection retry_unknown_universe = Reject ExpectedPi.
Proof. vm_compute. reflexivity. Qed.
Example retry_decline_precedes_unfold_validation :
  core_lazy_delta 2 (retry_methods (Decline UnsupportedExpression)) 32 [retry_poly] [] empty_context
    retry_unknown_universe retry_projection = Decline UnsupportedExpression.
Proof. vm_compute. reflexivity. Qed.
Example retry_unchanged_preserves_unfold_validation :
  core_lazy_delta 2 (retry_methods (Accept retry_projection)) 32 [retry_poly] [] empty_context
    retry_unknown_universe retry_projection = Reject UnknownUniverse.
Proof. vm_compute. reflexivity. Qed.
