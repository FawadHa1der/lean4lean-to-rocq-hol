(* SPDX-License-Identifier: Apache-2.0
   Stuck projections retain their original major, not its attempted WHNF.
   This is a control-flow property, not a typing or whole-checker theorem. *)
From Stdlib Require Import List.
From LeanPort Require Import Syntax EagerPolicy Checker.
Import ListNotations.

Theorem whnf_projection_stuck rec fuel env ps (cheap : bool) g owner index value :
  core_reduce_projection_with rec
    (if cheap then whnf_core_method rec true else whnf_method rec)
    env g owner index value = Accept None ->
  whnf_core_step rec fuel env ps cheap g (EProj owner index value) =
    Accept (EProj owner index value).
Proof. intro H. cbn [whnf_core_step]. rewrite H. reflexivity. Qed.

Theorem whnf_projection_reduced rec fuel env ps (cheap : bool) g owner index value field :
  core_reduce_projection_with rec
    (if cheap then whnf_core_method rec true else whnf_method rec)
    env g owner index value = Accept (Some field) ->
  whnf_core_step rec fuel env ps cheap g (EProj owner index value) =
    whnf_core_method rec cheap g field.
Proof. intro H. cbn [whnf_core_step]. rewrite H. reflexivity. Qed.

Theorem whnf_projection_rejected rec fuel env ps (cheap : bool) g owner index value error :
  core_reduce_projection_with rec
    (if cheap then whnf_core_method rec true else whnf_method rec)
    env g owner index value = Reject error ->
  whnf_core_step rec fuel env ps cheap g (EProj owner index value) = Reject error.
Proof. intro H. cbn [whnf_core_step]. rewrite H. reflexivity. Qed.

Theorem whnf_projection_declined rec fuel env ps (cheap : bool) g owner index value reason :
  core_reduce_projection_with rec
    (if cheap then whnf_core_method rec true else whnf_method rec)
    env g owner index value = Decline reason ->
  whnf_core_step rec fuel env ps cheap g (EProj owner index value) = Decline reason.
Proof. intro H. cbn [whnf_core_step]. rewrite H. reflexivity. Qed.

Module ProjectionPreservationFixtures.
Definition original := EApp (EConst NameAnon []) (EBVar 0).
Definition changed := EPi NameAnon BDefault (ESort LZero) (ESort LZero).
Definition projected := EProj NameAnon 0 original.
Definition callbacks (answer : result expr) : methods :=
  {| infer_method := fun _ _ => Reject ExpectedSort;
     infer_type_method := fun _ _ => Reject ExpectedSort;
     whnf_method := fun _ _ => answer;
     whnf_core_method := fun _ _ _ => answer;
     defeq_method := fun _ _ _ => Reject TypeMismatch;
     method_mode := NormalReduction;
     eager_defeq_method := fun _ _ _ => Reject TypeMismatch |}.

Example changed_major_is_not_retained_cheap :
  whnf_core_step (callbacks (Accept changed)) 0 [] [] true empty_context projected =
    Accept projected.
Proof. reflexivity. Qed.

Example changed_major_is_not_retained_full :
  whnf_core_step (callbacks (Accept changed)) 0 [] [] false empty_context projected =
    Accept projected.
Proof. reflexivity. Qed.

Example unchanged_major_is_retained :
  whnf_core_step (callbacks (Accept original)) 0 [] [] true empty_context projected =
    Accept projected.
Proof. reflexivity. Qed.

Example reduction_rejection_is_not_stuck :
  whnf_core_step (callbacks (Reject ExpectedPi)) 0 [] [] true empty_context projected =
    Reject ExpectedPi.
Proof. reflexivity. Qed.

Example reduction_decline_is_not_stuck :
  whnf_core_step (callbacks (Decline OutOfFuel)) 0 [] [] false empty_context projected =
    Decline OutOfFuel.
Proof. reflexivity. Qed.

Example unsupported_reduction_is_not_stuck :
  whnf_core_step (callbacks (Decline UnsupportedExpression)) 0 [] [] true empty_context projected =
    Decline UnsupportedExpression.
Proof. reflexivity. Qed.

Definition split_callbacks (cheap_answer full_answer : result expr)
    (finish : bool -> expr -> result expr) : methods :=
  {| infer_method := fun _ _ => Reject ExpectedSort;
     infer_type_method := fun _ _ => Reject ExpectedSort;
     whnf_method := fun _ _ => full_answer;
     whnf_core_method := fun cheap _ e =>
       if expr_eqb e original then cheap_answer else finish cheap e;
     defeq_method := fun _ _ _ => Reject TypeMismatch;
     method_mode := NormalReduction;
     eager_defeq_method := fun _ _ _ => Reject TypeMismatch |}.
Definition no_continuation (_ : bool) (_ : expr) : result expr := Reject TypeMismatch.
Definition ctor_name := NameNum NameAnon BinNums.N0.
Definition ctor_env owner params fields : environment :=
  [{| decl_name := ctor_name; decl_params := []; decl_type := ESort LZero;
      decl_value := None; decl_hints := HintOpaque;
      decl_kind_of := DConstructor
        {| ctor_induct := owner; ctor_index := 0; ctor_num_params := params;
           ctor_num_fields := fields; ctor_is_unsafe := false |} |}].
Definition field := ESort LZero.
Definition constructed := EApp (EConst ctor_name []) field.
Definition finish_field (mode : bool) (e : expr) : result expr :=
  if expr_eqb e field then
    if mode then Accept (ESort (LSucc LZero)) else Accept (ESort (LSucc (LSucc LZero)))
  else Reject TypeMismatch.

Example cheap_selector_ignores_full_error :
  whnf_core_step (split_callbacks (Accept changed) (Reject ExpectedPi) no_continuation)
    0 [] [] true empty_context projected = Accept projected.
Proof. reflexivity. Qed.

Example full_selector_ignores_cheap_error :
  whnf_core_step (split_callbacks (Reject ExpectedPi) (Accept changed) no_continuation)
    0 [] [] false empty_context projected = Accept projected.
Proof. reflexivity. Qed.

Example successful_field_continues_cheap :
  whnf_core_step (split_callbacks (Accept constructed) (Reject ExpectedPi) finish_field)
    0 (ctor_env NameAnon 0 1) [] true empty_context projected =
    Accept (ESort (LSucc LZero)).
Proof. reflexivity. Qed.

Example successful_field_continues_full :
  whnf_core_step (split_callbacks (Reject ExpectedPi) (Accept constructed) finish_field)
    0 (ctor_env NameAnon 0 1) [] false empty_context projected =
    Accept (ESort (LSucc (LSucc LZero))).
Proof. reflexivity. Qed.

Example successful_field_continuation_rejects :
  whnf_core_step (split_callbacks (Accept constructed) (Reject ExpectedPi) no_continuation)
    0 (ctor_env NameAnon 0 1) [] true empty_context projected = Reject TypeMismatch.
Proof. reflexivity. Qed.

Example successful_field_continuation_declines :
  whnf_core_step (split_callbacks (Accept constructed) (Reject ExpectedPi)
    (fun _ _ => Decline UnsupportedExpression))
    0 (ctor_env NameAnon 0 1) [] true empty_context projected = Decline UnsupportedExpression.
Proof. reflexivity. Qed.

Example wrong_owner_retains_original_major :
  whnf_core_step (split_callbacks (Accept constructed) (Reject ExpectedPi) no_continuation)
    0 (ctor_env ctor_name 0 1) [] true empty_context projected = Accept projected.
Proof. reflexivity. Qed.

Example out_of_range_retains_original_major :
  whnf_core_step (split_callbacks (Accept constructed) (Reject ExpectedPi) no_continuation)
    0 (ctor_env NameAnon 0 1) [] true empty_context (EProj NameAnon 1 original) =
    Accept (EProj NameAnon 1 original).
Proof. reflexivity. Qed.

Example wrong_arity_retains_original_major :
  whnf_core_step (split_callbacks (Accept (EConst ctor_name [])) (Reject ExpectedPi) no_continuation)
    0 (ctor_env NameAnon 0 1) [] true empty_context projected = Accept projected.
Proof. reflexivity. Qed.

Example nonzero_parameter_and_field_offsets :
  let major := core_apps (EConst ctor_name []) [changed; original; field] in
  whnf_core_step (split_callbacks (Accept major) (Reject ExpectedPi) finish_field)
    0 (ctor_env NameAnon 1 2) [] true empty_context (EProj NameAnon 1 original) =
    Accept (ESort (LSucc LZero)).
Proof. reflexivity. Qed.
End ProjectionPreservationFixtures.

Print Assumptions whnf_projection_stuck.
Print Assumptions whnf_projection_reduced.
Print Assumptions whnf_projection_rejected.
Print Assumptions whnf_projection_declined.
