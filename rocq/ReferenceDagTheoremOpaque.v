(* SPDX-License-Identifier: Apache-2.0
   Private theorem and safe opaque admission, exactly refining Declarations.
   Original callbacks, Prop checks and repeated header validation are retained. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Universes Checker Declarations
  DagScope DagArena ReferenceDagAdmission.
Import ListNotations.
Set Implicit Arguments.

Definition input_proposition budget fuel env ps arena root : result unit :=
  inferred <- input_infer budget fuel env ps arena root ;;
  reduced <- whnf fuel env ps empty_context inferred ;;
  match reduced with
  | ESort u =>
    is_zero <- level_equiv fuel u LZero ;;
    if is_zero then Accept tt else Reject MalformedDeclaration
  | _ => Reject ExpectedSort
  end.

Lemma input_proposition_refines budget fuel env ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_proposition budget fuel env ps arena root =
    check_proposition fuel env ps (scope_expr entry).
Proof.
  intros Arena Root. unfold input_proposition, check_proposition.
  rewrite (@input_infer_refines budget fuel env ps arena root entry Arena Root).
  reflexivity.
Qed.

Definition input_checked_constant budget fuel env n ps arena type_root body_root
    (ty body : scope_entry) kind : result environment :=
  ignored <- input_header budget fuel env n ps arena type_root ty ;;
  ignored <- if entry_scoped 0 body
    then input_check budget fuel env ps arena type_root body_root (scope_expr ty)
    else Reject MalformedDeclaration ;;
  Accept ({| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := scope_expr ty;
    decl_value := Some (scope_expr body); decl_kind_of := kind |} :: env).

Lemma input_checked_constant_refines budget fuel env n ps arena type_root body_root ty body kind :
  arena_ok arena ->
  scope_ref (arena_scope arena) type_root = Accept ty ->
  scope_ref (arena_scope arena) body_root = Accept body ->
  input_checked_constant budget fuel env n ps arena type_root body_root ty body kind =
    checked_constant fuel env n ps (scope_expr ty) (Some (scope_expr body)) kind.
Proof.
  intros Arena Htype Hbody. unfold input_checked_constant, checked_constant.
  rewrite (@input_header_refines budget fuel env n ps arena type_root ty Arena Htype).
  rewrite (@entry_scoped_refines 0 body).
  - rewrite (@input_check_refines budget fuel env ps arena type_root body_root ty body Arena Htype Hbody).
    reflexivity.
  - eapply scope_ref_ok; [exact (proj1 Arena)|exact Hbody].
Qed.

Definition theorem_in_arena budget fuel env n ps arena type_root body_root ty body
    : result environment :=
  if name_mem n reserved_names then Reject MalformedDeclaration else
  ignored <- input_header budget fuel env n ps arena type_root ty ;;
  ignored <- input_proposition budget fuel env ps arena type_root ;;
  input_checked_constant budget fuel env n ps arena type_root body_root ty body DTheorem.

Definition safe_opaque_in_arena budget fuel env n ps arena type_root body_root ty body
    : result environment :=
  if name_mem n reserved_names then Reject MalformedDeclaration else
  input_checked_constant budget fuel env n ps arena type_root body_root ty body DOpaque.

Theorem theorem_in_arena_refines budget fuel env n ps arena type_root body_root ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) type_root = Accept ty ->
  scope_ref (arena_scope arena) body_root = Accept body ->
  theorem_in_arena budget fuel env n ps arena type_root body_root ty body =
    admit fuel env (InputTheorem n ps (scope_expr ty) (scope_expr body)).
Proof.
  intros Arena Htype Hbody. unfold theorem_in_arena, admit.
  rewrite (@input_header_refines budget fuel env n ps arena type_root ty Arena Htype).
  rewrite (@input_proposition_refines budget fuel env ps arena type_root ty Arena Htype).
  rewrite (@input_checked_constant_refines budget fuel env n ps arena type_root body_root ty body DTheorem Arena Htype Hbody).
  reflexivity.
Qed.

Theorem safe_opaque_in_arena_refines budget fuel env n ps arena type_root body_root ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) type_root = Accept ty ->
  scope_ref (arena_scope arena) body_root = Accept body ->
  safe_opaque_in_arena budget fuel env n ps arena type_root body_root ty body =
    admit fuel env (InputOpaque n ps (scope_expr ty) (scope_expr body) false).
Proof.
  intros Arena Htype Hbody. unfold safe_opaque_in_arena, admit.
  rewrite (@input_checked_constant_refines budget fuel env n ps arena type_root body_root ty body DOpaque Arena Htype Hbody).
  reflexivity.
Qed.

Definition admit_dag_theorem budget fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  theorem_in_arena budget fuel env n ps arena type_root body_root ty body.

Definition decode_then_admit_theorem fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  admit fuel env (InputTheorem n ps (scope_expr ty) (scope_expr body)).

Definition admit_dag_opaque budget fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  safe_opaque_in_arena budget fuel env n ps arena type_root body_root ty body.

Definition decode_then_admit_opaque fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  admit fuel env (InputOpaque n ps (scope_expr ty) (scope_expr body) false).

Theorem admit_dag_theorem_refines budget fuel env n ps rows type_root body_root :
  admit_dag_theorem budget fuel env n ps rows type_root body_root =
  decode_then_admit_theorem fuel env n ps rows type_root body_root.
Proof.
  unfold admit_dag_theorem, decode_then_admit_theorem.
  destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) type_root) eqn:Htype; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) body_root) eqn:Hbody; cbn [bind]; try reflexivity.
  eapply theorem_in_arena_refines; eauto.
  eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Theorem admit_dag_opaque_refines budget fuel env n ps rows type_root body_root :
  admit_dag_opaque budget fuel env n ps rows type_root body_root =
  decode_then_admit_opaque fuel env n ps rows type_root body_root.
Proof.
  unfold admit_dag_opaque, decode_then_admit_opaque.
  destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) type_root) eqn:Htype; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) body_root) eqn:Hbody; cbn [bind]; try reflexivity.
  eapply safe_opaque_in_arena_refines; eauto.
  eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Print Assumptions admit_dag_theorem_refines.
Print Assumptions admit_dag_opaque_refines.
