(* SPDX-License-Identifier: Apache-2.0
   Private safe-definition admission, exactly refining Declarations.admit.
   No arena, cache, or summary is supplied through the public boundary. *)
From Stdlib Require Import List Bool Arith NArith Lia.
From LeanPort Require Import Syntax Checker Primitives Declarations
  DagScope DagMemo DagArena DagQuery DagInfer DagEntry.
Import ListNotations.
Set Implicit Arguments.

Definition entry_scoped (depth : nat) (entry : scope_entry) : bool :=
  N.leb (scope_need entry) (N.of_nat depth).

Lemma entry_scoped_refines depth entry : scope_entry_ok entry ->
  entry_scoped depth entry = scoped depth (scope_expr entry).
Proof.
  intro H. unfold scope_entry_ok in H. unfold entry_scoped.
  rewrite scoped_required_depth, <- H.
  apply Bool.eq_true_iff_eq. rewrite N.leb_le, Nat.leb_le. lia.
Qed.

Definition input_infer budget fuel env ps arena root : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S n => run_memo_infer (checker n env ps) n env ps empty_context
      arena budget true (root,[])
  end.

Lemma input_infer_refines budget fuel env ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_infer budget fuel env ps arena root =
    infer fuel env ps empty_context (scope_expr entry).
Proof.
  intros Arena Root. destruct fuel as [|n]; [reflexivity|].
  unfold input_infer. rewrite run_memo_infer_refines by exact Arena.
  unfold step_eval. cbn [path_from bind]. rewrite Root. reflexivity.
Qed.

Definition input_header budget fuel env n ps arena root entry : result unit :=
  match find_decl n env with
  | Some _ => Reject DuplicateDeclaration
  | None =>
    if negb (names_unique ps) then Reject DuplicateUniverse else
    if negb (entry_scoped 0 entry) then Reject MalformedDeclaration else
    inferred <- input_infer budget fuel env ps arena root ;;
    reduced <- whnf fuel env ps empty_context inferred ;;
    match reduced with ESort _ => Accept tt | _ => Reject ExpectedSort end
  end.

Lemma input_header_refines budget fuel env n ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_header budget fuel env n ps arena root entry =
    check_header fuel env n ps (scope_expr entry).
Proof.
  intros Arena Root. unfold input_header, check_header.
  rewrite (@entry_scoped_refines 0 entry).
  - rewrite (@input_infer_refines budget fuel env ps arena root entry Arena Root).
    reflexivity.
  - eapply scope_ref_ok; [exact (proj1 Arena)|exact Root].
Qed.

Definition input_check budget fuel env ps arena type_root body_root ty : result unit :=
  type_type <- input_infer budget fuel env ps arena type_root ;;
  type_type <- whnf_method (checker fuel env ps) empty_context type_type ;;
  ignored <- match type_type with ESort u => Accept u | _ => Reject ExpectedSort end ;;
  body_type <- input_infer budget fuel env ps arena body_root ;;
  ok <- defeq fuel env ps empty_context body_type ty ;;
  require ok TypeMismatch.

Lemma input_check_refines budget fuel env ps arena type_root body_root ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) type_root = Accept ty ->
  scope_ref (arena_scope arena) body_root = Accept body ->
  input_check budget fuel env ps arena type_root body_root (scope_expr ty) =
    check fuel env ps empty_context (scope_expr body) (scope_expr ty).
Proof.
  intros Arena Htype Hbody. unfold input_check, check, sort_of.
  rewrite (@input_infer_refines budget fuel env ps arena type_root ty Arena Htype).
  rewrite (@input_infer_refines budget fuel env ps arena body_root body Arena Hbody).
  unfold infer. destruct (infer_method (checker fuel env ps) empty_context (scope_expr ty));
    cbn [bind]; try reflexivity.
  destruct (whnf_method (checker fuel env ps) empty_context e);
    cbn [bind]; try reflexivity.
Qed.

Definition safe_definition_in_arena hints budget fuel env n ps arena type_root body_root
    (ty body : scope_entry) : result environment :=
  ignored <- input_header budget fuel env n ps arena type_root ty ;;
  ignored <- require (entry_scoped 0 body) MalformedDeclaration ;;
  ignored <- input_check budget fuel env ps arena type_root body_root (scope_expr ty) ;;
  primitive <- classify_primitive fuel env n ps (scope_expr ty) (scope_expr body) ;;
  let kind := match primitive with Some p => DPrimitive p | None => DDefinition end in
  Accept ({| decl_hints := hints; decl_name := n; decl_params := ps; decl_type := scope_expr ty;
    decl_value := Some (scope_expr body); decl_kind_of := kind |} :: env).

Theorem safe_definition_in_arena_refines hints budget fuel env n ps arena type_root body_root ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) type_root = Accept ty ->
  scope_ref (arena_scope arena) body_root = Accept body ->
  safe_definition_in_arena hints budget fuel env n ps arena type_root body_root ty body =
    admit fuel env (InputDefinition hints n ps (scope_expr ty) (scope_expr body) InputSafe).
Proof.
  intros Arena Htype Hbody. unfold safe_definition_in_arena, admit.
  rewrite (@input_header_refines budget fuel env n ps arena type_root ty Arena Htype).
  rewrite (@entry_scoped_refines 0 body).
  - rewrite (@input_check_refines budget fuel env ps arena type_root body_root ty body Arena Htype Hbody).
    reflexivity.
  - eapply scope_ref_ok; [exact (proj1 Arena)|exact Hbody].
Qed.

(* Decode exactly once for a definition's type/body pair. Input row order and
   root-validation precedence are the same in the optimized/reference paths. *)
Definition admit_dag_definition hints budget fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  safe_definition_in_arena hints budget fuel env n ps arena type_root body_root ty body.

Definition decode_then_admit_definition hints fuel env n ps rows type_root body_root
    : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) type_root ;;
  body <- scope_ref (arena_scope arena) body_root ;;
  admit fuel env (InputDefinition hints n ps (scope_expr ty) (scope_expr body) InputSafe).

Theorem admit_dag_definition_refines hints budget fuel env n ps rows type_root body_root :
  admit_dag_definition hints budget fuel env n ps rows type_root body_root =
  decode_then_admit_definition hints fuel env n ps rows type_root body_root.
Proof.
  unfold admit_dag_definition, decode_then_admit_definition.
  destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) type_root) eqn:Htype; cbn [bind]; try reflexivity.
  destruct (scope_ref (arena_scope d) body_root) eqn:Hbody; cbn [bind]; try reflexivity.
  eapply safe_definition_in_arena_refines; eauto.
  eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Print Assumptions admit_dag_definition_refines.
