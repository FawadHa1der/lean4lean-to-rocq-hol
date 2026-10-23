(* SPDX-License-Identifier: Apache-2.0
   Private lookup composition. One internal index per admission; no caller
   lookup or cache is accepted by the native frontend. The linear-environment
   DAG route and declaration reference both use this tree's NEW Checker. *)
From Stdlib Require Import List Bool NArith.
From LeanPort Require Import Syntax Universes Checker Primitives Declarations
  DagScope DagMemo DagArena DagQuery DagAdmission DagTheoremOpaque
  LookupIntegration LookupRefinement IndexedChecker PreparedDagLookup
  IndexedDagInfer RuntimeChecker.
Import ListNotations.
Set Implicit Arguments.

Inductive dag_admission_kind := DagDefinition : reducibility_hints -> dag_admission_kind
  | DagTheorem | DagOpaque.

Definition linear_env_admit kind budget fuel env n ps rows tr br :=
  match kind with
  | DagDefinition hints => DagAdmission.admit_dag_definition hints budget fuel env n ps rows tr br
  | DagTheorem => DagTheoremOpaque.admit_dag_theorem budget fuel env n ps rows tr br
  | DagOpaque => DagTheoremOpaque.admit_dag_opaque budget fuel env n ps rows tr br
  end.

Module PreparedDag.
Section Admission.
Context (lookup : declaration_lookup) (env : environment).
Hypothesis Lookup : forall n, lookup n = find_decl n env.

Definition input_infer budget fuel ps arena root : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S n => IndexedDagInfer.run_memo_infer lookup
      (checker_with_lookup n env lookup ps) n env ps empty_context
      arena budget true (root,[])
  end.

Lemma input_infer_refines budget fuel ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_infer budget fuel ps arena root =
    Checker.infer fuel env ps empty_context (scope_expr entry).
Proof.
  intros Arena Root. destruct fuel as [|n]; [reflexivity|].
  unfold input_infer. rewrite IndexedDagInfer.run_memo_infer_refines
    by assumption.
  unfold step_eval. cbn [path_from bind]. rewrite Root. cbn [bind].
  apply original_infer_step_methods, checker_with_lookup_refines. exact Lookup.
Qed.

Definition input_header budget fuel n ps arena root entry : result unit :=
  match lookup n with
  | Some _ => Reject DuplicateDeclaration
  | None =>
    if negb (names_unique ps) then Reject DuplicateUniverse else
    if negb (entry_scoped 0 entry) then Reject MalformedDeclaration else
    inferred <- input_infer budget fuel ps arena root ;;
    reduced <- prepared_whnf lookup fuel env ps empty_context inferred ;;
    match reduced with ESort _ => Accept tt | _ => Reject ExpectedSort end
  end.

Lemma input_header_refines budget fuel n ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_header budget fuel n ps arena root entry =
    check_header fuel env n ps (scope_expr entry).
Proof.
  intros Arena Root. unfold input_header, check_header.
  rewrite Lookup, (@entry_scoped_refines 0 entry).
  - rewrite (@input_infer_refines budget fuel ps arena root entry Arena Root).
    destruct (find_decl n env); [reflexivity|].
    destruct (negb (names_unique ps)); [reflexivity|].
    destruct (negb (scoped 0 (scope_expr entry))); [reflexivity|].
    apply bind_pointwise; [reflexivity|intro inferred].
    rewrite prepared_whnf_refines by exact Lookup. reflexivity.
  - eapply scope_ref_ok; [exact (proj1 Arena)|exact Root].
Qed.

Definition input_check budget fuel ps arena tr br ty : result unit :=
  type_type <- input_infer budget fuel ps arena tr ;;
  type_type <- whnf_method (checker_with_lookup fuel env lookup ps) empty_context type_type ;;
  ignored <- match type_type with ESort u => Accept u | _ => Reject ExpectedSort end ;;
  body_type <- input_infer budget fuel ps arena br ;;
  ok <- prepared_defeq lookup fuel env ps empty_context body_type ty ;;
  require ok TypeMismatch.

Lemma input_check_refines budget fuel ps arena tr br ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) tr = Accept ty ->
  scope_ref (arena_scope arena) br = Accept body ->
  input_check budget fuel ps arena tr br (scope_expr ty) =
    Checker.check fuel env ps empty_context (scope_expr body) (scope_expr ty).
Proof.
  intros Arena Htype Hbody. unfold input_check, Checker.check, Checker.sort_of.
  rewrite (@input_infer_refines budget fuel ps arena tr ty Arena Htype).
  rewrite (@input_infer_refines budget fuel ps arena br body Arena Hbody).
  unfold Checker.infer.
  destruct (infer_method (Checker.checker fuel env ps) empty_context (scope_expr ty));
    cbn [bind]; try reflexivity.
  rewrite (same_whnf _ _ (checker_with_lookup_refines fuel env lookup ps Lookup)).
  destruct (whnf_method (Checker.checker fuel env ps) empty_context e);
    cbn [bind]; try reflexivity.
  destruct e0; cbn [bind]; try reflexivity.
  apply bind_pointwise; [reflexivity|intro body_type].
  rewrite PreparedDagLookup.prepared_defeq_refines by exact Lookup. reflexivity.
Qed.

Definition input_proposition budget fuel ps arena root : result unit :=
  inferred <- input_infer budget fuel ps arena root ;;
  reduced <- prepared_whnf lookup fuel env ps empty_context inferred ;;
  match reduced with
  | ESort u =>
    is_zero <- level_equiv fuel u LZero ;;
    if is_zero then Accept tt else Reject MalformedDeclaration
  | _ => Reject ExpectedSort
  end.

Lemma input_proposition_refines budget fuel ps arena root entry :
  arena_ok arena -> scope_ref (arena_scope arena) root = Accept entry ->
  input_proposition budget fuel ps arena root =
    check_proposition fuel env ps (scope_expr entry).
Proof.
  intros Arena Root. unfold input_proposition, check_proposition.
  rewrite (@input_infer_refines budget fuel ps arena root entry Arena Root).
  apply bind_pointwise; [reflexivity|intro inferred].
  rewrite prepared_whnf_refines by exact Lookup. reflexivity.
Qed.

Definition checked_constant budget fuel n ps arena tr br (ty body : scope_entry) kind :=
  ignored <- input_header budget fuel n ps arena tr ty ;;
  ignored <- if entry_scoped 0 body
    then input_check budget fuel ps arena tr br (scope_expr ty)
    else Reject MalformedDeclaration ;;
  Accept ({| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := scope_expr ty;
    decl_value := Some (scope_expr body); decl_kind_of := kind |} :: env).

Lemma checked_constant_refines budget fuel n ps arena tr br ty body kind :
  arena_ok arena ->
  scope_ref (arena_scope arena) tr = Accept ty ->
  scope_ref (arena_scope arena) br = Accept body ->
  checked_constant budget fuel n ps arena tr br ty body kind =
    Declarations.checked_constant fuel env n ps (scope_expr ty) (Some (scope_expr body)) kind.
Proof.
  intros Arena Htype Hbody. unfold checked_constant, Declarations.checked_constant.
  rewrite (@input_header_refines budget fuel n ps arena tr ty Arena Htype).
  rewrite (@entry_scoped_refines 0 body).
  - rewrite (@input_check_refines budget fuel ps arena tr br ty body Arena Htype Hbody).
    reflexivity.
  - eapply scope_ref_ok; [exact (proj1 Arena)|exact Hbody].
Qed.

Definition in_arena kind budget fuel n ps arena tr br (ty body : scope_entry) :=
  match kind with
  | DagDefinition hints =>
    ignored <- input_header budget fuel n ps arena tr ty ;;
    ignored <- require (entry_scoped 0 body) MalformedDeclaration ;;
    ignored <- input_check budget fuel ps arena tr br (scope_expr ty) ;;
    primitive <- classify_primitive fuel env n ps (scope_expr ty) (scope_expr body) ;;
    let kind := match primitive with Some p => DPrimitive p | None => DDefinition end in
    Accept ({| decl_hints := hints; decl_name := n; decl_params := ps; decl_type := scope_expr ty;
      decl_value := Some (scope_expr body); decl_kind_of := kind |} :: env)
  | DagTheorem =>
    if name_mem n reserved_names then Reject MalformedDeclaration else
    ignored <- input_header budget fuel n ps arena tr ty ;;
    ignored <- input_proposition budget fuel ps arena tr ;;
    checked_constant budget fuel n ps arena tr br ty body DTheorem
  | DagOpaque =>
    if name_mem n reserved_names then Reject MalformedDeclaration else
    checked_constant budget fuel n ps arena tr br ty body DOpaque
  end.

Lemma in_arena_refines kind budget fuel n ps arena tr br ty body :
  arena_ok arena ->
  scope_ref (arena_scope arena) tr = Accept ty ->
  scope_ref (arena_scope arena) br = Accept body ->
  in_arena kind budget fuel n ps arena tr br ty body =
    match kind with
    | DagDefinition hints => safe_definition_in_arena hints budget fuel env n ps arena tr br ty body
    | DagTheorem => theorem_in_arena budget fuel env n ps arena tr br ty body
    | DagOpaque => safe_opaque_in_arena budget fuel env n ps arena tr br ty body
    end.
Proof.
  intros Arena Htype Hbody. destruct kind; unfold in_arena.
  - rewrite (@input_header_refines budget fuel n ps arena tr ty Arena Htype).
    rewrite (@input_check_refines budget fuel ps arena tr br ty body Arena Htype Hbody).
    unfold safe_definition_in_arena.
    rewrite (@DagAdmission.input_header_refines budget fuel env n ps arena tr ty Arena Htype).
    rewrite (@DagAdmission.input_check_refines budget fuel env ps arena tr br ty body Arena Htype Hbody).
    reflexivity.
  - rewrite (@input_header_refines budget fuel n ps arena tr ty Arena Htype).
    rewrite (@input_proposition_refines budget fuel ps arena tr ty Arena Htype).
    rewrite (@checked_constant_refines budget fuel n ps arena tr br ty body DTheorem Arena Htype Hbody).
    unfold theorem_in_arena.
    rewrite (@DagAdmission.input_header_refines budget fuel env n ps arena tr ty Arena Htype).
    rewrite (@DagTheoremOpaque.input_proposition_refines budget fuel env ps arena tr ty Arena Htype).
    rewrite (@input_checked_constant_refines budget fuel env n ps arena tr br ty body DTheorem Arena Htype Hbody).
    reflexivity.
  - rewrite (@checked_constant_refines budget fuel n ps arena tr br ty body DOpaque Arena Htype Hbody).
    unfold safe_opaque_in_arena.
    rewrite (@input_checked_constant_refines budget fuel env n ps arena tr br ty body DOpaque Arena Htype Hbody).
    reflexivity.
Qed.
End Admission.
End PreparedDag.

(* Only a known cheap defect triggers the linear duplicate lookup: duplicate
   declarations precede universe/scope errors. Valid headers keep indexed lookup. *)
Definition cheap_header_error env n ps ty : option reject_reason :=
  let defect :=
    if negb (names_unique ps) then Some DuplicateUniverse else
    if negb (entry_scoped 0 ty) then Some MalformedDeclaration else None in
  match defect with
  | None => None
  | Some reason =>
    match find_decl n env with
    | Some _ => Some DuplicateDeclaration
    | None => Some reason
    end
  end.

Definition early_header_error kind env n ps ty : option reject_reason :=
  match kind with
  | DagDefinition _ => cheap_header_error env n ps ty
  | DagTheorem | DagOpaque =>
    if name_mem n reserved_names then Some MalformedDeclaration
    else cheap_header_error env n ps ty
  end.

Lemma cheap_header_error_sound lookup env budget fuel n ps arena tr ty reason :
  (forall name, lookup name = find_decl name env) ->
  cheap_header_error env n ps ty = Some reason ->
  PreparedDag.input_header lookup env budget fuel n ps arena tr ty = Reject reason.
Proof.
  intros Lookup Error. unfold cheap_header_error in Error.
  unfold PreparedDag.input_header. rewrite Lookup.
  destruct (names_unique ps); destruct (entry_scoped 0 ty);
    cbn [negb] in *; try discriminate;
    destruct (find_decl n env); inversion Error; reflexivity.
Qed.

Lemma early_header_error_sound lookup env kind budget fuel n ps arena tr br ty body reason :
  (forall name, lookup name = find_decl name env) ->
  early_header_error kind env n ps ty = Some reason ->
  PreparedDag.in_arena lookup env kind budget fuel n ps arena tr br ty body = Reject reason.
Proof.
  intros Lookup Error. destruct kind; cbn [early_header_error] in Error.
  - unfold PreparedDag.in_arena.
    rewrite (cheap_header_error_sound lookup env budget fuel n ps arena tr ty Lookup Error).
    reflexivity.
  - destruct (name_mem n reserved_names) eqn:Reserved.
    + inversion Error; subst. unfold PreparedDag.in_arena. rewrite Reserved. reflexivity.
    + unfold PreparedDag.in_arena. rewrite Reserved.
      rewrite (cheap_header_error_sound lookup env budget fuel n ps arena tr ty Lookup Error).
      reflexivity.
  - destruct (name_mem n reserved_names) eqn:Reserved.
    + inversion Error; subst. unfold PreparedDag.in_arena. rewrite Reserved. reflexivity.
    + unfold PreparedDag.in_arena, PreparedDag.checked_constant. rewrite Reserved.
      rewrite (cheap_header_error_sound lookup env budget fuel n ps arena tr ty Lookup Error).
      reflexivity.
Qed.

(* The thunk is internal, never frontend-supplied. It makes preparation's branch
   boundary explicit in ordinary strict extraction and available to test spies. *)
Definition admit_with_preparation (prepare : unit -> declaration_lookup)
    kind budget fuel env n ps rows tr br : result environment :=
  arena <- arena_build empty_arena rows ;;
  ty <- scope_ref (arena_scope arena) tr ;;
  body <- scope_ref (arena_scope arena) br ;;
  match early_header_error kind env n ps ty with
  | Some reason => Reject reason
  | None =>
    let lookup := prepare tt in
    PreparedDag.in_arena lookup env kind budget fuel n ps arena tr br ty body
  end.

Definition indexed_admit hash kind budget fuel env n ps rows tr br : result environment :=
  admit_with_preparation (fun _ => prepare_lookup hash env)
    kind budget fuel env n ps rows tr br.

Lemma early_in_arena_refines lookup env kind budget fuel n ps arena tr br ty body :
  (forall name, lookup name = find_decl name env) ->
  arena_ok arena ->
  scope_ref (arena_scope arena) tr = Accept ty ->
  scope_ref (arena_scope arena) br = Accept body ->
  (match early_header_error kind env n ps ty with
   | Some reason => Reject reason
   | None => PreparedDag.in_arena lookup env kind budget fuel n ps arena tr br ty body
   end) =
    match kind with
    | DagDefinition hints => safe_definition_in_arena hints budget fuel env n ps arena tr br ty body
    | DagTheorem => theorem_in_arena budget fuel env n ps arena tr br ty body
    | DagOpaque => safe_opaque_in_arena budget fuel env n ps arena tr br ty body
    end.
Proof.
  intros Lookup Arena Htype Hbody.
  transitivity (PreparedDag.in_arena lookup env kind budget fuel n ps arena tr br ty body).
  - destruct (early_header_error kind env n ps ty) eqn:Early; [|reflexivity].
    symmetry. eapply early_header_error_sound; eauto.
  - apply PreparedDag.in_arena_refines; assumption.
Qed.

Theorem indexed_admit_refines hash kind budget fuel env n ps rows tr br :
  indexed_admit hash kind budget fuel env n ps rows tr br =
    linear_env_admit kind budget fuel env n ps rows tr br.
Proof.
  unfold indexed_admit, admit_with_preparation, linear_env_admit.
  destruct kind; unfold DagAdmission.admit_dag_definition,
    DagTheoremOpaque.admit_dag_theorem, DagTheoremOpaque.admit_dag_opaque;
    destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) tr) eqn:Htype; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) br) eqn:Hbody; cbn [bind]; try reflexivity.
  all: apply early_in_arena_refines; auto using prepare_lookup_correct;
    eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Definition indexed_dag_admit kind budget fuel env n ps rows tr br :=
  if RuntimeChecker.use_index fuel env
  then indexed_admit suffix_bitfold8 kind budget fuel env n ps rows tr br
  else linear_env_admit kind budget fuel env n ps rows tr br.

Theorem indexed_dag_admit_refines kind budget fuel env n ps rows tr br :
  indexed_dag_admit kind budget fuel env n ps rows tr br =
    linear_env_admit kind budget fuel env n ps rows tr br.
Proof.
  unfold indexed_dag_admit. destruct (RuntimeChecker.use_index fuel env);
    auto using indexed_admit_refines.
Qed.

Definition indexed_admit_dag_definition hints := indexed_dag_admit (DagDefinition hints).
Definition indexed_admit_dag_theorem := indexed_dag_admit DagTheorem.
Definition indexed_admit_dag_opaque := indexed_dag_admit DagOpaque.

Print Assumptions indexed_admit_refines.
Print Assumptions indexed_dag_admit_refines.
Print Assumptions early_header_error_sound.
