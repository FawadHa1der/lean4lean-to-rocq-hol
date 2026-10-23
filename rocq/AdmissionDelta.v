(* SPDX-License-Identifier: Apache-2.0
   Checked admission deltas. Existing validators and their ordering are retained;
   complete-result lemmas justify committing only the newly admitted prefix. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker Declarations Safety Inductive InductiveUtils
  NestedTransform NestedAdmission InductiveSafety Quotient LookupRefinement.
Import ListNotations.
Set Implicit Arguments.

Definition result_map {A B} (f : A -> B) (r : result A) : result B :=
  x <- r ;; Accept (f x).
Definition attach_prefix env (r : result environment) :=
  result_map (fun added => added ++ env) r.

Lemma attach_bind {A} env (r : result A) k :
  attach_prefix env (x <- r ;; k x) = (x <- r ;; attach_prefix env (k x)).
Proof. destruct r; reflexivity. Qed.

Definition single_extension env (r : result environment) : Prop :=
  match r with Accept next => exists d, next = d :: env | _ => True end.
Lemma single_bind {A} env (r : result A) k :
  (forall x, single_extension env (k x)) -> single_extension env (x <- r ;; k x).
Proof. destruct r; cbn [bind single_extension]; auto. Qed.

Lemma checked_constant_single fuel env n ps ty body kind :
  single_extension env (checked_constant fuel env n ps ty body kind).
Proof.
  unfold checked_constant. apply single_bind. intro ignored.
  apply single_bind. intro ignored2. cbn [single_extension]. eauto.
Qed.

Ltac solve_single :=
  repeat first [apply single_bind; intro
    | apply checked_constant_single
    | match goal with |- single_extension _ (if ?b then _ else _) => destruct b end
    | solve [cbn [single_extension]; eauto]].

Lemma admit_single fuel env input : single_extension env (admit fuel env input).
Proof.
  destruct input; cbn [admit]; try destruct b; try destruct i; solve_single.
Qed.

Lemma extended_single fuel env input : single_extension env (admit_extended fuel env input).
Proof.
  destruct input; cbn [admit_extended]; try destruct b; try destruct i;
    first [apply admit_single | solve_single].
Qed.

Lemma quotient_single fuel env n ps ty kind :
  single_extension env (admit_quotient fuel env n ps ty kind).
Proof. unfold admit_quotient. solve_single. Qed.

Definition single_delta (r : result environment) := result_map (firstn 1) r.
Lemma single_delta_exact env r : single_extension env r ->
  attach_prefix env (single_delta r) = r.
Proof.
  destruct r as [next|err|reason]; cbn [single_extension]; try reflexivity.
  intros [d ->]. reflexivity.
Qed.

Definition mutual_delta fuel env inputs : result environment :=
  match inputs with
  | InputDefinition _ _ ps _ _ mode :: _ =>
    _ <- require (negb (safety_eqb mode InputSafe)) MalformedDeclaration ;;
    _ <- require (names_unique (map mutual_name inputs)) DuplicateDeclaration ;;
    let view := safety_environment mode env in
    placeholders <- check_mutual_headers fuel view ps mode inputs ;;
    generated <- check_mutual_values fuel (placeholders ++ view) inputs ;;
    Accept generated
  | _ => Reject MalformedDeclaration
  end.

Lemma mutual_delta_exact fuel env inputs :
  attach_prefix env (mutual_delta fuel env inputs) = admit_mutual fuel env inputs.
Proof.
  destruct inputs as [|input rest]; [reflexivity|]. destruct input; try reflexivity.
  unfold mutual_delta, admit_mutual.
  repeat (rewrite attach_bind; apply bind_pointwise; [reflexivity|intro]). reflexivity.
Qed.

Definition nested_delta fuel env types ctors recs : result environment :=
  prepared <- prepare_inductive env types ctors recs ;;
  let '(ps,np,specs) := prepared in
  _ <- require (negb (existsb (fun d => uses_reserved_nested (decl_type d)) ctors))
                MalformedDeclaration ;;
  transformed <- eliminate_nested fuel env ps np specs ;;
  generated <- derive_inductive fuel env ps np (nested_specs transformed) ;;
  if Nat.eqb (nested_aux_count transformed) 0 then
    _ <- verify_members (types ++ ctors ++ recs) generated ;;
    Accept generated
  else
    match types with
    | [] => Reject MalformedDeclaration
    | main::_ =>
      let all := ind_names types in
      let auxiliary := skipn (List.length types)
        (map (fun s => decl_name (spec_decl s)) (nested_specs transformed)) in
      let rec_map := auxiliary_rec_names (decl_name main) auxiliary 1 in
      restored_inds <- map_result (restore_inductive generated transformed all) all ;;
      restored_ctors <- map_result (restore_constructor fuel generated transformed) (ind_names ctors) ;;
      restored_recs <- map_result (restore_recursor fuel generated transformed rec_map all)
        (map rec_name (all ++ auxiliary)) ;;
      let restored := restored_recs ++ restored_ctors ++ restored_inds in
      _ <- verify_members (types ++ ctors ++ recs) restored ;;
      let final_env := restored ++ env in
      _ <- map_result (fun entry =>
        inferred <- infer fuel final_env ps (nested_context transformed) (fst entry) ;; Accept tt)
        (nested_mapping transformed) ;;
      Accept restored
    end.

Lemma nested_delta_exact fuel env types ctors recs :
  attach_prefix env (nested_delta fuel env types ctors recs) =
    admit_inductive_nested fuel env types ctors recs.
Proof.
  unfold nested_delta, admit_inductive_nested. rewrite attach_bind.
  apply bind_pointwise; [reflexivity|intros [[ps np] specs]].
  rewrite attach_bind. apply bind_pointwise; [reflexivity|intro ignored].
  rewrite attach_bind. apply bind_pointwise; [reflexivity|intro transformed].
  rewrite attach_bind. apply bind_pointwise; [reflexivity|intro generated].
  destruct (Nat.eqb (nested_aux_count transformed) 0).
  - rewrite attach_bind. apply bind_pointwise; [reflexivity|intro]. reflexivity.
  - destruct types as [|main rest]; [reflexivity|].
    repeat (rewrite attach_bind; apply bind_pointwise; [reflexivity|intro]). reflexivity.
Qed.

Definition inductive_delta fuel env types ctors recs : result environment :=
  if inductive_input_unsafe types then
    let view := safety_environment InputUnsafe env in
    next <- admit_inductive_nested fuel view types ctors recs ;;
    let generated := filter (fun d =>
      match find_decl (decl_name d) env with None => true | _ => false end) next in
    Accept (map mark_unsafe_inductive generated)
  else nested_delta fuel env types ctors recs.

Lemma inductive_delta_exact fuel env types ctors recs :
  attach_prefix env (inductive_delta fuel env types ctors recs) =
    admit_inductive_extended fuel env types ctors recs.
Proof.
  unfold inductive_delta, admit_inductive_extended.
  destruct (inductive_input_unsafe types).
  - rewrite attach_bind. apply bind_pointwise; [reflexivity|intro]. reflexivity.
  - apply nested_delta_exact.
Qed.

Print Assumptions extended_single.
Print Assumptions mutual_delta_exact.
Print Assumptions nested_delta_exact.
Print Assumptions inductive_delta_exact.
