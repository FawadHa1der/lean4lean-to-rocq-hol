(* SPDX-License-Identifier: Apache-2.0
   Admission modes from Lean4Lean/Environment.lean. Restricted declarations
   remain marked in the persistent environment; only checking-local views
   permit their use. The ordinary checker rejects all restricted markers. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker Declarations.
Import ListNotations.

Definition safety_eqb (a b : input_safety) :=
  match a,b with
  | InputSafe,InputSafe | InputPartial,InputPartial | InputUnsafe,InputUnsafe => true
  | _,_ => false
  end.
Definition checking_view (mode : input_safety) (d : declaration) : declaration :=
  let kind := match decl_kind_of d,mode with
    | DUnsafe inner,InputUnsafe => inner
    | DPartial,InputPartial | DPartial,InputUnsafe => DDefinition
    | k,_ => k
    end in
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := decl_value d; decl_kind_of := kind |}.
Definition safety_environment mode env := map (checking_view mode) env.
Definition safety_kind (mode : input_safety) :=
  match mode with InputSafe => DDefinition | InputPartial => DPartial
  | InputUnsafe => DUnsafe DDefinition end.
Definition safe_name n := require (negb (name_mem n reserved_names)) MalformedDeclaration.
Definition check_value (fuel : nat) (env : environment) (ps : list name) (ty value : expr)
    : result unit :=
  _ <- require (scoped 0 value) MalformedDeclaration ;;
  check fuel env ps empty_context value ty.
Definition restricted_constant n ps ty body kind : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := ty;
     decl_value := body; decl_kind_of := kind |}.

Definition restricted_definition hints n ps ty value kind : declaration :=
  {| decl_hints := hints; decl_name := n; decl_params := ps; decl_type := ty;
     decl_value := Some value; decl_kind_of := kind |}.

Definition admit_extended (fuel : nat) (env : environment) (input : input_decl)
    : result environment :=
  match input with
  | InputAxiom n ps ty true =>
    _ <- safe_name n ;;
    let view := safety_environment InputUnsafe env in
    _ <- check_header fuel view n ps ty ;;
    Accept (restricted_constant n ps ty None (DUnsafe DAssumption)::env)
  | InputDefinition hints n ps ty value InputUnsafe =>
    _ <- safe_name n ;;
    let view := safety_environment InputUnsafe env in
    _ <- check_header fuel view n ps ty ;;
    let self := restricted_constant n ps ty None DAssumption in
    _ <- check_value fuel (self::view) ps ty value ;;
    Accept (restricted_definition hints n ps ty value (DUnsafe DDefinition)::env)
  | InputDefinition hints n ps ty value InputPartial =>
    _ <- safe_name n ;;
    _ <- check_header fuel env n ps ty ;;
    _ <- check_value fuel env ps ty value ;;
    Accept (restricted_definition hints n ps ty value DPartial::env)
  | InputOpaque n ps ty value true =>
    _ <- safe_name n ;;
    _ <- check_header fuel env n ps ty ;;
    _ <- check_value fuel env ps ty value ;;
    Accept (restricted_constant n ps ty (Some value) (DUnsafe DOpaque)::env)
  | _ => admit fuel env input
  end.

Definition mutual_name (input : input_decl) : name :=
  match input with InputDefinition _ n _ _ _ _ => n | _ => NameAnon end.
Fixpoint check_mutual_headers (fuel : nat) (view : environment) (ps : list name)
    (mode : input_safety) (inputs : list input_decl) : result (list declaration) :=
  match inputs with
  | [] => Accept []
  | InputDefinition _ n qs ty value safety::inputs =>
    _ <- require (safety_eqb safety mode && list_eqb name_eqb qs ps) MalformedDeclaration ;;
    _ <- safe_name n ;;
    _ <- check_header fuel view n ps ty ;;
    rest <- check_mutual_headers fuel view ps mode inputs ;;
    Accept (restricted_constant n ps ty None DAssumption::rest)
  | _ => Reject MalformedDeclaration
  end.
Fixpoint check_mutual_values (fuel : nat) (view : environment)
    (inputs : list input_decl) : result (list declaration) :=
  match inputs with
  | [] => Accept []
  | InputDefinition hints n ps ty value safety::inputs =>
    _ <- check_value fuel view ps ty value ;;
    rest <- check_mutual_values fuel view inputs ;;
    Accept (restricted_definition hints n ps ty value (safety_kind safety)::rest)
  | _ => Reject MalformedDeclaration
  end.
Definition admit_mutual (fuel : nat) (env : environment) (inputs : list input_decl)
    : result environment :=
  match inputs with
  | InputDefinition _ _ ps _ _ mode::_ =>
    _ <- require (negb (safety_eqb mode InputSafe)) MalformedDeclaration ;;
    _ <- require (names_unique (map mutual_name inputs)) DuplicateDeclaration ;;
    let view := safety_environment mode env in
    placeholders <- check_mutual_headers fuel view ps mode inputs ;;
    generated <- check_mutual_values fuel (List.app placeholders view) inputs ;;
    Accept (List.app generated env)
  | _ => Reject MalformedDeclaration
  end.

Lemma checking_view_preserves_name mode d : decl_name (checking_view mode d) = decl_name d.
Proof. reflexivity. Qed.
Lemma safe_view_retains_partial n ps ty body :
  decl_kind_of (checking_view InputSafe (restricted_constant n ps ty body DPartial)) = DPartial.
Proof. reflexivity. Qed.
Lemma safe_view_retains_unsafe n ps ty body kind :
  decl_kind_of (checking_view InputSafe (restricted_constant n ps ty body (DUnsafe kind))) = DUnsafe kind.
Proof. reflexivity. Qed.
