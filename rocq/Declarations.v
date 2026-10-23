(* SPDX-License-Identifier: Apache-2.0
   Changed Gallina port of Lean4Lean/Environment.lean's checked admission.
   Upstream reference and license attribution: NOTICE, ../UPSTREAM.md. *)
From Coq Require Import List String Bool.
From LeanPort Require Import Syntax Universes Checker Primitives.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Definition nat_name := NameStr NameAnon "Nat".
Definition bool_name := NameStr NameAnon "Bool".
Definition reserved_names : list name :=
  [nat_name; NameStr nat_name "zero"; NameStr nat_name "succ";
   NameStr nat_name "add"; NameStr nat_name "pred"; NameStr nat_name "sub";
   NameStr nat_name "mul"; NameStr nat_name "pow"; NameStr nat_name "gcd";
   NameStr nat_name "mod"; NameStr nat_name "div"; NameStr nat_name "beq";
   NameStr nat_name "ble"; NameStr nat_name "bitwise"; NameStr nat_name "land";
   NameStr nat_name "lor"; NameStr nat_name "xor"; NameStr nat_name "shiftLeft";
   NameStr nat_name "shiftRight"; bool_name; NameStr bool_name "false";
   NameStr bool_name "true"; NameStr (NameStr NameAnon "String") "ofList";
   NameStr (NameStr NameAnon "Char") "ofNat"].

Inductive input_safety := InputSafe | InputPartial | InputUnsafe.
Inductive input_decl : Type :=
| InputAxiom : name -> list name -> expr -> bool -> input_decl
| InputDefinition : reducibility_hints -> name -> list name -> expr -> expr -> input_safety -> input_decl
| InputTheorem : name -> list name -> expr -> expr -> input_decl
| InputOpaque : name -> list name -> expr -> expr -> bool -> input_decl
| InputUnsupported : input_decl.

Definition check_header (fuel : nat) (env : environment)
    (n : name) (ps : list name) (ty : expr) : result unit :=
  match find_decl n env with
  | Some _ => Reject DuplicateDeclaration
  | None =>
    if negb (names_unique ps) then Reject DuplicateUniverse else
    if negb (scoped 0 ty) then Reject MalformedDeclaration else
    inferred <- infer fuel env ps empty_context ty ;;
    reduced <- whnf fuel env ps empty_context inferred ;;
    match reduced with ESort _ => Accept tt | _ => Reject ExpectedSort end
  end.

Definition check_proposition (fuel : nat) (env : environment)
    (ps : list name) (ty : expr) : result unit :=
  inferred <- infer fuel env ps empty_context ty ;;
  reduced <- whnf fuel env ps empty_context inferred ;;
  match reduced with
  | ESort u =>
    is_zero <- level_equiv fuel u LZero ;;
    if is_zero then Accept tt else Reject MalformedDeclaration
  | _ => Reject ExpectedSort
  end.

Definition checked_constant (fuel : nat) (env : environment)
    (n : name) (ps : list name) (ty : expr) (body : option expr)
    (kind : decl_kind) : result environment :=
  _ <- check_header fuel env n ps ty ;;
  _ <- match body with
       | None => Accept tt
       | Some value =>
         if scoped 0 value then check fuel env ps empty_context value ty
         else Reject MalformedDeclaration
       end ;;
  Accept ({| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := ty;
             decl_value := body; decl_kind_of := kind |} :: env).

(* Primitive definitions need their own signature/equation validation. Never
   install a familiar name under an arbitrary type or defining equation. *)
Definition admit (fuel : nat) (env : environment) (input : input_decl)
    : result environment :=
  match input with
  | InputAxiom n ps ty unsafe =>
    if unsafe then Decline UnsupportedDeclaration else
    if name_mem n reserved_names then Reject MalformedDeclaration else
    checked_constant fuel env n ps ty None DAssumption
  | InputDefinition hints n ps ty body InputSafe =>
    _ <- check_header fuel env n ps ty ;;
    _ <- require (scoped 0 body) MalformedDeclaration ;;
    _ <- check fuel env ps empty_context body ty ;;
    primitive <- classify_primitive fuel env n ps ty body ;;
    let kind := match primitive with Some p => DPrimitive p | None => DDefinition end in
    Accept ({| decl_hints := hints; decl_name := n; decl_params := ps; decl_type := ty;
      decl_value := Some body; decl_kind_of := kind |}::env)
  | InputDefinition _ _ _ _ _ _ => Decline UnsupportedDeclaration
  | InputTheorem n ps ty body =>
    if name_mem n reserved_names then Reject MalformedDeclaration else
    _ <- check_header fuel env n ps ty ;;
    _ <- check_proposition fuel env ps ty ;;
    checked_constant fuel env n ps ty (Some body) DTheorem
  | InputOpaque n ps ty body unsafe =>
    if unsafe then Decline UnsupportedDeclaration else
    if name_mem n reserved_names then Reject MalformedDeclaration else
    checked_constant fuel env n ps ty (Some body) DOpaque
  | InputUnsupported => Decline UnsupportedDeclaration
  end.

Fixpoint check_declarations (fuel : nat) (env : environment) (ds : list input_decl)
    : result environment :=
  match ds with
  | [] => Accept env
  | d :: ds => next <- admit fuel env d ;; check_declarations fuel next ds
  end.

Lemma unsupported_declines fuel env :
  admit fuel env InputUnsupported = Decline UnsupportedDeclaration.
Proof. reflexivity. Qed.

Lemma partial_definition_declines hints fuel env n ps ty body :
  admit fuel env (InputDefinition hints n ps ty body InputPartial) =
    Decline UnsupportedDeclaration.
Proof. reflexivity. Qed.

Lemma empty_export_unchanged fuel env :
  check_declarations fuel env [] = Accept env.
Proof. reflexivity. Qed.
