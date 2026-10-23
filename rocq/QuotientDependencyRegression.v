(* SPDX-License-Identifier: Apache-2.0
   Source-only proposed regressions; not yet compiled or executed.
   Admission witnesses use checked environments, not hand-installed tags. *)
From Stdlib Require Import List String Bool.
From LeanPort Require Import Syntax Checker Declarations Quotient MetadataFixtures.
Import ListNotations.
Open Scope string_scope.
Module QDR.
Module M := Metadata.

Definition admit_axiom_header env kind :=
  let d := canonical_quotient kind in
  Declarations.admit M.fuel env
    (InputAxiom (decl_name d) (decl_params d) (decl_type d) false).

Definition axiom_type_env := env <- M.eq_env ;; admit_axiom_header env QType.
Definition type_env := env <- M.eq_env ;; M.add_quot env QType.
Definition axiom_ctor_env := env <- type_env ;; admit_axiom_header env QCtor.
Definition ctor_env := env <- type_env ;; M.add_quot env QCtor.
Definition header env kind := let d := canonical_quotient kind in
  check_header M.fuel env (decl_name d) (decl_params d) (decl_type d).

Example ordinary_dependencies_are_reachable :
  (env <- axiom_type_env ;; Accept (List.length env)) = Accept 72 /\
  (env <- axiom_ctor_env ;; Accept (List.length env)) = Accept 73.
Proof. vm_compute. split; reflexivity. Qed.

(* These must pass before a rejection can demonstrate the new metadata guard.
   Both were the substantive checks in the old admission function. *)
Example impostors_pass_eq_and_header_checks :
  (env <- axiom_type_env ;; quotient_check_eq env) = Accept tt /\
  (env <- axiom_type_env ;; header env QCtor) = Accept tt /\
  (env <- axiom_type_env ;; header env QLift) = Accept tt /\
  (env <- axiom_ctor_env ;; quotient_check_eq env) = Accept tt /\
  (env <- axiom_ctor_env ;; header env QInd) = Accept tt.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example canonical_input_signatures_match :
  map (fun kind => let d := canonical_quotient kind in
    name_eqb (decl_name d) (decl_name d) &&
    Nat.eqb (List.length (decl_params d)) (List.length (decl_params d)) &&
    expr_eqb (subst_levels (decl_params d) (map LParam (decl_params d))
      (decl_type d)) (decl_type d)) [QType;QCtor;QLift;QInd] =
  [true;true;true;true].
Proof. vm_compute. reflexivity. Qed.

Example ordinary_type_cannot_authorize_quotient_members :
  (env <- axiom_type_env ;; M.add_quot env QCtor) = Reject MalformedDeclaration /\
  (env <- axiom_type_env ;; M.add_quot env QLift) = Reject MalformedDeclaration.
Proof. vm_compute. split; reflexivity. Qed.

Example ordinary_constructor_cannot_authorize_induction :
  (env <- axiom_ctor_env ;; M.add_quot env QInd) = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Example genuine_dependencies_allow_members :
  (env <- type_env ;; next <- M.add_quot env QCtor ;;
    Accept (List.length next)) = Accept 73 /\
  (env <- type_env ;; next <- M.add_quot env QLift ;;
    Accept (List.length next)) = Accept 73 /\
  (env <- ctor_env ;; next <- M.add_quot env QInd ;;
    Accept (List.length next)) = Accept 74.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition renamed_type : declaration :=
  let d := canonical_quotient QType in
  let fresh := NameStr NameAnon "quotient_test_universe" in
  {| decl_name := decl_name d; decl_params := [fresh];
     decl_type := subst_levels (decl_params d) [LParam fresh] (decl_type d);
     decl_value := None; decl_kind_of := DQuotient QType; decl_hints := HintOpaque |}.

Example renamed_canonical_dependency_is_recognized :
  quotient_header_matches QType renamed_type = true.
Proof. vm_compute. reflexivity. Qed.

Definition with_kind d kind : declaration :=
  {| decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := decl_value d;
     decl_kind_of := kind; decl_hints := decl_hints d |}.
Definition with_value d value : declaration :=
  {| decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := value;
     decl_kind_of := decl_kind_of d; decl_hints := decl_hints d |}.
Definition with_header d n ps ty : declaration :=
  {| decl_name := n; decl_params := ps; decl_type := ty;
     decl_value := decl_value d; decl_kind_of := decl_kind_of d;
     decl_hints := decl_hints d |}.

(* Raw-record controls test the guard itself, not reachable admission. *)
Example incorrect_metadata_is_not_a_dependency :
  map (quotient_header_matches QType)
    [with_kind (canonical_quotient QType) DAssumption;
     with_kind (canonical_quotient QType) (DQuotient QCtor);
     with_kind (canonical_quotient QType) (DUnsafe (DQuotient QType));
     with_value (canonical_quotient QType) (Some (ESort LZero))] =
  [false;false;false;false].
Proof. vm_compute. reflexivity. Qed.

Example malformed_dependency_headers_are_rejected :
  let d := canonical_quotient QType in
  let u := NameStr NameAnon "u" in
  map (quotient_header_matches QType)
    [with_header d q_mk_name (decl_params d) (decl_type d);
     with_header d q_name [] (decl_type d);
     with_header d q_name [u;u] (decl_type d);
     with_header d q_name (decl_params d) (ESort LZero)] =
  [false;false;false;false].
Proof. vm_compute. reflexivity. Qed.

Example undeclared_canonical_universe_is_not_hidden_by_renaming :
  let d := canonical_quotient QType in
  quotient_header_matches QType
    (with_header d q_name [NameStr NameAnon "quotient_test_universe"]
      (decl_type d)) = false.
Proof. vm_compute. reflexivity. Qed.

Example first_visible_declaration_controls_authentication :
  let good := canonical_quotient QType in
  let bad := with_kind good DAssumption in
  quotient_dependencies [bad;good] QCtor = false /\
  quotient_dependencies [good;bad] QCtor = true.
Proof. vm_compute. split; reflexivity. Qed.

Example no_extra_constructor_dependency_for_lift :
  quotient_dependencies [canonical_quotient QType] QLift = true /\
  quotient_dependencies [canonical_quotient QType] QInd = false.
Proof. vm_compute. split; reflexivity. Qed.

Example missing_eq_keeps_first_error :
  M.add_quot [] QCtor = Reject UnknownConstant.
Proof. reflexivity. Qed.

Example duplicate_keeps_first_error :
  (env <- axiom_type_env ;; M.add_quot env QType) = Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.

Example header_fuel_decline_is_not_changed_to_rejection :
  (env <- axiom_type_env ;; let d := canonical_quotient QCtor in
    admit_quotient 0 env (decl_name d) (decl_params d) (decl_type d) QCtor) =
  Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

Lemma accepted_quotient_requires_dependencies fuel env n ps ty kind next :
  admit_quotient fuel env n ps ty kind = Accept next ->
  quotient_dependencies env kind = true.
Proof.
  intro accepted. unfold admit_quotient in accepted.
  destruct (quotient_check_eq env); cbn [bind] in accepted; try discriminate.
  destruct (check_header fuel env n ps ty); cbn [bind] in accepted; try discriminate.
  destruct (name_eqb n (decl_name (canonical_quotient kind)) &&
    Nat.eqb (List.length ps) (List.length (decl_params (canonical_quotient kind))));
    cbn [require bind] in accepted; try discriminate.
  destruct (expr_eqb (subst_levels ps
    (map LParam (decl_params (canonical_quotient kind))) ty)
    (decl_type (canonical_quotient kind))); cbn [require bind] in accepted; try discriminate.
  destruct (quotient_dependencies env kind); cbn [require bind] in accepted;
    [reflexivity | discriminate].
Qed.

End QDR.
Print Assumptions QDR.accepted_quotient_requires_dependencies.
Print Assumptions QDR.ordinary_dependencies_are_reachable.
Print Assumptions QDR.ordinary_constructor_cannot_authorize_induction.
