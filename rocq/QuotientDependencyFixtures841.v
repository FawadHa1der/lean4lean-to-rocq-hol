(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   SOURCE ONLY: every proof script below is proposed and UNEXECUTED.
   Targets the actual LeanPort.Quotient definitions, not a replacement checker.
   Source pins and attribution: SOURCE_PINS.sha256 and README.md. *)
From Stdlib Require Import List String Bool.
From LeanPort Require Import Syntax Checker Declarations Quotient.
Import ListNotations.
Open Scope string_scope.

Module Q841.

Definition kinds : list quotient_kind := [QType; QCtor; QLift; QInd].
Definition fresh_u := NameStr NameAnon "quotient841_u".
Definition fresh_v := NameStr NameAnon "quotient841_v".
Definition fresh_w := NameStr NameAnon "quotient841_w".
Definition unrelated_name := NameStr NameAnon "quotient841_unrelated".
Definition fresh_params (k : quotient_kind) : list name :=
  match k with QLift => [fresh_u; fresh_v] | _ => [fresh_u] end.

(* Data mutations only. All verdicts below call the production predicates. *)
Definition retag (d : declaration) (k : decl_kind) : declaration :=
  {| decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := decl_value d;
     decl_kind_of := k; decl_hints := decl_hints d |}.
Definition reheader (d : declaration) (n : name) (ps : list name)
    (ty : expr) : declaration :=
  {| decl_name := n; decl_params := ps; decl_type := ty;
     decl_value := decl_value d; decl_kind_of := decl_kind_of d;
     decl_hints := decl_hints d |}.
Definition with_value (d : declaration) (v : option expr) : declaration :=
  {| decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := v;
     decl_kind_of := decl_kind_of d; decl_hints := decl_hints d |}.
Definition renamed (k : quotient_kind) (ps : list name) : declaration :=
  let d := canonical_quotient k in
  reheader d (decl_name d) ps
    (subst_levels (decl_params d) (map LParam ps) (decl_type d)).
Definition wrong_kind (k : quotient_kind) : quotient_kind :=
  match k with
  | QType => QCtor | QCtor => QLift | QLift => QInd | QInd => QType
  end.

(* These are raw-header unit fixtures, not checked admission witnesses. *)
Example canonical_names_and_arities :
  map (fun k => let d := canonical_quotient k in
    (decl_name d, List.length (decl_params d))) kinds =
  [(q_name, 1); (q_mk_name, 1); (q_lift_name, 2); (q_ind_name, 1)].
Proof. vm_compute; reflexivity. Qed.

Example canonical_headers_each_kind :
  map (fun k => quotient_header_matches k (canonical_quotient k)) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example canonical_singleton_dependencies_each_kind :
  map (fun k => quotient_dependency [canonical_quotient k] k) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example alpha_renamed_headers_each_kind :
  map (fun k => quotient_header_matches k (renamed k (fresh_params k))) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example alpha_renamed_dependencies_each_kind :
  map (fun k => quotient_dependency [renamed k (fresh_params k)] k) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example lift_universe_positions_can_be_renamed_consistently :
  quotient_header_matches QLift
    (renamed QLift [NameStr NameAnon "v"; NameStr NameAnon "u"]) = true.
Proof. vm_compute; reflexivity. Qed.

Example changing_only_the_parameter_list_is_not_alpha_renaming :
  map (fun k => let d := canonical_quotient k in
    quotient_header_matches k
      (reheader d (decl_name d) (fresh_params k) (decl_type d))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example swapping_lift_parameters_without_substitution_is_rejected :
  let d := canonical_quotient QLift in
  quotient_header_matches QLift
    (reheader d (decl_name d) (rev (decl_params d)) (decl_type d)) = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_quotient_tags_each_kind :
  map (fun k => quotient_header_matches k
    (retag (canonical_quotient k) (DQuotient (wrong_kind k)))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_forged_headers_each_kind :
  map (fun k => map (fun tag => quotient_header_matches k
    (retag (canonical_quotient k) tag))
    [DAssumption; DDefinition; DTheorem; DOpaque]) kinds =
  [[false; false; false; false]; [false; false; false; false];
   [false; false; false; false]; [false; false; false; false]].
Proof. vm_compute; reflexivity. Qed.

Example wrapped_unsafe_tags_each_kind :
  map (fun k => quotient_header_matches k
    (retag (canonical_quotient k) (DUnsafe (DQuotient k)))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example present_values_each_kind :
  map (fun k => quotient_header_matches k
    (with_value (canonical_quotient k) (Some (ESort LZero)))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example malformed_types_each_kind :
  map (fun k => let d := canonical_quotient k in
    quotient_header_matches k
      (reheader d (decl_name d) (decl_params d) (ESort LZero))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example wrong_names_each_kind :
  map (fun k => let d := canonical_quotient k in
    quotient_header_matches k
      (reheader d unrelated_name (decl_params d) (decl_type d))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example missing_universe_binders_each_kind :
  map (fun k => quotient_header_matches k (renamed k [])) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example excess_unique_universe_binders_each_kind :
  map (fun k => quotient_header_matches k
    (renamed k (fresh_w :: fresh_params k))) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Definition duplicate_lift := renamed QLift [fresh_u; fresh_u].

(* Unlike a two-binder QType, this isolates uniqueness from the arity guard.
   It also satisfies the matcher's exact expected substituted type. *)
Example duplicate_lift_has_correct_arity_and_substituted_type :
  let d := canonical_quotient QLift in
  (Nat.eqb (List.length (decl_params duplicate_lift))
     (List.length (decl_params d)),
   expr_eqb (decl_type duplicate_lift)
     (subst_levels (decl_params d) (map LParam (decl_params duplicate_lift))
       (decl_type d)),
   names_unique (decl_params duplicate_lift)) = (true, true, false).
Proof. vm_compute; reflexivity. Qed.

Example duplicate_lift_header_and_dependency_are_rejected :
  (quotient_header_matches QLift duplicate_lift,
   quotient_dependency [duplicate_lift] QLift) = (false, false).
Proof. vm_compute; reflexivity. Qed.

Example absent_dependencies_each_kind :
  map (quotient_dependency []) kinds = [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example wrong_kind_singleton_dependencies_each_kind :
  map (fun k => quotient_dependency
    [retag (canonical_quotient k) (DQuotient (wrong_kind k))] k) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_forged_singleton_dependencies_each_kind :
  map (fun k => quotient_dependency
    [retag (canonical_quotient k) DAssumption] k) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example present_value_singleton_dependencies_each_kind :
  map (fun k => quotient_dependency
    [with_value (canonical_quotient k) (Some (ESort LZero))] k) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example malformed_type_singleton_dependencies_each_kind :
  map (fun k => let d := canonical_quotient k in
    quotient_dependency
      [reheader d (decl_name d) (decl_params d) (ESort LZero)] k) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example first_visible_impostor_hides_canonical_each_kind :
  map (fun k => let d := canonical_quotient k in
    quotient_dependency [retag d DAssumption; d] k) kinds =
  [false; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example first_visible_canonical_hides_impostor_each_kind :
  map (fun k => let d := canonical_quotient k in
    quotient_dependency [d; retag d DAssumption] k) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example unrelated_headers_do_not_shadow_each_kind :
  map (fun k => let d := canonical_quotient k in
    let other := reheader d unrelated_name (decl_params d) (ESort LZero) in
    (quotient_dependency [other] k, quotient_dependency [other; d] k)) kinds =
  [(false, true); (false, true); (false, true); (false, true)].
Proof. vm_compute; reflexivity. Qed.

Example empty_dependency_graph :
  map (quotient_dependencies []) kinds = [true; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example qtype_alone_authorizes_ctor_and_lift_but_not_ind :
  map (quotient_dependencies [canonical_quotient QType]) kinds =
  [true; true; true; false].
Proof. vm_compute; reflexivity. Qed.

Example qctor_alone_does_not_replace_qtype :
  map (quotient_dependencies [canonical_quotient QCtor]) kinds =
  [true; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example qtype_and_qctor_authorize_all_four :
  map (quotient_dependencies [canonical_quotient QType; canonical_quotient QCtor])
    kinds = [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

Example lift_and_ind_headers_are_not_substitutes :
  map (quotient_dependencies [canonical_quotient QLift; canonical_quotient QInd])
    kinds = [true; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example forged_ctor_does_not_block_lift_but_blocks_ind :
  map (quotient_dependencies
    [retag (canonical_quotient QCtor) DAssumption; canonical_quotient QType])
    kinds = [true; true; true; false].
Proof. vm_compute; reflexivity. Qed.

Example forged_type_blocks_all_members_even_with_genuine_ctor :
  map (quotient_dependencies
    [retag (canonical_quotient QType) DAssumption; canonical_quotient QCtor])
    kinds = [true; false; false; false].
Proof. vm_compute; reflexivity. Qed.

Example ind_cannot_recover_buried_canonical_type :
  quotient_dependencies
    [retag (canonical_quotient QType) DAssumption;
     canonical_quotient QCtor; canonical_quotient QType] QInd = false.
Proof. vm_compute; reflexivity. Qed.

Example ind_cannot_recover_buried_canonical_ctor :
  quotient_dependencies
    [retag (canonical_quotient QCtor) DAssumption;
     canonical_quotient QType; canonical_quotient QCtor] QInd = false.
Proof. vm_compute; reflexivity. Qed.

Example ind_ignores_buried_impostors_after_visible_canonicals :
  quotient_dependencies
    [canonical_quotient QCtor; canonical_quotient QType;
     retag (canonical_quotient QType) DAssumption;
     retag (canonical_quotient QCtor) DAssumption] QInd = true.
Proof. vm_compute; reflexivity. Qed.

Example dependencies_can_use_independent_universe_binder_names :
  map (quotient_dependencies
    [renamed QCtor [fresh_v]; renamed QType [fresh_u]]) kinds =
  [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

(* Operational equations only; no global typing/soundness assertion. *)
Lemma qtype_never_requires_dependencies (env : environment) :
  quotient_dependencies env QType = true.
Proof. reflexivity. Qed.

Lemma ctor_and_lift_have_exactly_the_type_dependency (env : environment) :
  quotient_dependencies env QCtor = quotient_dependency env QType /\
  quotient_dependencies env QLift = quotient_dependency env QType.
Proof. split; reflexivity. Qed.

Lemma ind_has_exactly_both_dependencies (env : environment) :
  quotient_dependencies env QInd =
    (quotient_dependency env QType && quotient_dependency env QCtor).
Proof. reflexivity. Qed.

Lemma dependency_uses_first_visible_header k d env :
  find_decl (decl_name (canonical_quotient k)) env = Some d ->
  quotient_dependency env k = quotient_header_matches k d.
Proof. intro visible; unfold quotient_dependency; rewrite visible; reflexivity. Qed.

Lemma eq_rejection_is_first fuel env n ps ty k reason :
  quotient_check_eq env = Reject reason ->
  admit_quotient fuel env n ps ty k = Reject reason.
Proof. intro eq_error; unfold admit_quotient; rewrite eq_error; reflexivity. Qed.

Lemma header_rejection_precedes_signature_and_dependencies fuel env n ps ty k reason :
  quotient_check_eq env = Accept tt ->
  check_header fuel env n ps ty = Reject reason ->
  admit_quotient fuel env n ps ty k = Reject reason.
Proof.
  intros eq_ok header_error; unfold admit_quotient; rewrite eq_ok.
  cbn [bind]; rewrite header_error; reflexivity.
Qed.

Lemma header_decline_precedes_signature_and_dependencies fuel env n ps ty k reason :
  quotient_check_eq env = Accept tt ->
  check_header fuel env n ps ty = Decline reason ->
  admit_quotient fuel env n ps ty k = Decline reason.
Proof.
  intros eq_ok header_decline; unfold admit_quotient; rewrite eq_ok.
  cbn [bind]; rewrite header_decline; reflexivity.
Qed.

(* Reuse QDR.accepted_quotient_requires_dependencies from the existing
   regression module; do not duplicate that proof here. *)
End Q841.
