(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   SOURCE ONLY: every proof script below is proposed and UNEXECUTED.
   Extends, rather than reimplements, QuotientDependencyRegression.QDR.
   Source pins and attribution: SOURCE_PINS.sha256 and README.md. *)
From Stdlib Require Import List String Bool.
From LeanPort Require Import Syntax Checker Declarations Quotient MetadataFixtures
  QuotientDependencyRegression.
From Quotient841 Require Import QuotientDependencyFixtures841.
Import ListNotations.
Open Scope string_scope.

Module QA841.
Module M := Metadata.
Module Existing := QDR.
Module F := Q841.

(* Existing supplies checked type_env/ctor_env/axiom_type_env/axiom_ctor_env,
   non-vacuous Eq/header witnesses, all three ordinary-forgery rejections,
   successful admissions, missing-Eq/duplicate/fuel first-error tests, and
   accepted_quotient_requires_dependencies. Those are not repeated here.
   In particular InputAxiom there is object-language input, not a Rocq axiom. *)

Example reachable_ordinary_dependencies_have_ordinary_tags :
  (env <- Existing.axiom_type_env ;;
    Accept (option_map decl_kind_of (find_decl q_name env))) =
    Accept (Some DAssumption) /\
  (env <- Existing.axiom_ctor_env ;;
    Accept (option_map decl_kind_of (find_decl q_mk_name env))) =
    Accept (Some DAssumption).
Proof. vm_compute; split; reflexivity. Qed.

(* Strengthen existing length-only positives to exact installed declarations. *)
Example genuine_qtype_is_installed :
  (env <- Existing.type_env ;; Accept (find_decl q_name env)) =
  Accept (Some (canonical_quotient QType)).
Proof. vm_compute; reflexivity. Qed.

Example genuine_qctor_is_installed :
  (env <- Existing.ctor_env ;; Accept (find_decl q_mk_name env)) =
  Accept (Some (canonical_quotient QCtor)).
Proof. vm_compute; reflexivity. Qed.

Example genuine_qlift_needs_no_qctor :
  (env <- Existing.type_env ;; Accept (find_decl q_mk_name env)) = Accept None /\
  (env <- Existing.type_env ;; next <- M.add_quot env QLift ;;
    Accept (find_decl q_lift_name next)) = Accept (Some (canonical_quotient QLift)).
Proof. vm_compute; split; reflexivity. Qed.

Example genuine_qind_is_installed :
  (env <- Existing.ctor_env ;; next <- M.add_quot env QInd ;;
    Accept (find_decl q_ind_name next)) = Accept (Some (canonical_quotient QInd)).
Proof. vm_compute; reflexivity. Qed.

Definition admit_renamed (env : environment) (k : quotient_kind) :=
  let d := F.renamed k (F.fresh_params k) in
  admit_quotient M.fuel env (decl_name d) (decl_params d) (decl_type d) k.

Example alpha_renamed_inputs_install_canonical_declarations_each_kind :
  (env <- M.eq_env ;; next <- admit_renamed env QType ;;
    Accept (find_decl q_name next)) = Accept (Some (canonical_quotient QType)) /\
  (env <- Existing.type_env ;; next <- admit_renamed env QCtor ;;
    Accept (find_decl q_mk_name next)) = Accept (Some (canonical_quotient QCtor)) /\
  (env <- Existing.type_env ;; next <- admit_renamed env QLift ;;
    Accept (find_decl q_lift_name next)) = Accept (Some (canonical_quotient QLift)) /\
  (env <- Existing.ctor_env ;; next <- admit_renamed env QInd ;;
    Accept (find_decl q_ind_name next)) = Accept (Some (canonical_quotient QInd)).
Proof. vm_compute; repeat split; reflexivity. Qed.

(* Additional multi-fault ordering controls. Fuel 0 is a negative test input,
   not a change to Metadata.fuel or any operational limit. *)
Example duplicate_name_precedes_duplicate_universes_scope_fuel_and_kind :
  (env <- Existing.axiom_type_env ;;
    admit_quotient 0 env q_name [F.fresh_u; F.fresh_u] (EBVar 0) QCtor) =
  Reject DuplicateDeclaration.
Proof. vm_compute; reflexivity. Qed.

Example duplicate_lift_universes_precede_scope_fuel_and_dependencies :
  (env <- Existing.axiom_type_env ;;
    admit_quotient 0 env q_lift_name [F.fresh_u; F.fresh_u] (EBVar 0) QLift) =
  Reject DuplicateUniverse.
Proof. vm_compute; reflexivity. Qed.

Example scope_error_precedes_fuel_decline :
  (env <- Existing.axiom_type_env ;;
    admit_quotient 0 env q_mk_name [F.fresh_u] (EBVar 0) QCtor) =
  Reject MalformedDeclaration.
Proof. vm_compute; reflexivity. Qed.

Example unknown_header_constant_precedes_dependency_rejection :
  (env <- Existing.axiom_type_env ;;
    admit_quotient M.fuel env q_mk_name [F.fresh_u]
      (EConst F.unrelated_name []) QCtor) = Reject UnknownConstant.
Proof. vm_compute; reflexivity. Qed.

End QA841.
