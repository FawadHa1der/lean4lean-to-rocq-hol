(* SPDX-License-Identifier: Apache-2.0
   Focused structural extraction only. No production extraction or overrides. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax EagerPolicy Checker Primitives Declarations
  Inductive InductiveSafety LookupCore LookupIntegration IndexedChecker PreparedDagLookup
  DagScope DagArena DagInfer ReferenceDagInfer IndexedDagInfer EagerPolicyRegression
  ApplicationOrderRegression.
Extraction Language OCaml.
Extraction "eager_policy_native.ml"
  has_external_local_at has_external_local nat_probe_allowed true_probe_allowed
  is_eager_reduce_argument eager_reduce_name
  Checker.checker_mode Accessor.checker_mode checker_with_lookup_mode
  inference_only Accessor.inference_only application_type_defeq infer_step Accessor.infer_step
  core_lazy_delta Accessor.core_lazy_delta core_reduce_nat Accessor.core_reduce_nat
  core_true_shortcut Accessor.core_true_shortcut defeq_step
  derive_inductive admit_inductive_extended admit primitive_authenticated
  primitive_name primitive_signature primitive_call primitive_succ
  core_nat core_nat_name core_zero_name core_succ_name
  core_bool_name core_false_name core_true_name core_nat_ready core_bool_ready
  empty_context push_binding prepare_lookup
  DagInfer.run_memo_infer ReferenceDagInfer.run_memo_infer
  IndexedDagInfer.run_memo_infer arena_build empty_arena scope_ref.
