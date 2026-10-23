(* SPDX-License-Identifier: Apache-2.0
   Standard extraction of actual guard sites and exact dispatch helpers. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax EagerPolicy NatProbeDispatch Checker LookupCore
  GuardOrderPlan GuardOrderRefinement.
Extraction Language OCaml.
Extraction "guard_order_native.ml"
  nat_probe_head pair_probe_guard find_decl core_spine core_succ_name
  Checker.core_lazy_delta Accessor.core_lazy_delta
  Checker.core_true_shortcut Accessor.core_true_shortcut empty_context.
