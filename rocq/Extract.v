(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Default structural extraction only; no Extract Constant/Inductive overrides. *)
From Coq Require Import Extraction.
From LeanPort Require Import Syntax Universes Checker Declarations Regression ExtensionRegression PerformanceRegression.

Extraction Language OCaml.
Extraction "lean_core.ml"
  infer whnf defeq check check_defeq
  level_equiv level_le normalize_level level_eval sublevel_eval sublevels_eval
  lift subst instantiate subst_levels name_eqb
  empty_context push_binding
  admit check_declarations regression_checks extension_checks performance_checks.
