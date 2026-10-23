(* SPDX-License-Identifier: Apache-2.0
   Direct production-method boundary controls, with ordinary extraction. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax EagerPolicy WhnfPolicy Checker LookupCore.
Extraction Language OCaml.
Extraction "whnf_production_native.ml"
  Checker.checker_mode Checker.checker_eager_mode
  Accessor.checker_mode Accessor.checker_eager_mode
  find_decl empty_context push_binding.
