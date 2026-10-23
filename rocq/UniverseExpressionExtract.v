(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax UniverseExpression.
Extraction Language OCaml.
Extraction "universe_expression_native.ml"
  subst_levels lift subst subst_many instantiate instantiate_many scoped.
