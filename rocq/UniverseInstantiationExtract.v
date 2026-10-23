(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Universes UniverseSoundness UniverseInstantiation.
Extraction Language OCaml.
Extraction "universe_instantiation_native.ml" subst_level lookup_level
  level_wf level_has_meta level_nodes level_le level_equiv level_eval instantiated_assignment.
