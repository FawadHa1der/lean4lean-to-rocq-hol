(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Universes UniverseSoundness UniverseCompleteness.
Extraction Language OCaml.
Extraction "universe_complete_native.ml" normalize_aux normalize_level level_le
  level_equiv levels_equiv level_eval sublevels_eval sublevel_le sublevels_le
  atom_countervaluation level_nodes.
