(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Universes.
From LeanPort Require Import UniverseSoundness.
Extraction Language OCaml.
Extraction "universe_native.ml" normalize_aux normalize_level level_le
  level_equiv levels_equiv level_eval sublevels_eval guard_holds guard_insert level_nodes.
