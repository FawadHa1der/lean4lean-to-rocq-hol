(* SPDX-License-Identifier: Apache-2.0
   Default structural extraction only; expected outcomes stay in the test driver. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import StringParityFixtures.
Extraction Language OCaml.
Extraction "string_parity.ml" sp_gate_results sp_observations.
