(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax EagerPolicy WhnfPolicy.
Extraction Language OCaml.
Extraction "whnf_policy_native.ml" whnf_round_limit normal_whnf_rounds
  eager_whnf_rounds run_whnf_rounds.
