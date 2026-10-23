(* Test-only joint extraction of depth and linear-cache algorithms. Both use
   the NEW shared Checker; frozen_* aliases name cache topology, not old semantics. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Checker DagScope DagArena
  DagMemo DagQuery DagInfer DagAdmission DagTheoremOpaque
  DagMemoReference ReferenceDagQuery ReferenceDagInfer ReferenceDagAdmission ReferenceDagTheoremOpaque.
Definition indexed_find := DagMemo.cache_find.
Definition indexed_add := DagMemo.cache_add.
Definition frozen_find := DagMemoReference.cache_find.
Definition frozen_add := DagMemoReference.cache_add.
Definition indexed_memo := DagMemo.memo_query.
Definition frozen_memo := DagMemoReference.memo_query.
Definition indexed_recursive := DagInfer.run_memo_infer.
Definition frozen_recursive := ReferenceDagInfer.run_memo_infer.
Definition indexed_state_query := DagInfer.memo_infer.
Definition frozen_state_query := ReferenceDagInfer.memo_infer.
Definition indexed_empty := DagQuery.empty_step_cache.
Definition frozen_empty := ReferenceDagQuery.empty_step_cache.
Definition indexed_definition := DagAdmission.admit_dag_definition.
Definition frozen_definition := ReferenceDagAdmission.admit_dag_definition.
Definition indexed_theorem := DagTheoremOpaque.admit_dag_theorem.
Definition frozen_theorem := ReferenceDagTheoremOpaque.admit_dag_theorem.
Definition indexed_opaque := DagTheoremOpaque.admit_dag_opaque.
Definition frozen_opaque := ReferenceDagTheoremOpaque.admit_dag_opaque.
Extraction Language OCaml.
Extraction "depth_native.ml" indexed_find indexed_add frozen_find frozen_add
  indexed_memo frozen_memo indexed_recursive frozen_recursive
  indexed_state_query frozen_state_query indexed_empty frozen_empty
  indexed_definition frozen_definition indexed_theorem frozen_theorem indexed_opaque frozen_opaque
  empty_arena arena_build checker empty_context DagMemo.path_bucket.
