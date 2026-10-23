(* Test-only ordinary extraction, without custom substitutions or casts.
   All algorithm references here use the NEW repaired ordinary Checker. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import IndexedDagAdmission LookupIntegration
  EnvironmentIndexSuffixBenchmark CombinedAdmissionRefinement CheapHeaderRefinement
  MetadataFixtures MetadataCases.
Extraction Language OCaml.
Extraction "cheap_header_native.ml"
  cheap_header_error early_header_error admit_with_preparation
  indexed_admit indexed_dag_admit linear_env_admit
  before_header_indexed_admit before_header_guarded
  linear_cache_new_admit new_ordinary_decode_admit
  RuntimeChecker.use_index prepare_lookup suffix_bitfold8
  MetadataCases.cases MetadataCases.positives MetadataCases.quote_pair
  MetadataCases.expected MetadataCases.check_decoded Metadata.fuel.
