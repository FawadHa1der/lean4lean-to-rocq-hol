(* Test-only ordinary extraction. No extraction substitutions. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Checker Primitives MetadataFixtures MetadataCases
  PreparedDagLookup LookupIntegration IndexedDagAdmission RuntimeChecker.
Extraction Language OCaml.
Extraction "metadata_native.ml"
  Metadata.padded_env Metadata.nat_env Metadata.eq_env Metadata.structure_env Metadata.base_env
  Metadata.with_add Metadata.fixture_shape_checks Metadata.rejected_ctor_metadata Metadata.rejected_rec_metadata
  Metadata.rejected_quot_signature Metadata.missing_eq_quot
  MetadataCases.cases MetadataCases.positives MetadataCases.reductions
  MetadataCases.guarded MetadataCases.forced MetadataCases.linear_cache_new MetadataCases.ordinary
  MetadataCases.expected MetadataCases.check_decoded MetadataCases.quote_pair
  prepared_whnf prepare_lookup suffix_bitfold8 Checker.whnf Syntax.empty_context
  RuntimeChecker.use_index primitive_authenticated primitive_name
  Metadata.fuel Metadata.add_value primitive_two.
