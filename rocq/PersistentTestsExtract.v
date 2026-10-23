(* Ordinary extraction of test APIs, independent of the runtime frontend. *)
From Stdlib Require Import Extraction.
From LeanPort Require Import Syntax Checker Primitives Declarations MetadataFixtures
  MetadataCases PersistentFixtures PersistentIndex PersistentAdmission AdmissionDelta
  LookupIntegration EnvironmentIndexSuffixBenchmark Quotient PersistentStreamFixtures
  StringParityFixtures NestedRegression NestedTransform.
Extraction Language OCaml.
Extraction "persistent_tests_native.ml"
  seed_state extend_state state_environment state_lookup
  state_step state_stream project_result transaction reference_batch reference_stream
  generated_batch find_decl
  Metadata.padded_env Metadata.nat_env Metadata.eq_env Metadata.base_env Metadata.with_add
  Metadata.nat_spec Metadata.eq_spec Metadata.box_spec Metadata.dep_spec Metadata.seed_ind
  MetadataCases.cases MetadataCases.expected MetadataCases.quote_pair MetadataCases.reductions
  Metadata.corrupt_fields Metadata.corrupt_rule Metadata.unsafe_shadow Metadata.without
  Metadata.type0 Metadata.type1 Metadata.u_name Metadata.fuel Metadata.add_value
  lookup_get_constant lookup_nat_ready suffix_bitfold8 canonical_quotient
  PreparedDagLookup.prepared_whnf Checker.whnf empty_context
  RuntimeChecker.use_index primitive_authenticated
  StringParityFixtures.sp_list_spec StringParityFixtures.sp_string_spec
  StringParityFixtures.sp_eq_spec StringParityFixtures.sp_literal_equality
  StringParityFixtures.sp_refl StringParityFixtures.sp_nil StringParityFixtures.sp_u
  StringParityFixtures.sp_observations StringParityFixtures.sp_gate_results
  PersistentStreamFixtures.nested_box_batch PersistentStreamFixtures.nested_tree_batch
  PersistentStreamFixtures.nested_mutations
  NestedRegression.NestedRegression.tree_admission
  NestedRegression.NestedRegression.box_admission
  NestedRegression.NestedRegression.tree NestedRegression.NestedRegression.nested_rec
  NestedRegression.NestedRegression.aux
  NestedRegression.NestedRegression.box_at NestedRegression.NestedRegression.tree_ty
  NestedRegression.NestedRegression.tree_decl NestedRegression.NestedRegression.leaf_ctor
  NestedRegression.NestedRegression.node_ctor
  PreparedDagLookup.prepared_defeq core_expand_string core_char_list core_utf8
  check check_defeq defeq primitive_signature eliminate_nested.
