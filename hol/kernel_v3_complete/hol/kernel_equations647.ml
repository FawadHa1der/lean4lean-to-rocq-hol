(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Explicit canonical theorem registry. SOURCE ONLY / UNCOMPILED / NOT RUN.
   No fixture equations, theorem-name lookup, compset creation or query run.
   See ../REPORT647.txt for the retained FLAT finding,650 repair and boundaries. *)
needs "hol/file_driver642.ml";;
needs "compute.ml";;
needs "calc_num.ml";;

(* Genuine defining theorems, including508's proved specification equation.
   Induction/recursion-existence principles and proof fixtures are not rules. *)
let l4_kernel_project_equations647 : thm list = [
  (* /private/tmp/hol-flatten-repair650/hol/flatten_prelude650.ml *)
  l4_flat650;
  (* /private/tmp/hol-checked-admission631/hol/checked_admission631.ml *)
  l4_inductive_derived_names631;
  l4_derive_inductive631;
  l4_has_nested_inductive631;
  l4_admit_inductive631;
  (* /private/tmp/hol-checked-inductives629/hol/checked_inductives629.ml *)
  l4_check_inductive_types629;
  l4_check_positive629;
  l4_check_field629;
  l4_check_ctors629;
  l4_check_all_ctors629;
  l4_large_elimination629;
  l4_k_target629;
  (* /private/tmp/hol-checked-minors630/hol/checked_minors630.ml *)
  l4_build_recursive_args630;
  l4_build_minors630;
  l4_build_all_minors630;
  (* /private/tmp/hol-checked-telescope606/hol/checked_telescope606.ml *)
  l4_ind_sort606;
  l4_consume_type_annotations_aux606;
  l4_consume_type_annotations606;
  l4_checked_domain606;
  l4_open_telescope606;
  l4_open_parameters606;
  l4_apply_parameters606;
  (* /private/tmp/hol-constant-operations528/hol/constant_operations528.ml *)
  l4_level_wf528;
  l4_check_level528;
  l4_check_levels528;
  l4_get_constant528;
  l4_core_unfold528;
  (* /private/tmp/hol-conversion-fallback596/hol/conversion_fallback596.ml *)
  l4_core_try_string_expansion596;
  l4_core_compare_fallback596;
  l4_compare_after_whnf596;
  l4_core_quick596;
  l4_core_proof_irrel596;
  l4_core_offset596;
  l4_core_try_unfold_proj_app596;
  l4_core_opposite_projection596;
  (* /private/tmp/hol-conversion-helpers595/hol/conversion_helpers595.ml *)
  l4_eta_compare595;
  l4_core_compare_args595;
  l4_core_same_head595;
  l4_core_congruent_apps595;
  l4_core_delta_congruent595;
  l4_compare_heads595;
  l4_core_compare_fields595;
  l4_core_structure_eta595;
  l4_core_unit_like595;
  (* /private/tmp/hol-inductive-derivation516/hol/inductive_derivation516.ml *)
  l4_kchecked_spec516;
  l4_kchecked_indices516;
  l4_kchecked_level516;
  l4_kstats_params516;
  l4_kstats_types516;
  l4_kstats_names516;
  l4_kstats_levels516;
  l4_kstats_result516;
  l4_kstats_unsafe516;
  l4_kstats_state516;
  l4_kmotive_type_info516;
  l4_kmotive_local516;
  l4_kmotive_major516;
  l4_kra_field516;
  l4_kra_arguments516;
  l4_kra_inductive516;
  l4_kra_indices516;
  l4_kminor_ctor516;
  l4_kminor_owner516;
  l4_kminor_local516;
  l4_kminor_fields516;
  l4_kminor_recursive516;
  l4_has_inductive516;
  l4_recursive_constructor516;
  l4_reflexive_constructor516;
  l4_check_primitive_inductive516;
  l4_kflatten516;
  l4_derived_inductive516;
  l4_verify_ind_metadata516;
  (* /private/tmp/hol-inductive-operations521/hol/inductive_operations521.ml *)
  l4_valid_ind_app_at521;
  l4_valid_ind_app521;
  l4_ind_app_indices521;
  l4_raw_arity521;
  l4_level_never_zero521;
  l4_fresh_elim_name521;
  l4_build_motives521;
  l4_build_ihs521;
  (* /private/tmp/hol-inductive-preparation518/hol/inductive_preparation518.ml *)
  l4_gather_ctors518;
  l4_gather_specs518;
  l4_safety_matches518;
  l4_prepare_inductive518;
  (* /private/tmp/hol-inductive-safety633/hol/inductive_safety633.ml *)
  l4_mark_unsafe_inductive633;
  l4_inductive_input_unsafe633;
  l4_admit_inductive_extended633;
  (* /private/tmp/hol-inference586/hol/inference586.ml *)
  l4_infer_step586;
  (* /private/tmp/hol-kernel-beta526/hol/kernel_beta526.ml *)
  l4_ksubst_many526;
  l4_kinstantiate_many526;
  l4_kcore_beta_collect526;
  l4_kcore_beta526;
  (* /private/tmp/hol-kernel-composition597/hol/kernel_checker597.ml *)
  l4_checker_mode597;
  l4_checker597;
  l4_infer597;
  l4_whnf597;
  l4_defeq597;
  l4_check597;
  l4_check_defeq597;
  (* /private/tmp/hol-kernel-composition597/hol/kernel_conversion597.ml *)
  l4_core_lazy_delta597;
  l4_core_finish_conversion597;
  l4_core_is_true597;
  l4_core_true_shortcut597;
  l4_defeq_step597;
  (* /private/tmp/hol-kernel-context532/hol/kernel_context532.ml *)
  l4_kbinding_type532;
  l4_kbinding_value532;
  l4_kcontext_bound532;
  l4_kcontext_free532;
  l4_kempty_context532;
  l4_kpush_binding532;
  l4_kfind_free532;
  l4_kstate_context532;
  l4_core_occurs532;
  l4_core_inductive532;
  l4_core_constructor532;
  l4_core_structure532;
  (* /private/tmp/hol-kernel-control543/hol/kernel_control543.ml *)
  l4_has_external_local_at543;
  l4_has_external_local543;
  l4_has_named_fvar543;
  l4_nat_probe_allowed543;
  l4_true_probe_allowed543;
  l4_eager_reduce_name543;
  l4_is_eager_reduce_argument543;
  l4_nat_probe_head543;
  l4_pair_probe_guard543;
  l4_infer_method543;
  l4_infer_type_method543;
  l4_whnf_method543;
  l4_whnf_core_method543;
  l4_defeq_method543;
  l4_method_mode543;
  l4_eager_defeq_method543;
  l4_inference_only543;
  l4_application_type_defeq543;
  l4_sort_of543;
  l4_core_apply_type543;
  l4_normal_whnf_rounds543;
  l4_eager_whnf_rounds543;
  l4_whnf_round_limit543;
  l4_run_whnf_rounds543;
  (* /private/tmp/hol-kernel-declarations493/hol/kernel_declarations493.ml *)
  l4_kind_num_params493;
  l4_kind_num_indices493;
  l4_kind_all493;
  l4_kind_ctors493;
  l4_kind_num_nested493;
  l4_kind_is_rec493;
  l4_kind_is_reflexive493;
  l4_kind_is_unsafe493;
  l4_kctor_induct493;
  l4_kctor_index493;
  l4_kctor_num_params493;
  l4_kctor_num_fields493;
  l4_kctor_is_unsafe493;
  l4_krule_ctor493;
  l4_krule_nfields493;
  l4_krule_rhs493;
  l4_krec_all493;
  l4_krec_num_params493;
  l4_krec_num_indices493;
  l4_krec_num_motives493;
  l4_krec_num_minors493;
  l4_krec_rules493;
  l4_krec_k493;
  l4_krec_is_unsafe493;
  l4_kprimitive_eqb493;
  l4_khints_lt493;
  l4_kdecl_name493;
  l4_kdecl_params493;
  l4_kdecl_type493;
  l4_kdecl_value493;
  l4_kdecl_kind493;
  l4_kdecl_hints493;
  l4_keffective_hints493;
  l4_kfind_decl493;
  l4_kspec_decl493;
  l4_kspec_ctors493;
  (* /private/tmp/hol-kernel-fastpaths538/hol/kernel_fastpaths538.ml *)
  l4_core_alpha538;
  l4_core_alpha_eq538;
  l4_core_delta_info538;
  l4_core_delta_head538;
  l4_core_delta_sides538;
  l4_core_erasing_delta538;
  (* /private/tmp/hol-kernel-locals489/hol/kernel_locals489.ml *)
  l4_klocal_id489;
  l4_klocal_user489;
  l4_klocal_binder489;
  l4_klocal_type489;
  l4_klocal_expr489;
  l4_kabstract_local489;
  l4_kclose_pi489;
  l4_kclose_lam489;
  l4_kapply_exprs489;
  l4_kapply_locals489;
  l4_ksplit_app_aux489;
  l4_ksplit_app489;
  (* /private/tmp/hol-kernel-naturals544/hol/kernel_naturals544.ml *)
  l4_core_bitfold544;
  l4_core_bitop544;
  l4_core_nat_value544;
  l4_core_nat_constructor544;
  l4_core_shiftr544;
  l4_core_binary_nat544;
  (* /private/tmp/hol-kernel-strings539/hol/kernel_strings539.ml *)
  l4_core_list_name539;
  l4_core_cont539;
  l4_core_digit539;
  l4_core_append_digit539;
  l4_core_utf8_scan539;
  l4_core_utf8_539;
  l4_core_char_list539;
  l4_core_expand_string539;
  (* /private/tmp/hol-kernel-syntax447/hol/kernel_syntax447.ml *)
  l4_klift447;
  l4_ksubst447;
  l4_kinst447;
  l4_kscoped447;
  l4_kfree447;
  l4_klevel_meta447;
  l4_kmeta447;
  (* /private/tmp/hol-kernel-universes488/hol/kernel_universes488.ml *)
  l4_klookup_level488;
  l4_ksubst_level488;
  l4_ksubst_levels488;
  (* /private/tmp/hol-literal-readiness533/hol/literal_readiness533.ml *)
  l4_core_nat_name533;
  l4_core_zero_name533;
  l4_core_succ_name533;
  l4_core_bool_name533;
  l4_core_false_name533;
  l4_core_true_name533;
  l4_core_char_name533;
  l4_core_char_of_nat533;
  l4_core_string_name533;
  l4_core_string_of_list533;
  l4_core_nat533;
  l4_core_ctor_shape533;
  l4_core_nat_ready533;
  l4_core_bool_ready533;
  l4_core_string_ready533;
  l4_core_supported533;
  (* /private/tmp/hol-member-verification509/hol/member_verification509.ml *)
  l4_klist_eqb509;
  l4_ksame_names509;
  l4_inductive_data_eqb509;
  l4_constructor_data_eqb509;
  l4_rule_eqb509;
  l4_recursor_data_eqb509;
  l4_verify_rec_metadata509;
  l4_verify_member_metadata509;
  l4_verify_members509;
  (* /private/tmp/hol-natural-reduction549/hol/natural_reduction549.ml *)
  l4_core_reduce_nat_reference549;
  l4_core_reduce_nat549;
  (* /private/tmp/hol-nested-admission634/hol/nested_admission634.ml *)
  l4_nested_checked_context634;
  l4_admit_inductive_nested634;
  (* /private/tmp/hol-nested-allocation437/hol/nested_allocation437.ml *)
  l4_na_bind437;
  l4_nested_replace_prefix437;
  l4_nested_rename_ctors437;
  l4_nested_aux_name437;
  l4_nested_rec_name437;
  l4_name_mem437;
  l4_names_unique437;
  l4_nested_reserved437;
  l4_nested_blocked437;
  l4_nested_unique_aux437;
  (* /private/tmp/hol-nested-candidate494/hol/nested_candidate494.ml *)
  l4_knw_specs494;
  l4_knw_mapping494;
  l4_knw_next_aux494;
  l4_knw_next_local494;
  l4_nested_set_specs494;
  l4_nested_set_local494;
  l4_kfirstn494;
  l4_knested_names494;
  l4_nested_candidate494;
  (* /private/tmp/hol-nested-declarations505/hol/nested_declarations505.ml *)
  l4_restore_rule505;
  l4_restore_recursor505;
  l4_restore_constructor505;
  l4_restore_inductive505;
  l4_name_prefix505;
  l4_uses_reserved_nested505;
  (* /private/tmp/hol-nested-expression499/hol/nested_expression499.ml *)
  l4_knested_params499;
  l4_knested_context499;
  l4_knested_specs499;
  l4_knested_mapping499;
  l4_knested_aux_names499;
  l4_knested_aux_count499;
  l4_kskipn499;
  l4_kmap_result499;
  l4_nested_ctor_pattern499;
  l4_restore_ctor_name499;
  l4_rewrite_nested_head499;
  l4_restore_nested_expr499;
  l4_restore_open499;
  l4_restore_nested_type499;
  (* /private/tmp/hol-nested-family498/hol/nested_family498.ml *)
  l4_knested_used_names498;
  l4_nested_make_ctors498;
  l4_nested_expand_family498;
  (* /private/tmp/hol-nested-keys480/hol/nested_keys480.ml *)
  l4_kexpr_eqb480;
  l4_nested_same_flags480;
  l4_nested_key_eq480;
  l4_nested_find_mapping480;
  (* /private/tmp/hol-nested-names508/hol/nested_names508.ml *)
  l4_decimal_digits508;
  l4_indexed_rec_name508;
  l4_auxiliary_rec_names508;
  (* /private/tmp/hol-nested-parameters491/hol/nested_parameters491.ml *)
  l4_kr_bind491;
  l4_kr_from_na491;
  l4_kstate_next491;
  l4_kstate_bound491;
  l4_kstate_free491;
  l4_kinitial_state491;
  l4_kind_id491;
  l4_kind_fresh491;
  l4_nested_open_params491;
  l4_nested_instantiate_params491;
  (* /private/tmp/hol-nested-prefix420/hol/nested_prefix420.ml *)
  l4_prefix_string420;
  l4_prefix_numeric420;
  l4_name_prefix420;
  l4_name_replace_prefix420;
  l4_name_append420;
  l4_name_depth420;
  (* /private/tmp/hol-nested-restoration495/hol/nested_restoration495.ml *)
  l4_krestore_lookup495;
  l4_krestore_name495;
  l4_klocal_replacement495;
  l4_kreplacement_at495;
  l4_kinstantiate_locals495;
  (* /private/tmp/hol-nested-transform502/hol/nested_transform502.ml *)
  l4_nested_replace_root502;
  l4_nested_rewrite502;
  l4_nested_rewrite_ctors502;
  l4_knth_error502;
  l4_nested_replace_spec502;
  l4_nested_worklist502;
  l4_eliminate_nested502;
  (* /private/tmp/hol-nested-traversal449/hol/nested_traversal449.ml *)
  l4_nested_lookup_local449;
  l4_nested_rebase449;
  l4_nested_has_new449;
  l4_nested_any_new449;
  (* /private/tmp/hol-ordinary-admission607/hol/ordinary_admission607.ml *)
  l4_reserved_names607;
  l4_check_header607;
  l4_check_proposition607;
  l4_checked_constant607;
  l4_admit_basic607;
  l4_check_basic_declarations607;
  (* /private/tmp/hol-primitive-admission620/hol/ordinary_admission620.ml *)
  l4_admit620;
  l4_check_declarations620;
  (* /private/tmp/hol-primitive-admission620/hol/primitive_admission620.ml *)
  l4_primitive_equations620;
  l4_primitive_check_equations620;
  l4_primitive_is_text620;
  l4_primitive_ensure_type620;
  l4_primitive_check_text_interface620;
  l4_primitive_check_nat_equations620;
  l4_classify_primitive620;
  (* /private/tmp/hol-primitive-foundations619/hol/primitive_foundations619.ml *)
  l4_primitive_name619;
  l4_primitive_kinds619;
  l4_primitive_lookup_in619;
  l4_primitive_lookup619;
  l4_primitive_bitwise_name619;
  l4_primitive_bool619;
  l4_primitive_char619;
  l4_primitive_string619;
  l4_primitive_list_char619;
  l4_primitive_arrow619;
  l4_primitive_signature619;
  l4_primitive_zero619;
  l4_primitive_succ619;
  l4_primitive_one619;
  l4_primitive_two619;
  l4_primitive_true619;
  l4_primitive_false619;
  l4_primitive_call619;
  l4_primitive_check_signature619;
  l4_primitive_authenticated619;
  l4_primitive_dependencies619;
  l4_primitive_closed619;
  l4_primitive_context619;
  l4_primitive_lhs619;
  l4_primitive_rhs619;
  l4_primitive_equation_at619;
  l4_primitive_x_context619;
  l4_primitive_xy_context619;
  (* /private/tmp/hol-primitive-recursors622/hol/primitive_recursors622.ml *)
  l4_primitive_whnf_core622;
  l4_primitive_unfold622;
  l4_primitive_lambda_telescope622;
  l4_primitive_no_free622;
  l4_primitive_proof622;
  l4_primitive_probe_pack622;
  l4_primitive_probe_dom622;
  l4_primitive_probe_functional622;
  l4_primitive_check_go622;
  l4_primitive_unfold_nat_well_founded622;
  l4_primitive_run_probe622;
  l4_primitive_first_measure622;
  l4_primitive_check_gcd622;
  l4_primitive_bool_operator_type622;
  l4_primitive_check_bitwise622;
  l4_primitive_check_boolean_operator622;
  l4_primitive_check_bitwise_instance622;
  (* /private/tmp/hol-primitive-reflection621/hol/primitive_reflection621.ml *)
  l4_primitive_path_aux621;
  l4_primitive_path621;
  l4_primitive_const621;
  l4_pq_embed621;
  l4_pq_app621;
  l4_pq_apps621;
  l4_pq_lam621;
  l4_pq_pi621;
  l4_pq_arrow621;
  l4_pq_run621;
  l4_pq_const621;
  l4_pq_prop621;
  l4_pq_type0621;
  l4_pq_nat621;
  l4_pq_bool621;
  l4_pq_tru621;
  l4_pq_fal621;
  l4_pq_zero621;
  l4_pq_one621;
  l4_pq_two621;
  l4_pq_succ621;
  l4_pq_call621;
  l4_pq_eq621;
  l4_pq_refl621;
  l4_pq_not621;
  l4_pq_dec621;
  l4_pq_is_true621;
  l4_pq_is_false621;
  l4_pq_ite621;
  l4_pq_dite621;
  l4_pq_bool_dec621;
  l4_reflection_type621;
  l4_reflection_true621;
  l4_reflection_false621;
  l4_reflection_dec621;
  l4_primitive_reflection_type621;
  l4_primitive_reflection_make621;
  l4_primitive_reflection_ite621;
  l4_primitive_reflection_dite621;
  l4_primitive_eq_closed621;
  l4_primitive_check_closed621;
  l4_primitive_check_reflection621;
  l4_primitive_condition_prop621;
  l4_primitive_condition_dec621;
  l4_primitive_condition_ite621;
  l4_primitive_condition_dite621;
  l4_primitive_condition_decide621;
  l4_primitive_condition_proof621;
  l4_primitive_check_condition621;
  l4_primitive_go_name621;
  l4_primitive_le621;
  l4_primitive_go_type621;
  l4_primitive_fuel_top621;
  l4_primitive_fuel_step621;
  l4_primitive_check_fuel_rec621;
  (* /private/tmp/hol-projection-quotient550/hol/projection_quotient550.ml *)
  l4_nth_error550;
  l4_skip550;
  l4_core_reduce_projection_with550;
  l4_core_reduce_projection550;
  l4_core_reduce_quotient550;
  (* /private/tmp/hol-projection-typing577/hol/projection_typing577.ml *)
  l4_projection_verify_prop577;
  l4_core_projection_field577;
  l4_core_infer_projection577;
  (* /private/tmp/hol-quotient-admission608/hol/quotient_admission608.ml *)
  l4_admit_quotient608;
  (* Current Rocq quotient-dependency parity repair839. *)
  l4_quotient_header_matches839;
  l4_quotient_dependency839;
  l4_quotient_dependencies839;
  (* /private/tmp/hol-quotient-admission608/hol/quotient_terms608.ml *)
  l4_q_name608;
  l4_q_mk_name608;
  l4_q_lift_name608;
  l4_q_ind_name608;
  l4_q_eq_name608;
  l4_q_arrow608;
  l4_q_local608;
  l4_quotient_eq_type608;
  l4_quotient_eq_refl_type608;
  l4_quotient_check_eq608;
  l4_canonical_quotient608;
  (* /private/tmp/hol-recursor-composition560/hol/recursor_helpers560.ml *)
  l4_core_major_induct557;
  l4_core_project_fields557;
  l4_core_make_structure557;
  l4_core_find_rule557;
  (* /private/tmp/hol-recursor-construction522/hol/recursor_construction522.ml *)
  l4_recursive_value522;
  l4_build_rule522;
  l4_build_recursor522;
  l4_build_recursors522;
  l4_verify_recursors522;
  (* /private/tmp/hol-recursor-conversion585/hol/recursor_conversion585.ml *)
  l4_core_to_structure585;
  l4_core_to_constructor585;
  l4_core_reduce_recursor585;
  (* /private/tmp/hol-safety-admission624/hol/safety_admission624.ml *)
  l4_safety_eqb624;
  l4_checking_view624;
  l4_safety_environment624;
  l4_safety_kind624;
  l4_safe_name624;
  l4_check_value624;
  l4_restricted_constant624;
  l4_restricted_definition624;
  l4_admit_extended624;
  l4_mutual_name624;
  l4_check_mutual_headers624;
  l4_check_mutual_values624;
  l4_admit_mutual624;
  (* /private/tmp/hol-string-compose340/run-002/source-package/hol/syntax.ml *)
  l4_eval_level;
  l4_level_equiv;
  l4_lift;
  l4_subst;
  l4_inst;
  (* /private/tmp/hol-universe-decision555/hol/universe_decision555.ml *)
  l4_klevel_eval555;
  l4_kguard_insert555;
  l4_kconst_atom555;
  l4_kcombine_levels555;
  l4_knormalize_aux555;
  l4_knormalize_level555;
  l4_kguard_subset555;
  l4_ksublevel_le555;
  l4_ksublevels_le555;
  l4_klevel_le555;
  l4_klevel_equiv555;
  l4_klevels_equiv555;
  l4_kguard_holds555;
  l4_ksublevel_eval555;
  l4_ksublevels_eval555;
  l4_core_level_positive555;
  (* /private/tmp/hol-whnf-control594/hol/whnf_control594.ml *)
  l4_core_reduce_head594;
  l4_whnf_core_step594;
  l4_whnf_step594;
  l4_finish_whnf_unfold594;
  l4_whnf_round_step594;
  l4_whnf_loop594;
  (* /private/tmp/hol-file-driver642/hol/file_driver642.ml *)
  l4_file_rows642;
  l4_file_decl_names642;
  l4_file_all642;
  l4_file_requires_mutual642;
  l4_file_batch_members642;
  l4_file_schedule_rows642;
  l4_file_indices_unique642;
  l4_file_coverage642;
  l4_file_same_name_set642;
  l4_file_resolve_members642;
  l4_file_mutual_inputs642;
  l4_file_admit_single642;
  l4_file_check_batch642;
  l4_file_check_batches642;
  l4_check_file642;
  l4_file_accepts642;
  l4_file_axioms642;
];;

(* Explicit stock operational equations. Do not unfold raw numeric arithmetic,
   minimal bitsize, gcd specification, or raw _MATCH/choice definitions. *)
let l4_kernel_stock_equations647 : thm list = [
  LET_END_DEF;
  FST; SND; PAIR_EQ;
  HD; TL; APPEND; REVERSE; LENGTH; MAP; NULL;
  ALL; EX; ITLIST; MEM; ALL2_DEF; EL; FILTER;
  CONS_11; option_INJ
];;

(* All these functions derive facts from actual datatype recursion theorems.
   No string lookup into distinctness/injectivity stores is used. *)
let l4_kernel_injectivity647 : thm list = [
  prove_constructors_injective l4_kind_checked_RECURSION516;
  prove_constructors_injective l4_kind_stats_RECURSION516;
  prove_constructors_injective l4_kind_motive_RECURSION516;
  prove_constructors_injective l4_kind_recursive_arg_RECURSION516;
  prove_constructors_injective l4_kind_minor_RECURSION516;
  prove_constructors_injective l4_conversion_progress_RECURSION597;
  prove_constructors_injective l4_kcontext_RECURSION532;
  prove_constructors_injective l4_kmethods_RECURSION543;
  prove_constructors_injective l4_whnf_round_RECURSION543;
  prove_constructors_injective l4_kinductive_data_RECURSION493;
  prove_constructors_injective l4_kconstructor_data_RECURSION493;
  prove_constructors_injective l4_krecursor_rule_RECURSION493;
  prove_constructors_injective l4_krecursor_data_RECURSION493;
  prove_constructors_injective l4_kdecl_kind_RECURSION493;
  prove_constructors_injective l4_khints_RECURSION493;
  prove_constructors_injective l4_kdeclaration_RECURSION493;
  prove_constructors_injective l4_kind_spec_RECURSION493;
  prove_constructors_injective l4_klocal_RECURSION489;
  prove_constructors_injective l4_klevel_RECURSION447;
  prove_constructors_injective l4_kexpr_RECURSION447;
  prove_constructors_injective l4_na_result_RECURSION437;
  prove_constructors_injective l4_knested_work_RECURSION494;
  prove_constructors_injective l4_knested_elimination_RECURSION499;
  prove_constructors_injective l4_kresult_RECURSION491;
  prove_constructors_injective l4_kbinding_RECURSION491;
  prove_constructors_injective l4_kstate_RECURSION491;
  prove_constructors_injective l4_prefix_result_RECURSION420;
  prove_constructors_injective l4_input_decl_RECURSION607;
  prove_constructors_injective l4_primitive_equation_RECURSION619;
  prove_constructors_injective l4_primitive_probe_RECURSION622;
  prove_constructors_injective l4_primitive_reflection_RECURSION621;
  prove_constructors_injective l4_name_RECURSION;
  prove_constructors_injective l4_level_RECURSION;
  prove_constructors_injective l4_expr_RECURSION;
  prove_constructors_injective l4_ksublevel_RECURSION555;
  prove_constructors_injective l4_file_decl_RECURSION642;
  prove_constructors_injective l4_file_batch_RECURSION642;
  prove_constructors_injective l4_file_input_RECURSION642;
];;

let l4_kernel_distinctness647 : thm list = [
  NOT_CONS_NIL;
  option_DISTINCT;
  prove_constructors_distinct l4_conversion_progress_RECURSION597;
  prove_constructors_distinct l4_reduction_mode_RECURSION543;
  prove_constructors_distinct l4_whnf_round_RECURSION543;
  prove_constructors_distinct l4_kprimitive_RECURSION493;
  prove_constructors_distinct l4_kquotient_RECURSION493;
  prove_constructors_distinct l4_kdecl_kind_RECURSION493;
  prove_constructors_distinct l4_khints_RECURSION493;
  prove_constructors_distinct l4_kbinder_RECURSION447;
  prove_constructors_distinct l4_klevel_RECURSION447;
  prove_constructors_distinct l4_kexpr_RECURSION447;
  prove_constructors_distinct l4_na_result_RECURSION437;
  prove_constructors_distinct l4_kreject_RECURSION491;
  prove_constructors_distinct l4_kdecline_RECURSION491;
  prove_constructors_distinct l4_kresult_RECURSION491;
  prove_constructors_distinct l4_prefix_result_RECURSION420;
  prove_constructors_distinct l4_input_safety_RECURSION607;
  prove_constructors_distinct l4_input_decl_RECURSION607;
  prove_constructors_distinct l4_primitive_condition_RECURSION621;
  prove_constructors_distinct l4_name_RECURSION;
  prove_constructors_distinct l4_level_RECURSION;
  prove_constructors_distinct l4_expr_RECURSION;
  prove_constructors_distinct l4_ksublevel_RECURSION555;
  prove_constructors_distinct l4_file_decl_RECURSION642;
  prove_constructors_distinct l4_file_batch_RECURSION642;
];;

let rec l4_registry_clauses647 th =
  if is_forall (concl th) then l4_registry_clauses647 (SPEC_ALL th)
  else if is_conj (concl th) then
    l4_registry_clauses647 (CONJUNCT1 th) @
    l4_registry_clauses647 (CONJUNCT2 th)
  else [th];;

(* Compute's first-order matcher does not reverse a constructor inequality.
   Derive BOTH orientations; never install equality symmetry as a rewrite. *)
let l4_registry_distinct_equations647 th =
  List.concat (List.map (fun clause ->
    if hyp clause <> [] || not (is_neg (concl clause)) then
      failwith "647: expected a closed constructor distinctness theorem";
    let equation = EQF_INTRO clause in
    [equation; CONV_RULE (LAND_CONV SYM_CONV) equation])
    (l4_registry_clauses647 th));;

let l4_kernel_constructor_equations647 : thm list =
  l4_kernel_injectivity647 @
  List.concat
    (List.map l4_registry_distinct_equations647 l4_kernel_distinctness647);;

let l4_kernel_equations647 : thm list =
  l4_kernel_project_equations647 @ l4_kernel_stock_equations647 @
  l4_kernel_constructor_equations647;;

(* These stock conversions construct and check HOL equations; numeric host
   proposals alone are not returned as verdicts. Parent646 must install them
   explicitly in its LOCAL compset. No attachment is installed here. *)
let l4_kernel_conversions647 : (term * int * conv) list = [
  (`bitsize:num->num`,1,BITSIZE_CONV);
  (`gcd:num#num->num`,1,GCD_CONV)
];;
