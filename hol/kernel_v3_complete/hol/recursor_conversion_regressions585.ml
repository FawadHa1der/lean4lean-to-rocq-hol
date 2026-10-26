(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Focused literal/conditional regressions. ALL SCRIPTS UNCOMPILED / NOT RUN.
   These are proposed HOL equations, not synthetic native evidence. *)
needs "hol/recursor_conversion_properties585.ml";;

let l4_reg_rule_argument_order585 = prove
 (`!p m minor idx major tail cp f0 f1:l4_kexpr447.
   APPEND (l4_kfirstn494 [p;m;minor;idx;major;tail] 3)
     (APPEND (l4_skip550 [cp;f0;f1] 1)
       (l4_skip550 [p;m;minor;idx;major;tail] 5)) =
   [p;m;minor;f0;f1;tail]`,
  REWRITE_TAC [l4_kfirstn494;l4_skip550] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [APPEND]);;
let l4_reg_rule_universe_substitution585 = prove
 (`!u:l4_klevel447.
   l4_ksubst_levels488 [L4Anonymous] [u]
     (L4KApp447 (L4KConst447 (L4Numeric L4Anonymous 9) [L4KParam447 L4Anonymous])
       (L4KSort447 (L4KParam447 L4Anonymous))) =
   L4KApp447 (L4KConst447 (L4Numeric L4Anonymous 9) [u]) (L4KSort447 u)`,
  REWRITE_TAC [l4_ksubst_levels488;l4_ksubst_level488;l4_klookup_level488;
    MAP;NULL;HD]);;
let l4_reg_nat_zero585 = prove
 (`l4_core_nat_constructor544 0 = L4KConst447 l4_core_zero_name533 []`,
  REWRITE_TAC [l4_core_nat_constructor544]);;
let l4_reg_nat_successor585 = prove
 (`!n. l4_core_nat_constructor544 (SUC n) =
   L4KApp447 (L4KConst447 l4_core_succ_name533 []) (L4KNatLit447 n)`,
  REWRITE_TAC [l4_core_nat_constructor544;NOT_SUC;ARITH_RULE `SUC n - 1 = n`]);;
let l4_reg_string_invalid_before_whnf585 = prove
 (`!rec fuel env g owner k value.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KStrLit447 [192;128]) ==>
   l4_core_to_constructor585 rec fuel env g owner k value =
     L4KReject491 L4KMalformedDeclaration491`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [l4_core_to_constructor585;l4_kr_bind491;
    l4_core_expand_string539;l4_core_utf8_539] THEN
  ONCE_REWRITE_TAC [l4_core_utf8_scan539] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [l4_kr_bind491]);;
let l4_reg_string_empty_no_readiness_gate585 = prove
 (`!rec fuel env g owner k value.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KStrLit447 []) ==>
   l4_core_to_constructor585 rec fuel env g owner k value =
     l4_whnf_method543 rec g
       (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) (l4_core_char_list539 []))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [l4_core_to_constructor585;l4_kr_bind491;
    l4_core_expand_string539;l4_core_utf8_539;l4_core_utf8_scan539] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [l4_kr_bind491]);;
let l4_reg_constructor_bypasses_k_fuel585 = prove
 (`!rec env g owner value cn us ci.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KConst447 cn us) /\
   l4_core_constructor532 env cn = SOME ci ==>
   l4_core_to_constructor585 rec 0 env g owner T value = L4KAccept491 (L4KConst447 cn us)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [l4_core_to_constructor585;l4_kr_bind491;l4_ksplit_app489;l4_ksplit_app_aux489;FST]);;
let l4_reg_nonrecursor_literal585 = prove
 (`!rec fuel env g n.
   l4_core_reduce_recursor585 rec fuel env g (L4KNatLit447 n) = L4KAccept491 NONE`,
  REWRITE_TAC [l4_core_reduce_recursor585;l4_ksplit_app489;l4_ksplit_app_aux489;
    LET_DEF;LET_END_DEF;FST;SND]);;
let l4_reg_missing_major_no_type_scan585 = prove
 (`!rec fuel env g n us d info.
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDRecursor493 info ==>
   l4_core_reduce_recursor585 rec fuel env g (L4KConst447 n us) = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_reduce_recursor585;l4_ksplit_app489;l4_ksplit_app_aux489;
    LET_DEF;LET_END_DEF;FST;SND;l4_nth_error550]);;
let l4_reg_k_meta_before_fuel585 = prove
 (`!u. l4_klevel_meta447 u ==>
   l4_klevel_equiv555 0 u L4KZero447 = L4KReject491 L4KMetaVariable491`,
  SIMP_TAC [l4_klevel_equiv555;l4_knormalize_level555;l4_kr_bind491]);;
let l4_reg_k_zero_fuel_declines585 = prove
 (`l4_klevel_equiv555 0 L4KZero447 L4KZero447 = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_klevel_equiv555;l4_knormalize_level555;l4_klevel_meta447;
    l4_knormalize_aux555;l4_kr_bind491]);;
let l4_reg_eta_parameter_not_positive585 = prove
 (`!n. ~l4_core_level_positive555 (L4KParam447 n)`,
  REWRITE_TAC [l4_core_level_positive555]);;
