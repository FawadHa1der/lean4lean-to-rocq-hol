(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed component properties, all UNCOMPILED. No global soundness claim. *)
(* Successor562: GSYM ALL_MEM repair only; all 30 scripts remain UNCOMPILED. *)
needs "hol/universe_decision555.ml";;

let l4_guard_insert_present555 = prove
 (`!n path. l4_name_mem437 n path ==> l4_kguard_insert555 n path = path`,
  SIMP_TAC [l4_kguard_insert555]);;
let l4_guard_insert_absent555 = prove
 (`!n path. ~l4_name_mem437 n path ==> l4_kguard_insert555 n path = CONS n path`,
  SIMP_TAC [l4_kguard_insert555]);;
let l4_guard_insert_contains555 = prove
 (`!n path. l4_name_mem437 n (l4_kguard_insert555 n path)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_kguard_insert555;l4_name_mem437] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC [MEM]);;
let l4_guard_subset_sound555 = prove
 (`!rho xs ys. l4_kguard_subset555 xs ys /\ l4_kguard_holds555 rho ys ==>
   l4_kguard_holds555 rho xs`,
  REWRITE_TAC [l4_kguard_subset555;l4_kguard_holds555;l4_name_mem437;GSYM ALL_MEM] THEN
  MESON_TAC []);;
let l4_const_atom_zero555 = prove
 (`!path. l4_kconst_atom555 path 0 = []`, REWRITE_TAC [l4_kconst_atom555]);;
let l4_const_atom_positive555 = prove
 (`!path k. l4_kconst_atom555 path (SUC k) = [L4KSubConst555 path (SUC k)]`,
  REWRITE_TAC [l4_kconst_atom555;NOT_SUC]);;
let l4_combine_accepted555 = prove
 (`!xs ys. l4_kcombine_levels555 (L4KAccept491 xs) (L4KAccept491 ys) =
   L4KAccept491 (APPEND xs ys)`,
  REWRITE_TAC [l4_kcombine_levels555;l4_kr_bind491]);;
let l4_combine_first_reject555 = prove
 (`!reason other. l4_kcombine_levels555 (L4KReject491 reason) other =
   L4KReject491 reason`, REWRITE_TAC [l4_kcombine_levels555;l4_kr_bind491]);;
let l4_combine_first_decline555 = prove
 (`!reason other. l4_kcombine_levels555 (L4KDecline491 reason) other =
   L4KDecline491 reason`, REWRITE_TAC [l4_kcombine_levels555;l4_kr_bind491]);;
let l4_raw_normalize_zero_fuel555 = prove
 (`!u path k. l4_knormalize_aux555 0 u path k = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_knormalize_aux555]);;
let l4_raw_normalize_meta555 = prove
 (`!fuel n path k. l4_knormalize_aux555 (SUC fuel) (L4KLevelMVar447 n) path k =
   L4KReject491 L4KMetaVariable491`, REWRITE_TAC [l4_knormalize_aux555]);;
let l4_normalize_meta_priority555 = prove
 (`!fuel u. l4_klevel_meta447 u ==>
   l4_knormalize_level555 fuel u = L4KReject491 L4KMetaVariable491`,
  SIMP_TAC [l4_knormalize_level555]);;
let l4_normalize_metafree_zero_fuel555 = prove
 (`!u. ~l4_klevel_meta447 u ==>
   l4_knormalize_level555 0 u = L4KDecline491 L4KOutOfFuel491`,
  SIMP_TAC [l4_knormalize_level555;l4_knormalize_aux555]);;
let l4_raw_imax_zero555 = prove
 (`!fuel u path k. l4_knormalize_aux555 (SUC fuel) (L4KIMax447 u L4KZero447) path k =
   L4KAccept491 (l4_kconst_atom555 path k)`, REWRITE_TAC [l4_knormalize_aux555]);;
let l4_raw_imax_parameter555 = prove
 (`!fuel u n path k.
   l4_knormalize_aux555 (SUC fuel) (L4KIMax447 u (L4KParam447 n)) path k =
   l4_kr_bind491 (l4_knormalize_aux555 fuel u (l4_kguard_insert555 n path) k)
     (\xs. L4KAccept491 (APPEND (l4_kconst_atom555 path k)
       (CONS (L4KSubVar555 (l4_kguard_insert555 n path) n k) xs)))`,
  REWRITE_TAC [l4_knormalize_aux555;LET_DEF;LET_END_DEF]);;
let l4_equiv_first_reject555 = prove
 (`!fuel u v reason. l4_knormalize_level555 fuel u = L4KReject491 reason ==>
   l4_klevel_equiv555 fuel u v = L4KReject491 reason`,
  SIMP_TAC [l4_klevel_equiv555;l4_kr_bind491]);;
let l4_equiv_first_decline555 = prove
 (`!fuel u v reason. l4_knormalize_level555 fuel u = L4KDecline491 reason ==>
   l4_klevel_equiv555 fuel u v = L4KDecline491 reason`,
  SIMP_TAC [l4_klevel_equiv555;l4_kr_bind491]);;
let l4_le_first_reject555 = prove
 (`!fuel u v reason. l4_knormalize_level555 fuel u = L4KReject491 reason ==>
   l4_klevel_le555 fuel u v = L4KReject491 reason`,
  SIMP_TAC [l4_klevel_le555;l4_kr_bind491]);;
let l4_le_first_decline555 = prove
 (`!fuel u v reason. l4_knormalize_level555 fuel u = L4KDecline491 reason ==>
   l4_klevel_le555 fuel u v = L4KDecline491 reason`,
  SIMP_TAC [l4_klevel_le555;l4_kr_bind491]);;
let l4_levels_nil555 = prove
 (`!fuel. l4_klevels_equiv555 [] fuel [] = L4KAccept491 T`,
  REWRITE_TAC [l4_klevels_equiv555]);;
let l4_levels_left_nil555 = prove
 (`!fuel v vs. l4_klevels_equiv555 [] fuel (CONS v vs) = L4KAccept491 F`,
  REWRITE_TAC [l4_klevels_equiv555;NOT_CONS_NIL]);;
let l4_levels_right_nil555 = prove
 (`!fuel u us. l4_klevels_equiv555 (CONS u us) fuel [] = L4KAccept491 F`,
  REWRITE_TAC [l4_klevels_equiv555;NULL]);;
let l4_levels_false_shortcut555 = prove
 (`!fuel u us v vs. l4_klevel_equiv555 fuel u v = L4KAccept491 F ==>
   l4_klevels_equiv555 (CONS u us) fuel (CONS v vs) = L4KAccept491 F`,
  SIMP_TAC [l4_klevels_equiv555;NULL;HD;TL;l4_kr_bind491]);;
let l4_levels_true_continue555 = prove
 (`!fuel u us v vs. l4_klevel_equiv555 fuel u v = L4KAccept491 T ==>
   l4_klevels_equiv555 (CONS u us) fuel (CONS v vs) = l4_klevels_equiv555 us fuel vs`,
  SIMP_TAC [l4_klevels_equiv555;NULL;HD;TL;l4_kr_bind491]);;
let l4_levels_first_reject555 = prove
 (`!fuel u us v vs reason. l4_klevel_equiv555 fuel u v = L4KReject491 reason ==>
   l4_klevels_equiv555 (CONS u us) fuel (CONS v vs) = L4KReject491 reason`,
  SIMP_TAC [l4_klevels_equiv555;NULL;HD;TL;l4_kr_bind491]);;
let l4_levels_first_decline555 = prove
 (`!fuel u us v vs reason. l4_klevel_equiv555 fuel u v = L4KDecline491 reason ==>
   l4_klevels_equiv555 (CONS u us) fuel (CONS v vs) = L4KDecline491 reason`,
  SIMP_TAC [l4_klevels_equiv555;NULL;HD;TL;l4_kr_bind491]);;
let l4_sublevel_variable_to_constant555 = prove
 (`!p n k q j. ~l4_ksublevel_le555 (L4KSubVar555 p n k) (L4KSubConst555 q j)`,
  REWRITE_TAC [l4_ksublevel_le555]);;
let l4_sublevel_constant_variable_guard555 = prove
 (`!p k q n j. ~l4_name_mem437 n q ==>
   ~l4_ksublevel_le555 (L4KSubConst555 p k) (L4KSubVar555 q n j)`,
  SIMP_TAC [l4_ksublevel_le555]);;
let l4_positive_imax_right555 = prove
 (`!u v. l4_core_level_positive555 (L4KIMax447 u v) <=> l4_core_level_positive555 v`,
  REWRITE_TAC [l4_core_level_positive555]);;
let l4_parameter_not_definitely_positive555 = prove
 (`!n. ~l4_core_level_positive555 (L4KParam447 n)`,
  REWRITE_TAC [l4_core_level_positive555]);;
