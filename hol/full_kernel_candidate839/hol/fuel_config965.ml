(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of Lean4Lean/FuelConfig.lean: multi-axis fuel
   configuration separating WHNF, inference, definitional-equality, lazy-delta,
   and recursor budgets, with uniform embedding and fail-closed OutOfFuel
   theorems. Zero new axioms. *)
needs "hol/ordinary_admission607.ml";;

let l4_fuel_config_INDUCT965,l4_fuel_config_RECURSION965 = define_type
 "l4_fuel_config965 = L4FuelConfig965 num num num num num";;

let l4_fc_whnf965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_whnf965 (L4FuelConfig965 w i d dl r) = w`;;
let l4_fc_infer965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_infer965 (L4FuelConfig965 w i d dl r) = i`;;
let l4_fc_defeq965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_defeq965 (L4FuelConfig965 w i d dl r) = d`;;
let l4_fc_delta965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_delta965 (L4FuelConfig965 w i d dl r) = dl`;;
let l4_fc_recursor965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_recursor965 (L4FuelConfig965 w i d dl r) = r`;;

let l4_uniform_fuel_config965 = new_definition
 `l4_uniform_fuel_config965 (fuel:num) = L4FuelConfig965 fuel fuel fuel fuel fuel`;;

let l4_min_fuel_of_config965 = new_definition
 `l4_min_fuel_of_config965 cfg =
   MIN (l4_fc_whnf965 cfg)
     (MIN (l4_fc_infer965 cfg)
       (MIN (l4_fc_defeq965 cfg)
         (MIN (l4_fc_delta965 cfg) (l4_fc_recursor965 cfg))))`;;

let l4_infer_with_config965 = new_definition
 `l4_infer_with_config965 cfg env ps g e =
   if l4_min_fuel_of_config965 cfg = 0 then L4KDecline491 L4KOutOfFuel491
   else l4_infer597 (l4_fc_infer965 cfg) env ps g e`;;

let l4_whnf_with_config965 = new_definition
 `l4_whnf_with_config965 cfg env ps g e =
   if l4_min_fuel_of_config965 cfg = 0 then L4KDecline491 L4KOutOfFuel491
   else l4_whnf597 (l4_fc_whnf965 cfg) env ps g e`;;

let l4_defeq_with_config965 = new_definition
 `l4_defeq_with_config965 cfg env ps g t s =
   if l4_min_fuel_of_config965 cfg = 0 then L4KDecline491 L4KOutOfFuel491
   else l4_defeq597 (l4_fc_defeq965 cfg) env ps g t s`;;

let l4_check_with_config965 = new_definition
 `l4_check_with_config965 cfg env ps g e ty =
   if l4_min_fuel_of_config965 cfg = 0 then L4KDecline491 L4KOutOfFuel491
   else
     l4_kr_bind491 (l4_sort_of543 (l4_checker597 (l4_fc_infer965 cfg) env ps) g ty)
       (\ignored.
         l4_kr_bind491 (l4_infer_with_config965 cfg env ps g e) (\et.
           l4_kr_bind491 (l4_defeq_with_config965 cfg env ps g et ty)
             (\ok. if ok then L4KAccept491 one
                   else L4KReject491 L4KTypeMismatch491)))`;;

let l4_uniform_min_fuel965 = prove
 (`!fuel. l4_min_fuel_of_config965 (l4_uniform_fuel_config965 fuel) = fuel`,
  GEN_TAC THEN
  REWRITE_TAC [l4_min_fuel_of_config965;l4_uniform_fuel_config965;
    l4_fc_whnf965;l4_fc_infer965;l4_fc_defeq965;l4_fc_delta965;
    l4_fc_recursor965;MIN] THEN
  ARITH_TAC);;

let l4_infer_uniform_config_eq965 = prove
 (`!fuel env ps g e.
   l4_infer_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e =
   l4_infer597 fuel env ps g e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_infer_with_config965;l4_uniform_min_fuel965;
    l4_uniform_fuel_config965;l4_fc_infer965] THEN
  ASM_CASES_TAC `fuel = 0` THEN
  ASM_REWRITE_TAC [l4_infer597;l4_checker597;l4_checker_mode597;l4_infer_method543]);;

let l4_whnf_uniform_config_eq965 = prove
 (`!fuel env ps g e.
   l4_whnf_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e =
   l4_whnf597 fuel env ps g e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_whnf_with_config965;l4_uniform_min_fuel965;
    l4_uniform_fuel_config965;l4_fc_whnf965] THEN
  ASM_CASES_TAC `fuel = 0` THEN ASM_REWRITE_TAC [l4_whnf597]);;

let l4_defeq_uniform_config_eq965 = prove
 (`!fuel env ps g t s.
   l4_defeq_with_config965 (l4_uniform_fuel_config965 fuel) env ps g t s =
   l4_defeq597 fuel env ps g t s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_defeq_with_config965;l4_uniform_min_fuel965;
    l4_uniform_fuel_config965;l4_fc_defeq965] THEN
  ASM_CASES_TAC `fuel = 0` THEN ASM_REWRITE_TAC [l4_defeq597]);;

let l4_check_uniform_config_eq965 = prove
 (`!fuel env ps g e ty.
   l4_check_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e ty =
   l4_check597 fuel env ps g e ty`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_check_with_config965;l4_uniform_min_fuel965;
    l4_infer_uniform_config_eq965;l4_defeq_uniform_config_eq965] THEN
  REWRITE_TAC [l4_uniform_fuel_config965;l4_fc_infer965] THEN
  ASM_CASES_TAC `fuel = 0` THEN
  ASM_REWRITE_TAC [l4_check597;l4_sort_of543;l4_checker597;
    l4_checker_mode597;l4_infer_method543;l4_kr_bind491]);;

let l4_config_zero_min_declines965 = prove
 (`!cfg env ps g e ty t s.
   l4_min_fuel_of_config965 cfg = 0 ==>
   l4_infer_with_config965 cfg env ps g e = L4KDecline491 L4KOutOfFuel491 /\
   l4_whnf_with_config965 cfg env ps g e = L4KDecline491 L4KOutOfFuel491 /\
   l4_defeq_with_config965 cfg env ps g t s = L4KDecline491 L4KOutOfFuel491 /\
   l4_check_with_config965 cfg env ps g e ty = L4KDecline491 L4KOutOfFuel491`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [l4_infer_with_config965;l4_whnf_with_config965;
    l4_defeq_with_config965;l4_check_with_config965]);;
