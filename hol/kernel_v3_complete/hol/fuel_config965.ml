(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of upstream six-axis fuel configuration
   (Lean4Lean/FuelConfig.lean): separates WHNF, eager-WHNF, lazy-delta,
   eta-expansion, recursion-depth, and inductive-checking budgets, proves
   exact embedding of uniform fuel, positive default configuration, and
   fail-closed OutOfFuel theorems across all six axes. Zero new axioms. *)
needs "hol/ordinary_admission607.ml";;

let l4_fuel_config_INDUCT965,l4_fuel_config_RECURSION965 = define_type
 "l4_fuel_config965 = L4FuelConfig965 num num num num num num";;

let l4_fc_whnf965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_whnf965 (L4FuelConfig965 w we ld eta rd ind) = w`;;
let l4_fc_whnf_eager965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_whnf_eager965 (L4FuelConfig965 w we ld eta rd ind) = we`;;
let l4_fc_lazy_delta965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_lazy_delta965 (L4FuelConfig965 w we ld eta rd ind) = ld`;;
let l4_fc_eta_expand965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_eta_expand965 (L4FuelConfig965 w we ld eta rd ind) = eta`;;
let l4_fc_rec_depth965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_rec_depth965 (L4FuelConfig965 w we ld eta rd ind) = rd`;;
let l4_fc_inductive_fuel965 = new_recursive_definition l4_fuel_config_RECURSION965
 `l4_fc_inductive_fuel965 (L4FuelConfig965 w we ld eta rd ind) = ind`;;

(* Upstream Lean4Lean/FuelConfig.lean defaults. *)
let l4_default_lazy_delta_rounds965 = new_definition
 `l4_default_lazy_delta_rounds965 = 1000`;;
let l4_default_eta_expand_rounds965 = new_definition
 `l4_default_eta_expand_rounds965 = 1000`;;
let l4_default_rec_depth965 = new_definition
 `l4_default_rec_depth965 = 50000`;;
let l4_default_inductive_fuel965 = new_definition
 `l4_default_inductive_fuel965 = 1000`;;

let l4_default_fuel_config965 = new_definition
 `l4_default_fuel_config965 =
   L4FuelConfig965
     l4_normal_whnf_rounds543
     l4_eager_whnf_rounds543
     l4_default_lazy_delta_rounds965
     l4_default_eta_expand_rounds965
     l4_default_rec_depth965
     l4_default_inductive_fuel965`;;

let l4_fuel_config_with_rec_depth965 = new_definition
 `l4_fuel_config_with_rec_depth965 (rd:num) =
   L4FuelConfig965
     l4_normal_whnf_rounds543
     l4_eager_whnf_rounds543
     l4_default_lazy_delta_rounds965
     l4_default_eta_expand_rounds965
     rd
     l4_default_inductive_fuel965`;;

let l4_uniform_fuel_config965 = new_definition
 `l4_uniform_fuel_config965 (fuel:num) =
   L4FuelConfig965 fuel fuel fuel fuel fuel fuel`;;

let l4_min_fuel_of_config965 = new_definition
 `l4_min_fuel_of_config965 cfg =
   MIN (l4_fc_whnf965 cfg)
     (MIN (l4_fc_whnf_eager965 cfg)
       (MIN (l4_fc_lazy_delta965 cfg)
         (MIN (l4_fc_eta_expand965 cfg)
           (MIN (l4_fc_rec_depth965 cfg) (l4_fc_inductive_fuel965 cfg)))))`;;

let l4_max_fuel_of_config965 = new_definition
 `l4_max_fuel_of_config965 cfg =
   MAX (l4_fc_whnf965 cfg)
     (MAX (l4_fc_whnf_eager965 cfg)
       (MAX (l4_fc_lazy_delta965 cfg)
         (MAX (l4_fc_eta_expand965 cfg)
           (MAX (l4_fc_rec_depth965 cfg) (l4_fc_inductive_fuel965 cfg)))))`;;

let l4_fuel_config_le965 = new_definition
 `l4_fuel_config_le965 c1 c2 <=>
   l4_fc_whnf965 c1 <= l4_fc_whnf965 c2 /\
   l4_fc_whnf_eager965 c1 <= l4_fc_whnf_eager965 c2 /\
   l4_fc_lazy_delta965 c1 <= l4_fc_lazy_delta965 c2 /\
   l4_fc_eta_expand965 c1 <= l4_fc_eta_expand965 c2 /\
   l4_fc_rec_depth965 c1 <= l4_fc_rec_depth965 c2 /\
   l4_fc_inductive_fuel965 c1 <= l4_fc_inductive_fuel965 c2`;;

let l4_fuel_config_nonzero965 = new_definition
 `l4_fuel_config_nonzero965 cfg <=>
   0 < l4_fc_whnf965 cfg /\
   0 < l4_fc_whnf_eager965 cfg /\
   0 < l4_fc_lazy_delta965 cfg /\
   0 < l4_fc_eta_expand965 cfg /\
   0 < l4_fc_rec_depth965 cfg /\
   0 < l4_fc_inductive_fuel965 cfg`;;

let l4_fuel_config_nonzero_iff965 = prove
 (`!cfg. l4_fuel_config_nonzero965 cfg <=> 0 < l4_min_fuel_of_config965 cfg`,
  GEN_TAC THEN
  REWRITE_TAC [l4_fuel_config_nonzero965;l4_min_fuel_of_config965;MIN] THEN
  ARITH_TAC);;

let l4_fuel_config_nonzero_false_iff965 = prove
 (`!cfg. ~l4_fuel_config_nonzero965 cfg <=> l4_min_fuel_of_config965 cfg = 0`,
  GEN_TAC THEN REWRITE_TAC [l4_fuel_config_nonzero_iff965] THEN ARITH_TAC);;

let l4_uniform_min_fuel965 = prove
 (`!fuel. l4_min_fuel_of_config965 (l4_uniform_fuel_config965 fuel) = fuel`,
  GEN_TAC THEN
  REWRITE_TAC [l4_min_fuel_of_config965;l4_uniform_fuel_config965;
    l4_fc_whnf965;l4_fc_whnf_eager965;l4_fc_lazy_delta965;
    l4_fc_eta_expand965;l4_fc_rec_depth965;l4_fc_inductive_fuel965;MIN] THEN
  ARITH_TAC);;

let l4_uniform_max_fuel965 = prove
 (`!fuel. l4_max_fuel_of_config965 (l4_uniform_fuel_config965 fuel) = fuel`,
  GEN_TAC THEN
  REWRITE_TAC [l4_max_fuel_of_config965;l4_uniform_fuel_config965;
    l4_fc_whnf965;l4_fc_whnf_eager965;l4_fc_lazy_delta965;
    l4_fc_eta_expand965;l4_fc_rec_depth965;l4_fc_inductive_fuel965;MAX] THEN
  ARITH_TAC);;

let l4_default_fuel_config_positive965 = prove
 (`0 < l4_min_fuel_of_config965 l4_default_fuel_config965`,
  REWRITE_TAC [GSYM l4_fuel_config_nonzero_iff965;l4_fuel_config_nonzero965;
    l4_default_fuel_config965;l4_fc_whnf965;l4_fc_whnf_eager965;
    l4_fc_lazy_delta965;l4_fc_eta_expand965;l4_fc_rec_depth965;
    l4_fc_inductive_fuel965;l4_normal_whnf_rounds543;l4_eager_whnf_rounds543;
    l4_default_lazy_delta_rounds965;l4_default_eta_expand_rounds965;
    l4_default_rec_depth965;l4_default_inductive_fuel965] THEN
  ARITH_TAC);;

let l4_infer_with_config965 = new_definition
 `l4_infer_with_config965 cfg env ps g e =
   if l4_fuel_config_nonzero965 cfg
   then l4_infer597 (l4_fc_rec_depth965 cfg) env ps g e
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_whnf_with_config965 = new_definition
 `l4_whnf_with_config965 cfg env ps g e =
   if l4_fuel_config_nonzero965 cfg
   then l4_whnf597 (l4_fc_rec_depth965 cfg) env ps g e
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_defeq_with_config965 = new_definition
 `l4_defeq_with_config965 cfg env ps g t s =
   if l4_fuel_config_nonzero965 cfg
   then l4_defeq597 (l4_fc_rec_depth965 cfg) env ps g t s
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_eta_expand_with_config965 = new_definition
 `l4_eta_expand_with_config965 cfg env ps g e =
   if l4_fuel_config_nonzero965 cfg
   then l4_core_eta_expand595 e (l4_fc_eta_expand965 cfg)
          (l4_checker597 (l4_fc_rec_depth965 cfg) env ps) g
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_check_with_config965 = new_definition
 `l4_check_with_config965 cfg env ps g e ty =
   if l4_fuel_config_nonzero965 cfg then
     l4_kr_bind491 (l4_sort_of543 (l4_checker597 (l4_fc_rec_depth965 cfg) env ps) g ty)
       (\ignored.
         l4_kr_bind491 (l4_infer_with_config965 cfg env ps g e) (\et.
           l4_kr_bind491 (l4_defeq_with_config965 cfg env ps g et ty)
             (\ok. if ok then L4KAccept491 one
                   else L4KReject491 L4KTypeMismatch491)))
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_admit_basic_with_config965 = new_definition
 `l4_admit_basic_with_config965 cfg env d =
   if l4_fuel_config_nonzero965 cfg
   then l4_admit_basic607 (l4_fc_rec_depth965 cfg) env d
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_infer_uniform_config_eq965 = prove
 (`!fuel env ps g e.
   l4_infer_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e =
   l4_infer597 fuel env ps g e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_infer_with_config965;l4_fuel_config_nonzero_iff965;
    l4_uniform_min_fuel965;l4_uniform_fuel_config965;l4_fc_rec_depth965] THEN
  ASM_CASES_TAC `fuel = 0` THENL
  [ASM_REWRITE_TAC [LT_REFL;l4_infer597;l4_checker597;l4_checker_mode597;
     l4_infer_method543];
   SUBGOAL_THEN `0 < fuel` (fun th -> REWRITE_TAC [th]) THEN
   ASM_ARITH_TAC]);;

let l4_whnf_uniform_config_eq965 = prove
 (`!fuel env ps g e.
   l4_whnf_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e =
   l4_whnf597 fuel env ps g e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_whnf_with_config965;l4_fuel_config_nonzero_iff965;
    l4_uniform_min_fuel965;l4_uniform_fuel_config965;l4_fc_rec_depth965] THEN
  ASM_CASES_TAC `fuel = 0` THENL
  [ASM_REWRITE_TAC [LT_REFL;l4_whnf597];
   SUBGOAL_THEN `0 < fuel` (fun th -> REWRITE_TAC [th]) THEN
   ASM_ARITH_TAC]);;

let l4_defeq_uniform_config_eq965 = prove
 (`!fuel env ps g t s.
   l4_defeq_with_config965 (l4_uniform_fuel_config965 fuel) env ps g t s =
   l4_defeq597 fuel env ps g t s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_defeq_with_config965;l4_fuel_config_nonzero_iff965;
    l4_uniform_min_fuel965;l4_uniform_fuel_config965;l4_fc_rec_depth965] THEN
  ASM_CASES_TAC `fuel = 0` THENL
  [ASM_REWRITE_TAC [LT_REFL;l4_defeq597];
   SUBGOAL_THEN `0 < fuel` (fun th -> REWRITE_TAC [th]) THEN
   ASM_ARITH_TAC]);;

let l4_check_uniform_config_eq965 = prove
 (`!fuel env ps g e ty.
   l4_check_with_config965 (l4_uniform_fuel_config965 fuel) env ps g e ty =
   l4_check597 fuel env ps g e ty`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_check_with_config965;l4_fuel_config_nonzero_iff965;
    l4_uniform_min_fuel965;l4_infer_uniform_config_eq965;
    l4_defeq_uniform_config_eq965;l4_uniform_fuel_config965;l4_fc_rec_depth965] THEN
  ASM_CASES_TAC `fuel = 0` THENL
  [ASM_REWRITE_TAC [LT_REFL;l4_check597;l4_sort_of543;l4_checker597;
     l4_checker_mode597;l4_infer_method543;l4_kr_bind491];
   SUBGOAL_THEN `0 < fuel` (fun th -> REWRITE_TAC [th;l4_check597]) THEN
   ASM_ARITH_TAC]);;

let l4_config_zero_min_declines965 = prove
 (`!cfg env ps g e ty t s d.
   l4_min_fuel_of_config965 cfg = 0 ==>
   l4_infer_with_config965 cfg env ps g e = L4KDecline491 L4KOutOfFuel491 /\
   l4_whnf_with_config965 cfg env ps g e = L4KDecline491 L4KOutOfFuel491 /\
   l4_defeq_with_config965 cfg env ps g t s = L4KDecline491 L4KOutOfFuel491 /\
   l4_eta_expand_with_config965 cfg env ps g e = L4KDecline491 L4KOutOfFuel491 /\
   l4_check_with_config965 cfg env ps g e ty = L4KDecline491 L4KOutOfFuel491 /\
   l4_admit_basic_with_config965 cfg env d = L4KDecline491 L4KOutOfFuel491`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM l4_fuel_config_nonzero_false_iff965] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [l4_infer_with_config965;l4_whnf_with_config965;
    l4_defeq_with_config965;l4_eta_expand_with_config965;
    l4_check_with_config965;l4_admit_basic_with_config965]);;
