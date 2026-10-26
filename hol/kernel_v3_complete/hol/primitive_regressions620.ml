(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed source regressions. UNCOMPILED / NOT RUN; no model results. *)
needs "hol/primitive_properties620.ml";;

let l4_primitive_equations_empty620 = prove
 (`!steps fuel env. l4_primitive_check_equations620 [] steps fuel env = L4KAccept491 one`,
  REWRITE_TAC [l4_primitive_check_equations620]);;

let l4_primitive_equations_zero_steps620 = prove
 (`!e es fuel env. l4_primitive_check_equations620 (CONS e es) 0 fuel env =
   L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_check_equations620]);;

let l4_primitive_equations_zero_kernel_fuel620 = prove
 (`!e es steps env. ~(steps = 0) ==>
   l4_primitive_check_equations620 (CONS e es) steps 0 env = L4KDecline491 L4KOutOfFuel491`,
  SIMP_TAC [l4_primitive_check_equations620;l4_check_defeq597;l4_infer597;
    l4_checker597;l4_checker_mode597;l4_infer_method543;l4_kr_bind491]);;

let l4_primitive_ensure_type_zero_fuel620 = prove
 (`!env e. l4_primitive_ensure_type620 0 env e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_ensure_type620;l4_sort_of543;l4_checker597;
    l4_checker_mode597;l4_infer_method543;l4_kr_bind491]);;

let l4_primitive_text_flags620 = prove
 (`l4_primitive_is_text620 L4KPCharOfNat493 /\
   l4_primitive_is_text620 L4KPStringOfList493 /\
   ~l4_primitive_is_text620 L4KPNatAdd493 /\
   ~l4_primitive_is_text620 L4KPNatBitwise493`,
  REWRITE_TAC [l4_primitive_is_text620]);;

let l4_primitive_nontext_interface_is_not_admission620 = prove
 (`!env. l4_primitive_check_text_interface620 0 env L4KPNatAdd493 = L4KAccept491 one`,
  REWRITE_TAC [l4_primitive_check_text_interface620]);;

let l4_primitive_pred_equations620 = prove
 (`!body. l4_primitive_equations620 L4KPNatPred493 body = SOME
   [l4_primitive_equation_at619 l4_kempty_context532
      (L4KApp447 body l4_primitive_zero619) l4_primitive_zero619;
    l4_primitive_equation_at619 l4_primitive_x_context619
      (L4KApp447 body (l4_primitive_succ619 (L4KBVar447 0))) (L4KBVar447 0)]`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_add_body_recursion620 = prove
 (`!body. l4_primitive_equations620 L4KPNatAdd493 body = SOME
   [l4_primitive_equation_at619 l4_primitive_x_context619
      (l4_kapply_exprs489 [L4KBVar447 0;l4_primitive_zero619] body) (L4KBVar447 0);
    l4_primitive_equation_at619 l4_primitive_xy_context619
      (l4_kapply_exprs489 [L4KBVar447 1;l4_primitive_succ619 (L4KBVar447 0)] body)
      (l4_primitive_succ619 (l4_kapply_exprs489 [L4KBVar447 1;L4KBVar447 0] body))]`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_shift_left_step620 = prove
 (`!body. l4_primitive_equations620 L4KPNatShiftLeft493 body = SOME
   [l4_primitive_equation_at619 l4_primitive_x_context619
      (l4_kapply_exprs489 [L4KBVar447 0;l4_primitive_zero619] body) (L4KBVar447 0);
    l4_primitive_equation_at619 l4_primitive_xy_context619
      (l4_kapply_exprs489 [L4KBVar447 1;l4_primitive_succ619 (L4KBVar447 0)] body)
      (l4_kapply_exprs489
        [l4_primitive_call619 L4KPNatMul493 [l4_primitive_two619;L4KBVar447 1];L4KBVar447 0]
        body)]`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_shift_right_step620 = prove
 (`!body. l4_primitive_equations620 L4KPNatShiftRight493 body = SOME
   [l4_primitive_equation_at619 l4_primitive_x_context619
      (l4_kapply_exprs489 [L4KBVar447 0;l4_primitive_zero619] body) (L4KBVar447 0);
    l4_primitive_equation_at619 l4_primitive_xy_context619
      (l4_kapply_exprs489 [L4KBVar447 1;l4_primitive_succ619 (L4KBVar447 0)] body)
      (l4_primitive_call619 L4KPNatDiv493
        [l4_kapply_exprs489 [L4KBVar447 1;L4KBVar447 0] body;l4_primitive_two619])]`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_specialized_equations_absent620 = prove
 (`!body.
   l4_primitive_equations620 L4KPNatMod493 body = NONE /\
   l4_primitive_equations620 L4KPNatDiv493 body = NONE /\
   l4_primitive_equations620 L4KPNatGcd493 body = NONE /\
   l4_primitive_equations620 L4KPNatBitwise493 body = NONE /\
   l4_primitive_equations620 L4KPNatLAnd493 body = NONE /\
   l4_primitive_equations620 L4KPNatLOr493 body = NONE /\
   l4_primitive_equations620 L4KPNatXor493 body = NONE`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_text_equations_absent620 = prove
 (`!body. l4_primitive_equations620 L4KPCharOfNat493 body = NONE /\
   l4_primitive_equations620 L4KPStringOfList493 body = NONE`,
  REWRITE_TAC [l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_mod_dispatch620 = prove
 (`!fuel env body. l4_primitive_check_nat_equations620 fuel env L4KPNatMod493 body =
   l4_primitive_check_fuel_rec621 fuel env T body`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_div_dispatch620 = prove
 (`!fuel env body. l4_primitive_check_nat_equations620 fuel env L4KPNatDiv493 body =
   l4_primitive_check_fuel_rec621 fuel env F body`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_gcd_dispatch620 = prove
 (`!fuel env body. l4_primitive_check_nat_equations620 fuel env L4KPNatGcd493 body =
   l4_primitive_check_gcd622 fuel env body`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_bitwise_dispatch620 = prove
 (`!fuel env body. l4_primitive_check_nat_equations620 fuel env L4KPNatBitwise493 body =
   l4_primitive_check_bitwise622 fuel env body`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_instances_dispatch620 = prove
 (`!fuel env body.
   l4_primitive_check_nat_equations620 fuel env L4KPNatLAnd493 body =
     l4_primitive_check_bitwise_instance622 fuel env L4KPNatLAnd493 body /\
   l4_primitive_check_nat_equations620 fuel env L4KPNatLOr493 body =
     l4_primitive_check_bitwise_instance622 fuel env L4KPNatLOr493 body /\
   l4_primitive_check_nat_equations620 fuel env L4KPNatXor493 body =
     l4_primitive_check_bitwise_instance622 fuel env L4KPNatXor493 body`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;

let l4_primitive_text_nat_dispatch_declines620 = prove
 (`!fuel env body.
   l4_primitive_check_nat_equations620 fuel env L4KPCharOfNat493 body =
     L4KDecline491 L4KUnsupportedDeclaration491 /\
   l4_primitive_check_nat_equations620 fuel env L4KPStringOfList493 body =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_primitive_check_nat_equations620;l4_primitive_equations620;LET_DEF;LET_END_DEF]);;
