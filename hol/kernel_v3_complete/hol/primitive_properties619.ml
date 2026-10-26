(* SPDX-License-Identifier: Apache-2.0. Proposed scripts, ALL UNCOMPILED. *)
needs "hol/primitive_foundations619.ml";;

let l4_primitive_kind_count619 = prove
 (`LENGTH l4_primitive_kinds619 = 18`,
  REWRITE_TAC [l4_primitive_kinds619;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
let l4_primitive_lookup_empty619 = prove
 (`!n. l4_primitive_lookup_in619 [] n = NONE`,
  REWRITE_TAC [l4_primitive_lookup_in619]);;
let l4_primitive_lookup_first619 = prove
 (`!op ops. l4_primitive_lookup_in619 (CONS op ops) (l4_primitive_name619 op) = SOME op`,
  REWRITE_TAC [l4_primitive_lookup_in619]);;
let l4_primitive_lookup_skip619 = prove
 (`!op ops n. ~(n = l4_primitive_name619 op) ==>
   l4_primitive_lookup_in619 (CONS op ops) n = l4_primitive_lookup_in619 ops n`,
  SIMP_TAC [l4_primitive_lookup_in619]);;
let l4_primitive_call_empty619 = prove
 (`!op. l4_primitive_call619 op [] = L4KConst447 (l4_primitive_name619 op) []`,
  REWRITE_TAC [l4_primitive_call619;l4_kapply_exprs489]);;
let l4_primitive_call_order619 = prove
 (`!op a b. l4_primitive_call619 op [a;b] =
   L4KApp447 (L4KApp447 (L4KConst447 (l4_primitive_name619 op) []) a) b`,
  REWRITE_TAC [l4_primitive_call619;l4_kapply_exprs489]);;
let l4_primitive_signature_no_fuel619 = prove
 (`!actual expected. l4_primitive_check_signature619 0 actual expected =
   L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_check_signature619]);;
let l4_primitive_signature_metadata619 = prove
 (`!fuel a e. l4_primitive_check_signature619 (SUC fuel) (L4KMData447 a) e =
   l4_primitive_check_signature619 fuel a e`,
  REWRITE_TAC [l4_primitive_check_signature619]);;
let l4_primitive_signature_pi619 = prove
 (`!fuel n bi a b m bj c d.
   l4_primitive_check_signature619 (SUC fuel)
     (L4KPi447 n bi a b) (L4KPi447 m bj c d) =
   l4_kr_bind491 (l4_primitive_check_signature619 fuel a c)
     (\ignored. l4_primitive_check_signature619 fuel b d)`,
  REWRITE_TAC [l4_primitive_check_signature619]);;
let l4_primitive_signature_app619 = prove
 (`!fuel a b c d.
   l4_primitive_check_signature619 (SUC fuel) (L4KApp447 a b) (L4KApp447 c d) =
   l4_kr_bind491 (l4_primitive_check_signature619 fuel a c)
     (\ignored. l4_primitive_check_signature619 fuel b d)`,
  REWRITE_TAC [l4_primitive_check_signature619]);;
let l4_primitive_signature_domain_decline619 = prove
 (`!fuel n bi a b m bj c d reason.
   l4_primitive_check_signature619 fuel a c = L4KDecline491 reason ==>
   l4_primitive_check_signature619 (SUC fuel)
     (L4KPi447 n bi a b) (L4KPi447 m bj c d) = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_signature619;l4_kr_bind491]);;
let l4_primitive_authenticated_missing619 = prove
 (`!fuel env op. l4_kfind_decl493 env (l4_primitive_name619 op) = NONE ==>
   l4_primitive_authenticated619 fuel env op = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_authenticated619]);;
let l4_primitive_authenticated_checked619 = prove
 (`!fuel env op d body.
   l4_kfind_decl493 env (l4_primitive_name619 op) = SOME d /\
   l4_kdecl_kind493 d = L4KDPrimitive493 op /\ l4_kdecl_value493 d = SOME body /\
   LENGTH (l4_kdecl_params493 d) = 0 ==>
   l4_primitive_authenticated619 fuel env op =
     l4_primitive_check_signature619 fuel (l4_kdecl_type493 d) (l4_primitive_signature619 op)`,
  SIMP_TAC [l4_primitive_authenticated619;l4_kprimitive_eqb493]);;
let l4_primitive_dependencies_nat_first619 = prove
 (`!fuel env op. ~l4_core_nat_ready533 env ==>
   l4_primitive_dependencies619 fuel env op = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_dependencies619]);;
let l4_primitive_dependencies_sub619 = prove
 (`!fuel env. l4_core_nat_ready533 env ==>
   l4_primitive_dependencies619 fuel env L4KPNatSub493 =
     l4_primitive_authenticated619 fuel env L4KPNatPred493`,
  SIMP_TAC [l4_primitive_dependencies619]);;
let l4_primitive_dependencies_multiply619 = prove
 (`!fuel env. l4_core_nat_ready533 env ==>
   l4_primitive_dependencies619 fuel env L4KPNatMul493 =
     l4_primitive_authenticated619 fuel env L4KPNatAdd493`,
  SIMP_TAC [l4_primitive_dependencies619]);;
let l4_primitive_dependencies_right_shift619 = prove
 (`!fuel env. l4_core_nat_ready533 env ==>
   l4_primitive_dependencies619 fuel env L4KPNatShiftRight493 =
     l4_primitive_authenticated619 fuel env L4KPNatDiv493`,
  SIMP_TAC [l4_primitive_dependencies619]);;
let l4_primitive_closed_no_fuel619 = prove
 (`!depth e. l4_primitive_closed619 0 depth e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_bvar619 = prove
 (`!fuel depth i. l4_primitive_closed619 (SUC fuel) depth (L4KBVar447 i) =
   if i < depth then L4KAccept491 one else L4KReject491 L4KLooseBoundVariable491`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_free619 = prove
 (`!fuel depth n. l4_primitive_closed619 (SUC fuel) depth (L4KFVar447 n) =
   L4KReject491 L4KUnknownFreeVariable491`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_meta619 = prove
 (`!fuel depth n. l4_primitive_closed619 (SUC fuel) depth (L4KMVar447 n) =
   L4KReject491 L4KMetaVariable491`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_lam619 = prove
 (`!fuel depth n bi a b.
   l4_primitive_closed619 (SUC fuel) depth (L4KLam447 n bi a b) =
   l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
     (\ignored. l4_primitive_closed619 fuel (SUC depth) b)`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_let619 = prove
 (`!fuel depth n a v b nd.
   l4_primitive_closed619 (SUC fuel) depth (L4KLet447 n a v b nd) =
   l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
     (\ignored_type. l4_kr_bind491 (l4_primitive_closed619 fuel depth v)
       (\ignored_value. l4_primitive_closed619 fuel (SUC depth) b))`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_closed_let_first_error619 = prove
 (`!fuel depth n a v b nd reason.
   l4_primitive_closed619 fuel depth a = L4KReject491 reason ==>
   l4_primitive_closed619 (SUC fuel) depth (L4KLet447 n a v b nd) = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_closed619;l4_kr_bind491]);;
let l4_primitive_equation_fields619 = prove
 (`!g a b. l4_primitive_context619 (l4_primitive_equation_at619 g a b) = g /\
   l4_primitive_lhs619 (l4_primitive_equation_at619 g a b) = a /\
   l4_primitive_rhs619 (l4_primitive_equation_at619 g a b) = b`,
  REWRITE_TAC [l4_primitive_equation_at619;l4_primitive_context619;
    l4_primitive_lhs619;l4_primitive_rhs619]);;
let l4_primitive_xy_context_shape619 = prove
 (`l4_primitive_xy_context619 = L4KContext532
   [L4KBinding491 l4_core_nat533 NONE;L4KBinding491 l4_core_nat533 NONE] []`,
  REWRITE_TAC [l4_primitive_xy_context619;l4_primitive_x_context619;
    l4_kempty_context532;l4_kpush_binding532]);;
