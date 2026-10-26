(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED REGRESSION PROOFS: ALL UNCOMPILED / NOT EXECUTED.
   No installed environment, native computation or proof evidence is claimed. *)
needs "hol/primitive_recursors622.ml";;

let l4_primitive_lambda_zero622 = prove
 (`!fuel env s e. l4_primitive_lambda_telescope622 0 fuel env s e =
   L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_lambda_telescope622]);;

let l4_primitive_lambda_metadata_depth622 = prove
 (`!fuel env s e. l4_primitive_lambda_telescope622 (SUC 0) fuel env s (L4KMData447 e) =
   L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_lambda_telescope622]);;

let l4_primitive_lambda_stops_at_pi622 = prove
 (`!depth fuel env s n bi a b.
   l4_primitive_lambda_telescope622 (SUC depth) fuel env s (L4KPi447 n bi a b) =
   L4KAccept491 ([],(L4KPi447 n bi a b,s))`,
  REWRITE_TAC [l4_primitive_lambda_telescope622]);;

let l4_primitive_no_free_zero622 = prove
 (`!n e. l4_primitive_no_free622 0 n e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_no_free622]);;

let l4_primitive_no_free_self622 = prove
 (`!fuel n. l4_primitive_no_free622 (SUC fuel) n (L4KFVar447 n) =
   L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_no_free622]);;

let l4_primitive_no_free_not_closedness622 = prove
 (`!fuel n m. l4_primitive_no_free622 (SUC fuel) n (L4KMVar447 m) = L4KAccept491 one`,
  REWRITE_TAC [l4_primitive_no_free622]);;

let l4_primitive_no_free_reject_before_exhaustion622 = prove
 (`!n e. l4_primitive_no_free622 (SUC (SUC 0)) n
   (L4KApp447 (L4KFVar447 n) (L4KMData447 e)) = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_no_free622;l4_kr_bind491]);;

let l4_primitive_no_free_exhaustion_before_capture622 = prove
 (`!n e. l4_primitive_no_free622 (SUC (SUC 0)) n
   (L4KApp447 (L4KMData447 e) (L4KFVar447 n)) = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_no_free622;l4_kr_bind491]);;

let l4_primitive_no_free_let_value_capture622 = prove
 (`!n user b nd. l4_primitive_no_free622 (SUC (SUC 0)) n
   (L4KLet447 user (L4KSort447 L4KZero447) (L4KFVar447 n) b nd) =
   L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_no_free622;l4_kr_bind491]);;

let l4_primitive_unfold_not_delta_on_metadata622 = prove
 (`!env n us. l4_primitive_unfold622 env (L4KMData447 (L4KConst447 n us)) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_primitive_unfold622;l4_ksplit_app489;l4_ksplit_app_aux489;LET_DEF;LET_END_DEF]);;

let l4_primitive_unfold_theorem_decline622 = prove
 (`!env n us ps ty value hints.
   l4_get_constant528 env [] n us =
     L4KAccept491 (L4KDeclaration493 n ps ty (SOME value) L4KDTheorem493 hints) ==>
   l4_primitive_unfold622 env (L4KConst447 n us) = L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_unfold622;l4_ksplit_app489;l4_ksplit_app_aux489;
    l4_kdecl_kind493;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_unfold_missing_body622 = prove
 (`!env n us ps ty hints.
   l4_get_constant528 env [] n us =
     L4KAccept491 (L4KDeclaration493 n ps ty NONE L4KDDefinition493 hints) ==>
   l4_primitive_unfold622 env (L4KConst447 n us) = L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_unfold622;l4_ksplit_app489;l4_ksplit_app_aux489;
    l4_kdecl_kind493;l4_kdecl_value493;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_unfold_definition_substitution622 = prove
 (`!env n us ps ty body hints args e.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_get_constant528 env [] n us =
     L4KAccept491 (L4KDeclaration493 n ps ty (SOME body) L4KDDefinition493 hints) ==>
   l4_primitive_unfold622 env e =
     L4KAccept491 (l4_kapply_exprs489 args (l4_ksubst_levels488 ps us body))`,
  SIMP_TAC [l4_primitive_unfold622;l4_kdecl_kind493;l4_kdecl_value493;
    l4_kdecl_params493;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_unfold_primitive_substitution622 = prove
 (`!env n us ps ty body hints args e op.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_get_constant528 env [] n us =
     L4KAccept491 (L4KDeclaration493 n ps ty (SOME body) (L4KDPrimitive493 op) hints) ==>
   l4_primitive_unfold622 env e =
     L4KAccept491 (l4_kapply_exprs489 args (l4_ksubst_levels488 ps us body))`,
  SIMP_TAC [l4_primitive_unfold622;l4_kdecl_kind493;l4_kdecl_value493;
    l4_kdecl_params493;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_unfold_getter_error_first622 = prove
 (`!env n us reason. l4_get_constant528 env [] n us = L4KReject491 reason ==>
   l4_primitive_unfold622 env (L4KConst447 n us) = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_unfold622;l4_ksplit_app489;l4_ksplit_app_aux489;
    l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_wf_zero622 = prove
 (`!env s e measure. l4_primitive_unfold_nat_well_founded622 0 env s e measure =
   L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_unfold_nat_well_founded622;l4_primitive_lambda_telescope622;l4_kr_bind491]);;

let l4_primitive_first_measure_two_binders622 = prove
 (`l4_primitive_first_measure622 =
   L4KLam447 L4Anonymous L4KDefault447 l4_core_nat533
     (L4KLam447 L4Anonymous L4KDefault447 l4_core_nat533 (L4KBVar447 1))`,
  REWRITE_TAC [l4_primitive_first_measure622;l4_pq_run621;l4_pq_lam621;
    l4_pq_nat621;l4_pq_embed621;l4_core_nat533;l4_klift447] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let l4_primitive_gcd_readiness_first622 = prove
 (`!fuel env body. ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env) ==>
   l4_primitive_check_gcd622 fuel env body = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_gcd622]);;

let l4_primitive_bitwise_readiness_first622 = prove
 (`!fuel env body. ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env) ==>
   l4_primitive_check_bitwise622 fuel env body = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_bitwise622]);;

let l4_primitive_boolean_other_op_decline622 = prove
 (`!fuel env operator.
   l4_check597 fuel env [] l4_kempty_context532 operator l4_primitive_bool_operator_type622 =
     L4KAccept491 one ==>
   l4_primitive_check_boolean_operator622 fuel env L4KPNatAdd493 operator =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_check_boolean_operator622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_instance_nonempty_universes622 = prove
 (`!fuel env op n u us operator.
   l4_primitive_authenticated619 fuel env L4KPNatBitwise493 = L4KAccept491 one ==>
   l4_primitive_check_bitwise_instance622 fuel env op
     (L4KApp447 (L4KConst447 n (CONS u us)) operator) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_check_bitwise_instance622;l4_kr_bind491]);;

let l4_primitive_instance_wrong_name622 = prove
 (`!fuel env op n operator.
   l4_primitive_authenticated619 fuel env L4KPNatBitwise493 = L4KAccept491 one /\
   ~(n = l4_primitive_bitwise_name619) ==>
   l4_primitive_check_bitwise_instance622 fuel env op (L4KApp447 (L4KConst447 n []) operator) =
   L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_bitwise_instance622;l4_kr_bind491]);;

let l4_primitive_instance_no_metadata_wrapper622 = prove
 (`!fuel env op body.
   l4_primitive_authenticated619 fuel env L4KPNatBitwise493 = L4KAccept491 one ==>
   l4_primitive_check_bitwise_instance622 fuel env op (L4KMData447 body) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_check_bitwise_instance622;l4_kr_bind491]);;
