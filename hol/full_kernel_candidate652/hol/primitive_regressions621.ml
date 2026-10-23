(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED REGRESSION PROOFS / UNCOMPILED / UNEXECUTED.
   Expected raw syntax and failure precedence, not a corpus of assumed passes. *)
needs "hol/primitive_reflection621.ml";;

let L4_PQ_PATH_COMPONENTS621 = prove
 (`l4_primitive_path621 [[78;97;116];[100;105;118];[103;111]] =
     L4String (L4String (L4String L4Anonymous [78;97;116]) [100;105;118]) [103;111]`,
  REWRITE_TAC [l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_PQ_DIV_GO621 = prove
 (`l4_primitive_go_name621 F =
     L4String (L4String (L4String L4Anonymous [78;97;116]) [100;105;118]) [103;111]`,
  REWRITE_TAC [l4_primitive_go_name621; l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_PQ_MOD_GO621 = prove
 (`l4_primitive_go_name621 T =
     L4String (L4String (L4String L4Anonymous [78;97;116])
       [109;111;100;67;111;114;101]) [103;111]`,
  REWRITE_TAC [l4_primitive_go_name621; l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_PQ_DEPENDENT_PI621 = prove
 (`l4_pq_run621 (l4_pq_pi621 l4_pq_type0621 (\a. l4_pq_pi621 a (\x. a))) =
     L4KPi447 L4Anonymous L4KDefault447 (L4KSort447 (L4KSucc447 L4KZero447))
       (L4KPi447 L4Anonymous L4KDefault447 (L4KBVar447 0) (L4KBVar447 1))`,
  REWRITE_TAC [l4_pq_run621; l4_pq_pi621; l4_pq_type0621; l4_pq_embed621; l4_klift447] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let L4_PQ_EMBED_OPEN_CAPTURE_FREE621 = prove
 (`l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\x. l4_pq_embed621 (L4KBVar447 3))) =
     L4KLam447 L4Anonymous L4KDefault447 (L4KSort447 L4KZero447) (L4KBVar447 4)`,
  REWRITE_TAC [l4_pq_run621; l4_pq_lam621; l4_pq_prop621; l4_pq_embed621; l4_klift447] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let L4_PQ_SATURATING_LEVEL621 = prove
 (`l4_pq_lam621 l4_pq_prop621 (\x d. x 0) 7 =
     L4KLam447 L4Anonymous L4KDefault447 (L4KSort447 L4KZero447) (L4KBVar447 0)`,
  REWRITE_TAC [l4_pq_lam621; l4_pq_prop621; l4_pq_embed621; l4_klift447] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let L4_PQ_EMBED_FULL_FIELDS621 = prove
 (`l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\ignored.
     l4_pq_embed621 (L4KMData447
       (L4KLam447 (L4Numeric L4Anonymous 17) L4KInstImplicit447
         (L4KSort447 L4KZero447) (L4KBVar447 1))))) =
     L4KLam447 L4Anonymous L4KDefault447 (L4KSort447 L4KZero447)
       (L4KMData447 (L4KLam447 (L4Numeric L4Anonymous 17) L4KInstImplicit447
         (L4KSort447 L4KZero447) (L4KBVar447 2)))`,
  REWRITE_TAC [l4_pq_run621; l4_pq_lam621; l4_pq_prop621; l4_pq_embed621; l4_klift447] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let L4_PQ_LE_PROPOSITION621 = prove
 (`l4_primitive_condition_prop621 L4PCNatLE621 =
     L4KConst447 (L4String (L4String L4Anonymous [78;97;116]) [108;101]) []`,
  REWRITE_TAC [l4_primitive_condition_prop621; l4_primitive_const621;
    l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_PQ_EQ_PROPOSITION_UNIVERSE621 = prove
 (`l4_primitive_condition_prop621 L4PCNatEq621 =
     L4KApp447 (L4KConst447 (L4String L4Anonymous [69;113]) [L4KSucc447 L4KZero447])
       l4_core_nat533`,
  REWRITE_TAC [l4_primitive_condition_prop621; l4_primitive_const621;
    l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_PQ_EQ_DECIDER621 = prove
 (`l4_primitive_condition_dec621 L4PCNatEq621 =
     L4KConst447 (L4String (L4String L4Anonymous [78;97;116]) [100;101;99;69;113]) []`,
  REWRITE_TAC [l4_primitive_condition_dec621; l4_primitive_const621;
    l4_primitive_path621; l4_primitive_path_aux621]);;

let L4_CONDITION_NO_SKIP_EMPTY_ENV621 = prove
 (`!c wi wd. l4_primitive_check_condition621 0 [] c wi wd =
     L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_check_condition621; l4_core_bool_ready533; l4_kfind_decl493]);;

let L4_FUEL_REC_NO_SKIP_EMPTY_ENV621 = prove
 (`!modulo body. l4_primitive_check_fuel_rec621 0 [] modulo body =
     L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_check_fuel_rec621; l4_core_nat_ready533;
    l4_core_bool_ready533; l4_kfind_decl493]);;
