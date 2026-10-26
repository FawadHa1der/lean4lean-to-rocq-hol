(* SPDX-License-Identifier: Apache-2.0. Proposed adversarial regressions.
   ALL UNCOMPILED; these are not Arena outcomes or proved soundness claims. *)
needs "hol/primitive_foundations619.ml";;

let l4_primitive_no_fuel_even_free619 = prove
 (`l4_primitive_closed619 0 0 (L4KFVar447 L4Anonymous) = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_loose_zero619 = prove
 (`l4_primitive_closed619 1 0 (L4KBVar447 0) = L4KReject491 L4KLooseBoundVariable491`,
  REWRITE_TAC [ONE;l4_primitive_closed619;LT_REFL]);;
let l4_primitive_scope_boundary619 = prove
 (`!fuel depth. l4_primitive_closed619 (SUC fuel) depth (L4KBVar447 depth) =
   L4KReject491 L4KLooseBoundVariable491`,
  REWRITE_TAC [l4_primitive_closed619;LT_REFL]);;
let l4_primitive_closed_not_typing619 = prove
 (`!fuel n us. l4_primitive_closed619 (SUC fuel) 0 (L4KConst447 n us) = L4KAccept491 one`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_literal_not_readiness619 = prove
 (`!fuel bytes. l4_primitive_closed619 (SUC fuel) 0 (L4KStrLit447 bytes) = L4KAccept491 one`,
  REWRITE_TAC [l4_primitive_closed619]);;
let l4_primitive_expected_metadata_not_erased619 = prove
 (`!fuel n us. l4_primitive_check_signature619 (SUC fuel)
   (L4KConst447 n us) (L4KMData447 (L4KConst447 n us)) = L4KReject491 L4KTypeMismatch491`,
  REWRITE_TAC [l4_primitive_check_signature619;l4_kexpr_eqb480]);;
let l4_primitive_metadata_costs_fuel619 = prove
 (`!n us. l4_primitive_check_signature619 1
   (L4KMData447 (L4KConst447 n us)) (L4KConst447 n us) = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [ONE;l4_primitive_check_signature619]);;
let l4_primitive_signature_no_alias_unfold619 = prove
 (`!fuel n m us. ~(n = m) ==>
   l4_primitive_check_signature619 (SUC fuel) (L4KConst447 n us) (L4KConst447 m us) =
     L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_primitive_check_signature619;l4_kexpr_eqb480]);;
let l4_primitive_plain_definition_not_authenticated619 = prove
 (`!fuel env op ty body hints.
   l4_primitive_authenticated619 fuel
     (CONS (L4KDeclaration493 (l4_primitive_name619 op) [] ty (SOME body)
       L4KDDefinition493 hints) env) op = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_authenticated619;l4_kfind_decl493;l4_kdecl_name493;
    l4_kdecl_kind493;l4_kdecl_value493]);;
let l4_primitive_body_required619 = prove
 (`!fuel env op ps ty hints.
   l4_primitive_authenticated619 fuel
     (CONS (L4KDeclaration493 (l4_primitive_name619 op) ps ty NONE
       (L4KDPrimitive493 op) hints) env) op = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_authenticated619;l4_kfind_decl493;l4_kdecl_name493;
    l4_kdecl_kind493;l4_kdecl_value493]);;
let l4_primitive_no_polymorphic_tag619 = prove
 (`!fuel env op p ps ty body hints.
   l4_primitive_authenticated619 fuel
     (CONS (L4KDeclaration493 (l4_primitive_name619 op) (CONS p ps) ty (SOME body)
       (L4KDPrimitive493 op) hints) env) op = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_authenticated619;l4_kfind_decl493;l4_kdecl_name493;
    l4_kdecl_kind493;l4_kdecl_value493;l4_kdecl_params493;l4_kprimitive_eqb493;
    LENGTH;NOT_SUC]);;
let l4_primitive_wrong_tag619 = prove
 (`!fuel env op actual ty body hints. ~(actual = op) ==>
   l4_primitive_authenticated619 fuel
     (CONS (L4KDeclaration493 (l4_primitive_name619 op) [] ty (SOME body)
       (L4KDPrimitive493 actual) hints) env) op = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_authenticated619;l4_kfind_decl493;l4_kdecl_name493;
    l4_kdecl_kind493;l4_kdecl_value493;l4_kprimitive_eqb493]);;
let l4_primitive_missing_before_fuel619 = prove
 (`!op. l4_primitive_authenticated619 0 [] op = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_primitive_authenticated619;l4_kfind_decl493]);;
let l4_primitive_list_universe619 = prove
 (`l4_primitive_list_char619 =
   L4KApp447 (L4KConst447 l4_core_list_name539 [L4KZero447])
     (L4KConst447 l4_core_char_name533 [])`,
  REWRITE_TAC [l4_primitive_list_char619;l4_primitive_char619]);;
