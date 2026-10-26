(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational properties of concrete kernel calls. UNCOMPILED.
   These are not supplied verdict callbacks or semantic soundness theorems. *)
needs "hol/primitive_admission620.ml";;

let l4_primitive_equations_first_reject620 = prove
 (`!e es steps fuel env reason.
   ~(steps = 0) /\
   l4_check_defeq597 fuel env [] (l4_primitive_context619 e)
     (l4_primitive_lhs619 e) (l4_primitive_rhs619 e) = L4KReject491 reason ==>
   l4_primitive_check_equations620 (CONS e es) steps fuel env = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_equations620;l4_kr_bind491]);;

let l4_primitive_equations_first_decline620 = prove
 (`!e es steps fuel env reason.
   ~(steps = 0) /\
   l4_check_defeq597 fuel env [] (l4_primitive_context619 e)
     (l4_primitive_lhs619 e) (l4_primitive_rhs619 e) = L4KDecline491 reason ==>
   l4_primitive_check_equations620 (CONS e es) steps fuel env = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_equations620;l4_kr_bind491]);;

let l4_primitive_equations_next620 = prove
 (`!e es steps fuel env.
   ~(steps = 0) /\
   l4_check_defeq597 fuel env [] (l4_primitive_context619 e)
     (l4_primitive_lhs619 e) (l4_primitive_rhs619 e) = L4KAccept491 one ==>
   l4_primitive_check_equations620 (CONS e es) steps fuel env =
     l4_primitive_check_equations620 es (steps - 1) fuel env`,
  SIMP_TAC [l4_primitive_check_equations620;l4_kr_bind491]);;

let l4_primitive_ensure_type_reject620 = prove
 (`!fuel env e reason.
   l4_sort_of543 (l4_checker597 fuel env []) l4_kempty_context532 e = L4KReject491 reason ==>
   l4_primitive_ensure_type620 fuel env e = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_ensure_type620;l4_kr_bind491]);;

let l4_primitive_ensure_type_decline620 = prove
 (`!fuel env e reason.
   l4_sort_of543 (l4_checker597 fuel env []) l4_kempty_context532 e = L4KDecline491 reason ==>
   l4_primitive_ensure_type620 fuel env e = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_ensure_type620;l4_kr_bind491]);;

let l4_primitive_ensure_type_accept620 = prove
 (`!fuel env e u.
   l4_sort_of543 (l4_checker597 fuel env []) l4_kempty_context532 e = L4KAccept491 u ==>
   l4_primitive_ensure_type620 fuel env e = L4KAccept491 one`,
  SIMP_TAC [l4_primitive_ensure_type620;l4_kr_bind491]);;

let l4_primitive_char_not_ready620 = prove
 (`!fuel env. ~l4_core_nat_ready533 env ==>
   l4_primitive_check_text_interface620 fuel env L4KPCharOfNat493 =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_text_interface620]);;

let l4_primitive_char_ready620 = prove
 (`!fuel env. l4_core_nat_ready533 env ==>
   l4_primitive_check_text_interface620 fuel env L4KPCharOfNat493 =
     l4_primitive_ensure_type620 fuel env l4_primitive_char619`,
  SIMP_TAC [l4_primitive_check_text_interface620]);;

let l4_primitive_string_list_type_first620 = prove
 (`!fuel env reason.
   l4_primitive_ensure_type620 fuel env l4_primitive_list_char619 = L4KReject491 reason ==>
   l4_primitive_check_text_interface620 fuel env L4KPStringOfList493 = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_text_interface620;l4_kr_bind491]);;

let l4_primitive_nat_dependencies_reject620 = prove
 (`!fuel env op body equations reason.
   l4_primitive_equations620 op body = SOME equations /\
   l4_primitive_dependencies619 fuel env op = L4KReject491 reason ==>
   l4_primitive_check_nat_equations620 fuel env op body = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_nat_equations620;l4_kr_bind491]);;

let l4_primitive_nat_dependencies_decline620 = prove
 (`!fuel env op body equations reason.
   l4_primitive_equations620 op body = SOME equations /\
   l4_primitive_dependencies619 fuel env op = L4KDecline491 reason ==>
   l4_primitive_check_nat_equations620 fuel env op body = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_nat_equations620;l4_kr_bind491]);;

let l4_primitive_nat_equations_order620 = prove
 (`!fuel env op body equations.
   l4_primitive_equations620 op body = SOME equations /\
   l4_primitive_dependencies619 fuel env op = L4KAccept491 one ==>
   l4_primitive_check_nat_equations620 fuel env op body =
     l4_primitive_check_equations620 equations fuel fuel env`,
  SIMP_TAC [l4_primitive_check_nat_equations620;l4_kr_bind491]);;

let l4_classify_unknown_nonreserved620 = prove
 (`!fuel env n params ty body.
   l4_primitive_lookup619 n = NONE /\
   ~l4_name_mem437 n
     [l4_core_nat_name533;l4_core_zero_name533;l4_core_succ_name533;
      l4_core_bool_name533;l4_core_false_name533;l4_core_true_name533] ==>
   l4_classify_primitive620 fuel env n params ty body = L4KAccept491 NONE`,
  SIMP_TAC [l4_classify_primitive620]);;

let l4_classify_unknown_reserved620 = prove
 (`!fuel env n params ty body.
   l4_primitive_lookup619 n = NONE /\
   l4_name_mem437 n
     [l4_core_nat_name533;l4_core_zero_name533;l4_core_succ_name533;
      l4_core_bool_name533;l4_core_false_name533;l4_core_true_name533] ==>
   l4_classify_primitive620 fuel env n params ty body = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_classify_primitive620]);;

let l4_classify_duplicate_first620 = prove
 (`!fuel env n params ty body op d.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = SOME d ==>
   l4_classify_primitive620 fuel env n params ty body = L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_classify_arity_before_signature620 = prove
 (`!fuel env n params ty body op.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = NONE /\
   ~(LENGTH params = 0) ==>
   l4_classify_primitive620 fuel env n params ty body = L4KReject491 L4KUniverseArity491`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_classify_signature_before_closed620 = prove
 (`!fuel env n params ty body op reason.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = NONE /\
   LENGTH params = 0 /\
   l4_primitive_check_signature619 fuel ty (l4_primitive_signature619 op) = L4KReject491 reason ==>
   l4_classify_primitive620 fuel env n params ty body = L4KReject491 reason`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_classify_closed_before_certificate620 = prove
 (`!fuel env n params ty body op reason.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = NONE /\
   LENGTH params = 0 /\
   l4_primitive_check_signature619 fuel ty (l4_primitive_signature619 op) = L4KAccept491 one /\
   l4_primitive_closed619 fuel 0 body = L4KDecline491 reason ==>
   l4_classify_primitive620 fuel env n params ty body = L4KDecline491 reason`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_classify_text_interface_only620 = prove
 (`!fuel env n params ty body op.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = NONE /\
   LENGTH params = 0 /\
   l4_primitive_check_signature619 fuel ty (l4_primitive_signature619 op) = L4KAccept491 one /\
   l4_primitive_closed619 fuel 0 body = L4KAccept491 one /\ l4_primitive_is_text620 op ==>
   l4_classify_primitive620 fuel env n params ty body =
     l4_kr_bind491 (l4_primitive_check_text_interface620 fuel env op)
       (\checked. L4KAccept491 (SOME op))`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_classify_nat_certificate620 = prove
 (`!fuel env n params ty body op.
   l4_primitive_lookup619 n = SOME op /\ l4_kfind_decl493 env n = NONE /\
   LENGTH params = 0 /\
   l4_primitive_check_signature619 fuel ty (l4_primitive_signature619 op) = L4KAccept491 one /\
   l4_primitive_closed619 fuel 0 body = L4KAccept491 one /\ ~l4_primitive_is_text620 op ==>
   l4_classify_primitive620 fuel env n params ty body =
     l4_kr_bind491 (l4_primitive_check_nat_equations620 fuel env op body)
       (\checked. L4KAccept491 (SOME op))`,
  SIMP_TAC [l4_classify_primitive620;l4_kr_bind491]);;

let l4_primitive_string_list_type_decline620 = prove
 (`!fuel env reason.
   l4_primitive_ensure_type620 fuel env l4_primitive_list_char619 = L4KDecline491 reason ==>
   l4_primitive_check_text_interface620 fuel env L4KPStringOfList493 = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_text_interface620;l4_kr_bind491]);;

let l4_primitive_string_char_type_second620 = prove
 (`!fuel env reason.
   l4_primitive_ensure_type620 fuel env l4_primitive_list_char619 = L4KAccept491 one /\
   l4_primitive_ensure_type620 fuel env l4_primitive_char619 = L4KReject491 reason ==>
   l4_primitive_check_text_interface620 fuel env L4KPStringOfList493 = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_text_interface620;l4_kr_bind491]);;

let l4_primitive_string_nil_before_cons620 = prove
 (`!fuel env reason.
   l4_primitive_ensure_type620 fuel env l4_primitive_list_char619 = L4KAccept491 one /\
   l4_primitive_ensure_type620 fuel env l4_primitive_char619 = L4KAccept491 one /\
   l4_check597 fuel env [] l4_kempty_context532
     (L4KApp447
       (L4KConst447 (L4String l4_core_list_name539 [110;105;108]) [L4KZero447])
       l4_primitive_char619) l4_primitive_list_char619 = L4KReject491 reason ==>
   l4_primitive_check_text_interface620 fuel env L4KPStringOfList493 = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_text_interface620;l4_kr_bind491]);;

let l4_primitive_string_cons_last620 = prove
 (`!fuel env.
   l4_primitive_ensure_type620 fuel env l4_primitive_list_char619 = L4KAccept491 one /\
   l4_primitive_ensure_type620 fuel env l4_primitive_char619 = L4KAccept491 one /\
   l4_check597 fuel env [] l4_kempty_context532
     (L4KApp447
       (L4KConst447 (L4String l4_core_list_name539 [110;105;108]) [L4KZero447])
       l4_primitive_char619) l4_primitive_list_char619 = L4KAccept491 one ==>
   l4_primitive_check_text_interface620 fuel env L4KPStringOfList493 =
     l4_check597 fuel env [] l4_kempty_context532
       (L4KApp447
         (L4KConst447 (L4String l4_core_list_name539 [99;111;110;115]) [L4KZero447])
         l4_primitive_char619)
       (l4_primitive_arrow619 l4_primitive_char619
         (l4_primitive_arrow619 l4_primitive_list_char619 l4_primitive_list_char619))`,
  SIMP_TAC [l4_primitive_check_text_interface620;l4_kr_bind491]);;
