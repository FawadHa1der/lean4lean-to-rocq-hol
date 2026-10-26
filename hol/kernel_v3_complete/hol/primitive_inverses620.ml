(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational inverses of Primitives.v781-819. UNCOMPILED / NOT RUN.
   Accepted gates expose their unit payload existentially: no verdict oracle,
   assumed certificate, or whole-kernel soundness theorem is introduced. *)
needs "hol/primitive_admission620.ml";;

let l4_kr_bind_accept_inverse620 = prove
 (`!r:A l4_kresult491. !f:A->B l4_kresult491. !y:B.
   l4_kr_bind491 r f = L4KAccept491 y <=>
   ?x. r = L4KAccept491 x /\ f x = L4KAccept491 y`,
  MATCH_MP_TAC l4_kresult_INDUCT491 THEN
  SIMP_TAC [l4_kr_bind491;distinctness "l4_kresult491";injectivity "l4_kresult491"]);;

let l4_primitive_check_equations_accepts620 = prove
 (`!equations steps fuel env.
   l4_primitive_check_equations620 equations steps fuel env = L4KAccept491 one ==>
   ALL (\e. ?checked:1.
     l4_check_defeq597 fuel env [] (l4_primitive_context619 e)
       (l4_primitive_lhs619 e) (l4_primitive_rhs619 e) = L4KAccept491 checked) equations`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [l4_primitive_check_equations620;ALL];
    REPEAT GEN_TAC THEN
    REWRITE_TAC [l4_primitive_check_equations620;ALL] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [l4_kr_bind_accept_inverse620;distinctness "l4_kresult491"] THEN
    ASM_MESON_TAC []]);;

let l4_classify_primitive_metadata_requires_certificate620 = prove
 (`!fuel env n params ty body op.
   l4_classify_primitive620 fuel env n params ty body = L4KAccept491 (SOME op) ==>
   l4_primitive_lookup619 n = SOME op /\
   ((~l4_primitive_is_text620 op /\
     (?checked:1. l4_primitive_check_nat_equations620 fuel env op body = L4KAccept491 checked)) \/
    (l4_primitive_is_text620 op /\
     (?checked:1. l4_primitive_check_text_interface620 fuel env op = L4KAccept491 checked)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_classify_primitive620] THEN
  STRUCT_CASES_TAC (SPEC `l4_primitive_lookup619 n` (prove_cases_thm option_INDUCT)) THEN
  STRUCT_CASES_TAC (SPEC `l4_kfind_decl493 env n` (prove_cases_thm option_INDUCT)) THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC [l4_kr_bind491;l4_kr_bind_accept_inverse620;
    distinctness "l4_kresult491";injectivity "l4_kresult491";
    distinctness "option";injectivity "option"] THEN
  ASM_MESON_TAC []);;
