(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational admission equations. ALL SCRIPTS UNCOMPILED / NOT RUN.
   Premises concern the concrete607/597 functions, never supplied verdicts. *)
needs "hol/quotient_admission608.ml";;

let l4_quotient_eq_error_first608 = prove
 (`!fuel env n ps ty kind reason.
   l4_quotient_check_eq608 env = L4KReject491 reason ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 reason`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491]);;
let l4_quotient_empty_environment608 = prove
 (`!fuel n ps ty kind.
   l4_admit_quotient608 fuel [] n ps ty kind = L4KReject491 L4KUnknownConstant491`,
  REWRITE_TAC [l4_admit_quotient608;l4_quotient_check_eq608;l4_kfind_decl493;l4_kr_bind491]);;
let l4_quotient_header_reject608 = prove
 (`!fuel env n ps ty kind reason.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KReject491 reason ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 reason`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491]);;
let l4_quotient_header_decline608 = prove
 (`!fuel env n ps ty kind reason.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KDecline491 reason ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491]);;
let l4_quotient_duplicate_header608 = prove
 (`!fuel env n ps ty kind d.
   l4_quotient_check_eq608 env = L4KAccept491 one /\ l4_kfind_decl493 env n = SOME d ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_admit_quotient608;l4_check_header607;l4_kr_bind491]);;
let l4_quotient_wrong_generated_name608 = prove
 (`!fuel env n ps ty kind.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   ~(n = l4_kdecl_name493 (l4_canonical_quotient608 kind)) ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
let l4_quotient_wrong_generated_arity608 = prove
 (`!fuel env n ps ty kind.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   ~(LENGTH ps = LENGTH (l4_kdecl_params493 (l4_canonical_quotient608 kind))) ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
let l4_quotient_renamed_type_reject608 = prove
 (`!fuel env n ps ty kind.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   n = l4_kdecl_name493 (l4_canonical_quotient608 kind) /\
   LENGTH ps = LENGTH (l4_kdecl_params493 (l4_canonical_quotient608 kind)) /\
   ~l4_kexpr_eqb480
     (l4_ksubst_levels488 ps (MAP L4KParam447 (l4_kdecl_params493 (l4_canonical_quotient608 kind))) ty)
     (l4_kdecl_type493 (l4_canonical_quotient608 kind)) ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
let l4_quotient_inserts_generated608 = prove
 (`!fuel env n ps ty kind.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   n = l4_kdecl_name493 (l4_canonical_quotient608 kind) /\
   LENGTH ps = LENGTH (l4_kdecl_params493 (l4_canonical_quotient608 kind)) /\
   l4_kexpr_eqb480
     (l4_ksubst_levels488 ps (MAP L4KParam447 (l4_kdecl_params493 (l4_canonical_quotient608 kind))) ty)
     (l4_kdecl_type493 (l4_canonical_quotient608 kind)) /\
   l4_quotient_dependencies839 env kind ==>
   l4_admit_quotient608 fuel env n ps ty kind =
     L4KAccept491 (CONS (l4_canonical_quotient608 kind) env)`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_quotient_missing_dependencies839 = prove
 (`!fuel env n ps ty kind.
   l4_quotient_check_eq608 env = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   n = l4_kdecl_name493 (l4_canonical_quotient608 kind) /\
   LENGTH ps = LENGTH (l4_kdecl_params493 (l4_canonical_quotient608 kind)) /\
   l4_kexpr_eqb480
     (l4_ksubst_levels488 ps (MAP L4KParam447 (l4_kdecl_params493 (l4_canonical_quotient608 kind))) ty)
     (l4_kdecl_type493 (l4_canonical_quotient608 kind)) /\
   ~l4_quotient_dependencies839 env kind ==>
   l4_admit_quotient608 fuel env n ps ty kind = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_quotient608;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_quotient_universe_renaming608 = prove
 (`!p q. l4_ksubst_levels488 [p] [L4KParam447 q] (L4KSort447 (L4KParam447 p)) =
   L4KSort447 (L4KParam447 q)`,
  REWRITE_TAC [l4_ksubst_levels488;l4_ksubst_level488;l4_klookup_level488;NULL;HD]);;
