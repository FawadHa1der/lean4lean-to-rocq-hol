(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed HOL proofs; UNCOMPILED / UNRUN. Not a Lean equivalence theorem. *)
needs "hol/quotient_dependencies839.ml";;

let l4_quotient_dependency_absent839 = prove
 (`!env kind.
   l4_kfind_decl493 env (l4_kdecl_name493 (l4_canonical_quotient608 kind)) = NONE ==>
   ~l4_quotient_dependency839 env kind`,
  SIMP_TAC [l4_quotient_dependency839]);;

let l4_quotient_dependency_first_visible839 = prove
 (`!env kind d.
   l4_kfind_decl493 env (l4_kdecl_name493 (l4_canonical_quotient608 kind)) = SOME d ==>
   (l4_quotient_dependency839 env kind <=> l4_quotient_header_matches839 kind d)`,
  SIMP_TAC [l4_quotient_dependency839]);;

let l4_quotient_dependency_shadow839 = prove
 (`!env kind d.
   l4_kdecl_name493 (l4_canonical_quotient608 kind) = l4_kdecl_name493 d ==>
   (l4_quotient_dependency839 (CONS d env) kind <=> l4_quotient_header_matches839 kind d)`,
  SIMP_TAC [l4_quotient_dependency839;l4_kfind_decl493]);;

let l4_quotient_dependency_wrong_kind839 = prove
 (`!kind d. ~(l4_kdecl_kind493 d = L4KDQuotient493 kind) ==>
   ~l4_quotient_header_matches839 kind d`,
  SIMP_TAC [l4_quotient_header_matches839;LET_DEF;LET_END_DEF]);;

let l4_quotient_dependency_value839 = prove
 (`!kind d value. l4_kdecl_value493 d = SOME value ==>
   ~l4_quotient_header_matches839 kind d`,
  SIMP_TAC [l4_quotient_header_matches839;LET_DEF;LET_END_DEF]);;

let l4_quotient_dependency_duplicate_params839 = prove
 (`!kind d. ~l4_names_unique437 (l4_kdecl_params493 d) ==>
   ~l4_quotient_header_matches839 kind d`,
  SIMP_TAC [l4_quotient_header_matches839;LET_DEF;LET_END_DEF]);;

let l4_quotient_dependency_cases839 = prove
 (`!env.
   l4_quotient_dependencies839 env L4KQType493 /\
   (l4_quotient_dependencies839 env L4KQCtor493 <=>
     l4_quotient_dependency839 env L4KQType493) /\
   (l4_quotient_dependencies839 env L4KQLift493 <=>
     l4_quotient_dependency839 env L4KQType493) /\
   (l4_quotient_dependencies839 env L4KQInd493 <=>
     l4_quotient_dependency839 env L4KQType493 /\
     l4_quotient_dependency839 env L4KQCtor493)`,
  REWRITE_TAC [l4_quotient_dependencies839]);;
