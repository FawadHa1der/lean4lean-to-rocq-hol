(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Port of the current Rocq Quotient.v dependency predicates.
   SOURCE ONLY / UNCOMPILED. No axiom or supplied-checker oracle. *)
needs "hol/quotient_terms608.ml";;
needs "hol/kernel_universes488.ml";;
needs "hol/nested_allocation437.ml";;

let l4_quotient_header_matches839 = new_definition
 `l4_quotient_header_matches839 kind d <=>
   let generated = l4_canonical_quotient608 kind in
   l4_kdecl_kind493 d = L4KDQuotient493 kind /\
   l4_kdecl_name493 d = l4_kdecl_name493 generated /\
   l4_names_unique437 (l4_kdecl_params493 d) /\
   LENGTH (l4_kdecl_params493 d) = LENGTH (l4_kdecl_params493 generated) /\
   (match l4_kdecl_value493 d with NONE -> T | SOME value -> F) /\
   l4_kexpr_eqb480 (l4_kdecl_type493 d)
     (l4_ksubst_levels488 (l4_kdecl_params493 generated)
       (MAP L4KParam447 (l4_kdecl_params493 d)) (l4_kdecl_type493 generated))`;;

(* Do not search past a malformed first visible declaration with this name. *)
let l4_quotient_dependency839 = new_definition
 `l4_quotient_dependency839 env kind <=>
   match l4_kfind_decl493 env (l4_kdecl_name493 (l4_canonical_quotient608 kind)) with
   | NONE -> F
   | SOME d -> l4_quotient_header_matches839 kind d`;;

let l4_quotient_dependencies839 = new_definition
 `l4_quotient_dependencies839 env kind <=>
   match kind with
   | L4KQType493 -> T
   | L4KQCtor493 -> l4_quotient_dependency839 env L4KQType493
   | L4KQLift493 -> l4_quotient_dependency839 env L4KQType493
   | L4KQInd493 -> l4_quotient_dependency839 env L4KQType493 /\
                   l4_quotient_dependency839 env L4KQCtor493`;;
