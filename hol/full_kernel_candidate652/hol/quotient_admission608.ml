(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of Rocq Quotient.v, with dependency parity repair839.
   SOURCE ONLY / UNCOMPILED. The pinned candidate652 remains unchanged.
   Header607 uses concrete597 methods. No injected checker/admission oracle.
   See ../DEPENDENCY608.txt for the exact header contract and observed pin. *)
needs "hol/quotient_terms608.ml";;
needs "hol/kernel_universes488.ml";;
needs "hol/ordinary_admission607.ml";;
needs "hol/quotient_dependencies839.ml";;

let l4_admit_quotient608 = new_definition
 `l4_admit_quotient608 fuel env n ps ty kind =
   l4_kr_bind491 (l4_quotient_check_eq608 env) (\eq_checked.
     l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header_checked.
       let generated = l4_canonical_quotient608 kind in
       if ~(n = l4_kdecl_name493 generated /\
            LENGTH ps = LENGTH (l4_kdecl_params493 generated))
       then L4KReject491 L4KMalformedDeclaration491 else
       if ~l4_kexpr_eqb480
         (l4_ksubst_levels488 ps (MAP L4KParam447 (l4_kdecl_params493 generated)) ty)
         (l4_kdecl_type493 generated)
       then L4KReject491 L4KMalformedDeclaration491 else
       if ~l4_quotient_dependencies839 env kind
       then L4KReject491 L4KMalformedDeclaration491 else
       L4KAccept491 (CONS generated env)))`;;
