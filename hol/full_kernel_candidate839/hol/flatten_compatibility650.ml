(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   TWO PROPOSED COMPATIBILITY PROOFS, UNCOMPILED / NOT EXECUTED.
   Not required by the prelude or future computation registry. *)
needs "hol/load_flatten_repair650.ml";;
needs "hol/flatten_properties650.ml";;
needs "hol/inductive_derivation516.ml";;

let L4_FLAT_CANONICAL516650 = prove
 (`!xss:(A list)list. FLAT xss = l4_kflatten516 xss`,
  REWRITE_TAC[l4_kflatten516;L4_FLAT_ITLIST650]);;

let L4_NESTED_USED_NAMES_FOLD650 = prove
 (`!env w. l4_knested_used_names498 env w =
   APPEND (MAP l4_kdecl_name493 env)
    (APPEND (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) (l4_knw_specs494 w))
     (APPEND (MAP (\s. l4_nested_rec_name437 (l4_kdecl_name493 (l4_kspec_decl493 s)))
                   (l4_knw_specs494 w))
      (l4_kflatten516
        (MAP (\s. MAP l4_kdecl_name493 (l4_kspec_ctors493 s)) (l4_knw_specs494 w)))))`,
  REWRITE_TAC[l4_knested_used_names498;L4_FLAT_CANONICAL516650]);;
