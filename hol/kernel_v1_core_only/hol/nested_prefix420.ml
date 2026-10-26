(* Copyright 2026 Fawad Haider. Apache-2.0; see ../NOTICE420.txt.
   Structured-name helper for nested constructor generation/restoration.
   SOURCE ONLY: not parsed or compiled by HOL Light; no admission is enabled.
   A missing prefix is explicit, never a successful unchanged-name fallback. *)
needs "hol/syntax.ml";;

let l4_prefix_result_INDUCT420,l4_prefix_result_RECURSION420 = define_type
 "l4_prefix_result420 = L4PrefixMiss420 | L4PrefixHit420 l4_name";;

let l4_prefix_string420 = new_recursive_definition l4_prefix_result_RECURSION420
 `(l4_prefix_string420 L4PrefixMiss420 s = L4PrefixMiss420) /\
  (l4_prefix_string420 (L4PrefixHit420 n) s = L4PrefixHit420 (L4String n s))`;;

let l4_prefix_numeric420 = new_recursive_definition l4_prefix_result_RECURSION420
 `(l4_prefix_numeric420 L4PrefixMiss420 k = L4PrefixMiss420) /\
  (l4_prefix_numeric420 (L4PrefixHit420 n) k = L4PrefixHit420 (L4Numeric n k))`;;

(* The first argument is the name being inspected, not the proposed prefix. *)
let l4_name_prefix420 = new_recursive_definition l4_name_RECURSION
 `(l4_name_prefix420 L4Anonymous old <=> old = L4Anonymous) /\
  (l4_name_prefix420 (L4String n s) old <=>
    L4String n s = old \/ l4_name_prefix420 n old) /\
  (l4_name_prefix420 (L4Numeric n k) old <=>
    L4Numeric n k = old \/ l4_name_prefix420 n old)`;;

let l4_name_replace_prefix420 = new_recursive_definition l4_name_RECURSION
 `(l4_name_replace_prefix420 L4Anonymous old replacement =
    if old = L4Anonymous then L4PrefixHit420 replacement else L4PrefixMiss420) /\
  (l4_name_replace_prefix420 (L4String n s) old replacement =
    if L4String n s = old then L4PrefixHit420 replacement
    else l4_prefix_string420 (l4_name_replace_prefix420 n old replacement) s) /\
  (l4_name_replace_prefix420 (L4Numeric n k) old replacement =
    if L4Numeric n k = old then L4PrefixHit420 replacement
    else l4_prefix_numeric420 (l4_name_replace_prefix420 n old replacement) k)`;;

(* Re-root a suffix at a new base; the suffix root is anonymous. *)
let l4_name_append420 = new_recursive_definition l4_name_RECURSION
 `(l4_name_append420 L4Anonymous base = base) /\
  (l4_name_append420 (L4String n s) base = L4String (l4_name_append420 n base) s) /\
  (l4_name_append420 (L4Numeric n k) base = L4Numeric (l4_name_append420 n base) k)`;;

let l4_name_depth420 = new_recursive_definition l4_name_RECURSION
 `(l4_name_depth420 L4Anonymous = 0) /\
  (l4_name_depth420 (L4String n s) = SUC (l4_name_depth420 n)) /\
  (l4_name_depth420 (L4Numeric n k) = SUC (l4_name_depth420 n))`;;
