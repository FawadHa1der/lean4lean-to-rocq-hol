(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider. See ../NOTICE488.txt and ../LICENSE.
   Changed HOL port of local Rocq Syntax.v universe substitution.
   SOURCE ONLY / UNCOMPILED. No checker loader or authority is changed. *)
needs "hol/kernel_syntax447.ml";;

(* Rocq argument order: parameter names, replacement levels, subject.
   The NULL guard makes HD/TL irrelevant on an empty replacement list.
   No ZIP: lookup truncates at either list end and keeps the first match. *)
let l4_klookup_level488 = new_recursive_definition list_RECURSION
 `(l4_klookup_level488 [] (us:l4_klevel447 list) (n:l4_name) =
     L4KParam447 n) /\
  (l4_klookup_level488 (CONS p ps) us n =
     if NULL us then L4KParam447 n
     else if p = n then HD us
     else l4_klookup_level488 ps (TL us) n)`;;

(* A matched replacement is returned as-is, not traversed or normalized.
   Level metavariables are not universe parameters, even with the same name. *)
let l4_ksubst_level488 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_ksubst_level488 ps us L4KZero447 = L4KZero447) /\
  (l4_ksubst_level488 ps us (L4KSucc447 u) =
     L4KSucc447 (l4_ksubst_level488 ps us u)) /\
  (l4_ksubst_level488 ps us (L4KMax447 u v) =
     L4KMax447 (l4_ksubst_level488 ps us u) (l4_ksubst_level488 ps us v)) /\
  (l4_ksubst_level488 ps us (L4KIMax447 u v) =
     L4KIMax447 (l4_ksubst_level488 ps us u) (l4_ksubst_level488 ps us v)) /\
  (l4_ksubst_level488 ps us (L4KParam447 n) = l4_klookup_level488 ps us n) /\
  (l4_ksubst_level488 ps us (L4KLevelMVar447 n) = L4KLevelMVar447 n)`;;

(* Term binders do not bind universe parameters. Preserve names, binderInfo,
   nonDep, projection fields, literal contents and each metadata wrapper. *)
let l4_ksubst_levels488 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_ksubst_levels488 ps us (L4KBVar447 i) = L4KBVar447 i) /\
  (l4_ksubst_levels488 ps us (L4KFVar447 n) = L4KFVar447 n) /\
  (l4_ksubst_levels488 ps us (L4KMVar447 n) = L4KMVar447 n) /\
  (l4_ksubst_levels488 ps us (L4KSort447 u) =
     L4KSort447 (l4_ksubst_level488 ps us u)) /\
  (l4_ksubst_levels488 ps us (L4KConst447 n vs) =
     L4KConst447 n (MAP (l4_ksubst_level488 ps us) vs)) /\
  (l4_ksubst_levels488 ps us (L4KApp447 f a) =
     L4KApp447 (l4_ksubst_levels488 ps us f) (l4_ksubst_levels488 ps us a)) /\
  (l4_ksubst_levels488 ps us (L4KLam447 n bi a b) =
     L4KLam447 n bi (l4_ksubst_levels488 ps us a) (l4_ksubst_levels488 ps us b)) /\
  (l4_ksubst_levels488 ps us (L4KPi447 n bi a b) =
     L4KPi447 n bi (l4_ksubst_levels488 ps us a) (l4_ksubst_levels488 ps us b)) /\
  (l4_ksubst_levels488 ps us (L4KLet447 n a v b nd) =
     L4KLet447 n (l4_ksubst_levels488 ps us a) (l4_ksubst_levels488 ps us v)
       (l4_ksubst_levels488 ps us b) nd) /\
  (l4_ksubst_levels488 ps us (L4KNatLit447 nat_value488) = L4KNatLit447 nat_value488) /\
  (l4_ksubst_levels488 ps us (L4KStrLit447 cs) = L4KStrLit447 cs) /\
  (l4_ksubst_levels488 ps us (L4KProj447 n i e) =
     L4KProj447 n i (l4_ksubst_levels488 ps us e)) /\
  (l4_ksubst_levels488 ps us (L4KMData447 e) =
     L4KMData447 (l4_ksubst_levels488 ps us e))`;;
