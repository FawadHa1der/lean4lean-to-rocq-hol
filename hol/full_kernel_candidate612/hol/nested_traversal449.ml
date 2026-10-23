(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed local Rocq nested-transform port. See ../NOTICE449.txt.
   SOURCE ONLY / UNCOMPILED. No default loader or admission integration. *)
needs "hol/kernel_syntax447.ml";;
needs "hol/nested_allocation437.ml";;

(* Only ind_local.il_id is observed by these operations. Both input lists
   contain those identifiers, not local types, values or binder annotations.
   Do not precheck total lengths: an early match precedes a malformed tail. *)
let l4_nested_lookup_local449 = new_recursive_definition list_RECURSION
 `(l4_nested_lookup_local449 [] fuel n ys =
   if ys = [] then L4NAOk437 (L4KFVar447 n) else L4NAUnsupported437) /\
 (l4_nested_lookup_local449 (CONS x xs) fuel n ys =
   if ys = [] then L4NAUnsupported437 else
   if fuel = 0 then L4NAOutOfFuel437 else
   if n = x then L4NAOk437 (L4KFVar447 (HD ys))
   else l4_nested_lookup_local449 xs (fuel - 1) n (TL ys))`;;

(* Structural recursion is used to define the same depth-fuel behavior as
   the Rocq fuel recursion. Replacements are free variables, never binders. *)
let l4_nested_rebase449 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_nested_rebase449 (L4KBVar447 i) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KBVar447 i)) /\
 (l4_nested_rebase449 (L4KFVar447 n) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437
   else l4_nested_lookup_local449 xs (fuel - 1) n ys) /\
 (l4_nested_rebase449 (L4KMVar447 n) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KMVar447 n)) /\
 (l4_nested_rebase449 (L4KSort447 u) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KSort447 u)) /\
 (l4_nested_rebase449 (L4KConst447 n us) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KConst447 n us)) /\
 (l4_nested_rebase449 (L4KApp447 a b) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 a (fuel - 1) xs ys) (\c.
   l4_na_bind437 (l4_nested_rebase449 b (fuel - 1) xs ys) (\d.
   L4NAOk437 (L4KApp447 c d)))) /\
 (l4_nested_rebase449 (L4KLam447 n bi a b) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 a (fuel - 1) xs ys) (\c.
   l4_na_bind437 (l4_nested_rebase449 b (fuel - 1) xs ys) (\d.
   L4NAOk437 (L4KLam447 n bi c d)))) /\
 (l4_nested_rebase449 (L4KPi447 n bi a b) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 a (fuel - 1) xs ys) (\c.
   l4_na_bind437 (l4_nested_rebase449 b (fuel - 1) xs ys) (\d.
   L4NAOk437 (L4KPi447 n bi c d)))) /\
 (l4_nested_rebase449 (L4KLet447 n a v b nd) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 a (fuel - 1) xs ys) (\c.
   l4_na_bind437 (l4_nested_rebase449 v (fuel - 1) xs ys) (\w.
   l4_na_bind437 (l4_nested_rebase449 b (fuel - 1) xs ys) (\d.
   L4NAOk437 (L4KLet447 n c w d nd))))) /\
 (l4_nested_rebase449 (L4KNatLit447 nat_value449) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KNatLit447 nat_value449)) /\
 (l4_nested_rebase449 (L4KStrLit447 s) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (L4KStrLit447 s)) /\
 (l4_nested_rebase449 (L4KProj447 n i e) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 e (fuel - 1) xs ys) (\a.
   L4NAOk437 (L4KProj447 n i a))) /\
 (l4_nested_rebase449 (L4KMData447 e) fuel xs ys =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_rebase449 e (fuel - 1) xs ys) (\a.
   L4NAOk437 (L4KMData447 a)))`;;

let l4_nested_has_new449 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_nested_has_new449 (L4KBVar447 i) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KFVar447 n) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KMVar447 n) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KSort447 u) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KConst447 n us) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 (MEM n ns)) /\
 (l4_nested_has_new449 (L4KApp447 a b) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_has_new449 a (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else l4_nested_has_new449 b (fuel - 1) ns)) /\
 (l4_nested_has_new449 (L4KLam447 n bi a b) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_has_new449 a (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else l4_nested_has_new449 b (fuel - 1) ns)) /\
 (l4_nested_has_new449 (L4KPi447 n bi a b) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_has_new449 a (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else l4_nested_has_new449 b (fuel - 1) ns)) /\
 (l4_nested_has_new449 (L4KLet447 n a v b nd) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_has_new449 a (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else
   l4_na_bind437 (l4_nested_has_new449 v (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else l4_nested_has_new449 b (fuel - 1) ns))) /\
 (l4_nested_has_new449 (L4KNatLit447 nat_value449) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KStrLit447 s) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 F) /\
 (l4_nested_has_new449 (L4KProj447 n i e) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else l4_nested_has_new449 e (fuel - 1) ns) /\
 (l4_nested_has_new449 (L4KMData447 e) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else l4_nested_has_new449 e (fuel - 1) ns)`;;

let l4_nested_any_new449 = new_recursive_definition list_RECURSION
 `(l4_nested_any_new449 [] fuel ns = L4NAOk437 F) /\
 (l4_nested_any_new449 (CONS e es) fuel ns =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_has_new449 e (fuel - 1) ns) (\found.
   if found then L4NAOk437 T else l4_nested_any_new449 es (fuel - 1) ns))`;;
