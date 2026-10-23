(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider. Changed local Rocq port; see ../NOTICE480.txt.
   SOURCE ONLY / UNCOMPILED. No default loader or admission integration. *)
needs "hol/kernel_syntax447.ml";;
needs "hol/nested_allocation437.ml";;

(* Syntax.expr_eqb, NOT raw expression equality or Lean metadata equality.
   Equality on names, levels and their lists is structural (no universe
   normalization). Their byte/natural encodings are inherited from447.
   Binder names/info and let nonDep are ignored; metadata wrappers are not.
   Explicit conditionals keep the recursive comparisons left-to-right. *)
let l4_kexpr_eqb480 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kexpr_eqb480 (L4KBVar447 i) y <=> y = L4KBVar447 i) /\
 (l4_kexpr_eqb480 (L4KFVar447 n) y <=> y = L4KFVar447 n) /\
 (l4_kexpr_eqb480 (L4KMVar447 n) y <=> y = L4KMVar447 n) /\
 (l4_kexpr_eqb480 (L4KSort447 u) y <=> y = L4KSort447 u) /\
 (l4_kexpr_eqb480 (L4KConst447 n us) y <=>
   match y with
   | L4KConst447 m vs -> if n = m then us = vs else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KApp447 a b) y <=>
   match y with
   | L4KApp447 c d -> if l4_kexpr_eqb480 a c then l4_kexpr_eqb480 b d else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KLam447 n bi a b) y <=>
   match y with
   | L4KLam447 m bj c d -> if l4_kexpr_eqb480 a c then l4_kexpr_eqb480 b d else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KPi447 n bi a b) y <=>
   match y with
   | L4KPi447 m bj c d -> if l4_kexpr_eqb480 a c then l4_kexpr_eqb480 b d else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KLet447 n a v b nd) y <=>
   match y with
   | L4KLet447 m c w d md ->
     if l4_kexpr_eqb480 a c then
       if l4_kexpr_eqb480 v w then l4_kexpr_eqb480 b d else F
     else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KNatLit447 nat_value480) y <=> y = L4KNatLit447 nat_value480) /\
 (l4_kexpr_eqb480 (L4KStrLit447 s) y <=> y = L4KStrLit447 s) /\
 (l4_kexpr_eqb480 (L4KProj447 n i a) y <=>
   match y with
   | L4KProj447 m j b ->
     if n = m then if i = j then l4_kexpr_eqb480 a b else F else F
   | _ -> F) /\
 (l4_kexpr_eqb480 (L4KMData447 a) y <=>
   match y with
   | L4KMData447 b -> l4_kexpr_eqb480 a b
   | _ -> F)`;;

(* Argument order is expression, fuel, expression, for structural recursion.
   Fuel is tested before shape/flags, even for mismatched constructors.
   Nonmatching shapes return true here; only key_eq supplies the eqb gate.
   Siblings each receive fuel-1, not a shared consumable fuel counter. *)
let l4_nested_same_flags480 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_nested_same_flags480 (L4KBVar447 i) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KFVar447 n) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KMVar447 n) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KSort447 u) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KConst447 n us) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KApp447 a b) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KApp447 c d ->
     l4_na_bind437 (l4_nested_same_flags480 a (fuel - 1) c) (\same.
       if same then l4_nested_same_flags480 b (fuel - 1) d else L4NAOk437 F)
   | _ -> L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KLam447 n bi a b) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KLam447 m bj c d ->
     l4_na_bind437 (l4_nested_same_flags480 a (fuel - 1) c) (\same.
       if same then l4_nested_same_flags480 b (fuel - 1) d else L4NAOk437 F)
   | _ -> L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KPi447 n bi a b) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KPi447 m bj c d ->
     l4_na_bind437 (l4_nested_same_flags480 a (fuel - 1) c) (\same.
       if same then l4_nested_same_flags480 b (fuel - 1) d else L4NAOk437 F)
   | _ -> L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KLet447 n a v b nd) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KLet447 m c w d md ->
     if nd = md then
       l4_na_bind437 (l4_nested_same_flags480 a (fuel - 1) c) (\same.
         if same then
           l4_na_bind437 (l4_nested_same_flags480 v (fuel - 1) w) (\same.
             if same then l4_nested_same_flags480 b (fuel - 1) d else L4NAOk437 F)
         else L4NAOk437 F)
     else L4NAOk437 F
   | _ -> L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KNatLit447 nat_value480) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KStrLit447 s) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KProj447 n i a) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KProj447 m j b -> l4_nested_same_flags480 a (fuel - 1) b
   | _ -> L4NAOk437 T) /\
 (l4_nested_same_flags480 (L4KMData447 a) fuel y =
   if fuel = 0 then L4NAOutOfFuel437 else
   match y with
   | L4KMData447 b -> l4_nested_same_flags480 a (fuel - 1) b
   | _ -> L4NAOk437 T)`;;

let l4_nested_key_eq480 = new_definition
 `l4_nested_key_eq480 fuel a b =
   if l4_kexpr_eqb480 a b then l4_nested_same_flags480 a fuel b else L4NAOk437 F`;;

(* List-first argument order. Empty mapping wins over zero fuel; a nonempty
   mapping spends one unit BEFORE key_eq, even when eqb would return false.
   The first match wins. Neither a failure nor a match visits the tail. *)
let l4_nested_find_mapping480 = new_recursive_definition list_RECURSION
 `(l4_nested_find_mapping480 [] fuel e = L4NAOk437 (NONE:l4_name option)) /\
 (l4_nested_find_mapping480 (CONS p ps) fuel e =
   if fuel = 0 then L4NAOutOfFuel437 else
   l4_na_bind437 (l4_nested_key_eq480 (fuel - 1) (FST p) e) (\same.
     if same then L4NAOk437 (SOME (SND p))
     else l4_nested_find_mapping480 ps (fuel - 1) e))`;;
