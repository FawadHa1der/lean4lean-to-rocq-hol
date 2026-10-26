(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447/491/493 port of local Rocq Checker.v270-323.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE544.txt. *)
needs "hol/literal_readiness533.ml";;
needs "hol/nested_parameters491.ml";;
needs "Library/bitsize.ml";;
needs "Library/prime.ml";;

(* A finite fold over the input-derived width, not caller resource fuel or a
   fixed-width machine word. Public uses below have operation F F = F.
   Universal correspondence with Rocq N.land/lor/lxor remains to be proved. *)
let l4_core_bitfold544 = new_recursive_definition num_RECURSION
 `(l4_core_bitfold544 0 operation a b = 0) /\
  (l4_core_bitfold544 (SUC width) operation a b =
     (if operation (ODD a) (ODD b) then 1 else 0) +
     2 * l4_core_bitfold544 width operation (a DIV 2) (b DIV 2))`;;

let l4_core_bitop544 = new_definition
 `l4_core_bitop544 operation a b =
   l4_core_bitfold544 (MAX (bitsize a) (bitsize b)) operation a b`;;

let l4_core_nat_value544 = new_definition
 `l4_core_nat_value544 e =
   match e with
   | L4KNatLit447 n -> SOME n
   | L4KConst447 n us ->
       if us = [] /\ n = l4_core_zero_name533 then SOME 0 else NONE
   | _ -> NONE`;;

let l4_core_nat_constructor544 = new_definition
 `l4_core_nat_constructor544 n =
   if n = 0 then L4KConst447 l4_core_zero_name533 []
   else L4KApp447 (L4KConst447 l4_core_succ_name533 []) (L4KNatLit447 (n - 1))`;;

(* Natural subtraction makes bitsize 0 - 1 = 0, matching N.log2 0.
   Keep this shortcut BEFORE the budget test, including at fuel zero. *)
let l4_core_shiftr544 = new_definition
 `l4_core_shiftr544 (fuel:num) a b =
   if bitsize a - 1 < b then L4KAccept491 0
   else if b <= fuel then L4KAccept491 (a DIV (2 EXP b))
   else L4KDecline491 L4KOutOfFuel491`;;

let l4_core_binary_nat544 = new_definition
 `l4_core_binary_nat544 (fuel:num) env op a b =
   let numeric = \n. L4KAccept491 (SOME (L4KNatLit447 n)) in
   let bounded = \operation:num->num->num.
     if b <= fuel then numeric (operation a b)
     else L4KDecline491 L4KOutOfFuel491 in
   let boolean = \answer.
     if l4_core_bool_ready533 env then
       L4KAccept491
         (SOME (L4KConst447 (if answer then l4_core_true_name533
                            else l4_core_false_name533) []))
     else L4KDecline491 L4KUnsupportedExpression491 in
   match op with
   | L4KPNatAdd493 -> numeric (a + b)
   | L4KPNatPred493 -> L4KAccept491 NONE
   | L4KPNatSub493 -> numeric (a - b)
   | L4KPNatMul493 -> numeric (a * b)
   | L4KPNatPow493 -> bounded (\x y. x EXP y)
   | L4KPNatGcd493 -> numeric (gcd(a,b))
   | L4KPNatMod493 -> numeric (a MOD b)
   | L4KPNatDiv493 -> numeric (a DIV b)
   | L4KPNatBEq493 -> boolean (a = b)
   | L4KPNatBLE493 -> boolean (a <= b)
   | L4KPNatLAnd493 -> numeric (l4_core_bitop544 (\x y. x /\ y) a b)
   | L4KPNatLOr493 -> numeric (l4_core_bitop544 (\x y. x \/ y) a b)
   | L4KPNatXor493 -> numeric (l4_core_bitop544 (\x y. ~(x <=> y)) a b)
   | L4KPNatBitwise493 -> L4KAccept491 NONE
   | L4KPNatShiftLeft493 -> bounded (\x y. x * 2 EXP y)
   | L4KPNatShiftRight493 ->
       l4_kr_bind491 (l4_core_shiftr544 fuel a b) numeric
   | L4KPCharOfNat493 -> L4KAccept491 NONE
   | L4KPStringOfList493 -> L4KAccept491 NONE`;;
