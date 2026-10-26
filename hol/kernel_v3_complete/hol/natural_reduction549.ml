(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of local Checker.v325-405.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE549.txt.
   rec is an internal smaller-fuel method record,not a public verdict oracle. *)
needs "hol/kernel_control543.ml";;
needs "hol/kernel_naturals544.ml";;

let l4_core_reduce_nat_reference549 = new_definition
 `l4_core_reduce_nat_reference549 rec fuel env g e =
   if ~l4_core_nat_ready533 env then L4KAccept491 NONE else
   match l4_ksplit_app489 e with
   | (L4KConst447 n [],[a]) ->
       let op =
         if n = l4_core_succ_name533 then SOME T else
         (match l4_kfind_decl493 env n with
          | SOME d -> (match l4_kdecl_kind493 d with
                       | L4KDPrimitive493 L4KPNatPred493 -> SOME F
                       | _ -> NONE)
          | NONE -> NONE) in
       (match op with
        | SOME successor ->
          l4_kr_bind491 (l4_whnf_method543 rec g a) (\a.
            match l4_core_nat_value544 a with
            | SOME value -> L4KAccept491
                (SOME (L4KNatLit447 (if successor then SUC value else value - 1)))
            | NONE -> L4KAccept491 NONE)
        | NONE -> L4KAccept491 NONE)
   | (L4KConst447 n [],[a;b]) ->
       (match l4_kfind_decl493 env n with
        | SOME d ->
          (match l4_kdecl_kind493 d with
           | L4KDPrimitive493 L4KPNatBitwise493 -> L4KAccept491 NONE
           | L4KDPrimitive493 op ->
             l4_kr_bind491 (l4_whnf_method543 rec g a) (\a.
               l4_kr_bind491 (l4_whnf_method543 rec g b) (\b.
                 match (l4_core_nat_value544 a,l4_core_nat_value544 b) with
                 | (SOME av,SOME bv) -> l4_core_binary_nat544 fuel env op av bv
                 | _ -> L4KAccept491 NONE))
           | _ -> L4KAccept491 NONE)
        | NONE -> L4KAccept491 NONE)
   | _ -> L4KAccept491 NONE`;;

(* Delay readiness scanning until the head/arity/kind can use it. Both argument
   WHNFs must finish before numeral recognition,even when the first is not Nat. *)
let l4_core_reduce_nat549 = new_definition
 `l4_core_reduce_nat549 rec fuel env g e =
   match l4_ksplit_app489 e with
   | (L4KConst447 n [],[a]) ->
       let op =
         if n = l4_core_succ_name533 then SOME T else
         (match l4_kfind_decl493 env n with
          | SOME d -> (match l4_kdecl_kind493 d with
                       | L4KDPrimitive493 L4KPNatPred493 -> SOME F
                       | _ -> NONE)
          | NONE -> NONE) in
       (match op with
        | SOME successor ->
          if ~l4_core_nat_ready533 env then L4KAccept491 NONE else
          l4_kr_bind491 (l4_whnf_method543 rec g a) (\a.
            match l4_core_nat_value544 a with
            | SOME value -> L4KAccept491
                (SOME (L4KNatLit447 (if successor then SUC value else value - 1)))
            | NONE -> L4KAccept491 NONE)
        | NONE -> L4KAccept491 NONE)
   | (L4KConst447 n [],[a;b]) ->
       (match l4_kfind_decl493 env n with
        | SOME d ->
          (match l4_kdecl_kind493 d with
           | L4KDPrimitive493 L4KPNatBitwise493 -> L4KAccept491 NONE
           | L4KDPrimitive493 op ->
             if ~l4_core_nat_ready533 env then L4KAccept491 NONE else
             l4_kr_bind491 (l4_whnf_method543 rec g a) (\a.
               l4_kr_bind491 (l4_whnf_method543 rec g b) (\b.
                 match (l4_core_nat_value544 a,l4_core_nat_value544 b) with
                 | (SOME av,SOME bv) -> l4_core_binary_nat544 fuel env op av bv
                 | _ -> L4KAccept491 NONE))
           | _ -> L4KAccept491 NONE)
        | NONE -> L4KAccept491 NONE)
   | _ -> L4KAccept491 NONE`;;
