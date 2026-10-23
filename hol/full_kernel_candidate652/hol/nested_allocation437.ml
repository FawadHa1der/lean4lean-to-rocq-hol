(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider. Changed local policy port; see ../NOTICE437.txt.
   SOURCE ONLY / UNCOMPILED. No selected loader or checker integration. *)
needs "hol/nested_prefix420.ml";;

(* Name-first recursion; every branch checks fuel BEFORE equality.
   Bind propagates inability to decide, never invalidity or acceptance. *)
let l4_na_result_INDUCT437,l4_na_result_RECURSION437 = define_type
 "l4_na_result437 = L4NAOutOfFuel437 | L4NAUnsupported437 | L4NAOk437 A";;

let l4_na_bind437 = new_recursive_definition l4_na_result_RECURSION437
 `(l4_na_bind437 L4NAOutOfFuel437 f = L4NAOutOfFuel437) /\
 (l4_na_bind437 L4NAUnsupported437 f = L4NAUnsupported437) /\
 (l4_na_bind437 (L4NAOk437 x) f = f x)`;;

let l4_nested_replace_prefix437 = new_recursive_definition l4_name_RECURSION
 `(l4_nested_replace_prefix437 L4Anonymous fuel old replacement =
   if fuel = 0 then L4NAOutOfFuel437
   else if L4Anonymous = old then L4NAOk437 replacement
   else L4NAUnsupported437) /\
 (l4_nested_replace_prefix437 (L4String p s) fuel old replacement =
   if fuel = 0 then L4NAOutOfFuel437
   else if L4String p s = old then L4NAOk437 replacement
   else l4_na_bind437 (l4_nested_replace_prefix437 p (fuel - 1) old replacement)
     (\q. L4NAOk437 (L4String q s))) /\
 (l4_nested_replace_prefix437 (L4Numeric p k) fuel old replacement =
   if fuel = 0 then L4NAOutOfFuel437
   else if L4Numeric p k = old then L4NAOk437 replacement
   else l4_na_bind437 (l4_nested_replace_prefix437 p (fuel - 1) old replacement)
     (\q. L4NAOk437 (L4Numeric q k)))`;;

let l4_nested_rename_ctors437 = new_recursive_definition list_RECURSION
 `(l4_nested_rename_ctors437 [] fuel old aux = L4NAOk437 []) /\
 (l4_nested_rename_ctors437 (CONS c cs) fuel old aux =
   l4_na_bind437 (l4_nested_replace_prefix437 c fuel old aux)
     (\renamed. l4_na_bind437 (l4_nested_rename_ctors437 cs fuel old aux)
       (\rest. L4NAOk437 (CONS renamed rest))))`;;

let l4_nested_aux_name437 = new_definition
 `l4_nested_aux_name437 i =
 L4Numeric (L4String L4Anonymous [95;114;111;99;113;95;110;101;115;116;101;100]) i`;;

let l4_nested_rec_name437 = new_definition
 `l4_nested_rec_name437 n = L4String n [114;101;99]`;;

let l4_name_mem437 = new_definition
 `l4_name_mem437 (n:l4_name) ns <=> MEM n ns`;;

let l4_names_unique437 = new_recursive_definition list_RECURSION
 `(l4_names_unique437 [] <=> T) /\
 (l4_names_unique437 (CONS n ns) <=> ~l4_name_mem437 n ns /\ l4_names_unique437 ns)`;;

let l4_nested_reserved437 = new_definition
 `l4_nested_reserved437 aux renamed = CONS aux (CONS (l4_nested_rec_name437 aux) renamed)`;;

let l4_nested_blocked437 = new_definition
 `l4_nested_blocked437 used reserved <=>
 EX (\n. l4_name_mem437 n used) reserved \/ ~l4_names_unique437 reserved`;;

let l4_nested_unique_aux437 = new_recursive_definition num_RECURSION
 `(l4_nested_unique_aux437 0 used old ctors idx = L4NAOutOfFuel437) /\
 (l4_nested_unique_aux437 (SUC fuel) used old ctors idx =
   l4_na_bind437 (l4_nested_rename_ctors437 ctors fuel old (l4_nested_aux_name437 idx))
     (\renamed.
       if l4_nested_blocked437 used
         (l4_nested_reserved437 (l4_nested_aux_name437 idx) renamed)
       then l4_nested_unique_aux437 fuel used old ctors (SUC idx)
       else L4NAOk437 (l4_nested_aux_name437 idx,renamed,SUC idx)))`;;
