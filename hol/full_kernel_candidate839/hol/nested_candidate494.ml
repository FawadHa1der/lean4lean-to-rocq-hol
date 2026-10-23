(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local NestedTransform.v; see ../NOTICE494.txt.
   SOURCE ONLY / UNCOMPILED. Candidate detection is not admission. *)
needs "hol/kernel_declarations493.ml";;
needs "hol/nested_parameters491.ml";;
needs "hol/nested_traversal449.ml";;

let l4_knested_work_INDUCT494,l4_knested_work_RECURSION494 = define_type
 "l4_knested_work494 = L4KNestedWork494 (l4_kind_spec493 list)
   ((l4_kexpr447 # l4_name) list) num num";;
let l4_knw_specs494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_knw_specs494 (L4KNestedWork494 specs mapping nextaux nextlocal) = specs`;;
let l4_knw_mapping494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_knw_mapping494 (L4KNestedWork494 specs mapping nextaux nextlocal) = mapping`;;
let l4_knw_next_aux494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_knw_next_aux494 (L4KNestedWork494 specs mapping nextaux nextlocal) = nextaux`;;
let l4_knw_next_local494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_knw_next_local494 (L4KNestedWork494 specs mapping nextaux nextlocal) = nextlocal`;;

let l4_nested_set_specs494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_nested_set_specs494 (L4KNestedWork494 specs mapping nextaux nextlocal) replacement =
   L4KNestedWork494 replacement mapping nextaux nextlocal`;;
let l4_nested_set_local494 = new_recursive_definition l4_knested_work_RECURSION494
 `l4_nested_set_local494 (L4KNestedWork494 specs mapping nextaux nextlocal) replacement =
   L4KNestedWork494 specs mapping nextaux replacement`;;

(* Total Rocq firstn semantics, rather than a partial EL-based prefix. *)
let l4_kfirstn494 = new_recursive_definition list_RECURSION
 `(l4_kfirstn494 [] count = []) /\
 (l4_kfirstn494 (CONS a args) count =
   if count = 0 then [] else CONS a (l4_kfirstn494 args (count - 1)))`;;

let l4_knested_names494 = new_definition
 `l4_knested_names494 w = MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) (l4_knw_specs494 w)`;;

let l4_nested_candidate494 = new_definition
 `l4_nested_candidate494 fuel env w e =
   let split = l4_ksplit_app489 e in
   let head = FST split in
   let args = SND split in
   if NULL args then L4KAccept491 NONE else
   match head with
   | L4KConst447 n us ->
     (match l4_kfind_decl493 env n with
      | NONE -> L4KAccept491 NONE
      | SOME d ->
        (match l4_kdecl_kind493 d with
         | L4KDInductive493 data ->
           if l4_kind_num_params493 data <= LENGTH args then
             let params = l4_kfirstn494 args (l4_kind_num_params493 data) in
             l4_kr_bind491
               (l4_kr_from_na491 (l4_nested_any_new449 params fuel (l4_knested_names494 w)))
               (\found. if found then
                 if ALL (\param. l4_kscoped447 param 0) params
                 then L4KAccept491 (SOME (d,data,us,args))
                 else L4KReject491 L4KMalformedDeclaration491
                else L4KAccept491 NONE)
           else L4KAccept491 NONE
         | _ -> L4KAccept491 NONE))
   | _ -> L4KAccept491 NONE`;;
