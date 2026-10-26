(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local rocq/Inductive.v; see ../NOTICE509.txt.
   SOURCE ONLY / UNCOMPILED. Raw member matching is NOT checked derivation. *)
needs "hol/nested_keys480.ml";;
needs "hol/kernel_universes488.ml";;
needs "hol/kernel_declarations493.ml";;
needs "hol/nested_parameters491.ml";;

(* Rocq comparator/list/list argument order. Core ALL2_DEF already guards
   HD/TL, compares heads before tails and rejects either unequal-length case. *)
let l4_klist_eqb509 = new_definition
 `l4_klist_eqb509 (cmp:A->A->bool) xs ys <=> ALL2 cmp xs ys`;;

let l4_ksame_names509 = new_definition
 `l4_ksame_names509 xs ys <=> l4_klist_eqb509 (\a b:l4_name. a = b) xs ys`;;

let l4_inductive_data_eqb509 = new_definition
 `l4_inductive_data_eqb509 a b <=>
   if l4_kind_num_params493 a = l4_kind_num_params493 b then
   if l4_kind_num_indices493 a = l4_kind_num_indices493 b then
   if l4_ksame_names509 (l4_kind_all493 a) (l4_kind_all493 b) then
   if l4_ksame_names509 (l4_kind_ctors493 a) (l4_kind_ctors493 b) then
   if l4_kind_num_nested493 a = l4_kind_num_nested493 b then
   if l4_kind_is_rec493 a = l4_kind_is_rec493 b then
   if l4_kind_is_reflexive493 a = l4_kind_is_reflexive493 b then
     l4_kind_is_unsafe493 a = l4_kind_is_unsafe493 b
   else F else F else F else F else F else F else F`;;

let l4_constructor_data_eqb509 = new_definition
 `l4_constructor_data_eqb509 a b <=>
   if l4_kctor_induct493 a = l4_kctor_induct493 b then
   if l4_kctor_index493 a = l4_kctor_index493 b then
   if l4_kctor_num_params493 a = l4_kctor_num_params493 b then
   if l4_kctor_num_fields493 a = l4_kctor_num_fields493 b then
     l4_kctor_is_unsafe493 a = l4_kctor_is_unsafe493 b
   else F else F else F else F`;;

(* Only source RHS universes are renamed. Use expr_eqb480, NEVER key_eq480:
   binder names/info and let nonDep are ignored, metadata wrappers are not. *)
let l4_rule_eqb509 = new_definition
 `l4_rule_eqb509 source_ps target_ps a b <=>
   if l4_krule_ctor493 a = l4_krule_ctor493 b then
   if l4_krule_nfields493 a = l4_krule_nfields493 b then
     l4_kexpr_eqb480
       (l4_ksubst_levels488 source_ps (MAP L4KParam447 target_ps) (l4_krule_rhs493 a))
       (l4_krule_rhs493 b)
   else F else F`;;

let l4_recursor_data_eqb509 = new_definition
 `l4_recursor_data_eqb509 source_ps target_ps a b <=>
   if l4_ksame_names509 (l4_krec_all493 a) (l4_krec_all493 b) then
   if l4_krec_num_params493 a = l4_krec_num_params493 b then
   if l4_krec_num_indices493 a = l4_krec_num_indices493 b then
   if l4_krec_num_motives493 a = l4_krec_num_motives493 b then
   if l4_krec_num_minors493 a = l4_krec_num_minors493 b then
   if l4_krec_k493 a = l4_krec_k493 b then
   if l4_krec_is_unsafe493 a = l4_krec_is_unsafe493 b then
     l4_klist_eqb509 (l4_rule_eqb509 source_ps target_ps) (l4_krec_rules493 a) (l4_krec_rules493 b)
   else F else F else F else F else F else F else F`;;

(* Rocq unit tt is HOL's existing singleton one:1, not bool or a new datatype.
   Check source uniqueness/arity, name, renamed type, then exact recursor kinds.
   Generated parameter uniqueness and all logical premises belong to callers. *)
let l4_verify_rec_metadata509 = new_definition
 `l4_verify_rec_metadata509 source generated =
   let sps = l4_kdecl_params493 source in
   let gps = l4_kdecl_params493 generated in
   if l4_names_unique437 sps then
     if LENGTH sps = LENGTH gps then
       if l4_kdecl_name493 source = l4_kdecl_name493 generated then
         if l4_kexpr_eqb480
           (l4_ksubst_levels488 sps (MAP L4KParam447 gps) (l4_kdecl_type493 source))
           (l4_kdecl_type493 generated) then
           (match (l4_kdecl_kind493 source,l4_kdecl_kind493 generated) with
            | (L4KDRecursor493 a,L4KDRecursor493 b) ->
              if l4_recursor_data_eqb509 sps gps a b then L4KAccept491 one
              else L4KReject491 L4KMalformedDeclaration491
            | _ -> L4KReject491 L4KMalformedDeclaration491)
         else L4KReject491 L4KMalformedDeclaration491
       else L4KReject491 L4KMalformedDeclaration491
     else L4KReject491 L4KMalformedDeclaration491
   else L4KReject491 L4KMalformedDeclaration491`;;

(* Only a pair of exact Recursor kinds takes the renamed-universe path.
   Other pairs compare raw parameter lists and raw types before kind metadata.
   Values and reducibility hints are deliberately not compared. *)
let l4_verify_member_metadata509 = new_definition
 `l4_verify_member_metadata509 source actual =
   match (l4_kdecl_kind493 source,l4_kdecl_kind493 actual) with
   | (L4KDRecursor493 a,L4KDRecursor493 b) -> l4_verify_rec_metadata509 source actual
   | _ ->
     if l4_kdecl_name493 source = l4_kdecl_name493 actual then
       if l4_ksame_names509 (l4_kdecl_params493 source) (l4_kdecl_params493 actual) then
         if l4_kexpr_eqb480 (l4_kdecl_type493 source) (l4_kdecl_type493 actual) then
           (match (l4_kdecl_kind493 source,l4_kdecl_kind493 actual) with
            | (L4KDInductive493 a,L4KDInductive493 b) ->
              if l4_inductive_data_eqb509 a b then L4KAccept491 one
              else L4KReject491 L4KMalformedDeclaration491
            | (L4KDConstructor493 a,L4KDConstructor493 b) ->
              if l4_constructor_data_eqb509 a b then L4KAccept491 one
              else L4KReject491 L4KMalformedDeclaration491
            | _ -> L4KReject491 L4KMalformedDeclaration491)
         else L4KReject491 L4KMalformedDeclaration491
       else L4KReject491 L4KMalformedDeclaration491
     else L4KReject491 L4KMalformedDeclaration491`;;

(* Sources drive recursion; actual lookup is first-row. On success remove ALL
   rows of that name, not just the matched row. This assumes a derived actual
   environment; it neither derives declarations nor proves their uniqueness. *)
let l4_verify_members509 = new_recursive_definition list_RECURSION
 `(l4_verify_members509 [] actual =
   if LENGTH actual = 0 then L4KAccept491 one else L4KReject491 L4KMalformedDeclaration491) /\
 (l4_verify_members509 (CONS source sources) actual =
   match l4_kfind_decl493 actual (l4_kdecl_name493 source) with
   | NONE -> L4KReject491 L4KMalformedDeclaration491
   | SOME derived ->
     l4_kr_bind491 (l4_verify_member_metadata509 source derived)
       (\ignored. l4_verify_members509 sources
         (FILTER (\d. ~(l4_kdecl_name493 d = l4_kdecl_name493 source)) actual)))`;;
