(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447/493 HOL port of local Checker.v65-134.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE533.txt. Not admission. *)
needs "hol/kernel_context532.ml";;
needs "hol/member_verification509.ml";;

(* Hierarchical name components, not single strings containing dots. *)
let l4_core_nat_name533 = new_definition
 `l4_core_nat_name533 = L4String L4Anonymous [78;97;116]`;;
let l4_core_zero_name533 = new_definition
 `l4_core_zero_name533 = L4String l4_core_nat_name533 [122;101;114;111]`;;
let l4_core_succ_name533 = new_definition
 `l4_core_succ_name533 = L4String l4_core_nat_name533 [115;117;99;99]`;;
let l4_core_bool_name533 = new_definition
 `l4_core_bool_name533 = L4String L4Anonymous [66;111;111;108]`;;
let l4_core_false_name533 = new_definition
 `l4_core_false_name533 = L4String l4_core_bool_name533 [102;97;108;115;101]`;;
let l4_core_true_name533 = new_definition
 `l4_core_true_name533 = L4String l4_core_bool_name533 [116;114;117;101]`;;
let l4_core_char_name533 = new_definition
 `l4_core_char_name533 = L4String L4Anonymous [67;104;97;114]`;;
let l4_core_char_of_nat533 = new_definition
 `l4_core_char_of_nat533 = L4String l4_core_char_name533 [111;102;78;97;116]`;;
let l4_core_string_name533 = new_definition
 `l4_core_string_name533 = L4String L4Anonymous [83;116;114;105;110;103]`;;
let l4_core_string_of_list533 = new_definition
 `l4_core_string_of_list533 = L4String l4_core_string_name533 [111;102;76;105;115;116]`;;
let l4_core_nat533 = new_definition
 `l4_core_nat533 = L4KConst447 l4_core_nat_name533 []`;;

let l4_core_ctor_shape533 = new_definition
 `l4_core_ctor_shape533 env n parent idx fields ty <=>
   match l4_kfind_decl493 env n with
   | NONE -> F
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDConstructor493 c ->
        l4_kctor_induct493 c = parent /\
        l4_kctor_index493 c = idx /\
        l4_kctor_num_params493 c = 0 /\
        l4_kctor_num_fields493 c = fields /\
        ~l4_kctor_is_unsafe493 c /\
        LENGTH (l4_kdecl_params493 d) = 0 /\
        l4_kexpr_eqb480 (l4_kdecl_type493 d) ty
      | _ -> F)`;;

let l4_core_nat_ready533 = new_definition
 `l4_core_nat_ready533 env <=>
   match l4_kfind_decl493 env l4_core_nat_name533 with
   | NONE -> F
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDInductive493 i ->
        LENGTH (l4_kdecl_params493 d) = 0 /\
        l4_kexpr_eqb480 (l4_kdecl_type493 d) (L4KSort447 (L4KSucc447 L4KZero447)) /\
        l4_kind_num_params493 i = 0 /\
        l4_kind_num_indices493 i = 0 /\
        ~l4_kind_is_unsafe493 i /\
        l4_klist_eqb509 (\a b:l4_name. a = b) (l4_kind_ctors493 i)
          [l4_core_zero_name533;l4_core_succ_name533] /\
        l4_core_ctor_shape533 env l4_core_zero_name533 l4_core_nat_name533 0 0
          l4_core_nat533 /\
        l4_core_ctor_shape533 env l4_core_succ_name533 l4_core_nat_name533 1 1
          (L4KPi447 L4Anonymous L4KDefault447 l4_core_nat533 l4_core_nat533)
      | _ -> F)`;;

let l4_core_bool_ready533 = new_definition
 `l4_core_bool_ready533 env <=>
   match l4_kfind_decl493 env l4_core_bool_name533 with
   | NONE -> F
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDInductive493 i ->
        LENGTH (l4_kdecl_params493 d) = 0 /\
        l4_kexpr_eqb480 (l4_kdecl_type493 d) (L4KSort447 (L4KSucc447 L4KZero447)) /\
        l4_kind_num_params493 i = 0 /\
        l4_kind_num_indices493 i = 0 /\
        ~l4_kind_is_unsafe493 i /\
        l4_klist_eqb509 (\a b:l4_name. a = b) (l4_kind_ctors493 i)
          [l4_core_false_name533;l4_core_true_name533] /\
        l4_core_ctor_shape533 env l4_core_false_name533 l4_core_bool_name533 0 0
          (L4KConst447 l4_core_bool_name533 []) /\
        l4_core_ctor_shape533 env l4_core_true_name533 l4_core_bool_name533 1 0
          (L4KConst447 l4_core_bool_name533 [])
      | _ -> F)`;;

(* No additional type/arity/value/hint checks: these raw predicates rely on
   separately admitted environment metadata, exactly as the local reference. *)
let l4_core_string_ready533 = new_definition
 `l4_core_string_ready533 env <=>
   match (l4_kfind_decl493 env l4_core_char_of_nat533,
          l4_kfind_decl493 env l4_core_string_of_list533) with
   | (SOME c,SOME s) ->
     (match (l4_kdecl_kind493 c,l4_kdecl_kind493 s) with
      | (L4KDPrimitive493 L4KPCharOfNat493,L4KDPrimitive493 L4KPStringOfList493) ->
        l4_core_nat_ready533 env
      | _ -> F)
   | _ -> F`;;

(* Environment-first matches Rocq. Projection index,scoping,metavariables,
   declaration existence for constants and payload validity are checked elsewhere. *)
let l4_core_supported533 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_core_supported533 env (L4KBVar447 i) <=> T) /\
  (l4_core_supported533 env (L4KFVar447 n) <=> T) /\
  (l4_core_supported533 env (L4KMVar447 n) <=> T) /\
  (l4_core_supported533 env (L4KSort447 u) <=> T) /\
  (l4_core_supported533 env (L4KConst447 n us) <=> T) /\
  (l4_core_supported533 env (L4KApp447 a b) <=>
    l4_core_supported533 env a /\ l4_core_supported533 env b) /\
  (l4_core_supported533 env (L4KLam447 n bi a b) <=>
    l4_core_supported533 env a /\ l4_core_supported533 env b) /\
  (l4_core_supported533 env (L4KPi447 n bi a b) <=>
    l4_core_supported533 env a /\ l4_core_supported533 env b) /\
  (l4_core_supported533 env (L4KLet447 n a v b nd) <=>
    l4_core_supported533 env a /\ l4_core_supported533 env v /\ l4_core_supported533 env b) /\
  (l4_core_supported533 env (L4KNatLit447 nat_value533) <=> l4_core_nat_ready533 env) /\
  (l4_core_supported533 env (L4KStrLit447 bytes) <=> l4_core_string_ready533 env) /\
  (l4_core_supported533 env (L4KProj447 n i a) <=>
    match l4_core_inductive532 env n with
    | NONE -> F
    | SOME info -> l4_core_supported533 env a) /\
  (l4_core_supported533 env (L4KMData447 a) <=> l4_core_supported533 env a)`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_supported_nat899 = prove
 (`!env m. l4_core_supported533 env (L4KNatLit447 m) <=> l4_core_nat_ready533 env`,
  REWRITE_TAC[l4_core_supported533]);;

let l4_supported_name899 = prove
 (`!env name. l4_core_supported533 env (L4KFVar447 name)`,
  REWRITE_TAC[l4_core_supported533]);;
