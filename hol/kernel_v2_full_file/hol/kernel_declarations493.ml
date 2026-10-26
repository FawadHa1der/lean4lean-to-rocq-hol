(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local Syntax.v and Inductive.v; see ../NOTICE493.txt.
   SOURCE ONLY / UNCOMPILED. Metadata records are claims, not admission. *)
needs "hol/kernel_syntax447.ml";;

let l4_kinductive_data_INDUCT493,l4_kinductive_data_RECURSION493 = define_type
 "l4_kinductive_data493 = L4KInductiveData493 num num (l4_name list)
   (l4_name list) num bool bool bool";;
let l4_kconstructor_data_INDUCT493,l4_kconstructor_data_RECURSION493 = define_type
 "l4_kconstructor_data493 = L4KConstructorData493 l4_name num num num bool";;
let l4_krecursor_rule_INDUCT493,l4_krecursor_rule_RECURSION493 = define_type
 "l4_krecursor_rule493 = L4KRecursorRule493 l4_name num l4_kexpr447";;
let l4_krecursor_data_INDUCT493,l4_krecursor_data_RECURSION493 = define_type
 "l4_krecursor_data493 = L4KRecursorData493 (l4_name list) num num num num
   (l4_krecursor_rule493 list) bool bool";;

let l4_kind_num_params493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_num_params493 (L4KInductiveData493 p i ns cs k rf xf uf) = p`;;
let l4_kind_num_indices493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_num_indices493 (L4KInductiveData493 p i ns cs k rf xf uf) = i`;;
let l4_kind_all493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_all493 (L4KInductiveData493 p i ns cs k rf xf uf) = ns`;;
let l4_kind_ctors493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_ctors493 (L4KInductiveData493 p i ns cs k rf xf uf) = cs`;;
let l4_kind_num_nested493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_num_nested493 (L4KInductiveData493 p i ns cs k rf xf uf) = k`;;
let l4_kind_is_rec493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_is_rec493 (L4KInductiveData493 p i ns cs k rf xf uf) = rf`;;
let l4_kind_is_reflexive493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_is_reflexive493 (L4KInductiveData493 p i ns cs k rf xf uf) = xf`;;
let l4_kind_is_unsafe493 = new_recursive_definition l4_kinductive_data_RECURSION493
 `l4_kind_is_unsafe493 (L4KInductiveData493 p i ns cs k rf xf uf) = uf`;;

let l4_kctor_induct493 = new_recursive_definition l4_kconstructor_data_RECURSION493
 `l4_kctor_induct493 (L4KConstructorData493 n i p k uf) = n`;;
let l4_kctor_index493 = new_recursive_definition l4_kconstructor_data_RECURSION493
 `l4_kctor_index493 (L4KConstructorData493 n i p k uf) = i`;;
let l4_kctor_num_params493 = new_recursive_definition l4_kconstructor_data_RECURSION493
 `l4_kctor_num_params493 (L4KConstructorData493 n i p k uf) = p`;;
let l4_kctor_num_fields493 = new_recursive_definition l4_kconstructor_data_RECURSION493
 `l4_kctor_num_fields493 (L4KConstructorData493 n i p k uf) = k`;;
let l4_kctor_is_unsafe493 = new_recursive_definition l4_kconstructor_data_RECURSION493
 `l4_kctor_is_unsafe493 (L4KConstructorData493 n i p k uf) = uf`;;

let l4_krule_ctor493 = new_recursive_definition l4_krecursor_rule_RECURSION493
 `l4_krule_ctor493 (L4KRecursorRule493 n k rhs) = n`;;
let l4_krule_nfields493 = new_recursive_definition l4_krecursor_rule_RECURSION493
 `l4_krule_nfields493 (L4KRecursorRule493 n k rhs) = k`;;
let l4_krule_rhs493 = new_recursive_definition l4_krecursor_rule_RECURSION493
 `l4_krule_rhs493 (L4KRecursorRule493 n k rhs) = rhs`;;

let l4_krec_all493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_all493 (L4KRecursorData493 ns p i m k rs kf uf) = ns`;;
let l4_krec_num_params493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_num_params493 (L4KRecursorData493 ns p i m k rs kf uf) = p`;;
let l4_krec_num_indices493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_num_indices493 (L4KRecursorData493 ns p i m k rs kf uf) = i`;;
let l4_krec_num_motives493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_num_motives493 (L4KRecursorData493 ns p i m k rs kf uf) = m`;;
let l4_krec_num_minors493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_num_minors493 (L4KRecursorData493 ns p i m k rs kf uf) = k`;;
let l4_krec_rules493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_rules493 (L4KRecursorData493 ns p i m k rs kf uf) = rs`;;
let l4_krec_k493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_k493 (L4KRecursorData493 ns p i m k rs kf uf) = kf`;;
let l4_krec_is_unsafe493 = new_recursive_definition l4_krecursor_data_RECURSION493
 `l4_krec_is_unsafe493 (L4KRecursorData493 ns p i m k rs kf uf) = uf`;;

let l4_kprimitive_INDUCT493,l4_kprimitive_RECURSION493 = define_type
 "l4_kprimitive493 = L4KPNatAdd493 | L4KPNatPred493 | L4KPNatSub493 |
 L4KPNatMul493 | L4KPNatPow493 | L4KPNatGcd493 | L4KPNatMod493 | L4KPNatDiv493 |
 L4KPNatBEq493 | L4KPNatBLE493 | L4KPNatLAnd493 | L4KPNatLOr493 | L4KPNatXor493 |
 L4KPNatBitwise493 | L4KPNatShiftLeft493 | L4KPNatShiftRight493 | L4KPCharOfNat493 | L4KPStringOfList493";;
let l4_kprimitive_eqb493 = new_definition
 `l4_kprimitive_eqb493 (a:l4_kprimitive493) b <=> a = b`;;

let l4_kquotient_INDUCT493,l4_kquotient_RECURSION493 = define_type
 "l4_kquotient493 = L4KQType493 | L4KQCtor493 | L4KQLift493 | L4KQInd493";;
let l4_kdecl_kind_INDUCT493,l4_kdecl_kind_RECURSION493 = define_type
 "l4_kdecl_kind493 = L4KDAssumption493 | L4KDDefinition493 | L4KDTheorem493 |
 L4KDOpaque493 | L4KDUnsupported493 | L4KDInductive493 l4_kinductive_data493 |
 L4KDConstructor493 l4_kconstructor_data493 | L4KDRecursor493 l4_krecursor_data493 |
 L4KDPrimitive493 l4_kprimitive493 | L4KDQuotient493 l4_kquotient493 |
 L4KDUnsafe493 l4_kdecl_kind493 | L4KDPartial493";;

(* Regular heights are unbounded naturals, not truncated machine words. *)
let l4_khints_INDUCT493,l4_khints_RECURSION493 = define_type
 "l4_khints493 = L4KHintOpaque493 | L4KHintAbbrev493 | L4KHintRegular493 num";;
let l4_khints_lt493 = new_recursive_definition l4_khints_RECURSION493
 `(l4_khints_lt493 L4KHintOpaque493 b <=> ~(b = L4KHintOpaque493)) /\
 (l4_khints_lt493 L4KHintAbbrev493 b <=> F) /\
 (l4_khints_lt493 (L4KHintRegular493 n) b <=>
   match b with
   | L4KHintOpaque493 -> F
   | L4KHintAbbrev493 -> T
   | L4KHintRegular493 m -> n < m)`;;

let l4_kdeclaration_INDUCT493,l4_kdeclaration_RECURSION493 = define_type
 "l4_kdeclaration493 = L4KDeclaration493 l4_name (l4_name list) l4_kexpr447
   (l4_kexpr447 option) l4_kdecl_kind493 l4_khints493";;
let l4_kdecl_name493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_name493 (L4KDeclaration493 n ps ty value kind hints) = n`;;
let l4_kdecl_params493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_params493 (L4KDeclaration493 n ps ty value kind hints) = ps`;;
let l4_kdecl_type493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_type493 (L4KDeclaration493 n ps ty value kind hints) = ty`;;
let l4_kdecl_value493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_value493 (L4KDeclaration493 n ps ty value kind hints) = value`;;
let l4_kdecl_kind493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_kind493 (L4KDeclaration493 n ps ty value kind hints) = kind`;;
let l4_kdecl_hints493 = new_recursive_definition l4_kdeclaration_RECURSION493
 `l4_kdecl_hints493 (L4KDeclaration493 n ps ty value kind hints) = hints`;;

let l4_keffective_hints493 = new_definition
 `l4_keffective_hints493 d =
   match l4_kdecl_kind493 d with
   | L4KDDefinition493 -> l4_kdecl_hints493 d
   | L4KDPrimitive493 p -> l4_kdecl_hints493 d
   | _ -> L4KHintOpaque493`;;

let l4_kfind_decl493 = new_recursive_definition list_RECURSION
 `(l4_kfind_decl493 [] n = NONE) /\
 (l4_kfind_decl493 (CONS d env) n =
   if n = l4_kdecl_name493 d then SOME d else l4_kfind_decl493 env n)`;;

let l4_kind_spec_INDUCT493,l4_kind_spec_RECURSION493 = define_type
 "l4_kind_spec493 = L4KIndSpec493 l4_kdeclaration493 (l4_kdeclaration493 list)";;
let l4_kspec_decl493 = new_recursive_definition l4_kind_spec_RECURSION493
 `l4_kspec_decl493 (L4KIndSpec493 d cs) = d`;;
let l4_kspec_ctors493 = new_recursive_definition l4_kind_spec_RECURSION493
 `l4_kspec_ctors493 (L4KIndSpec493 d cs) = cs`;;
