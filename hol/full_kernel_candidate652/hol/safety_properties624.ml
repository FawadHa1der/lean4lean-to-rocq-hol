(* SPDX-License-Identifier: Apache-2.0. Proposed scripts, ALL UNCOMPILED. *)
needs "hol/safety_admission624.ml";;

let l4_safety_view_preserves_payload624 = prove
 (`!mode d.
   l4_kdecl_name493 (l4_checking_view624 mode d) = l4_kdecl_name493 d /\
   l4_kdecl_params493 (l4_checking_view624 mode d) = l4_kdecl_params493 d /\
   l4_kdecl_type493 (l4_checking_view624 mode d) = l4_kdecl_type493 d /\
   l4_kdecl_value493 (l4_checking_view624 mode d) = l4_kdecl_value493 d /\
   l4_kdecl_hints493 (l4_checking_view624 mode d) = l4_kdecl_hints493 d`,
  REWRITE_TAC [l4_checking_view624;LET_DEF;LET_END_DEF;l4_kdecl_name493;
    l4_kdecl_params493;l4_kdecl_type493;l4_kdecl_value493;l4_kdecl_hints493]);;
let l4_safety_safe_view_keeps_partial624 = prove
 (`!n ps ty value hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputSafe607
     (L4KDeclaration493 n ps ty value L4KDPartial493 hints)) = L4KDPartial493`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_safe_view_keeps_unsafe624 = prove
 (`!n ps ty value inner hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputSafe607
     (L4KDeclaration493 n ps ty value (L4KDUnsafe493 inner) hints)) = L4KDUnsafe493 inner`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_partial_view_keeps_unsafe624 = prove
 (`!n ps ty value inner hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputPartial607
     (L4KDeclaration493 n ps ty value (L4KDUnsafe493 inner) hints)) = L4KDUnsafe493 inner`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_unsafe_unwraps_once624 = prove
 (`!n ps ty value inner hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputUnsafe607
     (L4KDeclaration493 n ps ty value (L4KDUnsafe493 (L4KDUnsafe493 inner)) hints)) =
     L4KDUnsafe493 inner`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_partial_view624 = prove
 (`!n ps ty value hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputPartial607
     (L4KDeclaration493 n ps ty value L4KDPartial493 hints)) = L4KDDefinition493`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_unsafe_views_partial624 = prove
 (`!n ps ty value hints.
   l4_kdecl_kind493 (l4_checking_view624 L4InputUnsafe607
     (L4KDeclaration493 n ps ty value L4KDPartial493 hints)) = L4KDDefinition493`,
  REWRITE_TAC [l4_checking_view624;l4_kdecl_kind493;LET_DEF;LET_END_DEF]);;
let l4_safety_restricted_markers624 = prove
 (`l4_safety_kind624 L4InputSafe607 = L4KDDefinition493 /\
   l4_safety_kind624 L4InputPartial607 = L4KDPartial493 /\
   l4_safety_kind624 L4InputUnsafe607 = L4KDUnsafe493 L4KDDefinition493`,
  REWRITE_TAC [l4_safety_kind624]);;
let l4_safety_reserved_name_first624 = prove
 (`!n. l4_name_mem437 n l4_reserved_names607 ==>
   l4_safe_name624 n = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_safe_name624]);;
let l4_safety_body_scope_first624 = prove
 (`!fuel env ps ty value. ~l4_kscoped447 value 0 ==>
   l4_check_value624 fuel env ps ty value = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_check_value624]);;
let l4_safety_body_concrete_checker624 = prove
 (`!fuel env ps ty value. l4_kscoped447 value 0 ==>
   l4_check_value624 fuel env ps ty value = l4_check597 fuel env ps l4_kempty_context532 value ty`,
  SIMP_TAC [l4_check_value624]);;
let l4_safety_unsafe_axiom_original_env624 = prove
 (`!fuel env n ps ty.
   l4_safe_name624 n = L4KAccept491 one /\
   l4_check_header607 fuel (l4_safety_environment624 L4InputUnsafe607 env) n ps ty =
     L4KAccept491 one ==>
   l4_admit_extended624 fuel env (L4InputAxiom607 n ps ty T) =
     L4KAccept491 (CONS (l4_restricted_constant624 n ps ty NONE
       (L4KDUnsafe493 L4KDAssumption493)) env)`,
  SIMP_TAC [l4_admit_extended624;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
let l4_safety_unsafe_definition_original_env624 = prove
 (`!fuel env hints n ps ty value.
   l4_safe_name624 n = L4KAccept491 one /\
   l4_check_header607 fuel (l4_safety_environment624 L4InputUnsafe607 env) n ps ty =
     L4KAccept491 one /\
   l4_check_value624 fuel
     (CONS (l4_restricted_constant624 n ps ty NONE L4KDAssumption493)
       (l4_safety_environment624 L4InputUnsafe607 env)) ps ty value = L4KAccept491 one ==>
   l4_admit_extended624 fuel env
     (L4InputDefinition607 hints n ps ty value L4InputUnsafe607) =
     L4KAccept491 (CONS (l4_restricted_definition624 hints n ps ty value
       (L4KDUnsafe493 L4KDDefinition493)) env)`,
  SIMP_TAC [l4_admit_extended624;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
let l4_safety_partial_definition_original_env624 = prove
 (`!fuel env hints n ps ty value.
   l4_safe_name624 n = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   l4_check_value624 fuel env ps ty value = L4KAccept491 one ==>
   l4_admit_extended624 fuel env
     (L4InputDefinition607 hints n ps ty value L4InputPartial607) =
     L4KAccept491 (CONS (l4_restricted_definition624 hints n ps ty value L4KDPartial493) env)`,
  SIMP_TAC [l4_admit_extended624;l4_kr_bind491]);;
let l4_safety_unsafe_opaque_original_env624 = prove
 (`!fuel env n ps ty value.
   l4_safe_name624 n = L4KAccept491 one /\
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   l4_check_value624 fuel env ps ty value = L4KAccept491 one ==>
   l4_admit_extended624 fuel env (L4InputOpaque607 n ps ty value T) =
     L4KAccept491 (CONS (l4_restricted_constant624 n ps ty (SOME value)
       (L4KDUnsafe493 L4KDOpaque493)) env)`,
  SIMP_TAC [l4_admit_extended624;l4_kr_bind491]);;
let l4_safety_safe_definition_uses_full_admission624 = prove
 (`!fuel env hints n ps ty value.
   l4_admit_extended624 fuel env (L4InputDefinition607 hints n ps ty value L4InputSafe607) =
     l4_admit620 fuel env (L4InputDefinition607 hints n ps ty value L4InputSafe607)`,
  REWRITE_TAC [l4_admit_extended624]);;
let l4_safety_theorem_uses_full_admission624 = prove
 (`!fuel env n ps ty value.
   l4_admit_extended624 fuel env (L4InputTheorem607 n ps ty value) =
     l4_admit620 fuel env (L4InputTheorem607 n ps ty value)`,
  REWRITE_TAC [l4_admit_extended624]);;
let l4_safety_empty_header_list624 = prove
 (`!fuel view ps mode. l4_check_mutual_headers624 [] fuel view ps mode = L4KAccept491 []`,
  REWRITE_TAC [l4_check_mutual_headers624]);;
let l4_safety_empty_value_list624 = prove
 (`!fuel view. l4_check_mutual_values624 [] fuel view = L4KAccept491 []`,
  REWRITE_TAC [l4_check_mutual_values624]);;
let l4_safety_mutual_mixed_modes624 = prove
 (`!fuel view ps mode inputs hints n qs ty value safety.
   ~(safety = mode) ==>
   l4_check_mutual_headers624
     (CONS (L4InputDefinition607 hints n qs ty value safety) inputs) fuel view ps mode =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_check_mutual_headers624;l4_safety_eqb624]);;
let l4_safety_mutual_mixed_universes624 = prove
 (`!fuel view ps mode inputs hints n qs ty value.
   ~(qs = ps) ==>
   l4_check_mutual_headers624
     (CONS (L4InputDefinition607 hints n qs ty value mode) inputs) fuel view ps mode =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_check_mutual_headers624;l4_safety_eqb624]);;
let l4_safety_mutual_safe_forbidden624 = prove
 (`!fuel env hints n ps ty value rest.
   l4_admit_mutual624 fuel env
     (CONS (L4InputDefinition607 hints n ps ty value L4InputSafe607) rest) =
     L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_admit_mutual624;l4_safety_eqb624]);;
let l4_safety_empty_mutual_forbidden624 = prove
 (`!fuel env. l4_admit_mutual624 fuel env [] = L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_admit_mutual624]);;
let l4_safety_mutual_original_env624 = prove
 (`!fuel env hints n ps ty value mode rest placeholders generated.
   ~(mode = L4InputSafe607) /\
   l4_names_unique437 (MAP l4_mutual_name624
     (CONS (L4InputDefinition607 hints n ps ty value mode) rest)) /\
   l4_check_mutual_headers624
     (CONS (L4InputDefinition607 hints n ps ty value mode) rest)
     fuel (l4_safety_environment624 mode env) ps mode = L4KAccept491 placeholders /\
   l4_check_mutual_values624
     (CONS (L4InputDefinition607 hints n ps ty value mode) rest)
     fuel (APPEND placeholders (l4_safety_environment624 mode env)) = L4KAccept491 generated ==>
   l4_admit_mutual624 fuel env
     (CONS (L4InputDefinition607 hints n ps ty value mode) rest) =
     L4KAccept491 (APPEND generated env)`,
  SIMP_TAC [l4_admit_mutual624;l4_safety_eqb624;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
