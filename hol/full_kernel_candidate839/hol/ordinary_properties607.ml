(* SPDX-License-Identifier: Apache-2.0. Proposed equations, ALL UNCOMPILED. *)
needs "hol/ordinary_admission607.ml";;

let l4_header_duplicate_first607 = prove
 (`!fuel env n ps ty d. l4_kfind_decl493 env n = SOME d ==>
   l4_check_header607 fuel env n ps ty = L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_check_header607]);;

let l4_header_universe_before_scope607 = prove
 (`!fuel env n ps ty. l4_kfind_decl493 env n = NONE /\ ~l4_names_unique437 ps ==>
   l4_check_header607 fuel env n ps ty = L4KReject491 L4KDuplicateUniverse491`,
  SIMP_TAC [l4_check_header607]);;

let l4_header_scope_before_inference607 = prove
 (`!fuel env n ps ty. l4_kfind_decl493 env n = NONE /\ l4_names_unique437 ps /\
   ~l4_kscoped447 ty 0 ==>
   l4_check_header607 fuel env n ps ty = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_check_header607]);;

let l4_header_inference_decline607 = prove
 (`!fuel env n ps ty reason. l4_kfind_decl493 env n = NONE /\
   l4_names_unique437 ps /\ l4_kscoped447 ty 0 /\
   l4_infer597 fuel env ps l4_kempty_context532 ty = L4KDecline491 reason ==>
   l4_check_header607 fuel env n ps ty = L4KDecline491 reason`,
  SIMP_TAC [l4_check_header607;l4_kr_bind491]);;

let l4_header_sort607 = prove
 (`!fuel env n ps ty inferred u. l4_kfind_decl493 env n = NONE /\
   l4_names_unique437 ps /\ l4_kscoped447 ty 0 /\
   l4_infer597 fuel env ps l4_kempty_context532 ty = L4KAccept491 inferred /\
   l4_whnf597 fuel env ps l4_kempty_context532 inferred = L4KAccept491 (L4KSort447 u) ==>
   l4_check_header607 fuel env n ps ty = L4KAccept491 one`,
  SIMP_TAC [l4_check_header607;l4_kr_bind491]);;

let l4_proposition_zero_universe607 = prove
 (`!fuel env ps ty inferred u.
   l4_infer597 fuel env ps l4_kempty_context532 ty = L4KAccept491 inferred /\
   l4_whnf597 fuel env ps l4_kempty_context532 inferred = L4KAccept491 (L4KSort447 u) /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 T ==>
   l4_check_proposition607 fuel env ps ty = L4KAccept491 one`,
  SIMP_TAC [l4_check_proposition607;l4_kr_bind491]);;

let l4_proposition_nonzero_universe607 = prove
 (`!fuel env ps ty inferred u.
   l4_infer597 fuel env ps l4_kempty_context532 ty = L4KAccept491 inferred /\
   l4_whnf597 fuel env ps l4_kempty_context532 inferred = L4KAccept491 (L4KSort447 u) /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 F ==>
   l4_check_proposition607 fuel env ps ty = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_check_proposition607;l4_kr_bind491]);;

let l4_proposition_no_fuel607 = prove
 (`!env ps ty. l4_check_proposition607 0 env ps ty = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_check_proposition607;l4_infer597;l4_checker597;
    l4_checker_mode597;l4_infer_method543;l4_kr_bind491]);;

let l4_checked_constant_header_first607 = prove
 (`!fuel env n ps ty body kind reason.
   l4_check_header607 fuel env n ps ty = L4KReject491 reason ==>
   l4_checked_constant607 fuel env n ps ty body kind = L4KReject491 reason`,
  SIMP_TAC [l4_checked_constant607;l4_kr_bind491]);;

let l4_checked_constant_no_body607 = prove
 (`!fuel env n ps ty kind.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one ==>
   l4_checked_constant607 fuel env n ps ty NONE kind =
   L4KAccept491 (CONS (L4KDeclaration493 n ps ty NONE kind L4KHintOpaque493) env)`,
  SIMP_TAC [l4_checked_constant607;l4_kr_bind491]);;

let l4_checked_constant_unscoped_body607 = prove
 (`!fuel env n ps ty value kind.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   ~l4_kscoped447 value 0 ==>
   l4_checked_constant607 fuel env n ps ty (SOME value) kind =
   L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_checked_constant607;l4_kr_bind491]);;

let l4_checked_constant_body_decline607 = prove
 (`!fuel env n ps ty value kind reason.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   l4_kscoped447 value 0 /\
   l4_check597 fuel env ps l4_kempty_context532 value ty = L4KDecline491 reason ==>
   l4_checked_constant607 fuel env n ps ty (SOME value) kind = L4KDecline491 reason`,
  SIMP_TAC [l4_checked_constant607;l4_kr_bind491]);;

let l4_checked_constant_checked_body607 = prove
 (`!fuel env n ps ty value kind.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\
   l4_kscoped447 value 0 /\
   l4_check597 fuel env ps l4_kempty_context532 value ty = L4KAccept491 one ==>
   l4_checked_constant607 fuel env n ps ty (SOME value) kind =
   L4KAccept491 (CONS (L4KDeclaration493 n ps ty (SOME value) kind L4KHintOpaque493) env)`,
  SIMP_TAC [l4_checked_constant607;l4_kr_bind491]);;

let l4_basic_unsafe_axiom607 = prove
 (`!fuel env n ps ty. l4_admit_basic607 fuel env (L4InputAxiom607 n ps ty T) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_admit_basic607]);;

let l4_basic_unsafe_opaque607 = prove
 (`!fuel env n ps ty body. l4_admit_basic607 fuel env (L4InputOpaque607 n ps ty body T) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_admit_basic607]);;

let l4_basic_reserved_theorem607 = prove
 (`!fuel env n ps ty body. l4_name_mem437 n l4_reserved_names607 ==>
   l4_admit_basic607 fuel env (L4InputTheorem607 n ps ty body) =
   L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_basic607]);;

let l4_basic_definition_explicit_decline607 = prove
 (`!fuel env hints n ps ty body safety.
   l4_admit_basic607 fuel env (L4InputDefinition607 hints n ps ty body safety) =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_admit_basic607]);;

let l4_basic_unsupported_decline607 = prove
 (`!fuel env. l4_admit_basic607 fuel env L4InputUnsupported607 =
   L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_admit_basic607]);;

let l4_basic_empty_unchanged607 = prove
 (`!fuel env. l4_check_basic_declarations607 [] fuel env = L4KAccept491 env`,
  REWRITE_TAC [l4_check_basic_declarations607]);;

let l4_basic_list_first_decline607 = prove
 (`!inputs fuel env input reason. l4_admit_basic607 fuel env input = L4KDecline491 reason ==>
   l4_check_basic_declarations607 (CONS input inputs) fuel env = L4KDecline491 reason`,
  SIMP_TAC [l4_check_basic_declarations607;l4_kr_bind491]);;

let l4_reserved_count607 = prove
 (`LENGTH l4_reserved_names607 = 24`,
  REWRITE_TAC [l4_reserved_names607;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
