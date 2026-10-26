(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed conditional admission properties. UNCOMPILED / NOT RUN.
   No logical/environment preservation theorem is claimed by these equations. *)
needs "hol/ordinary_admission620.ml";;

let l4_admit_header_first620 = prove
 (`!fuel env hints n ps ty body reason.
   l4_check_header607 fuel env n ps ty = L4KReject491 reason ==>
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputSafe607) =
     L4KReject491 reason`,
  SIMP_TAC [l4_admit620;l4_kr_bind491]);;

let l4_admit_body_scope_before_typing620 = prove
 (`!fuel env hints n ps ty body.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\ ~l4_kscoped447 body 0 ==>
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputSafe607) =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit620;l4_kr_bind491]);;

let l4_admit_body_typing_before_classification620 = prove
 (`!fuel env hints n ps ty body reason.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\ l4_kscoped447 body 0 /\
   l4_check597 fuel env ps l4_kempty_context532 body ty = L4KReject491 reason ==>
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputSafe607) =
     L4KReject491 reason`,
  SIMP_TAC [l4_admit620;l4_kr_bind491]);;

let l4_admit_classification_decline_before_insert620 = prove
 (`!fuel env hints n ps ty body reason.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\ l4_kscoped447 body 0 /\
   l4_check597 fuel env ps l4_kempty_context532 body ty = L4KAccept491 one /\
   l4_classify_primitive620 fuel env n ps ty body = L4KDecline491 reason ==>
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputSafe607) =
     L4KDecline491 reason`,
  SIMP_TAC [l4_admit620;l4_kr_bind491]);;

let l4_admit_checked_kind_and_hints620 = prove
 (`!fuel env hints n ps ty body primitive.
   l4_check_header607 fuel env n ps ty = L4KAccept491 one /\ l4_kscoped447 body 0 /\
   l4_check597 fuel env ps l4_kempty_context532 body ty = L4KAccept491 one /\
   l4_classify_primitive620 fuel env n ps ty body = L4KAccept491 primitive ==>
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputSafe607) =
     L4KAccept491 (CONS
       (L4KDeclaration493 n ps ty (SOME body)
         (match primitive with | SOME op -> L4KDPrimitive493 op | NONE -> L4KDDefinition493)
         hints) env)`,
  SIMP_TAC [l4_admit620;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_admit_partial_unsafe_still_decline620 = prove
 (`!fuel env hints n ps ty body.
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputPartial607) =
     L4KDecline491 L4KUnsupportedDeclaration491 /\
   l4_admit620 fuel env (L4InputDefinition607 hints n ps ty body L4InputUnsafe607) =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  REWRITE_TAC [l4_admit620;l4_admit_basic607]);;

let l4_check_declarations_empty620 = prove
 (`!fuel env. l4_check_declarations620 [] fuel env = L4KAccept491 env`,
  REWRITE_TAC [l4_check_declarations620]);;

let l4_check_declarations_order620 = prove
 (`!input inputs fuel env next.
   l4_admit620 fuel env input = L4KAccept491 next ==>
   l4_check_declarations620 (CONS input inputs) fuel env =
     l4_check_declarations620 inputs fuel next`,
  SIMP_TAC [l4_check_declarations620;l4_kr_bind491]);;
