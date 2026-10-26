(* SPDX-License-Identifier: Apache-2.0. Proposed scripts, ALL UNCOMPILED.
   These are operational boundary lemmas, not a kernel soundness theorem. *)
needs "hol/checked_admission631.ml";;

let l4_derive_empty631 = prove
 (`!fuel env ps np. l4_derive_inductive631 fuel env ps np [] =
     L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_derive_inductive631]);;

let l4_derive_names_empty631 = prove
 (`l4_inductive_derived_names631 [] = []`,
  REWRITE_TAC [l4_inductive_derived_names631;LET_DEF;LET_END_DEF;MAP;ITLIST;APPEND]);;

let l4_derive_duplicate_names_first631 = prove
 (`!fuel env ps np first rest.
   ~l4_names_unique437 (l4_inductive_derived_names631 (CONS first rest)) ==>
   l4_derive_inductive631 fuel env ps np (CONS first rest) =
     L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_derive_inductive631;LET_DEF;LET_END_DEF]);;

let l4_derive_occupied_names631 = prove
 (`!fuel env ps np first rest.
   l4_names_unique437 (l4_inductive_derived_names631 (CONS first rest)) /\
   ~ALL (\n. l4_kfind_decl493 env n = NONE)
     (l4_inductive_derived_names631 (CONS first rest)) ==>
   l4_derive_inductive631 fuel env ps np (CONS first rest) =
     L4KReject491 L4KDuplicateDeclaration491`,
  SIMP_TAC [l4_derive_inductive631;LET_DEF;LET_END_DEF]);;

let l4_derive_duplicate_universes631 = prove
 (`!fuel env ps np first rest.
   l4_names_unique437 (l4_inductive_derived_names631 (CONS first rest)) /\
   ALL (\n. l4_kfind_decl493 env n = NONE)
     (l4_inductive_derived_names631 (CONS first rest)) /\
   ~l4_names_unique437 ps ==>
   l4_derive_inductive631 fuel env ps np (CONS first rest) =
     L4KReject491 L4KDuplicateUniverse491`,
  SIMP_TAC [l4_derive_inductive631;LET_DEF;LET_END_DEF]);;

let l4_nested_flag_empty631 = prove
 (`~l4_has_nested_inductive631 []`,
  REWRITE_TAC [l4_has_nested_inductive631;EX]);;

let l4_nested_flag_cons631 = prove
 (`!n ps ty value hints info rest.
   l4_has_nested_inductive631
     (CONS (L4KDeclaration493 n ps ty value (L4KDInductive493 info) hints) rest) <=>
   ~(l4_kind_num_nested493 info = 0) \/ l4_has_nested_inductive631 rest`,
  REWRITE_TAC [l4_has_nested_inductive631;EX;l4_kdecl_kind493]);;

let l4_nested_flag_ignores_wrapped631 = prove
 (`!n ps ty value hints info rest.
   l4_has_nested_inductive631
     (CONS (L4KDeclaration493 n ps ty value
       (L4KDUnsafe493 (L4KDInductive493 info)) hints) rest) =
   l4_has_nested_inductive631 rest`,
  REWRITE_TAC [l4_has_nested_inductive631;EX;l4_kdecl_kind493]);;

let l4_admit_preparation_reject_first631 = prove
 (`!fuel env types ctors recs reason.
   l4_prepare_inductive518 env types ctors recs = L4KReject491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491]);;

let l4_admit_preparation_decline631 = prove
 (`!fuel env types ctors recs reason.
   l4_prepare_inductive518 env types ctors recs = L4KDecline491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491]);;

let l4_admit_nested_decline631 = prove
 (`!fuel env types ctors recs ps np specs.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   l4_has_nested_inductive631 types ==>
   l4_admit_inductive631 fuel env types ctors recs =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491]);;

let l4_admit_derivation_reject631 = prove
 (`!fuel env types ctors recs ps np specs reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~l4_has_nested_inductive631 types /\
   l4_derive_inductive631 fuel env ps np specs = L4KReject491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491;FST;SND]);;

let l4_admit_derivation_decline631 = prove
 (`!fuel env types ctors recs ps np specs reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~l4_has_nested_inductive631 types /\
   l4_derive_inductive631 fuel env ps np specs = L4KDecline491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491;FST;SND]);;

let l4_admit_metadata_reject631 = prove
 (`!fuel env types ctors recs ps np specs generated reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~l4_has_nested_inductive631 types /\
   l4_derive_inductive631 fuel env ps np specs = L4KAccept491 generated /\
   l4_verify_members509 (APPEND types (APPEND ctors recs)) generated = L4KReject491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491;FST;SND]);;

let l4_admit_metadata_decline631 = prove
 (`!fuel env types ctors recs ps np specs generated reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~l4_has_nested_inductive631 types /\
   l4_derive_inductive631 fuel env ps np specs = L4KAccept491 generated /\
   l4_verify_members509 (APPEND types (APPEND ctors recs)) generated = L4KDecline491 reason ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491;FST;SND]);;

let l4_admit_generated_not_supplied631 = prove
 (`!fuel env types ctors recs ps np specs generated checked.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~l4_has_nested_inductive631 types /\
   l4_derive_inductive631 fuel env ps np specs = L4KAccept491 generated /\
   l4_verify_members509 (APPEND types (APPEND ctors recs)) generated = L4KAccept491 checked ==>
   l4_admit_inductive631 fuel env types ctors recs = L4KAccept491 (APPEND generated env)`,
  SIMP_TAC [l4_admit_inductive631;l4_kr_bind491;FST;SND]);;

let l4_bind_accept_inverse631 = prove
 (`!r:A l4_kresult491. !f:A->B l4_kresult491. !y:B.
   l4_kr_bind491 r f = L4KAccept491 y <=>
   ?x. r = L4KAccept491 x /\ f x = L4KAccept491 y`,
  MATCH_MP_TAC l4_kresult_INDUCT491 THEN
  REWRITE_TAC [l4_kr_bind491;distinctness "l4_kresult491";injectivity "l4_kresult491"] THEN
  MESON_TAC []);;

(* Inversion states the evidence actually required by successful admission.
   It does not assume that arbitrary supplied metadata was already checked. *)
let l4_admit_accept_evidence631 = prove
 (`!fuel env types ctors recs output.
   l4_admit_inductive631 fuel env types ctors recs = L4KAccept491 output <=>
   ?prepared generated. ?checked:1.
     l4_prepare_inductive518 env types ctors recs = L4KAccept491 prepared /\
     ~l4_has_nested_inductive631 types /\
     l4_derive_inductive631 fuel env (FST prepared) (FST (SND prepared))
       (SND (SND prepared)) = L4KAccept491 generated /\
     l4_verify_members509 (APPEND types (APPEND ctors recs)) generated =
       L4KAccept491 checked /\
     output = APPEND generated env`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_admit_inductive631;l4_bind_accept_inverse631] THEN
  ASM_CASES_TAC `l4_has_nested_inductive631 types` THEN
  ASM_REWRITE_TAC [l4_bind_accept_inverse631;distinctness "l4_kresult491";
    injectivity "l4_kresult491"] THEN MESON_TAC []);;
