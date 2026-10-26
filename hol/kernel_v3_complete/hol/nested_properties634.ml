(* SPDX-License-Identifier: Apache-2.0. Proposed scripts, ALL UNCOMPILED.
   Operational properties only; no whole-kernel soundness claim. *)
needs "hol/nested_admission634.ml";;

let l4_nested_context_complete634 = prove
 (`!params bound free specs mapping names count.
   l4_nested_checked_context634
     (L4KNestedElimination499 params (bound,free) specs mapping names count) =
   L4KContext532 bound free`,
  REWRITE_TAC [l4_nested_checked_context634;l4_knested_context499;
    LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_bound_context634 = prove
 (`!res. l4_kcontext_bound532 (l4_nested_checked_context634 res) =
   FST (l4_knested_context499 res)`,
  REWRITE_TAC [l4_nested_checked_context634;l4_kcontext_bound532;LET_DEF;LET_END_DEF]);;

let l4_nested_free_context634 = prove
 (`!res. l4_kcontext_free532 (l4_nested_checked_context634 res) =
   SND (l4_knested_context499 res)`,
  REWRITE_TAC [l4_nested_checked_context634;l4_kcontext_free532;LET_DEF;LET_END_DEF]);;

let l4_nested_preparation_reject_first634 = prove
 (`!fuel env types ctors recs reason.
   l4_prepare_inductive518 env types ctors recs = L4KReject491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491]);;

let l4_nested_preparation_decline634 = prove
 (`!fuel env types ctors recs reason.
   l4_prepare_inductive518 env types ctors recs = L4KDecline491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491]);;

let l4_nested_reserved_ctor_before_transform634 = prove
 (`!fuel env types ctors recs ps np specs.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors ==>
   l4_admit_inductive_nested634 fuel env types ctors recs =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_transform_reject634 = prove
 (`!fuel env types ctors recs ps np specs reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KReject491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_transform_decline634 = prove
 (`!fuel env types ctors recs ps np specs reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KDecline491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_derivation_reject634 = prove
 (`!fuel env types ctors recs ps np specs transformed reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KAccept491 transformed /\
   l4_derive_inductive631 fuel env ps np (l4_knested_specs499 transformed) = L4KReject491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KReject491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_derivation_decline634 = prove
 (`!fuel env types ctors recs ps np specs transformed reason.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KAccept491 transformed /\
   l4_derive_inductive631 fuel env ps np (l4_knested_specs499 transformed) = L4KDecline491 reason ==>
   l4_admit_inductive_nested634 fuel env types ctors recs = L4KDecline491 reason`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_nested_zero_aux_still_checks_metadata634 = prove
 (`!fuel env types ctors recs ps np specs transformed generated.
   l4_prepare_inductive518 env types ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KAccept491 transformed /\
   l4_derive_inductive631 fuel env ps np (l4_knested_specs499 transformed) = L4KAccept491 generated /\
   l4_knested_aux_count499 transformed = 0 ==>
   l4_admit_inductive_nested634 fuel env types ctors recs =
     l4_kr_bind491 (l4_verify_members509 (APPEND types (APPEND ctors recs)) generated)
       (\verified. L4KAccept491 (APPEND generated env))`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

(* This names every successful intermediate result in the nested branch.
   The final mapping check remains explicit in the conclusion, never omitted
   because structural restoration or supplied-metadata comparison succeeded. *)
let l4_nested_final_inference_gate634 = prove
 (`!fuel env main rest ctors recs ps np specs transformed generated
     restored_inds restored_ctors restored_recs verified.
   l4_prepare_inductive518 env (CONS main rest) ctors recs = L4KAccept491 (ps,np,specs) /\
   ~EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors /\
   l4_eliminate_nested502 fuel env ps np specs = L4KAccept491 transformed /\
   l4_derive_inductive631 fuel env ps np (l4_knested_specs499 transformed) = L4KAccept491 generated /\
   ~(l4_knested_aux_count499 transformed = 0) /\
   l4_kmap_result499 (MAP l4_kdecl_name493 (CONS main rest))
     (l4_restore_inductive505 generated transformed (MAP l4_kdecl_name493 (CONS main rest))) =
       L4KAccept491 restored_inds /\
   l4_kmap_result499 (MAP l4_kdecl_name493 ctors)
     (l4_restore_constructor505 fuel generated transformed) = L4KAccept491 restored_ctors /\
   l4_kmap_result499
     (MAP l4_nested_rec_name437 (APPEND (MAP l4_kdecl_name493 (CONS main rest))
       (l4_kskipn499 (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s))
         (l4_knested_specs499 transformed)) (LENGTH (CONS main rest)))))
     (l4_restore_recursor505 fuel generated transformed
       (l4_auxiliary_rec_names508
         (l4_kskipn499 (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s))
           (l4_knested_specs499 transformed)) (LENGTH (CONS main rest)))
         (l4_kdecl_name493 main) 1)
       (MAP l4_kdecl_name493 (CONS main rest))) = L4KAccept491 restored_recs /\
   l4_verify_members509 (APPEND (CONS main rest) (APPEND ctors recs))
     (APPEND restored_recs (APPEND restored_ctors restored_inds)) = L4KAccept491 verified ==>
   l4_admit_inductive_nested634 fuel env (CONS main rest) ctors recs =
     l4_kr_bind491
       (l4_kmap_result499 (l4_knested_mapping499 transformed)
         (\entry. l4_kr_bind491
           (l4_infer597 fuel (APPEND (APPEND restored_recs (APPEND restored_ctors restored_inds)) env)
             ps (l4_nested_checked_context634 transformed) (FST entry))
           (\inferred. L4KAccept491 one)))
       (\inferred. L4KAccept491
         (APPEND (APPEND restored_recs (APPEND restored_ctors restored_inds)) env))`,
  SIMP_TAC [l4_admit_inductive_nested634;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;
