(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed conditional operational equations. ALL SCRIPTS UNCOMPILED.
   No callback soundness, typed conversion or recursor adequacy is established. *)
needs "hol/recursor_conversion585.ml";;

let l4_to_constructor_whnf_reject585 = prove
 (`!rec fuel env g owner k value reason.
   l4_whnf_method543 rec g value = L4KReject491 reason ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KReject491 reason`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_whnf_decline585 = prove
 (`!rec fuel env g owner k value reason.
   l4_whnf_method543 rec g value = L4KDecline491 reason ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KDecline491 reason`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_nat_ready585 = prove
 (`!rec fuel env g k value n.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KNatLit447 n) /\
   l4_core_nat_ready533 env ==>
   l4_core_to_constructor585 rec fuel env g l4_core_nat_name533 k value =
     L4KAccept491 (l4_core_nat_constructor544 n)`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_nat_wrong_owner585 = prove
 (`!rec fuel env g owner k value n.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KNatLit447 n) /\
   ~(owner = l4_core_nat_name533) ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KAccept491 (L4KNatLit447 n)`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_nat_not_ready585 = prove
 (`!rec fuel env g owner k value n.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KNatLit447 n) /\
   ~l4_core_nat_ready533 env ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KAccept491 (L4KNatLit447 n)`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_string_route585 = prove
 (`!rec fuel env g owner k value bytes.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KStrLit447 bytes) ==>
   l4_core_to_constructor585 rec fuel env g owner k value =
     l4_kr_bind491 (l4_core_expand_string539 bytes) (\e. l4_whnf_method543 rec g e)`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_string_failure585 = prove
 (`!rec fuel env g owner k value bytes reason.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KStrLit447 bytes) /\
   l4_core_expand_string539 bytes = L4KReject491 reason ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KReject491 reason`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_string_expanded585 = prove
 (`!rec fuel env g owner k value bytes expanded.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KStrLit447 bytes) /\
   l4_core_expand_string539 bytes = L4KAccept491 expanded ==>
   l4_core_to_constructor585 rec fuel env g owner k value = l4_whnf_method543 rec g expanded`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491]);;
let l4_to_constructor_known_head585 = prove
 (`!rec fuel env g owner k value n us info.
   l4_whnf_method543 rec g value = L4KAccept491 (L4KConst447 n us) /\
   l4_core_constructor532 env n = SOME info ==>
   l4_core_to_constructor585 rec fuel env g owner k value = L4KAccept491 (L4KConst447 n us)`,
  SIMP_TAC [l4_core_to_constructor585;l4_kr_bind491;l4_ksplit_app489;
    l4_ksplit_app_aux489;FST]);;

let l4_to_structure_disabled585 = prove
 (`!rec fuel env g owner reduced. ~l4_core_structure532 env owner ==>
   l4_core_to_structure585 rec fuel env g owner F reduced = L4KAccept491 reduced`,
  SIMP_TAC [l4_core_to_structure585]);;
let l4_to_structure_infer_reject585 = prove
 (`!rec fuel env g owner k reduced reason.
   (k \/ l4_core_structure532 env owner) /\
   l4_infer_method543 rec g reduced = L4KReject491 reason ==>
   l4_core_to_structure585 rec fuel env g owner k reduced = L4KReject491 reason`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491]);;
let l4_to_structure_infer_decline585 = prove
 (`!rec fuel env g owner k reduced reason.
   (k \/ l4_core_structure532 env owner) /\
   l4_infer_method543 rec g reduced = L4KDecline491 reason ==>
   l4_core_to_structure585 rec fuel env g owner k reduced = L4KDecline491 reason`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491]);;
let l4_to_structure_whnf_reject585 = prove
 (`!rec fuel env g owner k reduced ty reason.
   (k \/ l4_core_structure532 env owner) /\
   l4_infer_method543 rec g reduced = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KReject491 reason ==>
   l4_core_to_structure585 rec fuel env g owner k reduced = L4KReject491 reason`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491]);;
let l4_to_structure_whnf_decline585 = prove
 (`!rec fuel env g owner k reduced ty reason.
   (k \/ l4_core_structure532 env owner) /\
   l4_infer_method543 rec g reduced = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KDecline491 reason ==>
   l4_core_to_structure585 rec fuel env g owner k reduced = L4KDecline491 reason`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491]);;

(* These equations expose exactly the remaining K/structure obligations.
   The first defeq operand is the normalized original type, never ct. *)
let l4_to_structure_k_candidate585 = prove
 (`!rec fuel env g owner reduced inferred ty us args candidate.
   l4_infer_method543 rec g reduced = L4KAccept491 inferred /\
   l4_whnf_method543 rec g inferred = L4KAccept491 ty /\
   l4_ksplit_app489 ty = (L4KConst447 owner us,args) /\
   l4_core_make_structure557 env owner us args reduced = SOME candidate ==>
   l4_core_to_structure585 rec fuel env g owner T reduced =
     l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
       l4_kr_bind491 (l4_klevel_equiv555 fuel sort L4KZero447) (\prop.
         if prop then l4_kr_bind491 (l4_infer_method543 rec g candidate) (\ct.
           l4_kr_bind491 (l4_defeq_method543 rec g ty ct) (\ok.
             if ok then L4KAccept491 candidate else L4KAccept491 reduced))
         else L4KAccept491 reduced))`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;
let l4_to_structure_eta_candidate585 = prove
 (`!rec fuel env g owner reduced inferred ty us args candidate.
   l4_core_structure532 env owner /\
   l4_infer_method543 rec g reduced = L4KAccept491 inferred /\
   l4_whnf_method543 rec g inferred = L4KAccept491 ty /\
   l4_ksplit_app489 ty = (L4KConst447 owner us,args) /\
   l4_core_make_structure557 env owner us args reduced = SOME candidate ==>
   l4_core_to_structure585 rec fuel env g owner F reduced =
     l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
       if l4_core_level_positive555 sort then L4KAccept491 candidate else L4KAccept491 reduced)`,
  SIMP_TAC [l4_core_to_structure585;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_reduce_recursor_unknown585 = prove
 (`!rec fuel env g e n us args.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_kfind_decl493 env n = NONE ==>
   l4_core_reduce_recursor585 rec fuel env g e = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND]);;
let l4_reduce_recursor_missing_major585 = prove
 (`!rec fuel env g e n us args d info.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDRecursor493 info /\
   l4_nth_error550 args (l4_krec_num_params493 info + l4_krec_num_motives493 info +
     l4_krec_num_minors493 info + l4_krec_num_indices493 info) = NONE ==>
   l4_core_reduce_recursor585 rec fuel env g e = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND;ADD_ASSOC]);;
let l4_reduce_recursor_malformed_major585 = prove
 (`!rec fuel env g e n us args d info first major value.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDRecursor493 info /\
   first = l4_krec_num_params493 info + l4_krec_num_motives493 info + l4_krec_num_minors493 info /\
   major = first + l4_krec_num_indices493 info /\ l4_nth_error550 args major = SOME value /\
   l4_core_major_induct557 major (l4_kdecl_type493 d) = NONE ==>
   l4_core_reduce_recursor585 rec fuel env g e = L4KReject491 L4KMalformedDeclaration491`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) then SUBST_ALL_TAC th else fail ())) THEN
  ASM_REWRITE_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;

let l4_reduce_recursor_major_reject585 = prove
 (`!rec fuel env g e n us args d info first major value owner reason.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDRecursor493 info /\
   first = l4_krec_num_params493 info + l4_krec_num_motives493 info + l4_krec_num_minors493 info /\
   major = first + l4_krec_num_indices493 info /\ l4_nth_error550 args major = SOME value /\
   l4_core_major_induct557 major (l4_kdecl_type493 d) = SOME owner /\
   l4_core_to_constructor585 rec fuel env g owner (l4_krec_k493 info) value =
     L4KReject491 reason ==>
   l4_core_reduce_recursor585 rec fuel env g e = L4KReject491 reason`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) then SUBST_ALL_TAC th else fail ())) THEN
  ASM_REWRITE_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_reduce_recursor_major_decline585 = prove
 (`!rec fuel env g e n us args d info first major value owner reason.
   l4_ksplit_app489 e = (L4KConst447 n us,args) /\
   l4_kfind_decl493 env n = SOME d /\ l4_kdecl_kind493 d = L4KDRecursor493 info /\
   first = l4_krec_num_params493 info + l4_krec_num_motives493 info + l4_krec_num_minors493 info /\
   major = first + l4_krec_num_indices493 info /\ l4_nth_error550 args major = SOME value /\
   l4_core_major_induct557 major (l4_kdecl_type493 d) = SOME owner /\
   l4_core_to_constructor585 rec fuel env g owner (l4_krec_k493 info) value =
     L4KDecline491 reason ==>
   l4_core_reduce_recursor585 rec fuel env g e = L4KDecline491 reason`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) then SUBST_ALL_TAC th else fail ())) THEN
  ASM_REWRITE_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_reduce_recursor_matching_rule585 = prove
 (`!rec fuel env g e n0 us0 args0 d0 info0 first0 major0 val0 own0 converted cn0 cus0 flds0 rule0 ci0.
   l4_ksplit_app489 e = (L4KConst447 n0 us0,args0) /\
   l4_kfind_decl493 env n0 = SOME d0 /\ l4_kdecl_kind493 d0 = L4KDRecursor493 info0 /\
   first0 = l4_krec_num_params493 info0 + l4_krec_num_motives493 info0 + l4_krec_num_minors493 info0 /\
   major0 = first0 + l4_krec_num_indices493 info0 /\ l4_nth_error550 args0 major0 = SOME val0 /\
   l4_core_major_induct557 major0 (l4_kdecl_type493 d0) = SOME own0 /\
   l4_core_to_constructor585 rec fuel env g own0 (l4_krec_k493 info0) val0 =
     L4KAccept491 converted /\
   l4_ksplit_app489 converted = (L4KConst447 cn0 cus0,flds0) /\
   l4_core_find_rule557 cn0 (l4_krec_rules493 info0) = SOME rule0 /\
   l4_core_constructor532 env cn0 = SOME ci0 ==>
   l4_core_reduce_recursor585 rec fuel env g e =
     if l4_kctor_induct493 ci0 = own0 /\
        LENGTH flds0 = l4_kctor_num_params493 ci0 + l4_kctor_num_fields493 ci0 /\
        l4_krule_nfields493 rule0 = l4_kctor_num_fields493 ci0 /\
        LENGTH us0 = LENGTH (l4_kdecl_params493 d0) then
       L4KAccept491 (SOME (l4_kapply_exprs489
         (APPEND (l4_kfirstn494 args0 first0)
           (APPEND (l4_skip550 flds0 (l4_kctor_num_params493 ci0))
             (l4_skip550 args0 (SUC major0))))
         (l4_ksubst_levels488 (l4_kdecl_params493 d0) us0 (l4_krule_rhs493 rule0))))
     else L4KAccept491 NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) then SUBST_ALL_TAC th else fail ())) THEN
  ASM_REWRITE_TAC [l4_core_reduce_recursor585;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
