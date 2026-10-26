(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Focused conditional operational equations. ALL SCRIPTS UNCOMPILED.
   No callback soundness, typed-equivalence preservation or admission theorem. *)
needs "hol/conversion_helpers595.ml";;

let l4_eta_infer_reject595 = prove
 (`!rec g domain body other reason.
   l4_infer_method543 rec g other = L4KReject491 reason ==>
   l4_eta_compare595 rec g domain body other = L4KReject491 reason`,
  SIMP_TAC [l4_eta_compare595;l4_kr_bind491]);;

let l4_eta_whnf_decline595 = prove
 (`!rec g domain body other ty reason.
   l4_infer_method543 rec g other = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KDecline491 reason ==>
   l4_eta_compare595 rec g domain body other = L4KDecline491 reason`,
  SIMP_TAC [l4_eta_compare595;l4_kr_bind491]);;

let l4_eta_nonpi_false595 = prove
 (`!rec g domain body other ty u.
   l4_infer_method543 rec g other = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty = L4KAccept491 (L4KSort447 u) ==>
   l4_eta_compare595 rec g domain body other = L4KAccept491 F`,
  SIMP_TAC [l4_eta_compare595;l4_kr_bind491]);;

let l4_eta_domain_false595 = prove
 (`!rec g domain body other ty n bi other_domain other_body.
   l4_infer_method543 rec g other = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty =
     L4KAccept491 (L4KPi447 n bi other_domain other_body) /\
   l4_defeq_method543 rec g domain other_domain = L4KAccept491 F ==>
   l4_eta_compare595 rec g domain body other = L4KAccept491 F`,
  SIMP_TAC [l4_eta_compare595;l4_kr_bind491]);;

let l4_eta_lifted_body595 = prove
 (`!rec g domain body other ty n bi other_domain other_body.
   l4_infer_method543 rec g other = L4KAccept491 ty /\
   l4_whnf_method543 rec g ty =
     L4KAccept491 (L4KPi447 n bi other_domain other_body) /\
   l4_defeq_method543 rec g domain other_domain = L4KAccept491 T ==>
   l4_eta_compare595 rec g domain body other =
     l4_defeq_method543 rec (l4_kpush_binding532 g domain NONE) body
       (L4KApp447 (l4_klift447 other 1 0) (L4KBVar447 0))`,
  SIMP_TAC [l4_eta_compare595;l4_kr_bind491]);;

let l4_compare_args_empty595 = prove
 (`!rec g. l4_core_compare_args595 [] rec g [] = L4KAccept491 T`,
  REWRITE_TAC [l4_core_compare_args595]);;

let l4_compare_args_missing_right595 = prove
 (`!x xs rec g. l4_core_compare_args595 (CONS x xs) rec g [] = L4KAccept491 F`,
  REWRITE_TAC [l4_core_compare_args595]);;

let l4_compare_args_first_false595 = prove
 (`!x xs y ys rec g.
   l4_defeq_method543 rec g x y = L4KAccept491 F ==>
   l4_core_compare_args595 (CONS x xs) rec g (CONS y ys) = L4KAccept491 F`,
  SIMP_TAC [l4_core_compare_args595;l4_kr_bind491]);;

let l4_compare_args_first_decline595 = prove
 (`!x xs y ys rec g reason.
   l4_defeq_method543 rec g x y = L4KDecline491 reason ==>
   l4_core_compare_args595 (CONS x xs) rec g (CONS y ys) = L4KDecline491 reason`,
  SIMP_TAC [l4_core_compare_args595;l4_kr_bind491]);;

let l4_compare_args_first_true595 = prove
 (`!x xs y ys rec g.
   l4_defeq_method543 rec g x y = L4KAccept491 T ==>
   l4_core_compare_args595 (CONS x xs) rec g (CONS y ys) =
     l4_core_compare_args595 xs rec g ys`,
  SIMP_TAC [l4_core_compare_args595;l4_kr_bind491]);;

let l4_same_head_name_mismatch595 = prove
 (`!fuel n m us vs. ~(n = m) ==>
   l4_core_same_head595 fuel (L4KConst447 n us) (L4KConst447 m vs) = L4KAccept491 F`,
  SIMP_TAC [l4_core_same_head595]);;

let l4_same_head_levels595 = prove
 (`!fuel n us vs.
   l4_core_same_head595 fuel (L4KConst447 n us) (L4KConst447 n vs) =
     l4_klevels_equiv555 us fuel vs`,
  REWRITE_TAC [l4_core_same_head595]);;

let l4_congruent_apps_reverse595 = prove
 (`!rec fuel g f a h b tf ta sf sa.
   l4_ksplit_app489 (L4KApp447 f a) = (tf,ta) /\
   l4_ksplit_app489 (L4KApp447 h b) = (sf,sa) /\
   l4_core_same_head595 fuel tf sf = L4KAccept491 T /\
   LENGTH ta = LENGTH sa ==>
   l4_core_congruent_apps595 rec fuel g (L4KApp447 f a) (L4KApp447 h b) =
     l4_core_compare_args595 (REVERSE ta) rec g (REVERSE sa)`,
  SIMP_TAC [l4_core_congruent_apps595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_congruent_apps_head_decline595 = prove
 (`!rec fuel g f a h b tf ta sf sa reason.
   l4_ksplit_app489 (L4KApp447 f a) = (tf,ta) /\
   l4_ksplit_app489 (L4KApp447 h b) = (sf,sa) /\
   l4_core_same_head595 fuel tf sf = L4KDecline491 reason ==>
   l4_core_congruent_apps595 rec fuel g (L4KApp447 f a) (L4KApp447 h b) =
     L4KDecline491 reason`,
  SIMP_TAC [l4_core_congruent_apps595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_delta_congruent_unavailable595 = prove
 (`!rec fuel env g t s. l4_core_delta_info538 env t = NONE ==>
   l4_core_delta_congruent595 rec fuel env g t s = L4KAccept491 F`,
  SIMP_TAC [l4_core_delta_congruent595]);;

let l4_delta_congruent_erasing595 = prove
 (`!rec fuel env g t s dt ds ht hs.
   l4_core_delta_info538 env t = SOME dt /\
   l4_core_delta_info538 env s = SOME ds /\
   l4_keffective_hints493 dt = L4KHintRegular493 ht /\
   l4_keffective_hints493 ds = L4KHintRegular493 hs /\
   (l4_core_erasing_delta538 env t \/ l4_core_erasing_delta538 env s) ==>
   l4_core_delta_congruent595 rec fuel env g t s = L4KAccept491 F`,
  SIMP_TAC [l4_core_delta_congruent595]);;

let l4_delta_congruent_enabled595 = prove
 (`!rec fuel env g t s dt ds height.
   l4_core_delta_info538 env t = SOME dt /\
   l4_core_delta_info538 env s = SOME ds /\
   l4_keffective_hints493 dt = L4KHintRegular493 height /\
   l4_keffective_hints493 ds = L4KHintRegular493 height /\
   ~(l4_core_erasing_delta538 env t \/ l4_core_erasing_delta538 env s) ==>
   l4_core_delta_congruent595 rec fuel env g t s =
     l4_core_congruent_apps595 rec fuel g t s`,
  SIMP_TAC [l4_core_delta_congruent595]);;

let l4_compare_heads_projection595 = prove
 (`!rec fuel g n i a b.
   l4_compare_heads595 rec fuel g (L4KProj447 n i a) (L4KProj447 n i b) =
     l4_defeq_method543 rec g a b`,
  REWRITE_TAC [l4_compare_heads595]);;

let l4_compare_heads_forward595 = prove
 (`!rec fuel g f a h b tf ta sf sa.
   l4_ksplit_app489 (L4KApp447 f a) = (tf,ta) /\
   l4_ksplit_app489 (L4KApp447 h b) = (sf,sa) /\
   LENGTH ta = LENGTH sa /\
   l4_defeq_method543 rec g tf sf = L4KAccept491 T ==>
   l4_compare_heads595 rec fuel g (L4KApp447 f a) (L4KApp447 h b) =
     l4_core_compare_args595 ta rec g sa`,
  SIMP_TAC [l4_compare_heads595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_compare_heads_left_eta595 = prove
 (`!rec fuel g n bi domain body other.
   l4_compare_heads595 rec fuel g (L4KLam447 n bi domain body) other =
     l4_eta_compare595 rec g domain body other`,
  REWRITE_TAC [l4_compare_heads595]);;

let l4_compare_fields_first_false595 = prove
 (`!field fields rec g owner value idx.
   l4_defeq_method543 rec g (L4KProj447 owner idx value) field = L4KAccept491 F ==>
   l4_core_compare_fields595 (CONS field fields) rec g owner value idx =
     L4KAccept491 F`,
  SIMP_TAC [l4_core_compare_fields595;l4_kr_bind491]);;

let l4_compare_fields_advance595 = prove
 (`!field fields rec g owner value idx.
   l4_defeq_method543 rec g (L4KProj447 owner idx value) field = L4KAccept491 T ==>
   l4_core_compare_fields595 (CONS field fields) rec g owner value idx =
     l4_core_compare_fields595 fields rec g owner value (SUC idx)`,
  SIMP_TAC [l4_core_compare_fields595;l4_kr_bind491]);;

let l4_structure_eta_arity595 = prove
 (`!rec env g value constructed ctor us args c.
   l4_ksplit_app489 constructed = (L4KConst447 ctor us,args) /\
   l4_core_constructor532 env ctor = SOME c /\
   ~(LENGTH args = l4_kctor_num_params493 c + l4_kctor_num_fields493 c) ==>
   l4_core_structure_eta595 rec env g value constructed = L4KAccept491 F`,
  SIMP_TAC [l4_core_structure_eta595;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_structure_eta_fields595 = prove
 (`!rec env g value constructed ctor us args c vt ct.
   l4_ksplit_app489 constructed = (L4KConst447 ctor us,args) /\
   l4_core_constructor532 env ctor = SOME c /\
   l4_core_structure532 env (l4_kctor_induct493 c) /\
   LENGTH args = l4_kctor_num_params493 c + l4_kctor_num_fields493 c /\
   l4_infer_method543 rec g value = L4KAccept491 vt /\
   l4_infer_method543 rec g constructed = L4KAccept491 ct /\
   l4_defeq_method543 rec g vt ct = L4KAccept491 T ==>
   l4_core_structure_eta595 rec env g value constructed =
     l4_core_compare_fields595 (l4_skip550 args (l4_kctor_num_params493 c))
       rec g (l4_kctor_induct493 c) value 0`,
  SIMP_TAC [l4_core_structure_eta595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_unit_like_nonstructure595 = prove
 (`!rec env g t s inferred ty owner us args.
   l4_infer_method543 rec g t = L4KAccept491 inferred /\
   l4_whnf_method543 rec g inferred = L4KAccept491 ty /\
   l4_ksplit_app489 ty = (L4KConst447 owner us,args) /\
   ~l4_core_structure532 env owner ==>
   l4_core_unit_like595 rec env g t s = L4KAccept491 F`,
  SIMP_TAC [l4_core_unit_like595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_unit_like_zero_fields595 = prove
 (`!rec env g t s inferred ty owner us args info ctor c sty.
   l4_infer_method543 rec g t = L4KAccept491 inferred /\
   l4_whnf_method543 rec g inferred = L4KAccept491 ty /\
   l4_ksplit_app489 ty = (L4KConst447 owner us,args) /\
   l4_core_structure532 env owner /\
   l4_core_inductive532 env owner = SOME info /\
   l4_kind_ctors493 info = [ctor] /\
   l4_core_constructor532 env ctor = SOME c /\
   l4_kctor_num_fields493 c = 0 /\
   l4_infer_method543 rec g s = L4KAccept491 sty ==>
   l4_core_unit_like595 rec env g t s = l4_defeq_method543 rec g ty sty`,
  SIMP_TAC [l4_core_unit_like595;l4_kr_bind491;LET_DEF;LET_END_DEF;FST;SND]);;
