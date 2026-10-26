(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed raw-shape and conditional regressions. ALL UNCOMPILED.
   These are HOL scripts, not executed models or native test receipts. *)
needs "hol/conversion_fallback_properties596.ml";;

let l4_reg_irrelevance_refutes596 = prove
 (`!rec fuel g t s ty sort sty.
   l4_infer_method543 rec g t = L4KAccept491 ty /\
   l4_sort_of543 rec g ty = L4KAccept491 sort /\
   l4_klevel_equiv555 fuel sort L4KZero447 = L4KAccept491 T /\
   l4_infer_method543 rec g s = L4KAccept491 sty /\
   l4_defeq_method543 rec g ty sty = L4KAccept491 F ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KAccept491 (SOME F)`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_reg_string_right_literal_operand_order596 = prove
 (`!rec g bytes arg expanded ok.
   l4_core_expand_string539 bytes = L4KAccept491 expanded /\
   l4_defeq_method543 rec g expanded
     (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg) = L4KAccept491 ok ==>
   l4_core_try_string_expansion596 rec g
     (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg)
     (L4KStrLit447 bytes) = L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_try_string_expansion596;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_reg_string_left_literal_operand_order596 = prove
 (`!rec g bytes arg expanded ok.
   l4_core_expand_string539 bytes = L4KAccept491 expanded /\
   l4_defeq_method543 rec g expanded
     (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg) = L4KAccept491 ok ==>
   l4_core_try_string_expansion596 rec g (L4KStrLit447 bytes)
     (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg) =
     L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_try_string_expansion596;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_reg_string_universe_nonempty596 = prove
 (`!rec g arg. l4_core_try_string_expansion596 rec g (L4KStrLit447 [65])
   (L4KApp447 (L4KConst447 l4_core_string_of_list533 [L4KZero447]) arg) =
   L4KAccept491 NONE`,
  REWRITE_TAC [l4_core_try_string_expansion596;LET_DEF;LET_END_DEF]);;

let l4_reg_string_extra_application596 = prove
 (`!rec g arg extra. l4_core_try_string_expansion596 rec g (L4KStrLit447 [65])
   (L4KApp447 (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg) extra) =
   L4KAccept491 NONE`,
  REWRITE_TAC [l4_core_try_string_expansion596;LET_DEF;LET_END_DEF]);;

let l4_reg_string_nonbyte_reject596 = prove
 (`!rec g arg. l4_core_try_string_expansion596 rec g (L4KStrLit447 [256])
   (L4KApp447 (L4KConst447 l4_core_string_of_list533 []) arg) =
   L4KReject491 L4KMalformedDeclaration491`,
  REWRITE_TAC [l4_core_try_string_expansion596;LET_DEF;LET_END_DEF;
    l4_core_expand_string539;l4_core_utf8_539;l4_core_utf8_scan539;
    l4_kr_bind491] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [l4_kr_bind491]);;

let l4_reg_quick_mixed_literals596 = prove
 (`!rec fuel g. l4_core_quick596 rec fuel g (L4KNatLit447 0) (L4KStrLit447 []) =
   L4KAccept491 (SOME F)`,
  REWRITE_TAC [l4_core_quick596;l4_core_alpha_eq538;l4_core_alpha538;FST;
    distinctness "l4_kexpr447"] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [FST]);;

let l4_reg_after_whnf_mixed_literals_infers596 = prove
 (`!rec fuel env g reason.
   l4_infer_method543 rec g (L4KNatLit447 0) = L4KReject491 reason ==>
   l4_compare_after_whnf596 rec fuel env g (L4KNatLit447 0) (L4KStrLit447 []) =
     L4KReject491 reason`,
  SIMP_TAC [l4_compare_after_whnf596;l4_core_alpha_eq538;l4_core_alpha538;FST;
    distinctness "l4_kexpr447";ARITH_RULE `~(256 = 0)`;l4_kr_bind491]);;

let l4_reg_quick_metadata_callback596 = prove
 (`!rec fuel g a b ok.
   ~l4_core_alpha_eq538 (L4KMData447 a) (L4KMData447 b) /\
   l4_defeq_method543 rec g a b = L4KAccept491 ok ==>
   l4_core_quick596 rec fuel g (L4KMData447 a) (L4KMData447 b) =
     L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_quick596;l4_kr_bind491]);;

let l4_reg_offset_literal_successor596 = prove
 (`!rec env g arg ok.
   l4_core_nat_ready533 env /\
   l4_defeq_method543 rec g (L4KNatLit447 3) arg = L4KAccept491 ok ==>
   l4_core_offset596 rec env g (L4KNatLit447 4)
     (L4KApp447 (L4KConst447 l4_core_succ_name533 []) arg) =
     L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_offset596;LET_DEF;LET_END_DEF;l4_kr_bind491;
    ARITH_RULE `~(4 = 0)`;ARITH_RULE `4 - 1 = 3`]);;

let l4_reg_offset_zero_no_predecessor596 = prove
 (`!rec env g arg. l4_core_nat_ready533 env ==>
   l4_core_offset596 rec env g (L4KNatLit447 0)
     (L4KApp447 (L4KConst447 l4_core_succ_name533 []) arg) = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_offset596;LET_DEF;LET_END_DEF]);;

let l4_reg_offset_zero_representations596 = prove
 (`!rec env g. l4_core_nat_ready533 env ==>
   l4_core_offset596 rec env g (L4KNatLit447 0)
     (L4KConst447 l4_core_zero_name533 []) = L4KAccept491 (SOME T)`,
  SIMP_TAC [l4_core_offset596;LET_DEF;LET_END_DEF]);;

let l4_reg_offset_universe_nonempty596 = prove
 (`!rec env g a b. l4_core_nat_ready533 env ==>
   l4_core_offset596 rec env g
     (L4KApp447 (L4KConst447 l4_core_succ_name533 [L4KZero447]) a)
     (L4KApp447 (L4KConst447 l4_core_succ_name533 []) b) = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_offset596;LET_DEF;LET_END_DEF]);;

let l4_reg_projection_unchanged596 = prove
 (`!rec g owner idx value arg.
   l4_kexpr_eqb480 value value /\ l4_kexpr_eqb480 arg arg /\
   l4_whnf_core_method543 rec F g (L4KApp447 (L4KProj447 owner idx value) arg) =
     L4KAccept491 (L4KApp447 (L4KProj447 owner idx value) arg) ==>
   l4_core_try_unfold_proj_app596 rec g (L4KApp447 (L4KProj447 owner idx value) arg) =
     L4KAccept491 NONE`,
  SIMP_TAC [l4_core_try_unfold_proj_app596;l4_ksplit_app489;
    l4_ksplit_app_aux489;FST;l4_kr_bind491;l4_kexpr_eqb480]);;

let l4_reg_projection_metadata_blocks_head596 = prove
 (`!rec g owner idx value arg. l4_core_try_unfold_proj_app596 rec g
   (L4KApp447 (L4KMData447 (L4KProj447 owner idx value)) arg) = L4KAccept491 NONE`,
  REWRITE_TAC [l4_core_try_unfold_proj_app596;l4_ksplit_app489;l4_ksplit_app_aux489;FST]);;

let l4_reg_projection_eqb_not_raw_change596 = prove
 (`!rec g e owner idx value reduced.
   FST (l4_ksplit_app489 e) = L4KProj447 owner idx value /\
   l4_kexpr_eqb480 reduced e /\ ~(reduced = e) /\
   l4_whnf_core_method543 rec F g e = L4KAccept491 reduced ==>
   l4_core_try_unfold_proj_app596 rec g e = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_try_unfold_proj_app596;l4_kr_bind491]);;

let l4_reg_projection_eqb_ignores_binder_info596 = prove
 (`!rec g n m.
   l4_whnf_core_method543 rec F g
     (L4KProj447 L4Anonymous 0
       (L4KLam447 n L4KDefault447 (L4KBVar447 0) (L4KBVar447 0))) =
     L4KAccept491 (L4KProj447 L4Anonymous 0
       (L4KLam447 m L4KImplicit447 (L4KBVar447 0) (L4KBVar447 0))) ==>
   l4_core_try_unfold_proj_app596 rec g
     (L4KProj447 L4Anonymous 0
       (L4KLam447 n L4KDefault447 (L4KBVar447 0) (L4KBVar447 0))) =
     L4KAccept491 NONE`,
  SIMP_TAC [l4_core_try_unfold_proj_app596;l4_ksplit_app489;l4_ksplit_app_aux489;
    FST;l4_kr_bind491;l4_kexpr_eqb480]);;

let l4_reg_opposite_both_delta_no_retry596 = prove
 (`!rec env g t s dt ds.
   l4_core_delta_info538 env t = SOME dt /\
   l4_core_delta_info538 env s = SOME ds ==>
   l4_core_opposite_projection596 rec env g t s = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_opposite_projection596]);;

let l4_reg_opposite_neither_delta_no_retry596 = prove
 (`!rec env g t s.
   l4_core_delta_info538 env t = NONE /\ l4_core_delta_info538 env s = NONE ==>
   l4_core_opposite_projection596 rec env g t s = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_opposite_projection596]);;
