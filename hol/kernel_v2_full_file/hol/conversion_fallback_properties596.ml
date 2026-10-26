(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed conditional component theorems. ALL UNCOMPILED. Method hypotheses
   state internal callback results; they do not establish checker soundness. *)
needs "hol/conversion_fallback596.ml";;

let l4_quick_alpha596 = prove
 (`!rec fuel g t s. l4_core_alpha_eq538 t s ==>
   l4_core_quick596 rec fuel g t s = L4KAccept491 (SOME T)`,
  SIMP_TAC [l4_core_quick596]);;

let l4_after_whnf_alpha596 = prove
 (`!rec fuel env g t s. l4_core_alpha_eq538 t s ==>
   l4_compare_after_whnf596 rec fuel env g t s = L4KAccept491 T`,
  SIMP_TAC [l4_compare_after_whnf596]);;

let l4_proof_irrel_decisive596 = prove
 (`!rec fuel g t s ty sort sty ok.
   l4_infer_method543 rec g t = L4KAccept491 ty /\
   l4_sort_of543 rec g ty = L4KAccept491 sort /\
   l4_klevel_equiv555 fuel sort L4KZero447 = L4KAccept491 T /\
   l4_infer_method543 rec g s = L4KAccept491 sty /\
   l4_defeq_method543 rec g ty sty = L4KAccept491 ok ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_proof_irrel_inapplicable596 = prove
 (`!rec fuel g t s ty sort.
   l4_infer_method543 rec g t = L4KAccept491 ty /\
   l4_sort_of543 rec g ty = L4KAccept491 sort /\
   l4_klevel_equiv555 fuel sort L4KZero447 = L4KAccept491 F ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_proof_irrel_first_error596 = prove
 (`!rec fuel g t s reason.
   l4_infer_method543 rec g t = L4KReject491 reason ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KReject491 reason`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_proof_irrel_sort_error596 = prove
 (`!rec fuel g t s ty reason.
   l4_infer_method543 rec g t = L4KAccept491 ty /\
   l4_sort_of543 rec g ty = L4KReject491 reason ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KReject491 reason`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_proof_irrel_level_decline596 = prove
 (`!rec fuel g t s ty sort reason.
   l4_infer_method543 rec g t = L4KAccept491 ty /\
   l4_sort_of543 rec g ty = L4KAccept491 sort /\
   l4_klevel_equiv555 fuel sort L4KZero447 = L4KDecline491 reason ==>
   l4_core_proof_irrel596 rec fuel g t s = L4KDecline491 reason`,
  SIMP_TAC [l4_core_proof_irrel596;l4_kr_bind491]);;

let l4_fallback_heads_stop596 = prove
 (`!rec fuel env g t s.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 T ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KAccept491 T`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_heads_error596 = prove
 (`!rec fuel env g t s reason.
   l4_compare_heads595 rec fuel g t s = L4KReject491 reason ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KReject491 reason`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_eta_reverse596 = prove
 (`!rec fuel env g t s.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g s t = L4KAccept491 T ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KAccept491 T`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_eta_forward_stop596 = prove
 (`!rec fuel env g t s.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g t s = L4KAccept491 T ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KAccept491 T`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_eta_forward_error596 = prove
 (`!rec fuel env g t s reason.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g t s = L4KDecline491 reason ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KDecline491 reason`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_string_decisive596 = prove
 (`!rec fuel env g t s ok.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g s t = L4KAccept491 F /\
   l4_core_try_string_expansion596 rec g t s = L4KAccept491 (SOME ok) ==>
   l4_core_compare_fallback596 rec fuel env g t s = L4KAccept491 ok`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_fallback_unit_only_on_none596 = prove
 (`!rec fuel env g t s.
   l4_compare_heads595 rec fuel g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g t s = L4KAccept491 F /\
   l4_core_structure_eta595 rec env g s t = L4KAccept491 F /\
   l4_core_try_string_expansion596 rec g t s = L4KAccept491 NONE ==>
   l4_core_compare_fallback596 rec fuel env g t s =
     l4_core_unit_like595 rec env g t s`,
  SIMP_TAC [l4_core_compare_fallback596;l4_kr_bind491]);;

let l4_quick_pi_left_domain_context596 = prove
 (`!rec fuel g n m bi bj a b c d ok.
   ~l4_core_alpha_eq538 (L4KPi447 n bi a b) (L4KPi447 m bj c d) /\
   l4_defeq_method543 rec g a c = L4KAccept491 T /\
   l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d = L4KAccept491 ok ==>
   l4_core_quick596 rec fuel g (L4KPi447 n bi a b) (L4KPi447 m bj c d) =
     L4KAccept491 (SOME ok)`,
  SIMP_TAC [l4_core_quick596;l4_kr_bind491]);;

let l4_quick_lam_domain_false596 = prove
 (`!rec fuel g n m bi bj a b c d.
   ~l4_core_alpha_eq538 (L4KLam447 n bi a b) (L4KLam447 m bj c d) /\
   l4_defeq_method543 rec g a c = L4KAccept491 F ==>
   l4_core_quick596 rec fuel g (L4KLam447 n bi a b) (L4KLam447 m bj c d) =
     L4KAccept491 (SOME F)`,
  SIMP_TAC [l4_core_quick596;l4_kr_bind491]);;

let l4_after_whnf_lam_body_result596 = prove
 (`!rec fuel env g n m bi bj a b c d.
   ~l4_core_alpha_eq538 (L4KLam447 n bi a b) (L4KLam447 m bj c d) /\
   l4_defeq_method543 rec g a c = L4KAccept491 T ==>
   l4_compare_after_whnf596 rec fuel env g
     (L4KLam447 n bi a b) (L4KLam447 m bj c d) =
     l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d`,
  SIMP_TAC [l4_compare_after_whnf596;l4_kr_bind491]);;

let l4_offset_readiness_gate596 = prove
 (`!rec env g t s. ~l4_core_nat_ready533 env ==>
   l4_core_offset596 rec env g t s = L4KAccept491 NONE`,
  SIMP_TAC [l4_core_offset596]);;

let l4_projection_retry_whole_expression596 = prove
 (`!rec g e owner idx value reduced.
   FST (l4_ksplit_app489 e) = L4KProj447 owner idx value /\
   l4_whnf_core_method543 rec F g e = L4KAccept491 reduced ==>
   l4_core_try_unfold_proj_app596 rec g e =
     L4KAccept491 (if l4_kexpr_eqb480 reduced e then NONE else SOME reduced)`,
  SIMP_TAC [l4_core_try_unfold_proj_app596;l4_kr_bind491]);;

let l4_projection_retry_error596 = prove
 (`!rec g e owner idx value reason.
   FST (l4_ksplit_app489 e) = L4KProj447 owner idx value /\
   l4_whnf_core_method543 rec F g e = L4KReject491 reason ==>
   l4_core_try_unfold_proj_app596 rec g e = L4KReject491 reason`,
  SIMP_TAC [l4_core_try_unfold_proj_app596;l4_kr_bind491]);;

let l4_opposite_projection_right596 = prove
 (`!rec env g t s dt sn.
   l4_core_delta_info538 env t = SOME dt /\
   l4_core_delta_info538 env s = NONE /\
   l4_core_try_unfold_proj_app596 rec g s = L4KAccept491 (SOME sn) ==>
   l4_core_opposite_projection596 rec env g t s = L4KAccept491 (SOME (t,sn))`,
  SIMP_TAC [l4_core_opposite_projection596;l4_kr_bind491]);;

let l4_opposite_projection_left596 = prove
 (`!rec env g t s ds tn.
   l4_core_delta_info538 env t = NONE /\
   l4_core_delta_info538 env s = SOME ds /\
   l4_core_try_unfold_proj_app596 rec g t = L4KAccept491 (SOME tn) ==>
   l4_core_opposite_projection596 rec env g t s = L4KAccept491 (SOME (tn,s))`,
  SIMP_TAC [l4_core_opposite_projection596;l4_kr_bind491]);;
