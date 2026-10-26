(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED CONDITIONAL OPERATIONAL PROOFS: ALL UNCOMPILED / NOT EXECUTED.
   Premises are concrete597 calls, not injected verdict callbacks. *)
needs "hol/primitive_recursors622.ml";;

let l4_primitive_whnf_core_method622 = prove
 (`!fuel env g e. l4_primitive_whnf_core622 fuel env g e =
   l4_whnf_core_method543 (l4_checker597 fuel env []) F g e`,
  REWRITE_TAC [l4_primitive_whnf_core622]);;

let l4_primitive_lambda_domain_reject622 = prove
 (`!depth fuel env s user bi ty b reason.
   l4_sort_of543 (l4_checker597 fuel env []) (l4_kstate_context532 s) ty =
     L4KReject491 reason ==>
   l4_primitive_lambda_telescope622 (SUC depth) fuel env s (L4KLam447 user bi ty b) =
     L4KReject491 reason`,
  SIMP_TAC [l4_primitive_lambda_telescope622;l4_kr_bind491]);;

let l4_primitive_lambda_domain_decline622 = prove
 (`!depth fuel env s user bi ty b reason.
   l4_sort_of543 (l4_checker597 fuel env []) (l4_kstate_context532 s) ty =
     L4KDecline491 reason ==>
   l4_primitive_lambda_telescope622 (SUC depth) fuel env s (L4KLam447 user bi ty b) =
     L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_lambda_telescope622;l4_kr_bind491]);;

let l4_primitive_lambda_checked_open622 = prove
 (`!depth fuel env s user bi ty b u.
   l4_sort_of543 (l4_checker597 fuel env []) (l4_kstate_context532 s) ty =
     L4KAccept491 u ==>
   l4_primitive_lambda_telescope622 (SUC depth) fuel env s (L4KLam447 user bi ty b) =
     let fresh = l4_kind_fresh491 s user bi ty in
     l4_kr_bind491 (l4_primitive_lambda_telescope622 depth fuel env (SND fresh)
       (l4_kinst447 b (l4_klocal_expr489 (FST fresh))))
       (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))`,
  SIMP_TAC [l4_primitive_lambda_telescope622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_no_free_app_first622 = prove
 (`!fuel n a b reason.
   l4_primitive_no_free622 fuel n a = L4KReject491 reason ==>
   l4_primitive_no_free622 (SUC fuel) n (L4KApp447 a b) = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_no_free622;l4_kr_bind491]);;

let l4_primitive_proof_infer_reject622 = prove
 (`!fuel env g e reason.
   l4_infer597 fuel env [] g e = L4KReject491 reason ==>
   l4_primitive_proof622 fuel env g e = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_proof622;l4_kr_bind491]);;

let l4_primitive_proof_sort_decline622 = prove
 (`!fuel env g e ty reason.
   l4_infer597 fuel env [] g e = L4KAccept491 ty /\
   l4_sort_of543 (l4_checker597 fuel env []) g ty = L4KDecline491 reason ==>
   l4_primitive_proof622 fuel env g e = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_proof622;l4_kr_bind491]);;

let l4_primitive_proof_nonprop622 = prove
 (`!fuel env g e ty u.
   l4_infer597 fuel env [] g e = L4KAccept491 ty /\
   l4_sort_of543 (l4_checker597 fuel env []) g ty = L4KAccept491 u /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 F ==>
   l4_primitive_proof622 fuel env g e = L4KReject491 L4KTypeMismatch491`,
  SIMP_TAC [l4_primitive_proof622;l4_kr_bind491]);;

let l4_primitive_proof_prop622 = prove
 (`!fuel env g e ty u.
   l4_infer597 fuel env [] g e = L4KAccept491 ty /\
   l4_sort_of543 (l4_checker597 fuel env []) g ty = L4KAccept491 u /\
   l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 T ==>
   l4_primitive_proof622 fuel env g e = L4KAccept491 one`,
  SIMP_TAC [l4_primitive_proof622;l4_kr_bind491]);;

let l4_primitive_go_unfold_decline622 = prove
 (`!fuel env s go reason.
   l4_primitive_unfold622 env go = L4KDecline491 reason ==>
   l4_primitive_check_go622 fuel env s go = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_go622;l4_kr_bind491]);;

let l4_primitive_go_bad_arity622 = prove
 (`!fuel env s go value b st.
   l4_primitive_unfold622 env go = L4KAccept491 value /\
   l4_primitive_lambda_telescope622 fuel fuel env s value = L4KAccept491 ([],(b,st)) ==>
   l4_primitive_check_go622 fuel env s go = L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_check_go622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_go_wrong_last_argument622 = prove
 (`!fuel env s go value st a0 a1 a2 f t nat_rec t'.
   l4_primitive_unfold622 env go = L4KAccept491 value /\
   l4_primitive_lambda_telescope622 fuel fuel env s value =
     L4KAccept491 ([a0;a1;a2;f;t],(L4KApp447 nat_rec t',st)) /\
   ~l4_kexpr_eqb480 t' (l4_klocal_expr489 t) ==>
   l4_primitive_check_go622 fuel env s go = L4KReject491 L4KNotDefinitionallyEqual491`,
  SIMP_TAC [l4_primitive_check_go622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_go_capture_reject622 = prove
 (`!fuel env s go value st a0 a1 a2 f t nat_rec t' reason.
   l4_primitive_unfold622 env go = L4KAccept491 value /\
   l4_primitive_lambda_telescope622 fuel fuel env s value =
     L4KAccept491 ([a0;a1;a2;f;t],(L4KApp447 nat_rec t',st)) /\
   l4_kexpr_eqb480 t' (l4_klocal_expr489 t) /\
   l4_primitive_no_free622 fuel (l4_klocal_id489 t) nat_rec = L4KReject491 reason ==>
   l4_primitive_check_go622 fuel env s go = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_go622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_wf_measure_decline622 = prove
 (`!fuel env s e measure reason.
   l4_primitive_lambda_telescope622 fuel fuel env s measure = L4KDecline491 reason ==>
   l4_primitive_unfold_nat_well_founded622 fuel env s e measure = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_unfold_nat_well_founded622;l4_kr_bind491]);;

let l4_primitive_wf_wrong_fix_name622 = prove
 (`!fuel env s e measure locals mb st aty top0 top1 top2 fix_name u v alpha motive meas fn packed.
   l4_primitive_lambda_telescope622 fuel fuel env s measure = L4KAccept491 (locals,(mb,st)) /\
   l4_infer597 fuel env [] (l4_kstate_context532 st) (l4_kapply_locals489 locals e) = L4KAccept491 aty /\
   l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st)
     (l4_kapply_locals489 locals e) = L4KAccept491 top0 /\
   l4_primitive_unfold622 env top0 = L4KAccept491 top1 /\
   l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st) top1 = L4KAccept491 top2 /\
   l4_ksplit_app489 top2 = (L4KConst447 fix_name [u;v],[alpha;motive;meas;fn;packed]) /\
   ~(fix_name = l4_primitive_path621
     [[87;101;108;108;70;111;117;110;100;101;100];[78;97;116];[102;105;120]]) ==>
   l4_primitive_unfold_nat_well_founded622 fuel env s e measure =
     L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_unfold_nat_well_founded622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_wf_wrong_fix_arity622 = prove
 (`!fuel env s e measure locals mb st aty top0 top1 top2 fix_name u v.
   l4_primitive_lambda_telescope622 fuel fuel env s measure = L4KAccept491 (locals,(mb,st)) /\
   l4_infer597 fuel env [] (l4_kstate_context532 st) (l4_kapply_locals489 locals e) = L4KAccept491 aty /\
   l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st)
     (l4_kapply_locals489 locals e) = L4KAccept491 top0 /\
   l4_primitive_unfold622 env top0 = L4KAccept491 top1 /\
   l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st) top1 = L4KAccept491 top2 /\
   l4_ksplit_app489 top2 = (L4KConst447 fix_name [u;v],[]) ==>
   l4_primitive_unfold_nat_well_founded622 fuel env s e measure =
     L4KDecline491 L4KUnsupportedDeclaration491`,
  SIMP_TAC [l4_primitive_unfold_nat_well_founded622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_probe_checked_equation622 = prove
 (`!fuel env s pack dom fn args rhs.
   l4_primitive_run_probe622 fuel env s (L4PrimitiveProbe622 pack dom fn) args rhs =
   let a = l4_kapply_exprs489 args pack in
   let fresh = l4_kind_fresh491 s L4Anonymous L4KDefault447 (L4KApp447 dom a) in
   l4_check_defeq597 fuel env [] (l4_kstate_context532 (SND fresh))
     (l4_kapply_exprs489 [a;l4_klocal_expr489 (FST fresh)] fn)
     (rhs (l4_klocal_expr489 (FST fresh)))`,
  REWRITE_TAC [l4_primitive_run_probe622;l4_primitive_probe_pack622;
    l4_primitive_probe_dom622;l4_primitive_probe_functional622]);;

let l4_primitive_gcd_dependency_reject622 = prove
 (`!fuel env body reason.
   l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
   l4_primitive_authenticated619 fuel env L4KPNatMod493 = L4KReject491 reason ==>
   l4_primitive_check_gcd622 fuel env body = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_gcd622;l4_kr_bind491]);;

let l4_primitive_gcd_condition_decline622 = prove
 (`!fuel env body reason.
   l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
   l4_primitive_authenticated619 fuel env L4KPNatMod493 = L4KAccept491 one /\
   l4_primitive_check_condition621 fuel env L4PCBool621 T F = L4KDecline491 reason ==>
   l4_primitive_check_gcd622 fuel env body = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_gcd622;l4_kr_bind491]);;

let l4_primitive_bitwise_add_first622 = prove
 (`!fuel env body reason.
   l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
   l4_primitive_authenticated619 fuel env L4KPNatAdd493 = L4KReject491 reason ==>
   l4_primitive_check_bitwise622 fuel env body = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_bitwise622;l4_kr_bind491]);;

let l4_primitive_bitwise_div_before_mod622 = prove
 (`!fuel env body reason.
   l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
   l4_primitive_authenticated619 fuel env L4KPNatAdd493 = L4KAccept491 one /\
   l4_primitive_authenticated619 fuel env L4KPNatDiv493 = L4KDecline491 reason ==>
   l4_primitive_check_bitwise622 fuel env body = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_bitwise622;l4_kr_bind491]);;

let l4_primitive_boolean_typing_first622 = prove
 (`!fuel env op operator reason.
   l4_check597 fuel env [] l4_kempty_context532 operator l4_primitive_bool_operator_type622 =
     L4KReject491 reason ==>
   l4_primitive_check_boolean_operator622 fuel env op operator = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_boolean_operator622;l4_kr_bind491]);;

let l4_primitive_instance_authentication_first622 = prove
 (`!fuel env op body reason.
   l4_primitive_authenticated619 fuel env L4KPNatBitwise493 = L4KReject491 reason ==>
   l4_primitive_check_bitwise_instance622 fuel env op body = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_bitwise_instance622;l4_kr_bind491]);;

let l4_primitive_instance_canonical622 = prove
 (`!fuel env op operator.
   l4_primitive_authenticated619 fuel env L4KPNatBitwise493 = L4KAccept491 one ==>
   l4_primitive_check_bitwise_instance622 fuel env op
     (L4KApp447 (L4KConst447 l4_primitive_bitwise_name619 []) operator) =
   l4_primitive_check_boolean_operator622 fuel env op operator`,
  SIMP_TAC [l4_primitive_check_bitwise_instance622;l4_kr_bind491]);;

let l4_primitive_and_false_branch_first622 = prove
 (`!fuel env operator reason.
   l4_check597 fuel env [] l4_kempty_context532 operator l4_primitive_bool_operator_type622 =
     L4KAccept491 one /\
   l4_primitive_eq_closed621 fuel env
     (l4_pq_lam621 l4_pq_bool621 (\x.
       l4_pq_apps621 (l4_pq_embed621 operator) [l4_pq_fal621;x]))
     (l4_pq_lam621 l4_pq_bool621 (\ignored. l4_pq_fal621)) = L4KReject491 reason ==>
   l4_primitive_check_boolean_operator622 fuel env L4KPNatLAnd493 operator = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_boolean_operator622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_or_false_branch_first622 = prove
 (`!fuel env operator reason.
   l4_check597 fuel env [] l4_kempty_context532 operator l4_primitive_bool_operator_type622 =
     L4KAccept491 one /\
   l4_primitive_eq_closed621 fuel env
     (l4_pq_lam621 l4_pq_bool621 (\x.
       l4_pq_apps621 (l4_pq_embed621 operator) [l4_pq_fal621;x]))
     (l4_pq_lam621 l4_pq_bool621 (\x. x)) = L4KDecline491 reason ==>
   l4_primitive_check_boolean_operator622 fuel env L4KPNatLOr493 operator = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_boolean_operator622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;

let l4_primitive_xor_true_false_before_false_true622 = prove
 (`!fuel env operator reason.
   l4_check597 fuel env [] l4_kempty_context532 operator l4_primitive_bool_operator_type622 =
     L4KAccept491 one /\
   l4_primitive_eq_closed621 fuel env
     (l4_pq_apps621 (l4_pq_embed621 operator) [l4_pq_fal621;l4_pq_fal621]) l4_pq_fal621 =
     L4KAccept491 one /\
   l4_primitive_eq_closed621 fuel env
     (l4_pq_apps621 (l4_pq_embed621 operator) [l4_pq_tru621;l4_pq_fal621]) l4_pq_tru621 =
     L4KReject491 reason ==>
   l4_primitive_check_boolean_operator622 fuel env L4KPNatXor493 operator = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_boolean_operator622;l4_kr_bind491;LET_DEF;LET_END_DEF]);;
