(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED HOL PROOFS / UNCOMPILED / UNEXECUTED.
   Conditional properties of the actual definitions, not assumed certificates. *)
needs "hol/primitive_reflection621.ml";;

let L4_PQ_EMBED_DEPTH621 = prove
 (`!e d. l4_pq_embed621 e d = l4_klift447 e d 0`,
  REWRITE_TAC [l4_pq_embed621]);;

let L4_PQ_APPS_ORDER621 = prove
 (`!f a b d. l4_pq_apps621 f [a;b] d =
     L4KApp447 (L4KApp447 (f d) (a d)) (b d)`,
  REWRITE_TAC [l4_pq_apps621; MAP; l4_kapply_exprs489]);;

let L4_PQ_LAM_SELF621 = prove
 (`!a d. l4_pq_lam621 a (\x. x) d =
     L4KLam447 L4Anonymous L4KDefault447 (a d) (L4KBVar447 0)`,
  REWRITE_TAC [l4_pq_lam621; SUB_REFL]);;

let L4_PQ_TWO_BINDERS_OUTER621 = prove
 (`!a b d. l4_pq_lam621 a (\x. l4_pq_lam621 b (\y. x)) d =
     L4KLam447 L4Anonymous L4KDefault447 (a d)
       (L4KLam447 L4Anonymous L4KDefault447 (b (SUC d)) (L4KBVar447 1))`,
  REWRITE_TAC [l4_pq_lam621;
    ARITH_RULE `!d. SUC (SUC d) - SUC d = 1`]);;

let L4_PQ_EQUALITY_USES_TYPED_CHECK621 = prove
 (`!fuel env a b. l4_primitive_eq_closed621 fuel env a b =
     l4_check_defeq597 fuel env [] l4_kempty_context532 (a 0) (b 0)`,
  REWRITE_TAC [l4_primitive_eq_closed621; l4_pq_run621]);;

let L4_PQ_TYPING_USES_CHECK621 = prove
 (`!fuel env a ty. l4_primitive_check_closed621 fuel env a ty =
     l4_check597 fuel env [] l4_kempty_context532 (a 0) (ty 0)`,
  REWRITE_TAC [l4_primitive_check_closed621; l4_pq_run621]);;

let L4_REFLECTION_TYPE_FIELD621 = prove
 (`!false_eq. l4_reflection_type621 (l4_primitive_reflection_make621 false_eq) =
     l4_primitive_reflection_type621 false_eq`,
  REWRITE_TAC [l4_primitive_reflection_make621; LET_DEF; LET_END_DEF; l4_reflection_type621]);;

let L4_CONDITION_UNREADY_FIRST621 = prove
 (`!fuel env c wi wd. ~l4_core_bool_ready533 env ==>
     l4_primitive_check_condition621 fuel env c wi wd =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_condition621]);;

let L4_CONDITION_INFER_REJECT621 = prove
 (`!fuel env c wi wd reason.
     l4_core_bool_ready533 env /\
     l4_infer597 fuel env [] l4_kempty_context532 (l4_primitive_condition_dec621 c) =
       L4KReject491 reason ==>
     l4_primitive_check_condition621 fuel env c wi wd = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_condition621; l4_kr_bind491]);;

let L4_CONDITION_INFER_DECLINE621 = prove
 (`!fuel env c wi wd reason.
     l4_core_bool_ready533 env /\
     l4_infer597 fuel env [] l4_kempty_context532 (l4_primitive_condition_dec621 c) =
       L4KDecline491 reason ==>
     l4_primitive_check_condition621 fuel env c wi wd = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_condition621; l4_kr_bind491]);;

let L4_REFLECTION_INITIAL_REJECT621 = prove
 (`!fuel env r wi wd reason.
     l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_type621 r))
       (l4_pq_arrow621 l4_pq_prop621 (l4_pq_arrow621 l4_pq_bool621 l4_pq_prop621)) =
       L4KReject491 reason ==>
     l4_primitive_check_reflection621 fuel env r wi wd = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_reflection621; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let L4_REFLECTION_INITIAL_DECLINE621 = prove
 (`!fuel env r wi wd reason.
     l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_type621 r))
       (l4_pq_arrow621 l4_pq_prop621 (l4_pq_arrow621 l4_pq_bool621 l4_pq_prop621)) =
       L4KDecline491 reason ==>
     l4_primitive_check_reflection621 fuel env r wi wd = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_reflection621; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let L4_REFLECTION_DISABLED_STILL_CHECKS621 = prove
 (`!fuel env r.
     l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_type621 r))
       (l4_pq_arrow621 l4_pq_prop621 (l4_pq_arrow621 l4_pq_bool621 l4_pq_prop621)) =
       L4KAccept491 one ==>
     l4_primitive_check_reflection621 fuel env r F F = L4KAccept491 one`,
  SIMP_TAC [l4_primitive_check_reflection621; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let L4_FUEL_REC_UNREADY_FIRST621 = prove
 (`!fuel env modulo body. ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env) ==>
     l4_primitive_check_fuel_rec621 fuel env modulo body =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_primitive_check_fuel_rec621]);;

let L4_FUEL_REC_AUTH_REJECT621 = prove
 (`!fuel env modulo body reason.
     l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
     l4_primitive_authenticated619 fuel env L4KPNatSub493 = L4KReject491 reason ==>
     l4_primitive_check_fuel_rec621 fuel env modulo body = L4KReject491 reason`,
  SIMP_TAC [l4_primitive_check_fuel_rec621; l4_kr_bind491]);;

let L4_FUEL_REC_AUTH_DECLINE621 = prove
 (`!fuel env modulo body reason.
     l4_core_nat_ready533 env /\ l4_core_bool_ready533 env /\
     l4_primitive_authenticated619 fuel env L4KPNatSub493 = L4KDecline491 reason ==>
     l4_primitive_check_fuel_rec621 fuel env modulo body = L4KDecline491 reason`,
  SIMP_TAC [l4_primitive_check_fuel_rec621; l4_kr_bind491]);;
