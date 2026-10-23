(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Conditional operational equations only. ALL SCRIPTS UNCOMPILED.
   Callback soundness, admitted metadata and typed reduction remain obligations. *)
needs "hol/whnf_control594.ml";;

let l4_head_nat_reject594 = prove
 (`!rec fuel env g e reason.
   l4_core_reduce_nat549 rec fuel env g e = L4KReject491 reason ==>
   l4_core_reduce_head594 rec fuel env g e = L4KReject491 reason`,
  SIMP_TAC [l4_core_reduce_head594;l4_kr_bind491]);;
let l4_head_nat_decline594 = prove
 (`!rec fuel env g e reason.
   l4_core_reduce_nat549 rec fuel env g e = L4KDecline491 reason ==>
   l4_core_reduce_head594 rec fuel env g e = L4KDecline491 reason`,
  SIMP_TAC [l4_core_reduce_head594;l4_kr_bind491]);;
let l4_head_nat_wins594 = prove
 (`!rec fuel env g e value.
   l4_core_reduce_nat549 rec fuel env g e = L4KAccept491 (SOME value) ==>
   l4_core_reduce_head594 rec fuel env g e = L4KAccept491 (SOME value)`,
  SIMP_TAC [l4_core_reduce_head594;l4_kr_bind491]);;
let l4_head_quotient_stage594 = prove
 (`!rec fuel env g e.
   l4_core_reduce_nat549 rec fuel env g e = L4KAccept491 NONE ==>
   l4_core_reduce_head594 rec fuel env g e =
     l4_kr_bind491 (l4_core_reduce_quotient550 rec env g e) (\q.
       match q with
       | SOME value -> L4KAccept491 q
       | NONE -> l4_core_reduce_recursor585 rec fuel env g e)`,
  SIMP_TAC [l4_core_reduce_head594;l4_kr_bind491]);;
let l4_head_recursor_stage594 = prove
 (`!rec fuel env g e.
   l4_core_reduce_nat549 rec fuel env g e = L4KAccept491 NONE /\
   l4_core_reduce_quotient550 rec env g e = L4KAccept491 NONE ==>
   l4_core_reduce_head594 rec fuel env g e = l4_core_reduce_recursor585 rec fuel env g e`,
  SIMP_TAC [l4_core_reduce_head594;l4_kr_bind491]);;

let l4_core_app_head_reject594 = prove
 (`!rec fuel env ps cheap g f a head args reason.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KReject491 reason ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) = L4KReject491 reason`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_core_app_head_decline594 = prove
 (`!rec fuel env ps cheap g f a head args reason.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KDecline491 reason ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) = L4KDecline491 reason`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_core_app_beta594 = prove
 (`!rec fuel env ps cheap g f a head args n bi domain body.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KAccept491 (L4KLam447 n bi domain body) ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) =
     l4_whnf_core_method543 rec cheap g (l4_kcore_beta526 (L4KLam447 n bi domain body) args)`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_core_app_quotient_wins594 = prove
 (`!rec fuel env ps cheap g f a head args n us value.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KAccept491 (L4KConst447 n us) /\
   l4_core_reduce_quotient550 rec env g (l4_kapply_exprs489 args (L4KConst447 n us)) =
     L4KAccept491 (SOME value) ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) =
     l4_whnf_core_method543 rec cheap g value`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;
let l4_core_app_recursor_stage594 = prove
 (`!rec fuel env ps cheap g f a head args n us.
   l4_ksplit_app489 (L4KApp447 f a) = (head,args) /\
   l4_whnf_core_method543 rec cheap g head = L4KAccept491 (L4KConst447 n us) /\
   l4_core_reduce_quotient550 rec env g (l4_kapply_exprs489 args (L4KConst447 n us)) =
     L4KAccept491 NONE ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KApp447 f a) =
     l4_kr_bind491
       (l4_core_reduce_recursor585 rec fuel env g (l4_kapply_exprs489 args (L4KConst447 n us)))
       (\step. match step with
               | SOME value -> l4_whnf_core_method543 rec cheap g value
               | NONE -> L4KAccept491 (l4_kapply_exprs489 args (L4KConst447 n us)))`,
  SIMP_TAC [l4_whnf_core_step594;LET_DEF;LET_END_DEF;FST;SND;l4_kr_bind491]);;

let l4_core_bound_value_lift594 = prove
 (`!rec fuel env ps cheap g i b v.
   l4_nth_error550 (l4_kcontext_bound532 g) i = SOME b /\
   l4_kbinding_value532 b = SOME v ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KBVar447 i) =
     l4_whnf_core_method543 rec cheap g (l4_klift447 v (SUC i) 0)`,
  SIMP_TAC [l4_whnf_core_step594]);;
let l4_core_free_value594 = prove
 (`!rec fuel env ps cheap g n b v.
   l4_kfind_free532 n (l4_kcontext_free532 g) = SOME b /\
   l4_kbinding_value532 b = SOME v ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KFVar447 n) =
     l4_whnf_core_method543 rec cheap g v`,
  SIMP_TAC [l4_whnf_core_step594]);;
let l4_core_constant_preserved594 = prove
 (`!rec fuel env ps cheap g n us d.
   l4_get_constant528 env ps n us = L4KAccept491 d ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KConst447 n us) =
     L4KAccept491 (L4KConst447 n us)`,
  SIMP_TAC [l4_whnf_core_step594;l4_kr_bind491]);;
let l4_core_string_validated594 = prove
 (`!rec fuel env ps cheap g bytes expanded.
   l4_core_expand_string539 bytes = L4KAccept491 expanded ==>
   l4_whnf_core_step594 rec fuel env ps cheap g (L4KStrLit447 bytes) =
     L4KAccept491 (L4KStrLit447 bytes)`,
  SIMP_TAC [l4_whnf_core_step594;l4_kr_bind491]);;

let l4_core_projection_cheap_route594 = prove
 (`!rec fuel env ps g owner idx value.
   l4_whnf_core_step594 rec fuel env ps T g (L4KProj447 owner idx value) =
     l4_kr_bind491
       (l4_core_reduce_projection_with550 rec (l4_whnf_core_method543 rec T)
         env g owner idx value)
       (\step. match step with
               | SOME selected -> l4_whnf_core_method543 rec T g selected
               | NONE -> L4KAccept491 (L4KProj447 owner idx value))`,
  REWRITE_TAC [l4_whnf_core_step594]);;
let l4_core_projection_full_route594 = prove
 (`!rec fuel env ps g owner idx value.
   l4_whnf_core_step594 rec fuel env ps F g (L4KProj447 owner idx value) =
     l4_kr_bind491
       (l4_core_reduce_projection_with550 rec (l4_whnf_method543 rec)
         env g owner idx value)
       (\step. match step with
               | SOME selected -> l4_whnf_core_method543 rec F g selected
               | NONE -> L4KAccept491 (L4KProj447 owner idx value))`,
  REWRITE_TAC [l4_whnf_core_step594]);;

let l4_whnf_core_reject_first594 = prove
 (`!rec fuel env ps g e reason.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KReject491 reason ==>
   l4_whnf_step594 rec fuel env ps g e = L4KReject491 reason /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KReject491 reason`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_core_decline_first594 = prove
 (`!rec fuel env ps g e reason.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KDecline491 reason ==>
   l4_whnf_step594 rec fuel env ps g e = L4KDecline491 reason /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KDecline491 reason`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_zero_ready594 = prove
 (`!rec fuel env ps g e us.
   l4_whnf_core_step594 rec fuel env ps F g e =
     L4KAccept491 (L4KConst447 l4_core_zero_name533 us) /\ l4_core_nat_ready533 env ==>
   l4_whnf_step594 rec fuel env ps g e = L4KAccept491 (L4KNatLit447 0) /\
   l4_whnf_round_step594 rec fuel env ps g e =
     L4KAccept491 (L4WhnfDone543 (L4KNatLit447 0))`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_constant_delta594 = prove
 (`!rec fuel env ps g e n us value.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KConst447 n us) /\
   ~(n = l4_core_zero_name533 /\ l4_core_nat_ready533 env) /\
   l4_core_unfold528 env ps (L4KConst447 n us) = L4KAccept491 (SOME value) ==>
   l4_whnf_step594 rec fuel env ps g e = l4_whnf_method543 rec g value /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfContinue543 value)`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_finish_whnf_unfold594;l4_kr_bind491]);;
let l4_whnf_app_nat_done594 = prove
 (`!rec fuel env ps g e f a value.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KApp447 f a) /\
   l4_core_reduce_nat549 rec fuel env g (L4KApp447 f a) = L4KAccept491 (SOME value) ==>
   l4_whnf_step594 rec fuel env ps g e = L4KAccept491 value /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfDone543 value)`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_app_nat_reject594 = prove
 (`!rec fuel env ps g e f a reason.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KApp447 f a) /\
   l4_core_reduce_nat549 rec fuel env g (L4KApp447 f a) = L4KReject491 reason ==>
   l4_whnf_step594 rec fuel env ps g e = L4KReject491 reason /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KReject491 reason`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_app_nat_decline594 = prove
 (`!rec fuel env ps g e f a reason.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KApp447 f a) /\
   l4_core_reduce_nat549 rec fuel env g (L4KApp447 f a) = L4KDecline491 reason ==>
   l4_whnf_step594 rec fuel env ps g e = L4KDecline491 reason /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KDecline491 reason`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_kr_bind491]);;
let l4_whnf_app_delta594 = prove
 (`!rec fuel env ps g e f a value.
   l4_whnf_core_step594 rec fuel env ps F g e = L4KAccept491 (L4KApp447 f a) /\
   l4_core_reduce_nat549 rec fuel env g (L4KApp447 f a) = L4KAccept491 NONE /\
   l4_core_unfold528 env ps (L4KApp447 f a) = L4KAccept491 (SOME value) ==>
   l4_whnf_step594 rec fuel env ps g e = l4_whnf_method543 rec g value /\
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfContinue543 value)`,
  SIMP_TAC [l4_whnf_step594;l4_whnf_round_step594;l4_finish_whnf_unfold594;l4_kr_bind491]);;

let l4_finish_unfold_some594 = prove
 (`!env ps e value. l4_core_unfold528 env ps e = L4KAccept491 (SOME value) ==>
   l4_finish_whnf_unfold594 env ps e = L4KAccept491 (L4WhnfContinue543 value)`,
  SIMP_TAC [l4_finish_whnf_unfold594;l4_kr_bind491]);;
let l4_finish_unfold_none594 = prove
 (`!env ps e. l4_core_unfold528 env ps e = L4KAccept491 NONE ==>
   l4_finish_whnf_unfold594 env ps e = L4KAccept491 (L4WhnfDone543 e)`,
  SIMP_TAC [l4_finish_whnf_unfold594;l4_kr_bind491]);;
let l4_finish_unfold_reject594 = prove
 (`!env ps e reason. l4_core_unfold528 env ps e = L4KReject491 reason ==>
   l4_finish_whnf_unfold594 env ps e = L4KReject491 reason`,
  SIMP_TAC [l4_finish_whnf_unfold594;l4_kr_bind491]);;
let l4_finish_unfold_decline594 = prove
 (`!env ps e reason. l4_core_unfold528 env ps e = L4KDecline491 reason ==>
   l4_finish_whnf_unfold594 env ps e = L4KDecline491 reason`,
  SIMP_TAC [l4_finish_whnf_unfold594;l4_kr_bind491]);;

let l4_whnf_loop_zero594 = prove
 (`!rec fuel env ps g e.
   l4_whnf_loop594 0 rec fuel env ps g e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_whnf_loop594;l4_run_whnf_rounds543]);;
let l4_whnf_loop_done594 = prove
 (`!rounds rec fuel env ps g e value.
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfDone543 value) ==>
   l4_whnf_loop594 (SUC rounds) rec fuel env ps g e = L4KAccept491 value`,
  SIMP_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_kr_bind491]);;
let l4_whnf_loop_continue594 = prove
 (`!rounds rec fuel env ps g e value.
   l4_whnf_round_step594 rec fuel env ps g e = L4KAccept491 (L4WhnfContinue543 value) ==>
   l4_whnf_loop594 (SUC rounds) rec fuel env ps g e =
     l4_whnf_loop594 rounds rec fuel env ps g value`,
  SIMP_TAC [l4_whnf_loop594;l4_run_whnf_rounds543;l4_kr_bind491]);;
