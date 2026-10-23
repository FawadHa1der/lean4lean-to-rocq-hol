(* SPDX-License-Identifier: Apache-2.0
   Scheduling laws for the newly ordered ordinary loop, not old/new equality. *)
From Stdlib Require Import List.
From LeanPort Require Import Syntax EagerPolicy Checker LookupCore LookupRefinement GuardOrderRefinement.

Section Scheduling.
Variables (rounds fuel : nat) (rec : methods) (env : environment)
  (ps : list name) (g : context) (t s : expr).
Hypothesis quick_none : core_quick rec fuel g t s = Accept None.
Hypothesis offset_none : core_offset rec env g t s = Accept None.
Hypothesis eligible : nat_probe_allowed (method_mode rec) t s = true.

Lemma nat_probe_left_success tn :
  core_reduce_nat rec fuel env g t = Accept (Some tn) ->
  core_lazy_delta (S rounds) rec fuel env ps g t s =
    bind (defeq_method rec g tn s) (fun ok => Accept (ConversionDone ok)).
Proof.
  intro H. rewrite guard_order_lazy_delta_exact. cbn [stage3_lazy_delta]. rewrite quick_none. cbn [bind].
  rewrite offset_none. cbn [bind]. rewrite eligible, H. reflexivity.
Qed.

Lemma nat_probe_right_success sn :
  core_reduce_nat rec fuel env g t = Accept None ->
  core_reduce_nat rec fuel env g s = Accept (Some sn) ->
  core_lazy_delta (S rounds) rec fuel env ps g t s =
    bind (defeq_method rec g t sn) (fun ok => Accept (ConversionDone ok)).
Proof.
  intros Ht Hs. rewrite guard_order_lazy_delta_exact. cbn [stage3_lazy_delta]. rewrite quick_none. cbn [bind].
  rewrite offset_none. cbn [bind]. rewrite eligible, Ht. cbn [bind].
  rewrite Hs. reflexivity.
Qed.

Lemma nat_probe_left_reject error :
  core_reduce_nat rec fuel env g t = Reject error ->
  core_lazy_delta (S rounds) rec fuel env ps g t s = Reject error.
Proof.
  intro H. rewrite guard_order_lazy_delta_exact. cbn [stage3_lazy_delta]. rewrite quick_none. cbn [bind].
  rewrite offset_none. cbn [bind]. rewrite eligible, H. reflexivity.
Qed.

Lemma nat_probe_left_decline reason :
  core_reduce_nat rec fuel env g t = Decline reason ->
  core_lazy_delta (S rounds) rec fuel env ps g t s = Decline reason.
Proof.
  intro H. rewrite guard_order_lazy_delta_exact. cbn [stage3_lazy_delta]. rewrite quick_none. cbn [bind].
  rewrite offset_none. cbn [bind]. rewrite eligible, H. reflexivity.
Qed.
End Scheduling.

Print Assumptions nat_probe_left_success.
Print Assumptions nat_probe_right_success.
Print Assumptions nat_probe_left_reject.
Print Assumptions nat_probe_left_decline.
Print Assumptions core_lazy_delta_refines.
Print Assumptions checker_lookup_refines.
