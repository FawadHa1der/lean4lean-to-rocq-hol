(* SPDX-License-Identifier: Apache-2.0
   Exact cache observations, including arbitrary stored Reject/Decline values,
   refine the frozen linear path buckets. No hash injectivity is assumed. *)
From Stdlib Require Import List Bool PArith.BinPos FSets.FMapPositive.
From LeanPort Require Import Syntax DagScope DagMemoReference DagMemo.
Import ListNotations.
Set Implicit Arguments.
Module Old := DagMemoReference.
Module Indexed := DagMemo.

Definition cache_equivalent (old : Old.query_cache) (indexed : Indexed.query_cache) :=
  forall q, Indexed.cache_find q indexed = Old.cache_find q old.

Lemma empty_cache_equivalent : cache_equivalent (PositiveMap.empty _) (PositiveMap.empty _).
Proof.
  intros [id path]. unfold Indexed.cache_find, Old.cache_find.
  rewrite !ScopeMapFacts.empty_o. reflexivity.
Qed.

Lemma old_cache_find_add id path value cache other opath :
  Old.cache_find (other,opath) (Old.cache_add (id,path) value cache) =
    if Pos.eqb id other && Indexed.path_eqb opath path then Some value
    else Old.cache_find (other,opath) cache.
Proof.
  unfold Old.cache_find, Old.cache_add.
  destruct (Pos.eq_dec id other) as [Same|Different].
  - subst other. rewrite ScopeMapFacts.add_eq_o by reflexivity.
    rewrite Pos.eqb_refl. cbn [andb Old.find_path].
    replace (Old.path_eqb opath path) with (Indexed.path_eqb opath path) by reflexivity.
    destruct (Indexed.path_eqb opath path); [reflexivity|].
    destruct (PositiveMap.find id cache); reflexivity.
  - rewrite ScopeMapFacts.add_neq_o by exact Different.
    assert (Pos.eqb id other = false) as E by (apply Pos.eqb_neq; exact Different).
    rewrite E. reflexivity.
Qed.

Theorem cache_add_refines old indexed q value : cache_equivalent old indexed ->
  cache_equivalent (Old.cache_add q value old) (Indexed.cache_add q value indexed).
Proof.
  intros Equivalent [other opath]. destruct q as [id path].
  rewrite Indexed.cache_find_add, old_cache_find_add.
  destruct (Pos.eqb id other && Indexed.path_eqb opath path); [reflexivity|apply Equivalent].
Qed.

Theorem memo_query_refines eval old indexed q : cache_equivalent old indexed ->
  fst (Indexed.memo_query eval indexed q) = fst (Old.memo_query eval old q) /\
  cache_equivalent (snd (Old.memo_query eval old q)) (snd (Indexed.memo_query eval indexed q)).
Proof.
  intro Equivalent. unfold Indexed.memo_query, Old.memo_query.
  rewrite Equivalent. destruct (Old.cache_find q old); cbn.
  - split; [reflexivity|exact Equivalent].
  - split; [reflexivity|apply cache_add_refines; exact Equivalent].
Qed.

Theorem query_batch_refines eval queries : forall old indexed,
  cache_equivalent old indexed ->
  Indexed.query_batch eval indexed queries = Old.query_batch eval old queries.
Proof.
  induction queries as [|q queries IH]; intros old indexed Equivalent; cbn; [reflexivity|].
  pose proof (@memo_query_refines eval old indexed q Equivalent) as H.
  destruct (Indexed.memo_query eval indexed q) as [value next].
  destruct (Old.memo_query eval old q) as [old_value old_next]. cbn in H.
  destruct H as [E Next]. rewrite E. f_equal. apply IH. exact Next.
Qed.

Theorem infer_queries_refines fuel env ps rows queries :
  Indexed.infer_queries fuel env ps rows queries = Old.infer_queries fuel env ps rows queries.
Proof.
  unfold Indexed.infer_queries, Old.infer_queries.
  destruct (scope_build (PositiveMap.empty scope_entry) rows); cbn [bind]; try reflexivity.
  change (Accept (Indexed.query_batch (Old.eval_query fuel env ps s) (PositiveMap.empty _) queries) =
    Accept (Old.query_batch (Old.eval_query fuel env ps s) (PositiveMap.empty _) queries)).
  f_equal. apply query_batch_refines. apply empty_cache_equivalent.
Qed.

Print Assumptions cache_add_refines.
Print Assumptions memo_query_refines.
Print Assumptions infer_queries_refines.
