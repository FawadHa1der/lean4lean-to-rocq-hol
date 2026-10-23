(* SPDX-License-Identifier: Apache-2.0
   Fresh query state for one fixed inference-step interpretation. *)
From Stdlib Require Import List Bool PArith.BinPos FSets.FMapPositive.
From LeanPort Require Import Syntax Checker DagScope DagMemoReference DagArena.
Import ListNotations.
Set Implicit Arguments.

Fixpoint path_from (base : context) (arena : scope_table) (path : context_path)
    : result context :=
  match path with
  | [] => Accept base
  | (ty,value)::path =>
      g <- path_from base arena path ;;
      t <- scope_ref arena ty ;;
      v <- match value with
           | None => Accept None
           | Some id => e <- scope_ref arena id ;; Accept (Some (scope_expr e))
           end ;;
      Accept (push_binding g (scope_expr t) v)
  end.

Section Queries.
  Context (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (base : context) (arena : dag_arena).

  Definition step_eval (checking : bool) (q : input_query) : result expr :=
    let '(id,path) := q in
    g <- path_from base (arena_scope arena) path ;;
    e <- scope_ref (arena_scope arena) id ;;
    infer_step rec fuel env ps checking g (scope_expr e).

  Record step_cache := {
    checked_cache : query_cache;
    unchecked_cache : query_cache
  }.
  Definition select_cache (checking : bool) (cache : step_cache) :=
    if checking then checked_cache cache else unchecked_cache cache.
  Definition update_cache (checking : bool) (entries : query_cache) (cache : step_cache) :=
    if checking then {| checked_cache := entries; unchecked_cache := unchecked_cache cache |}
    else {| checked_cache := checked_cache cache; unchecked_cache := entries |}.
  Definition step_cache_ok cache :=
    cache_ok (step_eval true) (checked_cache cache) /\
    cache_ok (step_eval false) (unchecked_cache cache).
  Definition empty_step_cache :=
    {| checked_cache := PositiveMap.empty _; unchecked_cache := PositiveMap.empty _ |}.

  Lemma empty_step_cache_ok : step_cache_ok empty_step_cache.
  Proof. split; apply empty_cache_ok. Qed.
  Lemma selected_cache_ok checking cache : step_cache_ok cache ->
    cache_ok (step_eval checking) (select_cache checking cache).
  Proof. destruct checking; intros [H1 H2]; assumption. Qed.
  Lemma updated_cache_ok checking entries cache : step_cache_ok cache ->
    cache_ok (step_eval checking) entries ->
    step_cache_ok (update_cache checking entries cache).
  Proof. destruct checking; intros [H1 H2] H; split; assumption. Qed.

  Definition action (A : Type) := step_cache -> result A * step_cache.
  Definition pure {A} (value : result A) : action A := fun cache => (value,cache).
  Definition then_do {A B} (a : action A) (f : A -> action B) : action B :=
    fun cache => let '(value,next) := a cache in
      match value with
      | Accept x => f x next
      | Reject why => (Reject why,next)
      | Decline why => (Decline why,next)
      end.
  Definition refines {A} (a : action A) (value : result A) :=
    forall cache, step_cache_ok cache ->
      fst (a cache) = value /\ step_cache_ok (snd (a cache)).

  Lemma pure_refines A (value : result A) : refines (pure value) value.
  Proof. intros cache H. split; auto. Qed.
  Lemma then_refines A B (a : action A) (f : A -> action B) value next :
    refines a value -> (forall x, refines (f x) (next x)) ->
    refines (then_do a f) (bind value next).
  Proof.
    intros H1 H2 cache Hc. specialize (H1 cache Hc).
    unfold then_do. destruct (a cache) as [v c]. cbn in H1.
    destruct H1 as [E Hc']. subst v. destruct value; cbn [bind];
      [apply H2; exact Hc' | split; auto | split; auto].
  Qed.

  Definition memo_action checking q (work : action expr) : action expr :=
    fun cache =>
    match cache_find q (select_cache checking cache) with
    | Some value => (value,cache)
    | None => let '(value,next) := work cache in
        (value,update_cache checking
          (cache_add q value (select_cache checking next)) next)
    end.

  Lemma memo_action_refines checking q work :
    refines work (step_eval checking q) ->
    refines (memo_action checking q work) (step_eval checking q).
  Proof.
    intros Hwork cache Hc. unfold memo_action.
    destruct (cache_find q (select_cache checking cache)) eqn:Find.
    - split; [|exact Hc]. symmetry. eapply selected_cache_ok; eauto.
    - specialize (Hwork cache Hc). destruct (work cache) as [v next]. cbn in Hwork.
      destruct Hwork as [E Hnext]. subst v. split; [reflexivity|].
      apply updated_cache_ok; [exact Hnext|]. apply cache_add_ok.
      apply selected_cache_ok. exact Hnext.
  Qed.

  Lemma step_eval_known checking id path g entry :
    path_from base (arena_scope arena) path = Accept g ->
    scope_ref (arena_scope arena) id = Accept entry ->
    step_eval checking (id,path) =
      infer_step rec fuel env ps checking g (scope_expr entry).
  Proof. intros H1 H2. unfold step_eval. rewrite H1, H2. reflexivity. Qed.
End Queries.

Print Assumptions memo_action_refines.
