(* SPDX-License-Identifier: Apache-2.0
   Private checked DAG arena. Node identity comes only from fresh table entries;
   no pointer equality, external certificate, or extraction override is used. *)
From Stdlib Require Import List PArith.BinPos FSets.FMapPositive.
From LeanPort Require Import Syntax DagScope.
Import ListNotations.
Set Implicit Arguments.

Definition scope_extends (a b : scope_table) :=
  forall id e, PositiveMap.find id a = Some e -> PositiveMap.find id b = Some e.

Lemma scope_ref_extends a b id e : scope_extends a b ->
  scope_ref a id = Accept e -> scope_ref b id = Accept e.
Proof.
  intros H E. unfold scope_ref in *. destruct (PositiveMap.find id a) eqn:F;
    try discriminate. inversion E; subst. rewrite (H _ _ F). reflexivity.
Qed.

Lemma scope_node_extends a b node e : scope_extends a b ->
  scope_node a node = Accept e -> scope_node b node = Accept e.
Proof.
  intros H. destruct node; cbn [scope_node]; intro E;
    repeat match type of E with
    | context [scope_ref a ?id] =>
      let F := fresh "F" in destruct (scope_ref a id) eqn:F;
        cbn [bind] in E; try discriminate;
        rewrite (@scope_ref_extends a b id _ H F); cbn [bind]
    end; exact E.
Qed.

Lemma fresh_scope_extends table id entry : PositiveMap.find id table = None ->
  scope_extends table (PositiveMap.add id entry table).
Proof.
  intros Fresh other value H. destruct (Pos.eq_dec id other) as [E|E].
  - subst. rewrite Fresh in H. discriminate.
  - rewrite ScopeMapFacts.add_neq_o by exact E. exact H.
Qed.

Record dag_arena := {
  arena_scope : scope_table;
  arena_nodes : PositiveMap.t dag_node
}.

(* Only successful decoded entries are observable. Every one has its exact
   original node and unchanged child denotations in the final arena. *)
Definition arena_ok (arena : dag_arena) :=
  scope_table_ok (arena_scope arena) /\
  forall id entry, PositiveMap.find id (arena_scope arena) = Some entry ->
    exists node, PositiveMap.find id (arena_nodes arena) = Some node /\
      scope_node (arena_scope arena) node = Accept entry.

Definition empty_arena : dag_arena :=
  {| arena_scope := PositiveMap.empty _; arena_nodes := PositiveMap.empty _ |}.

Definition arena_add arena id node : result dag_arena :=
  match PositiveMap.find id (arena_scope arena) with
  | Some _ => Reject DuplicateDeclaration
  | None =>
      entry <- scope_node (arena_scope arena) node ;;
      Accept {| arena_scope := PositiveMap.add id entry (arena_scope arena);
                arena_nodes := PositiveMap.add id node (arena_nodes arena) |}
  end.

Lemma empty_arena_ok : arena_ok empty_arena.
Proof.
  split; [apply empty_scope_table_ok |]. intros id entry H.
  rewrite ScopeMapFacts.empty_o in H. discriminate.
Qed.

Lemma arena_add_ok arena id node next : arena_ok arena ->
  arena_add arena id node = Accept next -> arena_ok next.
Proof.
  intros [Hs Hn] E. unfold arena_add in E.
  destruct (PositiveMap.find id (arena_scope arena)) eqn:Fresh; try discriminate.
  destruct (scope_node (arena_scope arena) node) eqn:Hnode;
    cbn [bind] in E; try discriminate. inversion E; subst next.
  assert (Ext : scope_extends (arena_scope arena)
    (PositiveMap.add id s (arena_scope arena))) by
    (apply fresh_scope_extends; exact Fresh).
  split; cbn [arena_scope arena_nodes].
  - eapply scope_add_ok; [exact Hs |].
    unfold scope_add. rewrite Fresh, Hnode. reflexivity.
  - intros other entry Find. destruct (Pos.eq_dec id other) as [Same|Different].
    + subst other. rewrite ScopeMapFacts.add_eq_o in Find by reflexivity.
      inversion Find; subst entry. exists node. split.
      * apply ScopeMapFacts.add_eq_o. reflexivity.
      * eapply scope_node_extends; eauto.
    + rewrite ScopeMapFacts.add_neq_o in Find by exact Different.
      destruct (Hn _ _ Find) as [old [Raw Denote]]. exists old. split.
      * rewrite ScopeMapFacts.add_neq_o by exact Different. exact Raw.
      * eapply scope_node_extends; eauto.
Qed.

Fixpoint arena_build arena rows : result dag_arena :=
  match rows with
  | [] => Accept arena
  | (id,node)::rows => next <- arena_add arena id node ;; arena_build next rows
  end.

Theorem arena_build_ok rows : forall arena next, arena_ok arena ->
  arena_build arena rows = Accept next -> arena_ok next.
Proof.
  induction rows as [|[id node] rows IH]; intros arena next H E;
    cbn [arena_build] in E.
  - inversion E; subst. exact H.
  - destruct (arena_add arena id node) eqn:F; cbn [bind] in E; try discriminate.
    eapply IH; [eapply arena_add_ok; eauto | exact E].
Qed.

Lemma arena_ref_node arena id entry : arena_ok arena ->
  scope_ref (arena_scope arena) id = Accept entry ->
  exists node, PositiveMap.find id (arena_nodes arena) = Some node /\
    scope_node (arena_scope arena) node = Accept entry.
Proof.
  intros [_ H] E. unfold scope_ref in E.
  destruct (PositiveMap.find id (arena_scope arena)) eqn:F; try discriminate.
  inversion E; subst. eauto.
Qed.

Print Assumptions arena_build_ok.
