(* SPDX-License-Identifier: Apache-2.0
   Private memoization of infer_step's syntactic descent. The reference
   algorithm is Lean4Lean 8223d223ed98661882e95d9d6a7126df7097cd76,
   independently ported in the unchanged dispatch-enabled Checker.v. *)
From Stdlib Require Import List Bool PArith.BinPos FSets.FMapPositive.
From LeanPort Require Import Syntax Checker DagScope DagMemo DagArena DagQuery
  LookupIntegration LookupCore LookupRefinement.
Import ListNotations.
Set Implicit Arguments.

Notation "x <@ a ;; b" := (then_do a (fun x => b))
  (at level 100, a at next level, right associativity).

Section Inference.
  Context (lookup : declaration_lookup).
  Context (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (base : context) (arena : dag_arena).
  Hypothesis Lookup : forall n, lookup n = find_decl n env.
  Local Abbreviation eval := (step_eval rec fuel env ps base arena).
  Local Abbreviation exact_action := (refines rec fuel env ps base arena).

  Definition lookup_step checking g e :=
    Accessor.infer_step (fun n _ => lookup n) rec fuel env ps checking g e.
  Lemma lookup_step_refines checking g e :
    lookup_step checking g e = infer_step rec fuel env ps checking g e.
  Proof. apply infer_step_refines; auto using methods_equivalent_refl. Qed.

  Definition lookup_eval checking (q : input_query) : result expr :=
    let '(id,path) := q in
    g <- path_from base (arena_scope arena) path ;;
    e <- scope_ref (arena_scope arena) id ;;
    lookup_step checking g (scope_expr e).
  Lemma lookup_eval_refines checking q : lookup_eval checking q = eval checking q.
  Proof.
    destruct q as [id path]. unfold lookup_eval, step_eval.
    apply bind_pointwise; [reflexivity|intro g].
    apply bind_pointwise; [reflexivity|intro e]. apply lookup_step_refines.
  Qed.

  Definition node_action (call : bool -> input_query -> action expr)
      (checking : bool) (path : context_path) (g : context) (node : dag_node)
      : action expr :=
    match node with
    | DApp f a =>
        ae <@ pure (scope_ref (arena_scope arena) a) ;;
        ft <@ call checking (f,path) ;;
        ft <@ pure (whnf_method rec g ft) ;;
        match ft with
        | EPi _ _ domain body =>
            ignored <@ (if checking then
              arg_type <@ call true (a,path) ;;
              ok <@ pure (application_type_defeq rec g (scope_expr ae) domain arg_type) ;;
              pure (require ok TypeMismatch)
              else pure (Accept tt)) ;;
            pure (Accept (instantiate body (scope_expr ae)))
        | _ => pure (Reject ExpectedPi)
        end
    | DLam n bi a b =>
        ae <@ pure (scope_ref (arena_scope arena) a) ;;
        ignored <@ (if checking then
          dt <@ call true (a,path) ;;
          dt <@ pure (whnf_method rec g dt) ;;
          pure (match dt with ESort _ => Accept tt | _ => Reject ExpectedSort end)
          else pure (Accept tt)) ;;
        bt <@ call checking (b,(a,None)::path) ;;
        pure (Accept (EPi n bi (scope_expr ae) bt))
    | DPi n bi a b =>
        ae <@ pure (scope_ref (arena_scope arena) a) ;;
        dt <@ call checking (a,path) ;;
        dt <@ pure (whnf_method rec g dt) ;;
        u <@ pure (match dt with ESort u => Accept u | _ => Reject ExpectedSort end) ;;
        let gb := push_binding g (scope_expr ae) None in
        bt <@ call checking (b,(a,None)::path) ;;
        bt <@ pure (whnf_method rec gb bt) ;;
        v <@ pure (match bt with ESort v => Accept v | _ => Reject ExpectedSort end) ;;
        pure (Accept (ESort (LIMax u v)))
    | DLet n a v b nd =>
        ae <@ pure (scope_ref (arena_scope arena) a) ;;
        ve <@ pure (scope_ref (arena_scope arena) v) ;;
        ignored <@ (if checking then
          dt <@ call true (a,path) ;;
          dt <@ pure (whnf_method rec g dt) ;;
          ignored <@ pure (match dt with ESort _ => Accept tt | _ => Reject ExpectedSort end) ;;
          vt <@ call true (v,path) ;;
          ok <@ pure (defeq_method rec g vt (scope_expr ae)) ;;
          pure (require ok TypeMismatch)
          else pure (Accept tt)) ;;
        bt <@ call checking (b,(a,Some v)::path) ;;
        pure (Accept (instantiate bt (scope_expr ve)))
    | DMData a => call checking (a,path)
    | _ =>
        e <@ pure (scope_node (arena_scope arena) node) ;;
        pure (lookup_step checking g (scope_expr e))
    end.

  Lemma call_known call :
    (forall mode q, exact_action (call mode q) (eval mode q)) ->
    forall mode id path g entry,
    path_from base (arena_scope arena) path = Accept g ->
    scope_ref (arena_scope arena) id = Accept entry ->
    exact_action (call mode (id,path))
      (infer_step rec fuel env ps mode g (scope_expr entry)).
  Proof.
    intros H mode id path g entry Hpath Hentry.
    rewrite <- (@step_eval_known rec fuel env ps base arena mode id path g entry Hpath Hentry).
    apply H.
  Qed.

  Lemma pure_then A B (v : A) (f : A -> action B) :
    then_do (pure (Accept v)) f = f v.
  Proof. reflexivity. Qed.

  Local Ltac known_path :=
    cbn [path_from];
    repeat match goal with
    | H : path_from _ _ _ = _ |- _ => rewrite H
    | H : scope_ref _ _ = _ |- context [scope_ref _ _] => rewrite H
    end; reflexivity.

  Local Ltac action_steps :=
    first [apply pure_refines
    | eapply call_known; [eassumption | known_path | eassumption]
    | eapply then_refines; [action_steps | intro; action_steps]
    | match goal with
      | |- exact_action (if ?b then _ else _) _ => destruct b; action_steps
      | |- exact_action (match ?e with _ => _ end) _ => destruct e; action_steps
      end].

  Lemma node_action_refines call checking path g node entry :
    (forall mode q, exact_action (call mode q) (eval mode q)) ->
    path_from base (arena_scope arena) path = Accept g ->
    scope_node (arena_scope arena) node = Accept entry ->
    exact_action (node_action call checking path g node)
      (infer_step rec fuel env ps checking g (scope_expr entry)).
  Proof.
    intros Calls Path Node.
    destruct node; cbn [scope_node] in Node;
      repeat match type of Node with
      | context [scope_ref (arena_scope arena) ?id] =>
        let E := fresh "Child" in destruct (scope_ref (arena_scope arena) id) eqn:E;
          cbn [bind] in Node; try discriminate
      end;
      inversion Node; subst entry; cbn [node_action scope_expr];
      repeat match goal with
      | E : scope_ref _ _ = _ |- context [scope_ref _ _] => rewrite E
      end;
      repeat rewrite pure_then;
      repeat rewrite lookup_step_refines;
      cbn [infer_step scope_expr].
    all: try action_steps.
    all: cbn [scope_node];
      repeat match goal with
      | E : scope_ref _ _ = _ |- context [scope_ref _ _] => rewrite E
      end;
      cbn [bind]; repeat rewrite pure_then; rewrite lookup_step_refines;
      apply pure_refines.
  Qed.

  Definition uncached_action (call : bool -> input_query -> action expr)
      checking (q : input_query) : action expr :=
    let '(id,path) := q in
    g <@ pure (path_from base (arena_scope arena) path) ;;
    e <@ pure (scope_ref (arena_scope arena) id) ;;
    match PositiveMap.find id (arena_nodes arena) with
    | Some node => node_action call checking path g node
    | None => pure (lookup_step checking g (scope_expr e))
    end.

  Lemma uncached_action_refines call checking q : arena_ok arena ->
    (forall mode q, exact_action (call mode q) (eval mode q)) ->
    exact_action (uncached_action call checking q) (eval checking q).
  Proof.
    intros Arena Calls. destruct q as [id path]. unfold uncached_action, step_eval.
    destruct (path_from base (arena_scope arena) path) eqn:Path;
      cbn [bind]; try apply pure_refines.
    rewrite pure_then. destruct (scope_ref (arena_scope arena) id) eqn:Entry;
      cbn [bind].
    2,3: intros cache H; split; [reflexivity|exact H].
    rewrite pure_then. destruct (@arena_ref_node arena id s Arena Entry) as [node [Raw Denote]].
    rewrite Raw. eapply node_action_refines; eauto.
  Qed.

  (* Budget controls only this optimization. Exhaustion runs the very same
     inference step with the same semantic fuel, rather than issuing a verdict. *)
  Fixpoint memo_infer (budget : nat) checking q : action expr :=
    memo_action checking q
      (fun cache =>
       match budget with
       | 0 => pure (lookup_eval checking q) cache
       | S n => uncached_action (memo_infer n) checking q cache
       end).

  Theorem memo_infer_refines budget checking q : arena_ok arena ->
    exact_action (memo_infer budget checking q) (eval checking q).
  Proof.
    intros Arena. revert checking q. induction budget; intros checking q;
      cbn [memo_infer]; apply memo_action_refines.
    - rewrite lookup_eval_refines. apply pure_refines.
    - apply uncached_action_refines; auto.
  Qed.

  Definition run_memo_infer budget checking q : result expr :=
    fst (memo_infer budget checking q empty_step_cache).

  Theorem run_memo_infer_refines budget checking q : arena_ok arena ->
    run_memo_infer budget checking q = eval checking q.
  Proof.
    intro H. unfold run_memo_infer.
    pose proof (memo_infer_refines budget checking q H) as R.
    unfold refines in R. exact (proj1 (@R empty_step_cache
      (empty_step_cache_ok rec fuel env ps base arena))).
  Qed.

End Inference.

Print Assumptions memo_infer_refines.
Print Assumptions run_memo_infer_refines.
