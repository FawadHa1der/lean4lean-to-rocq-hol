(* SPDX-License-Identifier: Apache-2.0
   Private, per-batch memo invariant for input-DAG inference queries.
   This does not replace recursive inference or declaration admission. *)
From Stdlib Require Import List Bool PArith.BinPos FSets.FMapPositive FSets.FMapFacts.
From LeanPort Require Import Syntax Checker DagScope.
Import ListNotations.
Set Implicit Arguments.

(* Newest binder first. A let value is part of the key, not just its type/depth. *)
Definition context_path := list (positive * option positive).
Definition value_key_eqb (a b : option positive) : bool :=
  match a,b with
  | None,None => true
  | Some a,Some b => Pos.eqb a b
  | _,_ => false
  end.
Fixpoint path_eqb (a b : context_path) : bool :=
  match a,b with
  | [],[] => true
  | (t,v)::a,(u,w)::b => Pos.eqb t u && value_key_eqb v w && path_eqb a b
  | _,_ => false
  end.
Lemma value_key_eqb_spec a b : value_key_eqb a b = true <-> a = b.
Proof. destruct a,b; simpl; try rewrite Pos.eqb_eq; split; congruence. Qed.
Lemma path_eqb_spec a b : path_eqb a b = true <-> a = b.
Proof.
  revert b; induction a as [|[t v] a IH]; intros [|[u w] b]; simpl;
    try (split; congruence).
  rewrite !andb_true_iff, Pos.eqb_eq, value_key_eqb_spec, IH. split.
  - intros [[H1 H2] H3]. subst. reflexivity.
  - intro H. inversion H. auto.
Qed.

Fixpoint path_context (arena : scope_table) (path : context_path) : result context :=
  match path with
  | [] => Accept empty_context
  | (type_id,value_id)::path =>
      g <- path_context arena path ;;
      ty <- scope_ref arena type_id ;;
      value <- match value_id with
               | None => Accept None
               | Some id => v <- scope_ref arena id ;; Accept (Some (scope_expr v))
               end ;;
      Accept (push_binding g (scope_expr ty) value)
  end.

Definition input_query := (positive * context_path)%type.
Definition eval_query (fuel : nat) (env : environment) (ps : list name)
    (arena : scope_table) (q : input_query) : result expr :=
  let '(id,path) := q in
  g <- path_context arena path ;;
  e <- scope_ref arena id ;;
  infer fuel env ps g (scope_expr e).

Definition query_cache := PositiveMap.t (list (context_path * result expr)).
Fixpoint find_path (path : context_path) (entries : list (context_path * result expr))
    : option (result expr) :=
  match entries with
  | [] => None
  | (key,value)::entries => if path_eqb path key then Some value else find_path path entries
  end.
Definition cache_find (q : input_query) (cache : query_cache) : option (result expr) :=
  let '(id,path) := q in
  match PositiveMap.find id cache with
  | None => None
  | Some entries => find_path path entries
  end.
Definition cache_add (q : input_query) (value : result expr) (cache : query_cache)
    : query_cache :=
  let '(id,path) := q in
  let entries := match PositiveMap.find id cache with Some xs => xs | None => [] end in
  PositiveMap.add id ((path,value)::entries) cache.

Definition cache_ok (eval : input_query -> result expr) (cache : query_cache) :=
  forall q value, cache_find q cache = Some value -> eval q = value.

Lemma empty_cache_ok eval : cache_ok eval (PositiveMap.empty _).
Proof.
  intros [id path] value H. unfold cache_find in H.
  rewrite ScopeMapFacts.empty_o in H. discriminate.
Qed.

Lemma cache_add_ok eval q cache : cache_ok eval cache ->
  cache_ok eval (cache_add q (eval q) cache).
Proof.
  destruct q as [id path]. intros H [other opath] value Hfind.
  unfold cache_find, cache_add in Hfind.
  destruct (Pos.eq_dec id other) as [E | E].
  - subst other. rewrite ScopeMapFacts.add_eq_o in Hfind by reflexivity.
    cbn [find_path] in Hfind. destruct (path_eqb opath path) eqn:Hp.
    + apply path_eqb_spec in Hp. subst opath. inversion Hfind. reflexivity.
    + apply (H (id,opath)). unfold cache_find.
      destruct (PositiveMap.find id cache); auto; discriminate.
  - rewrite ScopeMapFacts.add_neq_o in Hfind by exact E.
    exact (H (other,opath) value Hfind).
Qed.

Definition memo_query (eval : input_query -> result expr) (cache : query_cache)
    (q : input_query) : result expr * query_cache :=
  match cache_find q cache with
  | Some value => (value,cache)
  | None => let value := eval q in (value,cache_add q value cache)
  end.

Lemma memo_query_correct eval cache q : cache_ok eval cache ->
  fst (memo_query eval cache q) = eval q /\
  cache_ok eval (snd (memo_query eval cache q)).
Proof.
  intro H. unfold memo_query. destruct (cache_find q cache) eqn:E; simpl.
  - split; auto. symmetry. eapply H. exact E.
  - split; auto. apply cache_add_ok. exact H.
Qed.

Fixpoint query_batch (eval : input_query -> result expr) (cache : query_cache)
    (queries : list input_query) : list (result expr) :=
  match queries with
  | [] => []
  | q::queries =>
      let '(value,cache) := memo_query eval cache q in
      value :: query_batch eval cache queries
  end.

Theorem query_batch_correct eval queries : forall cache,
  cache_ok eval cache -> query_batch eval cache queries = map eval queries.
Proof.
  induction queries as [|q queries IH]; intros cache H; simpl; auto.
  pose proof (memo_query_correct q H) as Hmemo.
  destruct (memo_query eval cache q) as [value next]. simpl in Hmemo.
  destruct Hmemo as [E Hnext]. rewrite E, IH by exact Hnext. reflexivity.
Qed.

(* All logical inputs captured once; no cache can cross an environment, fuel,
   universe list or mode boundary. Every query is checked inference. *)
Definition infer_queries (fuel : nat) (env : environment) (ps : list name)
    (nodes : list (positive * dag_node)) (queries : list input_query)
    : result (list (result expr)) :=
  arena <- scope_build (PositiveMap.empty scope_entry) nodes ;;
  Accept (query_batch (eval_query fuel env ps arena) (PositiveMap.empty _) queries).

Theorem infer_queries_correct fuel env ps nodes queries arena :
  scope_build (PositiveMap.empty scope_entry) nodes = Accept arena ->
  infer_queries fuel env ps nodes queries =
    Accept (map (eval_query fuel env ps arena) queries).
Proof.
  intro H. unfold infer_queries. rewrite H. cbn [bind].
  rewrite query_batch_correct by apply empty_cache_ok. reflexivity.
Qed.

Definition context_test_nodes :=
  [(1%positive, DSort LZero); (2%positive, DSort (LSucc LZero)); (3%positive, DBVar 0)].
Example same_depth_different_types_do_not_share_results :
  infer_queries 8 [] [] context_test_nodes
    [(3%positive,[(1%positive,None)]); (3%positive,[(2%positive,None)]);
     (3%positive,[(1%positive,None)])] =
  Accept [Accept (ESort LZero); Accept (ESort (LSucc LZero)); Accept (ESort LZero)].
Proof. vm_compute. reflexivity. Qed.
Example let_values_are_part_of_context_key :
  path_eqb [(1%positive,Some 1%positive)] [(1%positive,Some 2%positive)] = false.
Proof. reflexivity. Qed.
Example different_fuel_batches_do_not_share :
  infer_queries 0 [] [] context_test_nodes [(1%positive,[])] = Accept [Decline OutOfFuel].
Proof. reflexivity. Qed.
Example missing_context_node_rejects :
  infer_queries 8 [] [] context_test_nodes [(3%positive,[(4%positive,None)])] =
    Accept [Reject MalformedDeclaration].
Proof. reflexivity. Qed.

Print Assumptions infer_queries_correct.
