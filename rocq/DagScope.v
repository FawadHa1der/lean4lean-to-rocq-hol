(* SPDX-License-Identifier: Apache-2.0
   Private scope-summary experiment. No change to the shared checker API. *)
From Stdlib Require Import List Bool Arith NArith PArith.Pnat Lia FSets.FMapPositive FSets.FMapFacts.
From LeanPort Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.

Fixpoint required_depth (e : expr) : nat :=
  match e with
  | EBVar i => S i
  | EApp f a => Nat.max (required_depth f) (required_depth a)
  | ELam _ _ a b | EPi _ _ a b => Nat.max (required_depth a) (Nat.pred (required_depth b))
  | ELet _ a v b _ => Nat.max (Nat.max (required_depth a) (required_depth v))
      (Nat.pred (required_depth b))
  | EProj _ _ a | EMData a => required_depth a
  | _ => 0
  end.

Lemma scoped_required_depth e : forall depth,
  scoped depth e = (required_depth e <=? depth).
Proof.
  induction e; intro depth; simpl; try reflexivity.
  - rewrite IHe1, IHe2. apply Bool.eq_true_iff_eq.
    rewrite andb_true_iff, !Nat.leb_le. lia.
  - rewrite IHe1, IHe2. apply Bool.eq_true_iff_eq.
    rewrite andb_true_iff, !Nat.leb_le. lia.
  - rewrite IHe1, IHe2. apply Bool.eq_true_iff_eq.
    rewrite andb_true_iff, !Nat.leb_le. lia.
  - rewrite IHe1, IHe2, IHe3. apply Bool.eq_true_iff_eq.
    rewrite !andb_true_iff, !Nat.leb_le. lia.
  - auto.
  - auto.
Qed.

Inductive dag_node :=
| DBVar : nat -> dag_node
| DFVar : name -> dag_node
| DMVar : name -> dag_node
| DSort : level -> dag_node
| DConst : name -> list level -> dag_node
| DApp : positive -> positive -> dag_node
| DLam : name -> binder_info -> positive -> positive -> dag_node
| DPi : name -> binder_info -> positive -> positive -> dag_node
| DLet : name -> positive -> positive -> positive -> bool -> dag_node
| DLit : literal -> dag_node
| DProj : name -> nat -> positive -> dag_node
| DMData : positive -> dag_node.

Record scope_entry := { scope_expr : expr; scope_need : N }.
Definition scope_table := PositiveMap.t scope_entry.
Definition scope_entry_ok (e : scope_entry) :=
  N.to_nat (scope_need e) = required_depth (scope_expr e).
Definition scope_table_ok (t : scope_table) :=
  forall id e, PositiveMap.find id t = Some e -> scope_entry_ok e.
Module ScopeMapFacts := WFacts_fun PositiveMap.E PositiveMap.

Definition scope_ref (t : scope_table) (id : positive) : result scope_entry :=
  match PositiveMap.find id t with
  | Some e => Accept e
  | None => Reject MalformedDeclaration
  end.

Definition scope_node (t : scope_table) (n : dag_node) : result scope_entry :=
  match n with
  | DBVar i => Accept {| scope_expr := EBVar i; scope_need := N.of_nat (S i) |}
  | DFVar n => Accept {| scope_expr := EFVar n; scope_need := 0%N |}
  | DMVar n => Accept {| scope_expr := EMVar n; scope_need := 0%N |}
  | DSort u => Accept {| scope_expr := ESort u; scope_need := 0%N |}
  | DConst n us => Accept {| scope_expr := EConst n us; scope_need := 0%N |}
  | DApp f a =>
      f <- scope_ref t f ;; a <- scope_ref t a ;;
      Accept {| scope_expr := EApp (scope_expr f) (scope_expr a);
        scope_need := N.max (scope_need f) (scope_need a) |}
  | DLam n bi a b =>
      a <- scope_ref t a ;; b <- scope_ref t b ;;
      Accept {| scope_expr := ELam n bi (scope_expr a) (scope_expr b);
        scope_need := N.max (scope_need a) (N.pred (scope_need b)) |}
  | DPi n bi a b =>
      a <- scope_ref t a ;; b <- scope_ref t b ;;
      Accept {| scope_expr := EPi n bi (scope_expr a) (scope_expr b);
        scope_need := N.max (scope_need a) (N.pred (scope_need b)) |}
  | DLet n a v b nd =>
      a <- scope_ref t a ;; v <- scope_ref t v ;; b <- scope_ref t b ;;
      Accept {| scope_expr := ELet n (scope_expr a) (scope_expr v) (scope_expr b) nd;
        scope_need := N.max (N.max (scope_need a) (scope_need v)) (N.pred (scope_need b)) |}
  | DLit l => Accept {| scope_expr := ELit l; scope_need := 0%N |}
  | DProj n i a => a <- scope_ref t a ;;
      Accept {| scope_expr := EProj n i (scope_expr a); scope_need := scope_need a |}
  | DMData a => a <- scope_ref t a ;;
      Accept {| scope_expr := EMData (scope_expr a); scope_need := scope_need a |}
  end.

Lemma scope_ref_ok t id e : scope_table_ok t ->
  scope_ref t id = Accept e -> scope_entry_ok e.
Proof.
  intros Ht H. unfold scope_ref in H.
  destruct (PositiveMap.find id t) eqn:He; try discriminate.
  inversion H; subst. eapply Ht. exact He.
Qed.

Lemma scope_node_ok t node e : scope_table_ok t ->
  scope_node t node = Accept e -> scope_entry_ok e.
Proof.
  intros Ht. destruct node; cbn [scope_node]; intro H;
    repeat match type of H with
    | context [scope_ref ?t ?id] =>
      let E := fresh "E" in destruct (scope_ref t id) eqn:E; cbn [bind] in H; try discriminate
    end;
    inversion H; subst; unfold scope_entry_ok; cbn [scope_need scope_expr required_depth];
    rewrite ?Nat2N.id, ?N2Nat.inj_max, ?N2Nat.inj_pred;
    repeat match goal with
    | E : scope_ref t ?id = Accept ?x |- context [N.to_nat (scope_need ?x)] =>
      let Hx := fresh "Hx" in pose proof (@scope_ref_ok t id x Ht E) as Hx;
      unfold scope_entry_ok in Hx; rewrite Hx
    end; try reflexivity; try apply SuccNat2Pos.id_succ.
Qed.

Definition scope_add (t : scope_table) (id : positive) (node : dag_node)
    : result scope_table :=
  match PositiveMap.find id t with
  | Some _ => Reject DuplicateDeclaration
  | None => e <- scope_node t node ;; Accept (PositiveMap.add id e t)
  end.

Lemma scope_add_ok t id node next : scope_table_ok t ->
  scope_add t id node = Accept next -> scope_table_ok next.
Proof.
  intros Ht H. unfold scope_add in H.
  destruct (PositiveMap.find id t); try discriminate.
  destruct (scope_node t node) eqn:He; cbn [bind] in H; try discriminate.
  inversion H; subst. intros key value Hfind.
  destruct (Pos.eq_dec id key) as [E | E].
  - subst key. rewrite ScopeMapFacts.add_eq_o in Hfind by reflexivity.
    inversion Hfind; subst. eapply scope_node_ok; eauto.
  - rewrite ScopeMapFacts.add_neq_o in Hfind by exact E. eapply Ht; eauto.
Qed.

Fixpoint scope_build (t : scope_table) (nodes : list (positive * dag_node))
    : result scope_table :=
  match nodes with
  | [] => Accept t
  | (id,node) :: nodes => t <- scope_add t id node ;; scope_build t nodes
  end.

Lemma scope_build_ok nodes : forall t next, scope_table_ok t ->
  scope_build t nodes = Accept next -> scope_table_ok next.
Proof.
  induction nodes as [|[id node] nodes IH]; intros t next Ht H; cbn [scope_build] in H.
  - inversion H; subst. exact Ht.
  - destruct (scope_add t id node) eqn:He; cbn [bind] in H; try discriminate.
    eapply IH; [eapply scope_add_ok; eauto | exact H].
Qed.

(* Public boundary: only node syntax and references are input. No supplied
   summary, trusted pointer identity, or certificate bit is consumed. *)
Definition decode_scoped (nodes : list (positive * dag_node))
    (root : positive) (depth : nat) : result (expr * bool) :=
  t <- scope_build (PositiveMap.empty scope_entry) nodes ;;
  e <- scope_ref t root ;;
  Accept (scope_expr e, N.leb (scope_need e) (N.of_nat depth)).

Lemma empty_scope_table_ok : scope_table_ok (PositiveMap.empty scope_entry).
Proof. intros id e H. rewrite ScopeMapFacts.empty_o in H. discriminate. Qed.

Theorem decode_scoped_correct nodes root depth e b :
  decode_scoped nodes root depth = Accept (e,b) -> scoped depth e = b.
Proof.
  unfold decode_scoped. destruct (scope_build (PositiveMap.empty scope_entry) nodes) eqn:Ht;
    cbn [bind]; try discriminate.
  destruct (scope_ref s root) eqn:He; cbn [bind]; try discriminate.
  intro H. inversion H; subst. rewrite scoped_required_depth.
  assert (Hgood : scope_entry_ok s0).
  { eapply scope_ref_ok; [eapply scope_build_ok; eauto using empty_scope_table_ok | exact He]. }
  unfold scope_entry_ok in Hgood. rewrite <- Hgood.
  apply Bool.eq_true_iff_eq. rewrite Nat.leb_le, N.leb_le.
  lia.
Qed.

Example root_bound_variable_is_open :
  decode_scoped [(1%positive, DBVar 0)] 1%positive 0 = Accept (EBVar 0, false).
Proof. reflexivity. Qed.
Example depth_changes_same_node_scope :
  decode_scoped [(1%positive, DBVar 0)] 1%positive 1 = Accept (EBVar 0, true).
Proof. reflexivity. Qed.
Example binder_closes_body_but_not_domain :
  decode_scoped [(1%positive, DBVar 0); (2%positive, DLam NameAnon BDefault 1 1)]
    2%positive 0 = Accept (ELam NameAnon BDefault (EBVar 0) (EBVar 0), false).
Proof. reflexivity. Qed.
Example missing_reference_rejects :
  decode_scoped [(1%positive, DApp 2 2)] 1%positive 0 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example duplicate_node_rejects :
  decode_scoped [(1%positive, DBVar 0); (1%positive, DSort LZero)] 1%positive 0 =
    Reject DuplicateDeclaration.
Proof. reflexivity. Qed.
Example self_reference_rejects :
  decode_scoped [(1%positive, DMData 1)] 1%positive 0 = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example sparse_node_keys_work :
  decode_scoped [(1000000%positive, DSort LZero)] 1000000%positive 0 =
    Accept (ESort LZero, true).
Proof. reflexivity. Qed.

Print Assumptions decode_scoped_correct.
