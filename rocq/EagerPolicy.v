(* SPDX-License-Identifier: Apache-2.0
   Pure policy helpers for Lean4Lean 8223d223ed98661882e95d9d6a7126df7097cd76,
   TypeChecker.lean 299-303, 782, 845. Shared by ordinary and accessor methods. *)
From Stdlib Require Import List String Bool Arith.
From LeanPort Require Import Syntax.
Import ListNotations.

Inductive reduction_mode := NormalReduction | EagerReduction.

(* Ambient bound variables stand for upstream instantiated FVars. Only binders
   inside this expression contribute to depth; the ambient context does not. *)
Fixpoint has_external_local_at (depth : nat) (e : expr) : bool :=
  match e with
  | EBVar i => negb (i <? depth)
  | EFVar _ => true
  | EApp a b => has_external_local_at depth a || has_external_local_at depth b
  | ELam _ _ a b | EPi _ _ a b =>
      has_external_local_at depth a || has_external_local_at (S depth) b
  | ELet _ a v b _ =>
      has_external_local_at depth a || has_external_local_at depth v ||
        has_external_local_at (S depth) b
  | EProj _ _ a | EMData a => has_external_local_at depth a
  | _ => false
  end.

Definition has_external_local := has_external_local_at 0.

Fixpoint has_named_fvar (e : expr) : bool :=
  match e with
  | EFVar _ => true
  | EApp a b | ELam _ _ a b | EPi _ _ a b =>
      has_named_fvar a || has_named_fvar b
  | ELet _ a v b _ => has_named_fvar a || has_named_fvar v || has_named_fvar b
  | EProj _ _ a | EMData a => has_named_fvar a
  | _ => false
  end.

Lemma has_external_local_at_spec e depth :
  has_external_local_at depth e = (has_named_fvar e || negb (scoped depth e)).
Proof.
  revert depth. induction e; intro depth;
    cbn [has_external_local_at has_named_fvar scoped];
    try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe;
    repeat match goal with
    | |- context [has_named_fvar ?x] => destruct (has_named_fvar x)
    | |- context [scoped ?d ?x] => destruct (scoped d x)
    end; reflexivity.
Qed.

Lemma has_external_local_false_iff e depth :
  has_external_local_at depth e = false <->
    has_named_fvar e = false /\ scoped depth e = true.
Proof.
  rewrite has_external_local_at_spec, Bool.orb_false_iff, Bool.negb_false_iff.
  reflexivity.
Qed.

Definition nat_probe_allowed (mode : reduction_mode) (t s : expr) : bool :=
  match mode with
  | EagerReduction => true
  | NormalReduction => negb (has_external_local t) && negb (has_external_local s)
  end.

Definition true_probe_allowed (mode : reduction_mode) (t : expr) : bool :=
  match mode with
  | EagerReduction => true
  | NormalReduction => negb (has_external_local t)
  end.

Definition eager_reduce_name := NameStr NameAnon "eagerReduce"%string.

Definition is_eager_reduce_argument (e : expr) : bool :=
  match e with
  | EApp (EApp (EConst n _) _) _ => name_eqb n eager_reduce_name
  | _ => false
  end.

Lemma normal_nat_probe_allowed_iff t s :
  nat_probe_allowed NormalReduction t s = true <->
    has_external_local t = false /\ has_external_local s = false.
Proof.
  unfold nat_probe_allowed. rewrite Bool.andb_true_iff, !Bool.negb_true_iff.
  reflexivity.
Qed.

Lemma eager_nat_probe_allowed t s : nat_probe_allowed EagerReduction t s = true.
Proof. reflexivity. Qed.

Lemma normal_true_probe_allowed_iff t :
  true_probe_allowed NormalReduction t = true <-> has_external_local t = false.
Proof. unfold true_probe_allowed. apply Bool.negb_true_iff. Qed.

Lemma eager_true_probe_allowed t : true_probe_allowed EagerReduction t = true.
Proof. reflexivity. Qed.

Print Assumptions has_external_local_at_spec.
Print Assumptions has_external_local_false_iff.
Print Assumptions normal_nat_probe_allowed_iff.
Print Assumptions eager_nat_probe_allowed.
Print Assumptions normal_true_probe_allowed_iff.
Print Assumptions eager_true_probe_allowed.
