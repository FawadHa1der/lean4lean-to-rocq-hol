(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq formalization of Lean4Lean/Theory/Typing/{Basic,Lemmas,Env,
   ChurchRosser,Injectivity,UniqueTyping}.lean: declarative typing &
   definitional equality (VIsDefEq / VHasType / VIsType / VIsDefEqU),
   context weakening, environment monotonicity, parallel reduction,
   Takahashi complete development, Church-Rosser confluence, Pi-injectivity,
   and uniqueness of syntactic typing. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Context Lookup & Weakening (Lean4Lean/Theory/Typing/Basic.lean)        *)
(* ========================================================================= *)

Inductive VLookup : list VExpr -> nat -> VExpr -> Prop :=
| VLookupZero : forall A G,
    VLookup (A :: G) 0 (vlift A)
| VLookupSucc : forall A G i B,
    VLookup G i B ->
    VLookup (A :: G) (S i) (vlift B).

Definition vlookup_fn (G : list VExpr) (i : nat) : option VExpr :=
  match nth_error G i with
  | Some A => Some (vliftN (S i) 0 A)
  | None => None
  end.

Theorem VLookup_deterministic G i A B :
  VLookup G i A -> VLookup G i B -> A = B.
Proof.
  intros H1. revert B.
  induction H1; intros B0 H2; inversion H2; subst; auto.
  f_equal. apply IHVLookup. assumption.
Qed.

Theorem VLookup_length_lt G i A :
  VLookup G i A -> i < List.length G.
Proof.
  intros H. induction H; simpl; lia.
Qed.

Inductive VCtxLiftN (n : nat) : nat -> list VExpr -> list VExpr -> Prop :=
| VCtxLiftN_zero : forall As G,
    List.length As = n ->
    VCtxLiftN n 0 G (As ++ G)
| VCtxLiftN_succ : forall k G G' A,
    VCtxLiftN n k G G' ->
    VCtxLiftN n (S k) (A :: G) (vliftN n k A :: G').

Lemma VCtxLiftN_lookup_zero As G i A :
  VLookup G i A ->
  VLookup (As ++ G) (List.length As + i) (vliftN (List.length As) 0 A).
Proof.
  intros Hlk.
  induction As as [|B rest IH]; simpl.
  - rewrite vliftN_zero. exact Hlk.
  - replace (vliftN (S (List.length rest)) 0 A)
      with (vlift (vliftN (List.length rest) 0 A)).
    2: { unfold vlift. rewrite vliftN_vliftN by lia. reflexivity. }
    constructor. exact IH.
Qed.

Theorem VCtxLiftN_lookup n k G G' i A :
  VCtxLiftN n k G G' ->
  VLookup G i A ->
  VLookup G' (vliftVar n i k) (vliftN n k A).
Proof.
  intros Hctx Hlk. revert i A Hlk.
  induction Hctx as [As G Hlen | k G G' C Hctx IH]; intros i A Hlk.
  - subst n. unfold vliftVar. simpl.
    apply VCtxLiftN_lookup_zero. exact Hlk.
  - inversion Hlk as [A0 G0 Heq1 Heq2 | A0 G0 j B0 Hlk0 Heq1 Heq2]; subst.
    + unfold vliftVar. simpl.
      replace (vliftN n (S k) (vlift C)) with (vlift (vliftN n k C)).
      2: { unfold vlift. symmetry. exact (@vliftN_comm C n 1 k 0 ltac:(lia)). }
      constructor.
    + unfold vliftVar.
      replace (S j <? S k) with (j <? k) by reflexivity.
      replace (if j <? k then S j else n + S j)
        with (S (vliftVar n j k)).
      2: { unfold vliftVar. destruct (j <? k); lia. }
      replace (vliftN n (S k) (vlift B0)) with (vlift (vliftN n k B0)).
      2: { unfold vlift. symmetry. exact (@vliftN_comm B0 n 1 k 0 ltac:(lia)). }
      constructor. apply IH. exact Hlk0.
Qed.

(* ========================================================================= *)
(* 2. Declarative Definitional Equality and Typing (IsDefEq / HasType)       *)
(* ========================================================================= *)

Inductive VIsDefEq (env : VEnv) (uvars : nat) :
    list VExpr -> VExpr -> VExpr -> VExpr -> Prop :=
| VDF_bvar : forall G i ty,
    VLookup G i ty ->
    VIsDefEq env uvars G (VBVar i) (VBVar i) ty
| VDF_symm : forall G e1 e2 ty,
    VIsDefEq env uvars G e1 e2 ty ->
    VIsDefEq env uvars G e2 e1 ty
| VDF_trans : forall G e1 e2 e3 ty,
    VIsDefEq env uvars G e1 e2 ty ->
    VIsDefEq env uvars G e2 e3 ty ->
    VIsDefEq env uvars G e1 e3 ty
| VDF_sortDF : forall G l1 l2,
    vlevel_wf uvars l1 ->
    vlevel_wf uvars l2 ->
    vlevel_equiv l1 l2 ->
    VIsDefEq env uvars G (VSort l1) (VSort l2) (VSort (VLSucc l1))
| VDF_constDF : forall G c ci ls1 ls2,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf uvars) ls1 ->
    Forall (vlevel_wf uvars) ls2 ->
    List.length ls1 = vc_uvars ci ->
    Forall2 vlevel_equiv ls1 ls2 ->
    VIsDefEq env uvars G (VConst c ls1) (VConst c ls2) (vinstL ls1 (vc_type ci))
| VDF_appDF : forall G f1 f2 a1 a2 A B,
    VIsDefEq env uvars G f1 f2 (VForallE A B) ->
    VIsDefEq env uvars G a1 a2 A ->
    VIsDefEq env uvars G (VApp f1 a1) (VApp f2 a2) (vinst0 B a1)
| VDF_lamDF : forall G A1 A2 b1 b2 u B,
    VIsDefEq env uvars G A1 A2 (VSort u) ->
    VIsDefEq env uvars (A1 :: G) b1 b2 B ->
    VIsDefEq env uvars G (VLam A1 b1) (VLam A2 b2) (VForallE A1 B)
| VDF_forallEDF : forall G A1 A2 B1 B2 u v,
    VIsDefEq env uvars G A1 A2 (VSort u) ->
    VIsDefEq env uvars (A1 :: G) B1 B2 (VSort v) ->
    VIsDefEq env uvars G (VForallE A1 B1) (VForallE A2 B2) (VSort (VLIMax u v))
| VDF_defeqDF : forall G e1 e2 A B u,
    VIsDefEq env uvars G A B (VSort u) ->
    VIsDefEq env uvars G e1 e2 A ->
    VIsDefEq env uvars G e1 e2 B
| VDF_beta : forall G A e a B,
    VIsDefEq env uvars (A :: G) e e B ->
    VIsDefEq env uvars G a a A ->
    VIsDefEq env uvars G (VApp (VLam A e) a) (vinst0 e a) (vinst0 B a)
| VDF_eta : forall G e A B,
    VIsDefEq env uvars G e e (VForallE A B) ->
    VIsDefEq env uvars G (VLam A (VApp (vlift e) (VBVar 0))) e (VForallE A B)
| VDF_proofIrrel : forall G p h h',
    VIsDefEq env uvars G p p (VSort VLZero) ->
    VIsDefEq env uvars G h h p ->
    VIsDefEq env uvars G h' h' p ->
    VIsDefEq env uvars G h h' p
| VDF_extra : forall G df ls,
    venv_defeqs env df ->
    Forall (vlevel_wf uvars) ls ->
    List.length ls = vdf_uvars df ->
    VIsDefEq env uvars G (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_rhs df))
      (vinstL ls (vdf_type df)).

Definition VHasType (env : VEnv) (uvars : nat) (G : list VExpr) (e A : VExpr) : Prop :=
  VIsDefEq env uvars G e e A.

Definition VIsType (env : VEnv) (uvars : nat) (G : list VExpr) (A : VExpr) : Prop :=
  exists u, VHasType env uvars G A (VSort u).

Definition VIsDefEqU (env : VEnv) (uvars : nat) (G : list VExpr) (e1 e2 : VExpr) : Prop :=
  exists A, VIsDefEq env uvars G e1 e2 A.

Definition VExprWF (env : VEnv) (uvars : nat) (G : list VExpr) (e : VExpr) : Prop :=
  exists A, VHasType env uvars G e A.

(* ========================================================================= *)
(* 3. Structural Lemmas for Declarative Typing (Lemmas.lean / Env.lean)      *)
(* ========================================================================= *)

Lemma VHasType_bvar env uvars G i ty :
  VLookup G i ty -> VHasType env uvars G (VBVar i) ty.
Proof. apply VDF_bvar. Qed.

Lemma VHasType_sort env uvars G l :
  vlevel_wf uvars l -> VHasType env uvars G (VSort l) (VSort (VLSucc l)).
Proof. intros H. apply VDF_sortDF; [exact H | exact H | apply vlevel_equiv_refl]. Qed.

Lemma VHasType_const env uvars G c ci ls :
  venv_constants env c = Some ci ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = vc_uvars ci ->
  VHasType env uvars G (VConst c ls) (vinstL ls (vc_type ci)).
Proof.
  intros Hc Hls Hlen.
  eapply VDF_constDF; [exact Hc | exact Hls | exact Hls | exact Hlen |].
  clear; induction ls; [constructor | constructor; [apply vlevel_equiv_refl | exact IHls]].
Qed.

Lemma VHasType_app env uvars G f a A B :
  VHasType env uvars G f (VForallE A B) ->
  VHasType env uvars G a A ->
  VHasType env uvars G (VApp f a) (vinst0 B a).
Proof. apply VDF_appDF. Qed.

Lemma VHasType_lam env uvars G A b u B :
  VHasType env uvars G A (VSort u) ->
  VHasType env uvars (A :: G) b B ->
  VHasType env uvars G (VLam A b) (VForallE A B).
Proof. apply VDF_lamDF. Qed.

Lemma VHasType_forallE env uvars G A B u v :
  VHasType env uvars G A (VSort u) ->
  VHasType env uvars (A :: G) B (VSort v) ->
  VHasType env uvars G (VForallE A B) (VSort (VLIMax u v)).
Proof. apply VDF_forallEDF. Qed.

Lemma VIsDefEq_refl_l env uvars G e1 e2 A :
  VIsDefEq env uvars G e1 e2 A -> VHasType env uvars G e1 A.
Proof.
  intros H. eapply VDF_trans; [exact H | apply VDF_symm; exact H].
Qed.

Lemma VIsDefEq_refl_r env uvars G e1 e2 A :
  VIsDefEq env uvars G e1 e2 A -> VHasType env uvars G e2 A.
Proof.
  intros H. eapply VDF_trans; [apply VDF_symm; exact H | exact H].
Qed.

Lemma VIsDefEq_hasType_both env uvars G e1 e2 A :
  VIsDefEq env uvars G e1 e2 A ->
  VHasType env uvars G e1 A /\ VHasType env uvars G e2 A.
Proof.
  intros H. split; [eapply VIsDefEq_refl_l | eapply VIsDefEq_refl_r]; exact H.
Qed.

Lemma VIsDefEqU_symm env uvars G e1 e2 :
  VIsDefEqU env uvars G e1 e2 -> VIsDefEqU env uvars G e2 e1.
Proof.
  intros [A H]. exists A. apply VDF_symm. exact H.
Qed.

Lemma VIsDefEqU_refl_of_hasType env uvars G e A :
  VHasType env uvars G e A -> VIsDefEqU env uvars G e e.
Proof. intros H. exists A. exact H. Qed.

(* Environment ordering monotonicity (Lean4Lean/Theory/Typing/Env.lean) *)
Theorem VEnvOrdered_preserve_VIsDefEq env1 env2 uvars G e1 e2 A :
  venv_ordered env1 env2 ->
  VIsDefEq env1 uvars G e1 e2 A ->
  VIsDefEq env2 uvars G e1 e2 A.
Proof.
  intros Hord H. induction H.
  - apply VDF_bvar; assumption.
  - apply VDF_symm; assumption.
  - eapply VDF_trans; eassumption.
  - apply VDF_sortDF; assumption.
  - eapply VDF_constDF; [apply (venv_ord_const Hord); eassumption | ..]; assumption.
  - eapply VDF_appDF; eassumption.
  - eapply VDF_lamDF; eassumption.
  - eapply VDF_forallEDF; eassumption.
  - eapply VDF_defeqDF; eassumption.
  - eapply VDF_beta; eassumption.
  - eapply VDF_eta; eassumption.
  - eapply VDF_proofIrrel; eassumption.
  - eapply VDF_extra; [apply (venv_ord_defeq Hord); eassumption | ..]; assumption.
Qed.

Corollary VEnvOrdered_preserve_VHasType env1 env2 uvars G e A :
  venv_ordered env1 env2 ->
  VHasType env1 uvars G e A ->
  VHasType env2 uvars G e A.
Proof. apply VEnvOrdered_preserve_VIsDefEq. Qed.

Corollary VEnvOrdered_preserve_VIsType env1 env2 uvars G A :
  venv_ordered env1 env2 ->
  VIsType env1 uvars G A ->
  VIsType env2 uvars G A.
Proof.
  intros Hord [u Hu]. exists u. eapply VEnvOrdered_preserve_VHasType; eassumption.
Qed.

Corollary VEnvOrdered_preserve_VIsDefEqU env1 env2 uvars G e1 e2 :
  venv_ordered env1 env2 ->
  VIsDefEqU env1 uvars G e1 e2 ->
  VIsDefEqU env2 uvars G e1 e2.
Proof.
  intros Hord [A HA]. exists A. eapply VEnvOrdered_preserve_VIsDefEq; eassumption.
Qed.

(* Environment well-formedness (Lean4Lean/Theory/Typing/Env.lean) *)
Definition VConstantWF (env : VEnv) (ci : VConstant) : Prop :=
  VIsType env (vc_uvars ci) [] (vc_type ci) /\ vclosed (vc_type ci).

Definition VDefEqWF (env : VEnv) (df : VDefEq) : Prop :=
  VHasType env (vdf_uvars df) [] (vdf_lhs df) (vdf_type df) /\
  VHasType env (vdf_uvars df) [] (vdf_rhs df) (vdf_type df) /\
  vclosed (vdf_lhs df) /\ vclosed (vdf_rhs df) /\ vclosed (vdf_type df).

Record VEnvClosed (env : VEnv) : Prop := {
  venv_closed_const : forall c ci,
    venv_constants env c = Some ci -> vclosed (vc_type ci);
  venv_closed_defeq : forall df,
    venv_defeqs env df ->
    vclosed (vdf_lhs df) /\ vclosed (vdf_rhs df) /\ vclosed (vdf_type df)
}.

Inductive VEnvWF : VEnv -> Prop :=
| VEnvWF_empty : VEnvWF venv_empty
| VEnvWF_add_const : forall env n ci env',
    VEnvWF env ->
    VConstantWF env ci ->
    venv_add_const env n ci = Some env' ->
    VEnvWF env'
| VEnvWF_add_defeq : forall env df,
    VEnvWF env ->
    VDefEqWF env df ->
    VEnvWF (venv_add_defeq env df).

Lemma vinstL_preserves_vclosedN ks e : forall k,
  vclosedN k e -> vclosedN k (vinstL ks e).
Proof.
  induction e as [idx | lvl | cname lvls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros k Hc; simpl in *; try tauto.
  - destruct Hc as [H1 H2]. split; auto.
  - destruct Hc as [H1 H2]. split; auto.
  - destruct Hc as [H1 H2]. split; auto.
Qed.

(* Context weakening theorem (Lean4Lean/Theory/Typing/Lemmas.lean: IsDefEq.weakN) *)
Theorem VIsDefEq_weakN env uvars G e1 e2 A :
  VEnvClosed env ->
  VIsDefEq env uvars G e1 e2 A ->
  forall n k G',
    VCtxLiftN n k G G' ->
    VIsDefEq env uvars G' (vliftN n k e1) (vliftN n k e2) (vliftN n k A).
Proof.
  intros Hclosed H. induction H; intros n0 k G' Hctx; simpl.
  - apply VDF_bvar. eapply VCtxLiftN_lookup; eassumption.
  - apply VDF_symm. apply IHVIsDefEq. exact Hctx.
  - eapply VDF_trans; [apply IHVIsDefEq1 | apply IHVIsDefEq2]; exact Hctx.
  - apply VDF_sortDF; assumption.
  - pose proof (venv_closed_const Hclosed c H) as Hcl.
    pose proof (@vinstL_preserves_vclosedN ls1 (vc_type ci) 0 Hcl) as Hcl_inst.
    rewrite (@vclosedN_vliftN_eq _ n0 k (@vclosedN_mono _ 0 k ltac:(lia) Hcl_inst)).
    eapply VDF_constDF; eassumption.
  - rewrite vliftN_vinst0.
    eapply VDF_appDF.
    + apply (IHVIsDefEq1 n0 k G' Hctx).
    + apply (IHVIsDefEq2 n0 k G' Hctx).
  - eapply VDF_lamDF.
    + apply (IHVIsDefEq1 n0 k G' Hctx).
    + apply (IHVIsDefEq2 n0 (S k) (vliftN n0 k A1 :: G')).
      constructor. exact Hctx.
  - eapply VDF_forallEDF.
    + apply (IHVIsDefEq1 n0 k G' Hctx).
    + apply (IHVIsDefEq2 n0 (S k) (vliftN n0 k A1 :: G')).
      constructor. exact Hctx.
  - eapply VDF_defeqDF.
    + apply (IHVIsDefEq1 n0 k G' Hctx).
    + apply (IHVIsDefEq2 n0 k G' Hctx).
  - rewrite !vliftN_vinst0.
    eapply VDF_beta.
    + apply (IHVIsDefEq1 n0 (S k) (vliftN n0 k A :: G')).
      constructor. exact Hctx.
    + apply (IHVIsDefEq2 n0 k G' Hctx).
  - unfold vlift at 1.
    replace (vliftN n0 (S k) (vliftN 1 0 e)) with (vlift (vliftN n0 k e)).
    2: { unfold vlift. symmetry. exact (@vliftN_comm e n0 1 k 0 ltac:(lia)). }
    replace (vliftVar n0 0 (S k)) with 0 by reflexivity.
    apply VDF_eta.
    apply (IHVIsDefEq n0 k G' Hctx).
  - eapply VDF_proofIrrel.
    + apply (IHVIsDefEq1 n0 k G' Hctx).
    + apply (IHVIsDefEq2 n0 k G' Hctx).
    + apply (IHVIsDefEq3 n0 k G' Hctx).
  - pose proof (venv_closed_defeq Hclosed df H) as [Hlhs [Hrhs Hty]].
    rewrite (@vclosedN_vliftN_eq _ n0 k (@vclosedN_mono _ 0 k ltac:(lia) (@vinstL_preserves_vclosedN ls (vdf_lhs df) 0 Hlhs))).
    rewrite (@vclosedN_vliftN_eq _ n0 k (@vclosedN_mono _ 0 k ltac:(lia) (@vinstL_preserves_vclosedN ls (vdf_rhs df) 0 Hrhs))).
    rewrite (@vclosedN_vliftN_eq _ n0 k (@vclosedN_mono _ 0 k ltac:(lia) (@vinstL_preserves_vclosedN ls (vdf_type df) 0 Hty))).
    eapply VDF_extra; eassumption.
Qed.

Corollary VHasType_weakN env uvars G e A n k G' :
  VEnvClosed env ->
  VCtxLiftN n k G G' ->
  VHasType env uvars G e A ->
  VHasType env uvars G' (vliftN n k e) (vliftN n k A).
Proof.
  intros Hc Hctx Hty. eapply VIsDefEq_weakN; eassumption.
Qed.

(* ========================================================================= *)
(* 4. Parallel Reduction, Complete Development, and Church-Rosser Confluence *)
(*    (Lean4Lean/Theory/Typing/ChurchRosser.lean & Injectivity.lean)         *)
(* ========================================================================= *)

Inductive VParRed : VExpr -> VExpr -> Prop :=
| VPR_bvar : forall i,
    VParRed (VBVar i) (VBVar i)
| VPR_sort : forall u,
    VParRed (VSort u) (VSort u)
| VPR_const : forall c ls,
    VParRed (VConst c ls) (VConst c ls)
| VPR_app : forall f f' a a',
    VParRed f f' ->
    VParRed a a' ->
    VParRed (VApp f a) (VApp f' a')
| VPR_lam : forall A A' b b',
    VParRed A A' ->
    VParRed b b' ->
    VParRed (VLam A b) (VLam A' b')
| VPR_forallE : forall A A' B B',
    VParRed A A' ->
    VParRed B B' ->
    VParRed (VForallE A B) (VForallE A' B')
| VPR_beta : forall A b b' a a',
    VParRed b b' ->
    VParRed a a' ->
    VParRed (VApp (VLam A b) a) (vinst0 b' a').

Inductive VParRedStar : VExpr -> VExpr -> Prop :=
| VPRS_refl : forall e, VParRedStar e e
| VPRS_step : forall e1 e2 e3,
    VParRed e1 e2 ->
    VParRedStar e2 e3 ->
    VParRedStar e1 e3.

Lemma VParRed_refl e : VParRed e e.
Proof.
  induction e; constructor; assumption.
Qed.

Lemma VParRedStar_trans e1 e2 e3 :
  VParRedStar e1 e2 -> VParRedStar e2 e3 -> VParRedStar e1 e3.
Proof.
  intros H1 H2. induction H1; [exact H2|].
  eapply VPRS_step; [exact H | apply IHVParRedStar; exact H2].
Qed.

Lemma VParRed_to_Star e1 e2 :
  VParRed e1 e2 -> VParRedStar e1 e2.
Proof.
  intros H. eapply VPRS_step; [exact H | apply VPRS_refl].
Qed.

Theorem VParRed_vliftN e1 e2 :
  VParRed e1 e2 ->
  forall n k, VParRed (vliftN n k e1) (vliftN n k e2).
Proof.
  intros H. induction H; intros n0 k; simpl; try (constructor; auto).
  rewrite vliftN_vinst0.
  apply VPR_beta; auto.
Qed.

Theorem VParRed_vinst e1 e2 :
  VParRed e1 e2 ->
  forall v1 v2 k,
    VParRed v1 v2 ->
    VParRed (vinst e1 v1 k) (vinst e2 v2 k).
Proof.
  intros He. induction He; intros v1 v2 k Hv; simpl.
  - unfold vinstVar.
    destruct (i <? k); [constructor|].
    destruct (Nat.eqb i k); [apply VParRed_vliftN; exact Hv | constructor].
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - rewrite (vinst0_vinst_hi b' a' v2 k).
    apply VPR_beta; auto.
Qed.

Corollary VParRed_vinst0 b1 b2 a1 a2 :
  VParRed b1 b2 ->
  VParRed a1 a2 ->
  VParRed (vinst0 b1 a1) (vinst0 b2 a2).
Proof.
  intros Hb Ha. apply VParRed_vinst; assumption.
Qed.

(* Takahashi's Complete Development Function *)
Fixpoint vcomplete_dev (e : VExpr) : VExpr :=
  match e with
  | VBVar i => VBVar i
  | VSort u => VSort u
  | VConst c ls => VConst c ls
  | VApp f a =>
      match f with
      | VLam _ b => vinst0 (vcomplete_dev b) (vcomplete_dev a)
      | _ => VApp (vcomplete_dev f) (vcomplete_dev a)
      end
  | VLam A b => VLam (vcomplete_dev A) (vcomplete_dev b)
  | VForallE A B => VForallE (vcomplete_dev A) (vcomplete_dev B)
  end.

Lemma VParRed_self_dev e : VParRed e (vcomplete_dev e).
Proof.
  induction e; simpl; try (constructor; assumption).
  destruct e1; try (constructor; assumption).
  inversion IHe1; subst.
  apply VPR_beta; assumption.
Qed.

(* Takahashi Triangle Property: if e1 => e2, then e2 => vcomplete_dev e1 *)
Theorem VParRed_triangle e1 e2 :
  VParRed e1 e2 -> VParRed e2 (vcomplete_dev e1).
Proof.
  intros H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor.
  - destruct f.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + inversion H; subst.
      inversion IHVParRed1; subst.
      apply VPR_beta; assumption.
    + constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - apply VParRed_vinst0; assumption.
Qed.

(* Diamond Property of Parallel Reduction *)
Theorem VParRed_diamond e e1 e2 :
  VParRed e e1 ->
  VParRed e e2 ->
  exists e3, VParRed e1 e3 /\ VParRed e2 e3.
Proof.
  intros H1 H2.
  exists (vcomplete_dev e).
  split; apply VParRed_triangle; assumption.
Qed.

(* Strip Lemma *)
Lemma VParRed_strip e e1 e2 :
  VParRed e e1 ->
  VParRedStar e e2 ->
  exists e3, VParRedStar e1 e3 /\ VParRed e2 e3.
Proof.
  intros Hstep Hstar. revert e1 Hstep.
  induction Hstar as [e | e a e2 H1 Hstar IH]; intros e1 Hstep.
  - exists e1. split; [apply VPRS_refl | exact Hstep].
  - destruct (VParRed_diamond H1 Hstep) as [b [Hab He1b]].
    destruct (IH b Hab) as [e3 [Hb3 He23]].
    exists e3. split.
    + eapply VPRS_step; [exact He1b | exact Hb3].
    + exact He23.
Qed.

(* Full Church-Rosser Confluence Theorem *)
Theorem VParRedStar_ChurchRosser e e1 e2 :
  VParRedStar e e1 ->
  VParRedStar e e2 ->
  exists e3, VParRedStar e1 e3 /\ VParRedStar e2 e3.
Proof.
  intros H1. revert e2.
  induction H1 as [e | e a e1 Hstep Hstar IH]; intros e2 H2.
  - exists e2. split; [exact H2 | apply VPRS_refl].
  - destruct (VParRed_strip Hstep H2) as [b [Hab He2b]].
    destruct (IH b Hab) as [e3 [He13 Hb3]].
    exists e3. split.
    + exact He13.
    + eapply VPRS_step; [exact He2b | exact Hb3].
Qed.

(* Head preservation under parallel reduction *)
Lemma VParRed_sort_inv u e :
  VParRed (VSort u) e -> e = VSort u.
Proof. intros H. inversion H; reflexivity. Qed.

Lemma VParRedStar_sort_inv u e :
  VParRedStar (VSort u) e -> e = VSort u.
Proof.
  remember (VSort u) as s eqn:Hs.
  intros H. revert u Hs.
  induction H; intros u Hs; subst; [reflexivity|].
  apply VParRed_sort_inv in H. subst.
  eapply IHVParRedStar. reflexivity.
Qed.

Lemma VParRed_forallE_inv A B e :
  VParRed (VForallE A B) e ->
  exists A' B', e = VForallE A' B' /\ VParRed A A' /\ VParRed B B'.
Proof.
  intros H. inversion H; subst.
  exists A', B'. repeat split; assumption.
Qed.

Lemma VParRedStar_forallE_inv A B e :
  VParRedStar (VForallE A B) e ->
  exists A' B', e = VForallE A' B' /\ VParRedStar A A' /\ VParRedStar B B'.
Proof.
  remember (VForallE A B) as p eqn:Hp.
  intros H. revert A B Hp.
  induction H; intros A0 B0 Hp; subst.
  - exists A0, B0. repeat split; apply VPRS_refl.
  - apply VParRed_forallE_inv in H as [A1 [B1 [Heq [HA1 HB1]]]].
    subst e2.
    destruct (IHVParRedStar A1 B1 eq_refl) as [A2 [B2 [Heq2 [HA2 HB2]]]].
    exists A2, B2. repeat split; [exact Heq2 | | ];
      eapply VPRS_step; eassumption.
Qed.

(* Pi-Injectivity up to Confluence (Lean4Lean/Theory/Typing/Injectivity.lean) *)
Theorem VParRedStar_forallE_injective A1 B1 A2 B2 :
  (exists C, VParRedStar (VForallE A1 B1) C /\ VParRedStar (VForallE A2 B2) C) ->
  (exists A0, VParRedStar A1 A0 /\ VParRedStar A2 A0) /\
  (exists B0, VParRedStar B1 B0 /\ VParRedStar B2 B0).
Proof.
  intros [C [H1 H2]].
  apply VParRedStar_forallE_inv in H1 as [A1' [B1' [Heq1 [HA1 HB1]]]].
  apply VParRedStar_forallE_inv in H2 as [A2' [B2' [Heq2 [HA2 HB2]]]].
  subst C. inversion Heq2; subst.
  split.
  - exists A2'. split; assumption.
  - exists B2'. split; assumption.
Qed.

(* Sort-vs-Pi Disjointness (Lean4Lean/Theory/Typing/Injectivity.lean) *)
Theorem VParRedStar_sort_forallE_disjoint u A B C :
  VParRedStar (VSort u) C ->
  VParRedStar (VForallE A B) C ->
  False.
Proof.
  intros Hs Hp.
  apply VParRedStar_sort_inv in Hs.
  apply VParRedStar_forallE_inv in Hp as [A' [B' [Heq _]]].
  congruence.
Qed.

(* ========================================================================= *)
(* 5. Algorithmic / Bidirectional Typing Uniqueness (UniqueTyping.lean)      *)
(* ========================================================================= *)

Inductive VSynHasType (env : VEnv) (uvars : nat) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VSyn_bvar : forall G i ty,
    VLookup G i ty ->
    VSynHasType env uvars G (VBVar i) ty
| VSyn_sort : forall G u,
    vlevel_wf uvars u ->
    VSynHasType env uvars G (VSort u) (VSort (VLSucc u))
| VSyn_const : forall G c ci ls,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf uvars) ls ->
    List.length ls = vc_uvars ci ->
    VSynHasType env uvars G (VConst c ls) (vinstL ls (vc_type ci))
| VSyn_app : forall G f a A B,
    VSynHasType env uvars G f (VForallE A B) ->
    VSynHasType env uvars G a A ->
    VSynHasType env uvars G (VApp f a) (vinst0 B a)
| VSyn_lam : forall G A b u B,
    VSynHasType env uvars G A (VSort u) ->
    VSynHasType env uvars (A :: G) b B ->
    VSynHasType env uvars G (VLam A b) (VForallE A B)
| VSyn_forallE : forall G A B u v,
    VSynHasType env uvars G A (VSort u) ->
    VSynHasType env uvars (A :: G) B (VSort v) ->
    VSynHasType env uvars G (VForallE A B) (VSort (VLIMax u v)).

Theorem VSynHasType_sound env uvars G e A :
  VSynHasType env uvars G e A -> VHasType env uvars G e A.
Proof.
  intros H. induction H.
  - apply VHasType_bvar; assumption.
  - apply VHasType_sort; assumption.
  - eapply VHasType_const; eassumption.
  - eapply VHasType_app; eassumption.
  - eapply VHasType_lam; eassumption.
  - eapply VHasType_forallE; eassumption.
Qed.

Theorem VSynHasType_unique env uvars G e A B :
  VSynHasType env uvars G e A ->
  VSynHasType env uvars G e B ->
  A = B.
Proof.
  intros H1. revert B.
  induction H1; intros B0 H2; inversion H2; subst.
  - eapply VLookup_deterministic; eassumption.
  - reflexivity.
  - match goal with
    | Hc1 : venv_constants env c = Some ci,
      Hc2 : venv_constants env c = Some ?ci0 |- _ =>
        rewrite Hc1 in Hc2; inversion Hc2; subst; reflexivity
    end.
  - match goal with
    | Hf : VSynHasType env uvars G f (VForallE ?A0 ?B1) |- _ =>
        specialize (IHVSynHasType1 _ Hf); inversion IHVSynHasType1; subst; reflexivity
    end.
  - f_equal. apply IHVSynHasType2. assumption.
  - match goal with
    | HA : VSynHasType env uvars G A (VSort ?u0),
      HB : VSynHasType env uvars (A :: G) B (VSort ?v0) |- _ =>
        specialize (IHVSynHasType1 _ HA); inversion IHVSynHasType1; subst;
        specialize (IHVSynHasType2 _ HB); inversion IHVSynHasType2; subst;
        reflexivity
    end.
Qed.

Print Assumptions VIsDefEq_weakN.
Print Assumptions VEnvOrdered_preserve_VIsDefEq.
Print Assumptions VParRed_triangle.
Print Assumptions VParRed_diamond.
Print Assumptions VParRedStar_ChurchRosser.
Print Assumptions VParRedStar_forallE_injective.
Print Assumptions VParRedStar_sort_forallE_disjoint.
Print Assumptions VSynHasType_sound.
Print Assumptions VSynHasType_unique.
