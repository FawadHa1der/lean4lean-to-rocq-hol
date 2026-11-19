(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/Typing/Strong.lean:
   Strong typing and definitional equality (VIsDefEqStrong / VHasTypeStrong),
   equivalence up to universe levels (VEqUpToLevels), syntactic typing
   inversions modulo VIsDefEq (app_inv, lam_inv, const_inv, bvar_inv),
   stratified typing (VHasTypeStratified), and simultaneous definitional-equality
   substitution (VIsDefEqStrong_substEq' / VIsDefEq_substDF). *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel
  DeclarativeTyping TypingLemmas SubstTheory.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Strong Definitional Equality & Strong Typing (Strong.lean)             *)
(* ========================================================================= *)

Inductive VIsDefEqStrong (env : VEnv) (uvars : nat) :
    list VExpr -> VExpr -> VExpr -> VExpr -> Prop :=
| VDFS_bvar : forall G i A u,
    VLookup G i A ->
    vlevel_wf uvars u ->
    VIsDefEqStrong env uvars G A A (VSort u) ->
    VIsDefEqStrong env uvars G (VBVar i) (VBVar i) A
| VDFS_symm : forall G e e' A,
    VIsDefEqStrong env uvars G e e' A ->
    VIsDefEqStrong env uvars G e' e A
| VDFS_trans : forall G e1 e2 e3 A,
    VIsDefEqStrong env uvars G e1 e2 A ->
    VIsDefEqStrong env uvars G e2 e3 A ->
    VIsDefEqStrong env uvars G e1 e3 A
| VDFS_sortDF : forall G l l',
    vlevel_wf uvars l ->
    vlevel_wf uvars l' ->
    vlevel_equiv l l' ->
    VIsDefEqStrong env uvars G (VSort l) (VSort l') (VSort (VLSucc l))
| VDFS_constDF : forall G c ci ls ls' u,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf uvars) ls ->
    Forall (vlevel_wf uvars) ls' ->
    List.length ls = vc_uvars ci ->
    Forall2 vlevel_equiv ls ls' ->
    vlevel_wf uvars u ->
    VIsDefEqStrong env uvars [] (vinstL ls (vc_type ci)) (vinstL ls' (vc_type ci)) (VSort u) ->
    VIsDefEqStrong env uvars G (vinstL ls (vc_type ci)) (vinstL ls' (vc_type ci)) (VSort u) ->
    VIsDefEqStrong env uvars G (VConst c ls) (VConst c ls') (vinstL ls (vc_type ci))
| VDFS_appDF : forall G A B f f' a a' u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VIsDefEqStrong env uvars G A A (VSort u) ->
    VIsDefEqStrong env uvars (A :: G) B B (VSort v) ->
    VIsDefEqStrong env uvars G f f' (VForallE A B) ->
    VIsDefEqStrong env uvars G a a' A ->
    VIsDefEqStrong env uvars G (vinst0 B a) (vinst0 B a') (VSort v) ->
    VIsDefEqStrong env uvars G (VApp f a) (VApp f' a') (vinst0 B a)
| VDFS_lamDF : forall G A A' B body body' u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VIsDefEqStrong env uvars G A A' (VSort u) ->
    VIsDefEqStrong env uvars (A :: G) B B (VSort v) ->
    VIsDefEqStrong env uvars (A' :: G) B B (VSort v) ->
    VIsDefEqStrong env uvars (A :: G) body body' B ->
    VIsDefEqStrong env uvars (A' :: G) body body' B ->
    VIsDefEqStrong env uvars G (VLam A body) (VLam A' body') (VForallE A B)
| VDFS_forallEDF : forall G A A' body body' u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VIsDefEqStrong env uvars G A A' (VSort u) ->
    VIsDefEqStrong env uvars (A :: G) body body' (VSort v) ->
    VIsDefEqStrong env uvars (A' :: G) body body' (VSort v) ->
    VIsDefEqStrong env uvars G (VForallE A body) (VForallE A' body') (VSort (VLIMax u v))
| VDFS_defeqDF : forall G e1 e2 A B u,
    vlevel_wf uvars u ->
    VIsDefEqStrong env uvars G A B (VSort u) ->
    VIsDefEqStrong env uvars G e1 e2 A ->
    VIsDefEqStrong env uvars G e1 e2 B
| VDFS_beta : forall G A B e e' u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VIsDefEqStrong env uvars G A A (VSort u) ->
    VIsDefEqStrong env uvars (A :: G) B B (VSort v) ->
    VIsDefEqStrong env uvars (A :: G) e e B ->
    VIsDefEqStrong env uvars G e' e' A ->
    VIsDefEqStrong env uvars G (vinst0 B e') (vinst0 B e') (VSort v) ->
    VIsDefEqStrong env uvars G (vinst0 e e') (vinst0 e e') (vinst0 B e') ->
    VIsDefEqStrong env uvars G (VApp (VLam A e) e') (vinst0 e e') (vinst0 B e')
| VDFS_eta : forall G A B e u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VIsDefEqStrong env uvars G A A (VSort u) ->
    VIsDefEqStrong env uvars (A :: G) B B (VSort v) ->
    VIsDefEqStrong env uvars (vlift A :: A :: G) (vliftN 1 1 B) (vliftN 1 1 B) (VSort v) ->
    VIsDefEqStrong env uvars G e e (VForallE A B) ->
    VIsDefEqStrong env uvars (A :: G) (vlift e) (vlift e) (VForallE (vlift A) (vliftN 1 1 B)) ->
    VIsDefEqStrong env uvars (A :: G) (vlift A) (vlift A) (VSort u) ->
    VIsDefEqStrong env uvars G (VLam A (VApp (vlift e) (VBVar 0))) e (VForallE A B)
| VDFS_proofIrrel : forall G p h h',
    VIsDefEqStrong env uvars G p p (VSort VLZero) ->
    VIsDefEqStrong env uvars G h h p ->
    VIsDefEqStrong env uvars G h' h' p ->
    VIsDefEqStrong env uvars G h h' p
| VDFS_extra : forall G df ls u,
    venv_defeqs env df ->
    Forall (vlevel_wf uvars) ls ->
    List.length ls = vdf_uvars df ->
    vlevel_wf uvars u ->
    VIsDefEqStrong env uvars [] (vinstL ls (vdf_type df)) (vinstL ls (vdf_type df)) (VSort u) ->
    VIsDefEqStrong env uvars [] (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_type df)) ->
    VIsDefEqStrong env uvars [] (vinstL ls (vdf_rhs df)) (vinstL ls (vdf_rhs df)) (vinstL ls (vdf_type df)) ->
    VIsDefEqStrong env uvars G (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_type df)) ->
    VIsDefEqStrong env uvars G (vinstL ls (vdf_rhs df)) (vinstL ls (vdf_rhs df)) (vinstL ls (vdf_type df)) ->
    VIsDefEqStrong env uvars G (vinstL ls (vdf_lhs df)) (vinstL ls (vdf_rhs df)) (vinstL ls (vdf_type df)).

Arguments VDFS_sortDF {env uvars} G {l l'} _ _ _.

Inductive VHasTypeStrong (env : VEnv) (uvars : nat) :
    list VExpr -> VExpr -> VExpr -> bool -> Prop :=
| VHTS_bvar : forall G i A u,
    VLookup G i A ->
    vlevel_wf uvars u ->
    VHasTypeStrong env uvars G A (VSort u) true ->
    VHasTypeStrong env uvars G (VBVar i) A false
| VHTS_sort' : forall G l l',
    vlevel_wf uvars l ->
    vlevel_wf uvars l' ->
    vlevel_equiv l l' ->
    VHasTypeStrong env uvars G (VSort l) (VSort (VLSucc l')) false
| VHTS_const : forall G c ci ls u,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf uvars) ls ->
    List.length ls = vc_uvars ci ->
    vlevel_wf uvars u ->
    VHasTypeStrong env uvars [] (vinstL ls (vc_type ci)) (VSort u) true ->
    VHasTypeStrong env uvars G (vinstL ls (vc_type ci)) (VSort u) true ->
    VHasTypeStrong env uvars G (VConst c ls) (vinstL ls (vc_type ci)) false
| VHTS_app : forall G A B f a u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VHasTypeStrong env uvars G A (VSort u) true ->
    VHasTypeStrong env uvars (A :: G) B (VSort v) true ->
    VHasTypeStrong env uvars G (VForallE A B) (VSort (VLIMax u v)) true ->
    VHasTypeStrong env uvars G f (VForallE A B) true ->
    VHasTypeStrong env uvars G a A true ->
    VHasTypeStrong env uvars G (vinst0 B a) (VSort v) true ->
    VHasTypeStrong env uvars G (VApp f a) (vinst0 B a) false
| VHTS_lam : forall G A B body u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VHasTypeStrong env uvars G A (VSort u) true ->
    VHasTypeStrong env uvars (A :: G) B (VSort v) true ->
    VHasTypeStrong env uvars (A :: G) body B true ->
    VHasTypeStrong env uvars G (VForallE A B) (VSort (VLIMax u v)) true ->
    VHasTypeStrong env uvars G (VLam A body) (VForallE A B) false
| VHTS_forallE : forall G A body u v,
    vlevel_wf uvars u ->
    vlevel_wf uvars v ->
    VHasTypeStrong env uvars G A (VSort u) true ->
    VHasTypeStrong env uvars (A :: G) body (VSort v) true ->
    VHasTypeStrong env uvars G (VForallE A body) (VSort (VLIMax u v)) false
| VHTS_base : forall G e A,
    VHasTypeStrong env uvars G e A false ->
    VHasTypeStrong env uvars G e A true
| VHTS_defeq : forall G e A B u,
    vlevel_wf uvars u ->
    VIsDefEqStrong env uvars G A B (VSort u) ->
    VHasTypeStrong env uvars G A (VSort u) true ->
    VHasTypeStrong env uvars G B (VSort u) true ->
    VHasTypeStrong env uvars G e A true ->
    VHasTypeStrong env uvars G e B true.

(* ========================================================================= *)
(* 2. Basic Structural Properties of VIsDefEqStrong                          *)
(* ========================================================================= *)

Theorem VIsDefEqStrong_hasType env U G e1 e2 A :
  VIsDefEqStrong env U G e1 e2 A ->
  VIsDefEqStrong env U G e1 e1 A /\ VIsDefEqStrong env U G e2 e2 A.
Proof.
  intros H. split.
  - eapply VDFS_trans; [exact H | apply VDFS_symm; exact H].
  - eapply VDFS_trans; [apply VDFS_symm; exact H | exact H].
Qed.

Lemma VIsDefEqStrong_refl_l env U G e1 e2 A :
  VIsDefEqStrong env U G e1 e2 A -> VIsDefEqStrong env U G e1 e1 A.
Proof. intros H. exact (proj1 (VIsDefEqStrong_hasType H)). Qed.

Lemma VIsDefEqStrong_refl_r env U G e1 e2 A :
  VIsDefEqStrong env U G e1 e2 A -> VIsDefEqStrong env U G e2 e2 A.
Proof. intros H. exact (proj2 (VIsDefEqStrong_hasType H)). Qed.

Lemma vlift_vliftN_succ e n k :
  vlift (vliftN n k e) = vliftN n (S k) (vlift e).
Proof.
  unfold vlift.
  pose proof (@vliftN_comm e n 1 k 0 ltac:(lia)) as H.
  symmetry. exact H.
Qed.

Lemma vliftN1_vliftN_succ e n k :
  vliftN 1 1 (vliftN n (S k) e) = vliftN n (S (S k)) (vliftN 1 1 e).
Proof.
  pose proof (@vliftN_comm e n 1 (S k) 1 ltac:(lia)) as H.
  symmetry. exact H.
Qed.

Theorem VIsDefEqStrong_weakN env U G e1 e2 A :
  VEnvClosed env ->
  VIsDefEqStrong env U G e1 e2 A ->
  forall n k G',
    VCtxLiftN n k G G' ->
    VIsDefEqStrong env U G' (vliftN n k e1) (vliftN n k e2) (vliftN n k A).
Proof.
  intros Hcl H. induction H; intros n0 k G' W; simpl.
  - eapply VDFS_bvar; [eapply VCtxLiftN_lookup; eassumption | exact H0 | apply IHVIsDefEqStrong; exact W].
  - apply VDFS_symm. apply IHVIsDefEqStrong. exact W.
  - eapply VDFS_trans; [apply IHVIsDefEqStrong1 | apply IHVIsDefEqStrong2]; exact W.
  - apply VDFS_sortDF; assumption.
  - rewrite (@vclosedN_vliftN_eq _ n0 k (closed_inst_const ls k Hcl H)).
    pose proof (IHVIsDefEqStrong2 n0 k G' W) as IH2. simpl in IH2.
    rewrite (@vclosedN_vliftN_eq _ n0 k (closed_inst_const ls k Hcl H)),
            (@vclosedN_vliftN_eq _ n0 k (closed_inst_const ls' k Hcl H)) in IH2.
    eapply VDFS_constDF; eassumption.
  - rewrite vliftN_vinst0.
    pose proof (IHVIsDefEqStrong5 n0 k G' W) as IH5. simpl in IH5.
    rewrite !vliftN_vinst0 in IH5.
    eapply VDFS_appDF;
      [exact H | exact H0 | apply IHVIsDefEqStrong1; exact W
      | apply IHVIsDefEqStrong2; constructor; exact W
      | apply IHVIsDefEqStrong3; exact W | apply IHVIsDefEqStrong4; exact W | exact IH5].
  - eapply VDFS_lamDF;
      [exact H | exact H0 | apply IHVIsDefEqStrong1; exact W
      | apply IHVIsDefEqStrong2; constructor; exact W
      | apply IHVIsDefEqStrong3; constructor; exact W
      | apply IHVIsDefEqStrong4; constructor; exact W
      | apply IHVIsDefEqStrong5; constructor; exact W].
  - eapply VDFS_forallEDF;
      [exact H | exact H0 | apply IHVIsDefEqStrong1; exact W
      | apply IHVIsDefEqStrong2; constructor; exact W
      | apply IHVIsDefEqStrong3; constructor; exact W].
  - eapply VDFS_defeqDF; [exact H | apply IHVIsDefEqStrong1; exact W | apply IHVIsDefEqStrong2; exact W].
  - rewrite !vliftN_vinst0.
    pose proof (IHVIsDefEqStrong5 n0 k G' W) as IH5. simpl in IH5.
    rewrite !vliftN_vinst0 in IH5.
    pose proof (IHVIsDefEqStrong6 n0 k G' W) as IH6. simpl in IH6.
    rewrite !vliftN_vinst0 in IH6.
    eapply VDFS_beta;
      [exact H | exact H0 | apply IHVIsDefEqStrong1; exact W
      | apply IHVIsDefEqStrong2; constructor; exact W
      | apply IHVIsDefEqStrong3; constructor; exact W
      | apply IHVIsDefEqStrong4; exact W | exact IH5 | exact IH6].
  - rewrite <- vlift_vliftN_succ.
    pose proof (IHVIsDefEqStrong3 n0 (S (S k)) _ (VCtxLiftN_succ (vlift A) (VCtxLiftN_succ A W))) as IH3.
    simpl in IH3. rewrite <- vlift_vliftN_succ, <- vliftN1_vliftN_succ in IH3.
    pose proof (IHVIsDefEqStrong5 n0 (S k) _ (VCtxLiftN_succ A W)) as IH5.
    simpl in IH5. rewrite <- !vlift_vliftN_succ, <- vliftN1_vliftN_succ in IH5.
    pose proof (IHVIsDefEqStrong6 n0 (S k) _ (VCtxLiftN_succ A W)) as IH6.
    simpl in IH6. rewrite <- vlift_vliftN_succ in IH6.
    eapply VDFS_eta;
      [exact H | exact H0 | apply IHVIsDefEqStrong1; exact W
      | apply IHVIsDefEqStrong2; constructor; exact W
      | exact IH3 | apply IHVIsDefEqStrong4; exact W | exact IH5 | exact IH6].
  - eapply VDFS_proofIrrel;
      [apply IHVIsDefEqStrong1 | apply IHVIsDefEqStrong2 | apply IHVIsDefEqStrong3]; exact W.
  - destruct (closed_inst_defeq ls k Hcl H) as [Hl [Hr Ht]].
    rewrite (@vclosedN_vliftN_eq _ n0 k Hl),
            (@vclosedN_vliftN_eq _ n0 k Hr),
            (@vclosedN_vliftN_eq _ n0 k Ht).
    pose proof (IHVIsDefEqStrong4 n0 k G' W) as IH4.
    pose proof (IHVIsDefEqStrong5 n0 k G' W) as IH5.
    rewrite (@vclosedN_vliftN_eq _ n0 k Hl), (@vclosedN_vliftN_eq _ n0 k Ht) in IH4.
    rewrite (@vclosedN_vliftN_eq _ n0 k Hr), (@vclosedN_vliftN_eq _ n0 k Ht) in IH5.
    eapply VDFS_extra; eassumption.
Qed.

Theorem VIsDefEqStrong_defeq env U G e1 e2 A :
  VIsDefEqStrong env U G e1 e2 A -> VIsDefEq env U G e1 e2 A.
Proof.
  induction 1.
  - apply VDF_bvar; assumption.
  - apply VDF_symm; assumption.
  - eapply VDF_trans; eassumption.
  - apply VDF_sortDF; assumption.
  - eapply VDF_constDF; eassumption.
  - eapply VDF_appDF; eassumption.
  - eapply VDF_lamDF; eassumption.
  - eapply VDF_forallEDF; eassumption.
  - eapply VDF_defeqDF; eassumption.
  - eapply VDF_beta; eassumption.
  - apply VDF_eta; assumption.
  - eapply VDF_proofIrrel; eassumption.
  - eapply VDF_extra; eassumption.
Qed.

Theorem VIsDefEqStrong_mono env1 env2 U G e1 e2 A :
  venv_ordered env1 env2 ->
  VIsDefEqStrong env1 U G e1 e2 A ->
  VIsDefEqStrong env2 U G e1 e2 A.
Proof.
  intros Hord H. induction H.
  - eapply VDFS_bvar; [exact H | exact H0 | exact IHVIsDefEqStrong].
  - apply VDFS_symm; exact IHVIsDefEqStrong.
  - eapply VDFS_trans; [exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2].
  - apply VDFS_sortDF; assumption.
  - eapply VDFS_constDF;
      [apply (venv_ord_const Hord); exact H | exact H0 | exact H1 | exact H2 | exact H3
      | exact H4 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2].
  - eapply VDFS_appDF;
      [exact H | exact H0 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2
      | exact IHVIsDefEqStrong3 | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5].
  - eapply VDFS_lamDF;
      [exact H | exact H0 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2
      | exact IHVIsDefEqStrong3 | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5].
  - eapply VDFS_forallEDF;
      [exact H | exact H0 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2 | exact IHVIsDefEqStrong3].
  - eapply VDFS_defeqDF; [exact H | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2].
  - eapply VDFS_beta;
      [exact H | exact H0 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2
      | exact IHVIsDefEqStrong3 | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5 | exact IHVIsDefEqStrong6].
  - eapply VDFS_eta;
      [exact H | exact H0 | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2
      | exact IHVIsDefEqStrong3 | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5 | exact IHVIsDefEqStrong6].
  - eapply VDFS_proofIrrel; [exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2 | exact IHVIsDefEqStrong3].
  - eapply VDFS_extra;
      [apply (venv_ord_defeq Hord); exact H | exact H0 | exact H1 | exact H2
      | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2 | exact IHVIsDefEqStrong3
      | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5].
Qed.

Theorem VIsDefEqStrong_weak0 env U G e1 e2 A :
  VEnvClosed env ->
  VIsDefEqStrong env U [] e1 e2 A ->
  VIsDefEqStrong env U G e1 e2 A.
Proof.
  intros Hcl H.
  destruct (VIsDefEq_closedN Hcl (VIsDefEqStrong_defeq H) I) as [H1 [H2 H3]].
  simpl in H1, H2, H3.
  assert (Hz : VCtxLiftN (List.length G) 0 [] (G ++ [])) by (constructor; reflexivity).
  rewrite app_nil_r in Hz.
  pose proof (VIsDefEqStrong_weakN Hcl H Hz) as Hw.
  rewrite !(@vclosedN_vliftN_eq _ (List.length G) 0) in Hw by assumption.
  exact Hw.
Qed.

Arguments VIsDefEqStrong_weak0 {env U G e1 e2 A} _ _.

(* ========================================================================= *)
(* 3. Equivalence Up To Universe Levels (VEqUpToLevels)                      *)
(* ========================================================================= *)

Inductive VEqUpToLevels (U : nat) : VExpr -> VExpr -> Prop :=
| VEUL_bvar : forall i,
    VEqUpToLevels U (VBVar i) (VBVar i)
| VEUL_const : forall c ls ls',
    Forall (vlevel_wf U) ls ->
    Forall (vlevel_wf U) ls' ->
    Forall2 vlevel_equiv ls ls' ->
    VEqUpToLevels U (VConst c ls) (VConst c ls')
| VEUL_sort : forall l l',
    vlevel_wf U l ->
    vlevel_wf U l' ->
    vlevel_equiv l l' ->
    VEqUpToLevels U (VSort l) (VSort l')
| VEUL_app : forall f f' a a',
    VEqUpToLevels U f f' ->
    VEqUpToLevels U a a' ->
    VEqUpToLevels U (VApp f a) (VApp f' a')
| VEUL_lam : forall A A' e e',
    VEqUpToLevels U A A' ->
    VEqUpToLevels U e e' ->
    VEqUpToLevels U (VLam A e) (VLam A' e')
| VEUL_forallE : forall A A' B B',
    VEqUpToLevels U A A' ->
    VEqUpToLevels U B B' ->
    VEqUpToLevels U (VForallE A B) (VForallE A' B').

Lemma Forall2_vlevel_equiv_symm ls1 ls2 :
  Forall2 vlevel_equiv ls1 ls2 -> Forall2 vlevel_equiv ls2 ls1.
Proof.
  induction 1; constructor; [apply vlevel_equiv_symm; assumption | assumption].
Qed.

Lemma Forall2_vlevel_equiv_trans ls1 ls2 ls3 :
  Forall2 vlevel_equiv ls1 ls2 ->
  Forall2 vlevel_equiv ls2 ls3 ->
  Forall2 vlevel_equiv ls1 ls3.
Proof.
  intros H1. revert ls3.
  induction H1; intros ls3 H2; inversion H2; subst; constructor.
  - eapply vlevel_equiv_trans; eassumption.
  - apply IHForall2; assumption.
Qed.

Lemma Forall2_length_eq {A B} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> List.length xs = List.length ys.
Proof.
  induction 1; simpl; congruence.
Qed.

Lemma Forall2_map_vlevel_inst_congr ls ls' us :
  Forall2 vlevel_equiv ls ls' ->
  Forall2 vlevel_equiv (map (vlevel_inst ls) us) (map (vlevel_inst ls') us).
Proof.
  intros Heq.
  induction us as [|u us IH]; simpl; constructor; [|exact IH].
  apply vlevel_inst_congr; [exact Heq | apply vlevel_equiv_refl].
Qed.

Theorem VEqUpToLevels_instL env U U' ls ls' G e1 e2 A :
  Forall (vlevel_wf U) ls ->
  Forall (vlevel_wf U) ls' ->
  Forall2 vlevel_equiv ls ls' ->
  VIsDefEqStrong env U' G e1 e2 A ->
  VEqUpToLevels U (vinstL ls e1) (vinstL ls' e1) /\
  VEqUpToLevels U (vinstL ls e2) (vinstL ls' e2).
Proof.
  intros Hls Hls' Heq H.
  induction H; simpl.
  - split; constructor.
  - tauto.
  - tauto.
  - split; apply VEUL_sort;
      try (apply vlevel_inst_wf_any; assumption);
      (apply vlevel_inst_congr; [exact Heq | apply vlevel_equiv_refl]).
  - split; apply VEUL_const;
      try (apply Forall_vlevel_inst_wf; assumption);
      apply Forall2_map_vlevel_inst_congr; exact Heq.
  - destruct IHVIsDefEqStrong3, IHVIsDefEqStrong4.
    split; constructor; assumption.
  - destruct IHVIsDefEqStrong1, IHVIsDefEqStrong4.
    split; constructor; assumption.
  - destruct IHVIsDefEqStrong1, IHVIsDefEqStrong2.
    split; constructor; assumption.
  - exact IHVIsDefEqStrong2.
  - destruct IHVIsDefEqStrong1, IHVIsDefEqStrong3, IHVIsDefEqStrong4, IHVIsDefEqStrong6.
    split; [repeat constructor; assumption | assumption].
  - destruct IHVIsDefEqStrong1, IHVIsDefEqStrong4, IHVIsDefEqStrong5.
    split; [repeat constructor; assumption | assumption].
  - tauto.
  - tauto.
Qed.

Theorem VEqUpToLevels_refl env U G e1 e2 A :
  VCtxLevelWF U G ->
  VIsDefEqStrong env U G e1 e2 A ->
  VEqUpToLevels U e1 e1 /\ VEqUpToLevels U e2 e2.
Proof.
  intros Hctx H.
  destruct (VIsDefEq_levelWF (VIsDefEqStrong_defeq H) Hctx) as [He1 [He2 _]].
  pose proof (VEqUpToLevels_instL (vlevel_params_wf U) (vlevel_params_wf U)
                (Forall2_vlevel_equiv_refl _) H) as [H1 H2].
  rewrite (vinstL_params He1) in H1.
  rewrite (vinstL_params He2) in H2.
  split; assumption.
Qed.

Theorem VEqUpToLevels_weakN U e e' n k :
  VEqUpToLevels U e e' ->
  VEqUpToLevels U (vliftN n k e) (vliftN n k e').
Proof.
  intros H. revert k.
  induction H; intros k; simpl; constructor; auto.
Qed.

Theorem VEqUpToLevels_instN U e e' e0 e0' k :
  VEqUpToLevels U e0 e0' ->
  VEqUpToLevels U e e' ->
  VEqUpToLevels U (vinst e e0 k) (vinst e' e0' k).
Proof.
  intros H0 H. revert k.
  induction H; intros k; simpl; try (constructor; auto).
  unfold vinstVar.
  destruct (i <? k); [constructor |].
  destruct (Nat.eqb i k); [apply VEqUpToLevels_weakN; exact H0 | constructor].
Qed.

(* ========================================================================= *)
(* 4. Strong Universe Instantiation, Contexts, and Substitution              *)
(* ========================================================================= *)

Definition VEnvStrongPred (env : VEnv) (U : nat) (e A : VExpr) : Prop :=
  VIsDefEqStrong env U [] e e A /\
  (exists u, VIsDefEqStrong env U [] A A (VSort u)) /\
  (forall U' ls ls',
      Forall (vlevel_wf U') ls ->
      Forall (vlevel_wf U') ls' ->
      Forall2 vlevel_equiv ls ls' ->
      VIsDefEqStrong env U' [] (vinstL ls e) (vinstL ls' e) (vinstL ls A)) /\
  (forall A0 B0, e = VForallE A0 B0 ->
      (exists u, VIsDefEqStrong env U [] A0 A0 (VSort u)) /\
      (exists u, VIsDefEqStrong env U [A0] B0 B0 (VSort u))).

Definition VEnvStrong (env : VEnv) : Prop :=
  (forall n ci, venv_constants env n = Some ci ->
     exists u, VEnvStrongPred env (vc_uvars ci) (vc_type ci) (VSort u)) /\
  (forall df, venv_defeqs env df ->
     VEnvStrongPred env (vdf_uvars df) (vdf_lhs df) (vdf_type df) /\
     VEnvStrongPred env (vdf_uvars df) (vdf_rhs df) (vdf_type df)).

Theorem VIsDefEqStrong_instL env U U' ls G e1 e2 A :
  Forall (vlevel_wf U') ls ->
  VIsDefEqStrong env U G e1 e2 A ->
  VIsDefEqStrong env U' (map (vinstL ls) G) (vinstL ls e1) (vinstL ls e2) (vinstL ls A).
Proof.
  intros Hls H. induction H; simpl.
  - eapply VDFS_bvar; [apply VLookup_instL; eassumption | apply vlevel_inst_wf_any; exact Hls | exact IHVIsDefEqStrong].
  - apply VDFS_symm; exact IHVIsDefEqStrong.
  - eapply VDFS_trans; eassumption.
  - apply VDFS_sortDF; try (apply vlevel_inst_wf_any; exact Hls).
    apply vlevel_inst_equiv; assumption.
  - rewrite !vinstL_vinstL in *.
    eapply VDFS_constDF.
    + eassumption.
    + apply Forall_vlevel_inst_wf; exact Hls.
    + apply Forall_vlevel_inst_wf; exact Hls.
    + rewrite length_map; assumption.
    + apply Forall2_vlevel_inst_equiv; assumption.
    + apply vlevel_inst_wf_any; exact Hls.
    + exact IHVIsDefEqStrong1.
    + exact IHVIsDefEqStrong2.
  - unfold vinst0 in *. rewrite !vinstL_vinst in *.
    eapply VDFS_appDF; try (apply vlevel_inst_wf_any; exact Hls); eassumption.
  - eapply VDFS_lamDF; try (apply vlevel_inst_wf_any; exact Hls); eassumption.
  - eapply VDFS_forallEDF; try (apply vlevel_inst_wf_any; exact Hls); eassumption.
  - eapply VDFS_defeqDF; [apply vlevel_inst_wf_any; exact Hls | eassumption | eassumption].
  - unfold vinst0 in *. rewrite !vinstL_vinst in *.
    eapply VDFS_beta; try (apply vlevel_inst_wf_any; exact Hls); eassumption.
  - simpl in *.
    assert (Hvl : forall x, vinstL ls (vlift x) = vlift (vinstL ls x))
      by (intros x; unfold vlift; apply vinstL_vliftN).
    rewrite !Hvl, !vinstL_vliftN in *.
    eapply VDFS_eta;
      [apply vlevel_inst_wf_any; exact Hls
      | apply vlevel_inst_wf_any; exact Hls
      | exact IHVIsDefEqStrong1 | exact IHVIsDefEqStrong2 | exact IHVIsDefEqStrong3
      | exact IHVIsDefEqStrong4 | exact IHVIsDefEqStrong5 | exact IHVIsDefEqStrong6].
  - eapply VDFS_proofIrrel; eassumption.
  - rewrite !vinstL_vinstL in *.
    eapply VDFS_extra.
    + eassumption.
    + apply Forall_vlevel_inst_wf; exact Hls.
    + rewrite length_map; assumption.
    + apply vlevel_inst_wf_any; exact Hls.
    + exact IHVIsDefEqStrong1.
    + exact IHVIsDefEqStrong2.
    + exact IHVIsDefEqStrong3.
    + exact IHVIsDefEqStrong4.
    + exact IHVIsDefEqStrong5.
Qed.

Fixpoint VCtxStrong (env : VEnv) (U : nat) (G : list VExpr) : Prop :=
  match G with
  | [] => True
  | A :: G' => VCtxStrong env U G' /\ exists u, VIsDefEqStrong env U G' A A (VSort u)
  end.

Theorem VCtxStrong_lookup env U G i A :
  VEnvClosed env ->
  VCtxStrong env U G ->
  VLookup G i A ->
  exists u, VIsDefEqStrong env U G A A (VSort u).
Proof.
  intros Hcl HG Hlk. revert HG.
  induction Hlk as [A G | A G i B Hlk IH]; simpl; intros [HG [u HA]].
  - exists u. exact (VIsDefEqStrong_weakN Hcl HA (VCtxLiftN_one A G)).
  - destruct (IH HG) as [w HB].
    exists w. exact (VIsDefEqStrong_weakN Hcl HB (VCtxLiftN_one A G)).
Qed.

Theorem VCtxStrong_defeq env U G :
  VCtxStrong env U G -> VCtxWF env U G.
Proof.
  induction G as [|A G IH]; simpl; auto.
  intros [HG [u HA]]. split; [exact (IH HG) | exists u; exact (VIsDefEqStrong_defeq HA)].
Qed.

Theorem VCtxStrong_levelWF env U G :
  VCtxStrong env U G -> VCtxLevelWF U G.
Proof.
  induction G as [|A G IH]; simpl; auto.
  intros [HG [u HA]]. split; [exact (IH HG) |].
  destruct (VIsDefEq_levelWF (VIsDefEqStrong_defeq HA) (IH HG)) as [Hl _].
  exact Hl.
Qed.

Lemma vinst_vliftN1_succ e v k :
  vinst (vliftN 1 1 e) v (S (S k)) = vliftN 1 1 (vinst e v (S k)).
Proof.
  symmetry. exact (@vliftN_vinst_lo e v 1 1 (S k) ltac:(lia)).
Qed.

Theorem VIsDefEqStrong_instN env U G0 e0 A0 G1 e1 e2 A :
  VEnvWF env ->
  VIsDefEqStrong env U G0 e0 e0 A0 ->
  VCtxStrong env U G0 ->
  VIsDefEqStrong env U G1 e1 e2 A ->
  forall k G,
    VCtxInstN G0 e0 A0 k G1 G ->
    VCtxStrong env U G ->
    VIsDefEqStrong env U G (vinst e1 e0 k) (vinst e2 e0 k) (vinst A e0 k).
Proof.
  intros Hwf He0 HG0 H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  induction H; intros k G' W HG'; simpl.
  - clear H0 H1 IHVIsDefEqStrong.
    revert i A H HG'.
    induction W as [|k G1 G' B W IHW]; intros i ty Hlk HG'.
    + inversion Hlk as [A' G'' Heq1 Heq2 | A' G'' j C Hj Heq1 Heq2]; subst.
      * change (vinstVar 0 e0 0) with (vliftN 0 0 e0). rewrite vliftN_zero.
        change (vinst (vlift A0) e0 0) with (vinst0 (vlift A0) e0).
        rewrite vinst0_vlift. exact He0.
      * change (vinstVar (S j) e0 0) with (VBVar j).
        change (vinst (vlift C) e0 0) with (vinst0 (vlift C) e0).
        rewrite vinst0_vlift.
        destruct (VCtxStrong_lookup Hcl HG0 Hj) as [w Hty].
        eapply VDFS_bvar; [exact Hj | exact (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG0) (VIsDefEqStrong_defeq Hty)) | exact Hty].
    + inversion Hlk as [A' G'' Heq1 Heq2 | A' G'' j C Hj Heq1 Heq2]; subst.
      * change (vinstVar 0 e0 (S k)) with (VBVar 0).
        rewrite vinst_vlift_succ.
        destruct (VCtxStrong_lookup Hcl HG' (VLookupZero _ _)) as [w Hty].
        eapply VDFS_bvar; [constructor | exact (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') (VIsDefEqStrong_defeq Hty)) | exact Hty].
      * rewrite vinstVar_succ, vinst_vlift_succ.
        destruct HG' as [HG'_tail _].
        exact (VIsDefEqStrong_weakN Hcl (IHW j C Hj HG'_tail) (VCtxLiftN_one _ _)).
  - apply VDFS_symm. apply IHVIsDefEqStrong; assumption.
  - eapply VDFS_trans; [apply IHVIsDefEqStrong1 | apply IHVIsDefEqStrong2]; assumption.
  - apply VDFS_sortDF; assumption.
  - rewrite (vclosedN_vinst_eq e0 (closed_inst_const ls k Hcl H)).
    pose proof (IHVIsDefEqStrong2 k G' W HG') as IH2. simpl in IH2.
    rewrite (vclosedN_vinst_eq e0 (closed_inst_const ls k Hcl H)),
            (vclosedN_vinst_eq e0 (closed_inst_const ls' k Hcl H)) in IH2.
    eapply VDFS_constDF; eassumption.
  - rewrite vinst0_vinst_hi.
    pose proof (IHVIsDefEqStrong1 k G' W HG') as IH1. simpl in IH1.
    pose proof (IHVIsDefEqStrong5 k G' W HG') as IH5. simpl in IH5.
    rewrite !vinst0_vinst_hi in IH5.
    eapply VDFS_appDF;
      [exact H | exact H0 | exact IH1
      | apply IHVIsDefEqStrong2; [constructor; exact W | split; [exact HG' | exists u; exact IH1]]
      | apply IHVIsDefEqStrong3; assumption
      | apply IHVIsDefEqStrong4; assumption
      | exact IH5].
  - pose proof (IHVIsDefEqStrong1 k G' W HG') as IH1. simpl in IH1.
    assert (HG1 : VCtxStrong env U (vinst A e0 k :: G'))
      by (split; [exact HG' | exists u; exact (VIsDefEqStrong_refl_l IH1)]).
    assert (HG2 : VCtxStrong env U (vinst A' e0 k :: G'))
      by (split; [exact HG' | exists u; exact (VIsDefEqStrong_refl_r IH1)]).
    eapply VDFS_lamDF;
      [exact H | exact H0 | exact IH1
      | apply IHVIsDefEqStrong2; [constructor; exact W | exact HG1]
      | apply IHVIsDefEqStrong3; [constructor; exact W | exact HG2]
      | apply IHVIsDefEqStrong4; [constructor; exact W | exact HG1]
      | apply IHVIsDefEqStrong5; [constructor; exact W | exact HG2]].
  - pose proof (IHVIsDefEqStrong1 k G' W HG') as IH1. simpl in IH1.
    assert (HG1 : VCtxStrong env U (vinst A e0 k :: G'))
      by (split; [exact HG' | exists u; exact (VIsDefEqStrong_refl_l IH1)]).
    assert (HG2 : VCtxStrong env U (vinst A' e0 k :: G'))
      by (split; [exact HG' | exists u; exact (VIsDefEqStrong_refl_r IH1)]).
    eapply VDFS_forallEDF;
      [exact H | exact H0 | exact IH1
      | apply IHVIsDefEqStrong2; [constructor; exact W | exact HG1]
      | apply IHVIsDefEqStrong3; [constructor; exact W | exact HG2]].
  - eapply VDFS_defeqDF; [exact H | apply IHVIsDefEqStrong1; assumption | apply IHVIsDefEqStrong2; assumption].
  - rewrite !vinst0_vinst_hi.
    pose proof (IHVIsDefEqStrong1 k G' W HG') as IH1. simpl in IH1.
    assert (HG1 : VCtxStrong env U (vinst A e0 k :: G'))
      by (split; [exact HG' | exists u; exact IH1]).
    pose proof (IHVIsDefEqStrong5 k G' W HG') as IH5. simpl in IH5.
    rewrite !vinst0_vinst_hi in IH5.
    pose proof (IHVIsDefEqStrong6 k G' W HG') as IH6. simpl in IH6.
    rewrite !vinst0_vinst_hi in IH6.
    eapply VDFS_beta;
      [exact H | exact H0 | exact IH1
      | apply IHVIsDefEqStrong2; [constructor; exact W | exact HG1]
      | apply IHVIsDefEqStrong3; [constructor; exact W | exact HG1]
      | apply IHVIsDefEqStrong4; assumption
      | exact IH5 | exact IH6].
  - rewrite vinst_vlift_succ.
    pose proof (IHVIsDefEqStrong1 k G' W HG') as IH1. simpl in IH1.
    assert (HG1 : VCtxStrong env U (vinst A e0 k :: G'))
      by (split; [exact HG' | exists u; exact IH1]).
    assert (HG2 : VCtxStrong env U (vinst (vlift A) e0 (S k) :: vinst A e0 k :: G')).
    { split; [exact HG1 |]. exists u. rewrite vinst_vlift_succ.
      exact (VIsDefEqStrong_weakN Hcl IH1 (VCtxLiftN_one _ _)). }
    pose proof (IHVIsDefEqStrong3 (S (S k)) _ (VCtxInstN_succ (vlift A) (VCtxInstN_succ A W)) HG2) as IH3.
    simpl in IH3. rewrite vinst_vlift_succ, !vinst_vliftN1_succ in IH3.
    pose proof (IHVIsDefEqStrong5 (S k) _ (VCtxInstN_succ A W) HG1) as IH5.
    simpl in IH5. rewrite !vinst_vlift_succ, vinst_vliftN1_succ in IH5.
    pose proof (IHVIsDefEqStrong6 (S k) _ (VCtxInstN_succ A W) HG1) as IH6.
    simpl in IH6. rewrite !vinst_vlift_succ in IH6.
    eapply VDFS_eta;
      [exact H | exact H0 | exact IH1
      | apply IHVIsDefEqStrong2; [constructor; exact W | exact HG1]
      | exact IH3 | apply IHVIsDefEqStrong4; assumption | exact IH5 | exact IH6].
  - eapply VDFS_proofIrrel;
      [apply IHVIsDefEqStrong1 | apply IHVIsDefEqStrong2 | apply IHVIsDefEqStrong3]; assumption.
  - destruct (closed_inst_defeq ls k Hcl H) as [Hl [Hr Ht]].
    rewrite (vclosedN_vinst_eq e0 Hl), (vclosedN_vinst_eq e0 Hr), (vclosedN_vinst_eq e0 Ht).
    pose proof (IHVIsDefEqStrong4 k G' W HG') as IH4.
    pose proof (IHVIsDefEqStrong5 k G' W HG') as IH5.
    rewrite (vclosedN_vinst_eq e0 Hl), (vclosedN_vinst_eq e0 Ht) in IH4.
    rewrite (vclosedN_vinst_eq e0 Hr), (vclosedN_vinst_eq e0 Ht) in IH5.
    eapply VDFS_extra; eassumption.
Qed.

Theorem VIsDefEqStrong_defeqDF_l env U G A A' u e1 e2 B :
  VEnvWF env ->
  VCtxStrong env U G ->
  VIsDefEqStrong env U G A A' (VSort u) ->
  VIsDefEqStrong env U (A :: G) e1 e2 B ->
  VIsDefEqStrong env U (A' :: G) e1 e2 B.
Proof.
  intros Hwf HG H1 H2.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) (VIsDefEqStrong_defeq H1)) as Hu.
  assert (HG' : VCtxStrong env U (A' :: G))
    by (split; [exact HG | exists u; exact (VIsDefEqStrong_refl_r H1)]).
  assert (H0 : VIsDefEqStrong env U (A' :: G) (VBVar 0) (VBVar 0) (vlift A)).
  { eapply VDFS_defeqDF.
    - exact Hu.
    - exact (VDFS_symm (VIsDefEqStrong_weakN Hcl H1 (VCtxLiftN_one A' G))).
    - eapply VDFS_bvar; [constructor | exact Hu |].
      exact (VIsDefEqStrong_weakN Hcl (VIsDefEqStrong_refl_r H1) (VCtxLiftN_one A' G)). }
  pose proof (VIsDefEqStrong_instN Hwf H0 HG'
                (VIsDefEqStrong_weakN Hcl H2 (VCtxLiftN_succ A (VCtxLiftN_one A' G)))
                (VCtxInstN_zero (A' :: G) (VBVar 0) (vlift A)) HG') as Hres.
  unfold vinst0 in Hres. rewrite !vinst_vliftN_bvar0 in Hres. exact Hres.
Qed.

(* ========================================================================= *)
(* 5. Inversion, Regularity, Equivalence to Weak Judgment                    *)
(* ========================================================================= *)

Theorem VIsDefEqStrong_forallE_inv' env U G e1 e2 V :
  VEnvWF env ->
  VEnvStrong env ->
  VCtxStrong env U G ->
  VIsDefEqStrong env U G e1 e2 V ->
  forall A B, (e1 = VForallE A B \/ e2 = VForallE A B) ->
    (exists u, VIsDefEqStrong env U G A A (VSort u)) /\
    (exists v, VIsDefEqStrong env U (A :: G) B B (VSort v)).
Proof.
  intros Hwf Henv HG H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert HG.
  induction H; intros HG A0 B0 Heq; try (destruct Heq as [Heq | Heq]; discriminate).
  - apply (IHVIsDefEqStrong HG). tauto.
  - destruct Heq as [Heq | Heq];
      [apply (IHVIsDefEqStrong1 HG) | apply (IHVIsDefEqStrong2 HG)]; tauto.
  - destruct Heq as [Heq | Heq]; inversion Heq; subst A0 B0.
    + split; [exists u; exact (VIsDefEqStrong_refl_l H1) | exists v; exact (VIsDefEqStrong_refl_l H2)].
    + split; [exists u; exact (VIsDefEqStrong_refl_r H1) |].
      exists v. eapply VIsDefEqStrong_defeqDF_l;
        [exact Hwf | exact HG | exact H1 | exact (VIsDefEqStrong_refl_r H2)].
  - apply (IHVIsDefEqStrong2 HG). exact Heq.
  - destruct Heq as [Heq | Heq]; [discriminate |].
    destruct (vinst0_eq_forallE Heq) as [[He Ha] | [A1 [B1 [He [HA0 HB0]]]]].
    + apply (IHVIsDefEqStrong4 HG). left. exact Ha.
    + subst e A0 B0.
      assert (HG1 : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact H1]).
      destruct (IHVIsDefEqStrong3 HG1 A1 B1 (or_introl eq_refl)) as [[u1 HA1] [v1 HB1]].
      assert (HA1_inst : VIsDefEqStrong env U G (vinst A1 e' 0) (vinst A1 e' 0) (VSort u1)).
      { exact (VIsDefEqStrong_instN Hwf H4 HG HA1 (VCtxInstN_zero G e' A) HG). }
      split; [exists u1; exact HA1_inst |].
      exists v1.
      exact (VIsDefEqStrong_instN Hwf H4 HG HB1 (VCtxInstN_succ A1 (VCtxInstN_zero G e' A))
              (conj HG (ex_intro _ u1 HA1_inst))).
  - destruct Heq as [Heq | Heq]; [discriminate |].
    apply (IHVIsDefEqStrong4 HG). left. exact Heq.
  - destruct Heq as [Heq | Heq];
      [apply (IHVIsDefEqStrong2 HG) | apply (IHVIsDefEqStrong3 HG)]; left; exact Heq.
  - assert (Hhelper : forall e,
      vinstL ls e = VForallE A0 B0 ->
      VEnvStrongPred env (vdf_uvars df) e (vdf_type df) ->
      (exists u0, VIsDefEqStrong env U G A0 A0 (VSort u0)) /\
      (exists v0, VIsDefEqStrong env U (A0 :: G) B0 B0 (VSort v0))).
    { intros e He Hpred.
      destruct e as [i|w|c us|f x|A1 b|A1 B1]; simpl in He; try discriminate.
      inversion He; subst A0 B0. clear He.
      destruct Hpred as [_ [_ [_ Hpi]]].
      destruct (Hpi A1 B1 eq_refl) as [[u1 HA1] [v1 HB1]].
      pose proof (VIsDefEqStrong_instL H0 HA1) as HA1'. simpl in HA1'.
      pose proof (VIsDefEqStrong_instL H0 HB1) as HB1'. simpl in HB1'.
      destruct (VIsDefEq_closedN Hcl (VIsDefEqStrong_defeq HA1') I) as [CA _]. simpl in CA.
      destruct (VIsDefEq_closedN Hcl (VIsDefEqStrong_defeq HB1') (conj I CA)) as [CB _]. simpl in CB.
      split.
      - exists (vlevel_inst ls u1). apply (VIsDefEqStrong_weak0 Hcl HA1').
      - exists (vlevel_inst ls v1).
        assert (Hz : VCtxLiftN (List.length G) 0 [] (G ++ [])) by (constructor; reflexivity).
        rewrite app_nil_r in Hz.
        pose proof (VIsDefEqStrong_weakN Hcl HB1' (VCtxLiftN_succ (vinstL ls A1) Hz)) as Hw.
        simpl in Hw.
        rewrite (@vclosedN_vliftN_eq _ (List.length G) 0 CA) in Hw.
        rewrite (@vclosedN_vliftN_eq _ (List.length G) 1 CB) in Hw.
        exact Hw. }
    destruct (proj2 Henv df H) as [HpL HpR].
    destruct Heq as [Heq | Heq]; [exact (Hhelper _ Heq HpL) | exact (Hhelper _ Heq HpR)].
Qed.

Theorem VIsDefEqStrong_isType' env U G e1 e2 A :
  VEnvWF env ->
  VEnvStrong env ->
  VCtxStrong env U G ->
  VIsDefEqStrong env U G e1 e2 A ->
  exists u, VIsDefEqStrong env U G A A (VSort u).
Proof.
  intros Hwf Henv HG H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert HG.
  induction H; intros HG.
  - eapply VCtxStrong_lookup; eassumption.
  - apply (IHVIsDefEqStrong HG).
  - apply (IHVIsDefEqStrong1 HG).
  - exists (VLSucc (VLSucc l)). apply VDFS_sortDF; [exact H | exact H | apply vlevel_equiv_refl].
  - destruct (proj1 Henv c ci H) as [w [Hc _]].
    exists (vlevel_inst ls w).
    apply (VIsDefEqStrong_weak0 Hcl (VIsDefEqStrong_instL H0 Hc)).
  - destruct (IHVIsDefEqStrong3 HG) as [w Hpi].
    destruct (VIsDefEqStrong_forallE_inv' Hwf Henv HG Hpi (or_introl eq_refl)) as [_ [v1 HB1]].
    exists v1.
    exact (VIsDefEqStrong_instN Hwf (VIsDefEqStrong_refl_l H4) HG HB1 (VCtxInstN_zero G a A) HG).
  - exists (VLIMax u v).
    eapply VDFS_forallEDF; [exact H | exact H0 | exact (VIsDefEqStrong_refl_l H1) | exact H2 | exact H2].
  - exists (VLSucc (VLIMax u v)).
    apply VDFS_sortDF; [simpl; auto | simpl; auto | apply vlevel_equiv_refl].
  - exists u. exact (VIsDefEqStrong_refl_r H0).
  - exists v. exact H5.
  - apply (IHVIsDefEqStrong4 HG).
  - exists VLZero. exact H.
  - destruct (proj2 Henv df H) as [[_ [[w Ht] _]] _].
    exists (vlevel_inst ls w).
    apply (VIsDefEqStrong_weak0 Hcl (VIsDefEqStrong_instL H0 Ht)).
Qed.

Theorem VIsDefEqStrong_instDF env U G A B f f' a a' u v :
  VEnvWF env ->
  VCtxStrong env U G ->
  vlevel_wf U u ->
  vlevel_wf U v ->
  VIsDefEqStrong env U G A A (VSort u) ->
  VIsDefEqStrong env U (A :: G) B B (VSort v) ->
  VIsDefEqStrong env U (A :: G) f f' B ->
  VIsDefEqStrong env U G a a' A ->
  VIsDefEqStrong env U G (vinst0 f a) (vinst0 f' a') (vinst0 B a).
Proof.
  intros Hwf HG Hu Hv HA HB Hf Ha.
  assert (H2 : forall f0 f0' B0 v0,
    vlevel_wf U v0 ->
    VIsDefEqStrong env U (A :: G) B0 B0 (VSort v0) ->
    VIsDefEqStrong env U (A :: G) f0 f0' B0 ->
    VIsDefEqStrong env U G (vinst0 B0 a) (vinst0 B0 a') (VSort v0) ->
    VIsDefEqStrong env U G (vinst0 f0 a) (vinst0 f0' a') (vinst0 B0 a)).
  { clear f f' B v Hv HB Hf.
    intros f0 f0' B0 v0 Hv0 HB0 Hf0 Hi.
    assert (H1 : forall a0 g0,
      VIsDefEqStrong env U (A :: G) g0 g0 B0 ->
      VIsDefEqStrong env U G a0 a0 A ->
      VIsDefEqStrong env U G (VApp (VLam A g0) a0) (vinst0 g0 a0) (vinst0 B0 a0)).
    { intros a0 g0 Hg0 Ha0.
      eapply VDFS_beta;
        [exact Hu | exact Hv0 | exact HA | exact HB0 | exact Hg0 | exact Ha0
        | exact (VIsDefEqStrong_instN Hwf Ha0 HG HB0 (VCtxInstN_zero G a0 A) HG)
        | exact (VIsDefEqStrong_instN Hwf Ha0 HG Hg0 (VCtxInstN_zero G a0 A) HG)]. }
    eapply VDFS_trans.
    - apply VDFS_symm. exact (H1 a f0 (VIsDefEqStrong_refl_l Hf0) (VIsDefEqStrong_refl_l Ha)).
    - eapply VDFS_trans.
      + eapply VDFS_appDF;
          [exact Hu | exact Hv0 | exact HA | exact HB0
          | eapply VDFS_lamDF; [exact Hu | exact Hv0 | exact HA | exact HB0 | exact HB0 | exact Hf0 | exact Hf0]
          | exact Ha | exact Hi].
      + eapply VDFS_defeqDF;
          [exact Hv0 | exact (VDFS_symm Hi)
          | exact (H1 a' f0' (VIsDefEqStrong_refl_r Hf0) (VIsDefEqStrong_refl_r Ha))]. }
  apply (H2 f f' B v Hv HB Hf).
  exact (H2 B B (VSort v) (VLSucc v) Hv
          (VDFS_sortDF (A :: G) Hv Hv (vlevel_equiv_refl v))
          HB
          (VDFS_sortDF G Hv Hv (vlevel_equiv_refl v))).
Qed.

Theorem VEqUpToLevels_defeq env U G e1 e2 e1' e2' A :
  VEnvWF env ->
  VEnvStrong env ->
  VCtxStrong env U G ->
  VIsDefEqStrong env U G e1 e2 A ->
  VEqUpToLevels U e1 e1' ->
  VEqUpToLevels U e2 e2' ->
  VIsDefEqStrong env U G e1' e2' A.
Proof.
  intros Hwf Henv W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert W e1' e2'.
  induction H; intros W e1' e2' Heul1 Heul2.
  - inversion Heul1; inversion Heul2; subst. eapply VDFS_bvar; [exact H | exact H0 | exact H1].
  - apply VDFS_symm. exact (IHVIsDefEqStrong W e2' e1' Heul2 Heul1).
  - pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H)) as Heul_mid.
    eapply VDFS_trans; [exact (IHVIsDefEqStrong1 W e1' e2 Heul1 Heul_mid) | exact (IHVIsDefEqStrong2 W e2 e2' Heul_mid Heul2)].
  - inversion Heul1 as [| |l1 l1' a1 a2 a3| | |]; subst.
    inversion Heul2 as [| |l2 l2' b1 b2 b3| | |]; subst.
    eapply VDFS_defeqDF with (u := VLSucc (VLSucc l)).
    + exact a1.
    + apply VDFS_symm.
      exact (@VDFS_sortDF env U G (VLSucc l) (VLSucc l1') a1 a2 (vlevel_succ_congr a3)).
    + apply VDFS_sortDF; [exact a2 | exact b2 |].
      eapply vlevel_equiv_trans; [apply vlevel_equiv_symm; exact a3 |].
      eapply vlevel_equiv_trans; [exact H1 | exact b3].
  - inversion Heul1 as [|c1 ls1 ls1' a1 a2 a3| | | |]; subst.
    inversion Heul2 as [|c2 ls2 ls2' b1 b2 b3| | | |]; subst.
    destruct (proj1 Henv c ci H) as [w [_ [_ [Hcongr _]]]].
    pose proof (Forall2_vlevel_equiv_trans (Forall2_vlevel_equiv_symm a3)
                  (Forall2_vlevel_equiv_trans H3 b3)) as Hc2.
    pose proof (Hcongr U ls1' ls2' a2 b2 Hc2) as Hty12.
    pose proof (Hcongr U ls ls1' a1 a2 a3) as Hty01.
    eapply VDFS_defeqDF.
    + apply vlevel_inst_wf_any; exact a1.
    + apply VDFS_symm. exact (VIsDefEqStrong_weak0 Hcl Hty01).
    + eapply VDFS_constDF.
      * exact H.
      * exact a2.
      * exact b2.
      * rewrite <- (Forall2_length_eq a3). exact H2.
      * exact Hc2.
      * apply vlevel_inst_wf_any; exact a2.
      * exact Hty12.
      * exact (VIsDefEqStrong_weak0 Hcl Hty12).
  - inversion Heul1 as [| | |f0 f0' a0 a0' a1 a2| |]; subst.
    inversion Heul2 as [| | |f2 f2' a2_0 a2' b1 b2| |]; subst.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H4)) as Ha_refl.
    pose proof (VDFS_trans (IHVIsDefEqStrong4 W _ _ a2 Ha_refl) (VDFS_symm H4)) as Ha_conv.
    eapply VDFS_defeqDF.
    + exact H0.
    + exact (VIsDefEqStrong_instDF (v := VLSucc v) Hwf W H H0 H1
              (VDFS_sortDF (A :: G) H0 H0 (vlevel_equiv_refl v)) H2 Ha_conv).
    + eapply VDFS_appDF;
        [exact H | exact H0 | exact H1 | exact H2
        | exact (IHVIsDefEqStrong3 W _ _ a1 b1)
        | exact (IHVIsDefEqStrong4 W _ _ a2 b2)
        | exact (VIsDefEqStrong_instDF (v := VLSucc v) Hwf W H H0 H1
                  (VDFS_sortDF (A :: G) H0 H0 (vlevel_equiv_refl v)) H2
                  (IHVIsDefEqStrong4 W _ _ a2 b2))].
  - inversion Heul1 as [| | | |A0 A0' bd0 bd0' a1 a2|]; subst.
    inversion Heul2 as [| | | |A2 A2' bd2 bd2' b1 b2|]; subst.
    destruct (VEqUpToLevels_refl (VCtxStrong_levelWF W) H1) as [HA_r1 HA_r2].
    pose proof (VDFS_trans (IHVIsDefEqStrong1 W _ _ a1 HA_r2) (VDFS_symm H1)) as c1.
    pose proof (IHVIsDefEqStrong1 W _ _ HA_r1 b1) as c2.
    pose proof (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) H2) as H2'.
    pose proof (IHVIsDefEqStrong4 (conj W (ex_intro _ u (VIsDefEqStrong_refl_l H1))) _ _ a2 b2) as ih_bd.
    eapply (VDFS_defeqDF (u := VLIMax u v)).
    + simpl; split; [exact H | exact H0].
    + eapply VDFS_forallEDF; [exact H | exact H0 | exact c1 | exact H2' | exact H2].
    + eapply VDFS_lamDF;
        [exact H | exact H0 | exact (IHVIsDefEqStrong1 W _ _ a1 b1)
        | exact H2' | exact (VIsDefEqStrong_defeqDF_l Hwf W c2 H2)
        | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) ih_bd)
        | exact (VIsDefEqStrong_defeqDF_l Hwf W c2 ih_bd)].
  - inversion Heul1 as [| | | | |A0 A0' bd0 bd0' a1 a2]; subst.
    inversion Heul2 as [| | | | |A2 A2' bd2 bd2' b1 b2]; subst.
    destruct (VEqUpToLevels_refl (VCtxStrong_levelWF W) H1) as [HA_r1 HA_r2].
    pose proof (VDFS_trans (IHVIsDefEqStrong1 W _ _ a1 HA_r2) (VDFS_symm H1)) as c1.
    pose proof (IHVIsDefEqStrong1 W _ _ HA_r1 b1) as c2.
    pose proof (IHVIsDefEqStrong2 (conj W (ex_intro _ u (VIsDefEqStrong_refl_l H1))) _ _ a2 b2) as ih_bd.
    eapply VDFS_forallEDF;
      [exact H | exact H0 | exact (IHVIsDefEqStrong1 W _ _ a1 b1)
      | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) ih_bd)
      | exact (VIsDefEqStrong_defeqDF_l Hwf W c2 ih_bd)].
  - eapply VDFS_defeqDF; [exact H | exact H0 | exact (IHVIsDefEqStrong2 W _ _ Heul1 Heul2)].
  - inversion Heul1 as [| | |fn0 fn0' arg0 arg0' Hlam a3| |]; subst.
    inversion Hlam as [| | | |A0 A0' e0_ e0' a1 a2|]; subst.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H1)) as HA_r.
    pose proof (VDFS_trans (IHVIsDefEqStrong1 W _ _ a1 HA_r) (VDFS_symm H1)) as c1.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H4)) as He'_r.
    pose proof (VDFS_trans (IHVIsDefEqStrong4 W _ _ a3 He'_r) (VDFS_symm H4)) as c2.
    assert (W_A : VCtxStrong env U (A :: G)) by (split; [exact W | exists u; exact H1]).
    pose proof (IHVIsDefEqStrong3 W_A _ _ a2 a2) as c3.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W_A) H2)) as hb.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H5)) as h7_r.
    pose proof (IHVIsDefEqStrong5 W _ _ (VEqUpToLevels_instN 0 a3 hb) h7_r) as c4.
    eapply VDFS_trans; [| exact (IHVIsDefEqStrong6 W _ _ (VEqUpToLevels_instN 0 a3 a2) Heul2)].
    eapply VDFS_defeqDF.
    + exact H0.
    + exact (VIsDefEqStrong_instDF (v := VLSucc v) Hwf W H H0 H1
              (VDFS_sortDF (A :: G) H0 H0 (vlevel_equiv_refl v)) H2 c2).
    + eapply VDFS_beta;
        [exact H | exact H0 | exact (VIsDefEqStrong_refl_l c1)
        | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) H2)
        | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) c3)
        | exact (VDFS_defeqDF H (VDFS_symm c1) (VIsDefEqStrong_refl_l c2))
        | exact (VIsDefEqStrong_refl_l c4)
        | exact (VIsDefEqStrong_instN Hwf (VIsDefEqStrong_refl_l c2) W c3 (VCtxInstN_zero G arg0' A) W)].
  - inversion Heul1 as [| | | |A0 A0' app0 app0' a1 Happ|]; subst.
    inversion Happ as [| | |el0 el0' bv0 bv0' a2 Hbvar| |]; subst.
    inversion Hbvar; subst.
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H1)) as HA_r.
    pose proof (VDFS_trans (IHVIsDefEqStrong1 W _ _ a1 HA_r) (VDFS_symm H1)) as c1.
    assert (W_A : VCtxStrong env U (A :: G)) by (split; [exact W | exists u; exact H1]).
    pose proof (proj2 (VEqUpToLevels_refl (VCtxStrong_levelWF W_A) H5)) as H5_r.
    pose proof (IHVIsDefEqStrong5 W_A _ _ a2 H5_r) as c2.
    assert (c3 : VIsDefEqStrong env U (A :: G) (VApp el0' (VBVar 0)) (VApp (vlift e) (VBVar 0)) B).
    { pose proof (VDFS_appDF H H0 H6 H3 c2 (VDFS_bvar (VLookupZero A G) H H6)) as Happ_raw.
      unfold vinst0 in Happ_raw. rewrite !vinst_vliftN_bvar0 in Happ_raw.
      exact (Happ_raw H2). }
    eapply VDFS_trans.
    + apply VDFS_symm.
      eapply VDFS_lamDF;
        [exact H | exact H0 | exact (VDFS_symm c1) | exact H2
        | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) H2)
        | exact (VDFS_symm c3)
        | exact (VIsDefEqStrong_defeqDF_l Hwf W (VDFS_symm c1) (VDFS_symm c3))].
    + eapply VDFS_trans.
      * eapply VDFS_eta; [exact H | exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6].
      * pose proof (proj1 (VEqUpToLevels_refl (VCtxStrong_levelWF W) H4)) as He_r.
        exact (IHVIsDefEqStrong4 W _ _ He_r Heul2).
  - eapply VDFS_proofIrrel;
      [exact H | exact (IHVIsDefEqStrong2 W _ _ Heul1 Heul1) | exact (IHVIsDefEqStrong3 W _ _ Heul2 Heul2)].
  - pose proof (proj2 (VEqUpToLevels_refl (I : VCtxLevelWF U []) H4)) as Hl_r.
    pose proof (proj2 (VEqUpToLevels_refl (I : VCtxLevelWF U []) H5)) as Hr_r.
    pose proof (IHVIsDefEqStrong2 I _ _ Heul1 Hl_r) as c1.
    pose proof (IHVIsDefEqStrong3 I _ _ Heul2 Hr_r) as c2.
    apply (VIsDefEqStrong_weak0 Hcl).
    eapply VDFS_trans; [exact c1 |].
    eapply VDFS_trans; [| exact (VDFS_symm c2)].
    eapply VDFS_extra; [exact H | exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H4 | exact H5].
Qed.

Theorem VIsDefEq_strong' env U G e1 e2 A :
  VEnvWF env ->
  VEnvStrong env ->
  VCtxStrong env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEqStrong env U G e1 e2 A.
Proof.
  intros Hwf Henv HG H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert HG.
  induction H; intros HG.
  - destruct (VCtxStrong_lookup Hcl HG H) as [u HA].
    eapply VDFS_bvar; [exact H | exact (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) (VIsDefEqStrong_defeq HA)) | exact HA].
  - apply VDFS_symm. exact (IHVIsDefEq HG).
  - eapply VDFS_trans; [exact (IHVIsDefEq1 HG) | exact (IHVIsDefEq2 HG)].
  - apply VDFS_sortDF; assumption.
  - destruct (proj1 Henv c ci H) as [w [_ [_ [Hcongr _]]]].
    pose proof (Hcongr U ls1 ls2 H0 H1 H3) as Hty.
    eapply VDFS_constDF; [exact H | exact H0 | exact H1 | exact H2 | exact H3
                         | apply vlevel_inst_wf_any; exact H0 | exact Hty
                         | exact (VIsDefEqStrong_weak0 Hcl Hty)].
  - pose proof (IHVIsDefEq1 HG) as ih1.
    pose proof (IHVIsDefEq2 HG) as ih2.
    destruct (VIsDefEqStrong_isType' Hwf Henv HG ih1) as [w Hpi].
    destruct (VIsDefEqStrong_forallE_inv' Hwf Henv HG Hpi (or_introl eq_refl)) as [[u HA] [v HB]].
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) (VIsDefEqStrong_defeq HA)) as Hu.
    assert (HG' : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact HA]).
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') (VIsDefEqStrong_defeq HB)) as Hv.
    eapply VDFS_appDF;
      [exact Hu | exact Hv | exact HA | exact HB | exact ih1 | exact ih2
      | exact (VIsDefEqStrong_instDF (v := VLSucc v) Hwf HG Hu Hv HA
                (VDFS_sortDF (A :: G) Hv Hv (vlevel_equiv_refl v)) HB ih2)].
  - pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) H) as Hu.
    pose proof (IHVIsDefEq1 HG) as ih1.
    assert (HG' : VCtxStrong env U (A1 :: G))
      by (split; [exact HG | exists u; exact (VIsDefEqStrong_refl_l ih1)]).
    pose proof (IHVIsDefEq2 HG') as ih2.
    destruct (VIsDefEqStrong_isType' Hwf Henv HG' ih2) as [v HB].
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') (VIsDefEqStrong_defeq HB)) as Hv.
    eapply VDFS_lamDF;
      [exact Hu | exact Hv | exact ih1 | exact HB
      | exact (VIsDefEqStrong_defeqDF_l Hwf HG ih1 HB)
      | exact ih2
      | exact (VIsDefEqStrong_defeqDF_l Hwf HG ih1 ih2)].
  - pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) H) as Hu.
    pose proof (IHVIsDefEq1 HG) as ih1.
    assert (HG' : VCtxStrong env U (A1 :: G))
      by (split; [exact HG | exists u; exact (VIsDefEqStrong_refl_l ih1)]).
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') H0) as Hv.
    pose proof (IHVIsDefEq2 HG') as ih2.
    eapply VDFS_forallEDF;
      [exact Hu | exact Hv | exact ih1 | exact ih2
      | exact (VIsDefEqStrong_defeqDF_l Hwf HG ih1 ih2)].
  - pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) H) as Hu.
    eapply VDFS_defeqDF; [exact Hu | exact (IHVIsDefEq1 HG) | exact (IHVIsDefEq2 HG)].
  - pose proof (IHVIsDefEq2 HG) as he'.
    destruct (VIsDefEqStrong_isType' Hwf Henv HG he') as [u HA].
    assert (HG' : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact HA]).
    pose proof (IHVIsDefEq1 HG') as he.
    destruct (VIsDefEqStrong_isType' Hwf Henv HG' he) as [v HB].
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) (VIsDefEqStrong_defeq HA)) as Hu.
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') (VIsDefEqStrong_defeq HB)) as Hv.
    eapply VDFS_beta;
      [exact Hu | exact Hv | exact HA | exact HB | exact he | exact he'
      | exact (VIsDefEqStrong_instN Hwf he' HG HB (VCtxInstN_zero G a A) HG)
      | exact (VIsDefEqStrong_instN Hwf he' HG he (VCtxInstN_zero G a A) HG)].
  - pose proof (IHVIsDefEq HG) as he.
    destruct (VIsDefEqStrong_isType' Hwf Henv HG he) as [w HAB].
    destruct (VIsDefEqStrong_forallE_inv' Hwf Henv HG HAB (or_introl eq_refl)) as [[u HA] [v HB]].
    assert (HG' : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact HA]).
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG) (VIsDefEqStrong_defeq HA)) as Hu.
    pose proof (VIsDefEq_sort_r Hwf (VCtxStrong_defeq HG') (VIsDefEqStrong_defeq HB)) as Hv.
    eapply VDFS_eta;
      [exact Hu | exact Hv | exact HA | exact HB
      | exact (VIsDefEqStrong_weakN Hcl HB (VCtxLiftN_succ A (VCtxLiftN_one A G)))
      | exact he
      | exact (VIsDefEqStrong_weakN Hcl he (VCtxLiftN_one A G))
      | exact (VIsDefEqStrong_weakN Hcl HA (VCtxLiftN_one A G))].
  - eapply VDFS_proofIrrel; [exact (IHVIsDefEq1 HG) | exact (IHVIsDefEq2 HG) | exact (IHVIsDefEq3 HG)].
  - destruct (proj2 Henv df H) as [[Hl [[w Ht] _]] [Hr _]].
    pose proof (VIsDefEqStrong_instL H0 Ht) as Ht'. simpl in Ht'.
    pose proof (VIsDefEqStrong_instL H0 Hl) as Hl'. simpl in Hl'.
    pose proof (VIsDefEqStrong_instL H0 Hr) as Hr'. simpl in Hr'.
    eapply VDFS_extra;
      [exact H | exact H0 | exact H1 | apply vlevel_inst_wf_any; exact H0
      | exact Ht' | exact Hl' | exact Hr'
      | exact (VIsDefEqStrong_weak0 Hcl Hl') | exact (VIsDefEqStrong_weak0 Hcl Hr')].
Qed.

Theorem VCtxStrong_strong' env U G :
  VEnvWF env ->
  VEnvStrong env ->
  VCtxWF env U G ->
  VCtxStrong env U G.
Proof.
  intros Hwf Henv.
  induction G as [|A G IH]; simpl; auto.
  intros [HG [u HA]].
  pose proof (IH HG) as HGs.
  split; [exact HGs | exists u; exact (VIsDefEq_strong' Hwf Henv HGs HA)].
Qed.

Lemma VEnvStrongPred_mono env1 env2 U e A :
  venv_ordered env1 env2 ->
  VEnvStrongPred env1 U e A ->
  VEnvStrongPred env2 U e A.
Proof.
  intros Hord [H1 [[u H2] [H3 H4]]].
  split; [exact (VIsDefEqStrong_mono Hord H1) |].
  split; [exists u; exact (VIsDefEqStrong_mono Hord H2) |].
  split.
  - intros U' ls ls' a1 a2 a3. exact (VIsDefEqStrong_mono Hord (H3 U' ls ls' a1 a2 a3)).
  - intros A0 B0 Heq. destruct (H4 A0 B0 Heq) as [[u0 HA0] [v0 HB0]].
    split; [exists u0; exact (VIsDefEqStrong_mono Hord HA0)
           |exists v0; exact (VIsDefEqStrong_mono Hord HB0)].
Qed.

Lemma VEnvStrongPred_of_hasType env U e A :
  VEnvWF env ->
  VEnvStrong env ->
  VHasType env U [] e A ->
  VEnvStrongPred env U e A.
Proof.
  intros Hwf IH Hty.
  pose proof (VIsDefEq_strong' Hwf IH (I : VCtxStrong env U []) Hty) as H'.
  split; [exact H' |].
  split; [exact (VIsDefEqStrong_isType' Hwf IH (I : VCtxStrong env U []) H') |].
  split.
  - intros U' ls ls' h1 h2 h3.
    pose proof (VIsDefEqStrong_instL h1 H') as Hi. simpl in Hi.
    exact (VEqUpToLevels_defeq Hwf IH (I : VCtxStrong env U' []) Hi
            (proj1 (VEqUpToLevels_refl (I : VCtxLevelWF U' []) Hi))
            (proj1 (VEqUpToLevels_instL h1 h2 h3 H'))).
  - intros A0 B0 Heq.
    exact (VIsDefEqStrong_forallE_inv' Hwf IH (I : VCtxStrong env U []) H' (or_introl Heq)).
Qed.

Theorem VEnvWF_strong env :
  VEnvWF env -> VEnvStrong env.
Proof.
  induction 1 as [|env n ci env' Hwf IH Hci Hadd | env df Hwf IH Hdf].
  - split; simpl; intros; [discriminate | contradiction].
  - pose proof (venv_add_const_ordered _ _ _ Hadd) as Hord.
    unfold venv_add_const in Hadd.
    destruct (venv_constants env n) eqn:Hn; [discriminate |].
    inversion Hadd; subst env'. clear Hadd.
    split; simpl.
    + intros c ci0. destruct (name_eqb c n).
      * intros Heq. inversion Heq; subst ci0.
        destruct Hci as [[u Hu] _].
        exists u. apply (VEnvStrongPred_mono Hord).
        exact (VEnvStrongPred_of_hasType Hwf IH Hu).
      * intros Hc. destruct (proj1 IH c ci0 Hc) as [u Hu].
        exists u. exact (VEnvStrongPred_mono Hord Hu).
    + intros df Hin. destruct (proj2 IH df Hin) as [Hl Hr].
      split; apply (VEnvStrongPred_mono Hord); assumption.
  - pose proof (venv_add_defeq_ordered env df) as Hord.
    split; simpl.
    + intros c ci Hc. destruct (proj1 IH c ci Hc) as [u Hu].
      exists u. exact (VEnvStrongPred_mono Hord Hu).
    + intros df0 [Heq | Hin].
      * subst df0. destruct Hdf as [Hl [Hr _]].
        split; apply (VEnvStrongPred_mono Hord);
          apply (VEnvStrongPred_of_hasType Hwf IH); assumption.
      * destruct (proj2 IH df0 Hin) as [Hl Hr].
        split; apply (VEnvStrongPred_mono Hord); assumption.
Qed.

Theorem VCtxStrong_strong env U G :
  VEnvWF env -> VCtxWF env U G -> VCtxStrong env U G.
Proof.
  intros Hwf HG. exact (VCtxStrong_strong' Hwf (VEnvWF_strong Hwf) HG).
Qed.

Theorem VIsDefEq_strong env U G e1 e2 A :
  VEnvWF env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEqStrong env U G e1 e2 A.
Proof.
  intros Hwf HG H.
  exact (VIsDefEq_strong' Hwf (VEnvWF_strong Hwf) (VCtxStrong_strong Hwf HG) H).
Qed.

Theorem VIsDefEq_eqUpToLevels env U G e1 e2 e2' A :
  VEnvWF env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VEqUpToLevels U e2 e2' ->
  VIsDefEq env U G e1 e2' A.
Proof.
  intros Hwf HG H Heul.
  pose proof (VCtxStrong_strong Hwf HG) as W.
  pose proof (VIsDefEq_strong Hwf HG H) as Hs.
  apply VIsDefEqStrong_defeq.
  exact (VEqUpToLevels_defeq Hwf (VEnvWF_strong Hwf) W Hs
          (proj1 (VEqUpToLevels_refl (VCtxStrong_levelWF W) Hs)) Heul).
Qed.

(* ========================================================================= *)
(* 6. Strong Typing Equivalence & Syntactic Typing Inversions Modulo DefEq   *)
(* ========================================================================= *)

Theorem VIsDefEqStrong_hasType' env U G e1 e2 A :
  VIsDefEqStrong env U G e1 e2 A ->
  VHasTypeStrong env U G e1 A true /\ VHasTypeStrong env U G e2 A true.
Proof.
  induction 1.
  - destruct IHVIsDefEqStrong as [HA _].
    assert (Hb : VHasTypeStrong env U G (VBVar i) A true)
      by (apply VHTS_base; eapply VHTS_bvar; [exact H | exact H0 | exact HA]).
    split; exact Hb.
  - tauto.
  - tauto.
  - split.
    + apply VHTS_base. apply VHTS_sort'; [exact H | exact H | apply vlevel_equiv_refl].
    + apply VHTS_base. apply VHTS_sort'; [exact H0 | exact H | apply vlevel_equiv_symm; exact H1].
  - destruct IHVIsDefEqStrong1 as [Hi1 Hi2].
    destruct IHVIsDefEqStrong2 as [Hg1 Hg2].
    split.
    + apply VHTS_base. eapply VHTS_const; [exact H | exact H0 | exact H2 | exact H4 | exact Hi1 | exact Hg1].
    + eapply VHTS_defeq; [exact H4 | exact (VDFS_symm H6) | exact Hg2 | exact Hg1 |].
      apply VHTS_base. eapply VHTS_const;
        [exact H | exact H1 | rewrite <- (Forall2_length_eq H3); exact H2 | exact H4 | exact Hi2 | exact Hg2].
  - destruct IHVIsDefEqStrong1 as [HA1 HA2], IHVIsDefEqStrong2 as [HB1 HB2],
             IHVIsDefEqStrong3 as [Hf1 Hf2], IHVIsDefEqStrong4 as [Ha1 Ha2],
             IHVIsDefEqStrong5 as [HBi1 HBi2].
    assert (Hpi : VHasTypeStrong env U G (VForallE A B) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA1 | exact HB1]).
    split.
    + apply VHTS_base. eapply VHTS_app; [exact H | exact H0 | exact HA1 | exact HB1 | exact Hpi | exact Hf1 | exact Ha1 | exact HBi1].
    + eapply VHTS_defeq; [exact H0 | exact (VDFS_symm H5) | exact HBi2 | exact HBi1 |].
      apply VHTS_base. eapply VHTS_app; [exact H | exact H0 | exact HA2 | exact HB2 | exact Hpi | exact Hf2 | exact Ha2 | exact HBi2].
  - destruct IHVIsDefEqStrong1 as [HA1 HA2], IHVIsDefEqStrong2 as [HB1 _],
             IHVIsDefEqStrong3 as [HB'1 _], IHVIsDefEqStrong4 as [Hbd1 _],
             IHVIsDefEqStrong5 as [_ Hbd'2].
    assert (Hpi1 : VHasTypeStrong env U G (VForallE A B) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA1 | exact HB1]).
    assert (Hpi2 : VHasTypeStrong env U G (VForallE A' B) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA2 | exact HB'1]).
    split.
    + apply VHTS_base. eapply VHTS_lam; [exact H | exact H0 | exact HA1 | exact HB1 | exact Hbd1 | exact Hpi1].
    + eapply (VHTS_defeq (u := VLIMax u v)).
      * simpl; split; [exact H | exact H0].
      * apply VDFS_symm. eapply VDFS_forallEDF; [exact H | exact H0 | exact H1 | exact H2 | exact H3].
      * exact Hpi2.
      * exact Hpi1.
      * apply VHTS_base. eapply VHTS_lam; [exact H | exact H0 | exact HA2 | exact HB'1 | exact Hbd'2 | exact Hpi2].
  - destruct IHVIsDefEqStrong1 as [HA1 HA2], IHVIsDefEqStrong2 as [HB1 _],
             IHVIsDefEqStrong3 as [_ HB'2].
    split; apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA1 | exact HB1 | exact H | exact H0 | exact HA2 | exact HB'2].
  - destruct IHVIsDefEqStrong1 as [HA1 HA2], IHVIsDefEqStrong2 as [He1 He2].
    split; eapply VHTS_defeq; [exact H | exact H0 | exact HA1 | exact HA2 | exact He1 | exact H | exact H0 | exact HA1 | exact HA2 | exact He2].
  - destruct IHVIsDefEqStrong1 as [HA1 _], IHVIsDefEqStrong2 as [HB1 _],
             IHVIsDefEqStrong3 as [He1 _], IHVIsDefEqStrong4 as [He'1 _],
             IHVIsDefEqStrong5 as [HBi1 _], IHVIsDefEqStrong6 as [Hei1 _].
    assert (Hpi : VHasTypeStrong env U G (VForallE A B) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA1 | exact HB1]).
    split; [|exact Hei1].
    apply VHTS_base. eapply VHTS_app; [exact H | exact H0 | exact HA1 | exact HB1 | exact Hpi | | exact He'1 | exact HBi1].
    apply VHTS_base. eapply VHTS_lam; [exact H | exact H0 | exact HA1 | exact HB1 | exact He1 | exact Hpi].
  - destruct IHVIsDefEqStrong1 as [HA1 _], IHVIsDefEqStrong2 as [HB1 _],
             IHVIsDefEqStrong3 as [HB_lift _], IHVIsDefEqStrong4 as [He1 _],
             IHVIsDefEqStrong5 as [He_lift _], IHVIsDefEqStrong6 as [HA_lift _].
    assert (Hpi : VHasTypeStrong env U G (VForallE A B) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA1 | exact HB1]).
    assert (Hpi_lift : VHasTypeStrong env U (A :: G)
                         (VForallE (vlift A) (vliftN 1 1 B)) (VSort (VLIMax u v)) true)
      by (apply VHTS_base; apply VHTS_forallE; [exact H | exact H0 | exact HA_lift | exact HB_lift]).
    assert (Hbv0 : VHasTypeStrong env U (A :: G) (VBVar 0) (vlift A) true)
      by (apply VHTS_base; eapply VHTS_bvar; [constructor | exact H | exact HA_lift]).
    pose proof (VHTS_app H H0 HA_lift HB_lift Hpi_lift He_lift Hbv0) as Happ.
    unfold vinst0 in Happ. rewrite vinst_vliftN_bvar0 in Happ.
    specialize (Happ HB1).
    split; [|exact He1].
    apply VHTS_base. eapply VHTS_lam; [exact H | exact H0 | exact HA1 | exact HB1 | apply VHTS_base; exact Happ | exact Hpi].
  - tauto.
  - destruct IHVIsDefEqStrong4 as [Hl _], IHVIsDefEqStrong5 as [Hr _].
    split; assumption.
Qed.

Theorem VHasTypeStrong_refl env U G e A b :
  VHasTypeStrong env U G e A b -> VIsDefEqStrong env U G e e A.
Proof.
  induction 1.
  - eapply VDFS_bvar; [exact H | exact H0 | exact IHVHasTypeStrong].
  - eapply VDFS_defeqDF with (u := VLSucc (VLSucc l)).
    + exact H.
    + apply VDFS_sortDF; [exact H | exact H0 | apply vlevel_succ_congr; exact H1].
    + apply VDFS_sortDF; [exact H | exact H | apply vlevel_equiv_refl].
  - eapply VDFS_constDF; [exact H | exact H0 | exact H0 | exact H1 | apply Forall2_vlevel_equiv_refl | exact H2 | exact IHVHasTypeStrong1 | exact IHVHasTypeStrong2].
  - eapply VDFS_appDF; [exact H | exact H0 | exact IHVHasTypeStrong1 | exact IHVHasTypeStrong2 | exact IHVHasTypeStrong4 | exact IHVHasTypeStrong5 | exact IHVHasTypeStrong6].
  - eapply VDFS_lamDF; [exact H | exact H0 | exact IHVHasTypeStrong1 | exact IHVHasTypeStrong2 | exact IHVHasTypeStrong2 | exact IHVHasTypeStrong3 | exact IHVHasTypeStrong3].
  - eapply VDFS_forallEDF; [exact H | exact H0 | exact IHVHasTypeStrong1 | exact IHVHasTypeStrong2 | exact IHVHasTypeStrong2].
  - exact IHVHasTypeStrong.
  - eapply VDFS_defeqDF; [exact H | exact H0 | exact IHVHasTypeStrong3].
Qed.

Theorem VHasTypeStrong_hasType env U G e A b :
  VHasTypeStrong env U G e A b -> VHasType env U G e A.
Proof.
  intros H. exact (VIsDefEq_refl_l (VIsDefEqStrong_defeq (VHasTypeStrong_refl H))).
Qed.

(* Syntactic Typing Inversions Modulo VIsDefEq *)

Lemma VHasTypeStrong_to_base env U G e V :
  VHasTypeStrong env U G e V true ->
  exists A, VHasTypeStrong env U G e A false.
Proof.
  remember true as b eqn:Hb.
  induction 1; try discriminate.
  - exists A. exact H.
  - exact (IHVHasTypeStrong3 eq_refl).
Qed.

Theorem VHasType_app_inv env U G f a V :
  VEnvWF env ->
  VCtxWF env U G ->
  VHasType env U G (VApp f a) V ->
  exists A B, VHasType env U G f (VForallE A B) /\ VHasType env U G a A.
Proof.
  intros Hwf HG H.
  destruct (VHasTypeStrong_to_base (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H)))) as [V0 Hbase].
  inversion Hbase; subst.
  exists A, B. split; eapply VHasTypeStrong_hasType; eassumption.
Qed.

Corollary VExprWF_app_inv env U G f a :
  VEnvWF env -> VCtxWF env U G ->
  VExprWF env U G (VApp f a) ->
  exists A B, VHasType env U G f (VForallE A B) /\ VHasType env U G a A.
Proof. intros Hwf HG [V HV]. exact (VHasType_app_inv Hwf HG HV). Qed.

Theorem VHasType_lam_inv env U G A body V :
  VEnvWF env ->
  VCtxWF env U G ->
  VHasType env U G (VLam A body) V ->
  VIsType env U G A /\ VExprWF env U (A :: G) body.
Proof.
  intros Hwf HG H.
  destruct (VHasTypeStrong_to_base (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H)))) as [V0 Hbase].
  inversion Hbase; subst.
  split; [exists u; eapply VHasTypeStrong_hasType; eassumption
         |exists B; eapply VHasTypeStrong_hasType; eassumption].
Qed.

Corollary VExprWF_lam_inv env U G A body :
  VEnvWF env -> VCtxWF env U G ->
  VExprWF env U G (VLam A body) ->
  VIsType env U G A /\ VExprWF env U (A :: G) body.
Proof. intros Hwf HG [V HV]. exact (VHasType_lam_inv Hwf HG HV). Qed.

Theorem VHasType_const_inv env U G c ls V :
  VEnvWF env ->
  VCtxWF env U G ->
  VHasType env U G (VConst c ls) V ->
  exists ci, venv_constants env c = Some ci /\
             Forall (vlevel_wf U) ls /\
             List.length ls = vc_uvars ci.
Proof.
  intros Hwf HG H.
  destruct (VHasTypeStrong_to_base (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H)))) as [V0 Hbase].
  inversion Hbase; subst.
  exists ci. auto.
Qed.

Corollary VExprWF_const_inv env U G c ls :
  VEnvWF env -> VCtxWF env U G ->
  VExprWF env U G (VConst c ls) ->
  exists ci, venv_constants env c = Some ci /\
             Forall (vlevel_wf U) ls /\
             List.length ls = vc_uvars ci.
Proof. intros Hwf HG [V HV]. exact (VHasType_const_inv Hwf HG HV). Qed.

Theorem VHasType_bvar_inv env U G i V :
  VEnvWF env ->
  VCtxWF env U G ->
  VHasType env U G (VBVar i) V ->
  exists A, VLookup G i A.
Proof.
  intros Hwf HG H.
  destruct (VHasTypeStrong_to_base (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H)))) as [V0 Hbase].
  inversion Hbase; subst.
  exists V0. assumption.
Qed.

Corollary VExprWF_bvar_inv env U G i :
  VEnvWF env -> VCtxWF env U G ->
  VExprWF env U G (VBVar i) ->
  exists A, VLookup G i A.
Proof. intros Hwf HG [V HV]. exact (VHasType_bvar_inv Hwf HG HV). Qed.

(* ========================================================================= *)
(* 7. Stratified Typing (HasTypeStratified)                                  *)
(* ========================================================================= *)

Inductive VHasTypeStratified (env : VEnv) (U : nat) :
    list VExpr -> VExpr -> VExpr -> bool -> nat -> Prop :=
| VHTSt_bvar : forall G i A u n,
    VLookup G i A ->
    VHasTypeStratified env U G A (VSort u) true n ->
    VHasTypeStratified env U G (VBVar i) A false (S n)
| VHTSt_sort' : forall G l l' n,
    vlevel_wf U l ->
    vlevel_wf U l' ->
    vlevel_equiv l l' ->
    VHasTypeStratified env U G (VSort l) (VSort (VLSucc l')) false n
| VHTSt_const : forall G c ci ls u n,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf U) ls ->
    List.length ls = vc_uvars ci ->
    VHasTypeStratified env U G (vinstL ls (vc_type ci)) (VSort u) true n ->
    VHasTypeStratified env U G (VConst c ls) (vinstL ls (vc_type ci)) false (S n)
| VHTSt_app : forall G A B f a u v n,
    vlevel_wf U u ->
    vlevel_wf U v ->
    VHasTypeStratified env U G A (VSort u) true n ->
    VHasTypeStratified env U (A :: G) B (VSort v) true n ->
    VHasTypeStratified env U G f (VForallE A B) true n ->
    VHasTypeStratified env U G a A true n ->
    VHasTypeStratified env U G (vinst0 B a) (VSort v) true n ->
    VHasTypeStratified env U G (VApp f a) (vinst0 B a) false (S n)
| VHTSt_lam : forall G A B body u v n,
    VHasTypeStratified env U G A (VSort u) true n ->
    VHasTypeStratified env U (A :: G) B (VSort v) true n ->
    VHasTypeStratified env U (A :: G) body B true n ->
    VHasTypeStratified env U G (VForallE A B) (VSort (VLIMax u v)) true n ->
    VHasTypeStratified env U G (VLam A body) (VForallE A B) false (S n)
| VHTSt_forallE : forall G A body u v n,
    vlevel_wf U u ->
    vlevel_wf U v ->
    VHasTypeStratified env U G A (VSort u) true n ->
    VHasTypeStratified env U (A :: G) body (VSort v) true n ->
    VHasTypeStratified env U G (VForallE A body) (VSort (VLIMax u v)) false (S n)
| VHTSt_base : forall G e A n,
    VHasTypeStratified env U G e A false n ->
    VHasTypeStratified env U G e A true n
| VHTSt_defeq : forall G e A B u n,
    vlevel_wf U u ->
    VIsDefEq env U G A B (VSort u) ->
    VHasTypeStratified env U G A (VSort u) true n ->
    VHasTypeStratified env U G B (VSort u) true n ->
    VHasTypeStratified env U G e A true n ->
    VHasTypeStratified env U G e B true (S n).

Theorem VHasTypeStratified_hasType env U G e A b n :
  VHasTypeStratified env U G e A b n -> VHasType env U G e A.
Proof.
  induction 1.
  - apply VDF_bvar; assumption.
  - eapply VDF_defeqDF;
      [apply (@VDF_sortDF env U G (VLSucc l) (VLSucc l')); [exact H | exact H0 | apply vlevel_succ_congr; exact H1]
      |apply VHasType_sort; exact H].
  - eapply VDF_constDF; [exact H | exact H0 | exact H0 | exact H1 | apply Forall2_vlevel_equiv_refl].
  - eapply VDF_appDF; [exact IHVHasTypeStratified3 | exact IHVHasTypeStratified4].
  - eapply VDF_lamDF; [exact IHVHasTypeStratified1 | exact IHVHasTypeStratified3].
  - eapply VDF_forallEDF; [exact IHVHasTypeStratified1 | exact IHVHasTypeStratified2].
  - exact IHVHasTypeStratified.
  - eapply VDF_defeqDF; [exact H0 | exact IHVHasTypeStratified3].
Qed.

Theorem VHasTypeStratified_mono env U G e A b m n :
  m <= n ->
  VHasTypeStratified env U G e A b m ->
  VHasTypeStratified env U G e A b n.
Proof.
  intros Hle H. revert n Hle.
  induction H; intros n' Hle;
    try (destruct n' as [|n']; [lia |]);
    try (assert (Hle' : n <= n') by lia).
  - eapply VHTSt_bvar; [eassumption | apply IHVHasTypeStratified; exact Hle'].
  - apply VHTSt_sort'; assumption.
  - eapply VHTSt_const; [eassumption | assumption | assumption | apply IHVHasTypeStratified; exact Hle'].
  - eapply VHTSt_app; [exact H | exact H0
      | apply IHVHasTypeStratified1; exact Hle'
      | apply IHVHasTypeStratified2; exact Hle'
      | apply IHVHasTypeStratified3; exact Hle'
      | apply IHVHasTypeStratified4; exact Hle'
      | apply IHVHasTypeStratified5; exact Hle'].
  - eapply VHTSt_lam;
      [ apply IHVHasTypeStratified1; exact Hle'
      | apply IHVHasTypeStratified2; exact Hle'
      | apply IHVHasTypeStratified3; exact Hle'
      | apply IHVHasTypeStratified4; exact Hle'].
  - eapply VHTSt_forallE; [exact H | exact H0
      | apply IHVHasTypeStratified1; exact Hle'
      | apply IHVHasTypeStratified2; exact Hle'].
  - apply VHTSt_base. apply IHVHasTypeStratified. exact Hle.
  - eapply VHTSt_defeq; [exact H | exact H0
      | apply IHVHasTypeStratified1; exact Hle'
      | apply IHVHasTypeStratified2; exact Hle'
      | apply IHVHasTypeStratified3; exact Hle'].
Qed.

Theorem VHasTypeStrong_stratify env U G e A b :
  VHasTypeStrong env U G e A b ->
  exists n, VHasTypeStratified env U G e A b n.
Proof.
  induction 1.
  - destruct IHVHasTypeStrong as [n Hn]. exists (S n). eapply VHTSt_bvar; eassumption.
  - exists 0. apply VHTSt_sort'; assumption.
  - destruct IHVHasTypeStrong2 as [n Hn]. exists (S n). eapply VHTSt_const; eassumption.
  - destruct IHVHasTypeStrong1 as [n1 H1'], IHVHasTypeStrong2 as [n2 H2'],
             IHVHasTypeStrong4 as [n3 H3'], IHVHasTypeStrong5 as [n4 H4'],
             IHVHasTypeStrong6 as [n5 H5'].
    set (m := Nat.max n1 (Nat.max n2 (Nat.max n3 (Nat.max n4 n5)))).
    exists (S m). eapply VHTSt_app;
      [exact H | exact H0
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n1 m ltac:(lia) H1')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n2 m ltac:(lia) H2')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n3 m ltac:(lia) H3')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n4 m ltac:(lia) H4')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n5 m ltac:(lia) H5')].
  - destruct IHVHasTypeStrong1 as [n1 H1'], IHVHasTypeStrong2 as [n2 H2'],
             IHVHasTypeStrong3 as [n3 H3'], IHVHasTypeStrong4 as [n4 H4'].
    set (m := Nat.max n1 (Nat.max n2 (Nat.max n3 n4))).
    exists (S m). eapply VHTSt_lam;
      [ apply (@VHasTypeStratified_mono _ _ _ _ _ _ n1 m ltac:(lia) H1')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n2 m ltac:(lia) H2')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n3 m ltac:(lia) H3')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n4 m ltac:(lia) H4')].
  - destruct IHVHasTypeStrong1 as [n1 H1'], IHVHasTypeStrong2 as [n2 H2'].
    set (m := Nat.max n1 n2).
    exists (S m). eapply VHTSt_forallE;
      [exact H | exact H0
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n1 m ltac:(lia) H1')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n2 m ltac:(lia) H2')].
  - destruct IHVHasTypeStrong as [n Hn]. exists n. apply VHTSt_base; exact Hn.
  - destruct IHVHasTypeStrong1 as [n1 H1'], IHVHasTypeStrong2 as [n2 H2'],
             IHVHasTypeStrong3 as [n3 H3'].
    set (m := Nat.max n1 (Nat.max n2 n3)).
    exists (S m). eapply VHTSt_defeq;
      [exact H | exact (VIsDefEqStrong_defeq H0)
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n1 m ltac:(lia) H1')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n2 m ltac:(lia) H2')
      | apply (@VHasTypeStratified_mono _ _ _ _ _ _ n3 m ltac:(lia) H3')].
Qed.

Theorem VHasTypeStratified_to_core env U G e A n :
  VHasTypeStratified env U G e A true n ->
  exists A', VHasTypeStratified env U G e A' false n.
Proof.
  remember true as b eqn:Hb.
  induction 1; try discriminate.
  - exists A. exact H.
  - destruct (IHVHasTypeStratified3 eq_refl) as [A' HA'].
    exists A'. apply (@VHasTypeStratified_mono _ _ _ _ _ _ n (S n) ltac:(lia) HA').
Qed.

Theorem VHasTypeStratified_isType env U G e A b n :
  VHasTypeStratified env U G e A b n ->
  exists u, VHasTypeStratified env U G A (VSort u) true (n - 1).
Proof.
  induction 1.
  - exists u. replace (S n - 1) with n by lia. exact H0.
  - exists (VLSucc (VLSucc l')). apply VHTSt_base. apply VHTSt_sort'; [exact H0 | exact H0 | apply vlevel_equiv_refl].
  - exists u. replace (S n - 1) with n by lia. exact H2.
  - exists v. replace (S n - 1) with n by lia. exact H5.
  - exists (VLIMax u v). replace (S n - 1) with n by lia. exact H2.
  - exists (VLSucc (VLIMax u v)). apply VHTSt_base. apply VHTSt_sort'; [simpl; auto | simpl; auto | apply vlevel_equiv_refl].
  - exact IHVHasTypeStratified.
  - exists u. replace (S n - 1) with n by lia. exact H2.
Qed.

(* ========================================================================= *)
(* 8. Simultaneous Definitional-Equality Substitution (substEq' / substDF)   *)
(* ========================================================================= *)

Theorem VIsDefEqStrong_substEq' env U Gamma Delta s1 s2 e1 e2 A :
  VEnvWF env ->
  VCtxStrong env U Gamma ->
  VCtxStrong env U Delta ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VIsDefEqStrong env U Gamma e1 e2 A ->
  VIsDefEqStrong env U Delta (vsubst s1 e1) (vsubst s2 e1) (vsubst s1 A) /\
  VIsDefEqStrong env U Delta (vsubst s1 e2) (vsubst s2 e2) (vsubst s1 A) /\
  VIsDefEqStrong env U Delta (vsubst s1 e1) (vsubst s2 e2) (vsubst s1 A).
Proof.
  intros Hwf HG HDelta W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert HG Delta s1 s2 HDelta W.
  induction H; intros HG Delta s1 s2 HDelta W; simpl.
  - (* bvar *)
    pose proof (VIsDefEq_strong Hwf (VCtxStrong_defeq HDelta) (VCtxSubstEq_lookup W H)) as Hs.
    repeat split; exact Hs.
  - (* symm *)
    destruct (IHVIsDefEqStrong HG Delta s1 s2 HDelta W) as [Hl [Hr Hc]].
    repeat split; [exact Hr | exact Hl |].
    eapply VDFS_trans; [eapply VDFS_trans; [exact Hr | exact (VDFS_symm Hc)] | exact Hl].
  - (* trans *)
    destruct (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W) as [Hl1 [_ Hc1]].
    destruct (IHVIsDefEqStrong2 HG Delta s1 s2 HDelta W) as [Hl2 [Hr2 Hc2]].
    repeat split; [exact Hl1 | exact Hr2 |].
    eapply VDFS_trans; [exact Hc1 | eapply VDFS_trans; [exact (VDFS_symm Hl2) | exact Hc2]].
  - (* sortDF *)
    pose proof (@VDFS_sortDF env U Delta _ _ H H0 H1) as HC.
    repeat split; [exact (VIsDefEqStrong_refl_l HC) | exact (VIsDefEqStrong_refl_r HC) | exact HC].
  - (* constDF *)
    rewrite (vclosed_vsubst_eq s1 (closed_inst_const ls 0 Hcl H)).
    pose proof (VDFS_constDF H H0 H1 H2 H3 H4 H5 (@VIsDefEqStrong_weak0 env U Delta _ _ _ Hcl H5)) as HC.
    repeat split; [exact (VIsDefEqStrong_refl_l HC) | exact (VIsDefEqStrong_refl_r HC) | exact HC].
  - (* appDF *)
    rewrite vsubst_vinst.
    pose proof (proj1 (IHVIsDefEqStrong1 HG Delta s1 s1 HDelta (VCtxSubstEq_left W))) as HA'.
    assert (HDelta_A : VCtxStrong env U (vsubst s1 A :: Delta))
      by (split; [exact HDelta | exists u; exact HA']).
    assert (HG_A : VCtxStrong env U (A :: G))
      by (split; [exact HG | exists u; exact H1]).
    pose proof (VCtxSubstEq_lift Hcl (VCtxSubstEq_left W) (VIsDefEqStrong_defeq H1)) as W_A.
    pose proof (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HDelta_A W_A)) as HB'.
    simpl in HB'.
    destruct (IHVIsDefEqStrong3 HG Delta s1 s2 HDelta W) as [ihf_l [ihf_r ihf_c]].
    destruct (IHVIsDefEqStrong4 HG Delta s1 s2 HDelta W) as [iha_l [iha_r iha_c]].
    destruct (IHVIsDefEqStrong4 HG Delta s1 s1 HDelta (VCtxSubstEq_left W)) as [_ [_ iha_cleft]].
    assert (ih2_cons : forall x y,
      VIsDefEqStrong env U Delta x y (vsubst s1 A) ->
      VIsDefEqStrong env U Delta
        (vinst0 (vsubst (vsubst_lift s1) B) x)
        (vinst0 (vsubst (vsubst_lift s1) B) y) (VSort v)).
    { intros x y Hxy.
      pose proof (VCtxSubstEq_cons_explicit (VCtxSubstEq_left W)
                    (VIsDefEqStrong_defeq H1) (VIsDefEqStrong_defeq Hxy)) as W_cons.
      pose proof (proj1 (IHVIsDefEqStrong2 HG_A Delta _ _ HDelta W_cons)) as Hinst.
      simpl in Hinst. rewrite <- !vinst_vlift_cons in Hinst. exact Hinst. }
    repeat split.
    + eapply VDFS_appDF; [exact H | exact H0 | exact HA' | exact HB' | exact ihf_l | exact iha_l | exact (ih2_cons _ _ iha_l)].
    + eapply VDFS_defeqDF; [exact H0 | exact (ih2_cons _ _ (VDFS_symm iha_cleft)) |].
      eapply VDFS_appDF; [exact H | exact H0 | exact HA' | exact HB' | exact ihf_r | exact iha_r | exact (ih2_cons _ _ iha_r)].
    + eapply VDFS_appDF; [exact H | exact H0 | exact HA' | exact HB' | exact ihf_c | exact iha_c | exact (ih2_cons _ _ iha_c)].
  - (* lamDF *)
    destruct (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W) as [ihA_l [ihA_r ihA_c]].
    pose proof (VIsDefEqStrong_refl_l H1) as hA_G.
    pose proof (VIsDefEqStrong_refl_r H1) as hA'_G.
    pose proof (VIsDefEqStrong_refl_l ihA_l) as hA_s1.
    pose proof (VIsDefEqStrong_refl_r ihA_l) as hA_s2.
    pose proof (VIsDefEqStrong_refl_l ihA_r) as hA'_s1.
    pose proof (VIsDefEqStrong_refl_r ihA_r) as hA'_s2.
    assert (HD_As1 : VCtxStrong env U (vsubst s1 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s1]).
    assert (HD_As2 : VCtxStrong env U (vsubst s2 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s2]).
    assert (HD_A's1 : VCtxStrong env U (vsubst s1 A' :: Delta)) by (split; [exact HDelta | exists u; exact hA'_s1]).
    assert (HD_A's2 : VCtxStrong env U (vsubst s2 A' :: Delta)) by (split; [exact HDelta | exists u; exact hA'_s2]).
    assert (HG_A : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact hA_G]).
    assert (HG_A' : VCtxStrong env U (A' :: G)) by (split; [exact HG | exists u; exact hA'_G]).
    pose proof (proj2 (proj2 (IHVIsDefEqStrong1 HG Delta s1 s1 HDelta (VCtxSubstEq_left W)))) as hAA'_s1.
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq hA_G)) as W_A.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA_G) (VIsDefEqStrong_defeq ihA_l)) as W_As2.
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq hA'_G)) as W_A'.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA'_G) (VIsDefEqStrong_defeq ihA_r)) as W_A's2.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA_G) (VIsDefEqStrong_defeq ihA_c)) as W_A_A's2.
    pose proof (VCtxSubstEq_lift_at Hcl (VCtxSubstEq_left W) (VIsDefEqStrong_defeq hA_G) (VIsDefEqStrong_defeq hAA'_s1)) as W_left_A's1.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A))) as B_As1.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As2 W_As2))) as B_As2.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_A's1 W_left_A's1))) as B_A's1.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_A's2 W_A_A's2))) as B_A's2.
    pose proof (proj1 (IHVIsDefEqStrong4 HG_A _ _ _ HD_As1 W_A)) as body_As1.
    pose proof (proj1 (IHVIsDefEqStrong4 HG_A _ _ _ HD_As2 W_As2)) as body_As2.
    pose proof (proj2 (proj2 (IHVIsDefEqStrong4 HG_A _ _ _ HD_As1 W_A))) as body_cross_As1.
    pose proof (proj2 (proj2 (IHVIsDefEqStrong4 HG_A _ _ _ HD_A's2 W_A_A's2))) as body_cross_A's2.
    pose proof (proj1 (proj2 (IHVIsDefEqStrong5 HG_A' _ _ _ HD_A's1 W_A'))) as body'_A's1.
    pose proof (proj1 (proj2 (IHVIsDefEqStrong5 HG_A' _ _ _ HD_A's2 W_A's2))) as body'_A's2.
    repeat split.
    + eapply VDFS_lamDF; [exact H | exact H0 | exact ihA_l | exact B_As1 | exact B_As2 | exact body_As1 | exact body_As2].
    + eapply (VDFS_defeqDF (u := VLIMax u v)).
      * simpl; split; [exact H | exact H0].
      * eapply VDFS_forallEDF; [exact H | exact H0 | exact (VDFS_symm hAA'_s1) | exact B_A's1 | exact B_As1].
      * eapply VDFS_lamDF; [exact H | exact H0 | exact ihA_r | exact B_A's1 | exact B_A's2 | exact body'_A's1 | exact body'_A's2].
    + eapply VDFS_lamDF; [exact H | exact H0 | exact ihA_c | exact B_As1 | exact B_A's2 | exact body_cross_As1 | exact body_cross_A's2].
  - (* forallEDF *)
    destruct (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W) as [ihA_l [ihA_r ihA_c]].
    pose proof (VIsDefEqStrong_refl_l H1) as hA_G.
    pose proof (VIsDefEqStrong_refl_r H1) as hA'_G.
    pose proof (VIsDefEqStrong_refl_l ihA_l) as hA_s1.
    pose proof (VIsDefEqStrong_refl_r ihA_l) as hA_s2.
    pose proof (VIsDefEqStrong_refl_l ihA_r) as hA'_s1.
    pose proof (VIsDefEqStrong_refl_r ihA_r) as hA'_s2.
    assert (HD_As1 : VCtxStrong env U (vsubst s1 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s1]).
    assert (HD_As2 : VCtxStrong env U (vsubst s2 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s2]).
    assert (HD_A's1 : VCtxStrong env U (vsubst s1 A' :: Delta)) by (split; [exact HDelta | exists u; exact hA'_s1]).
    assert (HD_A's2 : VCtxStrong env U (vsubst s2 A' :: Delta)) by (split; [exact HDelta | exists u; exact hA'_s2]).
    assert (HG_A : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact hA_G]).
    assert (HG_A' : VCtxStrong env U (A' :: G)) by (split; [exact HG | exists u; exact hA'_G]).
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq hA_G)) as W_A.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA_G) (VIsDefEqStrong_defeq ihA_l)) as W_As2.
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq hA'_G)) as W_A'.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA'_G) (VIsDefEqStrong_defeq ihA_r)) as W_A's2.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq hA_G) (VIsDefEqStrong_defeq ihA_c)) as W_A_A's2.
    pose proof (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A)) as body_As1.
    pose proof (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As2 W_As2)) as body_As2.
    pose proof (proj2 (proj2 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A))) as body_cross_As1.
    pose proof (proj2 (proj2 (IHVIsDefEqStrong2 HG_A _ _ _ HD_A's2 W_A_A's2))) as body_cross_A's2.
    pose proof (proj1 (proj2 (IHVIsDefEqStrong3 HG_A' _ _ _ HD_A's1 W_A'))) as body'_A's1.
    pose proof (proj1 (proj2 (IHVIsDefEqStrong3 HG_A' _ _ _ HD_A's2 W_A's2))) as body'_A's2.
    repeat split.
    + eapply VDFS_forallEDF; [exact H | exact H0 | exact ihA_l | exact body_As1 | exact body_As2].
    + eapply VDFS_forallEDF; [exact H | exact H0 | exact ihA_r | exact body'_A's1 | exact body'_A's2].
    + eapply VDFS_forallEDF; [exact H | exact H0 | exact ihA_c | exact body_cross_As1 | exact body_cross_A's2].
  - (* defeqDF *)
    pose proof (proj2 (proj2 (IHVIsDefEqStrong1 HG Delta s1 s1 HDelta (VCtxSubstEq_left W)))) as hty.
    destruct (IHVIsDefEqStrong2 HG Delta s1 s2 HDelta W) as [l2 [r2 c2]].
    repeat split; eapply VDFS_defeqDF; [exact H | exact hty | exact l2 | exact H | exact hty | exact r2 | exact H | exact hty | exact c2].
  - (* beta *)
    pose proof (proj1 (IHVIsDefEqStrong1 HG Delta s1 s1 HDelta (VCtxSubstEq_left W))) as hA's1.
    assert (HG_A : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact H1]).
    assert (HD_As1 : VCtxStrong env U (vsubst s1 A :: Delta)) by (split; [exact HDelta | exists u; exact hA's1]).
    pose proof (proj1 (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W)) as iha_l.
    assert (HD_As2 : VCtxStrong env U (vsubst s2 A :: Delta))
      by (split; [exact HDelta | exists u; exact (VIsDefEqStrong_refl_r iha_l)]).
    pose proof (VCtxSubstEq_lift Hcl (VCtxSubstEq_left W) (VIsDefEqStrong_defeq H1)) as W_A_left.
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq H1)) as W_A.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq H1) (VIsDefEqStrong_defeq iha_l)) as W_As2.
    pose proof (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A_left)) as hBs1.
    pose proof (proj1 (IHVIsDefEqStrong3 HG_A _ _ _ HD_As1 W_A_left)) as hes1.
    pose proof (proj1 (IHVIsDefEqStrong4 HG Delta s1 s1 HDelta (VCtxSubstEq_left W))) as he's1.
    assert (ih2_cons : forall x y,
      VIsDefEqStrong env U Delta x y (vsubst s1 A) ->
      VIsDefEqStrong env U Delta
        (vinst0 (vsubst (vsubst_lift s1) B) x)
        (vinst0 (vsubst (vsubst_lift s1) B) y) (VSort v)).
    { intros x y Hxy.
      pose proof (VCtxSubstEq_cons_explicit (VCtxSubstEq_left W)
                    (VIsDefEqStrong_defeq H1) (VIsDefEqStrong_defeq Hxy)) as W_cons.
      pose proof (proj1 (IHVIsDefEqStrong2 HG_A Delta _ _ HDelta W_cons)) as Hinst.
      simpl in Hinst. rewrite <- !vinst_vlift_cons in Hinst. exact Hinst. }
    pose proof (proj1 (IHVIsDefEqStrong6 HG Delta s1 s1 HDelta (VCtxSubstEq_left W))) as heinst_left.
    rewrite !vsubst_vinst in heinst_left.
    assert (H_s1 : VIsDefEqStrong env U Delta
      (VApp (VLam (vsubst s1 A) (vsubst (vsubst_lift s1) e)) (vsubst s1 e'))
      (vsubst s1 (vinst0 e e')) (vsubst s1 (vinst0 B e'))).
    { rewrite !vsubst_vinst.
      eapply VDFS_beta;
        [exact H | exact H0 | exact hA's1 | exact hBs1 | exact hes1 | exact he's1
        | exact (ih2_cons _ _ he's1) | exact heinst_left]. }
    pose proof (proj1 (IHVIsDefEqStrong6 HG Delta s1 s2 HDelta W)) as HR.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A))) as B_As1.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As2 W_As2))) as B_As2.
    pose proof (proj1 (IHVIsDefEqStrong3 HG_A _ _ _ HD_As1 W_A)) as e_As1.
    pose proof (proj1 (IHVIsDefEqStrong3 HG_A _ _ _ HD_As2 W_As2)) as e_As2.
    pose proof (proj1 (IHVIsDefEqStrong4 HG Delta s1 s2 HDelta W)) as ihe'_l.
    assert (HL : VIsDefEqStrong env U Delta
      (VApp (VLam (vsubst s1 A) (vsubst (vsubst_lift s1) e)) (vsubst s1 e'))
      (VApp (VLam (vsubst s2 A) (vsubst (vsubst_lift s2) e)) (vsubst s2 e'))
      (vsubst s1 (vinst0 B e'))).
    { rewrite vsubst_vinst.
      eapply VDFS_appDF;
        [exact H | exact H0 | exact hA's1 | exact hBs1
        | eapply VDFS_lamDF; [exact H | exact H0 | exact iha_l | exact B_As1 | exact B_As2 | exact e_As1 | exact e_As2]
        | exact ihe'_l | exact (ih2_cons _ _ ihe'_l)]. }
    repeat split; [exact HL | exact HR | exact (VDFS_trans H_s1 HR)].
  - (* eta *)
    rewrite !vlift_vsubst_lift.
    assert (HG_A : VCtxStrong env U (A :: G)) by (split; [exact HG | exists u; exact H1]).
    pose proof (proj1 (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W)) as iha_l.
    pose proof (VIsDefEqStrong_refl_l iha_l) as hA_s1.
    pose proof (VIsDefEqStrong_refl_r iha_l) as hA_s2.
    assert (HD_As1 : VCtxStrong env U (vsubst s1 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s1]).
    assert (HD_As2 : VCtxStrong env U (vsubst s2 A :: Delta)) by (split; [exact HDelta | exists u; exact hA_s2]).
    pose proof (VCtxSubstEq_lift Hcl (VCtxSubstEq_left W) (VIsDefEqStrong_defeq H1)) as W_A_s1.
    pose proof (VCtxSubstEq_lift Hcl W (VIsDefEqStrong_defeq H1)) as W_A_cross.
    pose proof (VCtxSubstEq_lift_at Hcl W (VIsDefEqStrong_defeq H1) (VIsDefEqStrong_defeq iha_l)) as W_A_s2.
    pose proof (VIsDefEqStrong_refl_l (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A_s1))) as hB_s1.
    pose proof (proj1 (IHVIsDefEqStrong4 HG Delta s1 s2 HDelta W)) as HR.
    simpl in HR.
    pose proof (VIsDefEqStrong_refl_l HR) as he_s1.
    assert (H_s1 : VIsDefEqStrong env U Delta
      (VLam (vsubst s1 A) (VApp (vlift (vsubst s1 e)) (VBVar 0)))
      (vsubst s1 e) (VForallE (vsubst s1 A) (vsubst (vsubst_lift s1) B))).
    { eapply VDFS_eta;
        [exact H | exact H0 | exact hA_s1 | exact hB_s1
        | exact (VIsDefEqStrong_weakN Hcl hB_s1 (VCtxLiftN_succ _ (VCtxLiftN_one _ _)))
        | exact he_s1
        | exact (VIsDefEqStrong_weakN Hcl he_s1 (VCtxLiftN_one _ _))
        | exact (VIsDefEqStrong_weakN Hcl hA_s1 (VCtxLiftN_one _ _))]. }
    pose proof (proj2 (proj2 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As1 W_A_cross))) as hB_cross_As1.
    pose proof (proj2 (proj2 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As2 W_A_s2))) as hB_cross_As2.
    pose proof (VIsDefEqStrong_refl_r (proj1 (IHVIsDefEqStrong2 HG_A _ _ _ HD_As2 W_A_s2))) as hB_s2.
    pose proof (VDFS_forallEDF H H0 iha_l hB_cross_As1 hB_cross_As2) as hTeq.
    pose proof (VDFS_defeqDF (u := VLIMax u v) (conj H H0) hTeq (VIsDefEqStrong_refl_r HR)) as he_s2.
    assert (H_s2 : VIsDefEqStrong env U Delta
      (VLam (vsubst s2 A) (VApp (vlift (vsubst s2 e)) (VBVar 0)))
      (vsubst s2 e) (VForallE (vsubst s2 A) (vsubst (vsubst_lift s2) B))).
    { eapply VDFS_eta;
        [exact H | exact H0 | exact hA_s2 | exact hB_s2
        | exact (VIsDefEqStrong_weakN Hcl hB_s2 (VCtxLiftN_succ _ (VCtxLiftN_one _ _)))
        | exact he_s2
        | exact (VIsDefEqStrong_weakN Hcl he_s2 (VCtxLiftN_one _ _))
        | exact (VIsDefEqStrong_weakN Hcl hA_s2 (VCtxLiftN_one _ _))]. }
    repeat split.
    + eapply VDFS_trans; [exact H_s1 |].
      eapply VDFS_trans; [exact HR |].
      exact (VDFS_defeqDF (u := VLIMax u v) (conj H H0) (VDFS_symm hTeq) (VDFS_symm H_s2)).
    + exact HR.
    + exact (VDFS_trans H_s1 HR).
  - (* proofIrrel *)
    pose proof (proj1 (IHVIsDefEqStrong1 HG Delta s1 s2 HDelta W)) as ihp.
    pose proof (proj1 (IHVIsDefEqStrong2 HG Delta s1 s2 HDelta W)) as ihh.
    pose proof (proj1 (IHVIsDefEqStrong3 HG Delta s1 s2 HDelta W)) as ihh'.
    repeat split; [exact ihh | exact ihh' |].
    eapply VDFS_proofIrrel;
      [exact (VIsDefEqStrong_refl_l ihp)
      |exact (VIsDefEqStrong_refl_l ihh)
      |exact (VIsDefEqStrong_refl_r ihh')].
  - (* extra *)
    destruct (closed_inst_defeq ls 0 Hcl H) as [Hl [Hr Ht]].
    rewrite !(vclosed_vsubst_eq s1 Hl), !(vclosed_vsubst_eq s2 Hl),
            !(vclosed_vsubst_eq s1 Hr), !(vclosed_vsubst_eq s2 Hr),
            !(vclosed_vsubst_eq s1 Ht).
    pose proof (VDFS_extra H H0 H1 H2 H3 H4 H5
                  (@VIsDefEqStrong_weak0 env U Delta _ _ _ Hcl H4)
                  (@VIsDefEqStrong_weak0 env U Delta _ _ _ Hcl H5)) as HC.
    repeat split; [exact (VIsDefEqStrong_refl_l HC) | exact (VIsDefEqStrong_refl_r HC) | exact HC].
Qed.

Theorem VIsDefEqStrong_subst env U Gamma Delta s1 s2 e1 e2 A :
  VEnvWF env ->
  VCtxStrong env U Gamma ->
  VCtxStrong env U Delta ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VIsDefEqStrong env U Gamma e1 e2 A ->
  VIsDefEqStrong env U Delta (vsubst s1 e1) (vsubst s2 e2) (vsubst s1 A).
Proof.
  intros Hwf HG HDelta W H.
  exact (proj2 (proj2 (VIsDefEqStrong_substEq' Hwf HG HDelta W H))).
Qed.

Theorem VIsDefEq_substDF env U Delta s1 s2 Gamma e1 e2 A :
  VEnvWF env ->
  VCtxWF env U Delta ->
  VCtxSubstEq env U Delta s1 s2 Gamma ->
  VIsDefEq env U Gamma e1 e2 A ->
  VIsDefEq env U Delta (vsubst s1 e1) (vsubst s2 e2) (vsubst s1 A).
Proof.
  intros Hwf HDelta W H.
  pose proof (VCtxSubstEq_wf W) as HGamma.
  apply VIsDefEqStrong_defeq.
  exact (VIsDefEqStrong_subst Hwf (VCtxStrong_strong Hwf HGamma)
          (VCtxStrong_strong Hwf HDelta) W (VIsDefEq_strong Hwf HGamma H)).
Qed.

Corollary VIsDefEq_subst env U Delta s Gamma e1 e2 A :
  VEnvWF env ->
  VCtxWF env U Delta ->
  VCtxSubstEq env U Delta s s Gamma ->
  VIsDefEq env U Gamma e1 e2 A ->
  VIsDefEq env U Delta (vsubst s e1) (vsubst s e2) (vsubst s A).
Proof. apply VIsDefEq_substDF. Qed.

Corollary VHasType_subst env U Delta s Gamma e A :
  VEnvWF env ->
  VCtxWF env U Delta ->
  VCtxSubstEq env U Delta s s Gamma ->
  VHasType env U Gamma e A ->
  VHasType env U Delta (vsubst s e) (vsubst s A).
Proof. apply VIsDefEq_substDF. Qed.

Corollary VIsDefEqU_subst env U Delta s Gamma e1 e2 :
  VEnvWF env ->
  VCtxWF env U Delta ->
  VCtxSubstEq env U Delta s s Gamma ->
  VIsDefEqU env U Gamma e1 e2 ->
  VIsDefEqU env U Delta (vsubst s e1) (vsubst s e2).
Proof.
  intros Hwf HDelta W [A HA].
  exists (vsubst s A). exact (VIsDefEq_substDF Hwf HDelta W HA).
Qed.

Corollary VIsType_subst env U Delta s Gamma A :
  VEnvWF env ->
  VCtxWF env U Delta ->
  VCtxSubstEq env U Delta s s Gamma ->
  VIsType env U Gamma A ->
  VIsType env U Delta (vsubst s A).
Proof.
  intros Hwf HDelta W [u Hu].
  exists u. exact (VIsDefEq_substDF Hwf HDelta W Hu).
Qed.

(* ========================================================================= *)
(* Axiom Audit                                                               *)
(* ========================================================================= *)

Print Assumptions VIsDefEqStrong_weakN.
Print Assumptions VIsDefEqStrong_instL.
Print Assumptions VIsDefEqStrong_instN.
Print Assumptions VIsDefEqStrong_defeqDF_l.
Print Assumptions VIsDefEqStrong_forallE_inv'.
Print Assumptions VIsDefEqStrong_isType'.
Print Assumptions VIsDefEqStrong_instDF.
Print Assumptions VEnvWF_strong.
Print Assumptions VCtxStrong_strong.
Print Assumptions VIsDefEq_strong.
Print Assumptions VIsDefEq_eqUpToLevels.
Print Assumptions VHasType_app_inv.
Print Assumptions VHasType_lam_inv.
Print Assumptions VHasType_const_inv.
Print Assumptions VHasType_bvar_inv.
Print Assumptions VHasTypeStrong_stratify.
Print Assumptions VIsDefEqStrong_substEq'.
Print Assumptions VIsDefEq_substDF.
Print Assumptions VHasType_subst.
