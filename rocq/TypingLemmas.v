(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/Typing/Lemmas.lean (upstream pin 8223d22).

   Every result here is unconditional and axiom-free.  It closes the gap
   between the bare 13-rule judgment of DeclarativeTyping.v and a usable
   metatheory:

   - universe instantiation           IsDefEq.instL       -> VIsDefEq_instL
   - scope / closedness               IsDefEq.closedN'    -> VIsDefEq_closedN
   - universe well-formedness         IsDefEq.levelWF     -> VIsDefEq_levelWF
   - environment invariants           Ordered.constWF/... -> VEnvWF_const_wf/...
   - weakening from the empty context IsDefEq.weak0       -> VIsDefEq_weak0
   - substitution                     IsDefEq.instN       -> VIsDefEq_instN
   - constant / extra at parameters   HasType.const0, IsDefEq.extra0

   Upstream assumes `env.Ordered` where we assume the weaker `VEnvClosed`
   (Ordered implies closedness; see VEnvWF_closed below). *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel
  DeclarativeTyping.
Import ListNotations.
Set Implicit Arguments.
(* Infer implicit arguments from flexible positions too (e.g. under VHasType). *)
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Universe-level instantiation algebra (VLevel.lean)                     *)
(* ========================================================================= *)

(* `inst` of an out-of-range parameter is `zero`, which is well-formed, so the
   premise `l.WF ls.length` of SemanticModel.vlevel_inst_wf is unnecessary. *)
Lemma vlevel_inst_wf_any U ks u :
  Forall (vlevel_wf U) ks -> vlevel_wf U (vlevel_inst ks u).
Proof.
  intros Hks.
  induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl; try split; auto.
  destruct (nth_in_or_default i ks VLZero) as [Hin | Hdef].
  - rewrite Forall_forall in Hks. apply Hks. exact Hin.
  - rewrite Hdef. exact I.
Qed.

Lemma Forall_vlevel_inst_wf U ks us :
  Forall (vlevel_wf U) ks -> Forall (vlevel_wf U) (map (vlevel_inst ks) us).
Proof.
  intros Hks. induction us as [|u us IH]; simpl; constructor; auto.
  apply vlevel_inst_wf_any. exact Hks.
Qed.

Lemma vlevel_inst_inst ks1 ks2 u :
  vlevel_inst ks2 (vlevel_inst ks1 u) = vlevel_inst (map (vlevel_inst ks2) ks1) u.
Proof.
  induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl; try congruence.
  revert ks1. induction i as [|i IH]; intros [|k ks1]; simpl; auto.
Qed.

Lemma vlevel_inst_equiv ks u v :
  vlevel_equiv u v -> vlevel_equiv (vlevel_inst ks u) (vlevel_inst ks v).
Proof.
  intros Huv ls. rewrite !vlevel_inst_eval. apply Huv.
Qed.

Lemma Forall2_vlevel_inst_equiv ks us vs :
  Forall2 vlevel_equiv us vs ->
  Forall2 vlevel_equiv (map (vlevel_inst ks) us) (map (vlevel_inst ks) vs).
Proof.
  induction 1; simpl; constructor; auto. apply vlevel_inst_equiv. assumption.
Qed.

Lemma Forall2_vlevel_equiv_refl us : Forall2 vlevel_equiv us us.
Proof. induction us; constructor; auto. apply vlevel_equiv_refl. Qed.

(* The identity instantiation `[param 0, ..., param (U-1)]` (VLevel.params). *)
Definition vlevel_params (U : nat) : list VLevel := map VLParam (seq 0 U).

Lemma vlevel_params_length U : List.length (vlevel_params U) = U.
Proof. unfold vlevel_params. rewrite length_map, length_seq. reflexivity. Qed.

Lemma vlevel_params_wf U : Forall (vlevel_wf U) (vlevel_params U).
Proof.
  unfold vlevel_params. apply Forall_forall. intros u Hin.
  apply in_map_iff in Hin as [i [Hi Hin]]. subst u.
  apply in_seq in Hin. simpl. lia.
Qed.

Lemma vlevel_inst_params U u :
  vlevel_wf U u -> vlevel_inst (vlevel_params U) u = u.
Proof.
  induction u as [|v IHv|a IHa b IHb|a IHa b IHb|i]; simpl; intros Hwf.
  - reflexivity.
  - rewrite IHv by exact Hwf. reflexivity.
  - destruct Hwf. rewrite IHa, IHb by assumption. reflexivity.
  - destruct Hwf. rewrite IHa, IHb by assumption. reflexivity.
  - unfold vlevel_params.
    rewrite nth_indep with (d' := VLParam 0) by (rewrite length_map, length_seq; exact Hwf).
    rewrite map_nth, seq_nth by exact Hwf. reflexivity.
Qed.

(* ========================================================================= *)
(* 2. Expression-level universe instantiation algebra (VExpr.lean)           *)
(* ========================================================================= *)

Lemma vinstL_vinstL ks1 ks2 e :
  vinstL ks2 (vinstL ks1 e) = vinstL (map (vlevel_inst ks2) ks1) e.
Proof.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB]; simpl; try congruence.
  - rewrite vlevel_inst_inst. reflexivity.
  - rewrite map_map. f_equal. apply map_ext. intros u. apply vlevel_inst_inst.
Qed.

Lemma vlevelWF_vinstL_any U ks e :
  Forall (vlevel_wf U) ks -> vlevelWF U (vinstL ks e).
Proof.
  intros Hks.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB]; simpl; auto.
  - apply vlevel_inst_wf_any. exact Hks.
  - apply Forall_vlevel_inst_wf. exact Hks.
Qed.

Lemma vinstL_params U e :
  vlevelWF U e -> vinstL (vlevel_params U) e = e.
Proof.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB]; simpl; intros Hwf.
  - reflexivity.
  - rewrite vlevel_inst_params by exact Hwf. reflexivity.
  - f_equal. induction Hwf as [|u us Hu Hus IH]; simpl; [reflexivity|].
    rewrite vlevel_inst_params by exact Hu. f_equal. exact IH.
  - destruct Hwf. rewrite IHf, IHa by assumption. reflexivity.
  - destruct Hwf. rewrite IHA, IHb by assumption. reflexivity.
  - destruct Hwf. rewrite IHA, IHB by assumption. reflexivity.
Qed.

Lemma VLookup_instL ls G i A :
  VLookup G i A -> VLookup (map (vinstL ls) G) i (vinstL ls A).
Proof.
  induction 1; simpl; unfold vlift; rewrite vinstL_vliftN; constructor; assumption.
Qed.

(* ========================================================================= *)
(* 3. Universe instantiation of derivations (IsDefEq.instL)                  *)
(* ========================================================================= *)

Theorem VIsDefEq_instL env U U' ls G e1 e2 A :
  Forall (vlevel_wf U') ls ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U' (map (vinstL ls) G) (vinstL ls e1) (vinstL ls e2) (vinstL ls A).
Proof.
  intros Hls H. induction H.
  - apply VDF_bvar. apply VLookup_instL. assumption.
  - apply VDF_symm. assumption.
  - eapply VDF_trans; eassumption.
  - apply VDF_sortDF.
    + apply vlevel_inst_wf_any. exact Hls.
    + apply vlevel_inst_wf_any. exact Hls.
    + apply vlevel_inst_equiv. assumption.
  - simpl. rewrite vinstL_vinstL. eapply VDF_constDF.
    + eassumption.
    + apply Forall_vlevel_inst_wf. exact Hls.
    + apply Forall_vlevel_inst_wf. exact Hls.
    + rewrite length_map. assumption.
    + apply Forall2_vlevel_inst_equiv. assumption.
  - unfold vinst0. rewrite vinstL_vinst. eapply VDF_appDF; eassumption.
  - eapply VDF_lamDF; eassumption.
  - eapply VDF_forallEDF; eassumption.
  - eapply VDF_defeqDF; eassumption.
  - unfold vinst0. rewrite !vinstL_vinst. eapply VDF_beta; eassumption.
  - simpl. unfold vlift. rewrite vinstL_vliftN. apply VDF_eta. assumption.
  - eapply VDF_proofIrrel; eassumption.
  - rewrite !vinstL_vinstL. eapply VDF_extra.
    + eassumption.
    + apply Forall_vlevel_inst_wf. exact Hls.
    + rewrite length_map. assumption.
Qed.

Corollary VHasType_instL env U U' ls G e A :
  Forall (vlevel_wf U') ls ->
  VHasType env U G e A ->
  VHasType env U' (map (vinstL ls) G) (vinstL ls e) (vinstL ls A).
Proof. apply VIsDefEq_instL. Qed.

Corollary VIsType_instL env U U' ls G A :
  Forall (vlevel_wf U') ls ->
  VIsType env U G A ->
  VIsType env U' (map (vinstL ls) G) (vinstL ls A).
Proof.
  intros Hls [u Hu]. exists (vlevel_inst ls u).
  exact (VIsDefEq_instL Hls Hu).
Qed.

Corollary VIsDefEqU_instL env U U' ls G e1 e2 :
  Forall (vlevel_wf U') ls ->
  VIsDefEqU env U G e1 e2 ->
  VIsDefEqU env U' (map (vinstL ls) G) (vinstL ls e1) (vinstL ls e2).
Proof.
  intros Hls [A HA]. exists (vinstL ls A). exact (VIsDefEq_instL Hls HA).
Qed.

(* ========================================================================= *)
(* 4. Closedness of derivations (IsDefEq.closedN')                           *)
(* ========================================================================= *)

(* CtxClosed: every context entry is closed in the suffix below it. *)
Fixpoint VCtxClosed (G : list VExpr) : Prop :=
  match G with
  | [] => True
  | A :: G' => VCtxClosed G' /\ vclosedN (List.length G') A
  end.

Lemma VLookup_closed G i A :
  VLookup G i A -> VCtxClosed G -> vclosedN (List.length G) A.
Proof.
  induction 1 as [A G | A G i B Hlk IH]; simpl; intros [HG HA]; unfold vlift.
  - exact (@vliftN_preserves_vclosedN A 1 0 (List.length G) (le_0_n _) HA).
  - exact (@vliftN_preserves_vclosedN B 1 0 (List.length G) (le_0_n _) (IH HG)).
Qed.

Lemma vclosedN_vinst_eq e : forall v k, vclosedN k e -> vinst e v k = e.
Proof.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB];
    intros v k Hc; simpl in *; try reflexivity.
  - unfold vinstVar.
    assert (Hlt : (i <? k) = true) by (apply Nat.ltb_lt; exact Hc).
    rewrite Hlt. reflexivity.
  - destruct Hc. rewrite IHf, IHa by assumption. reflexivity.
  - destruct Hc. rewrite IHA, IHb by assumption. reflexivity.
  - destruct Hc. rewrite IHA, IHB by assumption. reflexivity.
Qed.

Lemma vinst0_preserves_vclosedN e v d :
  vclosedN (S d) e -> vclosedN d v -> vclosedN d (vinst0 e v).
Proof.
  intros He Hv. unfold vinst0.
  apply (@vinst_preserves_vclosedN e v 0 d (le_0_n _) He).
  rewrite Nat.sub_0_r. exact Hv.
Qed.

Lemma closed_inst_const env c ci ls k :
  VEnvClosed env -> venv_constants env c = Some ci ->
  vclosedN k (vinstL ls (vc_type ci)).
Proof.
  intros Hcl Hc.
  apply (@vclosedN_mono _ 0 k (le_0_n _)).
  apply vinstL_preserves_vclosedN. exact (venv_closed_const Hcl c Hc).
Qed.

Lemma closed_inst_defeq env df ls k :
  VEnvClosed env -> venv_defeqs env df ->
  vclosedN k (vinstL ls (vdf_lhs df)) /\
  vclosedN k (vinstL ls (vdf_rhs df)) /\
  vclosedN k (vinstL ls (vdf_type df)).
Proof.
  intros Hcl Hdf. destruct (venv_closed_defeq Hcl df Hdf) as [H1 [H2 H3]].
  repeat split; apply (@vclosedN_mono _ 0 k (le_0_n _));
    apply vinstL_preserves_vclosedN; assumption.
Qed.

Theorem VIsDefEq_closedN env U G e1 e2 A :
  VEnvClosed env ->
  VIsDefEq env U G e1 e2 A ->
  VCtxClosed G ->
  vclosedN (List.length G) e1 /\ vclosedN (List.length G) e2 /\
  vclosedN (List.length G) A.
Proof.
  intros Hcl H. induction H; intros HG.
  - pose proof (VLookup_length_lt H) as Hlt. simpl.
    repeat split; try exact Hlt. eapply VLookup_closed; eassumption.
  - destruct (IHVIsDefEq HG) as [H1 [H2 H3]]. auto.
  - destruct (IHVIsDefEq1 HG) as [H1 [_ H3]]. destruct (IHVIsDefEq2 HG) as [_ [H5 _]]. auto.
  - simpl. auto.
  - simpl. repeat split. eapply closed_inst_const; eassumption.
  - destruct (IHVIsDefEq1 HG) as [Hf [Hf' [_ HB]]].
    destruct (IHVIsDefEq2 HG) as [Ha [Ha' _]].
    simpl. repeat split; try assumption.
    apply vinst0_preserves_vclosedN; assumption.
  - destruct (IHVIsDefEq1 HG) as [HA1 [HA2 _]].
    destruct (IHVIsDefEq2 (conj HG HA1)) as [Hb1 [Hb2 HB]].
    simpl in *. auto.
  - destruct (IHVIsDefEq1 HG) as [HA1 [HA2 _]].
    destruct (IHVIsDefEq2 (conj HG HA1)) as [Hb1 [Hb2 _]].
    simpl in *. auto.
  - destruct (IHVIsDefEq1 HG) as [_ [HB _]].
    destruct (IHVIsDefEq2 HG) as [He1 [He2 _]]. auto.
  - destruct (IHVIsDefEq2 HG) as [Ha [_ HA]].
    destruct (IHVIsDefEq1 (conj HG HA)) as [He [_ HB]].
    simpl in *. repeat split; try assumption;
      apply vinst0_preserves_vclosedN; assumption.
  - destruct (IHVIsDefEq HG) as [He [_ [HA HB]]].
    simpl. repeat split; try assumption.
    + unfold vlift.
      exact (@vliftN_preserves_vclosedN e 1 0 (List.length G) (le_0_n _) He).
    + lia.
  - destruct (IHVIsDefEq2 HG) as [Hh [_ Hp]].
    destruct (IHVIsDefEq3 HG) as [Hh' _]. auto.
  - eapply closed_inst_defeq; eassumption.
Qed.

(* ========================================================================= *)
(* 5. Universe well-formedness of derivations (IsDefEq.levelWF)              *)
(* ========================================================================= *)

Fixpoint VCtxLevelWF (U : nat) (G : list VExpr) : Prop :=
  match G with
  | [] => True
  | A :: G' => VCtxLevelWF U G' /\ vlevelWF U A
  end.

Lemma VLookup_levelWF U G i A :
  VLookup G i A -> VCtxLevelWF U G -> vlevelWF U A.
Proof.
  induction 1; simpl; intros [HG HA]; unfold vlift; apply vlevelWF_vliftN; auto.
Qed.

Theorem VIsDefEq_levelWF env U G e1 e2 A :
  VIsDefEq env U G e1 e2 A ->
  VCtxLevelWF U G ->
  vlevelWF U e1 /\ vlevelWF U e2 /\ vlevelWF U A.
Proof.
  induction 1; intros HG.
  - simpl. repeat split. eapply VLookup_levelWF; eassumption.
  - destruct (IHVIsDefEq HG) as [H1 [H2 H3]]. auto.
  - destruct (IHVIsDefEq1 HG) as [H1 [_ H3]]. destruct (IHVIsDefEq2 HG) as [_ [H5 _]]. auto.
  - simpl. auto.
  - simpl. repeat split; try assumption. apply vlevelWF_vinstL_any. assumption.
  - destruct (IHVIsDefEq1 HG) as [Hf [Hf' [_ HB]]].
    destruct (IHVIsDefEq2 HG) as [Ha [Ha' _]].
    simpl. repeat split; try assumption. apply vlevelWF_vinst; assumption.
  - destruct (IHVIsDefEq1 HG) as [HA1 [HA2 _]].
    destruct (IHVIsDefEq2 (conj HG HA1)) as [Hb1 [Hb2 HB]].
    simpl. auto.
  - destruct (IHVIsDefEq1 HG) as [HA1 [HA2 Hu]].
    destruct (IHVIsDefEq2 (conj HG HA1)) as [Hb1 [Hb2 Hv]].
    simpl in *. auto.
  - destruct (IHVIsDefEq1 HG) as [_ [HB _]].
    destruct (IHVIsDefEq2 HG) as [He1 [He2 _]]. auto.
  - destruct (IHVIsDefEq2 HG) as [Ha [_ HA]].
    destruct (IHVIsDefEq1 (conj HG HA)) as [He [_ HB]].
    simpl. repeat split; try assumption; apply vlevelWF_vinst; assumption.
  - destruct (IHVIsDefEq HG) as [He [_ [HA HB]]].
    simpl. repeat split; try assumption.
    unfold vlift. apply vlevelWF_vliftN. exact He.
  - destruct (IHVIsDefEq2 HG) as [Hh [_ Hp]].
    destruct (IHVIsDefEq3 HG) as [Hh' _]. auto.
  - repeat split; apply vlevelWF_vinstL_any; assumption.
Qed.

(* ========================================================================= *)
(* 6. Consequences of environment well-formedness (Ordered lemmas)             *)
(* ========================================================================= *)

Theorem VEnvWF_closed env : VEnvWF env -> VEnvClosed env.
Proof.
  induction 1 as [| env n ci env' Hwf IH [_ Hci] Hadd | env df Hwf IH Hdf].
  - constructor; simpl; intros; [discriminate | contradiction].
  - unfold venv_add_const in Hadd.
    destruct (venv_constants env n) eqn:Hn; [discriminate|].
    inversion Hadd; subst env'. clear Hadd.
    constructor; simpl.
    + intros c ci0. destruct (name_eqb c n).
      * intros Heq. inversion Heq; subst. exact Hci.
      * apply (venv_closed_const IH).
    + apply (venv_closed_defeq IH).
  - destruct Hdf as [_ [_ [Hl [Hr Ht]]]].
    constructor; simpl.
    + apply (venv_closed_const IH).
    + intros df0 [Heq | Hin].
      * subst df0. auto.
      * apply (venv_closed_defeq IH). exact Hin.
Qed.

Lemma VConstantWF_mono env1 env2 ci :
  venv_ordered env1 env2 -> VConstantWF env1 ci -> VConstantWF env2 ci.
Proof.
  intros Hord [Hty Hcl]. split; [eapply VEnvOrdered_preserve_VIsType; eassumption | exact Hcl].
Qed.

Lemma VDefEqWF_mono env1 env2 df :
  venv_ordered env1 env2 -> VDefEqWF env1 df -> VDefEqWF env2 df.
Proof.
  intros Hord [Hl [Hr Hcl]].
  split; [|split]; try (eapply VEnvOrdered_preserve_VHasType; eassumption). exact Hcl.
Qed.

Theorem VEnvWF_const_wf env c ci :
  VEnvWF env -> venv_constants env c = Some ci -> VConstantWF env ci.
Proof.
  intros Hwf. revert c ci.
  induction Hwf as [| env n ci' env' Hwf IH Hci Hadd | env df Hwf IH Hdf];
    intros c ci Hc.
  - discriminate.
  - pose proof (venv_add_const_ordered _ _ _ Hadd) as Hord.
    apply (VConstantWF_mono Hord).
    unfold venv_add_const in Hadd.
    destruct (venv_constants env n) eqn:Hn; [discriminate|].
    inversion Hadd; subst env'. simpl in Hc.
    destruct (name_eqb c n).
    + inversion Hc; subst. exact Hci.
    + eapply IH. exact Hc.
  - apply (VConstantWF_mono (venv_add_defeq_ordered env df)).
    eapply IH. exact Hc.
Qed.

Theorem VEnvWF_defeq_wf env df :
  VEnvWF env -> venv_defeqs env df -> VDefEqWF env df.
Proof.
  intros Hwf. revert df.
  induction Hwf as [| env n ci env' Hwf IH Hci Hadd | env df' Hwf IH Hdf];
    intros df Hin.
  - contradiction.
  - pose proof (venv_add_const_ordered _ _ _ Hadd) as Hord.
    apply (VDefEqWF_mono Hord).
    unfold venv_add_const in Hadd.
    destruct (venv_constants env n) eqn:Hn; [discriminate|].
    inversion Hadd; subst env'. simpl in Hin. eapply IH. exact Hin.
  - apply (VDefEqWF_mono (venv_add_defeq_ordered env df')).
    destruct Hin as [Heq | Hin].
    + subst. exact Hdf.
    + eapply IH. exact Hin.
Qed.

(* ========================================================================= *)
(* 7. Weakening from the empty context (IsDefEq.weakR / weak0)               *)
(* ========================================================================= *)

Theorem VIsDefEq_weak0 env U G e1 e2 A :
  VEnvClosed env ->
  VIsDefEq env U [] e1 e2 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hcl H.
  destruct (VIsDefEq_closedN Hcl H I) as [H1 [H2 H3]]. simpl in H1, H2, H3.
  assert (Hz : VCtxLiftN (List.length G) 0 [] (G ++ [])) by (constructor; reflexivity).
  rewrite app_nil_r in Hz.
  pose proof (VIsDefEq_weakN Hcl H Hz) as Hw.
  rewrite !(@vclosedN_vliftN_eq _ (List.length G) 0) in Hw by assumption.
  exact Hw.
Qed.

Corollary VHasType_weak0 env U G e A :
  VEnvClosed env -> VHasType env U [] e A -> VHasType env U G e A.
Proof. apply VIsDefEq_weak0. Qed.

Corollary VIsType_weak0 env U G A :
  VEnvClosed env -> VIsType env U [] A -> VIsType env U G A.
Proof. intros Hcl [u Hu]. exists u. apply VIsDefEq_weak0; assumption. Qed.

Lemma VCtxLiftN_one A G : VCtxLiftN 1 0 G (A :: G).
Proof.
  change (A :: G) with ([A] ++ G). constructor. reflexivity.
Qed.

Corollary VIsDefEq_weak env U G B e1 e2 A :
  VEnvClosed env ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U (B :: G) (vlift e1) (vlift e2) (vlift A).
Proof.
  intros Hcl H. exact (VIsDefEq_weakN Hcl H (VCtxLiftN_one B G)).
Qed.

Corollary VIsType_weakN env U G A n k G' :
  VEnvClosed env -> VCtxLiftN n k G G' ->
  VIsType env U G A -> VIsType env U G' (vliftN n k A).
Proof.
  intros Hcl Hctx [u Hu]. exists u.
  exact (VIsDefEq_weakN Hcl Hu Hctx).
Qed.

(* HasType.const0 and IsDefEq.extra0: instantiation at the identity levels. *)
Theorem VHasType_const0 env c ci :
  VEnvWF env -> venv_constants env c = Some ci ->
  VHasType env (vc_uvars ci) [] (VConst c (vlevel_params (vc_uvars ci))) (vc_type ci).
Proof.
  intros Hwf Hc.
  destruct (VEnvWF_const_wf Hwf Hc) as [[u Hu] _].
  destruct (VIsDefEq_levelWF Hu I) as [Hlv _].
  rewrite <- (vinstL_params Hlv).
  apply VHasType_const; [exact Hc | apply vlevel_params_wf | apply vlevel_params_length].
Qed.

Theorem VIsDefEq_extra0 env df :
  VEnvWF env -> venv_defeqs env df ->
  VIsDefEq env (vdf_uvars df) [] (vdf_lhs df) (vdf_rhs df) (vdf_type df).
Proof.
  intros Hwf Hdf.
  destruct (VEnvWF_defeq_wf Hwf Hdf) as [Hl [Hr _]].
  destruct (VIsDefEq_levelWF Hl I) as [Hlhs [_ Hty]].
  destruct (VIsDefEq_levelWF Hr I) as [Hrhs _].
  pose proof (@VDF_extra env (vdf_uvars df) [] df (vlevel_params (vdf_uvars df)) Hdf
    (vlevel_params_wf _) (vlevel_params_length _)) as H.
  rewrite (vinstL_params Hlhs), (vinstL_params Hrhs), (vinstL_params Hty) in H.
  exact H.
Qed.

(* ========================================================================= *)
(* 8. Substitution (IsDefEq.instN)                                           *)
(* ========================================================================= *)

(* Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ: Γ₁ has A₀ at depth k over Γ₀, and Γ is Γ₁ with
   that entry removed and e₀ substituted into the entries above it. *)
Inductive VCtxInstN (G0 : list VExpr) (e0 A0 : VExpr) :
    nat -> list VExpr -> list VExpr -> Prop :=
| VCtxInstN_zero : VCtxInstN G0 e0 A0 0 (A0 :: G0) G0
| VCtxInstN_succ : forall k G1 G A,
    VCtxInstN G0 e0 A0 k G1 G ->
    VCtxInstN G0 e0 A0 (S k) (A :: G1) (vinst A e0 k :: G).

Lemma vinst_vlift_succ e v k :
  vinst (vlift e) v (S k) = vlift (vinst e v k).
Proof.
  unfold vlift. symmetry.
  exact (@vliftN_vinst_lo e v 1 0 k (le_0_n _)).
Qed.

Lemma vinstVar_succ j v k :
  vinstVar (S j) v (S k) = vlift (vinstVar j v k).
Proof.
  pose proof (@vliftN_vinst_lo (VBVar j) v 1 0 k (le_0_n _)) as H.
  change (vinst (VBVar j) v k) with (vinstVar j v k) in H.
  change (vliftN 1 0 (VBVar j)) with (VBVar (S j)) in H.
  change (vinst (VBVar (S j)) v (1 + k)) with (vinstVar (S j) v (S k)) in H.
  unfold vlift. rewrite H. reflexivity.
Qed.

Lemma VCtxInstN_lookup env U G0 e0 A0 :
  VEnvClosed env -> VHasType env U G0 e0 A0 ->
  forall k G1 G, VCtxInstN G0 e0 A0 k G1 G ->
  forall i ty, VLookup G1 i ty ->
  VHasType env U G (vinstVar i e0 k) (vinst ty e0 k).
Proof.
  intros Hcl H0. induction 1 as [| k G1 G A W IH]; intros i ty Hlk.
  - inversion Hlk as [A' G' Heq1 Heq2 Heq3 | A' G' j B Hj Heq1 Heq2 Heq3]; subst.
    + change (vinstVar 0 e0 0) with (vliftN 0 0 e0). rewrite vliftN_zero.
      change (vinst (vlift A0) e0 0) with (vinst0 (vlift A0) e0).
      rewrite vinst0_vlift. exact H0.
    + change (vinstVar (S j) e0 0) with (VBVar j).
      change (vinst (vlift B) e0 0) with (vinst0 (vlift B) e0).
      rewrite vinst0_vlift. apply VDF_bvar. exact Hj.
  - inversion Hlk as [A' G' Heq1 Heq2 Heq3 | A' G' j B Hj Heq1 Heq2 Heq3]; subst.
    + change (vinstVar 0 e0 (S k)) with (VBVar 0).
      rewrite vinst_vlift_succ. apply VDF_bvar. constructor.
    + rewrite vinstVar_succ, vinst_vlift_succ.
      apply VIsDefEq_weak; [exact Hcl |]. apply IH. exact Hj.
Qed.

Theorem VIsDefEq_instN env U G0 e0 A0 G1 e1 e2 A :
  VEnvClosed env ->
  VHasType env U G0 e0 A0 ->
  VIsDefEq env U G1 e1 e2 A ->
  forall k G, VCtxInstN G0 e0 A0 k G1 G ->
  VIsDefEq env U G (vinst e1 e0 k) (vinst e2 e0 k) (vinst A e0 k).
Proof.
  intros Hcl H0 H. induction H; intros k G' W.
  - eapply VCtxInstN_lookup; eassumption.
  - apply VDF_symm. auto.
  - eapply VDF_trans; eauto.
  - apply VDF_sortDF; assumption.
  - rewrite (vclosedN_vinst_eq e0 (closed_inst_const ls1 k Hcl H)).
    eapply VDF_constDF; eassumption.
  - rewrite vinst0_vinst_hi. eapply VDF_appDF; eauto.
  - eapply VDF_lamDF; [eauto |]. apply IHVIsDefEq2. constructor. exact W.
  - eapply VDF_forallEDF; [eauto |]. apply IHVIsDefEq2. constructor. exact W.
  - eapply VDF_defeqDF; eauto.
  - rewrite !vinst0_vinst_hi. eapply VDF_beta; [| eauto].
    apply IHVIsDefEq1. constructor. exact W.
  - change (vinst (VLam A (VApp (vlift e) (VBVar 0))) e0 k)
      with (VLam (vinst A e0 k) (VApp (vinst (vlift e) e0 (S k)) (VBVar 0))).
    rewrite vinst_vlift_succ. apply VDF_eta. auto.
  - eapply VDF_proofIrrel; eauto.
  - destruct (closed_inst_defeq ls k Hcl H) as [Hl [Hr Ht]].
    rewrite (vclosedN_vinst_eq e0 Hl), (vclosedN_vinst_eq e0 Hr), (vclosedN_vinst_eq e0 Ht).
    eapply VDF_extra; eassumption.
Qed.

Corollary VHasType_instN env U G0 e0 A0 G1 e A k G :
  VEnvClosed env -> VCtxInstN G0 e0 A0 k G1 G ->
  VHasType env U G1 e A -> VHasType env U G0 e0 A0 ->
  VHasType env U G (vinst e e0 k) (vinst A e0 k).
Proof. intros Hcl W H H0. eapply VIsDefEq_instN; eassumption. Qed.

Corollary VIsType_instN env U G0 e0 A0 G1 A k G :
  VEnvClosed env -> VCtxInstN G0 e0 A0 k G1 G ->
  VIsType env U G1 A -> VHasType env U G0 e0 A0 ->
  VIsType env U G (vinst A e0 k).
Proof.
  intros Hcl W [u Hu] H0. exists u.
  exact (VIsDefEq_instN Hcl H0 Hu W).
Qed.

Corollary VIsDefEqU_instN env U G0 e0 A0 G1 e1 e2 k G :
  VEnvClosed env -> VCtxInstN G0 e0 A0 k G1 G ->
  VIsDefEqU env U G1 e1 e2 -> VHasType env U G0 e0 A0 ->
  VIsDefEqU env U G (vinst e1 e0 k) (vinst e2 e0 k).
Proof.
  intros Hcl W [A HA] H0. exists (vinst A e0 k).
  exact (VIsDefEq_instN Hcl H0 HA W).
Qed.

(* The common single-binder instance. *)
Corollary VIsDefEq_inst0 env U G A e1 e2 B a :
  VEnvClosed env ->
  VIsDefEq env U (A :: G) e1 e2 B ->
  VHasType env U G a A ->
  VIsDefEq env U G (vinst0 e1 a) (vinst0 e2 a) (vinst0 B a).
Proof.
  intros Hcl H Ha. exact (VIsDefEq_instN Hcl Ha H (VCtxInstN_zero G a A)).
Qed.

(* ========================================================================= *)
(* 9. Well-formed contexts and lookup (OnCtx, IsType.lookup)                 *)
(* ========================================================================= *)

(* OnCtx Γ (IsType env U): every entry is a type in the suffix below it. *)
Fixpoint VCtxWF (env : VEnv) (U : nat) (G : list VExpr) : Prop :=
  match G with
  | [] => True
  | A :: G' => VCtxWF env U G' /\ VIsType env U G' A
  end.

Lemma VCtxWF_closed env U G :
  VEnvClosed env -> VCtxWF env U G -> VCtxClosed G.
Proof.
  intros Hcl. induction G as [|A G IH]; simpl; auto.
  intros [HG [u Hu]]. split; [auto |].
  destruct (VIsDefEq_closedN Hcl Hu (IH HG)) as [H _]. exact H.
Qed.

Theorem VIsType_lookup env U G i A :
  VEnvClosed env -> VCtxWF env U G -> VLookup G i A -> VIsType env U G A.
Proof.
  intros Hcl HG Hlk. revert HG.
  induction Hlk as [A G | A G i B Hlk IH]; simpl; intros [HG HA].
  - exact (VIsType_weakN Hcl (VCtxLiftN_one A G) HA).
  - exact (VIsType_weakN Hcl (VCtxLiftN_one A G) (IH HG)).
Qed.

(* ========================================================================= *)
(* 10. Context conversion (IsDefEq.defeqDF_l', IsDefEqCtx, defeqDFC)         *)
(* ========================================================================= *)

Lemma vinst_vliftN_bvar0 e : forall k, vinst (vliftN 1 (S k) e) (VBVar 0) k = e.
Proof.
  induction e as [i|u|c us|f IHf a IHa|A IHA b IHb|A IHA B IHB]; intros k;
    cbn [vliftN vinst]; try (f_equal; auto; fail).
  unfold vliftVar.
  destruct (Nat.ltb_spec i (S k)) as [Hi | Hi]; cbv beta iota; unfold vinstVar.
  - destruct (Nat.ltb_spec i k) as [Hik | Hik]; [reflexivity |].
    assert (i = k) by lia. subst i. rewrite Nat.eqb_refl.
    cbn [vliftN]. unfold vliftVar. simpl. f_equal. lia.
  - destruct (Nat.ltb_spec (1 + i) k); [lia |].
    destruct (Nat.eqb_spec (1 + i) k); [lia |]. reflexivity.
Qed.

Theorem VIsDefEq_defeqDF_l' env U G A A' u D e1 e2 B :
  VEnvClosed env ->
  VIsDefEq env U G A A' (VSort u) ->
  VIsDefEq env U (D ++ A :: G) e1 e2 B ->
  VIsDefEq env U (D ++ A' :: G) e1 e2 B.
Proof.
  intros Hcl HA H.
  assert (Hctx : exists G',
    VCtxLiftN 1 (S (List.length D)) (D ++ A :: G) G' /\
    VCtxInstN (A' :: G) (VBVar 0) (vlift A) (List.length D) G' (D ++ A' :: G)).
  { clear H. induction D as [|C D IH]; simpl.
    - exists (vlift A :: A' :: G). split.
      + apply VCtxLiftN_succ. apply VCtxLiftN_one.
      + apply VCtxInstN_zero.
    - destruct IH as [G' [Hl Hi]].
      exists (vliftN 1 (S (List.length D)) C :: G'). split.
      + apply VCtxLiftN_succ. exact Hl.
      + pose proof (VCtxInstN_succ (vliftN 1 (S (List.length D)) C) Hi) as Hs.
        rewrite vinst_vliftN_bvar0 in Hs. exact Hs. }
  destruct Hctx as [G' [Hl Hi]].
  assert (H0 : VHasType env U (A' :: G) (VBVar 0) (vlift A)).
  { eapply VDF_defeqDF.
    - exact (VIsDefEq_weak A' Hcl (VDF_symm HA)).
    - apply VDF_bvar. constructor. }
  pose proof (VIsDefEq_instN Hcl H0 (VIsDefEq_weakN Hcl H Hl) Hi) as Hres.
  rewrite !vinst_vliftN_bvar0 in Hres. exact Hres.
Qed.

Corollary VIsDefEq_defeqDF_l env U G A A' u e1 e2 B :
  VEnvClosed env ->
  VIsDefEq env U G A A' (VSort u) ->
  VIsDefEq env U (A :: G) e1 e2 B ->
  VIsDefEq env U (A' :: G) e1 e2 B.
Proof. intros Hcl HA H. exact (@VIsDefEq_defeqDF_l' env U G A A' u [] e1 e2 B Hcl HA H). Qed.

Corollary VHasType_defeq_l env U G A A' u e B :
  VEnvClosed env ->
  VIsDefEq env U G A A' (VSort u) ->
  VHasType env U (A :: G) e B ->
  VHasType env U (A' :: G) e B.
Proof. apply VIsDefEq_defeqDF_l. Qed.

(* IsDefEqCtx: two contexts over a common suffix G0 that are pointwise defeq. *)
Inductive VIsDefEqCtx (env : VEnv) (U : nat) (G0 : list VExpr) :
    list VExpr -> list VExpr -> Prop :=
| VIsDefEqCtx_zero : VIsDefEqCtx env U G0 G0 G0
| VIsDefEqCtx_succ : forall G1 G2 A1 A2 u,
    VIsDefEqCtx env U G0 G1 G2 ->
    VIsDefEq env U G1 A1 A2 (VSort u) ->
    VIsDefEqCtx env U G0 (A1 :: G1) (A2 :: G2).

Lemma VIsDefEqCtx_length env U G0 G1 G2 :
  VIsDefEqCtx env U G0 G1 G2 -> List.length G1 = List.length G2.
Proof. induction 1; simpl; congruence. Qed.

Theorem VIsDefEq_defeqDFC' env U G0 G1 G2 :
  VEnvClosed env ->
  VIsDefEqCtx env U G0 G1 G2 ->
  forall D e1 e2 A,
    VIsDefEq env U (D ++ G1) e1 e2 A ->
    VIsDefEq env U (D ++ G2) e1 e2 A.
Proof.
  intros Hcl. induction 1 as [| G1 G2 A1 A2 u Hctx IH HA]; intros D e1 e2 A H.
  - exact H.
  - pose proof (VIsDefEq_defeqDF_l' (D:=D) Hcl HA H) as H'.
    replace (D ++ A2 :: G1) with ((D ++ [A2]) ++ G1) in H' by (rewrite <- app_assoc; reflexivity).
    replace (D ++ A2 :: G2) with ((D ++ [A2]) ++ G2) by (rewrite <- app_assoc; reflexivity).
    apply IH. exact H'.
Qed.

Corollary VIsDefEq_defeqDFC env U G0 G1 G2 e1 e2 A :
  VEnvClosed env ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VIsDefEq env U G1 e1 e2 A ->
  VIsDefEq env U G2 e1 e2 A.
Proof. intros Hcl Hctx H. exact (VIsDefEq_defeqDFC' Hcl Hctx (D:=[]) H). Qed.

Corollary VIsType_defeqDFC env U G0 G1 G2 A :
  VEnvClosed env -> VIsDefEqCtx env U G0 G1 G2 ->
  VIsType env U G1 A -> VIsType env U G2 A.
Proof. intros Hcl Hctx [u Hu]. exists u. eapply VIsDefEq_defeqDFC; eassumption. Qed.

Theorem VIsDefEqCtx_symm env U G0 G1 G2 :
  VEnvClosed env ->
  VIsDefEqCtx env U G0 G1 G2 -> VIsDefEqCtx env U G0 G2 G1.
Proof.
  intros Hcl. induction 1 as [| G1 G2 A1 A2 u Hctx IH HA].
  - constructor.
  - econstructor; [exact IH |].
    eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VDF_symm HA)].
Qed.

(* ========================================================================= *)
(* 11. Inversion: sorts and Pi types (IsDefEq.sort_inv', forallE_inv')       *)
(* ========================================================================= *)

Lemma vinst0_eq_sort e a u :
  vinst0 e a = VSort u -> e = VSort u \/ (e = VBVar 0 /\ a = VSort u).
Proof.
  unfold vinst0. destruct e as [i|u'|c us|f x|A b|A B]; simpl; try discriminate.
  - unfold vinstVar. destruct i as [|i]; simpl.
    + rewrite vliftN_zero. intros ->. right. auto.
    + discriminate.
  - intros H. left. exact H.
Qed.

Lemma vinst0_eq_forallE e a A B :
  vinst0 e a = VForallE A B ->
  (e = VBVar 0 /\ a = VForallE A B) \/
  (exists A0 B0, e = VForallE A0 B0 /\ A = vinst A0 a 0 /\ B = vinst B0 a 1).
Proof.
  unfold vinst0. destruct e as [i|u|c us|f x|A0 b|A0 B0]; simpl; try discriminate.
  - unfold vinstVar. destruct i as [|i]; simpl.
    + rewrite vliftN_zero. intros ->. left. auto.
    + discriminate.
  - intros H. inversion H; subst. right. exists A0, B0. auto.
Qed.

Theorem VIsDefEq_sort_inv' env U G e1 e2 V :
  VIsDefEq env U G e1 e2 V ->
  forall u, (e1 = VSort u \/ e2 = VSort u) -> vlevel_wf U u.
Proof.
  induction 1; intros w Heq; try (destruct Heq as [Heq | Heq]; discriminate).
  - apply (IHVIsDefEq w). tauto.
  - destruct Heq as [Heq | Heq]; [apply (IHVIsDefEq1 w) | apply (IHVIsDefEq2 w)]; tauto.
  - destruct Heq as [Heq | Heq]; inversion Heq; subst; assumption.
  - apply (IHVIsDefEq2 w). exact Heq.
  - destruct Heq as [Heq | Heq]; [discriminate |].
    destruct (vinst0_eq_sort Heq) as [He | [_ Ha]].
    + apply (IHVIsDefEq1 w). left. exact He.
    + apply (IHVIsDefEq2 w). left. exact Ha.
  - destruct Heq as [Heq | Heq]; [discriminate |]. apply (IHVIsDefEq w). left. exact Heq.
  - destruct Heq as [Heq | Heq]; [apply (IHVIsDefEq2 w) | apply (IHVIsDefEq3 w)]; left; exact Heq.
  - destruct Heq as [Heq | Heq];
      [destruct (vdf_lhs df) eqn:E | destruct (vdf_rhs df) eqn:E];
      simpl in Heq; try discriminate; inversion Heq; subst;
      apply vlevel_inst_wf_any; assumption.
Qed.

Corollary VIsDefEq_sort_inv_l env U G u e2 V :
  VIsDefEq env U G (VSort u) e2 V -> vlevel_wf U u.
Proof. intros H. exact (VIsDefEq_sort_inv' H (or_introl eq_refl)). Qed.

Corollary VIsType_sort_inv env U G u :
  VIsType env U G (VSort u) -> vlevel_wf U u.
Proof. intros [v Hv]. exact (VIsDefEq_sort_inv_l Hv). Qed.

(* The environment-level hypothesis of forallE_inv': every defeq side that is
   syntactically a Pi type has a well-formed domain and codomain. *)
Definition VDefEqsForallInv (env : VEnv) : Prop :=
  forall df, venv_defeqs env df ->
  forall A B, (vdf_lhs df = VForallE A B \/ vdf_rhs df = VForallE A B) ->
    VIsType env (vdf_uvars df) [] A /\ VIsType env (vdf_uvars df) [A] B.

Lemma forallE_inv_instL env U U0 G ls e A B :
  VEnvClosed env -> Forall (vlevel_wf U) ls ->
  vinstL ls e = VForallE A B ->
  (forall A0 B0, e = VForallE A0 B0 ->
     VIsType env U0 [] A0 /\ VIsType env U0 [A0] B0) ->
  VIsType env U G A /\ VIsType env U (A :: G) B.
Proof.
  intros Hcl Hls Heq IH.
  destruct e as [i|u|c us|f x|A1 b|A0 B0]; simpl in Heq; try discriminate.
  inversion Heq; subst A B. clear Heq.
  destruct (IH A0 B0 eq_refl) as [HA0 HB0].
  pose proof (VIsType_instL Hls HA0) as HA. simpl in HA.
  pose proof (VIsType_instL Hls HB0) as HB. simpl in HB.
  destruct HA as [u HAu]. destruct HB as [v HBv].
  destruct (VIsDefEq_closedN Hcl HAu I) as [CA _]. simpl in CA.
  destruct (VIsDefEq_closedN Hcl HBv (conj I CA)) as [CB _]. simpl in CB.
  split.
  - exists u. apply VIsDefEq_weak0; assumption.
  - exists v.
    assert (Hz : VCtxLiftN (List.length G) 0 [] (G ++ [])) by (constructor; reflexivity).
    rewrite app_nil_r in Hz.
    pose proof (VIsDefEq_weakN Hcl HBv (VCtxLiftN_succ (vinstL ls A0) Hz)) as Hw.
    rewrite (@vclosedN_vliftN_eq _ (List.length G) 0 CA) in Hw.
    rewrite (@vclosedN_vliftN_eq _ (List.length G) 1 CB) in Hw.
    exact Hw.
Qed.

Theorem VIsDefEq_forallE_inv' env U G e1 e2 V :
  VEnvClosed env -> VDefEqsForallInv env ->
  VIsDefEq env U G e1 e2 V ->
  forall A B, (e1 = VForallE A B \/ e2 = VForallE A B) ->
    VIsType env U G A /\ VIsType env U (A :: G) B.
Proof.
  intros Hcl Henv.
  induction 1; intros A0 B0 Heq; try (destruct Heq as [Heq | Heq]; discriminate).
  - apply IHVIsDefEq. tauto.
  - destruct Heq as [Heq | Heq]; [apply IHVIsDefEq1 | apply IHVIsDefEq2]; tauto.
  - destruct Heq as [Heq | Heq]; inversion Heq; subst A0 B0.
    + split; [exists u; exact (VIsDefEq_refl_l H) | exists v; exact (VIsDefEq_refl_l H0)].
    + split; [exists u; exact (VIsDefEq_refl_r H) |].
      exists v. eapply VIsDefEq_defeqDF_l; [exact Hcl | exact H | exact (VIsDefEq_refl_r H0)].
  - apply IHVIsDefEq2. exact Heq.
  - destruct Heq as [Heq | Heq]; [discriminate |].
    destruct (vinst0_eq_forallE Heq) as [[He Ha] | [A1 [B1 [He [HA0 HB0]]]]].
    + apply IHVIsDefEq2. left. exact Ha.
    + subst e A0 B0.
      destruct (IHVIsDefEq1 A1 B1 (or_introl eq_refl)) as [HA1 HB1].
      split.
      * exact (VIsType_instN Hcl (VCtxInstN_zero G a A) HA1 H0).
      * exact (VIsType_instN Hcl (VCtxInstN_succ A1 (VCtxInstN_zero G a A)) HB1 H0).
  - destruct Heq as [Heq | Heq]; [discriminate |]. apply IHVIsDefEq. left. exact Heq.
  - destruct Heq as [Heq | Heq]; [apply IHVIsDefEq2 | apply IHVIsDefEq3]; left; exact Heq.
  - destruct Heq as [Heq | Heq];
      (eapply forallE_inv_instL; [exact Hcl | eassumption | exact Heq |]);
      intros A1 B1 He; apply (Henv df H A1 B1); auto.
Qed.

(* Ordered.induction specialised to the forallE inversion invariant. *)
Theorem VEnvWF_forallE_inv env : VEnvWF env -> VDefEqsForallInv env.
Proof.
  intros Hwf. pose proof (VEnvWF_closed Hwf) as Hcl0. revert Hcl0.
  induction Hwf as [| env n ci env' Hwf IH Hci Hadd | env df Hwf IH Hdf]; intros Hcl0.
  - intros df Hin. contradiction.
  - pose proof (venv_add_const_ordered _ _ _ Hadd) as Hord.
    pose proof (IH (VEnvWF_closed Hwf)) as IH'.
    intros df Hin A B Heq.
    unfold venv_add_const in Hadd. destruct (venv_constants env n); [discriminate |].
    inversion Hadd; subst env'. simpl in Hin.
    destruct (IH' df Hin A B Heq) as [HA HB].
    split; eapply VEnvOrdered_preserve_VIsType; eassumption.
  - pose proof (venv_add_defeq_ordered env df) as Hord.
    pose proof (VEnvWF_closed Hwf) as Hcl.
    pose proof (IH Hcl) as IH'.
    intros df0 Hin A B Heq. simpl in Hin.
    assert (Hres : VIsType env (vdf_uvars df0) [] A /\ VIsType env (vdf_uvars df0) [A] B).
    { destruct Hin as [Hin | Hin].
      - subst df0. destruct Hdf as [Hl [Hr _]].
        destruct Heq as [Heq | Heq].
        + exact (VIsDefEq_forallE_inv' Hcl IH' Hl (or_introl Heq)).
        + exact (VIsDefEq_forallE_inv' Hcl IH' Hr (or_introl Heq)).
      - exact (IH' df0 Hin A B Heq). }
    destruct Hres as [HA HB].
    split; eapply VEnvOrdered_preserve_VIsType; eassumption.
Qed.

Theorem VHasType_forallE_inv env U G A B V :
  VEnvWF env ->
  VHasType env U G (VForallE A B) V ->
  VIsType env U G A /\ VIsType env U (A :: G) B.
Proof.
  intros Hwf H.
  exact (VIsDefEq_forallE_inv' (VEnvWF_closed Hwf) (VEnvWF_forallE_inv Hwf) H
           (or_introl eq_refl)).
Qed.

Corollary VIsType_forallE_inv env U G A B :
  VEnvWF env ->
  VIsType env U G (VForallE A B) ->
  VIsType env U G A /\ VIsType env U (A :: G) B.
Proof. intros Hwf [u Hu]. exact (VHasType_forallE_inv Hwf Hu). Qed.

(* ========================================================================= *)
(* 12. Regularity: the type of a derivation is a type (IsDefEq.isType)       *)
(* ========================================================================= *)

Definition VEnvTypesWF (env : VEnv) : Prop :=
  (forall c ci, venv_constants env c = Some ci ->
     VIsType env (vc_uvars ci) [] (vc_type ci)) /\
  (forall df, venv_defeqs env df ->
     VIsType env (vdf_uvars df) [] (vdf_type df)).

Theorem VIsDefEq_isType' env U G e1 e2 A :
  VEnvClosed env -> VDefEqsForallInv env -> VEnvTypesWF env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsType env U G A.
Proof.
  intros Hcl Hfi [Hconst Hdefeq] HG H. revert HG.
  induction H; intros HG.
  - eapply VIsType_lookup; eassumption.
  - auto.
  - auto.
  - exists (VLSucc (VLSucc l1)). apply VHasType_sort. exact H.
  - destruct (Hconst c ci H) as [w Hw].
    exists (vlevel_inst ls1 w).
    apply VIsDefEq_weak0; [exact Hcl |].
    exact (VIsDefEq_instL H0 Hw).
  - destruct (IHVIsDefEq1 HG) as [w Hw].
    destruct (VIsDefEq_forallE_inv' Hcl Hfi Hw (or_introl eq_refl)) as [_ HB].
    exact (VIsType_instN Hcl (VCtxInstN_zero G a1 A) HB (VIsDefEq_refl_l H0)).
  - destruct (IHVIsDefEq2 (conj HG (ex_intro _ u (VIsDefEq_refl_l H)))) as [v Hv].
    exists (VLIMax u v). apply VHasType_forallE; [exact (VIsDefEq_refl_l H) | exact Hv].
  - pose proof (VIsType_sort_inv (IHVIsDefEq1 HG)) as Hu.
    pose proof (VIsType_sort_inv (IHVIsDefEq2 (conj HG (ex_intro _ u (VIsDefEq_refl_l H)))))
      as Hv.
    exists (VLSucc (VLIMax u v)). apply VHasType_sort. simpl. auto.
  - exists u. exact (VIsDefEq_refl_r H).
  - pose proof (IHVIsDefEq2 HG) as HA.
    pose proof (IHVIsDefEq1 (conj HG HA)) as HB.
    exact (VIsType_instN Hcl (VCtxInstN_zero G a A) HB H0).
  - auto.
  - exists VLZero. exact H.
  - destruct (Hdefeq df H) as [w Hw].
    exists (vlevel_inst ls w).
    apply VIsDefEq_weak0; [exact Hcl |].
    exact (VIsDefEq_instL H0 Hw).
Qed.

(* Ordered.isType: every well-formed environment satisfies VEnvTypesWF. *)
Theorem VEnvWF_types env : VEnvWF env -> VEnvTypesWF env.
Proof.
  induction 1 as [| env n ci env' Hwf IH Hci Hadd | env df Hwf IH Hdf].
  - split; simpl; intros; [discriminate | contradiction].
  - pose proof (venv_add_const_ordered _ _ _ Hadd) as Hord.
    assert (Hwf' : VEnvWF env') by (econstructor; eassumption).
    assert (Hall : forall c ci0, venv_constants env' c = Some ci0 -> VConstantWF env' ci0)
      by (intros c ci0 Hc; exact (VEnvWF_const_wf Hwf' Hc)).
    split.
    + intros c ci0 Hc. exact (proj1 (Hall c ci0 Hc)).
    + intros df Hin.
      unfold venv_add_const in Hadd. destruct (venv_constants env n); [discriminate |].
      inversion Hadd; subst env'. simpl in Hin.
      eapply VEnvOrdered_preserve_VIsType; [exact Hord | exact (proj2 IH df Hin)].
  - pose proof (venv_add_defeq_ordered env df) as Hord.
    assert (Hwf' : VEnvWF (venv_add_defeq env df)) by (econstructor; eassumption).
    assert (Hall : forall c ci0, venv_constants (venv_add_defeq env df) c = Some ci0 ->
                   VConstantWF (venv_add_defeq env df) ci0)
      by (intros c ci0 Hc; exact (VEnvWF_const_wf Hwf' Hc)).
    split.
    + intros c ci Hc. exact (proj1 (Hall c ci Hc)).
    + intros df0 [Heq | Hin].
      * subst df0. destruct Hdf as [Hl _].
        eapply VEnvOrdered_preserve_VIsType; [exact Hord |].
        refine (VIsDefEq_isType' (VEnvWF_closed Hwf) (VEnvWF_forallE_inv Hwf) IH _ Hl). exact I.
      * eapply VEnvOrdered_preserve_VIsType; [exact Hord | exact (proj2 IH df0 Hin)].
Qed.

Theorem VIsDefEq_isType env U G e1 e2 A :
  VEnvWF env -> VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A -> VIsType env U G A.
Proof.
  intros Hwf HG H.
  exact (VIsDefEq_isType' (VEnvWF_closed Hwf) (VEnvWF_forallE_inv Hwf) (VEnvWF_types Hwf) HG H).
Qed.

Corollary VIsDefEq_sort_r env U G e1 e2 u :
  VEnvWF env -> VCtxWF env U G ->
  VIsDefEq env U G e1 e2 (VSort u) -> vlevel_wf U u.
Proof. intros Hwf HG H. exact (VIsType_sort_inv (VIsDefEq_isType Hwf HG H)). Qed.

(* ========================================================================= *)
(* 13. Congruence of substitution (IsDefEq.instDF)                           *)
(* ========================================================================= *)

Theorem VIsDefEq_instDF env U G A f f' B a a' :
  VEnvWF env -> VCtxWF env U G ->
  VIsDefEq env U (A :: G) f f' B ->
  VIsDefEq env U G a a' A ->
  VIsDefEq env U G (vinst0 f a) (vinst0 f' a') (vinst0 B a).
Proof.
  intros Hwf HG hf ha.
  destruct (VIsDefEq_isType Hwf HG ha) as [u hA].
  destruct (VIsDefEq_isType Hwf (conj HG (ex_intro _ u hA) : VCtxWF env U (A :: G)) hf) as [v hB].
  assert (H2 : forall f f' B v,
    VIsDefEq env U (A :: G) f f' B ->
    VIsDefEq env U G (vinst0 B a) (vinst0 B a') (VSort v) ->
    VIsDefEq env U G (vinst0 f a) (vinst0 f' a') (vinst0 B a)).
  { clear f f' B v hf hB. intros f f' B v hf hi.
    eapply VDF_trans.
    - apply VDF_symm. exact (VDF_beta (VIsDefEq_refl_l hf) (VIsDefEq_refl_l ha)).
    - eapply VDF_trans.
      + exact (VDF_appDF (VDF_lamDF hA hf) ha).
      + eapply VDF_defeqDF; [exact (VDF_symm hi) |].
        exact (VDF_beta (VIsDefEq_refl_r hf) (VIsDefEq_refl_r ha)). }
  apply (H2 f f' B v hf).
  pose proof (VIsDefEq_sort_r Hwf (conj HG (ex_intro _ u hA) : VCtxWF env U (A :: G)) hB) as Hv.
  exact (H2 B B (VSort v) (VLSucc v) hB (VHasType_sort env U G v Hv)).
Qed.

(* ========================================================================= *)
(* Axiom audit                                                               *)
(* ========================================================================= *)

Print Assumptions VIsDefEq_instL.
Print Assumptions VIsDefEq_closedN.
Print Assumptions VIsDefEq_levelWF.
Print Assumptions VEnvWF_closed.
Print Assumptions VEnvWF_const_wf.
Print Assumptions VEnvWF_defeq_wf.
Print Assumptions VIsDefEq_weak0.
Print Assumptions VHasType_const0.
Print Assumptions VIsDefEq_extra0.
Print Assumptions VIsDefEq_instN.
Print Assumptions VIsDefEq_defeqDF_l'.
Print Assumptions VIsDefEq_defeqDFC.
Print Assumptions VIsDefEqCtx_symm.
Print Assumptions VIsDefEq_sort_inv'.
Print Assumptions VHasType_forallE_inv.
Print Assumptions VIsDefEq_isType.
Print Assumptions VIsDefEq_sort_r.
Print Assumptions VIsDefEq_instDF.
