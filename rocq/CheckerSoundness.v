(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq formalization of Lean4Lean/Verify/{Typing/Expr.lean, Typing/CondTyped.lean,
   TypeChecker/*.lean, Environment/*.lean}: the verification bridge connecting
   executable kernel syntax, WHNF reduction, definitional equality, type
   inference/checking, and declaration admission to the declarative VEnv/VIsDefEq
   model. *)
From Stdlib Require Import List Bool Arith PeanoNat NArith String Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness Checker Declarations
  SemanticModel DeclarativeTyping.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Level and Expression Translation Relations (Lean4Lean/Verify/Typing)   *)
(* ========================================================================= *)

Definition TrLevel (ps : list name) (u : level) (u' : VLevel) : Prop :=
  vlevel_of_level ps u = Some u'.

Inductive TrLevels (ps : list name) : list level -> list VLevel -> Prop :=
| TrLevels_nil : TrLevels ps [] []
| TrLevels_cons : forall u u' us us',
    TrLevel ps u u' ->
    TrLevels ps us us' ->
    TrLevels ps (u :: us) (u' :: us').

Lemma TrLevels_length ps us us' :
  TrLevels ps us us' -> List.length us = List.length us'.
Proof.
  intros H. induction H; simpl; auto.
Qed.

Lemma TrLevels_wf ps us us' :
  TrLevels ps us us' -> Forall (vlevel_wf (List.length ps)) us'.
Proof.
  intros H. induction H; constructor.
  - eapply vlevel_of_level_wf; exact H.
  - exact IHTrLevels.
Qed.

Theorem check_levels_sound_TrLevels ps us :
  check_levels ps us = Accept tt ->
  exists us', TrLevels ps us us' /\ Forall (vlevel_wf (List.length ps)) us'.
Proof.
  induction us as [|u rest IH]; simpl.
  - intros _. exists []. split; constructor.
  - destruct (check_level ps u) as [[]|err|why] eqn:Hu; simpl; try discriminate.
    intros Hrest.
    destruct (check_level_sound_vlevel ps u Hu) as [u' [Hu' Hwfu]].
    destruct (IH Hrest) as [rest' [Htr Hwfr]].
    exists (u' :: rest'). split; constructor; assumption.
Qed.

Theorem levels_equiv_sound_TrLevels fuel ps us vs us' vs' :
  TrLevels ps us us' ->
  TrLevels ps vs vs' ->
  levels_equiv fuel us vs = Accept true ->
  Forall2 vlevel_equiv us' vs'.
Proof.
  intros Hus Hvs Heq. revert vs vs' Hvs Heq.
  induction Hus as [| u u' us0 us0' Hu Hus0 IH];
    intros [|v vs0] vs' Hvs Heq; simpl in Heq; try discriminate.
  - inversion Hvs; subst. constructor.
  - inversion Hvs as [| v0 v' vs1 vs0' Hv Hvs0 Heq1 Heq2]; subst v0 vs1 vs'.
    destruct (level_equiv fuel u v) as [ok|err|why] eqn:Huv;
      simpl in Heq; try discriminate.
    destruct ok; [|discriminate].
    constructor.
    + eapply level_equiv_sound_vlevel; eassumption.
    + eapply IH; eassumption.
Qed.

(* Syntactic-to-Semantic Expression Translation (TrExprS / TrExpr) *)
Inductive TrExprS (env : VEnv) (ps : list name) :
    list VExpr -> expr -> VExpr -> Prop :=
| TrExprS_bvar : forall G i ty,
    VLookup G i ty ->
    TrExprS env ps G (EBVar i) (VBVar i)
| TrExprS_sort : forall G u u',
    TrLevel ps u u' ->
    TrExprS env ps G (ESort u) (VSort u')
| TrExprS_const : forall G c ci us us',
    venv_constants env c = Some ci ->
    TrLevels ps us us' ->
    List.length us = vc_uvars ci ->
    TrExprS env ps G (EConst c us) (VConst c us')
| TrExprS_app : forall G f a f' a' A B,
    VHasType env (List.length ps) G f' (VForallE A B) ->
    VHasType env (List.length ps) G a' A ->
    TrExprS env ps G f f' ->
    TrExprS env ps G a a' ->
    TrExprS env ps G (EApp f a) (VApp f' a')
| TrExprS_lam : forall G n bi ty body ty' body',
    VIsType env (List.length ps) G ty' ->
    TrExprS env ps G ty ty' ->
    TrExprS env ps (ty' :: G) body body' ->
    TrExprS env ps G (ELam n bi ty body) (VLam ty' body')
| TrExprS_pi : forall G n bi ty body ty' body',
    VIsType env (List.length ps) G ty' ->
    VIsType env (List.length ps) (ty' :: G) body' ->
    TrExprS env ps G ty ty' ->
    TrExprS env ps (ty' :: G) body body' ->
    TrExprS env ps G (EPi n bi ty body) (VForallE ty' body')
| TrExprS_let : forall G n ty val body nd ty' val' body',
    VHasType env (List.length ps) G val' ty' ->
    TrExprS env ps G ty ty' ->
    TrExprS env ps G val val' ->
    TrExprS env ps (ty' :: G) body body' ->
    TrExprS env ps G (ELet n ty val body nd) (vinst0 body' val')
| TrExprS_mdata : forall G e e',
    TrExprS env ps G e e' ->
    TrExprS env ps G (EMData e) e'.

Definition TrExpr (env : VEnv) (ps : list name) (G : list VExpr)
    (e : expr) (e' : VExpr) : Prop :=
  exists e0, TrExprS env ps G e e0 /\ VIsDefEqU env (List.length ps) G e0 e'.

Definition TrTyping (env : VEnv) (ps : list name) (G : list VExpr)
    (e ty : expr) (e' ty' : VExpr) : Prop :=
  TrExpr env ps G e e' /\
  TrExpr env ps G ty ty' /\
  VHasType env (List.length ps) G e' ty'.

(* ========================================================================= *)
(* 2. Metatheoretic Properties of TrExprS / TrExpr / TrTyping                *)
(* ========================================================================= *)

(* Direct derivation of substitution typing from VDF_beta + VIsDefEq_refl_r *)
Lemma VHasType_vinst0_from_beta env uvars G A b B v :
  VHasType env uvars (A :: G) b B ->
  VHasType env uvars G v A ->
  VHasType env uvars G (vinst0 b v) (vinst0 B v).
Proof.
  intros Hb Hv.
  eapply VIsDefEq_refl_r.
  eapply VDF_beta; [exact Hb | exact Hv].
Qed.

Theorem TrExprS_has_type env ps G e e' :
  TrExprS env ps G e e' ->
  exists A, VHasType env (List.length ps) G e' A.
Proof.
  intros H. induction H.
  - exists ty. apply VDF_bvar. exact H.
  - exists (VSort (VLSucc u')). apply VHasType_sort.
    eapply vlevel_of_level_wf; exact H.
  - exists (vinstL us' (vc_type ci)).
    eapply VHasType_const; [exact H | eapply TrLevels_wf; exact H0 |].
    rewrite <- (TrLevels_length H0). exact H1.
  - exists (vinst0 B a'). eapply VDF_appDF; eassumption.
  - destruct H as [u Hu].
    destruct IHTrExprS2 as [B HB].
    exists (VForallE ty' B). eapply VDF_lamDF; eassumption.
  - destruct H as [u Hu]. destruct H0 as [v Hv].
    exists (VSort (VLIMax u v)). eapply VDF_forallEDF; eassumption.
  - destruct IHTrExprS3 as [B HB].
    exists (vinst0 B val').
    eapply VHasType_vinst0_from_beta; eassumption.
  - exact IHTrExprS.
Qed.

Theorem TrExprS_to_TrExpr env ps G e e' :
  TrExprS env ps G e e' ->
  TrExpr env ps G e e'.
Proof.
  intros H.
  destruct (TrExprS_has_type H) as [A HA].
  exists e'. split; [exact H | exists A; exact HA].
Qed.

Theorem TrExprS_monotonic_env env1 env2 ps G e e' :
  venv_ordered env1 env2 ->
  TrExprS env1 ps G e e' ->
  TrExprS env2 ps G e e'.
Proof.
  intros Hord H. induction H.
  - eapply TrExprS_bvar; eassumption.
  - eapply TrExprS_sort; eassumption.
  - eapply TrExprS_const; [apply (venv_ord_const Hord); eassumption | ..]; assumption.
  - eapply TrExprS_app; [eapply VEnvOrdered_preserve_VHasType; eassumption |
                         eapply VEnvOrdered_preserve_VHasType; eassumption | ..]; assumption.
  - eapply TrExprS_lam; [eapply VEnvOrdered_preserve_VIsType; eassumption | ..]; assumption.
  - eapply TrExprS_pi; [eapply VEnvOrdered_preserve_VIsType; eassumption |
                        eapply VEnvOrdered_preserve_VIsType; eassumption | ..]; assumption.
  - eapply TrExprS_let; [eapply VEnvOrdered_preserve_VHasType; eassumption | ..]; assumption.
  - apply TrExprS_mdata; assumption.
Qed.

Theorem TrExpr_monotonic_env env1 env2 ps G e e' :
  venv_ordered env1 env2 ->
  TrExpr env1 ps G e e' ->
  TrExpr env2 ps G e e'.
Proof.
  intros Hord [e0 [Htr Hdef]].
  exists e0. split.
  - eapply TrExprS_monotonic_env; eassumption.
  - eapply VEnvOrdered_preserve_VIsDefEqU; eassumption.
Qed.

Theorem TrTyping_monotonic_env env1 env2 ps G e ty e' ty' :
  venv_ordered env1 env2 ->
  TrTyping env1 ps G e ty e' ty' ->
  TrTyping env2 ps G e ty e' ty'.
Proof.
  intros Hord [He [Hty Hhas]].
  repeat split.
  - eapply TrExpr_monotonic_env; eassumption.
  - eapply TrExpr_monotonic_env; eassumption.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
Qed.

(* ========================================================================= *)
(* 3. Soundness Bridge for Kernel Type Inference, WHNF, DefEq & Admission    *)
(* ========================================================================= *)

Record KernelEnvBridge (env : environment) (venv : VEnv) : Prop := {
  keb_wf : VEnvWF venv;
  keb_closed : VEnvClosed venv;
  keb_constants : forall n d,
    find_decl n env = Some d ->
    match decl_kind_of d with
    | DUnsupported | DUnsafe _ | DPartial => True
    | _ =>
        exists ci,
          venv_constants venv n = Some ci /\
          vc_uvars ci = List.length (decl_params d) /\
          TrExpr venv (decl_params d) [] (decl_type d) (vc_type ci) /\
          VIsType venv (vc_uvars ci) [] (vc_type ci)
    end
}.

Theorem KernelEnvBridge_empty : KernelEnvBridge [] venv_empty.
Proof.
  constructor.
  - constructor.
  - constructor; simpl; intros; contradiction || discriminate.
  - intros n d H. simpl in H. discriminate.
Qed.

Theorem get_constant_sound_bridge env venv ps n us d :
  KernelEnvBridge env venv ->
  get_constant env ps n us = Accept d ->
  exists ci us',
    venv_constants venv n = Some ci /\
    TrLevels ps us us' /\
    List.length us' = vc_uvars ci /\
    Forall (vlevel_wf (List.length ps)) us' /\
    VHasType venv (List.length ps) [] (VConst n us') (vinstL us' (vc_type ci)).
Proof.
  intros Hbridge Hget.
  unfold get_constant in Hget.
  destruct (find_decl n env) as [decl|] eqn:Hfind; [|discriminate].
  pose proof (@keb_constants env venv Hbridge n decl Hfind) as Hdecl.
  destruct (decl_kind_of decl) eqn:Hkind; try discriminate.
  all: unfold require in Hget;
    destruct (Nat.eqb (List.length (decl_params decl)) (List.length us)) eqn:Harity;
    simpl in Hget; try discriminate;
    destruct (check_levels ps us) as [[]|err|why] eqn:Hlvls;
    simpl in Hget; try discriminate;
    inversion Hget; subst d;
    destruct Hdecl as [ci [Hci [Huv [Htr Htype]]]];
    destruct (@check_levels_sound_TrLevels ps us Hlvls) as [us' [Htr_us Hwf_us]];
    apply Nat.eqb_eq in Harity;
    pose proof (@TrLevels_length ps us us' Htr_us) as Hlen_us;
    exists ci, us';
    repeat split; try assumption; try lia;
    eapply VHasType_const; [exact Hci | exact Hwf_us | lia].
Qed.

Theorem infer_sort_sound_bridge rec fuel env venv ps checking g u ty :
  infer_step rec fuel env ps checking g (ESort u) = Accept ty ->
  forall G,
    exists u',
      ty = ESort (LSucc u) /\
      TrLevel ps u u' /\
      TrExprS venv ps G (ESort u) (VSort u') /\
      TrExprS venv ps G ty (VSort (VLSucc u')) /\
      VHasType venv (List.length ps) G (VSort u') (VSort (VLSucc u')).
Proof.
  intros Hinf G. simpl in Hinf.
  destruct (check_level ps u) as [[]|err|why] eqn:Hchk; simpl in Hinf; [|discriminate..].
  inversion Hinf; subst ty.
  destruct (check_level_sound_vlevel ps u Hchk) as [u' [Hu' Hwf]].
  exists u'. repeat split; auto.
  - constructor. exact Hu'.
  - constructor. unfold TrLevel. simpl. rewrite Hu'. reflexivity.
  - apply VHasType_sort. exact Hwf.
Qed.

Theorem infer_const_sound_bridge rec fuel env venv ps checking g n us ty :
  KernelEnvBridge env venv ->
  infer_step rec fuel env ps checking g (EConst n us) = Accept ty ->
  forall G,
    exists d ci us',
      find_decl n env = Some d /\
      ty = instantiate_levels (decl_params d) us (decl_type d) /\
      venv_constants venv n = Some ci /\
      TrLevels ps us us' /\
      TrExprS venv ps G (EConst n us) (VConst n us') /\
      VHasType venv (List.length ps) G (VConst n us') (vinstL us' (vc_type ci)).
Proof.
  intros Hbridge Hinf G. simpl in Hinf.
  destruct (get_constant env ps n us) as [d|err|why] eqn:Hget; simpl in Hinf; [|discriminate..].
  inversion Hinf; subst ty.
  destruct (@get_constant_sound_bridge env venv ps n us d Hbridge Hget)
    as [ci [us' [Hci [Htr_us [Hlen [Hwf _]]]]]].
  unfold get_constant in Hget.
  destruct (find_decl n env) as [d0|] eqn:Hfind; [|discriminate].
  assert (Hd : d0 = d).
  { destruct (decl_kind_of d0); try discriminate;
    destruct (Nat.eqb (List.length (decl_params d0)) (List.length us)); simpl in Hget; try discriminate;
    destruct (check_levels ps us); simpl in Hget; try discriminate;
    inversion Hget; reflexivity. }
  subst d0.
  exists d, ci, us'. repeat split; auto.
  - eapply TrExprS_const; [exact Hci | exact Htr_us |].
    rewrite (@TrLevels_length ps us us' Htr_us). exact Hlen.
  - eapply VHasType_const; [exact Hci | exact Hwf | exact Hlen].
Qed.

Theorem check_bridge_soundness fuel env venv ps g e ty G e' ty' :
  (forall et,
    infer fuel env ps g e = Accept et ->
    exists et',
      TrExpr venv ps G et et' /\
      VHasType venv (List.length ps) G e' et' /\
      (defeq fuel env ps g et ty = Accept true ->
       exists u, VIsDefEq venv (List.length ps) G et' ty' (VSort u))) ->
  check fuel env ps g e ty = Accept tt ->
  VHasType venv (List.length ps) G e' ty'.
Proof.
  intros Hmethods Hchk.
  destruct (@check_accepts_conversion fuel env ps g e ty Hchk) as [et [Hinf Hdef]].
  destruct (Hmethods et Hinf) as [et' [_ [Hhas Hconv]]].
  destruct (Hconv Hdef) as [u Heq].
  eapply VDF_defeqDF; [exact Heq | exact Hhas].
Qed.

Theorem checked_constant_extends_venv_wf fuel env venv n ps ty body kind env' ty' :
  VEnvWF venv ->
  VEnvClosed venv ->
  (find_decl n env = None -> venv_constants venv n = None) ->
  (check_header fuel env n ps ty = Accept tt ->
   VIsType venv (List.length ps) [] ty' /\ vclosed ty') ->
  checked_constant fuel env n ps ty body kind = Accept env' ->
  exists venv',
    venv_add_const venv n {| vc_uvars := List.length ps; vc_type := ty' |} = Some venv' /\
    VEnvWF venv' /\
    VEnvClosed venv' /\
    venv_ordered venv venv'.
Proof.
  intros Hwf Hcl Hfresh Hhdr Hadm.
  unfold checked_constant in Hadm.
  destruct (check_header fuel env n ps ty) as [[]|err|why] eqn:Hch; simpl in Hadm; [|discriminate..].
  assert (Hfind_none : find_decl n env = None).
  { unfold check_header in Hch. destruct (find_decl n env); [discriminate | reflexivity]. }
  pose proof (Hfresh Hfind_none) as Hvenv_none.
  pose proof (Hhdr eq_refl) as [Histype Hty_closed].
  unfold venv_add_const. rewrite Hvenv_none.
  eexists. split; [reflexivity |].
  split.
  - eapply (@VEnvWF_add_const venv n {| vc_uvars := List.length ps; vc_type := ty' |}); [exact Hwf | | ].
    + split; [exact Histype | exact Hty_closed].
    + unfold venv_add_const. rewrite Hvenv_none. reflexivity.
  - split.
    + constructor.
      * intros c ci. simpl. destruct (name_eqb c n).
        -- intros H. inversion H; subst. exact Hty_closed.
        -- apply (venv_closed_const Hcl).
      * intros df0 Hdf. simpl in Hdf. apply (venv_closed_defeq Hcl df0 Hdf).
    + eapply venv_add_const_ordered.
      unfold venv_add_const. rewrite Hvenv_none. reflexivity.
Qed.

Print Assumptions check_levels_sound_TrLevels.
Print Assumptions levels_equiv_sound_TrLevels.
Print Assumptions VHasType_vinst0_from_beta.
Print Assumptions TrExprS_has_type.
Print Assumptions TrExpr_monotonic_env.
Print Assumptions TrTyping_monotonic_env.
Print Assumptions get_constant_sound_bridge.
Print Assumptions infer_sort_sound_bridge.
Print Assumptions infer_const_sound_bridge.
Print Assumptions check_bridge_soundness.
Print Assumptions checked_constant_extends_venv_wf.
