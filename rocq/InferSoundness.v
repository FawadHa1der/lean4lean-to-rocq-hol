(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   Non-circular soundness of the executable type inference `infer_step`
   (Checker.v) with respect to the declarative judgment `VIsDefEq`
   (DeclarativeTyping.v), relative to explicit specifications of the WHNF and
   definitional-equality oracles.

   This corresponds to Lean4Lean/Verify/TypeChecker/InferType.lean, where the
   `inferType` correctness proof is likewise stated relative to (still partly
   `sorry`ed) WHNF and `isDefEq` correctness.  In contrast to
   CheckerSoundness.check_bridge_soundness -- whose hypothesis already contains
   the typing conclusion for the inferred term -- nothing here is assumed about
   `infer_step` itself:

   - `trE` is a *syntactic* (functional) translation of kernel expressions into
     `VExpr`; no typing is built into it, so the translation cannot be
     satisfied vacuously by an arbitrary well-typed term.
   - `MethodsSound` only constrains the reduction/conversion oracles
     `whnf_method`, `defeq_method` and `eager_defeq_method` that `infer_step`
     calls; the inference recursion itself is proved sound by induction on the
     expression.
   - `KernelEnvSyntacticBridge` relates the executable environment to a
     well-formed `VEnv` by exact syntactic translation of constant types.

   Fragment.  The theorem covers bound variables, sorts, constants, application,
   lambda, Pi and metadata in checking mode with a context of ordinary
   (non-let) bound variables.  Free variables, `let`, literals and projections
   are outside the translated fragment (`trE` returns `None`), and the
   remaining proof obligation -- that the concrete fuelled `checker` methods
   satisfy `MethodsSound` -- is stated as `CheckerMethodsSound` and is NOT
   discharged here (see GAP_ANALYSIS.md).  Zero axioms. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness EagerPolicy Checker SemanticModel
  DeclarativeTyping TypingLemmas.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Syntactic translation of levels and expressions                        *)
(* ========================================================================= *)

Fixpoint trLs (ps : list name) (us : list level) : option (list VLevel) :=
  match us with
  | [] => Some []
  | u :: us =>
      match vlevel_of_level ps u, trLs ps us with
      | Some u', Some us' => Some (u' :: us')
      | _, _ => None
      end
  end.

Fixpoint trE (ps : list name) (e : expr) : option VExpr :=
  match e with
  | EBVar i => Some (VBVar i)
  | ESort u => option_map VSort (vlevel_of_level ps u)
  | EConst c us => option_map (VConst c) (trLs ps us)
  | EApp f a =>
      match trE ps f, trE ps a with
      | Some f', Some a' => Some (VApp f' a')
      | _, _ => None
      end
  | ELam _ _ A b =>
      match trE ps A, trE ps b with
      | Some A', Some b' => Some (VLam A' b')
      | _, _ => None
      end
  | EPi _ _ A B =>
      match trE ps A, trE ps B with
      | Some A', Some B' => Some (VForallE A' B')
      | _, _ => None
      end
  | EMData a => trE ps a
  | EFVar _ | EMVar _ | ELet _ _ _ _ _ | ELit _ | EProj _ _ _ => None
  end.

Ltac inv_some :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : option_map _ ?x = Some _ |- _ =>
      let y := fresh "y" in let Hy := fresh "Hy" in
      destruct x as [y|] eqn:Hy; simpl in H; [|discriminate]
  end.

(* ========================================================================= *)
(* 2. The translation commutes with lifting and substitution                 *)
(* ========================================================================= *)

Lemma trE_lift ps e : forall n k e',
  trE ps e = Some e' -> trE ps (lift n k e) = Some (vliftN n k e').
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA v IHv b IHb nd|l|s i a IHa|a IHa];
    intros n k e' H; simpl in *; try discriminate.
  - inversion H; subst. simpl. unfold vliftVar.
    destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i k); try lia; reflexivity.
  - inv_some. reflexivity.
  - inv_some. reflexivity.
  - destruct (trE ps f) eqn:Hf; destruct (trE ps a) eqn:Ha; try discriminate.
    inversion H; subst. erewrite IHf, IHa by reflexivity. reflexivity.
  - destruct (trE ps A) eqn:HA; destruct (trE ps b) eqn:Hb; try discriminate.
    inversion H; subst. erewrite IHA, IHb by reflexivity. reflexivity.
  - destruct (trE ps A) eqn:HA; destruct (trE ps B) eqn:HB; try discriminate.
    inversion H; subst. erewrite IHA, IHB by reflexivity. reflexivity.
  - apply IHa. exact H.
Qed.

Lemma trE_subst ps e : forall k v e' v',
  trE ps e = Some e' -> trE ps v = Some v' ->
  trE ps (subst k v e) = Some (vinst e' v' k).
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s i a IHa|a IHa];
    intros k v e' v' H Hv; simpl in *; try discriminate.
  - inversion H; subst. simpl. unfold vinstVar.
    destruct (Nat.eqb_spec i k) as [Heq | Hne].
    + subst i. rewrite Nat.ltb_irrefl. destruct k as [|k].
      * rewrite vliftN_zero. exact Hv.
      * apply trE_lift. exact Hv.
    + destruct (Nat.ltb_spec i k); destruct (Nat.ltb_spec k i); try lia;
        apply Nat.eqb_neq in Hne; rewrite ?Hne; reflexivity.
  - inv_some. reflexivity.
  - inv_some. reflexivity.
  - destruct (trE ps f) eqn:Hf; destruct (trE ps a) eqn:Ha; try discriminate.
    inversion H; subst. erewrite IHf, IHa by eauto. reflexivity.
  - destruct (trE ps A) eqn:HA; destruct (trE ps b) eqn:Hb; try discriminate.
    inversion H; subst. erewrite IHA, IHb by eauto. reflexivity.
  - destruct (trE ps A) eqn:HA; destruct (trE ps B) eqn:HB; try discriminate.
    inversion H; subst. erewrite IHA, IHB by eauto. reflexivity.
  - eapply IHa; eassumption.
Qed.

Corollary trE_instantiate ps body value body' value' :
  trE ps body = Some body' -> trE ps value = Some value' ->
  trE ps (instantiate body value) = Some (vinst0 body' value').
Proof. intros. unfold instantiate, vinst0. apply trE_subst; assumption. Qed.

(* ========================================================================= *)
(* 3. The translation commutes with universe instantiation                   *)
(* ========================================================================= *)

Lemma name_eqb_sym a b : name_eqb a b = name_eqb b a.
Proof.
  destruct (name_eqb a b) eqn:H1; destruct (name_eqb b a) eqn:H2; auto.
  - apply name_eqb_eq in H1. subst. rewrite name_eqb_refl in H2. discriminate.
  - apply name_eqb_eq in H2. subst. rewrite name_eqb_refl in H1. discriminate.
Qed.

Lemma lookup_level_index params : forall us n i,
  index_of_name params n = Some i -> List.length us = List.length params ->
  lookup_level params us n = nth i us (LParam n).
Proof.
  induction params as [|p params IH]; intros us n i Hi Hlen; simpl in Hi; [discriminate|].
  destruct us as [|u us]; simpl in Hlen; [discriminate|].
  simpl. rewrite (name_eqb_sym p n).
  destruct (name_eqb n p).
  - inversion Hi; subst. reflexivity.
  - destruct (index_of_name params n) as [j|] eqn:Hj; simpl in Hi; [|discriminate].
    inversion Hi; subst. simpl. apply IH; [exact Hj | lia].
Qed.

Lemma trLs_length ps us us' : trLs ps us = Some us' -> List.length us' = List.length us.
Proof.
  revert us'. induction us as [|u us IH]; intros us' H; simpl in H.
  - inversion H. reflexivity.
  - destruct (vlevel_of_level ps u); destruct (trLs ps us) eqn:Hus; try discriminate.
    inversion H; subst. simpl. f_equal. apply IH. reflexivity.
Qed.

Lemma trLs_nth ps us : forall us' i d,
  trLs ps us = Some us' -> i < List.length us ->
  vlevel_of_level ps (nth i us d) = Some (nth i us' VLZero).
Proof.
  induction us as [|u us IH]; intros us' i d H Hi; simpl in *; [lia|].
  destruct (vlevel_of_level ps u) eqn:Hu; destruct (trLs ps us) eqn:Hus; try discriminate.
  inversion H; subst. destruct i as [|i]; simpl; [exact Hu |].
  apply IH; [reflexivity | lia].
Qed.

Lemma trL_subst ps params us us' u v :
  List.length us = List.length params ->
  trLs ps us = Some us' ->
  vlevel_of_level params u = Some v ->
  vlevel_of_level ps (subst_level params us u) = Some (vlevel_inst us' v).
Proof.
  intros Hlen Hus. revert v.
  induction u as [|u IH|a IHa b IHb|a IHa b IHb|n|n]; intros v Hv; simpl in *.
  - inversion Hv. reflexivity.
  - destruct (vlevel_of_level params u) eqn:Hu; simpl in Hv; [|discriminate].
    inversion Hv; subst. simpl. rewrite (IH _ eq_refl). reflexivity.
  - destruct (vlevel_of_level params a) eqn:Ha; destruct (vlevel_of_level params b) eqn:Hb;
      try discriminate.
    inversion Hv; subst. simpl. rewrite (IHa _ eq_refl), (IHb _ eq_refl). reflexivity.
  - destruct (vlevel_of_level params a) eqn:Ha; destruct (vlevel_of_level params b) eqn:Hb;
      try discriminate.
    inversion Hv; subst. simpl. rewrite (IHa _ eq_refl), (IHb _ eq_refl). reflexivity.
  - destruct (index_of_name params n) as [i|] eqn:Hi; simpl in Hv; [|discriminate].
    inversion Hv; subst. simpl.
    pose proof (index_of_name_lt params n Hi) as Hlt.
    rewrite (lookup_level_index Hi Hlen).
    apply trLs_nth; [exact Hus | lia].
  - discriminate.
Qed.

Lemma trLs_subst ps params us us' vs vs' :
  List.length us = List.length params ->
  trLs ps us = Some us' ->
  trLs params vs = Some vs' ->
  trLs ps (map (subst_level params us) vs) = Some (map (vlevel_inst us') vs').
Proof.
  intros Hlen Hus. revert vs'.
  induction vs as [|v vs IH]; intros vs' Hvs; simpl in *.
  - inversion Hvs. reflexivity.
  - destruct (vlevel_of_level params v) eqn:Hv; destruct (trLs params vs) eqn:Hvs';
      try discriminate.
    inversion Hvs; subst. simpl.
    rewrite (trL_subst Hlen Hus Hv), (IH _ eq_refl). reflexivity.
Qed.

Lemma trE_subst_levels ps params us us' e e' :
  List.length us = List.length params ->
  trLs ps us = Some us' ->
  trE params e = Some e' ->
  trE ps (subst_levels params us e) = Some (vinstL us' e').
Proof.
  intros Hlen Hus. revert e'.
  induction e as [i|x|x|u|c vs|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s i a IHa|a IHa];
    intros e' H; simpl in *; try discriminate.
  - inversion H. reflexivity.
  - destruct (vlevel_of_level params u) eqn:Hu; simpl in H; [|discriminate].
    inversion H; subst. simpl. rewrite (trL_subst Hlen Hus Hu). reflexivity.
  - destruct (trLs params vs) eqn:Hvs; simpl in H; [|discriminate].
    inversion H; subst. simpl. rewrite (trLs_subst Hlen Hus Hvs). reflexivity.
  - destruct (trE params f) eqn:Hf; destruct (trE params a) eqn:Ha; try discriminate.
    inversion H; subst. rewrite (IHf _ eq_refl), (IHa _ eq_refl). reflexivity.
  - destruct (trE params A) eqn:HA; destruct (trE params b) eqn:Hb; try discriminate.
    inversion H; subst. rewrite (IHA _ eq_refl), (IHb _ eq_refl). reflexivity.
  - destruct (trE params A) eqn:HA; destruct (trE params B) eqn:HB; try discriminate.
    inversion H; subst. rewrite (IHA _ eq_refl), (IHB _ eq_refl). reflexivity.
  - apply IHa. exact H.
Qed.

Lemma check_levels_trLs ps us :
  check_levels ps us = Accept tt ->
  exists us', trLs ps us = Some us' /\ Forall (vlevel_wf (List.length ps)) us'.
Proof.
  induction us as [|u us IH]; simpl.
  - intros _. exists []. split; [reflexivity | constructor].
  - destruct (check_level ps u) as [[]|err|why] eqn:Hu; simpl; try discriminate.
    intros Hrest.
    destruct (check_level_sound_vlevel ps u Hu) as [u' [Hu' Hwf]].
    destruct (IH Hrest) as [us' [Hus' Hwfs]].
    exists (u' :: us'). rewrite Hu', Hus'. split; [reflexivity | constructor; assumption].
Qed.

(* ========================================================================= *)
(* 4. Context translation                                                    *)
(* ========================================================================= *)

(* The executable bound context (innermost binder first) translates entrywise to
   the declarative context.  Only ordinary binders (no let values) occur. *)
Inductive TrBCtx (ps : list name) : list binding -> list VExpr -> Prop :=
| TrBCtx_nil : TrBCtx ps [] []
| TrBCtx_cons : forall ty bs T G,
    trE ps ty = Some T ->
    TrBCtx ps bs G ->
    TrBCtx ps ({| binding_type := ty; binding_value := None |} :: bs) (T :: G).

Lemma TrBCtx_lookup ps bs G :
  TrBCtx ps bs G ->
  forall i b, nth_error bs i = Some b ->
  exists T, trE ps (binding_type b) = Some T /\ VLookup G i (vliftN (S i) 0 T).
Proof.
  induction 1 as [| ty bs T G Hty Hbs IH]; intros i b Hb.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in Hb.
    + inversion Hb; subst b. exists T. simpl. split; [exact Hty |].
      change (vliftN 1 0 T) with (vlift T). constructor.
    + destruct (IH i b Hb) as [T' [HT' Hlk]]. exists T'. split; [exact HT' |].
      pose proof (VLookupSucc T Hlk) as Hs. unfold vlift in Hs.
      rewrite vliftN_comp in Hs. exact Hs.
Qed.

(* ========================================================================= *)
(* 5. Environment bridge and oracle specifications                           *)
(* ========================================================================= *)

(* Every admitted ordinary constant has a declarative counterpart whose type is
   the exact syntactic translation of the executable declaration type. *)
Record KernelEnvSyntacticBridge (env : environment) (venv : VEnv) : Prop := {
  kesb_wf : VEnvWF venv;
  kesb_constants : forall n d,
    find_decl n env = Some d ->
    match decl_kind_of d with
    | DUnsupported | DUnsafe _ | DPartial => True
    | _ =>
        exists ci,
          venv_constants venv n = Some ci /\
          vc_uvars ci = List.length (decl_params d) /\
          trE (decl_params d) (decl_type d) = Some (vc_type ci)
    end
}.

(* WHNF preserves the meaning of a well-typed term: the result is
   definitionally equal to the input at the input's type. *)
Definition WhnfSound (venv : VEnv) (ps : list name)
    (whnf : context -> expr -> result expr) : Prop :=
  forall g G t t' T V,
    TrBCtx ps (bound_context g) G ->
    VCtxWF venv (List.length ps) G ->
    whnf g t = Accept t' ->
    trE ps t = Some T ->
    VHasType venv (List.length ps) G T V ->
    exists T', trE ps t' = Some T' /\ VIsDefEq venv (List.length ps) G T T' V.

(* A positive conversion answer on two well-formed types is a declarative
   conversion at some sort. *)
Definition DefEqTypesSound (venv : VEnv) (ps : list name)
    (deq : context -> expr -> expr -> result bool) : Prop :=
  forall g G a b A B,
    TrBCtx ps (bound_context g) G ->
    VCtxWF venv (List.length ps) G ->
    deq g a b = Accept true ->
    trE ps a = Some A -> trE ps b = Some B ->
    VIsType venv (List.length ps) G A ->
    VIsType venv (List.length ps) G B ->
    exists u, VIsDefEq venv (List.length ps) G A B (VSort u).

Record MethodsSound (venv : VEnv) (ps : list name) (rec : methods) : Prop := {
  ms_whnf : WhnfSound venv ps (whnf_method rec);
  ms_defeq : DefEqTypesSound venv ps (defeq_method rec);
  ms_eager_defeq : DefEqTypesSound venv ps (eager_defeq_method rec)
}.

Lemma application_type_defeq_sound venv ps rec g G a dom aty D AT :
  MethodsSound venv ps rec ->
  TrBCtx ps (bound_context g) G ->
  VCtxWF venv (List.length ps) G ->
  application_type_defeq rec g a dom aty = Accept true ->
  trE ps dom = Some D -> trE ps aty = Some AT ->
  VIsType venv (List.length ps) G D ->
  VIsType venv (List.length ps) G AT ->
  exists u, VIsDefEq venv (List.length ps) G D AT (VSort u).
Proof.
  intros Hms Hctx HG Happ HD HAT HtD HtAT. unfold application_type_defeq in Happ.
  destruct (is_eager_reduce_argument a).
  - exact (ms_eager_defeq Hms Hctx HG Happ HD HAT HtD HtAT).
  - exact (ms_defeq Hms Hctx HG Happ HD HAT HtD HtAT).
Qed.

(* ========================================================================= *)
(* 6. Soundness of infer_step on the translated fragment                     *)
(* ========================================================================= *)

Section InferStep.
Variables (env : environment) (venv : VEnv) (ps : list name) (rec : methods) (fuel : nat).
Hypothesis Hbridge : KernelEnvSyntacticBridge env venv.
Hypothesis Hms : MethodsSound venv ps rec.

Let U := List.length ps.

Lemma bridge_wf : VEnvWF venv.
Proof. exact (kesb_wf Hbridge). Qed.

(* Converting along a WHNF step of a type. *)
Lemma whnf_retype g G E t T t' :
  TrBCtx ps (bound_context g) G -> VCtxWF venv U G ->
  VHasType venv U G E T -> trE ps t = Some T ->
  whnf_method rec g t = Accept t' ->
  exists T', trE ps t' = Some T' /\ VHasType venv U G E T'.
Proof.
  intros Hctx HG HE HT Hw.
  destruct (VIsDefEq_isType bridge_wf HG HE) as [w Hw'].
  destruct (ms_whnf Hms Hctx HG Hw HT Hw') as [T' [HT' Heq]].
  exists T'. split; [exact HT' |]. eapply VDF_defeqDF; [exact Heq | exact HE].
Qed.

Lemma const_sound g G n us ty e' :
  infer_step rec fuel env ps true g (EConst n us) = Accept ty ->
  trE ps (EConst n us) = Some e' ->
  exists ty', trE ps ty = Some ty' /\ VHasType venv U G e' ty'.
Proof.
  intros Hinf Htr. simpl in Hinf.
  destruct (get_constant env ps n us) as [d|err|why] eqn:Hget; simpl in Hinf; try discriminate.
  inversion Hinf; subst ty. clear Hinf.
  unfold get_constant in Hget.
  destruct (find_decl n env) as [d0|] eqn:Hfind; [|discriminate].
  pose proof (kesb_constants Hbridge Hfind) as Hdecl.
  destruct (decl_kind_of d0) eqn:Hkind; try discriminate.
  all: unfold require in Hget;
    destruct (Nat.eqb (List.length (decl_params d0)) (List.length us)) eqn:Harity;
    simpl in Hget; try discriminate.
  all: destruct (check_levels ps us) as [[]|err|why] eqn:Hlvls; simpl in Hget;
    try discriminate.
  all: inversion Hget; subst d0; clear Hget.
  all: destruct Hdecl as [ci [Hci [Huv Hty]]].
  all: destruct (check_levels_trLs Hlvls) as [us' [Hus' Hwf]].
  all: simpl in Htr; rewrite Hus' in Htr; simpl in Htr; inversion Htr; subst e'.
  all: apply Nat.eqb_eq in Harity.
  all: exists (vinstL us' (vc_type ci)); split.
  all: try (rewrite instantiate_levels_correct; apply trE_subst_levels;
              [ lia | exact Hus' | exact Hty ]).
  all: eapply VHasType_const; [ exact Hci | exact Hwf |].
  all: rewrite (trLs_length Hus'); lia.
Qed.

Theorem infer_step_sound e : forall g G ty e',
  TrBCtx ps (bound_context g) G ->
  VCtxWF venv U G ->
  infer_step rec fuel env ps true g e = Accept ty ->
  trE ps e = Some e' ->
  exists ty', trE ps ty = Some ty' /\ VHasType venv U G e' ty'.
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s i a IHa|a IHa];
    intros g G ty e' Hctx HG Hinf Htr; simpl in Htr; try discriminate.
  - (* bound variable *)
    simpl in Hinf. inversion Htr; subst e'.
    destruct (nth_error (bound_context g) i) as [bnd|] eqn:Hb; [|discriminate].
    inversion Hinf; subst ty.
    destruct (TrBCtx_lookup Hctx Hb) as [T [HT Hlk]].
    exists (vliftN (S i) 0 T). split; [exact (trE_lift (S i) 0 HT) |].
    apply VDF_bvar. exact Hlk.
  - (* sort *)
    simpl in Hinf.
    destruct (check_level ps u) as [[]|err|why] eqn:Hchk; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty.
    destruct (check_level_sound_vlevel ps u Hchk) as [u' [Hu' Hwf]].
    rewrite Hu' in Htr. simpl in Htr. inversion Htr; subst e'.
    exists (VSort (VLSucc u')). split.
    + simpl. rewrite Hu'. reflexivity.
    + apply VHasType_sort. exact Hwf.
  - (* constant *)
    exact (const_sound G Hinf Htr).
  - (* application *)
    destruct (trE ps f) as [F|] eqn:HF; destruct (trE ps a) as [Av|] eqn:HAv;
      try discriminate.
    inversion Htr; subst e'. clear Htr.
    simpl in Hinf.
    destruct (infer_step rec fuel env ps true g f) as [ft|err|why] eqn:Hft;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec g ft) as [ft'|err|why] eqn:Hwft; simpl in Hinf; try discriminate.
    destruct ft' as [| | | |? ?|? ?|? ?|n0 bi0 dom body| | | |]; try discriminate.
    destruct (infer_step rec fuel env ps true g a) as [aty|err|why] eqn:Hat;
      simpl in Hinf; try discriminate.
    destruct (application_type_defeq rec g a dom aty) as [ok|err|why] eqn:Hdef;
      simpl in Hinf; try discriminate.
    destruct ok; simpl in Hinf; [|discriminate].
    inversion Hinf; subst ty. clear Hinf.
    destruct (IHf g G ft F Hctx HG Hft eq_refl) as [FT [HFT HFty]].
    destruct (whnf_retype Hctx HG HFty HFT Hwft) as [PT [HPT HFpi]].
    simpl in HPT.
    destruct (trE ps dom) as [D|] eqn:HD; destruct (trE ps body) as [Bd|] eqn:HBd;
      try discriminate.
    inversion HPT; subst PT. clear HPT.
    pose proof (VIsDefEq_isType bridge_wf HG HFpi) as HtPi.
    destruct (VIsType_forallE_inv bridge_wf HtPi) as [HtD _].
    destruct (IHa g G aty Av Hctx HG Hat eq_refl) as [AT [HAT HAvty]].
    pose proof (VIsDefEq_isType bridge_wf HG HAvty) as HtAT.
    destruct (application_type_defeq_sound Hms Hctx HG Hdef HD HAT HtD HtAT) as [u Hconv].
    exists (vinst0 Bd Av). split.
    + apply trE_instantiate; assumption.
    + eapply VHasType_app; [exact HFpi |].
      eapply VDF_defeqDF; [exact (VDF_symm Hconv) | exact HAvty].
  - (* lambda *)
    destruct (trE ps A) as [Ad|] eqn:HA; destruct (trE ps b) as [Bd|] eqn:HBd;
      try discriminate.
    inversion Htr; subst e'. clear Htr.
    simpl in Hinf.
    destruct (infer_step rec fuel env ps true g A) as [dt|err|why] eqn:Hdt;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec g dt) as [dt'|err|why] eqn:Hwdt; simpl in Hinf; try discriminate.
    destruct dt' as [| | |u0| | | | | | | |]; simpl in Hinf; try discriminate.
    destruct (infer_step rec fuel env ps true (push_binding g A None) b) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    inversion Hinf; subst ty. clear Hinf.
    destruct (IHA g G dt Ad Hctx HG Hdt eq_refl) as [DT [HDT HAdty]].
    destruct (whnf_retype Hctx HG HAdty HDT Hwdt) as [S0 [HS0 HAsort]].
    simpl in HS0. destruct (vlevel_of_level ps u0) as [u0'|] eqn:Hu0; simpl in HS0;
      [|discriminate].
    inversion HS0; subst S0. clear HS0.
    assert (Hctx' : TrBCtx ps (bound_context (push_binding g A None)) (Ad :: G))
      by (simpl; constructor; assumption).
    assert (HG' : VCtxWF venv U (Ad :: G)) by (split; [exact HG | exists u0'; exact HAsort]).
    destruct (IHb _ (Ad :: G) bt Bd Hctx' HG' Hbt eq_refl) as [BT [HBT HBdty]].
    exists (VForallE Ad BT). split.
    + simpl. rewrite HA, HBT. reflexivity.
    + eapply VHasType_lam; [exact HAsort | exact HBdty].
  - (* Pi *)
    destruct (trE ps A) as [Ad|] eqn:HA; destruct (trE ps B) as [Bd|] eqn:HBd;
      try discriminate.
    inversion Htr; subst e'. clear Htr.
    simpl in Hinf.
    destruct (infer_step rec fuel env ps true g A) as [dt|err|why] eqn:Hdt;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec g dt) as [dt'|err|why] eqn:Hwdt; simpl in Hinf; try discriminate.
    destruct dt' as [| | |u0| | | | | | | |]; simpl in Hinf; try discriminate.
    destruct (infer_step rec fuel env ps true (push_binding g A None) B) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec (push_binding g A None) bt) as [bt'|err|why] eqn:Hwbt;
      simpl in Hinf; try discriminate.
    destruct bt' as [| | |v0| | | | | | | |]; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty. clear Hinf.
    destruct (IHA g G dt Ad Hctx HG Hdt eq_refl) as [DT [HDT HAdty]].
    destruct (whnf_retype Hctx HG HAdty HDT Hwdt) as [S0 [HS0 HAsort]].
    simpl in HS0. destruct (vlevel_of_level ps u0) as [u0'|] eqn:Hu0; simpl in HS0;
      [|discriminate].
    inversion HS0; subst S0. clear HS0.
    assert (Hctx' : TrBCtx ps (bound_context (push_binding g A None)) (Ad :: G))
      by (simpl; constructor; assumption).
    assert (HG' : VCtxWF venv U (Ad :: G)) by (split; [exact HG | exists u0'; exact HAsort]).
    destruct (IHB _ (Ad :: G) bt Bd Hctx' HG' Hbt eq_refl) as [BT [HBT HBdty]].
    destruct (whnf_retype Hctx' HG' HBdty HBT Hwbt) as [S1 [HS1 HBsort]].
    simpl in HS1. destruct (vlevel_of_level ps v0) as [v0'|] eqn:Hv0; simpl in HS1;
      [|discriminate].
    inversion HS1; subst S1. clear HS1.
    exists (VSort (VLIMax u0' v0')). split.
    + simpl. rewrite Hu0, Hv0. reflexivity.
    + eapply VHasType_forallE; [exact HAsort | exact HBsort].
  - (* metadata *)
    simpl in Hinf. exact (IHa g G ty e' Hctx HG Hinf Htr).
Qed.

(* Checking = inference followed by a positive conversion answer. *)
Theorem check_step_sound g G e ty et e' T :
  TrBCtx ps (bound_context g) G ->
  VCtxWF venv U G ->
  infer_step rec fuel env ps true g e = Accept et ->
  defeq_method rec g et ty = Accept true ->
  trE ps e = Some e' -> trE ps ty = Some T ->
  VIsType venv U G T ->
  VHasType venv U G e' T.
Proof.
  intros Hctx HG Hinf Hdef He HT HtT.
  destruct (infer_step_sound Hctx HG Hinf He) as [ET [HET Hety]].
  pose proof (VIsDefEq_isType bridge_wf HG Hety) as HtET.
  destruct (ms_defeq Hms Hctx HG Hdef HET HT HtET HtT) as [u Hconv].
  eapply VDF_defeqDF; [exact Hconv | exact Hety].
Qed.

End InferStep.

(* ========================================================================= *)
(* 7. The public `infer` entry point                                         *)
(* ========================================================================= *)

(* The remaining (undischarged) obligation: the concrete fuelled methods
   satisfy the oracle specifications at every fuel level. *)
Definition CheckerMethodsSound (env : environment) (venv : VEnv) (ps : list name) : Prop :=
  forall n, MethodsSound venv ps (checker n env ps).

Theorem infer_sound fuel env venv ps g G e ty e' :
  KernelEnvSyntacticBridge env venv ->
  CheckerMethodsSound env venv ps ->
  TrBCtx ps (bound_context g) G ->
  VCtxWF venv (List.length ps) G ->
  infer fuel env ps g e = Accept ty ->
  trE ps e = Some e' ->
  exists ty', trE ps ty = Some ty' /\ VHasType venv (List.length ps) G e' ty'.
Proof.
  intros Hbridge Hms Hctx HG Hinf He.
  unfold infer in Hinf. destruct fuel as [|n]; simpl in Hinf; [discriminate|].
  exact (infer_step_sound Hbridge (Hms n) Hctx HG Hinf He).
Qed.

(* ========================================================================= *)
(* 8. Non-vacuity: a concrete executable method record satisfying the spec   *)
(* ========================================================================= *)

(* A deliberately weak but executable oracle: WHNF is the identity and
   conversion is kernel alpha-equality `expr_eqb`.  It satisfies MethodsSound
   unconditionally, so `infer_step` instantiated with it is an executable type
   inferencer whose soundness below depends on no assumption other than the
   syntactic environment bridge.  This shows the specification is satisfiable
   and the main theorem is not vacuous. *)

Lemma level_eqb_true u v : level_eqb u v = true -> u = v.
Proof.
  revert v. induction u as [|u IH|a IHa b IHb|a IHa b IHb|n|n];
    intros [|v|c d|c d|m|m] H; simpl in H; try discriminate; try reflexivity.
  - f_equal. apply IH. exact H.
  - apply andb_true_iff in H as [H1 H2]. f_equal; [apply IHa | apply IHb]; assumption.
  - apply andb_true_iff in H as [H1 H2]. f_equal; [apply IHa | apply IHb]; assumption.
  - f_equal. apply name_eqb_eq. exact H.
  - f_equal. apply name_eqb_eq. exact H.
Qed.

Lemma list_level_eqb_true us : forall vs, list_eqb level_eqb us vs = true -> us = vs.
Proof.
  induction us as [|u us IH]; intros [|v vs] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2].
  rewrite (level_eqb_true H1), (IH vs H2). reflexivity.
Qed.

Lemma expr_eqb_trE ps a : forall b, expr_eqb a b = true -> trE ps a = trE ps b.
Proof.
  induction a as [i|x|x|u|c us|f IHf x IHx|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s i x IHx|x IHx];
    intros [j|y1|y2|v|d vs|g z|n1 b1 C1 c1|n2 b2 C2 c2|n3 C3 w3 c3 nd3|l'|s' j' z'|z''] H;
    simpl in H; try discriminate; simpl; try reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - rewrite (level_eqb_true H). reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    rewrite (name_eqb_eq _ _ H1), (list_level_eqb_true H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHf _ H1), (IHx _ H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHA _ H1), (IHb _ H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHA _ H1), (IHB _ H2). reflexivity.
  - apply IHx. exact H.
Qed.

Definition syntactic_methods : methods :=
  {| infer_method := fun _ _ => Decline UnsupportedExpression;
     infer_type_method := fun _ _ => Decline UnsupportedExpression;
     whnf_method := fun _ e => Accept e;
     whnf_core_method := fun _ _ e => Accept e;
     defeq_method := fun _ a b => Accept (expr_eqb a b);
     method_mode := NormalReduction;
     eager_defeq_method := fun _ a b => Accept (expr_eqb a b) |}.

Lemma syntactic_defeq_sound venv ps :
  DefEqTypesSound venv ps (fun _ a b => Accept (expr_eqb a b)).
Proof.
  intros g G a b A B _ _ Hdef HA HB [u Hu] _.
  inversion Hdef as [Heqb]. rewrite (expr_eqb_trE ps Heqb) in HA.
  rewrite HA in HB. inversion HB; subst B.
  exists u. exact Hu.
Qed.

Theorem syntactic_methods_sound venv ps : MethodsSound venv ps syntactic_methods.
Proof.
  constructor.
  - intros g G t t' T V _ _ Hw HT HTV. simpl in Hw. inversion Hw; subst t'.
    exists T. split; [exact HT | exact HTV].
  - apply syntactic_defeq_sound.
  - apply syntactic_defeq_sound.
Qed.

(* Unconditional (relative only to the syntactic environment bridge) soundness
   of the executable inferencer `infer_step syntactic_methods`. *)
Corollary syntactic_infer_sound env venv ps fuel g G e ty e' :
  KernelEnvSyntacticBridge env venv ->
  TrBCtx ps (bound_context g) G ->
  VCtxWF venv (List.length ps) G ->
  infer_step syntactic_methods fuel env ps true g e = Accept ty ->
  trE ps e = Some e' ->
  exists ty', trE ps ty = Some ty' /\ VHasType venv (List.length ps) G e' ty'.
Proof.
  intros Hbridge Hctx HG Hinf He.
  exact (infer_step_sound Hbridge (syntactic_methods_sound venv ps) Hctx HG Hinf He).
Qed.

Print Assumptions trE_subst.
Print Assumptions trE_subst_levels.
Print Assumptions TrBCtx_lookup.
Print Assumptions infer_step_sound.
Print Assumptions check_step_sound.
Print Assumptions infer_sound.
Print Assumptions syntactic_methods_sound.
Print Assumptions syntactic_infer_sound.
