(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end soundness of the executable kernel type checker (`Checker.v`)
   and equivalence/defeq caches (`DefEqCache.v`) against the declarative typing
   judgment `VIsDefEq` (`DeclarativeTyping.v`) via the complete 12-constructor
   translation relation `VTrExpr` (`VerifyExpr.v`).

   Covers all upstream `Lean4Lean/Verify/TypeChecker/` modules:
   - `Reduce.lean`: beta, delta, native/Nat primitives, quotient, recursor iota
     (+ K-rule and structure-eta `toConstructor`), projection iota.
   - `WHNF.lean`: `whnf_core_step`, `whnf_round_step`, `whnf_loop`, `whnf_step`.
   - `InferType.lean`: all 13 `expr` constructors in both `checking = true` and
     `checking = false` modes (incl. `EFVar`, `ELet`, `ELit`, `EProj`).
   - `IsDefEq.lean`: quick checks, true shortcut, proof irrelevance, Nat offset,
     lazy delta + hint priority + delta congruence + opposite projection,
     lazy delta projection, head comparison, lambda eta, structure eta,
     unit-like eta, string literal expansion, `core_eta_expand`.
   - Master fuel induction `checker_mode_sound` discharging `FullMethodsSound`
     for all 6 methods of `checker_mode` simultaneously, discharging
     `InferSoundness.CheckerMethodsSound`, and composing with `DefEqCache.v`.

   Zero axioms, zero `Admitted`. *)

From Stdlib Require Import List Bool Arith PeanoNat NArith Lia String.
From LeanPort Require Import
  Syntax Universes UniverseSoundness EagerPolicy NatProbeDispatch WhnfPolicy
  Checker SemanticModel DeclarativeTyping TypingLemmas StrongTyping
  PatternConfluence CheckerSoundness InferSoundness DefEqCache VerifyExpr.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Checker-Specific Translation Helpers                                   *)
(* ========================================================================= *)

Lemma VTrExpr_defeq_r env venv ps L e e1 e2 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L e e1 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) e1 e2 ->
  VTrExpr env venv ps L e e2.
Proof.
  intros Hves HwfL [e0 [Htr H01]] H12.
  exists e0. split; [exact Htr |].
  eapply VIsDefEqU_trans;
    [exact (ves_wf Hves) | exact (ves_inj Hves) | exact (VLCtxWF_to_VCtxWF HwfL) | exact H01 | exact H12].
Qed.

Lemma VHasType_conv_U env U G e A B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VIsDefEqU env U G A B ->
  VHasType env U G e B.
Proof.
  intros Hwf Hinj HG He [T HAB].
  destruct (VIsDefEq_isType Hwf HG He) as [u Hu].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_l HAB)) as [v Hconv].
  eapply VDF_defeqDF; [eapply VDF_defeqDF; [exact (VDF_symm Hconv) | exact HAB] | exact He].
Qed.

Lemma VIsDefEqU_symm env U G e1 e2 :
  VIsDefEqU env U G e1 e2 -> VIsDefEqU env U G e2 e1.
Proof.
  intros [A H]. exists A. apply VDF_symm. exact H.
Qed.

Lemma VIsDefEqU_refl_l env U G e1 e2 :
  VIsDefEqU env U G e1 e2 -> VExprWF env U G e1.
Proof.
  intros [A H]. exists A. exact (VIsDefEq_refl_l H).
Qed.

Lemma VIsDefEqU_refl_r env U G e1 e2 :
  VIsDefEqU env U G e1 e2 -> VExprWF env U G e2.
Proof.
  intros [A H]. exists A. exact (VIsDefEq_refl_r H).
Qed.

Lemma VIsDefEqU_hasType_r env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VHasType env U G e1 A ->
  VIsDefEqU env U G e1 e2 ->
  VHasType env U G e2 A.
Proof.
  intros Hwf Hinj HG Hty [B H12].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG Hty (VIsDefEq_refl_l H12)) as [u Hu].
  eapply VIsDefEq_refl_r. eapply VDF_defeqDF; [exact (VDF_symm Hu) | exact H12].
Qed.

Lemma vapps_wf_prefix env U G f xs ys :
  VEnvWF env ->
  VCtxWF env U G ->
  VExprWF env U G (vapps f (xs ++ ys)) ->
  VExprWF env U G (vapps f xs).
Proof.
  intros Hwf HG H.
  rewrite vapps_app in H.
  revert H. generalize (vapps f xs) as h.
  induction ys as [|y rest IH]; intros h Hh; [exact Hh |].
  simpl in Hh.
  destruct (IH (VApp h y) Hh) as [T HT].
  destruct (VHasType_app_inv Hwf HG HT) as [A [B [Hh' _]]].
  exists (VForallE A B). exact Hh'.
Qed.

Lemma vapps_defeq_congr_l env U G :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  forall xs ys f1 f2,
    VExprWF env U G (vapps f1 xs) ->
    VIsDefEqU env U G f1 f2 ->
    Forall2 (VIsDefEqU env U G) xs ys ->
    VExprWF env U G (vapps f2 ys) /\
    VIsDefEqU env U G (vapps f1 xs) (vapps f2 ys).
Proof.
  intros Hwf Hinj HG xs.
  induction xs as [|x xs IH]; intros ys f1 f2 Hwf1 Hf Hargs;
    inversion Hargs as [| ? y ? l' Hxy Hrest]; subst; simpl in *.
  - split; [exact (VIsDefEqU_refl_r Hf) | exact Hf].
  - assert (Hwf_app1 : VExprWF env U G (VApp f1 x)).
    { change (VApp f1 x) with (vapps (VApp f1 x) []).
      eapply vapps_wf_prefix with (ys := xs); [exact Hwf | exact HG | exact Hwf1]. }
    destruct Hwf_app1 as [T1 HT1].
    destruct (VHasType_app_inv Hwf HG HT1) as [A1 [B1 [Hf1 Hx1]]].
    destruct Hf as [Tf Hf12].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hf1 (VIsDefEq_refl_l Hf12)) as [uf Hcf].
    destruct Hxy as [Tx Hxy'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hx1 (VIsDefEq_refl_l Hxy')) as [ux Hcx].
    assert (Happ : VIsDefEqU env U G (VApp f1 x) (VApp f2 y)).
    { exists (vinst0 B1 x).
      eapply VDF_appDF;
        [eapply VDF_defeqDF; [exact (VDF_symm Hcf) | exact Hf12]
        | eapply VDF_defeqDF; [exact (VDF_symm Hcx) | exact Hxy']]. }
    exact (IH l' (VApp f1 x) (VApp f2 y) Hwf1 Happ Hrest).
Qed.

Lemma VTrExpr_has_type env venv ps L e e' :
  VTrExpr env venv ps L e e' ->
  VExprWF venv (List.length ps) (vl_ctx L) e'.
Proof.
  intros [e0 [_ H]]. exact (VIsDefEqU_refl_r H).
Qed.

Lemma core_level_positive_eval ps u : forall u',
  vlevel_of_level ps u = Some u' ->
  core_level_positive u = true ->
  1 <= vlevel_eval [] u'.
Proof.
  induction u as [|u IH|a IHa b IHb|a IHa b IHb|n|n]; intros u' Hu Hp;
    simpl in *; try discriminate.
  - destruct (vlevel_of_level ps u) as [v|] eqn:Hv; simpl in Hu; [|discriminate].
    inversion Hu; subst. simpl. lia.
  - destruct (vlevel_of_level ps a) as [va|] eqn:Ha;
    destruct (vlevel_of_level ps b) as [vb|] eqn:Hb; try discriminate.
    inversion Hu; subst. simpl.
    apply orb_true_iff in Hp as [Hpa | Hpb].
    + specialize (IHa va eq_refl Hpa). lia.
    + specialize (IHb vb eq_refl Hpb). lia.
  - destruct (vlevel_of_level ps a) as [va|] eqn:Ha;
    destruct (vlevel_of_level ps b) as [vb|] eqn:Hb; try discriminate.
    inversion Hu; subst. simpl.
    specialize (IHb vb eq_refl Hp). unfold vlevel_imax_nat.
    destruct (vlevel_eval [] vb); lia.
Qed.

Lemma core_level_positive_sound ps u u' :
  vlevel_of_level ps u = Some u' ->
  core_level_positive u = true ->
  ~ vlevel_equiv u' VLZero.
Proof.
  intros Hu Hp Heq.
  pose proof (core_level_positive_eval Hu Hp) as Hge.
  specialize (Heq []). simpl in Heq. lia.
Qed.

Lemma TrLevels_of_trLs ps us : forall us',
  trLs ps us = Some us' -> TrLevels ps us us'.
Proof.
  induction us as [|u r IH]; intros us' H; simpl in H.
  - inversion H; subst. constructor.
  - destruct (vlevel_of_level ps u) as [u'|] eqn:Hu;
    destruct (trLs ps r) as [r'|] eqn:Hr; try discriminate.
    inversion H; subst. constructor; [exact Hu | apply IH; reflexivity].
Qed.

Lemma check_levels_TrLevels ps us :
  check_levels ps us = Accept tt ->
  exists us', TrLevels ps us us' /\ Forall (vlevel_wf (List.length ps)) us'.
Proof.
  intros H. destruct (check_levels_trLs H) as [us' [Hus' Hwf]].
  exists us'. split; [apply TrLevels_of_trLs; exact Hus' | exact Hwf].
Qed.

Lemma get_constant_sound env venv ps L n us d :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  get_constant env ps n us = Accept d ->
  exists ci us',
    find_decl n env = Some d /\
    match decl_kind_of d with
    | DUnsupported | DUnsafe _ | DPartial => False
    | _ => True
    end /\
    venv_constants venv n = Some ci /\
    vc_uvars ci = List.length (decl_params d) /\
    List.length us = vc_uvars ci /\
    TrLevels ps us us' /\
    Forall (vlevel_wf (List.length ps)) us' /\
    VTrExpr env venv ps L (instantiate_levels (decl_params d) us (decl_type d))
      (vinstL us' (vc_type ci)) /\
    VHasType venv (List.length ps) (vl_ctx L) (VConst n us') (vinstL us' (vc_type ci)).
Proof.
  intros Hves HwfL Hget.
  unfold get_constant in Hget.
  destruct (find_decl n env) as [d0|] eqn:Hfind; [|discriminate].
  pose proof (ves_constants Hves Hfind) as Hdecl.
  destruct (decl_kind_of d0) eqn:Hkind; try discriminate.
  all: unfold require in Hget;
    destruct (Nat.eqb (List.length (decl_params d0)) (List.length us)) eqn:Har;
    simpl in Hget; try discriminate.
  all: destruct (check_levels ps us) as [[]|err|why] eqn:Hlv; simpl in Hget; try discriminate.
  all: inversion Hget; subst d0; clear Hget.
  all: apply Nat.eqb_eq in Har.
  all: destruct Hdecl as [ci [Hci [Huv [Hty_tr [Hty_is Hty_cl]]]]].
  all: destruct (check_levels_TrLevels Hlv) as [us' [Hus' Hwf_us]].
  all: exists ci, us'; repeat split; try assumption; try lia; try (rewrite Hkind; exact I).
  all: try (rewrite instantiate_levels_correct;
            apply VTrExpr_closed_to_any; [exact (ves_wf Hves) |];
            eapply VTrExpr_subst_levels; [lia | exact Hus' | exact Hty_tr]).
  all: eapply VHasType_const; [exact Hci | exact Hwf_us | rewrite <- (TrLevels_length Hus'); lia].
Qed.

(* Free-context weakening and bound-closedness *)
Lemma vl_lookup_free_in fs n d r :
  vl_lookup_free fs n d = Some r -> In n (map fst fs).
Proof.
  revert d r.
  induction fs as [|[m [A|A v]] rest IH]; intros d r H; simpl in *; try discriminate.
  - destruct (name_eqb n m) eqn:Em.
    + left. symmetry. apply name_eqb_eq. exact Em.
    + right. eapply IH; exact H.
  - destruct (name_eqb n m) eqn:Em.
    + left. symmetry. apply name_eqb_eq. exact Em.
    + right. eapply IH; exact H.
Qed.

Lemma VTrExprS_bound_closed env venv ps L e e' :
  VTrExprS env venv ps L e e' ->
  forall m, lift m (List.length (vl_bound L)) e = e.
Proof.
  induction 1; intros m; simpl in *; try reflexivity;
    try (rewrite IHVTrExprS1, IHVTrExprS2; reflexivity);
    try (rewrite IHVTrExprS1, IHVTrExprS2, IHVTrExprS3; reflexivity);
    try (rewrite IHVTrExprS; reflexivity).
  - assert (Hlt : i < List.length (vl_bound L)) by (eapply vl_lookup_bound_lt; exact H).
    replace (List.length (vl_bound L) <=? i) with false
      by (symmetry; apply Nat.leb_gt; exact Hlt).
    reflexivity.
Qed.

Lemma VTrExpr_bound_closed env venv ps fs e e' m :
  VTrExpr env venv ps {| vl_free := fs; vl_bound := [] |} e e' ->
  lift m 0 e = e.
Proof.
  intros [e0 [Htr _]]. exact (VTrExprS_bound_closed Htr m).
Qed.

Fixpoint vl_lift_bound_at (n : nat) (bs : list VLCtxEntry) : list VLCtxEntry :=
  match bs with
  | [] => []
  | VLLam A :: r =>
      VLLam (vliftN n (List.length (vlentries_to_ctx r)) A) :: vl_lift_bound_at n r
  | VLLet A v :: r =>
      VLLet (vliftN n (List.length (vlentries_to_ctx r)) A)
            (vliftN n (List.length (vlentries_to_ctx r)) v) :: vl_lift_bound_at n r
  end.

Lemma vl_lift_bound_at_len n bs :
  List.length (vlentries_to_ctx (vl_lift_bound_at n bs)) = List.length (vlentries_to_ctx bs).
Proof.
  induction bs as [|[A|A v] r IH]; simpl; auto.
Qed.

Lemma vl_lift_bound_at_VCtxLiftN entry bs base :
  let n := match entry with VLLam _ => 1 | VLLet _ _ => 0 end in
  let base' := match entry with VLLam A => A :: base | VLLet _ _ => base end in
  VCtxLiftN n (List.length (vlentries_to_ctx bs))
    (vlentries_to_ctx bs ++ base)
    (vlentries_to_ctx (vl_lift_bound_at n bs) ++ base').
Proof.
  intros n base'.
  induction bs as [|[A|A v] r IH]; simpl.
  - unfold n, base'. destruct entry as [A0|A0 v0]; simpl.
    + exact (VCtxLiftN_app_prefix [A0] base).
    + exact (VCtxLiftN_app_prefix [] base).
  - constructor. exact IH.
  - exact IH.
Qed.

Lemma vl_lift_bound_at_lookup n bs : forall i d e ty,
  vl_lookup_bound bs i d = Some (e, ty) ->
  vl_lookup_bound (vl_lift_bound_at n bs) i d =
    Some (vliftN n (List.length (vlentries_to_ctx bs) + d) e,
          vliftN n (List.length (vlentries_to_ctx bs) + d) ty).
Proof.
  induction bs as [|[A|A v] r IH]; intros [|i] d e ty Hlk; simpl in *; try discriminate.
  - inversion Hlk; subst e ty; clear Hlk. f_equal. f_equal.
    + simpl. unfold vliftVar.
      destruct (Nat.ltb_spec d (S (List.length (vlentries_to_ctx r) + d))); [reflexivity | lia].
    + replace (S (List.length (vlentries_to_ctx r) + d))
        with (S d + List.length (vlentries_to_ctx r)) by lia.
      rewrite vliftN_comm by lia. reflexivity.
  - replace (S (List.length (vlentries_to_ctx r) + d))
      with (List.length (vlentries_to_ctx r) + S d) by lia.
    exact (IH i (S d) e ty Hlk).
  - inversion Hlk; subst e ty; clear Hlk. f_equal. f_equal;
      replace (List.length (vlentries_to_ctx r) + d)
        with (d + List.length (vlentries_to_ctx r)) by lia;
      rewrite vliftN_comm by lia; reflexivity.
  - exact (IH i d e ty Hlk).
Qed.

Lemma VTrExprS_weak_free_one_L env venv ps :
  VEnvClosed venv ->
  forall L e e',
    VTrExprS env venv ps L e e' ->
    forall m entry,
      ~ In m (map fst (vl_free L)) ->
      let n := match entry with VLLam _ => 1 | VLLet _ _ => 0 end in
      let k := List.length (vlentries_to_ctx (vl_bound L)) in
      VTrExprS env venv ps
        {| vl_free := (m, entry) :: vl_free L;
           vl_bound := vl_lift_bound_at n (vl_bound L) |}
        e (vliftN n k e').
Proof.
  intros Hcl L e e' Htr.
  induction Htr as
    [ L i e1 ty1 Hlk Hty
    | L nm e1 ty1 Hlk Hty
    | L u u' Htr_u
    | L c ci us us' Hci Htr_us Hlen_us
    | L f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L nm ty val body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L owner idx0 a a' proj' field_ty Htr_a IHa Hproj
    | L n0 Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros m entry Hfresh n k;
    assert (W : VCtxLiftN n k (vl_ctx L)
                  (vl_ctx {| vl_free := (m, entry) :: vl_free L;
                             vl_bound := vl_lift_bound_at n (vl_bound L) |}))
      by (unfold vl_ctx, vl_free_ctx, n, k; simpl;
          destruct entry as [A0|A0 v0];
          [exact (vl_lift_bound_at_VCtxLiftN (VLLam A0) (vl_bound L) (vl_free_ctx (vl_free L)))
          | exact (vl_lift_bound_at_VCtxLiftN (VLLet A0 v0) (vl_bound L) (vl_free_ctx (vl_free L)))]);
    simpl in *.
  - pose proof (vl_lift_bound_at_lookup n Hlk) as Hlk'.
    rewrite Nat.add_0_r in Hlk'.
    eapply VTrExprS_bvar; [exact Hlk' | exact (VIsDefEq_weakN Hcl Hty W)].
  - assert (Hin : In nm (map fst (vl_free L))) by (eapply vl_lookup_free_in; exact Hlk).
    assert (Hne : name_eqb nm m = false).
    { destruct (name_eqb nm m) eqn:E; [|reflexivity].
      apply name_eqb_eq in E. subst nm. contradiction. }
    assert (Hlk' : vl_fvar {| vl_free := (m, entry) :: vl_free L;
                              vl_bound := vl_lift_bound_at n (vl_bound L) |} nm =
                   Some (vliftN n k e1, vliftN n k ty1)).
    { unfold vl_fvar, vl_bound_lams in *. simpl in *.
      rewrite vl_lift_bound_at_len.
      unfold n, k in *.
      destruct entry as [A0|A0 v0]; simpl; rewrite Hne.
      - pose proof (vl_lookup_free_shift_at 1 (Nat.le_refl _) Hlk) as Hs.
        exact Hs.
      - rewrite !vliftN_zero. exact Hlk. }
    eapply VTrExprS_fvar; [exact Hlk' | exact (VIsDefEq_weakN Hcl Hty W)].
  - constructor; exact Htr_u.
  - econstructor; eassumption.
  - eapply VTrExprS_app with (A := vliftN n k A) (B := vliftN n (S k) B);
      [exact (VIsDefEq_weakN Hcl Hf_ty W) | exact (VIsDefEq_weakN Hcl Ha_ty W) |
       exact (IHf m entry Hfresh) | exact (IHa m entry Hfresh)].
  - eapply VTrExprS_lam.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_weakN Hcl Hu W).
    + exact (IHA m entry Hfresh).
    + exact (IHb m entry Hfresh).
  - eapply VTrExprS_pi.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_weakN Hcl Hu W).
    + destruct Hbody_is as [v Hv]. exists v. exact (VIsDefEq_weakN Hcl Hv (VCtxLiftN_succ _ W)).
    + exact (IHA m entry Hfresh).
    + exact (IHB m entry Hfresh).
  - eapply VTrExprS_let with (ty' := vliftN n k ty') (val' := vliftN n k val');
      [exact (VIsDefEq_weakN Hcl Hval_ty W) |
       exact (IHA m entry Hfresh) | exact (IHv m entry Hfresh) | exact (IHb m entry Hfresh)].
  - eapply VTrExprS_proj; [exact (IHa m entry Hfresh) | exact (VTrProj_weakN Hcl W Hproj)].
  - rewrite vliftN_natLit.
    eapply VTrExprS_natlit; [exact Hnat |].
    pose proof (VIsDefEq_weakN Hcl Hnty W) as Hw. rewrite vliftN_natLit in Hw. exact Hw.
  - rewrite (vliftN_trStrLit n k Htrs).
    eapply VTrExprS_strlit; [exact Hstr | exact Htrs |].
    pose proof (VIsDefEq_weakN Hcl Hsty W) as Hw. rewrite (vliftN_trStrLit n k Htrs) in Hw. exact Hw.
  - constructor. exact (IHa m entry Hfresh).
Qed.

Lemma VTrExpr_weak_free_one env venv ps fs m entry e e' :
  VEnvClosed venv ->
  ~ In m (map fst fs) ->
  VTrExpr env venv ps {| vl_free := fs; vl_bound := [] |} e e' ->
  let n := match entry with VLLam _ => 1 | VLLet _ _ => 0 end in
  VTrExpr env venv ps {| vl_free := (m, entry) :: fs; vl_bound := [] |} e (vliftN n 0 e').
Proof.
  intros Hcl Hfresh [e0 [Htr [A Hdef]]] n.
  exists (vliftN n 0 e0). split.
  - exact (VTrExprS_weak_free_one_L Hcl Htr entry Hfresh).
  - exists (vliftN n 0 A).
    eapply VIsDefEq_weakN; [exact Hcl | exact Hdef |].
    unfold vl_ctx, vl_free_ctx, n; simpl; destruct entry as [A0|A0 v0]; simpl.
    + exact (VCtxLiftN_app_prefix [A0] (vlentries_to_ctx (map snd fs))).
    + exact (VCtxLiftN_app_prefix [] (vlentries_to_ctx (map snd fs))).
Qed.

(* Lookup lemmas for bound_context and free_context under VTrCtx *)
Lemma VTrBoundCtx_lookup env venv ps fs' bs bs' :
  VEnvClosed venv ->
  VTrBoundCtx env venv ps fs' bs bs' ->
  forall i b,
    nth_error bs i = Some b ->
    exists e' ty',
      vl_bvar {| vl_free := fs'; vl_bound := bs' |} i = Some (e', ty') /\
      VTrExpr env venv ps {| vl_free := fs'; vl_bound := bs' |}
        (lift (S i) 0 (binding_type b)) ty' /\
      (forall v, binding_value b = Some v ->
        VTrExpr env venv ps {| vl_free := fs'; vl_bound := bs' |}
          (lift (S i) 0 v) e').
Proof.
  intros Hcl Hbc.
  induction Hbc as
    [
    | ty bs0 ty' bs0' Hbc IH Hty His
    | ty val bs0 ty' val' bs0' Hbc IH Hty Hval Hhas ];
    intros [|i] b Hnth; simpl in *; try discriminate.
  - inversion Hnth; subst b; clear Hnth. simpl.
    exists (VBVar 0), (vlift ty'). repeat split.
    + exact (VTrExpr_lift_lam ty' Hcl Hty).
    + intros v Hv. discriminate.
  - destruct (IH i b Hnth) as [e' [ty0' [Hlk [Hty0 Hval0]]]].
    exists (vlift e'), (vlift ty0'). repeat split.
    + unfold vl_bvar in *. simpl in *.
      exact (vl_lookup_bound_shift_at 1 (Nat.le_0_l 0) Hlk).
    + replace (S (S i)) with (1 + S i) by lia. rewrite <- lift_lift_eq.
      exact (VTrExpr_lift_lam ty' Hcl Hty0).
    + intros v Hv. replace (S (S i)) with (1 + S i) by lia. rewrite <- lift_lift_eq.
      exact (VTrExpr_lift_lam ty' Hcl (Hval0 v Hv)).
  - inversion Hnth; subst b; clear Hnth. simpl.
    exists val', ty'. repeat split.
    + unfold vl_bvar. simpl. rewrite !vliftN_zero. reflexivity.
    + exact (VTrExpr_lift_let ty' val' Hcl Hty).
    + intros v Hv. inversion Hv; subst v.
      exact (VTrExpr_lift_let ty' val' Hcl Hval).
  - destruct (IH i b Hnth) as [e' [ty0' [Hlk [Hty0 Hval0]]]].
    exists e', ty0'. repeat split.
    + exact Hlk.
    + replace (S (S i)) with (1 + S i) by lia. rewrite <- lift_lift_eq.
      exact (VTrExpr_lift_let ty' val' Hcl Hty0).
    + intros v Hv. replace (S (S i)) with (1 + S i) by lia. rewrite <- lift_lift_eq.
      exact (VTrExpr_lift_let ty' val' Hcl (Hval0 v Hv)).
Qed.

Lemma VTrCtx_lookup_bound env venv ps g L i b :
  VEnvClosed venv ->
  VTrCtx env venv ps g L ->
  nth_error (bound_context g) i = Some b ->
  exists e' ty',
    vl_bvar L i = Some (e', ty') /\
    VHasType venv (List.length ps) (vl_ctx L) e' ty' /\
    VTrExpr env venv ps L (lift (S i) 0 (binding_type b)) ty' /\
    (forall v, binding_value b = Some v ->
      VTrExpr env venv ps L (lift (S i) 0 v) e').
Proof.
  intros Hcl Hctx Hnth.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  destruct Hctx as [_ Hbc].
  destruct (VTrBoundCtx_lookup Hcl Hbc Hnth) as [e' [ty' [Hlk [Hty Hval]]]].
  destruct L as [fs' bs']. simpl in *.
  exists e', ty'. repeat split; try assumption.
  eapply vl_lookup_bound_has_type; [exact Hcl | exact HwfL | exact Hlk].
Qed.

Lemma VTrFreeCtx_lookup env venv ps fs fs' :
  VEnvClosed venv ->
  VTrFreeCtx env venv ps fs fs' ->
  forall n b,
    find_free n fs = Some b ->
    exists e' ty',
      vl_lookup_free fs' n 0 = Some (e', ty') /\
      VTrExpr env venv ps {| vl_free := fs'; vl_bound := [] |} (binding_type b) ty' /\
      (forall v, binding_value b = Some v ->
        VTrExpr env venv ps {| vl_free := fs'; vl_bound := [] |} v e').
Proof.
  intros Hcl Hfc.
  induction Hfc as
    [
    | m ty fs0 ty' fs0' Hfc IH Hfresh Hty His
    | m ty val fs0 ty' val' fs0' Hfc IH Hfresh Hty Hval Hhas ];
    intros n b Hfind; simpl in *; try discriminate.
  - destruct (name_eqb n m) eqn:Em.
    + inversion Hfind; subst b; clear Hfind. simpl.
      exists (VBVar 0), (vlift ty'). repeat split.
      * exact (VTrExpr_weak_free_one (VLLam ty') Hcl Hfresh Hty).
      * intros v Hv. discriminate.
    + destruct (IH n b Hfind) as [e' [ty0' [Hlk [Hty0 Hval0]]]].
      exists (vlift e'), (vlift ty0'). repeat split.
      * exact (vl_lookup_free_shift_at 1 (Nat.le_0_l 0) Hlk).
      * exact (VTrExpr_weak_free_one (VLLam ty') Hcl Hfresh Hty0).
      * intros v Hv. exact (VTrExpr_weak_free_one (VLLam ty') Hcl Hfresh (Hval0 v Hv)).
  - destruct (name_eqb n m) eqn:Em.
    + inversion Hfind; subst b; clear Hfind. simpl.
      exists val', ty'. repeat split.
      * rewrite !vliftN_zero. reflexivity.
      * pose proof (VTrExpr_weak_free_one (VLLet ty' val') Hcl Hfresh Hty) as Hw.
        simpl in Hw. rewrite vliftN_zero in Hw. exact Hw.
      * intros v Hv. inversion Hv; subst v.
        pose proof (VTrExpr_weak_free_one (VLLet ty' val') Hcl Hfresh Hval) as Hw.
        simpl in Hw. rewrite vliftN_zero in Hw. exact Hw.
    + destruct (IH n b Hfind) as [e' [ty0' [Hlk [Hty0 Hval0]]]].
      exists e', ty0'. repeat split.
      * exact Hlk.
      * pose proof (VTrExpr_weak_free_one (VLLet ty' val') Hcl Hfresh Hty0) as Hw.
        simpl in Hw. rewrite vliftN_zero in Hw. exact Hw.
      * intros v Hv.
        pose proof (VTrExpr_weak_free_one (VLLet ty' val') Hcl Hfresh (Hval0 v Hv)) as Hw.
        simpl in Hw. rewrite vliftN_zero in Hw. exact Hw.
Qed.

Lemma VTrCtx_lookup_free env venv ps g L n b :
  VEnvClosed venv ->
  VTrCtx env venv ps g L ->
  find_free n (free_context g) = Some b ->
  exists e' ty',
    vl_fvar L n = Some (e', ty') /\
    VHasType venv (List.length ps) (vl_ctx L) e' ty' /\
    VTrExpr env venv ps L (binding_type b) ty' /\
    (forall v, binding_value b = Some v ->
      VTrExpr env venv ps L v e').
Proof.
  intros Hcl Hctx Hfind.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  destruct Hctx as [Hfc _].
  destruct (VTrFreeCtx_lookup Hcl Hfc Hfind) as [e0 [ty0 [Hlk0 [Hty0 Hval0]]]].
  destruct L as [fs' bs']. simpl in *.
  exists (vliftN (List.length (vlentries_to_ctx bs')) 0 e0),
         (vliftN (List.length (vlentries_to_ctx bs')) 0 ty0).
  assert (Hlk : vl_fvar {| vl_free := fs'; vl_bound := bs' |} n =
                Some (vliftN (List.length (vlentries_to_ctx bs')) 0 e0,
                      vliftN (List.length (vlentries_to_ctx bs')) 0 ty0)).
  { unfold vl_fvar, vl_bound_lams. simpl.
    pose proof (vl_lookup_free_shift_at (List.length (vlentries_to_ctx bs')) (Nat.le_0_l 0) Hlk0) as Hs.
    rewrite Nat.add_0_r in Hs. exact Hs. }
  repeat split; [exact Hlk | | |].
  - eapply vl_lookup_free_has_type; [exact Hcl | exact HwfL | exact Hlk].
  - pose proof (VTrExpr_lift_from_free bs' Hcl Hty0) as Hl.
    rewrite (VTrExpr_bound_closed (List.length bs') Hty0) in Hl. exact Hl.
  - intros v Hv. specialize (Hval0 v Hv).
    pose proof (VTrExpr_lift_from_free bs' Hcl Hval0) as Hl.
    rewrite (VTrExpr_bound_closed (List.length bs') Hval0) in Hl. exact Hl.
Qed.

(* String literal expansion translation *)
Lemma VTrExprS_core_char_list env venv ps L cs :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_string_ready env = true ->
  VTrExprS env venv ps L (core_char_list cs) (trCharList cs).
Proof.
  intros Hves HwfL Hstr.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  assert (Hnat : core_nat_ready env = true).
  { unfold core_string_ready in Hstr.
    destruct (find_decl core_char_of_nat env); try discriminate.
    destruct (find_decl core_string_of_list env); try discriminate.
    destruct (decl_kind_of d); try discriminate. destruct p; try discriminate.
    destruct (decl_kind_of d0); try discriminate. destruct p; try discriminate.
    exact Hstr. }
  destruct (hp_string (ves_prims Hves) Hstr) as [Hchar_ty [_ [Hcof [_ [Hnil Hcons]]]]].
  assert (Hlift0 : forall e A, vinstL [] e = e -> vinstL [] A = A ->
      VHasType venv 0 [] e A -> VHasType venv (List.length ps) (vl_ctx L) e A).
  { intros e A He HA Hty.
    pose proof (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hty) as Hi.
    simpl in Hi. rewrite He, HA in Hi. exact (VIsDefEq_weak0 (vl_ctx L) Hcl Hi). }
  assert (Hchar_ok : VTrExprS env venv ps L (EConst core_char_name []) vchar_ty).
  { pose proof (Hlift0 _ _ eq_refl eq_refl Hchar_ty) as Ht.
    destruct (VHasType_const_inv Hwf HG Ht) as [ci [Hci [_ Hlen]]].
    eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia]. }
  assert (Hcof_ok : VTrExprS env venv ps L (EConst core_char_of_nat []) (VConst core_char_of_nat [])).
  { pose proof (Hlift0 _ _ eq_refl eq_refl Hcof) as Ht.
    destruct (VHasType_const_inv Hwf HG Ht) as [ci [Hci [_ Hlen]]].
    eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia]. }
  assert (Hnil_ty : VHasType venv (List.length ps) (vl_ctx L)
      (VApp (VConst (NameStr core_list_name "nil") [VLZero]) vchar_ty) vlist_char_ty)
    by (apply Hlift0; auto).
  destruct (VHasType_app_inv Hwf HG Hnil_ty) as [Anil [Bnil [Hnil_f Hnil_a]]].
  assert (Hnil_c : VTrExprS env venv ps L (EConst (NameStr core_list_name "nil") [LZero])
      (VConst (NameStr core_list_name "nil") [VLZero])).
  { destruct (VHasType_const_inv Hwf HG Hnil_f) as [ci [Hci [_ Hlen]]].
    eapply VTrExprS_const; [exact Hci | constructor; [reflexivity | constructor] | simpl in *; lia]. }
  assert (Hcons_ty : VHasType venv (List.length ps) (vl_ctx L)
      (VApp (VConst (NameStr core_list_name "cons") [VLZero]) vchar_ty)
      (VForallE vchar_ty (VForallE vlist_char_ty vlist_char_ty)))
    by (apply Hlift0; auto).
  destruct (VHasType_app_inv Hwf HG Hcons_ty) as [Acons [Bcons [Hcons_f Hcons_a]]].
  assert (Hcons_c : VTrExprS env venv ps L (EConst (NameStr core_list_name "cons") [LZero])
      (VConst (NameStr core_list_name "cons") [VLZero])).
  { destruct (VHasType_const_inv Hwf HG Hcons_f) as [ci [Hci [_ Hlen]]].
    eapply VTrExprS_const; [exact Hci | constructor; [reflexivity | constructor] | simpl in *; lia]. }
  assert (Hcof_ty' : VHasType venv (List.length ps) (vl_ctx L)
      (VConst core_char_of_nat []) (VForallE vnat_ty vchar_ty)) by (apply Hlift0; auto).
  induction cs as [|c rest IH]; simpl.
  - eapply VTrExprS_app; [exact Hnil_f | exact Hnil_a | exact Hnil_c | exact Hchar_ok].
  - assert (Hc_nat : VHasType venv (List.length ps) (vl_ctx L) (natLit c) vnat_ty)
      by (eapply natLit_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hnat]).
    assert (Hc_char : VHasType venv (List.length ps) (vl_ctx L)
        (VApp (VConst core_char_of_nat []) (natLit c)) vchar_ty).
    { change vchar_ty with (vinst0 vchar_ty (natLit c)).
      eapply VDF_appDF; [exact Hcof_ty' | exact Hc_nat]. }
    assert (Hrest_ty : VHasType venv (List.length ps) (vl_ctx L) (trCharList rest) vlist_char_ty)
      by (eapply trCharList_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hstr]).
    assert (Happ1 : VHasType venv (List.length ps) (vl_ctx L)
        (VApp (VApp (VConst (NameStr core_list_name "cons") [VLZero]) vchar_ty)
              (VApp (VConst core_char_of_nat []) (natLit c)))
        (VForallE vlist_char_ty vlist_char_ty)).
    { change (VForallE vlist_char_ty vlist_char_ty)
        with (vinst0 (VForallE vlist_char_ty vlist_char_ty) (VApp (VConst core_char_of_nat []) (natLit c))).
      eapply VDF_appDF; [exact Hcons_ty | exact Hc_char]. }
    eapply VTrExprS_app; [exact Happ1 | exact Hrest_ty | | exact IH].
    eapply VTrExprS_app; [exact Hcons_ty | exact Hc_char | |].
    + eapply VTrExprS_app; [exact Hcons_f | exact Hcons_a | exact Hcons_c | exact Hchar_ok].
    + eapply VTrExprS_app; [exact Hcof_ty' | exact Hc_nat | exact Hcof_ok |].
      eapply VTrExprS_natlit; [exact Hnat | exact Hc_nat].
Qed.

Lemma VTrExprS_core_expand_string env venv ps L s expanded s' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_string_ready env = true ->
  core_expand_string s = Accept expanded ->
  trStrLit s = Some s' ->
  VTrExprS env venv ps L expanded s'.
Proof.
  intros Hves HwfL Hstr Hexp Htrs.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_expand_string in Hexp. unfold trStrLit in Htrs.
  destruct (core_utf8 s) as [cs|] eqn:Hu; [|discriminate].
  inversion Hexp; subst expanded; clear Hexp.
  inversion Htrs; subst s'; clear Htrs.
  destruct (hp_string (ves_prims Hves) Hstr) as [_ [_ [_ [Hsof _]]]].
  pose proof (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hsof) as Hi.
  simpl in Hi. pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl Hi) as Hsof'.
  destruct (VHasType_const_inv Hwf HG Hsof') as [ci [Hci [_ Hlen]]].
  assert (Hcl_ty : VHasType venv (List.length ps) (vl_ctx L) (trCharList cs) vlist_char_ty)
    by (eapply trCharList_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hstr]).
  eapply VTrExprS_app; [exact Hsof' | exact Hcl_ty | |].
  - eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
  - apply VTrExprS_core_char_list; assumption.
Qed.

(* Non-occurrence strengthening: if core_occurs idx e = false, e does not depend on binder idx *)
Lemma vl_lookup_bound_unshift es : forall j d k e' t',
  k <= d ->
  vl_lookup_bound es j (S d) = Some (e', t') ->
  exists e t,
    vl_lookup_bound es j d = Some (e, t) /\
    e' = vliftN 1 k e /\ t' = vliftN 1 k t.
Proof.
  induction es as [|[B|B w] r IH]; intros [|j] d k e' t' Hkd H; simpl in *; try discriminate.
  - inversion H; subst e' t'; clear H.
    exists (VBVar d), (vliftN (S d) 0 B). repeat split.
    + simpl. unfold vliftVar. destruct (Nat.ltb_spec d k); [lia | reflexivity].
    + rewrite vliftN_add_le by lia. reflexivity.
  - apply (IH j (S d) k e' t'); [lia | exact H].
  - inversion H; subst e' t'; clear H.
    exists (vliftN d 0 w), (vliftN d 0 B). repeat split;
      rewrite vliftN_add_le by lia; reflexivity.
  - exact (IH j d k e' t' Hkd H).
Qed.

Lemma vl_lookup_free_unshift fs n : forall d k e' t',
  k <= d ->
  vl_lookup_free fs n (S d) = Some (e', t') ->
  exists e t,
    vl_lookup_free fs n d = Some (e, t) /\
    e' = vliftN 1 k e /\ t' = vliftN 1 k t.
Proof.
  induction fs as [|[m [B|B w]] r IH]; intros d k e' t' Hkd H; simpl in *; try discriminate.
  - destruct (name_eqb n m).
    + inversion H; subst e' t'; clear H.
      exists (VBVar d), (vliftN (S d) 0 B). repeat split.
      * simpl. unfold vliftVar. destruct (Nat.ltb_spec d k); [lia | reflexivity].
      * rewrite vliftN_add_le by lia. reflexivity.
    + apply (IH (S d) k e' t'); [lia | exact H].
  - destruct (name_eqb n m).
    + inversion H; subst e' t'; clear H.
      exists (vliftN d 0 w), (vliftN d 0 B). repeat split;
        rewrite vliftN_add_le by lia; reflexivity.
    + exact (IH d k e' t' Hkd H).
Qed.

Lemma VLBoundLift_lookup_inv A0 idx k bs bs' :
  VLBoundLift [VLLam A0] idx k bs bs' ->
  forall i d e' ty',
    i <> idx ->
    vl_lookup_bound bs' i d = Some (e', ty') ->
    exists e ty,
      vl_lookup_bound bs (if idx <? i then pred i else i) d = Some (e, ty) /\
      e' = vliftN 1 (k + d) e /\ ty' = vliftN 1 (k + d) ty.
Proof.
  induction 1 as [suf | idx k A1 bs bs' H IH | idx k A1 v1 bs bs' H IH];
    intros [|i] d e' ty' Hne Hlk; simpl in *; try congruence; try discriminate.
  - apply vl_lookup_bound_unshift; [lia | exact Hlk].
  - inversion Hlk; subst e' ty'; clear Hlk.
    exists (VBVar d), (vliftN (S d) 0 A1). repeat split.
    + simpl. unfold vliftVar. destruct (Nat.ltb_spec d (S (k + d))); [reflexivity | lia].
    + replace (S (k + d)) with (S d + k) by lia.
      rewrite vliftN_comm by lia. reflexivity.
  - assert (Hne' : i <> idx) by lia.
    destruct (IH i (S d) e' ty' Hne' Hlk) as [e [ty [H1 [H2 H3]]]].
    exists e, ty. repeat split.
    + destruct (Nat.ltb_spec idx i) as [Hlt|Hge].
      * replace (S idx <? S i) with true by (symmetry; apply Nat.ltb_lt; lia).
        destruct i as [|i']; [lia | exact H1].
      * replace (S idx <? S i) with false by (symmetry; apply Nat.ltb_ge; lia).
        exact H1.
    + replace (S (k + d)) with (k + S d) by lia. exact H2.
    + replace (S (k + d)) with (k + S d) by lia. exact H3.
  - inversion Hlk; subst e' ty'; clear Hlk.
    exists (vliftN d 0 v1), (vliftN d 0 A1). repeat split;
      replace (k + d) with (d + k) by lia; rewrite vliftN_comm by lia; reflexivity.
  - assert (Hne' : i <> idx) by lia.
    destruct (IH i d e' ty' Hne' Hlk) as [e [ty [H1 [H2 H3]]]].
    exists e, ty. repeat split; try assumption.
    destruct (Nat.ltb_spec idx i) as [Hlt|Hge].
    + replace (S idx <? S i) with true by (symmetry; apply Nat.ltb_lt; lia).
      destruct i as [|i']; [lia | exact H1].
    + replace (S idx <? S i) with false by (symmetry; apply Nat.ltb_ge; lia).
      exact H1.
Qed.

Lemma VLCtxEntriesWF_lift_inv env U base A0 idx k bs bs' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U base ->
  VLBoundLift [VLLam A0] idx k bs bs' ->
  VLCtxEntriesWF env U base bs' ->
  VLCtxEntriesWF env U base bs.
Proof.
  intros Hwf Hinj Hbase Hbl.
  induction Hbl as [suf | idx k A1 bs bs' H IH | idx k A1 v1 bs bs' H IH];
    intros Hwf'; simpl in *.
  - inversion Hwf'; subst. assumption.
  - inversion Hwf' as [| ? ? Hrest Hty |]; subst.
    pose proof (VLBoundLift_to_VCtxLiftN base H) as W. simpl in W.
    pose proof (VLCtxEntriesWF_to_VCtxWF Hbase Hrest) as HG'.
    constructor; [exact (IH Hrest) |].
    exact (proj1 (VIsType_weakN_iff Hwf Hinj HG' W) Hty).
  - inversion Hwf' as [| | ? ? ? Hrest Hv]; subst.
    pose proof (VLBoundLift_to_VCtxLiftN base H) as W. simpl in W.
    pose proof (VLCtxEntriesWF_to_VCtxWF Hbase Hrest) as HG'.
    constructor; [exact (IH Hrest) |].
    exact (proj1 (VHasType_weakN_iff Hwf Hinj HG' W) Hv).
Qed.

Lemma VTrExprS_no_occurs_subst env venv ps :
  VEnvSound env venv ->
  forall e L' e' A0 idx k bs any_expr,
    VLCtxWF venv (List.length ps) L' ->
    VLBoundLift [VLLam A0] idx k bs (vl_bound L') ->
    core_occurs idx e = false ->
    VTrExprS env venv ps L' e e' ->
    exists e0,
      VIsDefEqU venv (List.length ps) (vl_ctx L') (vliftN 1 k e0) e' /\
      VTrExpr env venv ps {| vl_free := vl_free L'; vl_bound := bs |} (subst idx any_expr e) e0.
Proof.
  intros Hves.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  induction e as [i|nm|nm|u|c us|f IHf a IHa|nm bi ty IHA body IHb|nm bi ty IHA body IHB
                  |nm ty IHA val IHv body IHb nd|lit|owner idx0 a IHa|a IHa];
    intros L' e' A0 idx k bs any_expr HwfL' Hbl Hocc Htr;
    pose proof (VLBoundLift_to_VCtxLiftN (vl_free_ctx (vl_free L')) Hbl) as W;
    simpl in W;
    pose proof (VLCtxWF_to_VCtxWF HwfL') as HG';
    assert (HG : VCtxWF venv (List.length ps) (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}))
      by (eapply VCtxWF_weakN_inv; [exact Hwf | exact Hinj | exact W | exact HG']);
    assert (HwfL : VLCtxWF venv (List.length ps) {| vl_free := vl_free L'; vl_bound := bs |})
      by (destruct HwfL' as [Hf Hb]; split; [exact Hf |
          eapply VLCtxEntriesWF_lift_inv; [exact Hwf | exact Hinj | | exact Hbl | exact Hb];
          simpl; unfold vl_free_ctx; rewrite <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L'))));
          apply VLCtxEntriesWF_to_VCtxWF; [exact I | exact Hf]]);
    simpl in Hocc.
  - (* EBVar *)
    inversion Htr as [? ? ? ty1 Hlk Hty | | | | | | | | | | |]; subst.
    simpl. rewrite Hocc.
    assert (Hne : i <> idx) by (apply Nat.eqb_neq; exact Hocc).
    destruct (VLBoundLift_lookup_inv Hbl Hne Hlk) as [e0 [ty0 [Hlk0 [He1 Hty1]]]].
    rewrite Nat.add_0_r in He1, Hty1. subst e' ty1.
    assert (Hty0 : VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) e0 ty0)
      by (exact (proj1 (VHasType_weakN_iff Hwf Hinj HG' W) Hty)).
    exists e0. split; [exists (vliftN 1 k ty0); exact Hty |].
    apply VTrExprS_to_VTrExpr. eapply VTrExprS_bvar; [exact Hlk0 | exact Hty0].
  - (* EFVar *)
    inversion Htr as [| ? ? ? ty1 Hlk Hty | | | | | | | | | |]; subst.
    simpl.
    destruct (VLBoundLift_lams Hbl) as [Hlams Hkle]. simpl in Hlams.
    unfold vl_fvar, vl_bound_lams in Hlk. rewrite Hlams in Hlk.
    destruct (vl_lookup_free_unshift Hkle Hlk) as [e0 [ty0 [Hlk0 [He1 Hty1]]]].
    subst e' ty1.
    assert (Hty0 : VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) e0 ty0)
      by (exact (proj1 (VHasType_weakN_iff Hwf Hinj HG' W) Hty)).
    exists e0. split; [exists (vliftN 1 k ty0); exact Hty |].
    apply VTrExprS_to_VTrExpr. eapply VTrExprS_fvar; [exact Hlk0 | exact Hty0].
  - (* EMVar *)
    inversion Htr.
  - (* ESort *)
    inversion Htr as [| | ? ? u' Htr_u | | | | | | | | |]; subst.
    simpl. exists (VSort u'). split.
    + exists (VSort (VLSucc u')). apply VHasType_sort. eapply vlevel_of_level_wf; exact Htr_u.
    + apply VTrExprS_to_VTrExpr. constructor. exact Htr_u.
  - (* EConst *)
    inversion Htr as [| | | ? ? ci ? us' Hci Htr_us Hlen_us | | | | | | | |]; subst.
    simpl. exists (VConst c us'). split.
    + exists (vinstL us' (vc_type ci)).
      eapply VHasType_const; [exact Hci | eapply TrLevels_wf; exact Htr_us |
        rewrite <- (TrLevels_length Htr_us); exact Hlen_us].
    + apply VTrExprS_to_VTrExpr. econstructor; eassumption.
  - (* EApp *)
    inversion Htr as [| | | | ? ? ? f' a' A B Hf_ty Ha_ty Htr_f Htr_a | | | | | | |]; subst.
    apply orb_false_iff in Hocc as [Hof Hoa].
    destruct (IHf L' f' A0 idx k bs any_expr HwfL' Hbl Hof Htr_f) as [f0 [Hfeq Hf0]].
    destruct (IHa L' a' A0 idx k bs any_expr HwfL' Hbl Hoa Htr_a) as [a0 [Haeq Ha0]].
    destruct Hfeq as [Tf Hfeq']. destruct Haeq as [Ta Haeq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hf_ty (VIsDefEq_refl_r Hfeq')) as [uf Hcf].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Ha_ty (VIsDefEq_refl_r Haeq')) as [ua Hca].
    assert (Hfeq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k f0) f' (VForallE A B))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcf) | exact Hfeq']).
    assert (Haeq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k a0) a' A)
      by (eapply VDF_defeqDF; [exact (VDF_symm Hca) | exact Haeq']).
    assert (Happ_eq : VIsDefEq venv (List.length ps) (vl_ctx L')
        (vliftN 1 k (VApp f0 a0)) (VApp f' a') (vinst0 B (vliftN 1 k a0))).
    { simpl. eapply VDF_appDF; [exact Hfeq'' | exact Haeq'']. }
    assert (Happ_wf0 : VExprWF venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) (VApp f0 a0)).
    { eapply (proj1 (VIsDefEqU_weakN_iff Hinj HG' W)).
      exists (vinst0 B (vliftN 1 k a0)). exact (VIsDefEq_refl_l Happ_eq). }
    exists (VApp f0 a0). split; [exists (vinst0 B (vliftN 1 k a0)); exact Happ_eq |].
    simpl.
    change (EApp (subst idx any_expr f) (subst idx any_expr a))
      with (core_apps (subst idx any_expr f) [subst idx any_expr a]).
    change (VApp f0 a0) with (vapps f0 [a0]).
    eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hf0 |
      constructor; [exact Ha0 | constructor] | exact Happ_wf0].
  - (* ELam *)
    inversion Htr as [| | | | | ? ? ? ? ? ty' body' Hty_is Htr_ty Htr_body | | | | | |]; subst.
    apply orb_false_iff in Hocc as [HoA Hob].
    destruct (IHA L' ty' A0 idx k bs any_expr HwfL' Hbl HoA Htr_ty) as [ty0 [HAeq Hty0]].
    destruct Hty_is as [u Hu].
    destruct HAeq as [TA HAeq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hu (VIsDefEq_refl_r HAeq')) as [uA HcA].
    assert (HAeq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k ty0) ty' (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq']).
    assert (Hty0_is : VIsType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) ty0).
    { exists u. exact (proj1 (VHasType_weakN_iff (A := VSort u) Hwf Hinj HG' W) (VIsDefEq_refl_l HAeq'')). }
    assert (Hwf1 : VLCtxWF venv (List.length ps) (vl_push_lam L' ty'))
      by (apply VLCtxWF_push_lam; [exact HwfL' | exists u; exact Hu]).
    assert (Hwf2 : VLCtxWF venv (List.length ps) (vl_push_lam L' (vliftN 1 k ty0)))
      by (apply VLCtxWF_push_lam; [exact HwfL' | exists u; exact (VIsDefEq_refl_l HAeq'')]).
    assert (Hceq : VLCtxDefEq venv (List.length ps)
        (vl_push_lam L' ty') (vl_push_lam L' (vliftN 1 k ty0))).
    { destruct (VLCtxDefEq_refl Hwf HwfL') as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm HAeq'')]. }
    destruct (VTrExprS_defeq_ctx_uniq Hves Htr_body Hwf1 Hwf2 Hceq) as [body2 [Hbody2 [TB2 Hbe12]]].
    assert (Hbl' : VLBoundLift [VLLam A0] (S idx) (S k) (VLLam ty0 :: bs)
                     (vl_bound (vl_push_lam L' (vliftN 1 k ty0))))
      by (simpl; apply VLBoundLift_lam; exact Hbl).
    destruct (IHb _ body2 A0 (S idx) (S k) (VLLam ty0 :: bs) any_expr Hwf2 Hbl' Hob Hbody2)
      as [body0 [Hbeq02 Hb0]].
    assert (Hctx' : VIsDefEqCtx venv (List.length ps) []
        (ty' :: vl_ctx L') (vliftN 1 k ty0 :: vl_ctx L'))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    destruct Hbeq02 as [TB0 Hbeq02'].
    assert (Hbe21 : VIsDefEq venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L') body2 body' TB2).
    { apply VDF_symm. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx' | exact Hbe12]. }
    assert (HG2' : VCtxWF venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L'))
      by (split; [exact HG' | exists u; exact (VIsDefEq_refl_l HAeq'')]).
    destruct (VIsDefEqU_trans Hwf Hinj HG2'
        (ex_intro _ TB0 Hbeq02') (ex_intro _ TB2 Hbe21)) as [TB Hbeq].
    exists (VLam ty0 body0). split.
    + simpl. exists (VForallE (vliftN 1 k ty0) TB). eapply VDF_lamDF; [exact HAeq'' | exact Hbeq].
    + simpl.
      destruct Hty0 as [ty0s [Hty0s [TAs Hty0eq]]].
      destruct Hty0_is as [u0 Hu0].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu0 (VIsDefEq_refl_r Hty0eq)) as [uAs HcAs].
      assert (Hty0eq' : VIsDefEq venv (List.length ps)
          (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) ty0s ty0 (VSort u0))
        by (eapply VDF_defeqDF; [exact (VDF_symm HcAs) | exact Hty0eq]).
      assert (HwfL_s : VLCtxWF venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0s))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists u0; exact (VIsDefEq_refl_l Hty0eq')]).
      assert (HwfL_0 : VLCtxWF venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists u0; exact Hu0]).
      assert (Hceq0 : VLCtxDefEq venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0s)).
      { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
        repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm Hty0eq')]. }
      pose proof (VTrExpr_defeq_ctx Hves HwfL_0 HwfL_s Hceq0 Hb0) as [b0s [Hb0s [TB0s Hb0eq]]].
      exists (VLam ty0s b0s). split.
      * eapply VTrExprS_lam; [exists u0; exact (VIsDefEq_refl_l Hty0eq') | exact Hty0s | exact Hb0s].
      * exists (VForallE ty0s TB0s). eapply VDF_lamDF; [exact Hty0eq' | exact Hb0eq].
  - (* EPi *)
    inversion Htr as [| | | | | | ? ? ? ? ? ty' body' Hty_is Hbody_is Htr_ty Htr_body | | | | |]; subst.
    apply orb_false_iff in Hocc as [HoA Hob].
    destruct (IHA L' ty' A0 idx k bs any_expr HwfL' Hbl HoA Htr_ty) as [ty0 [HAeq Hty0]].
    destruct Hty_is as [u Hu].
    destruct HAeq as [TA HAeq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hu (VIsDefEq_refl_r HAeq')) as [uA HcA].
    assert (HAeq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k ty0) ty' (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq']).
    assert (Hty0_is : VIsType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) ty0).
    { exists u. exact (proj1 (VHasType_weakN_iff (A := VSort u) Hwf Hinj HG' W) (VIsDefEq_refl_l HAeq'')). }
    assert (Hwf1 : VLCtxWF venv (List.length ps) (vl_push_lam L' ty'))
      by (apply VLCtxWF_push_lam; [exact HwfL' | exists u; exact Hu]).
    assert (Hwf2 : VLCtxWF venv (List.length ps) (vl_push_lam L' (vliftN 1 k ty0)))
      by (apply VLCtxWF_push_lam; [exact HwfL' | exists u; exact (VIsDefEq_refl_l HAeq'')]).
    assert (Hceq : VLCtxDefEq venv (List.length ps)
        (vl_push_lam L' ty') (vl_push_lam L' (vliftN 1 k ty0))).
    { destruct (VLCtxDefEq_refl Hwf HwfL') as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm HAeq'')]. }
    destruct (VTrExprS_defeq_ctx_uniq Hves Htr_body Hwf1 Hwf2 Hceq) as [body2 [Hbody2 [TB2 Hbe12]]].
    assert (Hbl' : VLBoundLift [VLLam A0] (S idx) (S k) (VLLam ty0 :: bs)
                     (vl_bound (vl_push_lam L' (vliftN 1 k ty0))))
      by (simpl; apply VLBoundLift_lam; exact Hbl).
    destruct (IHB _ body2 A0 (S idx) (S k) (VLLam ty0 :: bs) any_expr Hwf2 Hbl' Hob Hbody2)
      as [body0 [Hbeq02 Hb0]].
    assert (Hctx' : VIsDefEqCtx venv (List.length ps) []
        (ty' :: vl_ctx L') (vliftN 1 k ty0 :: vl_ctx L'))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    destruct Hbeq02 as [TB0 Hbeq02'].
    assert (Hbe21 : VIsDefEq venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L') body2 body' TB2).
    { apply VDF_symm. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx' | exact Hbe12]. }
    assert (HG2' : VCtxWF venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L'))
      by (split; [exact HG' | exists u; exact (VIsDefEq_refl_l HAeq'')]).
    destruct (VIsDefEqU_trans Hwf Hinj HG2'
        (ex_intro _ TB0 Hbeq02') (ex_intro _ TB2 Hbe21)) as [TB Hbeq].
    destruct Hbody_is as [v Hv].
    assert (Hv2 : VHasType venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L') body' (VSort v))
      by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx' | exact Hv]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG2' Hv2 (VIsDefEq_refl_r Hbeq)) as [vB HcB].
    assert (Hbeq' : VIsDefEq venv (List.length ps) (vliftN 1 k ty0 :: vl_ctx L')
        (vliftN 1 (S k) body0) body' (VSort v))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcB) | exact Hbeq]).
    assert (Hbody0_v : VHasType venv (List.length ps)
        (ty0 :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) body0 (VSort v)).
    { exact (proj1 (VHasType_weakN_iff (A := VSort v) Hwf Hinj HG2' (VCtxLiftN_succ ty0 W))
              (VIsDefEq_refl_l Hbeq')). }
    exists (VForallE ty0 body0). split.
    + simpl. exists (VSort (VLIMax u v)). eapply VDF_forallEDF; [exact HAeq'' | exact Hbeq'].
    + simpl.
      destruct Hty0 as [ty0s [Hty0s [TAs Hty0eq]]].
      destruct Hty0_is as [u0 Hu0].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu0 (VIsDefEq_refl_r Hty0eq)) as [uAs HcAs].
      assert (Hty0eq' : VIsDefEq venv (List.length ps)
          (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) ty0s ty0 (VSort u0))
        by (eapply VDF_defeqDF; [exact (VDF_symm HcAs) | exact Hty0eq]).
      assert (HwfL_s : VLCtxWF venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0s))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists u0; exact (VIsDefEq_refl_l Hty0eq')]).
      assert (HwfL_0 : VLCtxWF venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists u0; exact Hu0]).
      assert (Hceq0 : VLCtxDefEq venv (List.length ps)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0)
          (vl_push_lam {| vl_free := vl_free L'; vl_bound := bs |} ty0s)).
      { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
        repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm Hty0eq')]. }
      pose proof (VTrExpr_defeq_ctx Hves HwfL_0 HwfL_s Hceq0 Hb0) as [b0s [Hb0s [TB0s Hb0eq]]].
      assert (Hctx0 : VIsDefEqCtx venv (List.length ps) []
          (ty0 :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |})
          (ty0s :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}))
        by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq0)).
      assert (Hbody0_vs : VHasType venv (List.length ps)
          (ty0s :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) body0 (VSort v))
        by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx0 | exact Hbody0_v]).
      assert (HG_s : VCtxWF venv (List.length ps)
          (ty0s :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}))
        by (split; [exact HG | exists u0; exact (VIsDefEq_refl_l Hty0eq')]).
      destruct (VIsDefEq_uniq_same Hwf Hinj HG_s Hbody0_vs (VIsDefEq_refl_r Hb0eq)) as [vBs HcBs].
      assert (Hb0eq' : VIsDefEq venv (List.length ps)
          (ty0s :: vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) b0s body0 (VSort v))
        by (eapply VDF_defeqDF; [exact (VDF_symm HcBs) | exact Hb0eq]).
      exists (VForallE ty0s b0s). split.
      * eapply VTrExprS_pi;
          [exists u0; exact (VIsDefEq_refl_l Hty0eq')
          | exists v; exact (VIsDefEq_refl_l Hb0eq')
          | exact Hty0s | exact Hb0s].
      * exists (VSort (VLIMax u0 v)). eapply VDF_forallEDF; [exact Hty0eq' | exact Hb0eq'].
  - (* ELet *)
    inversion Htr as [| | | | | | | ? ? ? ? ? ? ty' val' body' Hval_ty Htr_ty Htr_val Htr_body | | | |]; subst.
    apply orb_false_iff in Hocc as [HoAv Hob].
    apply orb_false_iff in HoAv as [HoA Hov].
    destruct (IHA L' ty' A0 idx k bs any_expr HwfL' Hbl HoA Htr_ty) as [ty0 [HAeq Hty0]].
    destruct (IHv L' val' A0 idx k bs any_expr HwfL' Hbl Hov Htr_val) as [val0 [Hveq Hval0]].
    destruct (VIsDefEq_isType Hwf HG' Hval_ty) as [u Hu].
    destruct HAeq as [TA HAeq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hu (VIsDefEq_refl_r HAeq')) as [uA HcA].
    assert (HAeq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k ty0) ty' (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq']).
    destruct Hveq as [Tv Hveq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hval_ty (VIsDefEq_refl_r Hveq')) as [uv Hcv].
    assert (Hveq'' : VIsDefEq venv (List.length ps) (vl_ctx L') (vliftN 1 k val0) val' ty')
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv) | exact Hveq']).
    assert (Hval0_ty0' : VHasType venv (List.length ps) (vl_ctx L') (vliftN 1 k val0) (vliftN 1 k ty0))
      by (eapply VDF_defeqDF; [exact (VDF_symm HAeq'') | exact (VIsDefEq_refl_l Hveq'')]).
    assert (Hval0_ty0 : VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) val0 ty0)
      by (exact (proj1 (VHasType_weakN_iff Hwf Hinj HG' W) Hval0_ty0')).
    assert (Hwf1 : VLCtxWF venv (List.length ps) (vl_push_let L' ty' val'))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hwf2 : VLCtxWF venv (List.length ps) (vl_push_let L' (vliftN 1 k ty0) (vliftN 1 k val0)))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hceq : VLCtxDefEq venv (List.length ps)
        (vl_push_let L' ty' val') (vl_push_let L' (vliftN 1 k ty0) (vliftN 1 k val0))).
    { destruct (VLCtxDefEq_refl Hwf HwfL') as [Hn [Hf Hb]].
      repeat split; simpl; auto.
      econstructor; [exact Hb | exact (VDF_symm HAeq'') | exact (VDF_symm Hveq'')]. }
    destruct (VTrExprS_defeq_ctx_uniq Hves Htr_body Hwf1 Hwf2 Hceq) as [body2 [Hbody2 Hbe12]].
    assert (Hbl' : VLBoundLift [VLLam A0] (S idx) k (VLLet ty0 val0 :: bs)
                     (vl_bound (vl_push_let L' (vliftN 1 k ty0) (vliftN 1 k val0))))
      by (simpl; apply VLBoundLift_let; exact Hbl).
    destruct (IHb _ body2 A0 (S idx) k (VLLet ty0 val0 :: bs) any_expr Hwf2 Hbl' Hob Hbody2)
      as [body0 [Hbeq02 Hb0]].
    exists body0. split.
    + eapply VIsDefEqU_trans;
        [exact Hwf | exact Hinj | exact HG' | exact Hbeq02 | apply VIsDefEqU_symm; exact Hbe12].
    + simpl.
      destruct Hty0 as [ty0s [Hty0s [TAs Hty0eq]]].
      destruct Hval0 as [val0s [Hval0s [Tvs Hval0eq]]].
      destruct (VIsDefEq_isType Hwf HG Hval0_ty0) as [u0 Hu0].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu0 (VIsDefEq_refl_r Hty0eq)) as [uAs HcAs].
      assert (Hty0eq' : VIsDefEq venv (List.length ps)
          (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) ty0s ty0 (VSort u0))
        by (eapply VDF_defeqDF; [exact (VDF_symm HcAs) | exact Hty0eq]).
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hval0_ty0 (VIsDefEq_refl_r Hval0eq)) as [uvs Hcvs].
      assert (Hval0eq' : VIsDefEq venv (List.length ps)
          (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) val0s val0 ty0)
        by (eapply VDF_defeqDF; [exact (VDF_symm Hcvs) | exact Hval0eq]).
      assert (Hval0s_ty0s : VHasType venv (List.length ps)
          (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) val0s ty0s)
        by (eapply VDF_defeqDF; [exact (VDF_symm Hty0eq') | exact (VIsDefEq_refl_l Hval0eq')]).
      assert (HwfL_s : VLCtxWF venv (List.length ps)
          (vl_push_let {| vl_free := vl_free L'; vl_bound := bs |} ty0s val0s))
        by (apply VLCtxWF_push_let; assumption).
      assert (HwfL_0 : VLCtxWF venv (List.length ps)
          (vl_push_let {| vl_free := vl_free L'; vl_bound := bs |} ty0 val0))
        by (apply VLCtxWF_push_let; assumption).
      assert (Hceq0 : VLCtxDefEq venv (List.length ps)
          (vl_push_let {| vl_free := vl_free L'; vl_bound := bs |} ty0 val0)
          (vl_push_let {| vl_free := vl_free L'; vl_bound := bs |} ty0s val0s)).
      { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
        repeat split; simpl; auto.
        econstructor; [exact Hb | exact (VDF_symm Hty0eq') | exact (VDF_symm Hval0eq')]. }
      pose proof (VTrExpr_defeq_ctx Hves HwfL_0 HwfL_s Hceq0 Hb0) as [b0s [Hb0s Hb0eq]].
      exists b0s. split; [eapply VTrExprS_let; eassumption | exact Hb0eq].
  - (* ELit *)
    destruct lit as [n|s].
    + inversion Htr as [| | | | | | | | | ? ? Hnat Hnty | |]; subst.
      simpl. exists (natLit n). split.
      * rewrite vliftN_natLit. exists vnat_ty. exact Hnty.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_natlit; [exact Hnat |].
        eapply natLit_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hnat].
    + inversion Htr as [| | | | | | | | | | ? ? s' Hstr Htrs Hsty |]; subst.
      simpl. exists e'. split.
      * rewrite (vliftN_trStrLit 1 k Htrs). exists vstring_ty. exact Hsty.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_strlit; [exact Hstr | exact Htrs |].
        eapply trStrLit_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hstr | exact Htrs].
  - (* EProj *)
    inversion Htr as [| | | | | | | | ? ? ? ? a' ? fty Htr_a Hproj | | |]; subst.
    destruct (IHa L' a' A0 idx k bs any_expr HwfL' Hbl Hocc Htr_a) as [a0 [Haeq Ha0]].
    destruct Hproj as [info ctor c d us ps_e idxs Hi Hc Hd Hk Hlt Hlp Hli Hw Hlu Hst Hpv Hty].
    subst e'.
    destruct (VTrExpr_has_type Ha0) as [Ta0 HTa0].
    pose proof (VIsDefEq_weakN Hcl HTa0 W) as HTa0'.
    destruct Haeq as [Ta Haeq'].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' HTa0' (VIsDefEq_refl_l Haeq')) as [u1 Hc1].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' (VIsDefEq_refl_r Haeq') Hst) as [u2 Hc2].
    assert (Hty_ind : VIsDefEqU venv (List.length ps) (vl_ctx L')
        (vliftN 1 k Ta0) (vapps (VConst owner us) (ps_e ++ idxs))).
    { eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG' |
        exists (VSort u1); exact Hc1 | exists (VSort u2); exact Hc2]. }
    destruct (ves_ind_weakN Hves HG' W Hi Hty_ind) as [args0 [Hlen0 Hargs0]].
    set (ps0 := firstn (ind_num_params info) args0).
    set (idxs0 := skipn (ind_num_params info) args0).
    assert (Hsplit : args0 = ps0 ++ idxs0) by (symmetry; apply firstn_skipn).
    assert (Hlp0 : List.length ps0 = ind_num_params info)
      by (unfold ps0; rewrite List.length_firstn, Hlen0, List.length_app; lia).
    assert (Hli0 : List.length idxs0 = ind_num_indices info)
      by (unfold idxs0; rewrite List.length_skipn, Hlen0, List.length_app; lia).
    rewrite Hsplit in Hargs0.
    assert (Hst0 : VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) a0
        (vapps (VConst owner us) (ps0 ++ idxs0)))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact HTa0 | exact Hargs0]).
    assert (Hargs_lift : VIsDefEqU venv (List.length ps) (vl_ctx L')
        (vapps (VConst owner us) (map (vliftN 1 k) (ps0 ++ idxs0)))
        (vapps (VConst owner us) (ps_e ++ idxs))).
    { destruct Hargs0 as [Targ Harg].
      pose proof (VIsDefEq_weakN Hcl Harg W) as Hw_arg.
      rewrite vliftN_vapps in Hw_arg. simpl in Hw_arg.
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG' |
        apply VIsDefEqU_symm; exists (vliftN 1 k Targ); exact Hw_arg | exact Hty_ind]. }
    destruct (ves_ind_inj Hves HG' Hi Hi Hargs_lift) as [_ [_ Hargs_eq]].
    assert (Hps_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L'))
        (map (vliftN 1 k) ps0) ps_e).
    { rewrite map_app in Hargs_eq.
      assert (Hlen_p : List.length (map (vliftN 1 k) ps0) = List.length ps_e)
        by (rewrite List.length_map; lia).
      clear -Hargs_eq Hlen_p.
      revert ps_e Hlen_p Hargs_eq.
      induction (map (vliftN 1 k) ps0) as [|x r IH]; intros [|y r2] Hl H; simpl in *; try lia;
        [constructor |].
      inversion H as [| ? ? ? ? Hxy Hrest]; subst.
      constructor; [exact Hxy | apply IH; [lia | exact Hrest]]. }
    assert (Hpv_eq : VExprWF venv (List.length ps) (vl_ctx L')
        (vliftN 1 k (vproj_expr owner idx0 us ps0 a0)) /\
      VIsDefEqU venv (List.length ps) (vl_ctx L')
        (vliftN 1 k (vproj_expr owner idx0 us ps0 a0))
        (vproj_expr owner idx0 us ps_e a')).
    { unfold vproj_expr in *.
      simpl. rewrite vliftN_vapps. simpl.
      assert (Hwf_r : VExprWF venv (List.length ps) (vl_ctx L')
          (vapps (VConst (proj_const_name owner idx0) us) (ps_e ++ [a']))).
      { rewrite vapps_app. simpl. exists fty. exact Hty. }
      assert (Hhead : VIsDefEqU venv (List.length ps) (vl_ctx L')
          (VConst (proj_const_name owner idx0) us) (VConst (proj_const_name owner idx0) us)).
      { destruct (ves_proj_const Hves Hi Hc Hd Hk Hlt) as [pci [Hpci Huv]].
        exists (vinstL us (vc_type pci)).
        eapply VHasType_const; [exact Hpci | exact Hw | lia]. }
      assert (Hall : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L'))
          (ps_e ++ [a']) (map (vliftN 1 k) ps0 ++ [vliftN 1 k a0])).
      { apply Forall2_app.
        - clear -Hps_eq. induction Hps_eq; constructor; [apply VIsDefEqU_symm; assumption | assumption].
        - constructor; [apply VIsDefEqU_symm; exists Ta; exact Haeq' | constructor]. }
      destruct (vapps_defeq_congr_l Hwf Hinj HG' Hwf_r Hhead Hall) as [Hwf_l Heq_rl].
      rewrite !vapps_app in Hwf_l. rewrite !vapps_app in Heq_rl. simpl in Hwf_l, Heq_rl.
      split; [exact Hwf_l | apply VIsDefEqU_symm; exact Heq_rl]. }
    destruct Hpv_eq as [Hpv_wf' Hpv_eq'].
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG' W) Hpv_wf') as [fty0 Hfty0].
    exists (vproj_expr owner idx0 us ps0 a0). split; [exact Hpv_eq' |].
    simpl.
    destruct Ha0 as [a0s [Ha0s [Ta0s Ha0eq]]].
    assert (Hst0s : VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |}) a0s
        (vapps (VConst owner us) (ps0 ++ idxs0))).
    { eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hst0 |
        apply VIsDefEqU_symm; exists Ta0s; exact Ha0eq]. }
    assert (Hpv0s : VIsDefEqU venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L'; vl_bound := bs |})
        (vproj_expr owner idx0 us ps0 a0s) (vproj_expr owner idx0 us ps0 a0)).
    { unfold vproj_expr in *.
      destruct (VHasType_app_inv Hwf HG Hfty0) as [Ap [Bp [Hpf Hpe]]].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe (VIsDefEq_refl_r Ha0eq)) as [up Hcp].
      exists (vinst0 Bp a0s).
      eapply VDF_appDF; [exact Hpf | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Ha0eq]]. }
    destruct Hpv0s as [Tpv0s Hpv0s'].
    exists (vproj_expr owner idx0 us ps0 a0s). split.
    + eapply VTrExprS_proj; [exact Ha0s |].
      eapply VTrProj_intro; try eassumption; [reflexivity | exact (VIsDefEq_refl_l Hpv0s')].
    + exists Tpv0s. exact Hpv0s'.
  - (* EMData *)
    inversion Htr as [| | | | | | | | | | | ? ? a' Htr_a]; subst.
    destruct (IHa L' e' A0 idx k bs any_expr HwfL' Hbl Hocc Htr_a) as [e0 [Heq H0]].
    exists e0. split; [exact Heq |].
    destruct H0 as [e0s [Htr0s Hdef0s]].
    exists e0s. split; [constructor; exact Htr0s | exact Hdef0s].
Qed.

Corollary VTrExpr_no_occurs_instantiate env venv ps L A body body' any_expr :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) (vl_push_lam L A) ->
  core_occurs 0 body = false ->
  VTrExpr env venv ps (vl_push_lam L A) body body' ->
  exists b0,
    VIsDefEqU venv (List.length ps) (A :: vl_ctx L) (vlift b0) body' /\
    VTrExpr env venv ps L (instantiate body any_expr) b0.
Proof.
  intros Hves HwfL' Hocc [b_s [Hb_s Hb_eq]].
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL') as HG'.
  destruct L as [fs bs].
  destruct (VTrExprS_no_occurs_subst Hves (A0 := A) (idx := 0) (k := 0) (bs := bs)
              any_expr HwfL' (VLBoundLift_base [VLLam A] bs) Hocc Hb_s)
    as [b0 [Hlift Hb0]].
  exists b0. split.
  - eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG' | exact Hlift | exact Hb_eq].
  - exact Hb0.
Qed.

(* Convenient VTrExpr inversion lemmas *)
Lemma VTrExpr_inv_sort env venv ps L u e' :
  VTrExpr env venv ps L (ESort u) e' ->
  exists u',
    vlevel_of_level ps u = Some u' /\
    vlevel_wf (List.length ps) u' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) (VSort u') e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | ? ? u' Hu | | | | | | | | |]; subst.
  exists u'. repeat split; [exact Hu | eapply vlevel_of_level_wf; exact Hu | exact Heq].
Qed.

Lemma VTrExpr_inv_const env venv ps L c us e' :
  VTrExpr env venv ps L (EConst c us) e' ->
  exists ci us',
    venv_constants venv c = Some ci /\
    TrLevels ps us us' /\
    Forall (vlevel_wf (List.length ps)) us' /\
    List.length us = vc_uvars ci /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) (VConst c us') e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | ? ? ci ? us' Hci Hus Hlen | | | | | | | |]; subst.
  exists ci, us'. repeat split; try assumption.
  eapply TrLevels_wf; exact Hus.
Qed.

Lemma VTrExpr_inv_app env venv ps L f a e' :
  VTrExpr env venv ps L (EApp f a) e' ->
  exists f' a' A B,
    VHasType venv (List.length ps) (vl_ctx L) f' (VForallE A B) /\
    VHasType venv (List.length ps) (vl_ctx L) a' A /\
    VTrExpr env venv ps L f f' /\
    VTrExpr env venv ps L a a' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) (VApp f' a') e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | ? ? ? f' a' A B Hf Ha Htrf Htra | | | | | | |]; subst.
  exists f', a', A, B. repeat split; try assumption; apply VTrExprS_to_VTrExpr; assumption.
Qed.

Lemma VTrExpr_inv_lam env venv ps L nm bi A b e' :
  VTrExpr env venv ps L (ELam nm bi A b) e' ->
  exists A' b',
    VIsType venv (List.length ps) (vl_ctx L) A' /\
    VTrExpr env venv ps L A A' /\
    VTrExpr env venv ps (vl_push_lam L A') b b' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) (VLam A' b') e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | ? ? ? ? ? A' b' HA HtrA Htrb | | | | | |]; subst.
  exists A', b'. repeat split; try assumption; apply VTrExprS_to_VTrExpr; assumption.
Qed.

Lemma VTrExpr_inv_pi env venv ps L nm bi A B e' :
  VTrExpr env venv ps L (EPi nm bi A B) e' ->
  exists A' B',
    VIsType venv (List.length ps) (vl_ctx L) A' /\
    VIsType venv (List.length ps) (A' :: vl_ctx L) B' /\
    VTrExpr env venv ps L A A' /\
    VTrExpr env venv ps (vl_push_lam L A') B B' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) (VForallE A' B') e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | ? ? ? ? ? A' B' HA HB HtrA HtrB | | | | |]; subst.
  exists A', B'. repeat split; try assumption; apply VTrExprS_to_VTrExpr; assumption.
Qed.

Lemma VTrExpr_inv_let env venv ps L nm ty val body nd e' :
  VTrExpr env venv ps L (ELet nm ty val body nd) e' ->
  exists ty' val' body',
    VHasType venv (List.length ps) (vl_ctx L) val' ty' /\
    VTrExpr env venv ps L ty ty' /\
    VTrExpr env venv ps L val val' /\
    VTrExpr env venv ps (vl_push_let L ty' val') body body' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) body' e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | | ? ? ? ? ? ? ty' val' body' Hvt HtrA Htrv Htrb | | | |]; subst.
  exists ty', val', e0. repeat split; try assumption; apply VTrExprS_to_VTrExpr; assumption.
Qed.

Lemma VTrExpr_inv_proj env venv ps L owner idx a e' :
  VTrExpr env venv ps L (EProj owner idx a) e' ->
  exists a' pv fty,
    VTrExpr env venv ps L a a' /\
    VTrProj env venv (List.length ps) (vl_ctx L) owner idx a' pv fty /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) pv e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | | | ? ? ? ? a' pv fty Htra Hproj | | |]; subst.
  exists a', e0, fty. repeat split; [apply VTrExprS_to_VTrExpr; exact Htra | exact Hproj | exact Heq].
Qed.

Lemma VTrExpr_inv_natlit env venv ps L n e' :
  VTrExpr env venv ps L (ELit (LitNat n)) e' ->
  core_nat_ready env = true /\
  VHasType venv (List.length ps) (vl_ctx L) (natLit n) vnat_ty /\
  VIsDefEqU venv (List.length ps) (vl_ctx L) (natLit n) e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | | | | ? ? Hnat Hnty | |]; subst.
  repeat split; assumption.
Qed.

Lemma VTrExpr_inv_strlit env venv ps L s e' :
  VTrExpr env venv ps L (ELit (LitString s)) e' ->
  exists s',
    core_string_ready env = true /\
    trStrLit s = Some s' /\
    VHasType venv (List.length ps) (vl_ctx L) s' vstring_ty /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) s' e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | | | | | ? ? s' Hstr Htrs Hsty |]; subst.
  exists e0. repeat split; assumption.
Qed.

Lemma VTrExpr_inv_mdata env venv ps L a e' :
  VTrExpr env venv ps L (EMData a) e' ->
  VTrExpr env venv ps L a e'.
Proof.
  intros [e0 [Htr Heq]].
  inversion Htr as [| | | | | | | | | | | ? ? a0 Htra]; subst.
  exists e0. split; assumption.
Qed.

(* ========================================================================= *)
(* 2. FullMethodsSound Specification & inference_only Preservation           *)
(* ========================================================================= *)

Record FullMethodsSound (env : environment) (venv : VEnv) (ps : list name)
    (checking_infer : bool) (rec : methods) : Prop := {
  fms_infer : forall g L e ty,
    VTrCtx env venv ps g L ->
    checking_infer = true ->
    infer_method rec g e = Accept ty ->
    exists e' ty', VTrTyping env venv ps L e ty e' ty';
  fms_infer_typed : forall g L e e' ty,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    infer_method rec g e = Accept ty ->
    exists ty', VTrExpr env venv ps L ty ty' /\
                VHasType venv (List.length ps) (vl_ctx L) e' ty';
  fms_infer_type : forall g L e e' ty,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    infer_type_method rec g e = Accept ty ->
    exists ty', VTrExpr env venv ps L ty ty' /\
                VHasType venv (List.length ps) (vl_ctx L) e' ty';
  fms_whnf_core : forall cheap g L e e' e1,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    whnf_core_method rec cheap g e = Accept e1 ->
    VTrExpr env venv ps L e1 e';
  fms_whnf : forall g L e e' e1,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    whnf_method rec g e = Accept e1 ->
    VTrExpr env venv ps L e1 e';
  fms_defeq : forall g L t t' s s',
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L t t' ->
    VTrExpr env venv ps L s s' ->
    defeq_method rec g t s = Accept true ->
    VIsDefEqU venv (List.length ps) (vl_ctx L) t' s';
  fms_eager_defeq : forall g L t t' s s',
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L t t' ->
    VTrExpr env venv ps L s s' ->
    eager_defeq_method rec g t s = Accept true ->
    VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'
}.

Lemma FullMethodsSound_inference_only env venv ps chk rec :
  FullMethodsSound env venv ps chk rec ->
  FullMethodsSound env venv ps false (inference_only rec).
Proof.
  intros H. constructor; simpl.
  - intros g L e ty _ Hc. discriminate.
  - exact (fms_infer_type H).
  - exact (fms_infer_type H).
  - exact (fms_whnf_core H).
  - exact (fms_whnf H).
  - exact (fms_defeq H).
  - exact (fms_eager_defeq H).
Qed.

Lemma application_type_defeq_full_sound env venv ps chk rec g L a dom dom' aty aty' :
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L dom dom' ->
  VTrExpr env venv ps L aty aty' ->
  application_type_defeq rec g a dom aty = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) dom' aty'.
Proof.
  intros Hms Hctx Hdom Haty Happ.
  unfold application_type_defeq in Happ.
  destruct (is_eager_reduce_argument a).
  - eapply (fms_eager_defeq Hms); eassumption.
  - eapply (fms_defeq Hms); eassumption.
Qed.



(* ========================================================================= *)
(* 3. Reduction Soundness (Beta, Delta, Nat, Quotient, Recursor, Projection) *)
(* ========================================================================= *)

Fixpoint replace_nth {A : Type} (n : nat) (x : A) (xs : list A) : list A :=
  match n, xs with
  | _, [] => []
  | 0, _ :: rest => x :: rest
  | S n', y :: rest => y :: replace_nth n' x rest
  end.

Lemma replace_nth_length {A : Type} n (x : A) xs :
  List.length (replace_nth n x xs) = List.length xs.
Proof.
  revert xs. induction n as [|n IH]; intros [|y r]; simpl; auto.
Qed.

Lemma replace_nth_same {A : Type} n (x : A) xs :
  n < List.length xs -> nth_error (replace_nth n x xs) n = Some x.
Proof.
  revert xs. induction n as [|n IH]; intros [|y r] H; simpl in *; try lia; auto.
  apply IH; lia.
Qed.

Lemma replace_nth_firstn {A : Type} k n (x : A) xs :
  k <= n -> firstn k (replace_nth n x xs) = firstn k xs.
Proof.
  revert n xs. induction k as [|k IH]; intros n xs H; simpl; [reflexivity |].
  destruct n as [|n']; [lia |].
  destruct xs as [|y r]; simpl; [reflexivity |].
  f_equal. apply IH; lia.
Qed.

Lemma replace_nth_skipn {A : Type} k n (x : A) xs :
  n < k -> skipn k (replace_nth n x xs) = skipn k xs.
Proof.
  revert n xs. induction k as [|k IH]; intros n xs H; [lia |].
  destruct xs as [|y r]; simpl; [destruct n; reflexivity |].
  destruct n as [|n']; simpl; [reflexivity |].
  apply IH; lia.
Qed.

Lemma replace_nth_other {A : Type} i n (x : A) xs :
  i <> n -> nth_error (replace_nth n x xs) i = nth_error xs i.
Proof.
  revert n xs. induction i as [|i IH]; intros [|n] [|y r] H; simpl in *; try congruence; auto.
Qed.

Lemma Forall2_nth_error {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys ->
  forall i x, nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ R x y.
Proof.
  induction 1 as [| a b r1 r2 Hab Hr IH]; intros [|i] x H; simpl in *; try discriminate.
  - inversion H; subst. exists b. auto.
  - exact (IH i x H).
Qed.

Lemma Forall2_nth_error_r {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys ->
  forall i y, nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  induction 1 as [| a b r1 r2 Hab Hr IH]; intros [|i] y H; simpl in *; try discriminate.
  - inversion H; subst. exists a. auto.
  - exact (IH i y H).
Qed.

Lemma Forall2_firstn {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> forall k, Forall2 R (firstn k xs) (firstn k ys).
Proof.
  induction 1; intros [|k]; simpl; constructor; auto.
Qed.

Lemma Forall2_skipn {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> forall k, Forall2 R (skipn k xs) (skipn k ys).
Proof.
  induction 1; intros [|k]; simpl; try constructor; auto.
Qed.

Lemma Forall2_length {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> List.length xs = List.length ys.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall2_VTrExprS_to_VTrExpr env venv ps L xs ys :
  Forall2 (VTrExprS env venv ps L) xs ys ->
  Forall2 (VTrExpr env venv ps L) xs ys.
Proof.
  induction 1; constructor; [apply VTrExprS_to_VTrExpr; assumption | assumption].
Qed.

Lemma Forall2_VIsDefEqU_replace_nth env U G args k y :
  Forall (VExprWF env U G) args ->
  forall x, nth_error args k = Some x ->
  VIsDefEqU env U G x y ->
  Forall2 (VIsDefEqU env U G) args (replace_nth k y args).
Proof.
  intros Hwf. revert k.
  induction Hwf as [| a r Ha Hr IH]; intros [|k] x Hnth Hxy; simpl in *; try discriminate.
  - inversion Hnth; subst x. constructor; [exact Hxy |].
    clear -Hr. induction Hr; constructor; assumption.
  - constructor; [exact Ha | exact (IH k x Hnth Hxy)].
Qed.

Lemma vapps_args_wf env U G f args :
  VEnvWF env ->
  VCtxWF env U G ->
  VExprWF env U G (vapps f args) ->
  Forall (VExprWF env U G) args.
Proof.
  intros Hwf HG. revert f.
  induction args as [|a r IH]; intros f H; [constructor |].
  simpl in H.
  assert (Hfa : VExprWF env U G (VApp f a)).
  { change (VApp f a) with (vapps (VApp f a) []).
    eapply vapps_wf_prefix with (ys := r); [exact Hwf | exact HG | exact H]. }
  destruct Hfa as [T HT].
  destruct (VHasType_app_inv Hwf HG HT) as [A [B [_ Ha]]].
  constructor; [exists A; exact Ha | exact (IH (VApp f a) H)].
Qed.

Lemma core_find_rule_In cn rules r :
  core_find_rule cn rules = Some r -> In r rules.
Proof.
  induction rules as [|r0 rest IH]; simpl; [discriminate |].
  destruct (name_eqb cn (rule_ctor r0)).
  - intros H. inversion H. left. reflexivity.
  - intros H. right. exact (IH H).
Qed.

(* 3a. Beta reduction (`core_beta_collect` / `core_beta`) *)
Lemma instantiate_many_eq_subst_many e vs :
  instantiate_many e vs = subst_many 0 vs e.
Proof. destruct vs; [symmetry; apply subst_many_nil | reflexivity]. Qed.

Lemma core_beta_collect_sound env venv ps :
  VEnvSound env venv ->
  forall args L head vals e',
    VLCtxWF venv (List.length ps) L ->
    VTrExpr env venv ps L
      (core_apps (instantiate_many head vals) args) e' ->
    VTrExpr env venv ps L (core_beta_collect head args vals) e'.
Proof.
  intros Hves.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  induction args as [|a rest IH]; intros L head vals e' HwfL Htr; simpl in *.
  - destruct head; exact Htr.
  - destruct head as [i|x|x|u|c us|f b|nm bi A body|nm bi A B|nm A w b nd|l|own idx b|b];
      try exact Htr.
    apply IH; [exact HwfL |].
    rewrite !instantiate_many_eq_subst_many in *.
    rewrite subst_many_cons.
    destruct (VTrExpr_core_apps_inv Htr) as [fa' [rest' [Heq_all [Hfa Hrest]]]].
    inversion Hfa as [| | | | ? ? ? f' a' A0 B0 Hf_ty Ha_ty Htr_f Htr_a | | | | | | |]; subst.
    simpl in Htr_f.
    inversion Htr_f as [| | | | | ? ? ? ? ? A1 body1 HA1 Htr_A1 Htr_body1 | | | | | |]; subst.
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
    destruct (VHasType_lam_inv Hwf HG Hf_ty) as [_ [TB Hbody1_ty]].
    destruct HA1 as [u Hu].
    pose proof (VHasType_lam Hu Hbody1_ty) as Hlam_ty.
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG (VIsDefEq_uniqU Hwf Hinj HG Hf_ty Hlam_ty))
      as [[uA HA_eq] [uB HB_eq]].
    assert (Ha_A1 : VHasType venv (List.length ps) (vl_ctx L) a' A1)
      by (eapply VDF_defeqDF; [exact HA_eq | exact Ha_ty]).
    assert (Hbeta : VIsDefEq venv (List.length ps) (vl_ctx L)
        (VApp (VLam A1 body1) a') (vinst0 body1 a') (vinst0 TB a'))
      by (eapply VDF_beta; [exact Hbody1_ty | exact Ha_A1]).
    assert (Hinst : VTrExpr env venv ps L (instantiate (subst_many 1 vals body) a) (vinst0 body1 a')).
    { eapply VTrExpr_instantiate_lam;
        [exact Hves | exact HwfL | exact Ha_A1
        | apply VTrExprS_to_VTrExpr; exact Htr_a
        | apply VTrExprS_to_VTrExpr; exact Htr_body1]. }
    assert (Hrest_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) rest' rest').
    { clear -Hrest. induction Hrest as [| x y r1 r2 Hxy Hr IHr]; constructor;
        [destruct (VTrExprS_has_type Hxy) as [T HT]; exists T; exact HT | exact IHr]. }
    assert (Hwf_l : VExprWF venv (List.length ps) (vl_ctx L) (vapps (VApp (VLam A1 body1) a') rest'))
      by (exact (VIsDefEqU_refl_l Heq_all)).
    destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_l
                (ex_intro _ (vinst0 TB a') Hbeta) Hrest_eq)
      as [Hwf_r Hbeta_apps].
    eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
    + eapply VTrExpr_core_apps;
        [exact Hves | exact HwfL | exact Hinst
        | apply Forall2_VTrExprS_to_VTrExpr; exact Hrest | exact Hwf_r].
    + eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        apply VIsDefEqU_symm; exact Hbeta_apps | exact Heq_all].
Qed.

Lemma core_beta_sound env venv ps L head args e' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L (core_apps head args) e' ->
  VTrExpr env venv ps L (core_beta head args) e'.
Proof.
  intros Hves HwfL Htr. unfold core_beta.
  apply core_beta_collect_sound; [exact Hves | exact HwfL | exact Htr].
Qed.

Lemma map_vlevel_inst_vlevel_params_aux ls :
  forall m k, k + m <= List.length ls ->
    map (vlevel_inst ls) (map VLParam (seq k m)) = firstn m (skipn k ls).
Proof.
  induction m as [|m IH]; intros k Hk; simpl; [reflexivity |].
  destruct (nth_error ls k) as [v|] eqn:Hnth.
  - assert (Hskip : skipn k ls = v :: skipn (S k) ls).
    { clear -Hnth. revert k Hnth. induction ls as [|x xs IHs]; intros [|k] H; simpl in *; try discriminate.
      - inversion H. reflexivity.
      - exact (IHs k H). }
    rewrite Hskip. simpl. f_equal.
    + rewrite nth_error_nth' with (d := VLZero) in Hnth by lia. inversion Hnth. reflexivity.
    + apply IH. lia.
  - apply nth_error_None in Hnth. lia.
Qed.

Lemma map_vlevel_inst_vlevel_params ls :
  map (vlevel_inst ls) (vlevel_params (List.length ls)) = ls.
Proof.
  unfold vlevel_params.
  rewrite map_vlevel_inst_vlevel_params_aux by lia.
  simpl. apply firstn_all.
Qed.

(* 3b. Delta unfolding (`core_unfold`) *)
Lemma core_unfold_sound env venv ps L e e' e1 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L e e' ->
  core_unfold env ps e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves HwfL Htr Hunf.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_unfold in Hunf.
  pose proof (core_spine_core_apps e []) as Hsp.
  destruct (core_spine e []) as [head args] eqn:E.
  simpl in Hsp. rewrite <- Hsp in Htr.
  destruct head as [| | | |n us| | | | | | |]; try discriminate.
  destruct (get_constant env ps n us) as [d|err|why] eqn:Hget; simpl in Hunf; try discriminate.
  destruct (get_constant_sound Hves HwfL Hget)
    as [ci [us' [Hfind [_ [Hci [Huv [Hlen_us [Hus' [Hwf_us [_ Hc_ty]]]]]]]]]].
  assert (Hkind_ok :
    match decl_kind_of d with DDefinition | DTheorem | DPrimitive _ => True | _ => False end /\
    exists val, decl_value d = Some val /\
      e1 = core_apps (instantiate_levels (decl_params d) us val) args).
  { destruct (decl_kind_of d); try discriminate;
    destruct (decl_value d) as [val|] eqn:Hval; try discriminate;
    inversion Hunf; subst e1; (split; [exact I | exists val; auto]). }
  destruct Hkind_ok as [Hkind [val [Hval ->]]].
  destruct (ves_delta Hves Hfind Hkind Hval) as [ci2 [val' [Hci2 [Huv2 [Hval_tr [Hval_cl Hdf]]]]]].
  rewrite Hci in Hci2. inversion Hci2; subst ci2; clear Hci2.
  destruct (VTrExpr_core_apps_inv Htr) as [h' [args' [Heq_all [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? ci3 ? us3 Hci3 Hus3 Hlen3 | | | | | | | |]; subst.
  assert (Hus_eq : us' = us3).
  { clear -Hus' Hus3. revert us3 Hus3.
    induction Hus' as [| u u' r r' Hu Hr IH]; intros us3 H;
      inversion H as [| ? u3 ? r3 Hu3 Hr3]; subst; [reflexivity |].
    unfold TrLevel in *. rewrite Hu in Hu3. inversion Hu3; subst. f_equal. auto. }
  subst us3.
  assert (Hdelta : VIsDefEq venv (List.length ps) (vl_ctx L)
      (VConst n us') (vinstL us' val') (vinstL us' (vc_type ci))).
  { assert (Hlen_us' : List.length us' = vc_uvars ci)
      by (rewrite <- (TrLevels_length Hus'); exact Hlen_us).
    pose proof (@VDF_extra venv (List.length ps) (vl_ctx L) _ us' Hdf Hwf_us Hlen_us') as Hd.
    simpl in Hd. rewrite <- Hlen_us' in Hd.
    rewrite map_vlevel_inst_vlevel_params in Hd. exact Hd. }
  assert (Hval_inst : VTrExpr env venv ps L
      (instantiate_levels (decl_params d) us val) (vinstL us' val')).
  { rewrite instantiate_levels_correct.
    apply VTrExpr_closed_to_any; [exact Hwf |].
    eapply VTrExpr_subst_levels; [lia | exact Hus' | exact Hval_tr]. }
  assert (Hargs_refl : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) args' args').
  { clear -Htr_args. induction Htr_args as [| x y r1 r2 Hxy Hr IH]; constructor;
      [destruct (VTrExprS_has_type Hxy) as [T HT]; exists T; exact HT | exact IH]. }
  assert (Hwf_l : VExprWF venv (List.length ps) (vl_ctx L) (vapps (VConst n us') args'))
    by (exact (VIsDefEqU_refl_l Heq_all)).
  destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_l
              (ex_intro _ (vinstL us' (vc_type ci)) Hdelta) Hargs_refl)
    as [Hwf_r Hdelta_apps].
  eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
  - eapply VTrExpr_core_apps;
      [exact Hves | exact HwfL | exact Hval_inst
      | apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args | exact Hwf_r].
  - eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hdelta_apps | exact Heq_all].
Qed.

(* 3c. Native hooks & Nat primitives *)
Lemma core_reduce_native_sound e e1 :
  core_reduce_native e = Accept (Some e1) -> False.
Proof.
  unfold core_reduce_native.
  destruct e as [| | | | |f a| | | | | |]; try discriminate.
  destruct f as [| | | |n us| | | | | | |]; try discriminate.
  destruct us; try discriminate.
  destruct a as [| | | |m vs| | | | | | |]; try discriminate.
  destruct (name_eqb n core_reduce_bool_name || name_eqb n core_reduce_nat_name); discriminate.
Qed.

Lemma core_nat_value_sound env venv ps L e e' n :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_nat_ready env = true ->
  VTrExpr env venv ps L e e' ->
  core_nat_value e = Some n ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) (natLit n) e'.
Proof.
  intros Hves HwfL Hnat Htr Hval.
  unfold core_nat_value in Hval.
  destruct e as [| | | |c us| | | | |lit| |]; try discriminate.
  - destruct us; try discriminate.
    destruct (name_eqb c core_zero_name) eqn:Ez; [|discriminate].
    apply name_eqb_eq in Ez. subst c. inversion Hval; subst n.
    destruct (VTrExpr_inv_const Htr) as [ci [us' [_ [Hus' [_ [_ Heq]]]]]].
    inversion Hus'; subst us'. rewrite natLit_0. exact Heq.
  - destruct lit as [m|s]; try discriminate.
    inversion Hval; subst m.
    destruct (VTrExpr_inv_natlit Htr) as [_ [_ Heq]]. exact Heq.
Qed.

Lemma core_binary_nat_sound env venv ps L fuel n d op a b res :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_nat_ready env = true ->
  find_decl n env = Some d ->
  decl_kind_of d = DPrimitive op ->
  core_binary_nat fuel env op a b = Accept (Some res) ->
  exists res_v rty,
    VTrExpr env venv ps L res res_v /\
    VIsDefEq venv (List.length ps) (vl_ctx L)
      (VApp (VApp (VConst n []) (natLit a)) (natLit b)) res_v rty.
Proof.
  intros Hves HwfL Hnat Hfind Hkind Hbin.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  assert (Hspec : exists res_v rty,
    vbinary_prim_spec op a b = Some (res_v, rty) /\
    (rty = vbool_ty -> core_bool_ready env = true) /\
    VTrExpr env venv ps L res res_v).
  { unfold core_binary_nat in Hbin. cbv zeta beta in Hbin.
    destruct op; try discriminate;
      try (inversion Hbin; subst res;
           eexists _, vnat_ty; split;
           [reflexivity
           | split;
             [intros Heq; unfold vnat_ty, vbool_ty, core_nat_name, core_bool_name in Heq; discriminate
             | apply VTrExprS_to_VTrExpr; eapply VTrExprS_natlit;
               [exact Hnat | eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]]]]).
    - (* PNatPow *)
      destruct (b <=? core_pow_max_exp)%N; try discriminate.
      inversion Hbin; subst res.
      exists (natLit (N.pow a b)), vnat_ty. split;
        [reflexivity
        | split;
          [intros Heq; unfold vnat_ty, vbool_ty, core_nat_name, core_bool_name in Heq; discriminate
          | apply VTrExprS_to_VTrExpr; eapply VTrExprS_natlit;
            [exact Hnat | eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]]]].
    - (* PNatBEq *)
      destruct (core_bool_ready env) eqn:Hbool; [|discriminate].
      inversion Hbin; subst res.
      destruct (hp_bool (ves_prims Hves) Hbool) as [_ [Hbf Hbt]].
      exists (vboolLit (N.eqb a b)), vbool_ty.
      split; [reflexivity | split; [intros _; reflexivity |]].
      apply VTrExprS_to_VTrExpr. unfold vboolLit.
      destruct (N.eqb a b).
      + pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
            (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hbt)) as Ht.
        simpl in Ht. destruct (VHasType_const_inv Hwf HG Ht) as [ci [Hci [_ Hlen]]].
        eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
      + pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
            (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hbf)) as Hf.
        simpl in Hf. destruct (VHasType_const_inv Hwf HG Hf) as [ci [Hci [_ Hlen]]].
        eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
    - (* PNatBLE *)
      destruct (core_bool_ready env) eqn:Hbool; [|discriminate].
      inversion Hbin; subst res.
      destruct (hp_bool (ves_prims Hves) Hbool) as [_ [Hbf Hbt]].
      exists (vboolLit (N.leb a b)), vbool_ty.
      split; [reflexivity | split; [intros _; reflexivity |]].
      apply VTrExprS_to_VTrExpr. unfold vboolLit.
      destruct (N.leb a b).
      + pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
            (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hbt)) as Ht.
        simpl in Ht. destruct (VHasType_const_inv Hwf HG Ht) as [ci [Hci [_ Hlen]]].
        eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
      + pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
            (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hbf)) as Hf.
        simpl in Hf. destruct (VHasType_const_inv Hwf HG Hf) as [ci [Hci [_ Hlen]]].
        eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
    - (* PNatShiftLeft *)
      destruct (b <=? core_pow_max_exp)%N; try discriminate.
      inversion Hbin; subst res.
      exists (natLit (N.shiftl a b)), vnat_ty. split;
        [reflexivity
        | split;
          [intros Heq; unfold vnat_ty, vbool_ty, core_nat_name, core_bool_name in Heq; discriminate
          | apply VTrExprS_to_VTrExpr; eapply VTrExprS_natlit;
            [exact Hnat | eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]]]].
    - (* PNatShiftRight *)
      destruct (core_shiftr a b) as [v|] eqn:Hsr; [|discriminate].
      inversion Hbin; subst res.
      rewrite (core_shiftr_sound a b v Hsr).
      exists (natLit (N.shiftr a b)), vnat_ty. split;
        [reflexivity
        | split;
          [intros Heq; unfold vnat_ty, vbool_ty, core_nat_name, core_bool_name in Heq; discriminate
          | apply VTrExprS_to_VTrExpr; eapply VTrExprS_natlit;
            [exact Hnat | eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]]]]. }
  destruct Hspec as [res_v [rty [Hsp [Hbool_ok Hres_tr]]]].
  pose proof (hp_binary (ves_prims Hves) Hnat Hfind Hkind Hsp Hbool_ok) as Hdf0.
  simpl in Hdf0.
  pose proof (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hdf0) as Hi.
  simpl in Hi. rewrite !vinstL_natLit in Hi.
  assert (Hrty_inst : vinstL [] res_v = res_v /\ vinstL [] rty = rty).
  { destruct op; simpl in Hsp; try discriminate;
      inversion Hsp; subst;
      try (split; [apply vinstL_natLit | reflexivity]);
      try (split; [unfold vboolLit; destruct (N.eqb a b) || destruct (N.leb a b); reflexivity | reflexivity]). }
  destruct Hrty_inst as [Hr1 Hr2]. rewrite Hr1, Hr2 in Hi.
  exists res_v, rty. split; [exact Hres_tr | exact (VIsDefEq_weak0 (vl_ctx L) Hcl Hi)].
Qed.

Lemma core_reduce_nat_sound env venv ps chk rec fuel g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  core_reduce_nat rec fuel env g e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hred.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  rewrite core_reduce_nat_dispatch_equivalent in Hred.
  unfold core_reduce_nat_reference in Hred.
  destruct (core_nat_ready env) eqn:Hnat; simpl in Hred; [|discriminate].
  pose proof (core_spine_core_apps e []) as Hsp.
  destruct (core_spine e []) as [head args] eqn:E. simpl in Hsp.
  rewrite <- Hsp in Htr.
  destruct head as [| | | |n us| | | | | | |]; try discriminate.
  destruct us; try discriminate.
  destruct args as [|a [|b [|c rest]]]; try discriminate.
  - (* Unary: Nat.succ or PNatPred *)
    destruct (name_eqb n core_succ_name) eqn:Esucc.
    + apply name_eqb_eq in Esucc. subst n.
      destruct (whnf_method rec g a) as [aw|err|why] eqn:Hwa; simpl in Hred; try discriminate.
      destruct (core_nat_value aw) as [av|] eqn:Hav; [|discriminate].
      inversion Hred; subst e1; clear Hred.
      destruct (VTrExpr_inv_app Htr) as [f' [a' [A [B [Hf_ty [Ha_ty [Htr_f [Htr_a Heq_app]]]]]]]].
      destruct (VTrExpr_inv_const Htr_f) as [_ [us' [_ [Hus' [_ [_ Hf_eq]]]]]].
      inversion Hus'; subst us'.
      pose proof (fms_whnf Hms Hctx Htr_a Hwa) as Haw_tr.
      pose proof (core_nat_value_sound Hves HwfL Hnat Haw_tr Hav) as Hav_eq.
      assert (Heq_succ : VIsDefEqU venv (List.length ps) (vl_ctx L)
          (natLit (N.succ av)) (VApp f' a')).
      { rewrite natLit_succ.
        assert (Hwf_r : VExprWF venv (List.length ps) (vl_ctx L) (vapps f' [a']))
          by (simpl; exact (VIsDefEqU_refl_l Heq_app)).
        destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_r (VIsDefEqU_symm Hf_eq)
                    (@Forall2_cons _ _ _ _ _ _ _ (VIsDefEqU_symm Hav_eq) (Forall2_nil _))) as [_ Hc].
        apply VIsDefEqU_symm. exact Hc. }
      eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_natlit; [exact Hnat |].
        eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat].
      * eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Heq_succ | exact Heq_app].
    + destruct (find_decl n env) as [d|] eqn:Hfind; [|discriminate].
      destruct (decl_kind_of d) eqn:Hkind; try discriminate.
      destruct p; try discriminate.
      destruct (whnf_method rec g a) as [aw|err|why] eqn:Hwa; simpl in Hred; try discriminate.
      destruct (core_nat_value aw) as [av|] eqn:Hav; [|discriminate].
      inversion Hred; subst e1; clear Hred.
      destruct (VTrExpr_inv_app Htr) as [f' [a' [A [B [Hf_ty [Ha_ty [Htr_f [Htr_a Heq_app]]]]]]]].
      destruct (VTrExpr_inv_const Htr_f) as [_ [us' [_ [Hus' [_ [_ Hf_eq]]]]]].
      inversion Hus'; subst us'.
      pose proof (fms_whnf Hms Hctx Htr_a Hwa) as Haw_tr.
      pose proof (core_nat_value_sound Hves HwfL Hnat Haw_tr Hav) as Hav_eq.
      pose proof (hp_pred (ves_prims Hves) Hnat Hfind Hkind av) as Hpred0.
      pose proof (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hpred0) as Hpred1.
      simpl in Hpred1. rewrite !vinstL_natLit in Hpred1.
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl Hpred1) as Hpred.
      assert (Hwf_r : VExprWF venv (List.length ps) (vl_ctx L) (vapps f' [a']))
        by (simpl; exact (VIsDefEqU_refl_l Heq_app)).
      destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_r (VIsDefEqU_symm Hf_eq)
                  (@Forall2_cons _ _ _ _ _ _ _ (VIsDefEqU_symm Hav_eq) (Forall2_nil _))) as [_ Hc].
      simpl in Hc.
      eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_natlit; [exact Hnat |].
        eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat].
      * eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
          exists vnat_ty; exact (VDF_symm Hpred) |].
        eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
          apply VIsDefEqU_symm; exact Hc | exact Heq_app].
  - (* Binary primitive *)
    destruct (find_decl n env) as [d|] eqn:Hfind; [|discriminate].
    destruct (decl_kind_of d) eqn:Hkind; try discriminate.
    assert (Hbin_step : exists aw bw av bv,
      whnf_method rec g a = Accept aw /\
      whnf_method rec g b = Accept bw /\
      core_nat_value aw = Some av /\
      core_nat_value bw = Some bv /\
      core_binary_nat fuel env p av bv = Accept (Some e1)).
    { assert (Hp_ok :
        (aw <- whnf_method rec g a;;
         bw <- whnf_method rec g b;;
         match core_nat_value aw, core_nat_value bw with
         | Some av, Some bv => core_binary_nat fuel env p av bv
         | _, _ => Accept None
         end) = Accept (Some e1)).
      { destruct p; try discriminate; exact Hred. }
      destruct (whnf_method rec g a) as [aw|err|why] eqn:Hwa; simpl in Hp_ok; try discriminate.
      destruct (whnf_method rec g b) as [bw|err|why] eqn:Hwb; simpl in Hp_ok; try discriminate.
      destruct (core_nat_value aw) as [av|] eqn:Hav; try discriminate.
      destruct (core_nat_value bw) as [bv|] eqn:Hbv; try discriminate.
      exists aw, bw, av, bv. auto. }
    destruct Hbin_step as [aw [bw [av [bv [Hwa [Hwb [Hav [Hbv Hbin]]]]]]]].
    destruct (core_binary_nat_sound Hves HwfL Hnat Hfind Hkind Hbin) as [res_v [rty [Hres_tr Hbin_eq]]].
    destruct (VTrExpr_core_apps_inv Htr) as [f' [args' [Heq_all [Htr_f Htr_args]]]].
    inversion Htr_args as [| ? a' ? ? Htr_a Htr_r1]; subst.
    inversion Htr_r1 as [| ? b' ? ? Htr_b Htr_r2]; subst.
    inversion Htr_r2; subst.
    destruct (VTrExpr_inv_const (VTrExprS_to_VTrExpr Htr_f)) as [_ [us' [_ [Hus' [_ [_ Hf_eq]]]]]].
    inversion Hus'; subst us'.
    pose proof (fms_whnf Hms Hctx (VTrExprS_to_VTrExpr Htr_a) Hwa) as Haw_tr.
    pose proof (fms_whnf Hms Hctx (VTrExprS_to_VTrExpr Htr_b) Hwb) as Hbw_tr.
    pose proof (core_nat_value_sound Hves HwfL Hnat Haw_tr Hav) as Hav_eq.
    pose proof (core_nat_value_sound Hves HwfL Hnat Hbw_tr Hbv) as Hbv_eq.
    destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_all)
                (VIsDefEqU_symm Hf_eq)
                (@Forall2_cons _ _ _ _ _ _ _ (VIsDefEqU_symm Hav_eq)
                  (@Forall2_cons _ _ _ _ _ _ _ (VIsDefEqU_symm Hbv_eq) (Forall2_nil _)))) as [_ Hc].
    simpl in Hc.
    eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | exact Hres_tr |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists rty; exact (VDF_symm Hbin_eq) |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hc | exact Heq_all].
Qed.

(* 3d. Quotient reduction (`core_reduce_quotient`) *)
Lemma core_reduce_quotient_sound env venv ps chk rec g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  core_reduce_quotient rec env g e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hred.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_reduce_quotient in Hred.
  pose proof (core_spine_core_apps e []) as Hsp.
  destruct (core_spine e []) as [head args] eqn:E. simpl in Hsp.
  rewrite <- Hsp in Htr.
  destruct head as [| | | |n us| | | | | | |]; try discriminate.
  destruct (find_decl n env) as [d|] eqn:Hfind; [|discriminate].
  assert (Hidx : exists index,
    (decl_kind_of d = DQuotient QLift /\ index = 5 \/
     decl_kind_of d = DQuotient QInd /\ index = 4) /\
    match nth_error args index, nth_error args 3 with
    | Some major, Some fn =>
        major0 <- whnf_method rec g major ;;
        let '(ctor, cargs) := core_spine major0 [] in
        match ctor, cargs with
        | EConst cn _, [_; _; representative] =>
            match find_decl cn env with
            | Some cd =>
                match decl_kind_of cd with
                | DQuotient QCtor =>
                    Accept (Some (core_apps (EApp fn representative) (skipn (S index) args)))
                | _ => Accept None
                end
            | None => Accept None
            end
        | _, _ => Accept None
        end
    | _, _ => Accept None
    end = Accept (Some e1)).
  { destruct (decl_kind_of d) eqn:Hk; try discriminate.
    destruct q; try discriminate; [exists 5 | exists 4]; split; auto. }
  destruct Hidx as [index [Hk_idx Hstep]].
  destruct (nth_error args index) as [major|] eqn:Hmaj; [|discriminate].
  destruct (nth_error args 3) as [fn|] eqn:Hfn; [|discriminate].
  destruct (whnf_method rec g major) as [maj_w|err|why] eqn:Hwmaj; simpl in Hstep; try discriminate.
  pose proof (core_spine_core_apps maj_w []) as Hspm.
  destruct (core_spine maj_w []) as [ctor cargs] eqn:Em. simpl in Hspm.
  destruct ctor as [| | | |cn cus| | | | | | |]; try discriminate.
  destruct cargs as [|a1 [|a2 [|rep [|x rest]]]]; try discriminate.
  destruct (find_decl cn env) as [cd|] eqn:Hfind_c; [|discriminate].
  destruct (decl_kind_of cd) eqn:Hkc; try discriminate.
  destruct q; try discriminate.
  inversion Hstep; subst e1; clear Hstep.
  destruct (VTrExpr_core_apps_inv Htr) as [h' [args' [Heq_all [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? ci ? us' Hci Hus' Hlen_us | | | | | | | |]; subst.
  destruct (Forall2_nth_error Htr_args Hmaj) as [maj' [Hmaj' Htr_maj]].
  destruct (Forall2_nth_error Htr_args Hfn) as [fn' [Hfn' Htr_fn]].
  pose proof (fms_whnf Hms Hctx (VTrExprS_to_VTrExpr Htr_maj) Hwmaj) as Hmaj_w.
  destruct (VTrExpr_core_apps_inv Hmaj_w) as [c' [cargs' [Heq_maj [Htr_c Htr_cargs]]]].
  inversion Htr_c as [| | | ? ? cic ? cus' Hcic Hcus' Hlen_cus | | | | | | | |]; subst.
  inversion Htr_cargs as [| ? a1' ? ? Htr_a1 Htr_ca1]; subst.
  inversion Htr_ca1 as [| ? a2' ? ? Htr_a2 Htr_ca2]; subst.
  inversion Htr_ca2 as [| ? rep' ? ? Htr_rep Htr_ca3]; subst.
  inversion Htr_ca3; subst.
  set (args'' := replace_nth index (vapps (VConst cn cus') [a1'; a2'; rep']) args').
  assert (Hargs_wf : Forall (VExprWF venv (List.length ps) (vl_ctx L)) args')
    by (eapply vapps_args_wf; [exact Hwf | exact HG | exact (VIsDefEqU_refl_l Heq_all)]).
  assert (Hargs_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) args' args'').
  { apply Forall2_VIsDefEqU_replace_nth with (x := maj');
      [exact Hargs_wf | exact Hmaj' | apply VIsDefEqU_symm; exact Heq_maj]. }
  assert (Hh_refl : VIsDefEqU venv (List.length ps) (vl_ctx L) (VConst n us') (VConst n us')).
  { destruct (VTrExprS_has_type Htr_h) as [T HT]. exists T. exact HT. }
  destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_all) Hh_refl Hargs_eq)
    as [Hwf_args'' Hcongr].
  assert (Hmaj'' : nth_error args'' index = Some (vapps (VConst cn cus') [a1'; a2'; rep'])).
  { apply replace_nth_same. apply nth_error_Some. rewrite Hmaj'. discriminate. }
  assert (Hfn'' : nth_error args'' 3 = Some fn').
  { unfold args''. rewrite replace_nth_other; [exact Hfn' |].
    destruct Hk_idx as [[_ ->] | [_ ->]]; lia. }
  pose proof (ves_quot_red Hves HG Hfind Hk_idx Hfind_c Hkc Hmaj'' Hfn'' Hwf_args'') as Hqred.
  unfold args'' in Hqred. rewrite replace_nth_skipn in Hqred by lia.
  eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
  - change (core_apps (EApp fn rep) (match args with [] => [] | _ :: l => skipn index l end))
      with (core_apps fn (rep :: skipn (S index) args)).
    change (vapps (VApp fn' rep') (skipn (S index) args'))
      with (vapps fn' (rep' :: skipn (S index) args')).
    eapply VTrExpr_core_apps; [exact Hves | exact HwfL | apply VTrExprS_to_VTrExpr; exact Htr_fn | |].
    + constructor; [apply VTrExprS_to_VTrExpr; exact Htr_rep |].
      apply Forall2_skipn. apply Forall2_VTrExprS_to_VTrExpr. exact Htr_args.
    + exact (VIsDefEqU_refl_r Hqred).
  - eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hqred |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hcongr | exact Heq_all].
Qed.

(* 3e. `core_to_constructor` & `core_reduce_recursor` *)
Lemma core_to_constructor_struct_branch env venv ps rec fuel g L owner k_rule reduced r' res :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L reduced r' ->
  (if negb (k_rule || core_structure env owner) then Accept reduced else
   ty <- infer_method rec g reduced ;;
   ty <- whnf_method rec g ty ;;
   let '(head, args) := core_spine ty [] in
   match head with
   | EConst n us =>
       if negb (name_eqb n owner) then Accept reduced else
       match core_make_structure env owner us args reduced with
       | Some candidate =>
           if k_rule then
             sort <- sort_of rec g ty ;;
             prop <- level_equiv fuel sort LZero ;;
             if prop then
               ct <- infer_method rec g candidate ;;
               ok <- defeq_method rec g ty ct ;;
               if ok then Accept candidate else Accept reduced
             else Accept reduced
           else
             sort <- sort_of rec g ty ;;
             if core_level_positive sort then Accept candidate else Accept reduced
       | None => Accept reduced
       end
   | _ => Accept reduced
   end) = Accept res ->
  VTrExpr env venv ps L res r'.
Proof.
  intros Hves Hms Hctx Hred Hstep.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  destruct (k_rule || core_structure env owner) eqn:Hkc; simpl in Hstep;
    [| inversion Hstep; subst; exact Hred].
  destruct (infer_method rec g reduced) as [ty0|err|why] eqn:Hinf; simpl in Hstep; try discriminate.
  destruct (whnf_method rec g ty0) as [ty|err|why] eqn:Hwty; simpl in Hstep; try discriminate.
  pose proof (core_spine_core_apps ty []) as Hsp.
  destruct (core_spine ty []) as [head args] eqn:Esp. simpl in Hsp.
  destruct head as [| | | |n us| | | | | | |];
    try (inversion Hstep; subst; exact Hred).
  destruct (name_eqb n owner) eqn:Eown; simpl in Hstep;
    [| inversion Hstep; subst; exact Hred].
  apply name_eqb_eq in Eown. subst n.
  destruct (core_make_structure env owner us args reduced) as [cand|] eqn:Hmk;
    [| inversion Hstep; subst; exact Hred].
  destruct (fms_infer_typed Hms Hctx Hred Hinf) as [ty' [Hty0_tr Hr_ty]].
  pose proof (fms_whnf Hms Hctx Hty0_tr Hwty) as Hty_tr.
  destruct k_rule.
  - (* K-rule: proof irrelevance at Prop! *)
    unfold sort_of in Hstep.
    destruct (infer_method rec g ty) as [st0|err|why] eqn:Hist; simpl in Hstep; try discriminate.
    destruct (whnf_method rec g st0) as [st|err|why] eqn:Hwst; simpl in Hstep; try discriminate.
    destruct st as [| | |su| | | | | | | |]; simpl in Hstep; try discriminate.
    destruct (level_equiv fuel su LZero) as [prop|err|why] eqn:Hprop; simpl in Hstep; try discriminate.
    destruct prop; [| inversion Hstep; subst; exact Hred].
    destruct (infer_method rec g cand) as [ct|err|why] eqn:Hict; simpl in Hstep; try discriminate.
    destruct (defeq_method rec g ty ct) as [ok|err|why] eqn:Hok; simpl in Hstep; try discriminate.
    destruct ok; [| inversion Hstep; subst; exact Hred].
    inversion Hstep; subst res; clear Hstep.
    destruct (fms_infer_typed Hms Hctx Hty_tr Hist) as [st' [Hst0_tr Hty_st]].
    pose proof (fms_whnf Hms Hctx Hst0_tr Hwst) as Hst_tr.
    destruct (VTrExpr_inv_sort Hst_tr) as [su' [Hsu [Hsu_wf Hsu_eq]]].
    assert (Hty_prop : VHasType venv (List.length ps) (vl_ctx L) ty' (VSort VLZero)).
    { assert (Hsu0 : vlevel_equiv su' VLZero)
        by (eapply level_equiv_sound_vlevel with (v := LZero); [exact Hsu | reflexivity | exact Hprop]).
      eapply VDF_defeqDF.
      - eapply VDF_sortDF; [exact Hsu_wf | exact I | exact Hsu0].
      - eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hty_st |
          apply VIsDefEqU_symm; exact Hsu_eq]. }
    destruct (fms_infer Hms Hctx eq_refl Hict) as [cand' [ct' [Hcand_tr [Hct_tr Hcand_ct]]]].
    pose proof (fms_defeq Hms Hctx Hty_tr Hct_tr Hok) as Hty_ct.
    assert (Hcand_ty : VHasType venv (List.length ps) (vl_ctx L) cand' ty')
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hcand_ct |
            apply VIsDefEqU_symm; exact Hty_ct]).
    eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | exact Hcand_tr |].
    exists ty'. eapply VDF_proofIrrel; [exact Hty_prop | exact Hcand_ty | exact Hr_ty].
  - (* Structure eta branch *)
    simpl in Hkc.
    unfold sort_of in Hstep.
    destruct (infer_method rec g ty) as [st0|err|why] eqn:Hist; simpl in Hstep; try discriminate.
    destruct (whnf_method rec g st0) as [st|err|why] eqn:Hwst; simpl in Hstep; try discriminate.
    destruct st as [| | |su| | | | | | | |]; simpl in Hstep; try discriminate.
    destruct (core_level_positive su) eqn:Hpos; [| inversion Hstep; subst; exact Hred].
    inversion Hstep; subst res; clear Hstep.
    unfold core_make_structure in Hmk.
    destruct (core_inductive env owner) as [info|] eqn:Hi; [|discriminate].
    destruct (ind_ctors info) as [|ctor [|? ?]] eqn:Hctors; try discriminate.
    destruct (core_constructor env ctor) as [c|] eqn:Hc; [|discriminate].
    inversion Hmk; subst cand; clear Hmk.
    pose proof Hkc as Hkc_orig.
    unfold core_structure in Hkc. rewrite Hi in Hkc.
    apply andb_true_iff in Hkc as [Hkc1 _].
    apply andb_true_iff in Hkc1 as [_ Hidx0].
    apply Nat.eqb_eq in Hidx0.
    unfold core_inductive in Hi.
    destruct (find_decl owner env) as [d_ind|] eqn:Hfind_ind; [|discriminate].
    destruct (decl_kind_of d_ind) eqn:Hk_ind; try discriminate.
    inversion Hi; subst i; clear Hi.
    assert (Hi' : core_inductive env owner = Some info)
      by (unfold core_inductive; rewrite Hfind_ind, Hk_ind; reflexivity).
    unfold core_constructor in Hc.
    destruct (find_decl ctor env) as [d_ctor|] eqn:Hfind_ctor; [|discriminate].
    destruct (decl_kind_of d_ctor) eqn:Hk_ctor; try discriminate.
    inversion Hc; subst c0; clear Hc.
    destruct (ves_ind_shape Hves Hfind_ind Hk_ind Hfind_ctor Hk_ctor) as [_ Hsh].
    rewrite Hctors in Hsh.
    destruct (Hsh (or_introl eq_refl)) as [Hcnp Hclen_p].
    rewrite <- Hsp in Hty_tr.
    destruct (VTrExpr_core_apps_inv Hty_tr) as [h' [args' [Heq_ty [Htr_h Htr_args]]]].
    inversion Htr_h as [| | | ? ? ci_ind ? us' Hci_ind Hus' Hlen_us | | | | | | | |]; subst.
    assert (Hr_ty_v : VHasType venv (List.length ps) (vl_ctx L) r' (vapps (VConst owner us') args'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hr_ty |
            apply VIsDefEqU_symm; exact Heq_ty]).
    destruct (VIsDefEq_isType Hwf HG Hr_ty_v) as [u_s Hu_s].
    pose proof (ves_ind_type_arity Hves HG Hi' Hu_s) as Hlen_args'.
    rewrite Hidx0, Nat.add_0_r in Hlen_args'.
    pose proof (ves_constants Hves Hfind_ind) as Hdc_ind.
    rewrite Hk_ind in Hdc_ind.
    destruct Hdc_ind as [ci_i [Hci_i [Huv_i _]]].
    rewrite Hci_ind in Hci_i. inversion Hci_i; subst ci_i; clear Hci_i.
    assert (Hwf_us' : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus').
    assert (Hlen_us' : List.length us' = List.length (decl_params d_ctor)).
    { rewrite <- (TrLevels_length Hus'). lia. }
    destruct (ves_struct_eta Hves HG Hkc_orig
        Hi' Hctors Hfind_ctor Hk_ctor Hlen_args' Hcnp Hwf_us' Hlen_us' Hr_ty_v)
      as [Hprojs Heta].
    (* Show firstn (ctor_num_params c) args = args *)
    assert (Hlen_args : List.length args = ctor_num_params c).
    { rewrite (Forall2_length Htr_args), Hlen_args', Hcnp. reflexivity. }
    rewrite firstn_all2 by lia.
    pose proof (ves_constants Hves Hfind_ctor) as Hdc_ctor.
    rewrite Hk_ctor in Hdc_ctor.
    destruct Hdc_ctor as [ci_c [Hci_c [Huv_c _]]].
    assert (Hctor_tr : VTrExpr env venv ps L (EConst ctor us) (VConst ctor us')).
    { apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci_c | exact Hus' | lia]. }
    assert (Hprojs_tr : Forall2 (VTrExpr env venv ps L)
        (map (fun i => EProj owner i reduced) (seq 0 (ctor_num_fields c)))
        (map (fun i => vproj_expr owner i us' args' r') (seq 0 (ctor_num_fields c)))).
    { assert (Hgen : forall start len,
        start + len <= ctor_num_fields c ->
        Forall2 (VTrExpr env venv ps L)
          (map (fun i => EProj owner i reduced) (seq start len))
          (map (fun i => vproj_expr owner i us' args' r') (seq start len))).
      { intros start len. revert start. induction len as [|len IH]; intros start Hle; simpl; [constructor |].
        constructor; [| apply IH; lia].
        destruct (Hprojs start ltac:(lia)) as [fty Hp].
        destruct Hred as [r0 [Hr0 [Tr Hreq]]].
        assert (Hr0_ty : VHasType venv (List.length ps) (vl_ctx L) r0 (vapps (VConst owner us') args')).
        { eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hr_ty_v |
            apply VIsDefEqU_symm; exists Tr; exact Hreq]. }
        inversion Hp as [info0 ctor0 c0 d0 us0 ps0 idxs0 Hi0 Hc0 Hd0 Hk0 Hlt0 Hlp0 Hli0 Hw0 Hlu0 Hst0 Hpv0 Hty0].
        inversion Hpv0 as [Hpf_eq].
        assert (Hty0' : VHasType venv (List.length ps) (vl_ctx L)
            (VApp (vapps (VConst (proj_const_name owner start) us0) ps0) r') fty)
          by (rewrite <- Hpf_eq; exact Hty0).
        assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
            (vproj_expr owner start us0 ps0 r0) (vproj_expr owner start us0 ps0 r')).
        { unfold vproj_expr in *.
          destruct (VHasType_app_inv Hwf HG Hty0') as [Ap [Bp [Hpf Hpe]]].
          destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe (VIsDefEq_refl_r Hreq)) as [up Hcp].
          exists (vinst0 Bp r0).
          eapply VDF_appDF; [exact Hpf | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Hreq]]. }
        destruct Hpv_eq as [Tpv Hpv_eq'].
        exists (vproj_expr owner start us0 ps0 r0). split.
        - eapply VTrExprS_proj; [exact Hr0 |].
          eapply VTrProj_intro; try eassumption; [| reflexivity | exact (VIsDefEq_refl_l Hpv_eq')].
          eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hst0 |
            apply VIsDefEqU_symm; exists Tr; exact Hreq].
        - unfold vproj_expr in *. rewrite Hpf_eq. exists Tpv. exact Hpv_eq'. }
      apply Hgen; lia. }
    eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
    + eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hctor_tr | |].
      * apply Forall2_app; [apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args | exact Hprojs_tr].
      * exists (vapps (VConst owner us') args'). exact (VIsDefEq_refl_r Heta).
    + exists (vapps (VConst owner us') args'). exact (VDF_symm Heta).
Qed.

Lemma core_to_constructor_sound env venv ps rec fuel g L owner k_rule value v' res :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L value v' ->
  core_to_constructor rec fuel env g owner k_rule value = Accept res ->
  VTrExpr env venv ps L res v'.
Proof.
  intros Hves Hms Hctx Hv Htc.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_to_constructor in Htc.
  destruct (whnf_method rec g value) as [red|err|why] eqn:Hw; simpl in Htc; try discriminate.
  pose proof (fms_whnf Hms Hctx Hv Hw) as Hred.
  destruct red as [i|x|x|u|c us|f a|nm bi A b|nm bi A B|nm A w b nd|lit|own idx a|a];
    try (simpl in Htc;
         match type of Htc with
         | context [fst (core_spine ?r ?acc)] =>
             destruct (fst (core_spine r acc)) as [| | | |cn cus| | | | | | |];
             try (eapply core_to_constructor_struct_branch; eassumption);
             destruct (core_constructor env cn);
             [inversion Htc; subst; exact Hred | eapply core_to_constructor_struct_branch; eassumption]
         | context [core_constructor env ?cn] =>
             destruct (core_constructor env cn);
             [inversion Htc; subst; exact Hred | eapply core_to_constructor_struct_branch; eassumption]
         | _ => eapply core_to_constructor_struct_branch; eassumption
         end).
  destruct lit as [n|s].
  - destruct (name_eqb owner core_nat_name && core_nat_ready env) eqn:Enat;
      [| inversion Htc; subst; exact Hred].
    apply andb_true_iff in Enat as [_ Hnat].
    inversion Htc; subst res; clear Htc.
    destruct (VTrExpr_inv_natlit Hred) as [_ [_ Heq_n]].
    unfold core_nat_constructor. destruct n as [|p].
    + destruct (hp_nat (ves_prims Hves) Hnat) as [_ [Hz _]].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hz)) as Hz'.
      simpl in Hz'. destruct (VHasType_const_inv Hwf HG Hz') as [ci [Hci [_ Hlen]]].
      exists (VConst core_zero_name []). split;
        [eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia] |
         rewrite <- natLit_0; exact Heq_n].
    + destruct (hp_nat (ves_prims Hves) Hnat) as [_ [_ Hs]].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hs)) as Hs'.
      simpl in Hs'. destruct (VHasType_const_inv Hwf HG Hs') as [ci [Hci [_ Hlen]]].
      assert (Hp_ty : VHasType venv (List.length ps) (vl_ctx L) (natLit (N.pred (N.pos p))) vnat_ty)
        by (eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]).
      exists (VApp (VConst core_succ_name []) (natLit (N.pred (N.pos p)))). split.
      * eapply VTrExprS_app; [exact Hs' | exact Hp_ty |
           eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia] |
           eapply VTrExprS_natlit; [exact Hnat | exact Hp_ty]].
      * rewrite <- natLit_pred_succ by discriminate. exact Heq_n.
  - destruct (core_expand_string s) as [exp|err|why] eqn:Hexp; simpl in Htc; try discriminate.
    destruct (VTrExpr_inv_strlit Hred) as [s' [Hstr [Htrs [_ Heq_s]]]].
    assert (Hexp_tr : VTrExpr env venv ps L exp v').
    { exists s'. split; [eapply VTrExprS_core_expand_string; eassumption | exact Heq_s]. }
    exact (fms_whnf Hms Hctx Hexp_tr Htc).
Qed.

Lemma core_reduce_recursor_sound env venv ps rec fuel g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  core_reduce_recursor rec fuel env g e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hred.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_reduce_recursor in Hred.
  pose proof (core_spine_core_apps e []) as Hsp.
  destruct (core_spine e []) as [head args] eqn:Esp. simpl in Hsp.
  rewrite <- Hsp in Htr.
  destruct head as [| | | |rname us| | | | | | |]; try discriminate.
  destruct (find_decl rname env) as [d|] eqn:Hfind; [|discriminate].
  destruct (decl_kind_of d) eqn:Hkind; try discriminate.
  set (first_idx := rec_num_params r + rec_num_motives r + rec_num_minors r) in *.
  set (major_idx := first_idx + rec_num_indices r) in *.
  destruct (nth_error args major_idx) as [major|] eqn:Hmaj; [|discriminate].
  destruct (core_major_induct major_idx (decl_type d)) as [owner|] eqn:Hown; [|discriminate].
  destruct (core_to_constructor rec fuel env g owner (rec_k r) major) as [maj1|err|why] eqn:Htc;
    simpl in Hred; try discriminate.
  pose proof (core_spine_core_apps maj1 []) as Hspm.
  destruct (core_spine maj1 []) as [ctor fields] eqn:Ecm. simpl in Hspm.
  destruct ctor as [| | | |cn cus| | | | | | |]; try discriminate.
  destruct (core_find_rule cn (rec_rules r)) as [rule|] eqn:Hrule; [|discriminate].
  destruct (core_constructor env cn) as [ci|] eqn:Hci; [|discriminate].
  destruct (name_eqb (ctor_induct ci) owner &&
            Nat.eqb (List.length fields) (ctor_num_params ci + ctor_num_fields ci) &&
            Nat.eqb (rule_nfields rule) (ctor_num_fields ci) &&
            Nat.eqb (List.length us) (List.length (decl_params d))) eqn:Hchk;
    simpl in Hred; [|discriminate].
  inversion Hred; subst e1; clear Hred.
  apply andb_true_iff in Hchk as [Hchk1 Hlu].
  apply andb_true_iff in Hchk1 as [Hchk2 Hnf].
  apply andb_true_iff in Hchk2 as [Ho Hlf].
  apply name_eqb_eq in Ho.
  apply Nat.eqb_eq in Hlf. apply Nat.eqb_eq in Hnf. apply Nat.eqb_eq in Hlu.
  destruct (VTrExpr_core_apps_inv Htr) as [h' [args' [Heq_all [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? cir ? us' Hcir Hus' Hlen_us | | | | | | | |]; subst.
  destruct (Forall2_nth_error Htr_args Hmaj) as [maj' [Hmaj' Htr_maj]].
  pose proof (core_to_constructor_sound Hves Hms Hctx (VTrExprS_to_VTrExpr Htr_maj) Htc) as Hmaj1_tr.
  destruct (VTrExpr_core_apps_inv Hmaj1_tr) as [c' [fields' [Heq_maj [Htr_c Htr_fields]]]].
  inversion Htr_c as [| | | ? ? cic ? cus' Hcic Hcus' Hlen_cus | | | | | | | |]; subst.
  set (args'' := replace_nth major_idx (vapps (VConst cn cus') fields') args').
  assert (Hargs_wf : Forall (VExprWF venv (List.length ps) (vl_ctx L)) args')
    by (eapply vapps_args_wf; [exact Hwf | exact HG | exact (VIsDefEqU_refl_l Heq_all)]).
  assert (Hargs_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) args' args'').
  { apply Forall2_VIsDefEqU_replace_nth with (x := maj');
      [exact Hargs_wf | exact Hmaj' | apply VIsDefEqU_symm; exact Heq_maj]. }
  assert (Hh_refl : VIsDefEqU venv (List.length ps) (vl_ctx L) (VConst rname us') (VConst rname us')).
  { destruct (VTrExprS_has_type Htr_h) as [T HT]. exists T. exact HT. }
  destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_all) Hh_refl Hargs_eq)
    as [Hwf_args'' Hcongr].
  assert (Hmaj'' : nth_error args'' major_idx = Some (vapps (VConst cn cus') fields')).
  { apply replace_nth_same. apply nth_error_Some. rewrite Hmaj'. discriminate. }
  destruct (ves_recursor_rhs Hves Hfind Hkind (core_find_rule_In Hrule)) as [rhs_v Hrhs_tr].
  assert (Hwf_us' : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus').
  assert (Hlen_us' : List.length us' = List.length (decl_params d))
    by (rewrite <- (TrLevels_length Hus'); exact Hlu).
  assert (Hlen_f' : List.length fields' = ctor_num_params ci + ctor_num_fields ci)
    by (rewrite <- (Forall2_length Htr_fields); exact Hlf).
  pose proof (ves_recursor_iota Hves HG Hfind Hkind eq_refl Hown Hmaj'' Hrule Hci eq_refl
                Hlen_f' Hnf Hlen_us' Hwf_us' Hrhs_tr Hwf_args'') as Hiota.
  unfold args'' in Hiota.
  rewrite replace_nth_firstn in Hiota by (unfold major_idx; lia).
  rewrite replace_nth_skipn in Hiota by (unfold major_idx; lia).
  assert (Hrhs_inst : VTrExpr env venv ps L (subst_levels (decl_params d) us (rule_rhs rule)) (vinstL us' rhs_v)).
  { apply VTrExpr_closed_to_any; [exact Hwf |].
    eapply VTrExpr_subst_levels; [exact Hlu | exact Hus' | exact Hrhs_tr]. }
  eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | |].
  - eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hrhs_inst | |].
    + apply Forall2_app; [apply Forall2_firstn; apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args |].
      apply Forall2_app; [apply Forall2_skipn; apply Forall2_VTrExprS_to_VTrExpr; exact Htr_fields |].
      change (match args with [] => [] | _ :: l => skipn major_idx l end) with (skipn (S major_idx) args).
      apply Forall2_skipn; apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args.
    + exact (VIsDefEqU_refl_r Hiota).
  - eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hiota |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hcongr | exact Heq_all].
Qed.

(* 3f. Projection reduction (`core_reduce_projection_with` and `core_reduce_proj_core`) *)
Lemma core_reduce_proj_core_sound env venv ps L owner idx val val' pv fty fval :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L val val' ->
  VTrProj env venv (List.length ps) (vl_ctx L) owner idx val' pv fty ->
  core_reduce_proj_core env idx val = Some fval ->
  exists fval',
    VTrExpr env venv ps L fval fval' /\
    VIsDefEqU venv (List.length ps) (vl_ctx L) pv fval'.
Proof.
  intros Hves HwfL Hval Hproj Hred.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_reduce_proj_core in Hred.
  pose proof (core_spine_core_apps val []) as Hsp.
  destruct (core_spine val []) as [head args] eqn:Esp. simpl in Hsp.
  rewrite <- Hsp in Hval.
  destruct head as [| | | |cn cus| | | | | | |]; try discriminate.
  destruct (core_constructor env cn) as [ci|] eqn:Hci; [|discriminate].
  destruct ((idx <? ctor_num_fields ci) &&
            Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci)) eqn:Hchk;
    [|discriminate].
  apply andb_true_iff in Hchk as [Hlt Hla].
  apply Nat.ltb_lt in Hlt. apply Nat.eqb_eq in Hla.
  destruct (VTrExpr_core_apps_inv Hval) as [h' [args' [Heq_val [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? cic ? cus' Hcic Hcus' Hlen_cus | | | | | | | |]; subst.
  destruct (Forall2_nth_error Htr_args Hred) as [fval' [Hfval' Htr_fv]].
  destruct Hproj as [info ctor c d us ps_e idxs Hi Hc Hd Hk Hlt_c Hlp Hli Hw Hlu Hst Hpv Hty].
  subst pv.
  assert (Hla' : List.length args' = ctor_num_params ci + ctor_num_fields ci)
    by (rewrite <- (Forall2_length Htr_args); exact Hla).
  destruct (VIsDefEqU_refl_l Heq_val) as [Tc HTc].
  destruct (ves_ctor_type_head Hves HG Hci Hla' HTc) as [oinfo [oidxs [Hoi [Hocnp [Holi Htc_eq]]]]].
  destruct Heq_val as [Tv Heq_val'].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG HTc (VIsDefEq_refl_l Heq_val')) as [u1 Hc1].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG (VIsDefEq_refl_r Heq_val') Hst) as [u2 Hc2].
  assert (Hty_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
      (vapps (VConst (ctor_induct ci) cus') (firstn (ctor_num_params ci) args' ++ oidxs))
      (vapps (VConst owner us) (ps_e ++ idxs))).
  { eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Htc_eq |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exists (VSort u1); exact Hc1 |
      exists (VSort u2); exact Hc2]. }
  destruct (ves_ind_inj Hves HG Hoi Hi Hty_eq) as [Hown_eq _].
  unfold core_inductive in Hi.
  destruct (find_decl owner env) as [d_ind|] eqn:Hfind_ind; [|discriminate].
  destruct (decl_kind_of d_ind) eqn:Hk_ind; try discriminate.
  inversion Hi; subst i; clear Hi.
  assert (Hi' : core_inductive env owner = Some info)
    by (unfold core_inductive; rewrite Hfind_ind, Hk_ind; reflexivity).
  unfold core_constructor in Hci.
  destruct (find_decl cn env) as [d_cn|] eqn:Hfind_cn; [|discriminate].
  destruct (decl_kind_of d_cn) eqn:Hk_cn; try discriminate.
  inversion Hci; subst c0; clear Hci.
  destruct (ves_ind_shape Hves Hfind_ind Hk_ind Hfind_cn Hk_cn) as [[_ Hto_in] _].
  specialize (Hto_in Hown_eq). rewrite Hc in Hto_in.
  destruct Hto_in as [Hcn_eq | []]. subst cn.
  rewrite Hfind_cn in Hd. inversion Hd; subst d_cn; clear Hd.
  rewrite Hk_cn in Hk. inversion Hk; subst ci; clear Hk.
  destruct (ves_ind_shape Hves Hfind_ind Hk_ind Hfind_cn Hk_cn) as [_ Hsh].
  destruct (Hsh (ltac:(rewrite Hc; left; reflexivity))) as [Hcnp _].
  exists fval'. split; [apply VTrExprS_to_VTrExpr; exact Htr_fv |].
  eapply ves_proj_iota; try eassumption.
  - apply VIsDefEqU_symm. exists Tv. exact Heq_val'.
  - exists fty. exact Hty.
Qed.

Lemma core_reduce_projection_with_sound env venv ps chk rec reduce g L owner idx val e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  (forall g0 L0 a a' a1, VTrCtx env venv ps g0 L0 -> VTrExpr env venv ps L0 a a' ->
     reduce g0 a = Accept a1 -> VTrExpr env venv ps L0 a1 a') ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L (EProj owner idx val) e' ->
  core_reduce_projection_with rec reduce env g owner idx val = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hred_s Hctx Htr Hred.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  destruct (VTrExpr_inv_proj Htr) as [val' [pv [fty [Hval [Hproj Heq_pv]]]]].
  unfold core_reduce_projection_with in Hred.
  destruct (reduce g val) as [r1|err|why] eqn:Hr1; simpl in Hred; try discriminate.
  pose proof (Hred_s g L val val' r1 Hctx Hval Hr1) as Hr1_tr.
  assert (Hr2_ex : exists r2,
    VTrExpr env venv ps L r2 val' /\
    (let '(head, args) := core_spine r2 [] in
     match head with
     | EConst n _ =>
         match core_constructor env n with
         | Some ci =>
             if name_eqb (ctor_induct ci) owner && (idx <? ctor_num_fields ci) &&
                Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci)
             then Accept (nth_error args (ctor_num_params ci + idx))
             else Accept None
         | None => Accept None
         end
     | _ => Accept None
     end) = Accept (Some e1)).
  { destruct r1 as [| | | | | | | | |lit| |]; try (eexists; split; [exact Hr1_tr | exact Hred]).
    destruct lit as [n|s]; [exists (ELit (LitNat n)); split; [exact Hr1_tr | exact Hred] |].
    destruct (core_expand_string s) as [exp|err|why] eqn:Hexp; simpl in Hred; try discriminate.
    destruct (whnf_method rec g exp) as [r2|err|why] eqn:Hw2; simpl in Hred; try discriminate.
    destruct (VTrExpr_inv_strlit Hr1_tr) as [s' [Hstr [Htrs [_ Heq_s]]]].
    assert (Hexp_tr : VTrExpr env venv ps L exp val')
      by (exists s'; split; [eapply VTrExprS_core_expand_string; eassumption | exact Heq_s]).
    exists r2. split; [exact (fms_whnf Hms Hctx Hexp_tr Hw2) | exact Hred]. }
  destruct Hr2_ex as [r2 [Hr2_tr Hstep]].
  assert (Hpc : core_reduce_proj_core env idx r2 = Some e1).
  { unfold core_reduce_proj_core.
    destruct (core_spine r2 []) as [head args].
    destruct head; try discriminate.
    destruct (core_constructor env n) as [ci|]; try discriminate.
    destruct (name_eqb (ctor_induct ci) owner) eqn:Eo; simpl in Hstep; [|discriminate].
    destruct ((idx <? ctor_num_fields ci) &&
              Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci));
      [inversion Hstep; reflexivity | discriminate]. }
  destruct (core_reduce_proj_core_sound Hves HwfL Hr2_tr Hproj Hpc) as [fv' [Hfv_tr Hpv_fv]].
  eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | exact Hfv_tr |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
    apply VIsDefEqU_symm; exact Hpv_fv | exact Heq_pv].
Qed.

Lemma core_reduce_head_sound env venv ps rec fuel g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  core_reduce_head rec fuel env g e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hred.
  unfold core_reduce_head in Hred.
  destruct (core_reduce_nat rec fuel env g e) as [[v|]|err|why] eqn:Hn; simpl in Hred; try discriminate.
  - inversion Hred; subst. eapply core_reduce_nat_sound; eassumption.
  - destruct (core_reduce_quotient rec env g e) as [[v|]|err|why] eqn:Hq; simpl in Hred; try discriminate.
    + inversion Hred; subst. eapply core_reduce_quotient_sound; eassumption.
    + eapply core_reduce_recursor_sound; eassumption.
Qed.

(* ========================================================================= *)
(* 4. WHNF Soundness (`whnf_core_step`, `whnf_round_step`, `whnf_loop`)      *)
(* ========================================================================= *)

Lemma whnf_core_step_sound env venv ps rec fuel cheap g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  whnf_core_step rec fuel env ps cheap g e = Accept e1 ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hw.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold whnf_core_step in Hw.
  destruct e as [i|n|n|u|c us|f a|nm bi A b|nm bi A B|nm A val body nd|lit|owner idx val|body].
  - (* EBVar *)
    destruct (nth_error (bound_context g) i) as [b|] eqn:Hnth; [|discriminate].
    destruct (binding_value b) as [v|] eqn:Hv.
    + destruct (VTrCtx_lookup_bound Hcl Hctx Hnth) as [eb' [tyb' [Hlk [_ [_ Hval_tr]]]]].
      destruct Htr as [e0 [Htr0 Heq0]].
      inversion Htr0 as [? ? ? ty0 Hlk0 _ | | | | | | | | | | |]; subst.
      rewrite Hlk in Hlk0. inversion Hlk0; subst e0 ty0.
      pose proof (VTrExpr_defeq_r Hves HwfL (Hval_tr v Hv) Heq0) as Hv_tr.
      exact (fms_whnf_core Hms Hctx Hv_tr Hw).
    + inversion Hw; subst. exact Htr.
  - (* EFVar *)
    destruct (find_free n (free_context g)) as [b|] eqn:Hfind; [|discriminate].
    destruct (binding_value b) as [v|] eqn:Hv.
    + destruct (VTrCtx_lookup_free Hcl Hctx Hfind) as [ef' [tyf' [Hlk [_ [_ Hval_tr]]]]].
      destruct Htr as [e0 [Htr0 Heq0]].
      inversion Htr0 as [| ? ? ? ty0 Hlk0 _ | | | | | | | | | |]; subst.
      rewrite Hlk in Hlk0. inversion Hlk0; subst e0 ty0.
      pose proof (VTrExpr_defeq_r Hves HwfL (Hval_tr v Hv) Heq0) as Hv_tr.
      exact (fms_whnf_core Hms Hctx Hv_tr Hw).
    + inversion Hw; subst. exact Htr.
  - (* EMVar *)
    discriminate.
  - (* ESort *)
    destruct (check_level ps u) as [[]|err|why]; simpl in Hw; try discriminate.
    inversion Hw; subst. exact Htr.
  - (* EConst *)
    destruct (get_constant env ps c us) as [d|err|why]; simpl in Hw; try discriminate.
    inversion Hw; subst. exact Htr.
  - (* EApp *)
    pose proof (core_spine_core_apps (EApp f a) []) as Hsp.
    destruct (core_spine (EApp f a) []) as [head args] eqn:Esp. simpl in Hsp.
    rewrite <- Hsp in Htr.
    destruct (whnf_core_method rec cheap g head) as [fn|err|why] eqn:Hwfn; simpl in Hw; try discriminate.
    destruct (VTrExpr_core_apps_inv Htr) as [h' [args' [Heq_all [Htr_h Htr_args]]]].
    pose proof (fms_whnf_core Hms Hctx (VTrExprS_to_VTrExpr Htr_h) Hwfn) as Hfn_tr.
    assert (Hreb_tr : VTrExpr env venv ps L (core_apps fn args) e').
    { eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | | exact Heq_all].
      eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hfn_tr |
        apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args | exact (VIsDefEqU_refl_l Heq_all)]. }
    destruct fn;
      try (destruct (core_reduce_quotient rec env g (core_apps _ args)) as [[qv|]|err|why] eqn:Hq;
           simpl in Hw; try discriminate;
           [exact (fms_whnf_core Hms Hctx (core_reduce_quotient_sound Hves Hms Hctx Hreb_tr Hq) Hw)
           | destruct (core_reduce_recursor rec fuel env g (core_apps _ args)) as [[rv|]|err|why] eqn:Hr;
             simpl in Hw; try discriminate;
             [exact (fms_whnf_core Hms Hctx (core_reduce_recursor_sound Hves Hms Hctx Hreb_tr Hr) Hw)
             | inversion Hw; subst; exact Hreb_tr]]).
    (* ELam: beta *)
    exact (fms_whnf_core Hms Hctx (core_beta_sound Hves HwfL Hreb_tr) Hw).
  - (* ELam *)
    inversion Hw; subst. exact Htr.
  - (* EPi *)
    inversion Hw; subst. exact Htr.
  - (* ELet *)
    destruct (VTrExpr_inv_let Htr) as [ty' [val' [body' [Hvt [_ [Hval_tr [Hbody_tr Heq_b]]]]]]].
    assert (Hinst : VTrExpr env venv ps L (instantiate body val) e').
    { eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | | exact Heq_b].
      eapply VTrExpr_instantiate_let; [exact Hves | exact HwfL | exact Hvt | exact Hval_tr | exact Hbody_tr]. }
    exact (fms_whnf_core Hms Hctx Hinst Hw).
  - (* ELit *)
    destruct lit as [n|s]; [inversion Hw; subst; exact Htr |].
    destruct (core_expand_string s) as [exp|err|why]; simpl in Hw; try discriminate.
    inversion Hw; subst. exact Htr.
  - (* EProj *)
    destruct (core_reduce_projection_with rec
        (if cheap then whnf_core_method rec true else whnf_method rec)
        env g owner idx val) as [[pv1|]|err|why] eqn:Hp; simpl in Hw; try discriminate.
    + assert (Hpv1 : VTrExpr env venv ps L pv1 e').
      { eapply core_reduce_projection_with_sound; [exact Hves | exact Hms | | exact Hctx | exact Htr | exact Hp].
        intros g0 L0 a0 a0' a1 Hc0 Ha0 Hr0.
        destruct cheap; [exact (fms_whnf_core Hms Hc0 Ha0 Hr0) | exact (fms_whnf Hms Hc0 Ha0 Hr0)]. }
      exact (fms_whnf_core Hms Hctx Hpv1 Hw).
    + inversion Hw; subst. exact Htr.
  - (* EMData *)
    exact (fms_whnf_core Hms Hctx (VTrExpr_inv_mdata Htr) Hw).
Qed.

Lemma finish_whnf_unfold_sound env venv ps L e e' r :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L e e' ->
  finish_whnf_unfold env ps e = Accept r ->
  VTrExpr env venv ps L (match r with WhnfDone v | WhnfContinue v => v end) e'.
Proof.
  intros Hves HwfL Htr Hf.
  unfold finish_whnf_unfold in Hf.
  destruct (core_unfold env ps e) as [[v|]|err|why] eqn:Hu; simpl in Hf; try discriminate;
    inversion Hf; subst r; simpl.
  - eapply core_unfold_sound; eassumption.
  - exact Htr.
Qed.

Lemma whnf_round_step_sound env venv ps rec fuel g L e e' r :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  whnf_round_step rec fuel env ps g e = Accept r ->
  VTrExpr env venv ps L (match r with WhnfDone v | WhnfContinue v => v end) e'.
Proof.
  intros Hves Hms Hctx Htr Hw.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  unfold whnf_round_step in Hw.
  destruct (whnf_core_step rec fuel env ps false g e) as [red|err|why] eqn:Hwc;
    simpl in Hw; try discriminate.
  pose proof (whnf_core_step_sound Hves Hms Hctx Htr Hwc) as Hred.
  assert (Hnonconst : forall red0,
    VTrExpr env venv ps L red0 e' ->
    (nat_hook <- core_reduce_native red0;;
     match nat_hook with
     | Some value => Accept (WhnfDone value)
     | None =>
         native <- core_reduce_nat rec fuel env g red0;;
         match native with
         | Some value => Accept (WhnfDone value)
         | None => finish_whnf_unfold env ps red0
         end
     end) = Accept r ->
    VTrExpr env venv ps L (match r with WhnfDone v | WhnfContinue v => v end) e').
  { intros red0 Hred0 Hw0.
    destruct (core_reduce_native red0) as [[nv|]|err|why] eqn:Hnh; simpl in Hw0; try discriminate.
    - exfalso. eapply core_reduce_native_sound; exact Hnh.
    - destruct (core_reduce_nat rec fuel env g red0) as [[nv|]|err|why] eqn:Hnat;
        simpl in Hw0; try discriminate.
      + inversion Hw0; subst r; simpl. eapply core_reduce_nat_sound; eassumption.
      + eapply finish_whnf_unfold_sound; eassumption. }
  destruct red as [| | | |n us| | | | | | |]; try (exact (Hnonconst _ Hred Hw)).
  (* EConst n us *)
  destruct (name_eqb n core_zero_name && core_nat_ready env) eqn:Ez.
  - apply andb_true_iff in Ez as [En Hnat].
    apply name_eqb_eq in En. subst n.
    inversion Hw; subst r; simpl.
    destruct (VTrExpr_inv_const Hred) as [ci [us' [Hci [Hus' [_ [Hlen Heq]]]]]].
    destruct (hp_nat (ves_prims Hves) Hnat) as [_ [Hz _]].
    pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
      (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hz)) as Hz'.
    simpl in Hz'.
    destruct (VHasType_const_inv Hwf (VLCtxWF_to_VCtxWF HwfL) Hz') as [ci0 [Hci0 [_ Hlen0]]].
    rewrite Hci in Hci0. inversion Hci0; subst ci0.
    destruct us; simpl in Hlen, Hlen0; try lia.
    inversion Hus'; subst us'.
    exists (natLit 0%N). split.
    + eapply VTrExprS_natlit; [exact Hnat |].
      eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat].
    + rewrite natLit_0. exact Heq.
  - eapply finish_whnf_unfold_sound; eassumption.
Qed.

Lemma whnf_loop_sound rounds env venv ps rec fuel g L :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  forall e e' e1,
    VTrExpr env venv ps L e e' ->
    whnf_loop rounds rec fuel env ps g e = Accept e1 ->
    VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx. unfold whnf_loop.
  induction rounds as [|rounds IH]; intros e e' e1 Htr Hw; simpl in Hw; [discriminate |].
  destruct (whnf_round_step rec fuel env ps g e) as [[v|v]|err|why] eqn:Hr;
    simpl in Hw; try discriminate.
  - inversion Hw; subst e1.
    exact (whnf_round_step_sound Hves Hms Hctx Htr Hr).
  - eapply IH; [exact (whnf_round_step_sound Hves Hms Hctx Htr Hr) | exact Hw].
Qed.

Lemma whnf_step_sound env venv ps rec fuel g L e e' e1 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  whnf_step rec fuel env ps g e = Accept e1 ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hms Hctx Htr Hw.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  unfold whnf_step in Hw.
  destruct (whnf_core_step rec fuel env ps false g e) as [red|err|why] eqn:Hwc;
    simpl in Hw; try discriminate.
  pose proof (whnf_core_step_sound Hves Hms Hctx Htr Hwc) as Hred.
  assert (Hnonconst : forall red0,
    VTrExpr env venv ps L red0 e' ->
    (nat_hook <- core_reduce_native red0;;
     match nat_hook with
     | Some value => Accept value
     | None =>
         native <- core_reduce_nat rec fuel env g red0;;
         match native with
         | Some value => Accept value
         | None =>
             unfolded <- core_unfold env ps red0;;
             match unfolded with
             | Some next => whnf_method rec g next
             | None => Accept red0
             end
         end
     end) = Accept e1 ->
    VTrExpr env venv ps L e1 e').
  { intros red0 Hred0 Hw0.
    destruct (core_reduce_native red0) as [[nv|]|err|why] eqn:Hnh; simpl in Hw0; try discriminate.
    - exfalso. eapply core_reduce_native_sound; exact Hnh.
    - destruct (core_reduce_nat rec fuel env g red0) as [[nv|]|err|why] eqn:Hnat;
        simpl in Hw0; try discriminate.
      + inversion Hw0; subst e1. eapply core_reduce_nat_sound; eassumption.
      + destruct (core_unfold env ps red0) as [[uv|]|err|why] eqn:Hu; simpl in Hw0; try discriminate.
        * exact (fms_whnf Hms Hctx (core_unfold_sound Hves HwfL Hred0 Hu) Hw0).
        * inversion Hw0; subst e1. exact Hred0. }
  destruct red as [| | | |n us| | | | | | |]; try (exact (Hnonconst _ Hred Hw)).
  destruct (name_eqb n core_zero_name && core_nat_ready env) eqn:Ez.
  - apply andb_true_iff in Ez as [En Hnat]. apply name_eqb_eq in En. subst n.
    inversion Hw; subst e1.
    destruct (VTrExpr_inv_const Hred) as [ci [us' [Hci [Hus' [_ [Hlen Heq]]]]]].
    destruct (hp_nat (ves_prims Hves) Hnat) as [_ [Hz _]].
    pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
      (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hz)) as Hz'.
    simpl in Hz'.
    destruct (VHasType_const_inv Hwf (VLCtxWF_to_VCtxWF HwfL) Hz') as [ci0 [Hci0 [_ Hlen0]]].
    rewrite Hci in Hci0. inversion Hci0; subst ci0.
    destruct us; simpl in Hlen, Hlen0; try lia. inversion Hus'; subst us'.
    exists (natLit 0%N). split.
    + eapply VTrExprS_natlit; [exact Hnat |].
      eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat].
    + rewrite natLit_0. exact Heq.
  - destruct (core_unfold env ps (EConst n us)) as [[uv|]|err|why] eqn:Hu;
      simpl in Hw; try discriminate.
    + exact (fms_whnf Hms Hctx (core_unfold_sound Hves HwfL Hred Hu) Hw).
    + inversion Hw; subst e1. exact Hred.
Qed.

(* ========================================================================= *)
(* 5. Type Inference Soundness — ALL 13 Constructors, Both Modes             *)
(* ========================================================================= *)

Lemma sort_of_sound_typed env venv ps chk rec g L e e' u :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  sort_of rec g e = Accept u ->
  exists u',
    vlevel_of_level ps u = Some u' /\
    vlevel_wf (List.length ps) u' /\
    VHasType venv (List.length ps) (vl_ctx L) e' (VSort u').
Proof.
  intros Hves Hms Hctx He Hso.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VCtxWF Hctx) as HG.
  unfold sort_of in Hso.
  destruct (infer_method rec g e) as [t0|err|why] eqn:Hinf; simpl in Hso; try discriminate.
  destruct (whnf_method rec g t0) as [t1|err|why] eqn:Hw; simpl in Hso; try discriminate.
  destruct t1 as [| | |u0| | | | | | | |]; try discriminate.
  inversion Hso; subst u0; clear Hso.
  destruct (fms_infer_typed Hms Hctx He Hinf) as [ty' [Ht0_tr He_ty]].
  pose proof (fms_whnf Hms Hctx Ht0_tr Hw) as Ht1_tr.
  destruct (VTrExpr_inv_sort Ht1_tr) as [u' [Hu' [Huwf Hueq]]].
  exists u'. repeat split; [exact Hu' | exact Huwf |].
  eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact He_ty |
    apply VIsDefEqU_symm; exact Hueq].
Qed.

Lemma sort_of_sound_checking env venv ps rec g L e u :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  sort_of rec g e = Accept u ->
  exists e' u',
    vlevel_of_level ps u = Some u' /\
    vlevel_wf (List.length ps) u' /\
    VTrExpr env venv ps L e e' /\
    VHasType venv (List.length ps) (vl_ctx L) e' (VSort u').
Proof.
  intros Hves Hms Hctx Hso.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VCtxWF Hctx) as HG.
  unfold sort_of in Hso.
  destruct (infer_method rec g e) as [t0|err|why] eqn:Hinf; simpl in Hso; try discriminate.
  destruct (whnf_method rec g t0) as [t1|err|why] eqn:Hw; simpl in Hso; try discriminate.
  destruct t1 as [| | |u0| | | | | | | |]; try discriminate.
  inversion Hso; subst u0; clear Hso.
  destruct (fms_infer Hms Hctx eq_refl Hinf) as [e' [ty' [He_tr [Ht0_tr He_ty]]]].
  pose proof (fms_whnf Hms Hctx Ht0_tr Hw) as Ht1_tr.
  destruct (VTrExpr_inv_sort Ht1_tr) as [u' [Hu' [Huwf Hueq]]].
  exists e', u'. repeat split; [exact Hu' | exact Huwf | exact He_tr |].
  eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact He_ty |
    apply VIsDefEqU_symm; exact Hueq].
Qed.

Lemma core_apply_type_sound env venv ps chk rec g L :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  forall args args' h ty ty' res,
    Forall2 (VTrExpr env venv ps L) args args' ->
    VTrExpr env venv ps L ty ty' ->
    VHasType venv (List.length ps) (vl_ctx L) h ty' ->
    VExprWF venv (List.length ps) (vl_ctx L) (vapps h args') ->
    core_apply_type rec g ty args = Accept res ->
    exists res',
      VTrExpr env venv ps L res res' /\
      VHasType venv (List.length ps) (vl_ctx L) (vapps h args') res'.
Proof.
  intros Hves Hms Hctx.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  induction args as [|a rest IH]; intros args' h ty ty' res Hargs Hty Hh Hwf_app Hcat;
    inversion Hargs as [| ? a' ? r' Ha Hr]; subst; simpl in *.
  - inversion Hcat; subst res. exists ty'. auto.
  - destruct (whnf_method rec g ty) as [tyw|err|why] eqn:Hw; simpl in Hcat; try discriminate.
    destruct tyw as [| | | | | | |nm bi dom body| | | |]; try discriminate.
    pose proof (fms_whnf Hms Hctx Hty Hw) as Htyw.
    destruct (VTrExpr_inv_pi Htyw) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Hpi_eq]]]]]].
    assert (Hh_pi : VHasType venv (List.length ps) (vl_ctx L) h (VForallE dom' body'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hh |
            apply VIsDefEqU_symm; exact Hpi_eq]).
    assert (Hha_wf : VExprWF venv (List.length ps) (vl_ctx L) (VApp h a')).
    { change (VApp h a') with (vapps (VApp h a') []).
      eapply vapps_wf_prefix with (ys := r'); [exact Hwf | exact HG | exact Hwf_app]. }
    destruct Hha_wf as [Tha HTha].
    destruct (VHasType_app_inv Hwf HG HTha) as [A1 [B1 [Hh1 Ha1]]].
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG (VIsDefEq_uniqU Hwf Hinj HG Hh1 Hh_pi))
      as [[uA HA_eq] _].
    assert (Ha_dom : VHasType venv (List.length ps) (vl_ctx L) a' dom')
      by (eapply VDF_defeqDF; [exact HA_eq | exact Ha1]).
    assert (Hha_ty : VHasType venv (List.length ps) (vl_ctx L) (VApp h a') (vinst0 body' a'))
      by (eapply VHasType_app; [exact Hh_pi | exact Ha_dom]).
    assert (Hinst_tr : VTrExpr env venv ps L (instantiate body a) (vinst0 body' a'))
      by (eapply VTrExpr_instantiate_lam; [exact Hves | exact HwfL | exact Ha_dom | exact Ha | exact Hbody_tr]).
    eapply IH; [exact Hr | exact Hinst_tr | exact Hha_ty | exact Hwf_app | exact Hcat].
Qed.

Lemma core_projection_field_sound env venv ps chk rec fuel g L
    owner info ctor c d ci_c us' params' indices' sv u_sort ty_p maybe_prop val :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  core_inductive env owner = Some info ->
  ind_ctors info = [ctor] ->
  find_decl ctor env = Some d ->
  decl_kind_of d = DConstructor c ->
  venv_constants venv ctor = Some ci_c ->
  List.length params' = ind_num_params info ->
  List.length indices' = ind_num_indices info ->
  Forall (vlevel_wf (List.length ps)) us' ->
  List.length us' = List.length (decl_params d) ->
  VTrExpr env venv ps L val sv ->
  VHasType venv (List.length ps) (vl_ctx L) sv (vapps (VConst owner us') (params' ++ indices')) ->
  VHasType venv (List.length ps) (vl_ctx L) (vapps (VConst owner us') (params' ++ indices')) (VSort u_sort) ->
  (maybe_prop = false -> ~ vlevel_equiv u_sort VLZero) ->
  VHasType venv (List.length ps) (vl_ctx L) (vapps (VConst ctor us') params') ty_p ->
  forall skip index ty ty' res,
    skip + index < ctor_num_fields c ->
    VTrExpr env venv ps L ty ty' ->
    (forall k fty,
       VProjTelescope env venv (List.length ps) (vl_ctx L) owner us' params' sv maybe_prop k index ty' fty ->
       VProjTelescope env venv (List.length ps) (vl_ctx L) owner us' params' sv maybe_prop (k + index) 0 ty_p fty) ->
    core_projection_field rec fuel g owner val maybe_prop skip index ty = Accept res ->
    exists fty,
      VTrExpr env venv ps L res fty /\
      VHasType venv (List.length ps) (vl_ctx L) (vproj_expr owner (skip + index) us' params' sv) fty.
Proof.
  intros Hves Hms Hctx Hi Hctors Hd Hk Hcic Hlp Hli Hwus Hlu Hval_tr Hsv_ty Hown_sort Hmp Hctor_typ.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  induction skip as [|skip IH]; intros index ty ty' res Hlt Hty_tr Hcont Hpf; simpl in Hpf.
  - (* skip = 0 *)
    destruct (whnf_method rec g ty) as [red|err|why] eqn:Hw; simpl in Hpf; try discriminate.
    destruct red as [| | | | | | |nm bi dom body| | | |]; try discriminate.
    pose proof (fms_whnf Hms Hctx Hty_tr Hw) as Hred_tr.
    destruct (VTrExpr_inv_pi Hred_tr) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Hpi_eq]]]]]].
    assert (Hprop_ok : maybe_prop = true -> VHasType venv (List.length ps) (vl_ctx L) dom' (VSort VLZero)).
    { intros Hmp_t. subst maybe_prop.
      destruct (sort_of rec g dom) as [du|err|why] eqn:Hdu; simpl in Hpf; try discriminate.
      destruct (level_equiv fuel du LZero) as [ok|err|why] eqn:Hok; simpl in Hpf; try discriminate.
      destruct ok; simpl in Hpf; [|discriminate].
      destruct (sort_of_sound_typed Hves Hms Hctx Hdom_tr Hdu) as [du' [Hdu' [Hdu_wf Hdom_du]]].
      eapply VDF_defeqDF;
        [eapply VDF_sortDF; [exact Hdu_wf | exact I |
           eapply level_equiv_sound_vlevel with (v := LZero); [exact Hdu' | reflexivity | exact Hok]]
        | exact Hdom_du]. }
    assert (Hres_eq : res = dom).
    { destruct maybe_prop; [| inversion Hpf; reflexivity].
      destruct (sort_of rec g dom); simpl in Hpf; try discriminate.
      destruct (level_equiv fuel l LZero) as [ok| |]; simpl in Hpf; try discriminate.
      destruct ok; simpl in Hpf; [inversion Hpf; reflexivity | discriminate]. }
    subst res.
    pose proof (@VPT_zero env venv (List.length ps) (vl_ctx L) owner us' params' sv maybe_prop
                  index ty' dom' body' (VIsDefEqU_symm Hpi_eq) Hprop_ok) as Hpt0.
    specialize (Hcont 0 dom' Hpt0). simpl in Hcont.
    exists dom'. split; [exact Hdom_tr |].
    eapply ves_proj_telescope; try eassumption.
  - (* skip = S skip *)
    destruct (whnf_method rec g ty) as [red|err|why] eqn:Hw; simpl in Hpf; try discriminate.
    destruct red as [| | | | | | |nm bi dom body| | | |]; try discriminate.
    pose proof (fms_whnf Hms Hctx Hty_tr Hw) as Hred_tr.
    destruct (VTrExpr_inv_pi Hred_tr) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Hpi_eq]]]]]].
    destruct (core_occurs 0 body) eqn:Hocc.
    + (* Dependent field: core_occurs 0 body = true *)
      rewrite andb_true_r in Hpf.
      assert (Hprop_ok : maybe_prop = true -> VHasType venv (List.length ps) (vl_ctx L) dom' (VSort VLZero)).
      { intros Hmp_t. subst maybe_prop.
        destruct (sort_of rec g dom) as [du|err|why] eqn:Hdu; simpl in Hpf; try discriminate.
        destruct (level_equiv fuel du LZero) as [ok|err|why] eqn:Hok; simpl in Hpf; try discriminate.
        destruct ok; simpl in Hpf; [|discriminate].
        destruct (sort_of_sound_typed Hves Hms Hctx Hdom_tr Hdu) as [du' [Hdu' [Hdu_wf Hdom_du]]].
        eapply VDF_defeqDF;
          [eapply VDF_sortDF; [exact Hdu_wf | exact I |
             eapply level_equiv_sound_vlevel with (v := LZero); [exact Hdu' | reflexivity | exact Hok]]
          | exact Hdom_du]. }
      assert (Hpf_next : core_projection_field rec fuel g owner val maybe_prop skip (S index)
                            (instantiate body (EProj owner index val)) = Accept res).
      { destruct maybe_prop; [| exact Hpf].
        destruct (sort_of rec g dom); simpl in Hpf; try discriminate.
        destruct (level_equiv fuel l LZero) as [ok| |]; simpl in Hpf; try discriminate.
        destruct ok; simpl in Hpf; [exact Hpf | discriminate]. }
      (* Project at current index first via Hcont 0 *)
      pose proof (@VPT_zero env venv (List.length ps) (vl_ctx L) owner us' params' sv maybe_prop
                    index ty' dom' body' (VIsDefEqU_symm Hpi_eq) Hprop_ok) as Hpt0.
      pose proof (Hcont 0 dom' Hpt0) as Hpt_idx. simpl in Hpt_idx.
      assert (Hidx_lt : index < ctor_num_fields c) by lia.
      pose proof (ves_proj_telescope Hves HG Hi Hctors Hd Hk Hcic Hidx_lt Hlp Hli Hwus Hlu
                    Hsv_ty Hown_sort Hmp Hctor_typ Hpt_idx) as Hproj_idx_ty.
      (* Construct VTrExpr for EProj owner index val *)
      assert (Hproj_idx_tr : VTrExpr env venv ps L (EProj owner index val)
                               (vproj_expr owner index us' params' sv)).
      { destruct Hval_tr as [v0 [Hv0 [Tv Hveq]]].
        assert (Hsv0 : VHasType venv (List.length ps) (vl_ctx L) v0
                         (vapps (VConst owner us') (params' ++ indices')))
          by (eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hsv_ty |
                apply VIsDefEqU_symm; exists Tv; exact Hveq]).
        assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
            (vproj_expr owner index us' params' v0) (vproj_expr owner index us' params' sv)).
        { unfold vproj_expr in *.
          destruct (VHasType_app_inv Hwf HG Hproj_idx_ty) as [Ap [Bp [Hpf_a Hpe_a]]].
          destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe_a (VIsDefEq_refl_r Hveq)) as [up Hcp].
          exists (vinst0 Bp v0).
          eapply VDF_appDF; [exact Hpf_a | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Hveq]]. }
        destruct Hpv_eq as [Tpv Hpv_eq'].
        exists (vproj_expr owner index us' params' v0). split.
        - eapply VTrExprS_proj; [exact Hv0 |].
          eapply VTrProj_intro; try eassumption; [reflexivity | exact (VIsDefEq_refl_l Hpv_eq')].
        - exists Tpv. exact Hpv_eq'. }
      assert (Hinst_tr : VTrExpr env venv ps L (instantiate body (EProj owner index val))
                           (vinst0 body' (vproj_expr owner index us' params' sv)))
        by (eapply VTrExpr_instantiate_lam;
              [exact Hves | exact HwfL | exact Hproj_idx_ty | exact Hproj_idx_tr | exact Hbody_tr]).
      replace (S skip + index) with (skip + S index) by lia.
      eapply IH with (ty' := vinst0 body' (vproj_expr owner index us' params' sv));
        [lia | exact Hinst_tr | | exact Hpf_next].
      intros k fty Hrest.
      replace (k + S index) with (S k + index) by lia.
      apply Hcont.
      eapply VPT_succ; [apply VIsDefEqU_symm; exact Hpi_eq | intros Hm _; exact (Hprop_ok Hm) | exact Hrest].
    + (* Non-dependent field: core_occurs 0 body = false *)
      rewrite andb_false_r in Hpf. simpl in Hpf.
      assert (HwfL' : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
        by (apply VLCtxWF_push_lam; assumption).
      destruct (VTrExpr_no_occurs_instantiate (EProj owner index val) Hves HwfL' Hocc Hbody_tr)
        as [b0 [Hlift_b0 Hb0_tr]].
      assert (Hpi_eq2 : VIsDefEqU venv (List.length ps) (vl_ctx L) ty' (VForallE dom' (vlift b0))).
      { destruct Hdom_is as [u Hu].
        destruct Hbody_is as [v Hv].
        destruct Hlift_b0 as [Tb Hlb].
        assert (HG' : VCtxWF venv (List.length ps) (dom' :: vl_ctx L))
          by (split; [exact HG | exists u; exact Hu]).
        destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hv (VIsDefEq_refl_r Hlb)) as [vb Hcb].
        assert (Hlb' : VIsDefEq venv (List.length ps) (dom' :: vl_ctx L) (vlift b0) body' (VSort v))
          by (eapply VDF_defeqDF; [exact (VDF_symm Hcb) | exact Hlb]).
        eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
          apply VIsDefEqU_symm; exact Hpi_eq |].
        exists (VSort (VLIMax u v)). eapply VDF_forallEDF; [exact Hu | exact (VDF_symm Hlb')]. }
      replace (S skip + index) with (skip + S index) by lia.
      eapply IH with (ty' := b0); [lia | exact Hb0_tr | | exact Hpf].
      intros k fty Hrest.
      replace (k + S index) with (S k + index) by lia.
      apply Hcont.
      eapply VPT_succ with (dom := dom') (body := vlift b0);
        [exact Hpi_eq2 | intros _ Hne; exfalso; exact (Hne b0 eq_refl) |].
      rewrite vinst0_vlift. exact Hrest.
Qed.

Lemma core_infer_projection_sound env venv ps chk rec fuel g L owner idx val res :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  (chk = true \/ exists v', VTrExpr env venv ps L val v') ->
  core_infer_projection rec fuel env g owner idx val = Accept res ->
  exists e' ty',
    VTrTyping env venv ps L (EProj owner idx val) res e' ty' /\
    (forall v', VTrExpr env venv ps L val v' ->
       exists pv, VIsDefEqU venv (List.length ps) (vl_ctx L) pv e' /\
                  VTrProj env venv (List.length ps) (vl_ctx L) owner idx v' pv ty').
Proof.
  intros Hves Hms Hctx Hmode Hip.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_infer_projection in Hip.
  destruct (infer_method rec g val) as [st0|err|why] eqn:Hinf; simpl in Hip; try discriminate.
  destruct (whnf_method rec g st0) as [st|err|why] eqn:Hwst; simpl in Hip; try discriminate.
  pose proof (core_spine_core_apps st []) as Hsp.
  destruct (core_spine st []) as [head args] eqn:Esp. simpl in Hsp.
  destruct head as [| | | |n us| | | | | | |]; try discriminate.
  destruct (core_inductive env owner) as [info|] eqn:Hi; [|discriminate].
  unfold require in Hip.
  destruct (name_eqb n owner &&
            Nat.eqb (List.length args) (ind_num_params info + ind_num_indices info)) eqn:Hreq;
    simpl in Hip; [|discriminate].
  apply andb_true_iff in Hreq as [En Hlen_a].
  apply name_eqb_eq in En. subst n. apply Nat.eqb_eq in Hlen_a.
  destruct (ind_ctors info) as [|ctor [|? ?]] eqn:Hctors; try discriminate.
  destruct (find_decl ctor env) as [d|] eqn:Hd; [|discriminate].
  destruct (decl_kind_of d) eqn:Hk; try discriminate.
  destruct (idx <? ctor_num_fields c) eqn:Hlt; simpl in Hip; [|discriminate].
  apply Nat.ltb_lt in Hlt.
  destruct (core_apply_type rec g (subst_levels (decl_params d) us (decl_type d))
              (firstn (ind_num_params info) args)) as [ty_p_e|err|why] eqn:Hcat;
    simpl in Hip; try discriminate.
  destruct (sort_of rec g st) as [u_s|err|why] eqn:Hso; simpl in Hip; try discriminate.
  (* Get val' and st' from Hmode *)
  assert (Hval_st : exists val' st',
    VTrExpr env venv ps L val val' /\
    VTrExpr env venv ps L st st' /\
    VHasType venv (List.length ps) (vl_ctx L) val' st').
  { destruct Hmode as [Hchk | [v' Hv']].
    - destruct (fms_infer Hms Hctx Hchk Hinf) as [val' [st0' [Hv [Hst0 Hvt]]]].
      exists val', st0'. repeat split; [exact Hv | exact (fms_whnf Hms Hctx Hst0 Hwst) | exact Hvt].
    - destruct (fms_infer_typed Hms Hctx Hv' Hinf) as [st0' [Hst0 Hvt]].
      exists v', st0'. repeat split; [exact Hv' | exact (fms_whnf Hms Hctx Hst0 Hwst) | exact Hvt]. }
  destruct Hval_st as [val' [st' [Hval_tr [Hst_tr Hval_st_ty]]]].
  pose proof Hst_tr as Hst_tr_orig.
  rewrite <- Hsp in Hst_tr.
  destruct (VTrExpr_core_apps_inv Hst_tr) as [h' [args' [Heq_st [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? ci_ind ? us' Hci_ind Hus' Hlen_us | | | | | | | |]; subst.
  assert (Hwf_us' : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus').
  pose proof Hi as Hi_orig.
  unfold core_inductive in Hi.
  destruct (find_decl owner env) as [d_ind|] eqn:Hfind_ind; [|discriminate].
  destruct (decl_kind_of d_ind) eqn:Hk_ind; try discriminate.
  inversion Hi; subst i; clear Hi.
  destruct (ves_ind_shape Hves Hfind_ind Hk_ind Hd Hk) as [_ Hsh].
  destruct (Hsh (ltac:(rewrite Hctors; left; reflexivity))) as [Hcnp Hclen_p].
  pose proof (ves_constants Hves Hfind_ind) as Hdc_ind. rewrite Hk_ind in Hdc_ind.
  destruct Hdc_ind as [ci_i [Hci_i [Huv_i _]]].
  rewrite Hci_ind in Hci_i. inversion Hci_i; subst ci_i; clear Hci_i.
  pose proof (ves_constants Hves Hd) as Hdc_c. rewrite Hk in Hdc_c.
  destruct Hdc_c as [ci_c [Hci_c [Huv_c [Hcty_tr _]]]].
  assert (Hlu_d : List.length us = List.length (decl_params d)) by lia.
  assert (Hlu' : List.length us' = List.length (decl_params d))
    by (rewrite <- (TrLevels_length Hus'); exact Hlu_d).
  set (params' := firstn (ind_num_params info) args').
  set (indices' := skipn (ind_num_params info) args').
  assert (Hsplit : args' = params' ++ indices') by (symmetry; apply firstn_skipn).
  assert (Hla' : List.length args' = ind_num_params info + ind_num_indices info)
    by (rewrite <- (Forall2_length Htr_args); exact Hlen_a).
  assert (Hlp' : List.length params' = ind_num_params info)
    by (unfold params'; rewrite List.length_firstn, Hla'; lia).
  assert (Hli' : List.length indices' = ind_num_indices info)
    by (unfold indices'; rewrite List.length_skipn, Hla'; lia).
  assert (Hval_ind : VHasType venv (List.length ps) (vl_ctx L) val'
                       (vapps (VConst owner us') (params' ++ indices'))).
  { rewrite <- Hsplit.
    eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hval_st_ty |
      apply VIsDefEqU_symm; exact Heq_st]. }
  destruct (sort_of_sound_typed Hves Hms Hctx Hst_tr_orig Hso) as [u_s' [Hus_tr [Hus_wf Hst_sort]]].
  assert (Hown_sort : VHasType venv (List.length ps) (vl_ctx L)
                        (vapps (VConst owner us') (params' ++ indices')) (VSort u_s')).
  { rewrite <- Hsplit.
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hst_sort |
      apply VIsDefEqU_symm; exact Heq_st]. }
  assert (Hmp_ok : negb (core_level_positive u_s) = false -> ~ vlevel_equiv u_s' VLZero).
  { intros Hnb. apply negb_false_iff in Hnb. eapply core_level_positive_sound; eassumption. }
  assert (Hctor_pwf : VExprWF venv (List.length ps) (vl_ctx L) (vapps (VConst ctor us') params'))
    by (eapply ves_ctor_params_wf; [exact Hves | exact HG | exact Hi_orig | exact Hctors |
          exact Hd | exact Hk | exact Hlp' | exact Hli' | exact Hown_sort]).
  assert (Hctor_ty0 : VHasType venv (List.length ps) (vl_ctx L) (VConst ctor us') (vinstL us' (vc_type ci_c)))
    by (eapply VHasType_const; [exact Hci_c | exact Hwf_us' | lia]).
  assert (Hctor_ty_tr : VTrExpr env venv ps L (subst_levels (decl_params d) us (decl_type d))
                          (vinstL us' (vc_type ci_c))).
  { apply VTrExpr_closed_to_any; [exact Hwf |].
    eapply VTrExpr_subst_levels; [exact Hlu_d | exact Hus' | exact Hcty_tr]. }
  assert (Hparams_tr : Forall2 (VTrExpr env venv ps L) (firstn (ind_num_params info) args) params')
    by (apply Forall2_firstn; apply Forall2_VTrExprS_to_VTrExpr; exact Htr_args).
  destruct (core_apply_type_sound Hves Hms Hctx Hparams_tr Hctor_ty_tr Hctor_ty0 Hctor_pwf Hcat)
    as [ty_p [Htyp_tr Hctor_typ]].
  destruct (core_projection_field_sound Hves Hms Hctx Hi_orig Hctors Hd Hk Hci_c Hlp' Hli'
              Hwf_us' Hlu' Hval_tr Hval_ind Hown_sort Hmp_ok Hctor_typ
              (skip := idx) (index := 0) (ltac:(lia)) Htyp_tr
              (fun k fty H => eq_rect_r (fun m => VProjTelescope _ _ _ _ _ _ _ _ _ m _ _ _) H (Nat.add_0_r k))
              Hip)
    as [fty [Hres_tr Hproj_ty]].
  rewrite Nat.add_0_r in Hproj_ty.
  assert (Hproj_val : VTrProj env venv (List.length ps) (vl_ctx L) owner idx val'
                        (vproj_expr owner idx us' params' val') fty)
    by (eapply VTrProj_intro; try eassumption; reflexivity).
  assert (Hproj_tr : VTrExpr env venv ps L (EProj owner idx val)
                       (vproj_expr owner idx us' params' val')).
  { destruct Hval_tr as [v0 [Hv0 [Tv Hveq]]].
    assert (Hsv0 : VHasType venv (List.length ps) (vl_ctx L) v0
                     (vapps (VConst owner us') (params' ++ indices')))
      by (eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hval_ind |
            apply VIsDefEqU_symm; exists Tv; exact Hveq]).
    assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
        (vproj_expr owner idx us' params' v0) (vproj_expr owner idx us' params' val')).
    { unfold vproj_expr in *.
      destruct (VHasType_app_inv Hwf HG Hproj_ty) as [Ap [Bp [Hpf_a Hpe_a]]].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe_a (VIsDefEq_refl_r Hveq)) as [up Hcp].
      exists (vinst0 Bp v0).
      eapply VDF_appDF; [exact Hpf_a | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Hveq]]. }
    destruct Hpv_eq as [Tpv Hpv_eq'].
    exists (vproj_expr owner idx us' params' v0). split.
    - eapply VTrExprS_proj; [exact Hv0 |].
      eapply VTrProj_intro; try eassumption; [reflexivity | exact (VIsDefEq_refl_l Hpv_eq')].
    - exists Tpv. exact Hpv_eq'. }
  exists (vproj_expr owner idx us' params' val'), fty. split.
  - repeat split; [exact Hproj_tr | exact Hres_tr | exact Hproj_ty].
  - intros v' Hv'.
    pose proof (VTrExpr_uniq Hves HwfL Hv' Hval_tr) as Hv_eq.
    assert (Hv'_ind : VHasType venv (List.length ps) (vl_ctx L) v'
                        (vapps (VConst owner us') (params' ++ indices')))
      by (eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hval_ind |
            apply VIsDefEqU_symm; exact Hv_eq]).
    assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
        (vproj_expr owner idx us' params' v') (vproj_expr owner idx us' params' val')).
    { unfold vproj_expr in *.
      destruct (VHasType_app_inv Hwf HG Hproj_ty) as [Ap [Bp [Hpf_a Hpe_a]]].
      destruct Hv_eq as [Tv Hv_eq'].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe_a (VIsDefEq_refl_r Hv_eq')) as [up Hcp].
      exists (vinst0 Bp v').
      eapply VDF_appDF; [exact Hpf_a | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Hv_eq']]. }
    exists (vproj_expr owner idx us' params' v'). split; [exact Hpv_eq |].
    eapply VTrProj_intro; try eassumption; [reflexivity |].
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hproj_ty |
      apply VIsDefEqU_symm; exact Hpv_eq].
Qed.

(* Full 13-constructor soundness of `infer_step ... true` (checking mode) *)
Theorem infer_step_sound_true env venv ps rec fuel e :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  forall g L ty,
    VTrCtx env venv ps g L ->
    infer_step rec fuel env ps true g e = Accept ty ->
    exists e' ty', VTrTyping env venv ps L e ty e' ty'.
Proof.
  intros Hves Hms.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  induction e as [i|n|n|u|c us|f IHf a IHa|nm bi dom IHA body IHb|nm bi dom IHA body IHB
                  |nm tyA IHA val IHv body IHb nd|lit|owner idx val IHa|body IHb];
    intros g L ty Hctx Hinf;
    pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL;
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG;
    simpl in Hinf; try discriminate.
  - (* EBVar *)
    destruct (nth_error (bound_context g) i) as [b|] eqn:Hnth; [|discriminate].
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrCtx_lookup_bound Hcl Hctx Hnth) as [e' [ty' [Hlk [Hty [Htr_ty _]]]]].
    exists e', ty'. repeat split; [apply VTrExprS_to_VTrExpr; eapply VTrExprS_bvar; eassumption | exact Htr_ty | exact Hty].
  - (* EFVar *)
    destruct (find_free n (free_context g)) as [b|] eqn:Hfind; [|discriminate].
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrCtx_lookup_free Hcl Hctx Hfind) as [e' [ty' [Hlk [Hty [Htr_ty _]]]]].
    exists e', ty'. repeat split; [apply VTrExprS_to_VTrExpr; eapply VTrExprS_fvar; eassumption | exact Htr_ty | exact Hty].
  - (* ESort *)
    destruct (check_level ps u) as [[]|err|why] eqn:Hchk; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (check_level_sound_vlevel ps u Hchk) as [u' [Hu' Huwf]].
    exists (VSort u'), (VSort (VLSucc u')). repeat split.
    + apply VTrExprS_to_VTrExpr. constructor. exact Hu'.
    + apply VTrExprS_to_VTrExpr. constructor. unfold TrLevel. simpl. rewrite Hu'. reflexivity.
    + apply VHasType_sort. exact Huwf.
  - (* EConst *)
    destruct (get_constant env ps c us) as [d|err|why] eqn:Hget; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (get_constant_sound Hves HwfL Hget)
      as [ci [us' [_ [_ [Hci [_ [Hlen [Hus' [_ [Hty_tr Hc_ty]]]]]]]]]].
    exists (VConst c us'), (vinstL us' (vc_type ci)). repeat split; [| exact Hty_tr | exact Hc_ty].
    apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci | exact Hus' | exact Hlen].
  - (* EApp *)
    destruct (infer_step rec fuel env ps true g f) as [ft0|err|why] eqn:Hft0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g ft0) as [ft|err|why] eqn:Hwft; simpl in Hinf; try discriminate.
    destruct ft as [| | | | | | |nm bi dom body| | | |]; try discriminate.
    destruct (infer_step rec fuel env ps true g a) as [aty|err|why] eqn:Haty; simpl in Hinf; try discriminate.
    destruct (application_type_defeq rec g a dom aty) as [ok|err|why] eqn:Hok; simpl in Hinf; try discriminate.
    destruct ok; simpl in Hinf; [|discriminate].
    inversion Hinf; subst ty; clear Hinf.
    destruct (IHf g L ft0 Hctx Hft0) as [f' [ft' [Hf_tr [Hft0_tr Hf_ty]]]].
    pose proof (fms_whnf Hms Hctx Hft0_tr Hwft) as Hft_tr.
    destruct (VTrExpr_inv_pi Hft_tr) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Hpi_eq]]]]]].
    assert (Hf_pi : VHasType venv (List.length ps) (vl_ctx L) f' (VForallE dom' body'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hf_ty |
            apply VIsDefEqU_symm; exact Hpi_eq]).
    destruct (IHa g L aty Hctx Haty) as [a' [aty' [Ha_tr [Haty_tr Ha_ty]]]].
    pose proof (application_type_defeq_full_sound Hms Hctx Hdom_tr Haty_tr Hok) as Hdom_aty.
    assert (Ha_dom : VHasType venv (List.length ps) (vl_ctx L) a' dom')
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Ha_ty |
            apply VIsDefEqU_symm; exact Hdom_aty]).
    assert (Hfa_ty : VHasType venv (List.length ps) (vl_ctx L) (VApp f' a') (vinst0 body' a'))
      by (eapply VHasType_app; [exact Hf_pi | exact Ha_dom]).
    exists (VApp f' a'), (vinst0 body' a'). repeat split; [| | exact Hfa_ty].
    + change (EApp f a) with (core_apps f [a]).
      change (VApp f' a') with (vapps f' [a']).
      eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hf_tr |
        constructor; [exact Ha_tr | constructor] | exists (vinst0 body' a'); exact Hfa_ty].
    + eapply VTrExpr_instantiate_lam; [exact Hves | exact HwfL | exact Ha_dom | exact Ha_tr | exact Hbody_tr].
  - (* ELam *)
    destruct (infer_step rec fuel env ps true g dom) as [dt0|err|why] eqn:Hdt0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g dt0) as [dt|err|why] eqn:Hwdt; simpl in Hinf; try discriminate.
    destruct dt as [| | |u0| | | | | | | |]; try discriminate.
    destruct (infer_step rec fuel env ps true (push_binding g dom None) body) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (IHA g L dt0 Hctx Hdt0) as [dom' [dt' [Hdom_tr [Hdt0_tr Hdom_dt]]]].
    pose proof (fms_whnf Hms Hctx Hdt0_tr Hwdt) as Hdt_tr.
    destruct (VTrExpr_inv_sort Hdt_tr) as [u' [_ [_ Hu_eq]]].
    assert (Hdom_u : VHasType venv (List.length ps) (vl_ctx L) dom' (VSort u'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hdom_dt |
            apply VIsDefEqU_symm; exact Hu_eq]).
    assert (Hctx' : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exists u'; exact Hdom_u]).
    destruct (IHb _ _ bt Hctx' Hbt) as [body' [bt' [Hbody_tr [Hbt_tr Hbody_bt]]]].
    assert (HG' : VCtxWF venv (List.length ps) (dom' :: vl_ctx L))
      by (split; [exact HG | exists u'; exact Hdom_u]).
    destruct (VIsDefEq_isType Hwf HG' Hbody_bt) as [v Hv].
    destruct Hdom_tr as [dom0 [Hdom0 [Td Hdom_eq]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hdom_u (VIsDefEq_refl_r Hdom_eq)) as [ud Hcd].
    assert (Hdom_eq' : VIsDefEq venv (List.length ps) (vl_ctx L) dom0 dom' (VSort u'))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcd) | exact Hdom_eq]).
    assert (HwfL0 : VLCtxWF venv (List.length ps) (vl_push_lam L dom0))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u'; exact (VIsDefEq_refl_l Hdom_eq')]).
    assert (HwfL' : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u'; exact Hdom_u]).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L dom') (vl_push_lam L dom0)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm Hdom_eq')]. }
    pose proof (VTrExpr_defeq_ctx Hves HwfL' HwfL0 Hceq Hbody_tr) as [b0 [Hb0 [Tb0 Hb0_eq]]].
    pose proof (VTrExpr_defeq_ctx Hves HwfL' HwfL0 Hceq Hbt_tr) as [bt0 [Hbt0 [Tbt0 Hbt0_eq]]].
    assert (Hctx_eq : VIsDefEqCtx venv (List.length ps) [] (dom' :: vl_ctx L) (dom0 :: vl_ctx L))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    assert (Hv0 : VHasType venv (List.length ps) (dom0 :: vl_ctx L) bt' (VSort v))
      by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx_eq | exact Hv]).
    assert (HG0' : VCtxWF venv (List.length ps) (dom0 :: vl_ctx L))
      by (split; [exact HG | exists u'; exact (VIsDefEq_refl_l Hdom_eq')]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG0' Hv0 (VIsDefEq_refl_r Hbt0_eq)) as [v0 Hcv0].
    assert (Hbt0_eq' : VIsDefEq venv (List.length ps) (dom0 :: vl_ctx L) bt0 bt' (VSort v))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv0) | exact Hbt0_eq]).
    exists (VLam dom' body'), (VForallE dom' bt'). repeat split.
    + exists (VLam dom0 b0). split.
      * eapply VTrExprS_lam; [exists u'; exact (VIsDefEq_refl_l Hdom_eq') | exact Hdom0 | exact Hb0].
      * exists (VForallE dom0 Tb0). eapply VDF_lamDF; [exact Hdom_eq' | exact Hb0_eq].
    + exists (VForallE dom0 bt0). split.
      * eapply VTrExprS_pi;
          [exists u'; exact (VIsDefEq_refl_l Hdom_eq') | exists v; exact (VIsDefEq_refl_l Hbt0_eq') |
           exact Hdom0 | exact Hbt0].
      * exists (VSort (VLIMax u' v)). eapply VDF_forallEDF; [exact Hdom_eq' | exact Hbt0_eq'].
    + eapply VHasType_lam; [exact Hdom_u | exact Hbody_bt].
  - (* EPi *)
    destruct (infer_step rec fuel env ps true g dom) as [dt0|err|why] eqn:Hdt0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g dt0) as [dt|err|why] eqn:Hwdt; simpl in Hinf; try discriminate.
    destruct dt as [| | |u0| | | | | | | |]; try discriminate.
    destruct (infer_step rec fuel env ps true (push_binding g dom None) body) as [bt0|err|why] eqn:Hbt0;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec (push_binding g dom None) bt0) as [bt|err|why] eqn:Hwbt;
      simpl in Hinf; try discriminate.
    destruct bt as [| | |v0| | | | | | | |]; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (IHA g L dt0 Hctx Hdt0) as [dom' [dt' [Hdom_tr [Hdt0_tr Hdom_dt]]]].
    pose proof (fms_whnf Hms Hctx Hdt0_tr Hwdt) as Hdt_tr.
    destruct (VTrExpr_inv_sort Hdt_tr) as [u' [Hu0' [Hu0_wf Hu_eq]]].
    assert (Hdom_u : VHasType venv (List.length ps) (vl_ctx L) dom' (VSort u'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hdom_dt |
            apply VIsDefEqU_symm; exact Hu_eq]).
    assert (Hctx' : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exists u'; exact Hdom_u]).
    destruct (IHB _ _ bt0 Hctx' Hbt0) as [body' [bt' [Hbody_tr [Hbt0_tr Hbody_bt]]]].
    pose proof (fms_whnf Hms Hctx' Hbt0_tr Hwbt) as Hbt_tr.
    destruct (VTrExpr_inv_sort Hbt_tr) as [v' [Hv0' [Hv0_wf Hv_eq]]].
    assert (HG' : VCtxWF venv (List.length ps) (dom' :: vl_ctx L))
      by (split; [exact HG | exists u'; exact Hdom_u]).
    assert (Hbody_v : VHasType venv (List.length ps) (dom' :: vl_ctx L) body' (VSort v'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG' | exact Hbody_bt |
            apply VIsDefEqU_symm; exact Hv_eq]).
    destruct Hdom_tr as [dom0 [Hdom0 [Td Hdom_eq]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hdom_u (VIsDefEq_refl_r Hdom_eq)) as [ud Hcd].
    assert (Hdom_eq' : VIsDefEq venv (List.length ps) (vl_ctx L) dom0 dom' (VSort u'))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcd) | exact Hdom_eq]).
    assert (HwfL0 : VLCtxWF venv (List.length ps) (vl_push_lam L dom0))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u'; exact (VIsDefEq_refl_l Hdom_eq')]).
    assert (HwfL' : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u'; exact Hdom_u]).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L dom') (vl_push_lam L dom0)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm Hdom_eq')]. }
    pose proof (VTrExpr_defeq_ctx Hves HwfL' HwfL0 Hceq Hbody_tr) as [b0 [Hb0 [Tb0 Hb0_eq]]].
    assert (Hctx_eq : VIsDefEqCtx venv (List.length ps) [] (dom' :: vl_ctx L) (dom0 :: vl_ctx L))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    assert (Hv0_b : VHasType venv (List.length ps) (dom0 :: vl_ctx L) body' (VSort v'))
      by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx_eq | exact Hbody_v]).
    assert (HG0' : VCtxWF venv (List.length ps) (dom0 :: vl_ctx L))
      by (split; [exact HG | exists u'; exact (VIsDefEq_refl_l Hdom_eq')]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG0' Hv0_b (VIsDefEq_refl_r Hb0_eq)) as [vb0 Hcvb0].
    assert (Hb0_eq' : VIsDefEq venv (List.length ps) (dom0 :: vl_ctx L) b0 body' (VSort v'))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcvb0) | exact Hb0_eq]).
    exists (VForallE dom' body'), (VSort (VLIMax u' v')). repeat split.
    + exists (VForallE dom0 b0). split.
      * eapply VTrExprS_pi;
          [exists u'; exact (VIsDefEq_refl_l Hdom_eq') | exists v'; exact (VIsDefEq_refl_l Hb0_eq') |
           exact Hdom0 | exact Hb0].
      * exists (VSort (VLIMax u' v')). eapply VDF_forallEDF; [exact Hdom_eq' | exact Hb0_eq'].
    + apply VTrExprS_to_VTrExpr. constructor. unfold TrLevel. simpl. rewrite Hu0', Hv0'. reflexivity.
    + eapply VHasType_forallE; [exact Hdom_u | exact Hbody_v].
  - (* ELet *)
    destruct (infer_step rec fuel env ps true g tyA) as [st0|err|why] eqn:Hst0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g st0) as [st|err|why] eqn:Hwst; simpl in Hinf; try discriminate.
    destruct st as [| | |u0| | | | | | | |]; try discriminate.
    destruct (infer_step rec fuel env ps true g val) as [vt|err|why] eqn:Hvt; simpl in Hinf; try discriminate.
    destruct (defeq_method rec g vt tyA) as [ok|err|why] eqn:Hok; simpl in Hinf; try discriminate.
    destruct ok; simpl in Hinf; [|discriminate].
    destruct (infer_step rec fuel env ps true (push_binding g tyA (Some val)) body) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (IHA g L st0 Hctx Hst0) as [tyA' [st' [HtyA_tr [Hst0_tr HtyA_st]]]].
    pose proof (fms_whnf Hms Hctx Hst0_tr Hwst) as Hst_tr.
    destruct (VTrExpr_inv_sort Hst_tr) as [u' [_ [_ Hu_eq]]].
    assert (HtyA_u : VHasType venv (List.length ps) (vl_ctx L) tyA' (VSort u'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact HtyA_st |
            apply VIsDefEqU_symm; exact Hu_eq]).
    destruct (IHv g L vt Hctx Hvt) as [val' [vt' [Hval_tr [Hvt_tr Hval_vt]]]].
    pose proof (fms_defeq Hms Hctx Hvt_tr HtyA_tr Hok) as Hvt_tyA.
    assert (Hval_tyA : VHasType venv (List.length ps) (vl_ctx L) val' tyA')
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hval_vt | exact Hvt_tyA]).
    assert (Hctx' : VTrCtx env venv ps (push_binding g tyA (Some val)) (vl_push_let L tyA' val'))
      by (apply VTrCtx_push_let; assumption).
    destruct (IHb _ _ bt Hctx' Hbt) as [body' [bt' [Hbody_tr [Hbt_tr Hbody_bt]]]].
    destruct HtyA_tr as [tyA0 [HtyA0 [TA0 HtyA_eq]]].
    destruct Hval_tr as [val0 [Hval0 [Tv0 Hval_eq]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG HtyA_u (VIsDefEq_refl_r HtyA_eq)) as [uA0 HcA0].
    assert (HtyA_eq' : VIsDefEq venv (List.length ps) (vl_ctx L) tyA0 tyA' (VSort u'))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA0) | exact HtyA_eq]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hval_tyA (VIsDefEq_refl_r Hval_eq)) as [uv0 Hcv0].
    assert (Hval_eq' : VIsDefEq venv (List.length ps) (vl_ctx L) val0 val' tyA')
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv0) | exact Hval_eq]).
    assert (Hval0_tyA0 : VHasType venv (List.length ps) (vl_ctx L) val0 tyA0)
      by (eapply VDF_defeqDF; [exact (VDF_symm HtyA_eq') | exact (VIsDefEq_refl_l Hval_eq')]).
    assert (HwfL' : VLCtxWF venv (List.length ps) (vl_push_let L tyA' val'))
      by (apply VLCtxWF_push_let; assumption).
    assert (HwfL0 : VLCtxWF venv (List.length ps) (vl_push_let L tyA0 val0))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_let L tyA' val') (vl_push_let L tyA0 val0)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto.
      econstructor; [exact Hb | exact (VDF_symm HtyA_eq') | exact (VDF_symm Hval_eq')]. }
    pose proof (VTrExpr_defeq_ctx Hves HwfL' HwfL0 Hceq Hbody_tr) as [b0 [Hb0 Hb0_eq]].
    exists body', bt'. repeat split.
    + exists b0. split; [eapply VTrExprS_let; eassumption | exact Hb0_eq].
    + eapply VTrExpr_instantiate_let;
        [exact Hves | exact HwfL | exact Hval_tyA |
         exists val0; split; [exact Hval0 | exists tyA'; exact Hval_eq'] | exact Hbt_tr].
    + exact Hbody_bt.
  - (* ELit *)
    destruct lit as [n|s].
    + destruct (core_nat_ready env) eqn:Hnat; [|discriminate].
      inversion Hinf; subst ty; clear Hinf.
      destruct (hp_nat (ves_prims Hves) Hnat) as [Hnat_ty _].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hnat_ty)) as Hnt'.
      simpl in Hnt'. destruct (VHasType_const_inv Hwf HG Hnt') as [ci [Hci [_ Hlen]]].
      assert (Hn_ty : VHasType venv (List.length ps) (vl_ctx L) (natLit n) vnat_ty)
        by (eapply natLit_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hnat]).
      exists (natLit n), vnat_ty. repeat split; [| | exact Hn_ty].
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_natlit; assumption.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
    + destruct (core_string_ready env) eqn:Hstr; [|discriminate].
      destruct (core_expand_string s) as [exp|err|why] eqn:Hexp; simpl in Hinf; try discriminate.
      inversion Hinf; subst ty; clear Hinf.
      unfold core_expand_string in Hexp.
      destruct (core_utf8 s) as [cs|] eqn:Hu; [|discriminate].
      assert (Htrs : trStrLit s = Some (VApp (VConst core_string_of_list []) (trCharList cs)))
        by (unfold trStrLit; rewrite Hu; reflexivity).
      destruct (hp_string (ves_prims Hves) Hstr) as [_ [Hstr_ty _]].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hstr_ty)) as Hst'.
      simpl in Hst'. destruct (VHasType_const_inv Hwf HG Hst') as [ci [Hci [_ Hlen]]].
      assert (Hs_ty : VHasType venv (List.length ps) (vl_ctx L)
                        (VApp (VConst core_string_of_list []) (trCharList cs)) vstring_ty)
        by (eapply trStrLit_has_type; [exact Hcl | exact (ves_prims Hves) | exact Hstr | exact Htrs]).
      exists (VApp (VConst core_string_of_list []) (trCharList cs)), vstring_ty.
      repeat split; [| | exact Hs_ty].
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_strlit; eassumption.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
  - (* EProj *)
    destruct (core_inductive env owner) as [info|]; [|discriminate].
    destruct (core_infer_projection_sound Hves Hms Hctx (or_introl eq_refl) Hinf) as [e' [ty' [Htp _]]].
    exists e', ty'. exact Htp.
  - (* EMData *)
    destruct (IHb g L ty Hctx Hinf) as [e' [ty' [[e0 [He0 Heq]] [Hty_tr Hht]]]].
    exists e', ty'. repeat split; [exists e0; split; [constructor; exact He0 | exact Heq] | exact Hty_tr | exact Hht].
Qed.

(* Full 13-constructor soundness of `infer_step ... false` (inference-only mode on already-translated terms) *)
Theorem infer_step_sound_false env venv ps chk rec fuel e :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  forall g L e' ty,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    infer_step rec fuel env ps false g e = Accept ty ->
    exists ty',
      VTrExpr env venv ps L ty ty' /\
      VHasType venv (List.length ps) (vl_ctx L) e' ty'.
Proof.
  intros Hves Hms.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  induction e as [i|n|n|u|c us|f IHf a IHa|nm bi dom IHA body IHb|nm bi dom IHA body IHB
                  |nm tyA IHA val IHv body IHb nd|lit|owner idx val IHa|body IHb];
    intros g L e' ty Hctx Htr Hinf;
    pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL;
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG;
    simpl in Hinf; try discriminate.
  - (* EBVar *)
    destruct (nth_error (bound_context g) i) as [b|] eqn:Hnth; [|discriminate].
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrCtx_lookup_bound Hcl Hctx Hnth) as [eb' [ty' [Hlk [Hty [Htr_ty _]]]]].
    destruct Htr as [e0 [Htr0 Heq0]].
    inversion Htr0 as [? ? ? ty0 Hlk0 _ | | | | | | | | | | |]; subst.
    rewrite Hlk in Hlk0. inversion Hlk0; subst e0 ty0.
    exists ty'. split; [exact Htr_ty |].
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hty | exact Heq0].
  - (* EFVar *)
    destruct (find_free n (free_context g)) as [b|] eqn:Hfind; [|discriminate].
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrCtx_lookup_free Hcl Hctx Hfind) as [ef' [ty' [Hlk [Hty [Htr_ty _]]]]].
    destruct Htr as [e0 [Htr0 Heq0]].
    inversion Htr0 as [| ? ? ? ty0 Hlk0 _ | | | | | | | | | |]; subst.
    rewrite Hlk in Hlk0. inversion Hlk0; subst e0 ty0.
    exists ty'. split; [exact Htr_ty |].
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hty | exact Heq0].
  - (* ESort *)
    destruct (check_level ps u) as [[]|err|why] eqn:Hchk; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrExpr_inv_sort Htr) as [u' [Hu' [Huwf Hueq]]].
    exists (VSort (VLSucc u')). split.
    + apply VTrExprS_to_VTrExpr. constructor. unfold TrLevel. simpl. rewrite Hu'. reflexivity.
    + eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | apply VHasType_sort; exact Huwf | exact Hueq].
  - (* EConst *)
    destruct (get_constant env ps c us) as [d|err|why] eqn:Hget; simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (get_constant_sound Hves HwfL Hget)
      as [ci [us' [_ [_ [Hci [_ [Hlen [Hus' [_ [Hty_tr Hc_ty]]]]]]]]]].
    destruct (VTrExpr_inv_const Htr) as [ci2 [us2 [Hci2 [Hus2 [_ [_ Heq]]]]]].
    assert (Hus_eq : us' = us2).
    { clear -Hus' Hus2. revert us2 Hus2.
      induction Hus' as [| u u' r r' Hu Hr IH]; intros us2 H;
        inversion H as [| ? u2 ? r2 Hu2 Hr2]; subst; [reflexivity |].
      unfold TrLevel in *. rewrite Hu in Hu2. inversion Hu2; subst. f_equal. auto. }
    subst us2.
    exists (vinstL us' (vc_type ci)). split; [exact Hty_tr |].
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hc_ty | exact Heq].
  - (* EApp *)
    destruct (infer_step rec fuel env ps false g f) as [ft0|err|why] eqn:Hft0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g ft0) as [ft|err|why] eqn:Hwft; simpl in Hinf; try discriminate.
    destruct ft as [| | | | | | |nm bi dom body| | | |]; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrExpr_inv_app Htr) as [f' [a' [A [B [Hf_AB [Ha_A [Hf_tr [Ha_tr Heq_app]]]]]]]].
    destruct (IHf g L f' ft0 Hctx Hf_tr Hft0) as [ft' [Hft0_tr Hf_ft]].
    pose proof (fms_whnf Hms Hctx Hft0_tr Hwft) as Hft_tr.
    destruct (VTrExpr_inv_pi Hft_tr) as [dom' [body' [_ [_ [_ [Hbody_tr Hpi_eq]]]]]].
    assert (Hf_pi : VHasType venv (List.length ps) (vl_ctx L) f' (VForallE dom' body'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hf_ft |
            apply VIsDefEqU_symm; exact Hpi_eq]).
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG (VIsDefEq_uniqU Hwf Hinj HG Hf_AB Hf_pi))
      as [[uA HA_eq] _].
    assert (Ha_dom : VHasType venv (List.length ps) (vl_ctx L) a' dom')
      by (eapply VDF_defeqDF; [exact HA_eq | exact Ha_A]).
    assert (Hfa_ty : VHasType venv (List.length ps) (vl_ctx L) (VApp f' a') (vinst0 body' a'))
      by (eapply VHasType_app; [exact Hf_pi | exact Ha_dom]).
    exists (vinst0 body' a'). split.
    + eapply VTrExpr_instantiate_lam; [exact Hves | exact HwfL | exact Ha_dom | exact Ha_tr | exact Hbody_tr].
    + eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hfa_ty | exact Heq_app].
  - (* ELam *)
    destruct (infer_step rec fuel env ps false (push_binding g dom None) body) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrExpr_inv_lam Htr) as [dom' [body' [Hdom_is [Hdom_tr [Hbody_tr Heq_lam]]]]].
    destruct Hdom_is as [u Hu].
    assert (Hctx' : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exists u; exact Hu]).
    destruct (IHb _ _ body' bt Hctx' Hbody_tr Hbt) as [bt' [Hbt_tr Hbody_bt]].
    assert (HG' : VCtxWF venv (List.length ps) (dom' :: vl_ctx L))
      by (split; [exact HG | exists u; exact Hu]).
    destruct (VIsDefEq_isType Hwf HG' Hbody_bt) as [v Hv].
    destruct Hdom_tr as [dom0 [Hdom0 [Td Hdom_eq]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_r Hdom_eq)) as [ud Hcd].
    assert (Hdom_eq' : VIsDefEq venv (List.length ps) (vl_ctx L) dom0 dom' (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcd) | exact Hdom_eq]).
    assert (HwfL0 : VLCtxWF venv (List.length ps) (vl_push_lam L dom0))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact (VIsDefEq_refl_l Hdom_eq')]).
    assert (HwfL' : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact Hu]).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L dom') (vl_push_lam L dom0)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact (VDF_symm Hdom_eq')]. }
    pose proof (VTrExpr_defeq_ctx Hves HwfL' HwfL0 Hceq Hbt_tr) as [bt0 [Hbt0 [Tbt0 Hbt0_eq]]].
    assert (Hctx_eq : VIsDefEqCtx venv (List.length ps) [] (dom' :: vl_ctx L) (dom0 :: vl_ctx L))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    assert (Hv0 : VHasType venv (List.length ps) (dom0 :: vl_ctx L) bt' (VSort v))
      by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx_eq | exact Hv]).
    assert (HG0' : VCtxWF venv (List.length ps) (dom0 :: vl_ctx L))
      by (split; [exact HG | exists u; exact (VIsDefEq_refl_l Hdom_eq')]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG0' Hv0 (VIsDefEq_refl_r Hbt0_eq)) as [v0 Hcv0].
    assert (Hbt0_eq' : VIsDefEq venv (List.length ps) (dom0 :: vl_ctx L) bt0 bt' (VSort v))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv0) | exact Hbt0_eq]).
    exists (VForallE dom' bt'). split.
    + exists (VForallE dom0 bt0). split.
      * eapply VTrExprS_pi;
          [exists u; exact (VIsDefEq_refl_l Hdom_eq') | exists v; exact (VIsDefEq_refl_l Hbt0_eq') |
           exact Hdom0 | exact Hbt0].
      * exists (VSort (VLIMax u v)). eapply VDF_forallEDF; [exact Hdom_eq' | exact Hbt0_eq'].
    + eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG |
        eapply VHasType_lam; [exact Hu | exact Hbody_bt] | exact Heq_lam].
  - (* EPi *)
    destruct (infer_step rec fuel env ps false g dom) as [dt0|err|why] eqn:Hdt0; simpl in Hinf; try discriminate.
    destruct (whnf_method rec g dt0) as [dt|err|why] eqn:Hwdt; simpl in Hinf; try discriminate.
    destruct dt as [| | |u0| | | | | | | |]; try discriminate.
    destruct (infer_step rec fuel env ps false (push_binding g dom None) body) as [bt0|err|why] eqn:Hbt0;
      simpl in Hinf; try discriminate.
    destruct (whnf_method rec (push_binding g dom None) bt0) as [bt|err|why] eqn:Hwbt;
      simpl in Hinf; try discriminate.
    destruct bt as [| | |v0| | | | | | | |]; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrExpr_inv_pi Htr) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Heq_pi]]]]]].
    destruct (IHA g L dom' dt0 Hctx Hdom_tr Hdt0) as [dt' [Hdt0_tr Hdom_dt]].
    pose proof (fms_whnf Hms Hctx Hdt0_tr Hwdt) as Hdt_tr.
    destruct (VTrExpr_inv_sort Hdt_tr) as [u' [Hu0' [Hu0_wf Hu_eq]]].
    assert (Hdom_u : VHasType venv (List.length ps) (vl_ctx L) dom' (VSort u'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hdom_dt |
            apply VIsDefEqU_symm; exact Hu_eq]).
    assert (Hctx' : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exists u'; exact Hdom_u]).
    destruct (IHB _ _ body' bt0 Hctx' Hbody_tr Hbt0) as [bt' [Hbt0_tr Hbody_bt]].
    pose proof (fms_whnf Hms Hctx' Hbt0_tr Hwbt) as Hbt_tr.
    destruct (VTrExpr_inv_sort Hbt_tr) as [v' [Hv0' [Hv0_wf Hv_eq]]].
    assert (HG' : VCtxWF venv (List.length ps) (dom' :: vl_ctx L))
      by (split; [exact HG | exists u'; exact Hdom_u]).
    assert (Hbody_v : VHasType venv (List.length ps) (dom' :: vl_ctx L) body' (VSort v'))
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG' | exact Hbody_bt |
            apply VIsDefEqU_symm; exact Hv_eq]).
    exists (VSort (VLIMax u' v')). split.
    + apply VTrExprS_to_VTrExpr. constructor. unfold TrLevel. simpl. rewrite Hu0', Hv0'. reflexivity.
    + eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG |
        eapply VHasType_forallE; [exact Hdom_u | exact Hbody_v] | exact Heq_pi].
  - (* ELet *)
    destruct (infer_step rec fuel env ps false (push_binding g tyA (Some val)) body) as [bt|err|why] eqn:Hbt;
      simpl in Hinf; try discriminate.
    inversion Hinf; subst ty; clear Hinf.
    destruct (VTrExpr_inv_let Htr) as [tyA' [val' [body' [Hvt [HtyA_tr [Hval_tr [Hbody_tr Heq_b]]]]]]].
    assert (Hctx' : VTrCtx env venv ps (push_binding g tyA (Some val)) (vl_push_let L tyA' val'))
      by (apply VTrCtx_push_let; assumption).
    destruct (IHb _ _ body' bt Hctx' Hbody_tr Hbt) as [bt' [Hbt_tr Hbody_bt]].
    exists bt'. split.
    + eapply VTrExpr_instantiate_let; [exact Hves | exact HwfL | exact Hvt | exact Hval_tr | exact Hbt_tr].
    + eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hbody_bt | exact Heq_b].
  - (* ELit *)
    destruct lit as [n|s].
    + destruct (core_nat_ready env) eqn:Hnat; [|discriminate].
      inversion Hinf; subst ty; clear Hinf.
      destruct (VTrExpr_inv_natlit Htr) as [_ [Hn_ty Heq_n]].
      destruct (hp_nat (ves_prims Hves) Hnat) as [Hnat_ty _].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hnat_ty)) as Hnt'.
      simpl in Hnt'. destruct (VHasType_const_inv Hwf HG Hnt') as [ci [Hci [_ Hlen]]].
      exists vnat_ty. split.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
      * eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hn_ty | exact Heq_n].
    + destruct (core_string_ready env) eqn:Hstr; [|discriminate].
      destruct (core_expand_string s) as [exp|err|why] eqn:Hexp; simpl in Hinf; try discriminate.
      inversion Hinf; subst ty; clear Hinf.
      destruct (VTrExpr_inv_strlit Htr) as [s' [_ [_ [Hs_ty Heq_s]]]].
      destruct (hp_string (ves_prims Hves) Hstr) as [_ [Hstr_ty _]].
      pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
        (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hstr_ty)) as Hst'.
      simpl in Hst'. destruct (VHasType_const_inv Hwf HG Hst') as [ci [Hci [_ Hlen]]].
      exists vstring_ty. split.
      * apply VTrExprS_to_VTrExpr. eapply VTrExprS_const; [exact Hci | constructor | simpl in *; lia].
      * eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hs_ty | exact Heq_s].
  - (* EProj *)
    destruct (core_inductive env owner) as [info|]; [|discriminate].
    destruct (VTrExpr_inv_proj Htr) as [val' [pv [fty [Hval_tr [Hproj Heq_pv]]]]].
    destruct (core_infer_projection_sound Hves (FullMethodsSound_inference_only Hms) Hctx
                (or_intror (ex_intro _ val' Hval_tr)) Hinf)
      as [e_p [ty' [[Hpe_tr [Hty_tr Hpe_ty]] Hproj_fn]]].
    destruct (Hproj_fn val' Hval_tr) as [pv2 [Hpv2_eq Hproj2]].
    pose proof (VTrProj_congr Hves HG Hproj Hproj2
                  (VTrExpr_has_type Hval_tr)) as Hpv12.
    exists ty'. split; [exact Hty_tr |].
    eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hpe_ty |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hpv2_eq |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hpv12 | exact Heq_pv].
  - (* EMData *)
    exact (IHb g L e' ty Hctx (VTrExpr_inv_mdata Htr) Hinf).
Qed.

(* ========================================================================= *)
(* 6. Definitional Equality Soundness (`IsDefEq.lean` Parity)                *)
(* ========================================================================= *)

Lemma VLCtxDefEq_push_lam env U L A1 A2 u :
  VEnvWF env ->
  VLCtxWF env U L ->
  VIsDefEq env U (vl_ctx L) A1 A2 (VSort u) ->
  VLCtxDefEq env U (vl_push_lam L A1) (vl_push_lam L A2).
Proof.
  intros Hwf HwfL HA.
  pose proof (VLCtxDefEq_refl Hwf HwfL) as [Hfn [Hfr Hbd]].
  unfold vl_push_lam, VLCtxDefEq; simpl.
  split; [exact Hfn | split; [exact Hfr |]].
  eapply VLCtxEntriesDefEq_lam; [exact Hbd | exact HA].
Qed.

Lemma VTrExpr_core_alpha_eq_local env venv ps L t s t' s' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_alpha_eq t s = true ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves HwfL Ha Ht Hs.
  unfold core_alpha_eq in Ha.
  destruct (core_alpha 256 t s) as [ok rem] eqn:E. simpl in Ha; subst ok.
  eapply VTrExpr_expr_eqb; [exact Hves | exact HwfL | eapply core_alpha_sound; exact E | exact Ht | exact Hs].
Qed.

(* 6a. Quick checks (`core_quick`) *)
Lemma core_quick_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_quick rec fuel g t s = Accept (Some true) ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hq.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_quick in Hq.
  destruct (core_alpha_eq t s) eqn:Hal.
  - eapply VTrExpr_core_alpha_eq_local; eassumption.
  - destruct t as [| | |u| | |nm1 bi1 a b|nm1 bi1 a b| |l1| |m1];
    destruct s as [| | |v| | |nm2 bi2 c d|nm2 bi2 c d| |l2| |m2];
    try discriminate.
    + (* ESort u, ESort v *)
      destruct (level_equiv fuel u v) as [ok|err|why] eqn:Heq; simpl in Hq; try discriminate.
      destruct ok; inversion Hq; clear Hq.
      destruct (VTrExpr_inv_sort Ht) as [u' [Hu [Hu_wf Heq_t]]].
      destruct (VTrExpr_inv_sort Hs) as [v' [Hv [Hv_wf Heq_s]]].
      assert (Huv : vlevel_equiv u' v') by (eapply level_equiv_sound_vlevel; eassumption).
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        exists (VSort (VLSucc u')); eapply VDF_sortDF; eassumption | exact Heq_s].
    + (* ELam, ELam *)
      destruct (defeq_method rec g a c) as [ok1|err|why] eqn:H1; simpl in Hq; try discriminate.
      destruct ok1; [|discriminate].
      destruct (defeq_method rec (push_binding g a None) b d) as [ok2|err|why] eqn:H2;
        simpl in Hq; try discriminate.
      destruct ok2; [|discriminate].
      destruct (VTrExpr_inv_lam Ht) as [a' [b' [Ha_is [Ha_tr [Hb_tr Heq_t]]]]].
      destruct (VTrExpr_inv_lam Hs) as [c' [d' [Hc_is [Hc_tr [Hd_tr Heq_s]]]]].
      pose proof (fms_defeq Hms Hctx Ha_tr Hc_tr H1) as [Tac Hac].
      destruct Ha_is as [uA HuA]. destruct Hc_is as [uC HuC].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG HuA Hac) as [u1 Hc1].
      assert (Hac_s : VIsDefEq venv (List.length ps) (vl_ctx L) a' c' (VSort uA))
        by (eapply VDF_defeqDF; [exact (VDF_symm Hc1) | exact Hac]).
      assert (HwfL_a : VLCtxWF venv (List.length ps) (vl_push_lam L a'))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists uA; exact HuA]).
      assert (HwfL_c : VLCtxWF venv (List.length ps) (vl_push_lam L c'))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists uC; exact HuC]).
      assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L c') (vl_push_lam L a'))
        by (eapply VLCtxDefEq_push_lam; [exact Hwf | exact HwfL | exact (VDF_symm Hac_s)]).
      pose proof (VTrExpr_defeq_ctx Hves HwfL_c HwfL_a Hceq Hd_tr) as Hd_tr_a.
      assert (Hctx_a : VTrCtx env venv ps (push_binding g a None) (vl_push_lam L a'))
        by (apply VTrCtx_push_lam; [exact Hctx | exact Ha_tr | exists uA; exact HuA]).
      pose proof (fms_defeq Hms Hctx_a Hb_tr Hd_tr_a H2) as [Tbd Hbd].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        exists (VForallE a' Tbd); eapply VDF_lamDF; [exact Hac_s | exact Hbd] | exact Heq_s].
    + (* EPi, EPi *)
      destruct (defeq_method rec g a c) as [ok1|err|why] eqn:H1; simpl in Hq; try discriminate.
      destruct ok1; [|discriminate].
      destruct (defeq_method rec (push_binding g a None) b d) as [ok2|err|why] eqn:H2;
        simpl in Hq; try discriminate.
      destruct ok2; [|discriminate].
      destruct (VTrExpr_inv_pi Ht) as [a' [b' [Ha_is [Hb_is [Ha_tr [Hb_tr Heq_t]]]]]].
      destruct (VTrExpr_inv_pi Hs) as [c' [d' [Hc_is [Hd_is [Hc_tr [Hd_tr Heq_s]]]]]].
      pose proof (fms_defeq Hms Hctx Ha_tr Hc_tr H1) as [Tac Hac].
      destruct Ha_is as [uA HuA]. destruct Hc_is as [uC HuC].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG HuA Hac) as [u1 Hc1].
      assert (Hac_s : VIsDefEq venv (List.length ps) (vl_ctx L) a' c' (VSort uA))
        by (eapply VDF_defeqDF; [exact (VDF_symm Hc1) | exact Hac]).
      assert (HwfL_a : VLCtxWF venv (List.length ps) (vl_push_lam L a'))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists uA; exact HuA]).
      assert (HwfL_c : VLCtxWF venv (List.length ps) (vl_push_lam L c'))
        by (apply VLCtxWF_push_lam; [exact HwfL | exists uC; exact HuC]).
      assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L c') (vl_push_lam L a'))
        by (eapply VLCtxDefEq_push_lam; [exact Hwf | exact HwfL | exact (VDF_symm Hac_s)]).
      pose proof (VTrExpr_defeq_ctx Hves HwfL_c HwfL_a Hceq Hd_tr) as Hd_tr_a.
      assert (Hctx_a : VTrCtx env venv ps (push_binding g a None) (vl_push_lam L a'))
        by (apply VTrCtx_push_lam; [exact Hctx | exact Ha_tr | exists uA; exact HuA]).
      pose proof (fms_defeq Hms Hctx_a Hb_tr Hd_tr_a H2) as [Tbd Hbd].
      destruct Hb_is as [vB HvB].
      assert (HG_a : VCtxWF venv (List.length ps) (a' :: vl_ctx L))
        by (split; [exact HG | exists uA; exact HuA]).
      destruct (VIsDefEq_uniq_same Hwf Hinj HG_a HvB Hbd) as [u2 Hc2].
      assert (Hbd_s : VIsDefEq venv (List.length ps) (a' :: vl_ctx L) b' d' (VSort vB))
        by (eapply VDF_defeqDF; [exact (VDF_symm Hc2) | exact Hbd]).
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        exists (VSort (VLIMax uA vB)); eapply VDF_forallEDF; [exact Hac_s | exact Hbd_s] | exact Heq_s].
    + (* ELit, ELit *)
      destruct (literal_eqb l1 l2) eqn:El; [|discriminate].
      apply literal_eqb_true in El. subst l2.
      eapply VTrExpr_uniq; eassumption.
    + (* EMData, EMData *)
      destruct (defeq_method rec g m1 m2) as [ok|err|why] eqn:H1; simpl in Hq; try discriminate.
      destruct ok; [|discriminate].
      exact (fms_defeq Hms Hctx (VTrExpr_inv_mdata Ht) (VTrExpr_inv_mdata Hs) H1).
Qed.

(* 6b. True shortcut (`core_true_shortcut`) *)
Lemma core_is_true_eq e :
  core_is_true e = true -> e = EConst core_true_name [].
Proof.
  unfold core_is_true. destruct e as [| | | |n us| | | | | | |]; try discriminate.
  destruct us; [|discriminate]. intros H. apply name_eqb_eq in H. subst. reflexivity.
Qed.

Lemma core_true_shortcut_sound env venv ps chk rec g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_true_shortcut rec env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hsc.
  unfold core_true_shortcut in Hsc.
  destruct (core_is_true s && true_probe_allowed (method_mode rec) t && core_bool_ready env) eqn:E;
    [|discriminate].
  apply andb_true_iff in E as [E1 _]. apply andb_true_iff in E1 as [Hs_t _].
  destruct (whnf_method rec g t) as [tn|err|why] eqn:Hw; simpl in Hsc; try discriminate.
  inversion Hsc as [Htn_t].
  apply core_is_true_eq in Hs_t. apply core_is_true_eq in Htn_t.
  subst s tn.
  pose proof (fms_whnf Hms Hctx Ht Hw) as Htn_tr.
  eapply VTrExpr_uniq; [exact Hves | exact (VTrCtx_to_VLCtxWF Hctx) | exact Htn_tr | exact Hs].
Qed.

(* 6c. Proof irrelevance (`core_proof_irrel`) *)
Lemma core_proof_irrel_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_proof_irrel rec fuel g t s = Accept (Some true) ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hpi.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_proof_irrel in Hpi.
  destruct (infer_method rec g t) as [ty|err|why] eqn:Hit; simpl in Hpi; try discriminate.
  destruct (sort_of rec g ty) as [su|err|why] eqn:Hsu; simpl in Hpi; try discriminate.
  destruct (level_equiv fuel su LZero) as [is_p|err|why] eqn:Hp; simpl in Hpi; try discriminate.
  destruct is_p; [|discriminate].
  destruct (infer_method rec g s) as [sty|err|why] eqn:His; simpl in Hpi; try discriminate.
  destruct (defeq_method rec g ty sty) as [ok|err|why] eqn:Hok; simpl in Hpi; try discriminate.
  destruct ok; [|discriminate].
  destruct (fms_infer_typed Hms Hctx Ht Hit) as [ty' [Hty_tr Ht_ty]].
  destruct (sort_of_sound_typed Hves Hms Hctx Hty_tr Hsu) as [su' [Hsu' [Hsu_wf Hty_su]]].
  assert (Hty_prop : VHasType venv (List.length ps) (vl_ctx L) ty' (VSort VLZero)).
  { eapply VDF_defeqDF;
      [eapply VDF_sortDF; [exact Hsu_wf | exact I |
         eapply level_equiv_sound_vlevel with (v := LZero); [exact Hsu' | reflexivity | exact Hp]]
      | exact Hty_su]. }
  destruct (fms_infer_typed Hms Hctx Hs His) as [sty' [Hsty_tr Hs_sty]].
  pose proof (fms_defeq Hms Hctx Hty_tr Hsty_tr Hok) as Hty_sty.
  assert (Hs_ty : VHasType venv (List.length ps) (vl_ctx L) s' ty')
    by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hs_sty |
          apply VIsDefEqU_symm; exact Hty_sty]).
  exists ty'. eapply VDF_proofIrrel; [exact Hty_prop | exact Ht_ty | exact Hs_ty].
Qed.

(* 6d. Nat offset (`core_offset`) *)
Lemma core_offset_sound env venv ps chk rec g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_offset rec env g t s = Accept (Some true) ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hoff.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_offset in Hoff.
  destruct (core_nat_ready env) eqn:Hnat; [|discriminate].
  set (zero := fun e => match e with
    | ELit (LitNat n) => N.eqb n 0
    | EConst n [] => name_eqb n core_zero_name
    | _ => false end).
  set (pred_of := fun e => match e with
    | ELit (LitNat n) => if N.eqb n 0 then None else Some (ELit (LitNat (N.pred n)))
    | EApp (EConst n []) a => if name_eqb n core_succ_name then Some a else None
    | _ => None end).
  change ((if zero t && zero s then Accept (Some true)
           else match pred_of t, pred_of s with
                | Some a, Some b => ok <- defeq_method rec g a b;; Accept (Some ok)
                | _, _ => Accept None
                end) = Accept (Some true)) in Hoff.
  assert (Hzero_s : forall e e', VTrExpr env venv ps L e e' -> zero e = true ->
      VIsDefEqU venv (List.length ps) (vl_ctx L) (natLit 0%N) e').
  { intros e e' He Hz. unfold zero in Hz.
    destruct e as [| | | |n us| | | | |lit| |]; try discriminate.
    - destruct us; [|discriminate]. apply name_eqb_eq in Hz. subst n.
      destruct (VTrExpr_inv_const He) as [_ [us' [_ [Hus' [_ [_ Heq]]]]]].
      inversion Hus'; subst us'. rewrite natLit_0. exact Heq.
    - destruct lit as [n|st]; [|discriminate]. apply N.eqb_eq in Hz. subst n.
      destruct (VTrExpr_inv_natlit He) as [_ [_ Heq]]. exact Heq. }
  destruct (hp_nat (ves_prims Hves) Hnat) as [_ [_ Hsucc0]].
  pose proof (VIsDefEq_weak0 (vl_ctx L) Hcl
    (VIsDefEq_instL (U' := List.length ps) (ls := []) (Forall_nil _) Hsucc0)) as Hsucc.
  simpl in Hsucc.
  assert (Hpred_s : forall e e' p, VTrExpr env venv ps L e e' -> pred_of e = Some p ->
      exists p',
        VTrExpr env venv ps L p p' /\
        VHasType venv (List.length ps) (vl_ctx L) p' vnat_ty /\
        VIsDefEqU venv (List.length ps) (vl_ctx L) (VApp (VConst core_succ_name []) p') e').
  { intros e e' p He Hp. unfold pred_of in Hp.
    destruct e as [| | | | |f a| | | |lit| |]; try discriminate.
    - destruct f as [| | | |n us| | | | | | |]; try discriminate.
      destruct us; [|discriminate].
      destruct (name_eqb n core_succ_name) eqn:En; [|discriminate].
      apply name_eqb_eq in En. subst n. inversion Hp; subst p; clear Hp.
      destruct (VTrExpr_inv_app He) as [f' [a' [A [B [Hf_ty [Ha_ty [Htr_f [Htr_a Heq]]]]]]]].
      destruct (VTrExpr_inv_const Htr_f) as [_ [us' [_ [Hus' [_ [_ Hf_eq]]]]]].
      inversion Hus'; subst us'.
      assert (Hwf_app : VExprWF venv (List.length ps) (vl_ctx L) (vapps f' [a']))
        by (simpl; exact (VIsDefEqU_refl_l Heq)).
      assert (Ha_refl : VIsDefEqU venv (List.length ps) (vl_ctx L) a' a')
        by (exists A; exact Ha_ty).
      destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_app (VIsDefEqU_symm Hf_eq)
                  (@Forall2_cons _ _ _ _ _ _ _ Ha_refl (Forall2_nil _))) as [Hwf_sa Hsa_eq].
      simpl in Hwf_sa, Hsa_eq.
      destruct Hwf_sa as [Ts Hsa_ty].
      destruct (VHasType_app_inv Hwf HG Hsa_ty) as [A1 [B1 [Hs_f Ha1]]].
      destruct (VIsDefEqU_forallE_inv Hwf Hinj HG (VIsDefEq_uniqU Hwf Hinj HG Hs_f Hsucc))
        as [[u1 HA1] _].
      exists a'. split; [exact Htr_a | split].
      + eapply VDF_defeqDF; [exact HA1 | exact Ha1].
      + eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
          apply VIsDefEqU_symm; exact Hsa_eq | exact Heq].
    - destruct lit as [n|st]; [|discriminate].
      destruct (N.eqb n 0) eqn:Ez; [discriminate |].
      inversion Hp; subst p; clear Hp.
      destruct (VTrExpr_inv_natlit He) as [_ [_ Heq]].
      assert (Hpn : VHasType venv (List.length ps) (vl_ctx L) (natLit (N.pred n)) vnat_ty)
        by (eapply (@natLit_has_type env); [exact Hcl | exact (ves_prims Hves) | exact Hnat]).
      exists (natLit (N.pred n)). split; [| split; [exact Hpn |]].
      + apply VTrExprS_to_VTrExpr. eapply VTrExprS_natlit; [exact Hnat | exact Hpn].
      + rewrite <- natLit_pred_succ by (apply N.eqb_neq; exact Ez). exact Heq. }
  destruct (zero t && zero s) eqn:Ezz.
  - apply andb_true_iff in Ezz as [Hzt Hzs].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact (Hzero_s _ _ Ht Hzt) | exact (Hzero_s _ _ Hs Hzs)].
  - destruct (pred_of t) as [a|] eqn:Hpt; [|discriminate].
    destruct (pred_of s) as [b|] eqn:Hps; [|discriminate].
    destruct (defeq_method rec g a b) as [ok|err|why] eqn:Hab; simpl in Hoff; try discriminate.
    destruct ok; [|discriminate].
    destruct (Hpred_s _ _ _ Ht Hpt) as [a' [Ha_tr [Ha_nat Ha_eq]]].
    destruct (Hpred_s _ _ _ Hs Hps) as [b' [Hb_tr [Hb_nat Hb_eq]]].
    pose proof (fms_defeq Hms Hctx Ha_tr Hb_tr Hab) as [Tab Hab_eq].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Ha_nat Hab_eq) as [u Hcu].
    assert (Hab_nat : VIsDefEq venv (List.length ps) (vl_ctx L) a' b' vnat_ty)
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcu) | exact Hab_eq]).
    assert (Hsa_sb : VIsDefEqU venv (List.length ps) (vl_ctx L)
        (VApp (VConst core_succ_name []) a') (VApp (VConst core_succ_name []) b')).
    { eexists. eapply VDF_appDF; [exact Hsucc | exact Hab_nat]. }
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Ha_eq |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hsa_sb | exact Hb_eq].
Qed.

(* 6e. Same head & argument list comparisons (`core_same_head`, `core_compare_args*`) *)
Lemma core_same_head_sound env venv ps fuel L t s t' s' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_same_head fuel t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves HwfL Ht Hs Hsh.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_same_head in Hsh.
  destruct t as [i|n| | |n us| | | | | | |];
  destruct s as [j|m| | |m vs| | | | | | |]; try discriminate.
  - inversion Hsh as [Hij]. apply Nat.eqb_eq in Hij. subst j.
    eapply VTrExpr_uniq; eassumption.
  - inversion Hsh as [Hnm]. apply name_eqb_eq in Hnm. subst m.
    eapply VTrExpr_uniq; eassumption.
  - destruct (name_eqb n m) eqn:Enm; [|discriminate].
    apply name_eqb_eq in Enm. subst m.
    destruct (VTrExpr_inv_const Ht) as [ci1 [us' [Hci1 [Hus' [Hw_us [Hlu Heq_t]]]]]].
    destruct (VTrExpr_inv_const Hs) as [ci2 [vs' [Hci2 [Hvs' [Hw_vs [Hlv Heq_s]]]]]].
    rewrite Hci1 in Hci2. inversion Hci2; subst ci2; clear Hci2.
    pose proof (levels_equiv_sound_TrLevels fuel Hus' Hvs' Hsh) as Huv.
    assert (Hcdf : VIsDefEqU venv (List.length ps) (vl_ctx L) (VConst n us') (VConst n vs')).
    { exists (vinstL us' (vc_type ci1)).
      eapply VDF_constDF; [exact Hci1 | exact Hw_us | exact Hw_vs |
        rewrite <- (TrLevels_length Hus'); exact Hlu | exact Huv]. }
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hcdf | exact Heq_s].
Qed.

Lemma core_compare_args_sound env venv ps chk rec g L :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  forall xs ys xs' ys',
    Forall2 (VTrExpr env venv ps L) xs xs' ->
    Forall2 (VTrExpr env venv ps L) ys ys' ->
    core_compare_args rec g xs ys = Accept true ->
    Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) xs' ys'.
Proof.
  intros Hves Hms Hctx.
  induction xs as [|x xs IH]; intros [|y ys] xs' ys' Hxs Hys Hc; simpl in Hc; try discriminate.
  - inversion Hxs; inversion Hys; subst. constructor.
  - inversion Hxs as [| ? x' ? r1 Hx Hrx]; subst.
    inversion Hys as [| ? y' ? r2 Hy Hry]; subst.
    destruct (defeq_method rec g x y) as [ok|err|why] eqn:Hxy; simpl in Hc; try discriminate.
    destruct ok; [|discriminate].
    constructor; [exact (fms_defeq Hms Hctx Hx Hy Hxy) | exact (IH ys r1 r2 Hrx Hry Hc)].
Qed.

Lemma core_compare_args_both_sound env venv ps chk rec g L :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  forall xs ys xs' ys',
    Forall2 (VTrExpr env venv ps L) xs xs' ->
    Forall2 (VTrExpr env venv ps L) ys ys' ->
    core_compare_args_filtered true rec env g xs ys = Accept true ->
    core_compare_args_filtered false rec env g xs ys = Accept true ->
    Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) xs' ys'.
Proof.
  intros Hves Hms Hctx.
  induction xs as [|x xs IH]; intros [|y ys] xs' ys' Hxs Hys H1 H2; simpl in H1, H2; try discriminate.
  - inversion Hxs; inversion Hys; subst. constructor.
  - inversion Hxs as [| ? x' ? r1 Hx Hrx]; subst.
    inversion Hys as [| ? y' ? r2 Hy Hry]; subst.
    destruct (core_is_cheap_arg env x && core_is_cheap_arg env y); simpl in H1, H2.
    + destruct (defeq_method rec g x y) as [ok|err|why] eqn:Hxy; simpl in H1; try discriminate.
      destruct ok; [|discriminate].
      constructor; [exact (fms_defeq Hms Hctx Hx Hy Hxy) | exact (IH ys r1 r2 Hrx Hry H1 H2)].
    + destruct (defeq_method rec g x y) as [ok|err|why] eqn:Hxy; simpl in H2; try discriminate.
      destruct ok; [|discriminate].
      constructor; [exact (fms_defeq Hms Hctx Hx Hy Hxy) | exact (IH ys r1 r2 Hrx Hry H1 H2)].
Qed.

Lemma core_compare_args_cheap_first_sound env venv ps chk rec g L xs ys xs' ys' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  Forall2 (VTrExpr env venv ps L) xs xs' ->
  Forall2 (VTrExpr env venv ps L) ys ys' ->
  core_compare_args_cheap_first rec env g xs ys = Accept true ->
  Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) xs' ys'.
Proof.
  intros Hves Hms Hctx Hxs Hys Hc.
  unfold core_compare_args_cheap_first in Hc.
  destruct (core_compare_args_filtered true rec env g xs ys) as [ok|err|why] eqn:H1;
    simpl in Hc; try discriminate.
  destruct ok; [|discriminate].
  eapply core_compare_args_both_sound; eassumption.
Qed.

Lemma Forall2_rev_local {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> Forall2 R (rev xs) (rev ys).
Proof.
  induction 1; simpl; [constructor | apply Forall2_app; [exact IHForall2 | constructor; auto]].
Qed.

(* 6f. Speculative congruence (`core_congruent_apps`, `core_delta_congruent`) *)
Lemma core_congruent_apps_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_congruent_apps rec fuel g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hc.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_congruent_apps in Hc.
  destruct t as [| | | | |tf0 ta0| | | | | |]; try discriminate.
  destruct s as [| | | | |sf0 sa0| | | | | |]; try discriminate.
  pose proof (core_spine_core_apps (EApp tf0 ta0) []) as Hspt.
  pose proof (core_spine_core_apps (EApp sf0 sa0) []) as Hsps.
  destruct (core_spine (EApp tf0 ta0) []) as [tf ta] eqn:Et.
  destruct (core_spine (EApp sf0 sa0) []) as [sf sa] eqn:Es.
  simpl in Hspt, Hsps.
  destruct (core_same_head fuel tf sf) as [same|err|why] eqn:Hsh; simpl in Hc; try discriminate.
  destruct (same && Nat.eqb (List.length ta) (List.length sa)) eqn:Eok; [|discriminate].
  apply andb_true_iff in Eok as [-> _].
  rewrite <- Hspt in Ht. rewrite <- Hsps in Hs.
  destruct (VTrExpr_core_apps_inv Ht) as [tf' [ta' [Heq_t [Htf Hta]]]].
  destruct (VTrExpr_core_apps_inv Hs) as [sf' [sa' [Heq_s [Hsf Hsa]]]].
  pose proof (core_same_head_sound Hves HwfL (VTrExprS_to_VTrExpr Htf) (VTrExprS_to_VTrExpr Hsf) Hsh)
    as Hhead_eq.
  pose proof (core_compare_args_sound Hves Hms Hctx
                (Forall2_rev_local (Forall2_VTrExprS_to_VTrExpr Hta))
                (Forall2_rev_local (Forall2_VTrExprS_to_VTrExpr Hsa)) Hc) as Hrev_eq.
  apply Forall2_rev_local in Hrev_eq. rewrite !rev_involutive in Hrev_eq.
  destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_t) Hhead_eq Hrev_eq) as [_ Happs].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Happs | exact Heq_s].
Qed.

Lemma core_delta_congruent_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_delta_congruent rec fuel env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hdc.
  unfold core_delta_congruent in Hdc.
  destruct (core_delta_info env t) as [dt|]; [|discriminate].
  destruct (core_delta_info env s) as [ds|]; [|discriminate].
  destruct (effective_hints dt); try discriminate.
  destruct (effective_hints ds); try discriminate.
  destruct (N.eqb n n0 && negb (core_erasing_delta env t || core_erasing_delta env s));
    [eapply core_congruent_apps_sound; eassumption | discriminate].
Qed.

(* 6g. Opposite projection unfolding (`core_try_unfold_proj_app`, `core_opposite_projection`) *)
Lemma core_try_unfold_proj_app_sound env venv ps chk rec g L e e' e1 :
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  core_try_unfold_proj_app rec g e = Accept (Some e1) ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hms Hctx He Hu.
  unfold core_try_unfold_proj_app in Hu.
  destruct (fst (core_spine e [])); try discriminate.
  destruct (whnf_core_method rec false g e) as [red|err|why] eqn:Hw; simpl in Hu; try discriminate.
  destruct (expr_eqb red e); [discriminate |].
  inversion Hu; subst e1.
  exact (fms_whnf_core Hms Hctx He Hw).
Qed.

Lemma core_opposite_projection_sound env venv ps chk rec g L t s t' s' tn sn :
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_opposite_projection rec env g t s = Accept (Some (tn, sn)) ->
  VTrExpr env venv ps L tn t' /\ VTrExpr env venv ps L sn s'.
Proof.
  intros Hms Hctx Ht Hs Hop.
  unfold core_opposite_projection in Hop.
  destruct (core_delta_info env t); destruct (core_delta_info env s); try discriminate.
  - destruct (core_try_unfold_proj_app rec g s) as [[s1|]|err|why] eqn:Hu;
      simpl in Hop; try discriminate.
    inversion Hop; subst tn sn.
    split; [exact Ht | eapply core_try_unfold_proj_app_sound; eassumption].
  - destruct (core_try_unfold_proj_app rec g t) as [[t1|]|err|why] eqn:Hu;
      simpl in Hop; try discriminate.
    inversion Hop; subst tn sn.
    split; [eapply core_try_unfold_proj_app_sound; eassumption | exact Hs].
Qed.

(* 6h. Lazy delta loop (`core_lazy_delta`) *)
Lemma core_lazy_delta_sound rounds env venv ps chk rec fuel g L :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  forall t s t' s' prog,
    VTrExpr env venv ps L t t' ->
    VTrExpr env venv ps L s s' ->
    core_lazy_delta rounds rec fuel env ps g t s = Accept prog ->
    match prog with
    | ConversionDone true => VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'
    | ConversionDone false => True
    | ConversionStuck tn sn =>
        VTrExpr env venv ps L tn t' /\ VTrExpr env venv ps L sn s'
    end.
Proof.
  intros Hves Hms Hctx.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  induction rounds as [|rounds IH]; intros t s t' s' prog Ht Hs Hld;
    simpl in Hld; [discriminate |].
  destruct (core_quick rec fuel g t s) as [[ok|]|err|why] eqn:Hq; simpl in Hld; try discriminate.
  { inversion Hld; subst prog. destruct ok; [eapply core_quick_sound; eassumption | exact I]. }
  destruct (core_offset rec env g t s) as [[ok|]|err|why] eqn:Ho; simpl in Hld; try discriminate.
  { inversion Hld; subst prog. destruct ok; [eapply core_offset_sound; eassumption | exact I]. }
  set (elig := pair_probe_guard
        (nat_probe_head find_decl core_succ_name env (core_spine t []))
        (nat_probe_head find_decl core_succ_name env (core_spine s []))
        (fun _ => nat_probe_allowed (method_mode rec) t s)) in *.
  destruct (if elig then core_reduce_nat rec fuel env g t else Accept None)
    as [[tn|]|err|why] eqn:Hnt; simpl in Hld; try discriminate.
  { destruct elig; [|discriminate].
    destruct (defeq_method rec g tn s) as [ok|err|why] eqn:Hd; simpl in Hld; try discriminate.
    inversion Hld; subst prog. destruct ok; [|exact I].
    exact (fms_defeq Hms Hctx (core_reduce_nat_sound Hves Hms Hctx Ht Hnt) Hs Hd). }
  destruct (if elig then core_reduce_nat rec fuel env g s else Accept None)
    as [[sn|]|err|why] eqn:Hns; simpl in Hld; try discriminate.
  { destruct elig; [|discriminate].
    destruct (defeq_method rec g t sn) as [ok|err|why] eqn:Hd; simpl in Hld; try discriminate.
    inversion Hld; subst prog. destruct ok; [|exact I].
    exact (fms_defeq Hms Hctx Ht (core_reduce_nat_sound Hves Hms Hctx Hs Hns) Hd). }
  destruct (core_reduce_native t) as [[tn|]|err|why] eqn:Hntv; simpl in Hld; try discriminate.
  { exfalso. eapply core_reduce_native_sound; exact Hntv. }
  destruct (core_reduce_native s) as [[sn|]|err|why] eqn:Hnsv; simpl in Hld; try discriminate.
  { exfalso. eapply core_reduce_native_sound; exact Hnsv. }
  destruct (core_delta_congruent rec fuel env g t s) as [same|err|why] eqn:Hdc;
    simpl in Hld; try discriminate.
  destruct same.
  { inversion Hld; subst prog. eapply core_delta_congruent_sound; eassumption. }
  destruct (core_opposite_projection rec env g t s) as [[[tn sn]|]|err|why] eqn:Hop;
    simpl in Hld; try discriminate.
  { destruct (core_opposite_projection_sound Hms Hctx Ht Hs Hop) as [Htn Hsn].
    exact (IH tn sn t' s' prog Htn Hsn Hld). }
  destruct (core_delta_sides env t s) as [ul ur].
  destruct (if ul then core_unfold env ps t else Accept None) as [td|err|why] eqn:Htd;
    simpl in Hld; try discriminate.
  destruct (if ur then core_unfold env ps s else Accept None) as [sd|err|why] eqn:Hsd;
    simpl in Hld; try discriminate.
  assert (Htd_tr : forall e, td = Some e -> VTrExpr env venv ps L e t').
  { intros e He. subst td. destruct ul; [eapply core_unfold_sound; eassumption | discriminate]. }
  assert (Hsd_tr : forall e, sd = Some e -> VTrExpr env venv ps L e s').
  { intros e He. subst sd. destruct ur; [eapply core_unfold_sound; eassumption | discriminate]. }
  destruct td as [t1|]; destruct sd as [s1|]; simpl in Hld.
  - destruct (whnf_core_method rec true g t1) as [tn|err|why] eqn:Hwt; simpl in Hld; try discriminate.
    destruct (whnf_core_method rec true g s1) as [sn|err|why] eqn:Hws; simpl in Hld; try discriminate.
    exact (IH tn sn t' s' prog
             (fms_whnf_core Hms Hctx (Htd_tr _ eq_refl) Hwt)
             (fms_whnf_core Hms Hctx (Hsd_tr _ eq_refl) Hws) Hld).
  - destruct (whnf_core_method rec true g t1) as [tn|err|why] eqn:Hwt; simpl in Hld; try discriminate.
    exact (IH tn s t' s' prog (fms_whnf_core Hms Hctx (Htd_tr _ eq_refl) Hwt) Hs Hld).
  - destruct (whnf_core_method rec true g s1) as [sn|err|why] eqn:Hws; simpl in Hld; try discriminate.
    exact (IH t sn t' s' prog Ht (fms_whnf_core Hms Hctx (Hsd_tr _ eq_refl) Hws) Hld).
  - inversion Hld; subst prog. split; [exact Ht | exact Hs].
Qed.

(* 6i. Lazy delta projection loop (`core_lazy_delta_proj`) *)
Lemma core_lazy_delta_proj_sound rounds env venv ps chk rec fuel g L
    owner1 owner2 idx te' se' pv1 pv2 fty1 fty2 :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrProj env venv (List.length ps) (vl_ctx L) owner1 idx te' pv1 fty1 ->
  VTrProj env venv (List.length ps) (vl_ctx L) owner2 idx se' pv2 fty2 ->
  forall t s,
    VTrExpr env venv ps L t te' ->
    VTrExpr env venv ps L s se' ->
    core_lazy_delta_proj rounds rec fuel env ps g idx t s = Accept true ->
    VIsDefEqU venv (List.length ps) (vl_ctx L) pv1 pv2.
Proof.
  intros Hves Hms Hctx Hp1 Hp2.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  induction rounds as [|rounds IH]; intros t s Ht Hs Hlp; simpl in Hlp; [discriminate |].
  destruct (core_quick rec fuel g t s) as [[ok|]|err|why] eqn:Hq; simpl in Hlp; try discriminate.
  { destruct ok; [|discriminate].
    eapply VTrProj_congr; [exact Hves | exact HG | exact Hp1 | exact Hp2 |
      eapply core_quick_sound; eassumption]. }
  destruct (core_delta_congruent rec fuel env g t s) as [same|err|why] eqn:Hdc;
    simpl in Hlp; try discriminate.
  destruct same.
  { eapply VTrProj_congr; [exact Hves | exact HG | exact Hp1 | exact Hp2 |
      eapply core_delta_congruent_sound; eassumption]. }
  destruct (core_opposite_projection rec env g t s) as [[[tn sn]|]|err|why] eqn:Hop;
    simpl in Hlp; try discriminate.
  { destruct (core_opposite_projection_sound Hms Hctx Ht Hs Hop) as [Htn Hsn].
    exact (IH tn sn Htn Hsn Hlp). }
  destruct (core_delta_sides env t s) as [ul ur].
  destruct (if ul then core_unfold env ps t else Accept None) as [td|err|why] eqn:Htd;
    simpl in Hlp; try discriminate.
  destruct (if ur then core_unfold env ps s else Accept None) as [sd|err|why] eqn:Hsd;
    simpl in Hlp; try discriminate.
  assert (Htd_tr : forall e, td = Some e -> VTrExpr env venv ps L e te').
  { intros e He. subst td. destruct ul; [eapply core_unfold_sound; eassumption | discriminate]. }
  assert (Hsd_tr : forall e, sd = Some e -> VTrExpr env venv ps L e se').
  { intros e He. subst sd. destruct ur; [eapply core_unfold_sound; eassumption | discriminate]. }
  destruct td as [t1|]; destruct sd as [s1|]; simpl in Hlp.
  - destruct (whnf_core_method rec true g t1) as [tn|err|why] eqn:Hwt; simpl in Hlp; try discriminate.
    destruct (whnf_core_method rec true g s1) as [sn|err|why] eqn:Hws; simpl in Hlp; try discriminate.
    exact (IH tn sn
             (fms_whnf_core Hms Hctx (Htd_tr _ eq_refl) Hwt)
             (fms_whnf_core Hms Hctx (Hsd_tr _ eq_refl) Hws) Hlp).
  - destruct (whnf_core_method rec true g t1) as [tn|err|why] eqn:Hwt; simpl in Hlp; try discriminate.
    exact (IH tn s (fms_whnf_core Hms Hctx (Htd_tr _ eq_refl) Hwt) Hs Hlp).
  - destruct (whnf_core_method rec true g s1) as [sn|err|why] eqn:Hws; simpl in Hlp; try discriminate.
    exact (IH t sn Ht (fms_whnf_core Hms Hctx (Hsd_tr _ eq_refl) Hws) Hlp).
  - destruct (core_reduce_proj_core env idx t) as [tf|] eqn:Htf;
    destruct (core_reduce_proj_core env idx s) as [sf|] eqn:Hsf.
    + destruct (core_reduce_proj_core_sound Hves HwfL Ht Hp1 Htf) as [tf' [Htf_tr Hpv1_tf]].
      destruct (core_reduce_proj_core_sound Hves HwfL Hs Hp2 Hsf) as [sf' [Hsf_tr Hpv2_sf]].
      pose proof (fms_defeq Hms Hctx Htf_tr Hsf_tr Hlp) as Htf_sf.
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hpv1_tf |].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Htf_sf |
        apply VIsDefEqU_symm; exact Hpv2_sf].
    + eapply VTrProj_congr; [exact Hves | exact HG | exact Hp1 | exact Hp2 |
        exact (fms_defeq Hms Hctx Ht Hs Hlp)].
    + eapply VTrProj_congr; [exact Hves | exact HG | exact Hp1 | exact Hp2 |
        exact (fms_defeq Hms Hctx Ht Hs Hlp)].
    + eapply VTrProj_congr; [exact Hves | exact HG | exact Hp1 | exact Hp2 |
        exact (fms_defeq Hms Hctx Ht Hs Hlp)].
Qed.

(* 6j. Lambda eta (`eta_compare`, `core_eta_expand_pis`, `core_eta_expand`) *)
Lemma eta_compare_sound env venv ps chk rec g L nm bi dom body other t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L (ELam nm bi dom body) t' ->
  VTrExpr env venv ps L other s' ->
  eta_compare rec g dom body other = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Hlam Hoth Heta.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold eta_compare in Heta.
  destruct (infer_method rec g other) as [ty0|err|why] eqn:Hinf; simpl in Heta; try discriminate.
  destruct (whnf_method rec g ty0) as [ty|err|why] eqn:Hw; simpl in Heta; try discriminate.
  destruct ty as [| | | | | | |nm2 bi2 dom2 cod2| | | |]; try discriminate.
  destruct (defeq_method rec g dom dom2) as [ok1|err|why] eqn:Hdom_eq; simpl in Heta; try discriminate.
  destruct ok1; [|discriminate].
  destruct (VTrExpr_inv_lam Hlam) as [dom' [body' [Hdom_is [Hdom_tr [Hbody_tr Heq_lam]]]]].
  destruct (fms_infer_typed Hms Hctx Hoth Hinf) as [ty' [Hty0_tr Hs_ty]].
  pose proof (fms_whnf Hms Hctx Hty0_tr Hw) as Hty_tr.
  destruct (VTrExpr_inv_pi Hty_tr) as [dom2' [cod2' [Hdom2_is [Hcod2_is [Hdom2_tr [_ Hpi_eq]]]]]].
  pose proof (fms_defeq Hms Hctx Hdom_tr Hdom2_tr Hdom_eq) as [Td Hd12].
  destruct Hdom_is as [u1 Hu1]. destruct Hdom2_is as [u2 Hu2].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu1 Hd12) as [u_eq Hcu].
  assert (Hdom12 : VIsDefEq venv (List.length ps) (vl_ctx L) dom' dom2' (VSort u1))
    by (eapply VDF_defeqDF; [exact (VDF_symm Hcu) | exact Hd12]).
  destruct Hcod2_is as [v2 Hv2].
  assert (Hpi_conv : VIsDefEq venv (List.length ps) (vl_ctx L)
      (VForallE dom2' cod2') (VForallE dom' cod2') (VSort (VLIMax u1 v2)))
    by (eapply VDF_forallEDF; [exact (VDF_symm Hdom12) | exact Hv2]).
  assert (Hs_pi : VHasType venv (List.length ps) (vl_ctx L) s' (VForallE dom' cod2')).
  { eapply VDF_defeqDF; [exact Hpi_conv |].
    eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hs_ty |
      apply VIsDefEqU_symm; exact Hpi_eq]. }
  assert (Hctx_d : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
    by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exists u1; exact Hu1]).
  assert (HwfL_d : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
    by (exact (VTrCtx_to_VLCtxWF Hctx_d)).
  assert (Hlift_oth : VTrExpr env venv ps (vl_push_lam L dom') (lift 1 0 other) (vlift s'))
    by (exact (VTrExpr_lift_lam dom' Hcl Hoth)).
  assert (Hbv0 : VTrExpr env venv ps (vl_push_lam L dom') (EBVar 0) (VBVar 0)).
  { apply VTrExprS_to_VTrExpr.
    eapply VTrExprS_bvar; [unfold vl_bvar; simpl; reflexivity |].
    apply VDF_bvar. constructor. }
  assert (Hs_lift_ty : VHasType venv (List.length ps) (dom' :: vl_ctx L)
      (vlift s') (VForallE (vlift dom') (vliftN 1 1 cod2'))).
  { pose proof (VIsDefEq_weakN Hcl Hs_pi (VCtxLiftN_one dom' (vl_ctx L))) as Hw1.
    simpl in Hw1. exact Hw1. }
  assert (Hv0_ty : VHasType venv (List.length ps) (dom' :: vl_ctx L) (VBVar 0) (vlift dom'))
    by (apply VDF_bvar; constructor).
  assert (Happ_wf : VExprWF venv (List.length ps) (dom' :: vl_ctx L) (VApp (vlift s') (VBVar 0)))
    by (exists (vinst0 (vliftN 1 1 cod2') (VBVar 0)); eapply VDF_appDF; [exact Hs_lift_ty | exact Hv0_ty]).
  assert (Happ_tr : VTrExpr env venv ps (vl_push_lam L dom')
      (EApp (lift 1 0 other) (EBVar 0)) (VApp (vlift s') (VBVar 0))).
  { change (EApp (lift 1 0 other) (EBVar 0)) with (core_apps (lift 1 0 other) [EBVar 0]).
    change (VApp (vlift s') (VBVar 0)) with (vapps (vlift s') [VBVar 0]).
    eapply VTrExpr_core_apps; [exact Hves | exact HwfL_d | exact Hlift_oth |
      constructor; [exact Hbv0 | constructor] | exact Happ_wf]. }
  pose proof (fms_defeq Hms Hctx_d Hbody_tr Happ_tr Heta) as [Tb Hbd].
  assert (Hlam_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
      (VLam dom' body') (VLam dom' (VApp (vlift s') (VBVar 0)))).
  { exists (VForallE dom' Tb). eapply VDF_lamDF; [exact Hu1 | exact Hbd]. }
  assert (Heta_s : VIsDefEqU venv (List.length ps) (vl_ctx L)
      (VLam dom' (VApp (vlift s') (VBVar 0))) s').
  { exists (VForallE dom' cod2'). exact (VDF_eta Hs_pi). }
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_lam |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hlam_eq | exact Heta_s].
Qed.

Lemma core_eta_expand_pis_sound eta_fuel env venv ps chk rec :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  forall g L e ty args e' ty' args' res,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    VTrExpr env venv ps L ty ty' ->
    Forall2 (VTrExpr env venv ps L) args args' ->
    VHasType venv (List.length ps) (vl_ctx L) (vapps e' args') ty' ->
    core_eta_expand_pis eta_fuel rec g e ty args = Accept res ->
    VTrExpr env venv ps L res (vapps e' args').
Proof.
  intros Hves Hms.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  induction eta_fuel as [|eta_fuel IH];
    intros g L e ty args e' ty' args' res Hctx He Hty Hargs Htyp Hexp;
    simpl in Hexp; [discriminate |].
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  destruct ty as [| | | | | | |nm bi dom body| | | |];
    try (inversion Hexp; subst res;
         eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact He | exact Hargs |
           exists ty'; exact Htyp]).
  destruct (whnf_method rec (push_binding g dom None) body) as [body1|err|why] eqn:Hw;
    simpl in Hexp; try discriminate.
  destruct (core_eta_expand_pis eta_fuel rec (push_binding g dom None)
              (lift 1 0 e) body1 (map (lift 1 0) args ++ [EBVar 0]))
    as [rest|err|why] eqn:Hrest; simpl in Hexp; try discriminate.
  inversion Hexp; subst res; clear Hexp.
  destruct (VTrExpr_inv_pi Hty) as [dom' [body' [Hdom_is [Hbody_is [Hdom_tr [Hbody_tr Hpi_eq]]]]]].
  assert (Hctx_d : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
    by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exact Hdom_is]).
  assert (HwfL_d : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
    by (exact (VTrCtx_to_VLCtxWF Hctx_d)).
  pose proof (fms_whnf Hms Hctx_d Hbody_tr Hw) as Hbody1_tr.
  assert (Hargs_lift : Forall2 (VTrExpr env venv ps (vl_push_lam L dom'))
      (map (lift 1 0) args ++ [EBVar 0]) (map vlift args' ++ [VBVar 0])).
  { apply Forall2_app.
    - clear -Hcl Hargs. induction Hargs as [|a a' r r' Ha Hr IHr]; simpl; constructor;
        [exact (VTrExpr_lift_lam dom' Hcl Ha) | exact IHr].
    - constructor; [|constructor]. apply VTrExprS_to_VTrExpr.
      eapply VTrExprS_bvar; [unfold vl_bvar; simpl; reflexivity | apply VDF_bvar; constructor]. }
  assert (Htyp_pi : VHasType venv (List.length ps) (vl_ctx L) (vapps e' args') (VForallE dom' body'))
    by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Htyp |
          apply VIsDefEqU_symm; exact Hpi_eq]).
  assert (Hlift_app : vapps (vlift e') (map vlift args' ++ [VBVar 0]) =
                      VApp (vlift (vapps e' args')) (VBVar 0)).
  { rewrite vapps_app. simpl. unfold vlift. rewrite vliftN_vapps. reflexivity. }
  assert (Htyp_lift : VHasType venv (List.length ps) (dom' :: vl_ctx L)
      (vapps (vlift e') (map vlift args' ++ [VBVar 0])) body').
  { rewrite Hlift_app.
    pose proof (VIsDefEq_weakN Hcl Htyp_pi (VCtxLiftN_one dom' (vl_ctx L))) as Hw1.
    simpl in Hw1.
    assert (Hv0 : VHasType venv (List.length ps) (dom' :: vl_ctx L) (VBVar 0) (vlift dom'))
      by (apply VDF_bvar; constructor).
    pose proof (VDF_appDF Hw1 Hv0) as Happ.
    unfold vinst0 in Happ. rewrite vinst_vliftN_bvar0 in Happ. exact Happ. }
  pose proof (IH _ _ _ _ _ _ _ _ _ Hctx_d (VTrExpr_lift_lam dom' Hcl He) Hbody1_tr Hargs_lift
                Htyp_lift Hrest) as Hrest_tr.
  rewrite Hlift_app in Hrest_tr.
  destruct Hdom_tr as [d0 [Hd0 [Td Hdeq]]].
  destruct Hdom_is as [u Hu].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_r Hdeq)) as [ud Hcd].
  assert (Hd_s : VIsDefEq venv (List.length ps) (vl_ctx L) d0 dom' (VSort u))
    by (eapply VDF_defeqDF; [exact (VDF_symm Hcd) | exact Hdeq]).
  assert (HwfL_d0 : VLCtxWF venv (List.length ps) (vl_push_lam L d0))
    by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact (VIsDefEq_refl_l Hd_s)]).
  pose proof (VTrExpr_defeq_ctx Hves HwfL_d HwfL_d0
                (VLCtxDefEq_push_lam Hwf HwfL (VDF_symm Hd_s)) Hrest_tr)
    as [r0 [Hr0 [Tr Hreq]]].
  exists (VLam d0 r0). split.
  - eapply VTrExprS_lam; [exists u; exact (VIsDefEq_refl_l Hd_s) | exact Hd0 | exact Hr0].
  - assert (Hlam_eq : VIsDefEq venv (List.length ps) (vl_ctx L)
        (VLam d0 r0) (VLam dom' (VApp (vlift (vapps e' args')) (VBVar 0))) (VForallE d0 Tr))
      by (eapply VDF_lamDF; [exact Hd_s | exact Hreq]).
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists (VForallE d0 Tr); exact Hlam_eq |
      exists (VForallE dom' body'); exact (VDF_eta Htyp_pi)].
Qed.

Lemma core_eta_expand_sound eta_fuel env venv ps chk rec :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  forall e g L e' res,
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L e e' ->
    core_eta_expand eta_fuel rec g e = Accept res ->
    VTrExpr env venv ps L res e'.
Proof.
  intros Hves Hms.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  induction e as [| | | | | |nm bi dom _ body IH| | | | |];
    intros g L e' res Hctx He Hexp; simpl in Hexp;
    pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL;
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  1-6, 8-12:
    destruct (infer_type_method rec g _) as [ty0|err|why] eqn:Hinf; simpl in Hexp; try discriminate;
    destruct (whnf_method rec g ty0) as [ty|err|why] eqn:Hw; simpl in Hexp; try discriminate;
    destruct ty as [| | | | | | |nm2 bi2 dom2 cod2| | | |];
      try (inversion Hexp; subst res; exact He);
    destruct (fms_infer_type Hms Hctx He Hinf) as [ty' [Hty0_tr He_ty]];
    pose proof (fms_whnf Hms Hctx Hty0_tr Hw) as Hty_tr;
    exact (core_eta_expand_pis_sound Hves Hms Hctx He Hty_tr (Forall2_nil _) He_ty Hexp).
  - (* ELam *)
    destruct (core_eta_expand eta_fuel rec (push_binding g dom None) body) as [b1|err|why] eqn:Hb1;
      simpl in Hexp; try discriminate.
    inversion Hexp; subst res; clear Hexp.
    destruct (VTrExpr_inv_lam He) as [dom' [body' [Hdom_is [Hdom_tr [Hbody_tr Heq_lam]]]]].
    assert (Hctx_d : VTrCtx env venv ps (push_binding g dom None) (vl_push_lam L dom'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Hdom_tr | exact Hdom_is]).
    assert (HwfL_d : VLCtxWF venv (List.length ps) (vl_push_lam L dom'))
      by (exact (VTrCtx_to_VLCtxWF Hctx_d)).
    pose proof (IH _ _ _ _ Hctx_d Hbody_tr Hb1) as Hb1_tr.
    destruct Hdom_tr as [d0 [Hd0 [Td Hdeq]]].
    destruct Hdom_is as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_r Hdeq)) as [ud Hcd].
    assert (Hd_s : VIsDefEq venv (List.length ps) (vl_ctx L) d0 dom' (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcd) | exact Hdeq]).
    assert (HwfL_d0 : VLCtxWF venv (List.length ps) (vl_push_lam L d0))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact (VIsDefEq_refl_l Hd_s)]).
    pose proof (VTrExpr_defeq_ctx Hves HwfL_d HwfL_d0
                  (VLCtxDefEq_push_lam Hwf HwfL (VDF_symm Hd_s)) Hb1_tr)
      as [r0 [Hr0 [Tr Hreq]]].
    exists (VLam d0 r0). split.
    + eapply VTrExprS_lam; [exists u; exact (VIsDefEq_refl_l Hd_s) | exact Hd0 | exact Hr0].
    + eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        exists (VForallE d0 Tr); eapply VDF_lamDF; [exact Hd_s | exact Hreq] | exact Heq_lam].
Qed.

(* 6k. Head comparison (`compare_heads`) *)
Lemma compare_heads_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  compare_heads rec fuel env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hch.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold compare_heads in Hch.
  destruct t as [i|n| | |n us|tf0 ta0|nm1 bi1 d1 b1| | | |own1 i1 a1|];
  destruct s as [j|m| | |m vs|sf0 sa0|nm2 bi2 d2 b2| | | |own2 j1 b1'|];
    try discriminate;
    try (eapply eta_compare_sound; eassumption);
    try (apply VIsDefEqU_symm; eapply eta_compare_sound; eassumption).
  - (* EBVar *)
    inversion Hch as [Hij]. apply Nat.eqb_eq in Hij. subst j.
    eapply VTrExpr_uniq; eassumption.
  - (* EFVar *)
    inversion Hch as [Hnm]. apply name_eqb_eq in Hnm. subst m.
    eapply VTrExpr_uniq; eassumption.
  - (* EConst *)
    destruct (name_eqb n m) eqn:Enm; [|discriminate].
    apply name_eqb_eq in Enm. subst m.
    destruct (VTrExpr_inv_const Ht) as [ci1 [us' [Hci1 [Hus' [Hw_us [Hlu Heq_t]]]]]].
    destruct (VTrExpr_inv_const Hs) as [ci2 [vs' [Hci2 [Hvs' [Hw_vs [Hlv Heq_s]]]]]].
    rewrite Hci1 in Hci2. inversion Hci2; subst ci2; clear Hci2.
    pose proof (levels_equiv_sound_TrLevels fuel Hus' Hvs' Hch) as Huv.
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists (vinstL us' (vc_type ci1));
      eapply VDF_constDF; [exact Hci1 | exact Hw_us | exact Hw_vs |
        rewrite <- (TrLevels_length Hus'); exact Hlu | exact Huv] | exact Heq_s].
  - (* EApp *)
    pose proof (core_spine_core_apps (EApp tf0 ta0) []) as Hspt.
    pose proof (core_spine_core_apps (EApp sf0 sa0) []) as Hsps.
    destruct (core_spine (EApp tf0 ta0) []) as [tf ta] eqn:Et.
    destruct (core_spine (EApp sf0 sa0) []) as [sf sa] eqn:Es.
    simpl in Hspt, Hsps.
    destruct (Nat.eqb (List.length ta) (List.length sa)) eqn:Elen; [|discriminate].
    destruct (defeq_method rec g tf sf) as [ok|err|why] eqn:Hhead; simpl in Hch; try discriminate.
    destruct ok; [|discriminate].
    rewrite <- Hspt in Ht. rewrite <- Hsps in Hs.
    destruct (VTrExpr_core_apps_inv Ht) as [tf' [ta' [Heq_t [Htf Hta]]]].
    destruct (VTrExpr_core_apps_inv Hs) as [sf' [sa' [Heq_s [Hsf Hsa]]]].
    pose proof (fms_defeq Hms Hctx (VTrExprS_to_VTrExpr Htf) (VTrExprS_to_VTrExpr Hsf) Hhead)
      as Hhead_eq.
    pose proof (core_compare_args_cheap_first_sound Hves Hms Hctx
                  (Forall2_VTrExprS_to_VTrExpr Hta) (Forall2_VTrExprS_to_VTrExpr Hsa) Hch)
      as Hargs_eq.
    destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_t) Hhead_eq Hargs_eq) as [_ Happs].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Happs | exact Heq_s].
  - (* EProj *)
    destruct (Nat.eqb i1 j1) eqn:Eij; [|discriminate].
    apply Nat.eqb_eq in Eij. subst j1.
    destruct (VTrExpr_inv_proj Ht) as [a1' [pv1 [fty1 [Ha1_tr [Hp1 Heq_t]]]]].
    destruct (VTrExpr_inv_proj Hs) as [b1'' [pv2 [fty2 [Hb1_tr [Hp2 Heq_s]]]]].
    pose proof (fms_defeq Hms Hctx Ha1_tr Hb1_tr Hch) as Hab.
    pose proof (VTrProj_congr Hves HG Hp1 Hp2 Hab) as Hpv.
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hpv | exact Heq_s].
Qed.

(* 6l. Structure eta & unit-like eta (`core_compare_fields`, `core_structure_eta`, `core_unit_like`) *)
Lemma core_compare_fields_sound env venv ps chk rec g L owner us' params' val v' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L val v' ->
  forall fields fields' start,
    (forall i, start <= i -> i < start + List.length fields ->
      exists fty, VTrProj env venv (List.length ps) (vl_ctx L) owner i v'
                    (vproj_expr owner i us' params' v') fty) ->
    Forall2 (VTrExpr env venv ps L) fields fields' ->
    core_compare_fields rec g owner val start fields = Accept true ->
    Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L))
      (map (fun i => vproj_expr owner i us' params' v') (seq start (List.length fields)))
      fields'.
Proof.
  intros Hves Hms Hctx Hv.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  induction fields as [|f rest IH]; intros fields' start Hprojs Hfs Hcf;
    inversion Hfs as [| ? f' ? rest' Hf Hrest]; subst; simpl in *.
  - constructor.
  - destruct (defeq_method rec g (EProj owner start val) f) as [ok|err|why] eqn:Hpf;
      simpl in Hcf; try discriminate.
    destruct ok; [|discriminate].
    destruct (Hprojs start ltac:(lia) ltac:(lia)) as [fty Hp].
    assert (Hp_tr : VTrExpr env venv ps L (EProj owner start val)
                      (vproj_expr owner start us' params' v')).
    { destruct Hv as [v0 [Hv0 [Tv Hveq]]].
      inversion Hp as [info0 ctor0 c0 d0 us0 ps0 idxs0 Hi0 Hc0 Hd0 Hk0 Hlt0 Hlp0 Hli0 Hw0 Hlu0 Hst0 Hpv0 Hty0].
      inversion Hpv0 as [Hpf_eq].
      assert (Hty0' : VHasType venv (List.length ps) (vl_ctx L)
          (VApp (vapps (VConst (proj_const_name owner start) us0) ps0) v') fty)
        by (rewrite <- Hpf_eq; exact Hty0).
      assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L)
          (vproj_expr owner start us0 ps0 v0) (vproj_expr owner start us0 ps0 v')).
      { unfold vproj_expr in *.
        destruct (VHasType_app_inv Hwf HG Hty0') as [Ap [Bp [Hpf_a Hpe_a]]].
        destruct (VIsDefEq_uniq_same Hwf Hinj HG Hpe_a (VIsDefEq_refl_r Hveq)) as [up Hcp].
        exists (vinst0 Bp v0).
        eapply VDF_appDF; [exact Hpf_a | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Hveq]]. }
      destruct Hpv_eq as [Tpv Hpv_eq'].
      exists (vproj_expr owner start us0 ps0 v0). split.
      - eapply VTrExprS_proj; [exact Hv0 |].
        eapply VTrProj_intro; try eassumption; [| reflexivity | exact (VIsDefEq_refl_l Hpv_eq')].
        eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hst0 |
          apply VIsDefEqU_symm; exists Tv; exact Hveq].
      - unfold vproj_expr in *. rewrite Hpf_eq. exists Tpv. exact Hpv_eq'. }
    constructor; [exact (fms_defeq Hms Hctx Hp_tr Hf Hpf) |].
    apply IH; [intros i Hi1 Hi2; apply Hprojs; lia | exact Hrest | exact Hcf].
Qed.

Lemma core_structure_eta_sound env venv ps chk rec g L val constructed v' c' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L val v' ->
  VTrExpr env venv ps L constructed c' ->
  core_structure_eta rec env g val constructed = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) v' c'.
Proof.
  intros Hves Hms Hctx Hv Hc Hse.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_structure_eta in Hse.
  pose proof (core_spine_core_apps constructed []) as Hsp.
  destruct (core_spine constructed []) as [head args] eqn:Esp. simpl in Hsp.
  destruct head as [| | | |ctor us| | | | | | |]; try discriminate.
  destruct (core_constructor env ctor) as [c|] eqn:Hctor; [|discriminate].
  destruct (core_structure env (ctor_induct c) &&
            Nat.eqb (List.length args) (ctor_num_params c + ctor_num_fields c)) eqn:Echk;
    [|discriminate].
  apply andb_true_iff in Echk as [Hstruct Hlen_args].
  apply Nat.eqb_eq in Hlen_args.
  destruct (infer_method rec g val) as [vt|err|why] eqn:Hivt; simpl in Hse; try discriminate.
  destruct (infer_method rec g constructed) as [ct|err|why] eqn:Hict; simpl in Hse; try discriminate.
  destruct (defeq_method rec g vt ct) as [ok|err|why] eqn:Hvt_ct; simpl in Hse; try discriminate.
  destruct ok; [|discriminate].
  destruct (fms_infer_typed Hms Hctx Hv Hivt) as [vt' [Hvt_tr Hv_vt]].
  destruct (fms_infer_typed Hms Hctx Hc Hict) as [ct' [Hct_tr Hc_ct]].
  pose proof (fms_defeq Hms Hctx Hvt_tr Hct_tr Hvt_ct) as Hvt_ct'.
  rewrite <- Hsp in Hc.
  destruct (VTrExpr_core_apps_inv Hc) as [h' [args' [Heq_c [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? cic ? us' Hcic Hus' Hlen_us | | | | | | | |]; subst.
  assert (Hlen_args' : List.length args' = ctor_num_params c + ctor_num_fields c)
    by (rewrite <- (Forall2_length Htr_args); exact Hlen_args).
  assert (Hc_apps_ty : VHasType venv (List.length ps) (vl_ctx L) (vapps (VConst ctor us') args') ct')
    by (eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact Hc_ct |
          apply VIsDefEqU_symm; exact Heq_c]).
  destruct (ves_ctor_type_head Hves HG Hctor Hlen_args' Hc_apps_ty)
    as [info [idxs [Hi [Hcnp [Hli Hct_head]]]]].
  pose proof Hstruct as Hstruct_orig.
  unfold core_structure in Hstruct. rewrite Hi in Hstruct.
  apply andb_true_iff in Hstruct as [Hs1 Hctors_len].
  apply andb_true_iff in Hs1 as [_ Hidx0].
  apply Nat.eqb_eq in Hidx0.
  destruct idxs; simpl in Hli; try lia. rewrite app_nil_r in Hct_head.
  assert (Hctors : ind_ctors info = [ctor]).
  { unfold core_inductive in Hi.
    destruct (find_decl (ctor_induct c) env) as [d_ind|] eqn:Hfi; [|discriminate].
    destruct (decl_kind_of d_ind) eqn:Hki; try discriminate.
    inversion Hi; subst i; clear Hi.
    unfold core_constructor in Hctor.
    destruct (find_decl ctor env) as [d_c|] eqn:Hfc; [|discriminate].
    destruct (decl_kind_of d_c) eqn:Hkc; try discriminate.
    inversion Hctor; subst c0; clear Hctor.
    destruct (ves_ind_shape Hves Hfi Hki Hfc Hkc) as [[_ Hin] _].
    specialize (Hin eq_refl).
    destruct (ind_ctors info) as [|c1 [|c2 rest]]; simpl in Hctors_len, Hin; try discriminate.
    destruct Hin as [-> | []]; reflexivity. }
  unfold core_constructor in Hctor.
  destruct (find_decl ctor env) as [d_ctor|] eqn:Hfind_ctor; [|discriminate].
  destruct (decl_kind_of d_ctor) eqn:Hk_ctor; try discriminate.
  inversion Hctor; subst c0; clear Hctor.
  pose proof (ves_constants Hves Hfind_ctor) as Hdc.
  rewrite Hk_ctor in Hdc. destruct Hdc as [ci2 [Hci2 [Huv2 _]]].
  rewrite Hcic in Hci2. inversion Hci2; subst ci2; clear Hci2.
  assert (Hv_head : VHasType venv (List.length ps) (vl_ctx L) v'
      (vapps (VConst (ctor_induct c) us') (firstn (ctor_num_params c) args'))).
  { eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hv_vt |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hvt_ct' | exact Hct_head]. }
  assert (Hlen_p : List.length (firstn (ctor_num_params c) args') = ind_num_params info)
    by (rewrite length_firstn; lia).
  assert (Hwf_us' : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus').
  assert (Hlen_us' : List.length us' = List.length (decl_params d_ctor))
    by (rewrite <- (TrLevels_length Hus'); lia).
  destruct (ves_struct_eta Hves HG Hstruct_orig Hi Hctors Hfind_ctor Hk_ctor
              Hlen_p Hcnp Hwf_us' Hlen_us' Hv_head) as [Hprojs Heta].
  pose proof (core_compare_fields_sound Hves Hms Hctx Hv
                (fields := skipn (ctor_num_params c) args)
                (fields' := skipn (ctor_num_params c) args')
                (start := 0)
                (ltac:(intros i _ Hi2; apply Hprojs; rewrite length_skipn in Hi2; lia))
                (Forall2_skipn (Forall2_VTrExprS_to_VTrExpr Htr_args) (ctor_num_params c))
                Hse) as Hfields_eq.
  rewrite length_skipn, Hlen_args in Hfields_eq.
  replace (ctor_num_params c + ctor_num_fields c - ctor_num_params c)
    with (ctor_num_fields c) in Hfields_eq by lia.
  assert (Hp_refl : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L))
      (firstn (ctor_num_params c) args') (firstn (ctor_num_params c) args')).
  { apply Forall2_firstn.
    clear -Htr_args. induction Htr_args as [|x y r1 r2 Hxy Hr IH]; constructor;
      [destruct (VTrExprS_has_type Hxy) as [T HT]; exists T; exact HT | exact IH]. }
  assert (Hall_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L))
      (firstn (ctor_num_params c) args' ++
       map (fun i => vproj_expr (ctor_induct c) i us' (firstn (ctor_num_params c) args') v')
           (seq 0 (ctor_num_fields c)))
      args').
  { pose proof (Forall2_app Hp_refl Hfields_eq) as Happ.
    rewrite firstn_skipn in Happ. exact Happ. }
  assert (Hh_refl : VIsDefEqU venv (List.length ps) (vl_ctx L) (VConst ctor us') (VConst ctor us'))
    by (destruct (VTrExprS_has_type Htr_h) as [T HT]; exists T; exact HT).
  assert (Hwf_eta : VExprWF venv (List.length ps) (vl_ctx L)
      (vapps (VConst ctor us')
         (firstn (ctor_num_params c) args' ++
          map (fun i => vproj_expr (ctor_induct c) i us' (firstn (ctor_num_params c) args') v')
              (seq 0 (ctor_num_fields c)))))
    by (exists (vapps (VConst (ctor_induct c) us') (firstn (ctor_num_params c) args'));
        exact (VIsDefEq_refl_r Heta)).
  destruct (vapps_defeq_congr_l Hwf Hinj HG Hwf_eta Hh_refl Hall_eq) as [_ Hcongr].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
    exists (vapps (VConst (ctor_induct c) us') (firstn (ctor_num_params c) args')); exact Heta |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hcongr | exact Heq_c].
Qed.

Lemma core_unit_like_sound env venv ps chk rec g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_unit_like rec env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hul.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_unit_like in Hul.
  destruct (infer_method rec g t) as [ty0|err|why] eqn:Hit; simpl in Hul; try discriminate.
  destruct (whnf_method rec g ty0) as [ty|err|why] eqn:Hwt; simpl in Hul; try discriminate.
  pose proof (core_spine_core_apps ty []) as Hsp.
  destruct (core_spine ty []) as [head args] eqn:Esp. simpl in Hsp, Hul.
  destruct head as [| | | |owner us| | | | | | |]; try discriminate.
  destruct (core_structure env owner) eqn:Hstruct; [|discriminate].
  destruct (core_inductive env owner) as [info|] eqn:Hi; [|discriminate].
  destruct (ind_ctors info) as [|ctor [|? ?]] eqn:Hctors; try discriminate.
  destruct (core_constructor env ctor) as [c|] eqn:Hctor; [|discriminate].
  destruct (Nat.eqb (ctor_num_fields c) 0) eqn:Hnf0; [|discriminate].
  apply Nat.eqb_eq in Hnf0.
  destruct (infer_method rec g s) as [sty|err|why] eqn:His; simpl in Hul; try discriminate.
  destruct (fms_infer_typed Hms Hctx Ht Hit) as [ty' [Hty0_tr Ht_ty]].
  pose proof (fms_whnf Hms Hctx Hty0_tr Hwt) as Hty_tr.
  destruct (fms_infer_typed Hms Hctx Hs His) as [sty' [Hsty_tr Hs_sty]].
  pose proof (fms_defeq Hms Hctx Hty_tr Hsty_tr Hul) as Hty_sty.
  rewrite <- Hsp in Hty_tr.
  destruct (VTrExpr_core_apps_inv Hty_tr) as [h' [args' [Heq_ty [Htr_h Htr_args]]]].
  inversion Htr_h as [| | | ? ? ci_ind ? us' Hci_ind Hus' Hlen_us | | | | | | | |]; subst.
  assert (Ht_v : VHasType venv (List.length ps) (vl_ctx L) t' (vapps (VConst owner us') args'))
    by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Ht_ty |
          apply VIsDefEqU_symm; exact Heq_ty]).
  assert (Hs_v : VHasType venv (List.length ps) (vl_ctx L) s' (vapps (VConst owner us') args')).
  { eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hs_sty |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      apply VIsDefEqU_symm; exact Hty_sty | apply VIsDefEqU_symm; exact Heq_ty]. }
  pose proof Hstruct as Hstruct_orig.
  unfold core_structure in Hstruct. rewrite Hi in Hstruct.
  apply andb_true_iff in Hstruct as [Hs1 _].
  apply andb_true_iff in Hs1 as [_ Hidx0]. apply Nat.eqb_eq in Hidx0.
  destruct (VIsDefEq_isType Hwf HG Ht_v) as [usort Husort].
  pose proof (ves_ind_type_arity Hves HG Hi Husort) as Hlen_args'.
  rewrite Hidx0, Nat.add_0_r in Hlen_args'.
  unfold core_inductive in Hi.
  destruct (find_decl owner env) as [d_ind|] eqn:Hfind_ind; [|discriminate].
  destruct (decl_kind_of d_ind) eqn:Hk_ind; try discriminate.
  inversion Hi; subst i; clear Hi.
  assert (Hi' : core_inductive env owner = Some info)
    by (unfold core_inductive; rewrite Hfind_ind, Hk_ind; reflexivity).
  unfold core_constructor in Hctor.
  destruct (find_decl ctor env) as [d_ctor|] eqn:Hfind_ctor; [|discriminate].
  destruct (decl_kind_of d_ctor) eqn:Hk_ctor; try discriminate.
  inversion Hctor; subst c0; clear Hctor.
  destruct (ves_ind_shape Hves Hfind_ind Hk_ind Hfind_ctor Hk_ctor) as [_ Hsh].
  rewrite Hctors in Hsh. destruct (Hsh (or_introl eq_refl)) as [Hcnp Hclen_p].
  pose proof (ves_constants Hves Hfind_ind) as Hdc_ind.
  rewrite Hk_ind in Hdc_ind. destruct Hdc_ind as [ci2 [Hci2 [Huv2 _]]].
  rewrite Hci_ind in Hci2. inversion Hci2; subst ci2; clear Hci2.
  assert (Hwf_us' : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus').
  assert (Hlen_us' : List.length us' = List.length (decl_params d_ctor))
    by (rewrite <- (TrLevels_length Hus'); lia).
  destruct (ves_struct_eta Hves HG Hstruct_orig Hi' Hctors Hfind_ctor Hk_ctor
              Hlen_args' Hcnp Hwf_us' Hlen_us' Ht_v) as [_ Heta_t].
  destruct (ves_struct_eta Hves HG Hstruct_orig Hi' Hctors Hfind_ctor Hk_ctor
              Hlen_args' Hcnp Hwf_us' Hlen_us' Hs_v) as [_ Heta_s].
  rewrite Hnf0 in Heta_t, Heta_s. simpl in Heta_t, Heta_s. rewrite app_nil_r in Heta_t, Heta_s.
  exists (vapps (VConst owner us') args').
  exact (VDF_trans Heta_t (VDF_symm Heta_s)).
Qed.

(* 6m. String literal expansion (`core_try_string_expansion`) *)
Lemma core_try_string_expansion_sound env venv ps chk rec g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_try_string_expansion rec g t s = Accept (Some true) ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hst.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  unfold core_try_string_expansion in Hst. cbv zeta beta in Hst.
  destruct t as [| | | | |f1 a1| | | |l1| |]; try discriminate.
  - destruct f1 as [| | | |cn us| | | | | | |]; try discriminate.
    destruct us; try discriminate.
    destruct s as [| | | | | | | | |l2| |]; try discriminate.
    destruct l2 as [|text]; [discriminate |].
    destruct (name_eqb cn core_string_of_list); [|discriminate].
    destruct (core_expand_string text) as [exp|err|why] eqn:Hexp; simpl in Hst; try discriminate.
    destruct (defeq_method rec g exp (EApp (EConst cn []) a1)) as [ok|err|why] eqn:Hd;
      simpl in Hst; try discriminate.
    destruct ok; [|discriminate].
    destruct (VTrExpr_inv_strlit Hs) as [sv [Hstr [Htrs [_ Heq_s]]]].
    assert (Hexp_tr : VTrExpr env venv ps L exp s')
      by (exists sv; split; [eapply VTrExprS_core_expand_string; eassumption | exact Heq_s]).
    apply VIsDefEqU_symm. exact (fms_defeq Hms Hctx Hexp_tr Ht Hd).
  - destruct l1 as [|text]; [discriminate |].
    destruct s as [| | | | |f2 a2| | | | | |]; try discriminate.
    destruct f2 as [| | | |cn us| | | | | | |]; try discriminate.
    destruct us; try discriminate.
    destruct (name_eqb cn core_string_of_list); [|discriminate].
    destruct (core_expand_string text) as [exp|err|why] eqn:Hexp; simpl in Hst; try discriminate.
    destruct (defeq_method rec g exp (EApp (EConst cn []) a2)) as [ok|err|why] eqn:Hd;
      simpl in Hst; try discriminate.
    destruct ok; [|discriminate].
    destruct (VTrExpr_inv_strlit Ht) as [sv [Hstr [Htrs [_ Heq_t]]]].
    assert (Hexp_tr : VTrExpr env venv ps L exp t')
      by (exists sv; split; [eapply VTrExprS_core_expand_string; eassumption | exact Heq_t]).
    exact (fms_defeq Hms Hctx Hexp_tr Hs Hd).
Qed.

(* 6n. Fallback, post-WHNF comparison, finish conversion, and `defeq_step` *)
Lemma core_compare_fallback_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_compare_fallback rec fuel env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hfb.
  unfold core_compare_fallback in Hfb.
  destruct (compare_heads rec fuel env g t s) as [ok1|err|why] eqn:H1; simpl in Hfb; try discriminate.
  destruct ok1; [eapply compare_heads_sound; eassumption |].
  destruct (core_structure_eta rec env g t s) as [ok2|err|why] eqn:H2; simpl in Hfb; try discriminate.
  destruct ok2; [eapply core_structure_eta_sound; eassumption |].
  destruct (core_structure_eta rec env g s t) as [ok3|err|why] eqn:H3; simpl in Hfb; try discriminate.
  destruct ok3; [apply VIsDefEqU_symm; eapply core_structure_eta_sound; eassumption |].
  destruct (core_try_string_expansion rec g t s) as [[ok4|]|err|why] eqn:H4;
    simpl in Hfb; try discriminate.
  - inversion Hfb; subst ok4. eapply core_try_string_expansion_sound; eassumption.
  - eapply core_unit_like_sound; eassumption.
Qed.

Lemma compare_after_whnf_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  compare_after_whnf rec fuel env g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hc.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold compare_after_whnf in Hc.
  destruct (core_alpha_eq t s) eqn:Hal;
    [eapply VTrExpr_core_alpha_eq_local; eassumption |].
  assert (Hpi_fb :
    (tt0 <- infer_method rec g t;;
     sort <- sort_of rec g tt0;;
     is_prop <- level_equiv fuel sort LZero;;
     if is_prop then st <- infer_method rec g s;; defeq_method rec g tt0 st
     else core_compare_fallback rec fuel env g t s) = Accept true ->
    VIsDefEqU venv (List.length ps) (vl_ctx L) t' s').
  { intros Hrest.
    destruct (infer_method rec g t) as [ty|err|why] eqn:Hit; simpl in Hrest; try discriminate.
    destruct (sort_of rec g ty) as [su|err|why] eqn:Hsu; simpl in Hrest; try discriminate.
    destruct (level_equiv fuel su LZero) as [is_p|err|why] eqn:Hp; simpl in Hrest; try discriminate.
    destruct is_p.
    - destruct (infer_method rec g s) as [sty|err|why] eqn:His; simpl in Hrest; try discriminate.
      destruct (fms_infer_typed Hms Hctx Ht Hit) as [ty' [Hty_tr Ht_ty]].
      destruct (sort_of_sound_typed Hves Hms Hctx Hty_tr Hsu) as [su' [Hsu' [Hsu_wf Hty_su]]].
      assert (Hty_prop : VHasType venv (List.length ps) (vl_ctx L) ty' (VSort VLZero)).
      { eapply VDF_defeqDF;
          [eapply VDF_sortDF; [exact Hsu_wf | exact I |
             eapply level_equiv_sound_vlevel with (v := LZero); [exact Hsu' | reflexivity | exact Hp]]
          | exact Hty_su]. }
      destruct (fms_infer_typed Hms Hctx Hs His) as [sty' [Hsty_tr Hs_sty]].
      pose proof (fms_defeq Hms Hctx Hty_tr Hsty_tr Hrest) as Hty_sty.
      assert (Hs_ty : VHasType venv (List.length ps) (vl_ctx L) s' ty')
        by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact Hs_sty |
              apply VIsDefEqU_symm; exact Hty_sty]).
      exists ty'. eapply VDF_proofIrrel; [exact Hty_prop | exact Ht_ty | exact Hs_ty].
    - eapply core_compare_fallback_sound; eassumption. }
  destruct t as [| | |u| | |nm1 bi1 a b|nm1 bi1 a b| |l1| |];
    try exact (Hpi_fb Hc).
  - (* ESort *)
    destruct s as [| | |v| | | | | | | |]; try exact (Hpi_fb Hc).
    destruct (VTrExpr_inv_sort Ht) as [u' [Hu [Hu_wf Heq_t]]].
    destruct (VTrExpr_inv_sort Hs) as [v' [Hv [Hv_wf Heq_s]]].
    assert (Huv : vlevel_equiv u' v') by (eapply level_equiv_sound_vlevel; eassumption).
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists (VSort (VLSucc u')); eapply VDF_sortDF; eassumption | exact Heq_s].
  - (* ELam *)
    destruct s as [| | | | | |nm2 bi2 c d| | | | |]; try exact (Hpi_fb Hc).
    destruct (defeq_method rec g a c) as [ok1|err|why] eqn:H1; simpl in Hc; try discriminate.
    destruct ok1; [|discriminate].
    destruct (VTrExpr_inv_lam Ht) as [a' [b' [Ha_is [Ha_tr [Hb_tr Heq_t]]]]].
    destruct (VTrExpr_inv_lam Hs) as [c' [d' [Hc_is [Hc_tr [Hd_tr Heq_s]]]]].
    pose proof (fms_defeq Hms Hctx Ha_tr Hc_tr H1) as [Tac Hac].
    destruct Ha_is as [uA HuA]. destruct Hc_is as [uC HuC].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG HuA Hac) as [u1 Hc1].
    assert (Hac_s : VIsDefEq venv (List.length ps) (vl_ctx L) a' c' (VSort uA))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hc1) | exact Hac]).
    assert (HwfL_a : VLCtxWF venv (List.length ps) (vl_push_lam L a'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists uA; exact HuA]).
    assert (HwfL_c : VLCtxWF venv (List.length ps) (vl_push_lam L c'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists uC; exact HuC]).
    pose proof (VTrExpr_defeq_ctx Hves HwfL_c HwfL_a
                  (VLCtxDefEq_push_lam Hwf HwfL (VDF_symm Hac_s)) Hd_tr) as Hd_tr_a.
    assert (Hctx_a : VTrCtx env venv ps (push_binding g a None) (vl_push_lam L a'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Ha_tr | exists uA; exact HuA]).
    pose proof (fms_defeq Hms Hctx_a Hb_tr Hd_tr_a Hc) as [Tbd Hbd].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists (VForallE a' Tbd); eapply VDF_lamDF; [exact Hac_s | exact Hbd] | exact Heq_s].
  - (* EPi *)
    destruct s as [| | | | | | |nm2 bi2 c d| | | |]; try exact (Hpi_fb Hc).
    destruct (defeq_method rec g a c) as [ok1|err|why] eqn:H1; simpl in Hc; try discriminate.
    destruct ok1; [|discriminate].
    destruct (VTrExpr_inv_pi Ht) as [a' [b' [Ha_is [Hb_is [Ha_tr [Hb_tr Heq_t]]]]]].
    destruct (VTrExpr_inv_pi Hs) as [c' [d' [Hc_is [Hd_is [Hc_tr [Hd_tr Heq_s]]]]]].
    pose proof (fms_defeq Hms Hctx Ha_tr Hc_tr H1) as [Tac Hac].
    destruct Ha_is as [uA HuA]. destruct Hc_is as [uC HuC].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG HuA Hac) as [u1 Hc1].
    assert (Hac_s : VIsDefEq venv (List.length ps) (vl_ctx L) a' c' (VSort uA))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hc1) | exact Hac]).
    assert (HwfL_a : VLCtxWF venv (List.length ps) (vl_push_lam L a'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists uA; exact HuA]).
    assert (HwfL_c : VLCtxWF venv (List.length ps) (vl_push_lam L c'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists uC; exact HuC]).
    pose proof (VTrExpr_defeq_ctx Hves HwfL_c HwfL_a
                  (VLCtxDefEq_push_lam Hwf HwfL (VDF_symm Hac_s)) Hd_tr) as Hd_tr_a.
    assert (Hctx_a : VTrCtx env venv ps (push_binding g a None) (vl_push_lam L a'))
      by (apply VTrCtx_push_lam; [exact Hctx | exact Ha_tr | exists uA; exact HuA]).
    pose proof (fms_defeq Hms Hctx_a Hb_tr Hd_tr_a Hc) as [Tbd Hbd].
    destruct Hb_is as [vB HvB].
    assert (HG_a : VCtxWF venv (List.length ps) (a' :: vl_ctx L))
      by (split; [exact HG | exists uA; exact HuA]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG_a HvB Hbd) as [u2 Hc2].
    assert (Hbd_s : VIsDefEq venv (List.length ps) (a' :: vl_ctx L) b' d' (VSort vB))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hc2) | exact Hbd]).
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
      exists (VSort (VLIMax uA vB)); eapply VDF_forallEDF; [exact Hac_s | exact Hbd_s] | exact Heq_s].
  - (* ELit *)
    destruct l1 as [n1|s1];
    destruct s as [| | | | | | | | |l2| |]; try exact (Hpi_fb Hc);
    destruct l2 as [n2|s2]; try exact (Hpi_fb Hc).
    + inversion Hc as [Hnm]. apply N.eqb_eq in Hnm. subst n2.
      eapply VTrExpr_uniq; eassumption.
    + inversion Hc as [Hst]. apply String.eqb_eq in Hst. subst s2.
      eapply VTrExpr_uniq; eassumption.
Qed.

Lemma core_finish_conversion_sound env venv ps chk rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps chk rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  core_finish_conversion rec fuel env ps g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hfc.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold core_finish_conversion in Hfc.
  pose proof (core_spine_core_apps t []) as Hspt.
  pose proof (core_spine_core_apps s []) as Hsps.
  destruct (core_spine t []) as [th ta] eqn:Et.
  destruct (core_spine s []) as [sh sa] eqn:Es.
  simpl in Hspt, Hsps.
  destruct (match th, sh with
    | EProj _ ti te, EProj _ si se =>
        if Nat.eqb ti si && Nat.eqb (List.length ta) (List.length sa) then
          ok <- core_lazy_delta_proj (S fuel) rec fuel env ps g ti te se;;
          if ok then
            match ta with
            | [] => Accept true
            | _ => core_compare_args_cheap_first rec env g ta sa
            end
          else Accept false
        else Accept false
    | _, _ => Accept false
    end) as [lpok|err|why] eqn:Hlp; simpl in Hfc; try discriminate.
  destruct lpok.
  - (* Lazy delta projection succeeded *)
    destruct th as [| | | | | | | | | |own1 ti te|]; try discriminate.
    destruct sh as [| | | | | | | | | |own2 si se|]; try discriminate.
    destruct (Nat.eqb ti si && Nat.eqb (List.length ta) (List.length sa)) eqn:Echk;
      [|discriminate].
    apply andb_true_iff in Echk as [Eidx Elen].
    apply Nat.eqb_eq in Eidx. apply Nat.eqb_eq in Elen. subst si.
    destruct (core_lazy_delta_proj (S fuel) rec fuel env ps g ti te se) as [ok|err|why] eqn:Hldp;
      simpl in Hlp; try discriminate.
    destruct ok; [|discriminate].
    rewrite <- Hspt in Ht. rewrite <- Hsps in Hs.
    destruct (VTrExpr_core_apps_inv Ht) as [th' [ta' [Heq_t [Hth Hta]]]].
    destruct (VTrExpr_core_apps_inv Hs) as [sh' [sa' [Heq_s [Hsh Hsa]]]].
    destruct (VTrExpr_inv_proj (VTrExprS_to_VTrExpr Hth))
      as [te' [pv1 [fty1 [Hte [Hp1 Hth_eq]]]]].
    destruct (VTrExpr_inv_proj (VTrExprS_to_VTrExpr Hsh))
      as [se' [pv2 [fty2 [Hse [Hp2 Hsh_eq]]]]].
    pose proof (core_lazy_delta_proj_sound Hves Hms Hctx Hp1 Hp2 Hte Hse Hldp) as Hpv12.
    assert (Hhead_eq : VIsDefEqU venv (List.length ps) (vl_ctx L) th' sh').
    { eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
        apply VIsDefEqU_symm; exact Hth_eq |].
      eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Hpv12 | exact Hsh_eq]. }
    assert (Hargs_eq : Forall2 (VIsDefEqU venv (List.length ps) (vl_ctx L)) ta' sa').
    { destruct ta as [|a0 ta_r].
      - destruct sa; simpl in Elen; try lia.
        inversion Hta; inversion Hsa; subst. constructor.
      - eapply core_compare_args_cheap_first_sound;
          [exact Hves | exact Hms | exact Hctx
          | apply Forall2_VTrExprS_to_VTrExpr; exact Hta
          | apply Forall2_VTrExprS_to_VTrExpr; exact Hsa | exact Hlp]. }
    destruct (vapps_defeq_congr_l Hwf Hinj HG (VIsDefEqU_refl_l Heq_t) Hhead_eq Hargs_eq) as [_ Happs].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | apply VIsDefEqU_symm; exact Heq_t |].
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Happs | exact Heq_s].
  - (* Full projection reduction or compare_after_whnf *)
    set (project := fun e => let '(head, args) := core_spine e [] in match head with
      | EProj owner index value =>
          field <- core_reduce_projection rec env g owner index value ;;
          Accept (option_map (fun f => core_apps f args) field)
      | _ => Accept None end).
    assert (Hfc' : (tp <- project t;;
             sp <- project s;;
             match tp, sp with
             | Some t0, Some s0 => defeq_method rec g t0 s0
             | Some t0, None => defeq_method rec g t0 s
             | None, Some s0 => defeq_method rec g t s0
             | None, None => compare_after_whnf rec fuel env g t s
             end) = Accept true)
      by (unfold project; rewrite Et, Es; exact Hfc).
    clear Hfc; rename Hfc' into Hfc.
    assert (Hproj_s : forall e e' e1,
        VTrExpr env venv ps L e e' ->
        project e = Accept (Some e1) ->
        VTrExpr env venv ps L e1 e').
    { intros e e' e1 He Hpe. unfold project in Hpe.
      pose proof (core_spine_core_apps e []) as Hspe.
      destruct (core_spine e []) as [eh ea] eqn:Ee. simpl in Hspe.
      destruct eh as [| | | | | | | | | |own idx val|]; try discriminate.
      destruct (core_reduce_projection rec env g own idx val) as [[fv|]|err|why] eqn:Hrp;
        simpl in Hpe; try discriminate.
      inversion Hpe; subst e1; clear Hpe.
      rewrite <- Hspe in He.
      destruct (VTrExpr_core_apps_inv He) as [eh' [ea' [Heq_e [Heh Hea]]]].
      pose proof (core_reduce_projection_with_sound Hves Hms
                    (fms_whnf Hms) Hctx (VTrExprS_to_VTrExpr Heh) Hrp) as Hfv_tr.
      eapply VTrExpr_defeq_r; [exact Hves | exact HwfL | | exact Heq_e].
      eapply VTrExpr_core_apps; [exact Hves | exact HwfL | exact Hfv_tr |
        apply Forall2_VTrExprS_to_VTrExpr; exact Hea | exact (VIsDefEqU_refl_l Heq_e)]. }
    destruct (project t) as [[tp|]|err|why] eqn:Hpt; simpl in Hfc; try discriminate;
    destruct (project s) as [[sp|]|err|why] eqn:Hps; simpl in Hfc; try discriminate.
    + exact (fms_defeq Hms Hctx (Hproj_s _ _ _ Ht Hpt) (Hproj_s _ _ _ Hs Hps) Hfc).
    + exact (fms_defeq Hms Hctx (Hproj_s _ _ _ Ht Hpt) Hs Hfc).
    + exact (fms_defeq Hms Hctx Ht (Hproj_s _ _ _ Hs Hps) Hfc).
    + eapply compare_after_whnf_sound; eassumption.
Qed.

Theorem defeq_step_sound env venv ps rec fuel g L t s t' s' :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true rec ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  defeq_step rec fuel env ps g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hms Hctx Ht Hs Hd.
  unfold defeq_step in Hd. cbv zeta in Hd.
  pose proof (FullMethodsSound_inference_only Hms) as Hms_io.
  set (rec0 := inference_only rec) in *.
  destruct (core_quick rec0 fuel g t s) as [[ok|]|err|why] eqn:Hq; cbn [bind] in Hd; try discriminate.
  { inversion Hd; subst ok. eapply core_quick_sound; eassumption. }
  destruct (core_true_shortcut rec0 env g t s) as [sc|err|why] eqn:Hsc; cbn [bind] in Hd; try discriminate.
  destruct sc; [eapply core_true_shortcut_sound; eassumption |].
  destruct (core_proof_irrel rec0 fuel g t s) as [[ok|]|err|why] eqn:Hpi;
    cbn [bind] in Hd; try discriminate.
  { inversion Hd; subst ok. eapply core_proof_irrel_sound; eassumption. }
  destruct (whnf_core_method rec0 true g t) as [tn|err|why] eqn:Hwt; cbn [bind] in Hd; try discriminate.
  destruct (whnf_core_method rec0 true g s) as [sn|err|why] eqn:Hws; cbn [bind] in Hd; try discriminate.
  pose proof (fms_whnf_core Hms_io Hctx Ht Hwt) as Htn.
  pose proof (fms_whnf_core Hms_io Hctx Hs Hws) as Hsn.
  destruct (core_lazy_delta (S fuel) rec0 fuel env ps g tn sn) as [prog|err|why] eqn:Hld;
    cbn [bind] in Hd; try discriminate.
  pose proof (core_lazy_delta_sound Hves Hms_io Hctx Htn Hsn Hld) as Hprog.
  destruct prog as [ok | tn1 sn1].
  - inversion Hd; subst ok. exact Hprog.
  - destruct Hprog as [Htn1 Hsn1].
    eapply core_finish_conversion_sound; eassumption.
Qed.

(* ========================================================================= *)
(* 7. Master Fuel Induction & Public Entry Points                            *)
(* ========================================================================= *)

Theorem checker_mode_sound fuel env venv ps :
  VEnvSound env venv ->
  forall mode, FullMethodsSound env venv ps true (checker_mode mode fuel env ps).
Proof.
  intros Hves.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  induction fuel as [|n IH]; intros mode.
  - constructor; simpl; intros; try discriminate.
  - pose proof (IH mode) as Hrec.
    pose proof (IH EagerReduction) as Heager.
    constructor; simpl.
    + (* fms_infer *)
      intros g L e ty Hctx _ Hinf.
      eapply infer_step_sound_true; [exact Hves | exact Hrec | exact Hctx | exact Hinf].
    + (* fms_infer_typed *)
      intros g L e e' ty Hctx He Hinf.
      destruct (infer_step_sound_true Hves Hrec Hctx Hinf) as [e1 [ty' [He1 [Hty' He1_ty]]]].
      pose proof (VTrExpr_uniq Hves (VTrCtx_to_VLCtxWF Hctx) He1 He) as He1e.
      exists ty'. split; [exact Hty' |].
      eapply VIsDefEqU_hasType_r;
        [exact Hwf | exact Hinj | exact (VLCtxWF_to_VCtxWF (VTrCtx_to_VLCtxWF Hctx))
        | exact He1_ty | exact He1e].
    + (* fms_infer_type *)
      intros g L e e' ty Hctx He Hinf.
      eapply infer_step_sound_false; [exact Hves | exact Hrec | exact Hctx | exact He | exact Hinf].
    + (* fms_whnf_core *)
      intros cheap g L e e' e1 Hctx He Hw.
      eapply whnf_core_step_sound; [exact Hves | exact Hrec | exact Hctx | exact He | exact Hw].
    + (* fms_whnf *)
      intros g L e e' e1 Hctx He Hw.
      eapply whnf_loop_sound; [exact Hves | exact Hrec | exact Hctx | exact He | exact Hw].
    + (* fms_defeq *)
      intros g L t s t' s' Hctx Ht Hs Hd.
      eapply defeq_step_sound; [exact Hves | exact Hrec | exact Hctx | exact Ht | exact Hs | exact Hd].
    + (* fms_eager_defeq *)
      intros g L t s t' s' Hctx Ht Hs Hd.
      eapply defeq_step_sound; [exact Hves | exact Heager | exact Hctx | exact Ht | exact Hs | exact Hd].
Qed.

Corollary checker_sound fuel env venv ps :
  VEnvSound env venv ->
  FullMethodsSound env venv ps true (checker fuel env ps).
Proof. intros Hves. exact (checker_mode_sound fuel ps Hves NormalReduction). Qed.

Theorem infer_full_sound fuel env venv ps g L e ty :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  infer fuel env ps g e = Accept ty ->
  exists e' ty',
    VTrExpr env venv ps L e e' /\
    VTrExpr env venv ps L ty ty' /\
    VHasType venv (List.length ps) (vl_ctx L) e' ty'.
Proof.
  intros Hves Hctx Hinf.
  exact (fms_infer (checker_sound fuel ps Hves) Hctx eq_refl Hinf).
Qed.

Theorem infer_full_sound_typed fuel env venv ps g L e e' ty :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  infer fuel env ps g e = Accept ty ->
  exists ty',
    VTrExpr env venv ps L ty ty' /\
    VHasType venv (List.length ps) (vl_ctx L) e' ty'.
Proof.
  intros Hves Hctx He Hinf.
  exact (fms_infer_typed (checker_sound fuel ps Hves) Hctx He Hinf).
Qed.

Theorem whnf_full_sound fuel env venv ps g L e e' e1 :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L e e' ->
  whnf fuel env ps g e = Accept e1 ->
  VTrExpr env venv ps L e1 e'.
Proof.
  intros Hves Hctx He Hw.
  unfold whnf in Hw. destruct fuel as [|n]; [discriminate |].
  destruct (core_supported env e); [|discriminate].
  exact (fms_whnf (checker_sound (S n) ps Hves) Hctx He Hw).
Qed.

Theorem defeq_full_sound fuel env venv ps g L t s t' s' :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  defeq fuel env ps g t s = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hctx Ht Hs Hd.
  unfold defeq in Hd. destruct fuel as [|n]; [discriminate |].
  destruct (core_supported env t && core_supported env s); [|discriminate].
  exact (fms_defeq (checker_sound (S n) ps Hves) Hctx Ht Hs Hd).
Qed.

Theorem check_full_sound fuel env venv ps g L e ty :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  check fuel env ps g e ty = Accept tt ->
  exists e' ty' u',
    VTrExpr env venv ps L e e' /\
    VTrExpr env venv ps L ty ty' /\
    VHasType venv (List.length ps) (vl_ctx L) ty' (VSort u') /\
    VHasType venv (List.length ps) (vl_ctx L) e' ty'.
Proof.
  intros Hves Hctx Hchk.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  unfold check in Hchk.
  destruct (sort_of (checker fuel env ps) g ty) as [u|err|why] eqn:Hsu;
    simpl in Hchk; try discriminate.
  destruct (infer fuel env ps g e) as [et|err|why] eqn:Hinf;
    simpl in Hchk; try discriminate.
  destruct (defeq fuel env ps g et ty) as [ok|err|why] eqn:Hdeq;
    simpl in Hchk; try discriminate.
  destruct ok; [|discriminate].
  destruct (sort_of_sound_checking Hves (checker_sound fuel ps Hves) Hctx Hsu)
    as [ty' [u' [_ [_ [Hty_tr Hty_u]]]]].
  destruct (infer_full_sound Hves Hctx Hinf) as [e' [et' [He_tr [Het_tr He_et]]]].
  pose proof (defeq_full_sound Hves Hctx Het_tr Hty_tr Hdeq) as Het_ty.
  exists e', ty', u'. repeat split; try assumption.
  eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | exact He_et | exact Het_ty].
Qed.

Theorem check_defeq_full_sound fuel env venv ps g L t s :
  VEnvSound env venv ->
  VTrCtx env venv ps g L ->
  check_defeq fuel env ps g t s = Accept tt ->
  exists t' s' T,
    VTrExpr env venv ps L t t' /\
    VTrExpr env venv ps L s s' /\
    VIsDefEq venv (List.length ps) (vl_ctx L) t' s' T.
Proof.
  intros Hves Hctx Hcd.
  unfold check_defeq in Hcd.
  destruct (infer fuel env ps g t) as [tt0|err|why] eqn:Hit; simpl in Hcd; try discriminate.
  destruct (infer fuel env ps g s) as [st0|err|why] eqn:His; simpl in Hcd; try discriminate.
  destruct (defeq fuel env ps g tt0 st0) as [ok1|err|why] eqn:Hd1; simpl in Hcd; try discriminate.
  destruct ok1; simpl in Hcd; [|discriminate].
  destruct (defeq fuel env ps g t s) as [ok2|err|why] eqn:Hd2; simpl in Hcd; try discriminate.
  destruct ok2; [|discriminate].
  destruct (infer_full_sound Hves Hctx Hit) as [t' [tt' [Ht_tr _]]].
  destruct (infer_full_sound Hves Hctx His) as [s' [st' [Hs_tr _]]].
  destruct (defeq_full_sound Hves Hctx Ht_tr Hs_tr Hd2) as [T Hts].
  exists t', s', T. repeat split; assumption.
Qed.

(* ========================================================================= *)
(* 8. Unconditional `trE`-Fragment Corollaries (Superseding `InferSoundness`) *)
(* ========================================================================= *)

Lemma VTrExpr_of_trE_lams env venv ps bs G e e' :
  VEnvWF venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  trE ps e = Some e' ->
  VExprWF venv (List.length ps) G e' ->
  VTrExpr env venv ps {| vl_free := []; vl_bound := vl_of_ctx_lams G |} e e'.
Proof.
  intros Hwf Hbs HG Htr Hwe.
  pose proof (VTrCtx_of_TrBCtx env Hwf Hbs HG) as Hctx.
  pose proof (VTrCtx_to_VLCtxWF Hctx) as HwfL.
  apply VTrExprS_to_VTrExpr.
  apply VTrExprS_of_trE; [exact Hwf | exact HwfL | | exact Htr |].
  - intros i T Hlk.
    unfold vl_ctx in Hlk; simpl in Hlk; rewrite vlentries_to_ctx_of_lams, app_nil_r in Hlk.
    unfold vl_bvar; simpl.
    rewrite (vl_lookup_bound_of_lams Hlk 0), Nat.add_0_r, vliftN_zero. reflexivity.
  - unfold vl_ctx; simpl; rewrite vlentries_to_ctx_of_lams, app_nil_r. exact Hwe.
Qed.

Theorem defeq_types_sound_unconditional fuel env venv ps mode bs G a b A B :
  VEnvSound env venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  defeq_method (checker_mode mode fuel env ps) {| bound_context := bs; free_context := [] |} a b
    = Accept true ->
  trE ps a = Some A ->
  trE ps b = Some B ->
  VIsType venv (List.length ps) G A ->
  VIsType venv (List.length ps) G B ->
  exists u, VIsDefEq venv (List.length ps) G A B (VSort u).
Proof.
  intros Hves Hbs HG Hd Ha Hb [uA HuA] [uB HuB].
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_of_TrBCtx env Hwf Hbs HG) as Hctx.
  pose proof (VTrExpr_of_trE_lams env Hwf Hbs HG Ha (ex_intro _ (VSort uA) HuA)) as Ha_tr.
  pose proof (VTrExpr_of_trE_lams env Hwf Hbs HG Hb (ex_intro _ (VSort uB) HuB)) as Hb_tr.
  pose proof (fms_defeq (checker_mode_sound fuel ps Hves mode) Hctx Ha_tr Hb_tr Hd) as [T HAB].
  unfold vl_ctx in HAB; simpl in HAB; rewrite vlentries_to_ctx_of_lams, app_nil_r in HAB.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG HuA HAB) as [us Hc].
  exists uA. eapply VDF_defeqDF; [exact (VDF_symm Hc) | exact HAB].
Qed.

(* Clean lemma: VTrExprS in pure-lambda context agrees syntactically with trE *)
Lemma VTrExprS_eq_trE env venv ps :
  forall L e e0,
    VTrExprS env venv ps L e e0 ->
    vl_free L = [] ->
    (forall i v t, vl_bvar L i = Some (v, t) -> v = VBVar i) ->
    forall e', trE ps e = Some e' -> e0 = e'.
Proof.
  intros L e e0 Htr.
  induction Htr as
    [L i v t Hlk _
    |
    |L u u' Hu
    |L c ci us us' Hci Hus' _
    |L f a f' a' A B _ _ Htr1 IH1 Htr2 IH2
    |L nm bi dom body dom' body' _ Htr1 IH1 Htr2 IH2
    |L nm bi dom body dom' body' _ _ Htr1 IH1 Htr2 IH2
    |
    |
    |
    |
    |L a a' Htr IH];
    intros Hfr Hbv res Hte; simpl in Hte; try discriminate.
  - inversion Hte; subst res. exact (Hbv _ _ _ Hlk).
  - unfold TrLevel in Hu. rewrite Hu in Hte. inversion Hte; reflexivity.
  - assert (Htrls : trLs ps us = Some us').
    { clear -Hus'. induction Hus' as [|u u' r r' Hu Hr IH]; simpl; [reflexivity |].
      unfold TrLevel in Hu. rewrite Hu, IH. reflexivity. }
    rewrite Htrls in Hte. inversion Hte; reflexivity.
  - destruct (trE ps f) as [f1|] eqn:Hf; destruct (trE ps a) as [a1|] eqn:Ha; try discriminate.
    inversion Hte; subst res. f_equal; [apply IH1 | apply IH2]; auto.
  - destruct (trE ps dom) as [A1|] eqn:HA; destruct (trE ps body) as [b1|] eqn:Hb; try discriminate.
    inversion Hte; subst res. f_equal; [apply IH1; auto |].
    apply IH2; [exact Hfr | | reflexivity].
    intros [|i] v t Hlk; unfold vl_bvar in Hlk; simpl in Hlk.
    + inversion Hlk; reflexivity.
    + destruct (vl_lookup_bound_unshift (Nat.le_0_l 0) Hlk)
        as [v0 [t0 [E0 [-> _]]]].
      rewrite (Hbv i v0 t0 E0). reflexivity.
  - destruct (trE ps dom) as [A1|] eqn:HA; destruct (trE ps body) as [B1|] eqn:HB; try discriminate.
    inversion Hte; subst res. f_equal; [apply IH1; auto |].
    apply IH2; [exact Hfr | | reflexivity].
    intros [|i] v t Hlk; unfold vl_bvar in Hlk; simpl in Hlk.
    + inversion Hlk; reflexivity.
    + destruct (vl_lookup_bound_unshift (Nat.le_0_l 0) Hlk)
        as [v0 [t0 [E0 [-> _]]]].
      rewrite (Hbv i v0 t0 E0). reflexivity.
  - apply IH; auto.
Qed.

Lemma vl_lookup_bound_of_lams_inv G : forall i d v t,
  vl_lookup_bound (vl_of_ctx_lams G) i d = Some (v, t) -> v = VBVar (i + d).
Proof.
  induction G as [|A G IH]; intros [|i] d v t H; simpl in H; try discriminate.
  - inversion H; reflexivity.
  - specialize (IH i (S d) v t H). rewrite IH. f_equal. lia.
Qed.

Theorem infer_sound_trE_unconditional fuel env venv ps bs G e ty e' :
  VEnvSound env venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  infer fuel env ps {| bound_context := bs; free_context := [] |} e = Accept ty ->
  trE ps e = Some e' ->
  exists ty',
    VTrExpr env venv ps {| vl_free := []; vl_bound := vl_of_ctx_lams G |} ty ty' /\
    VHasType venv (List.length ps) G e' ty'.
Proof.
  intros Hves Hbs HG Hinf He.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_of_TrBCtx env Hwf Hbs HG) as Hctx.
  destruct (infer_full_sound Hves Hctx Hinf) as [e1 [ty' [[e0 [He0 H01]] [Hty' He1_ty]]]].
  unfold vl_ctx in H01, He1_ty; simpl in H01, He1_ty;
    rewrite vlentries_to_ctx_of_lams, app_nil_r in H01, He1_ty.
  assert (He0_eq : e0 = e').
  { eapply VTrExprS_eq_trE; [exact He0 | reflexivity | | exact He].
    intros i v t Hlk. unfold vl_bvar in Hlk; simpl in Hlk.
    pose proof (vl_lookup_bound_of_lams_inv Hlk) as Hv.
    rewrite Nat.add_0_r in Hv. exact Hv. }
  subst e0.
  exists ty'. split; [exact Hty' |].
  eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact He1_ty |
    apply VIsDefEqU_symm; exact H01].
Qed.

Theorem check_sound_trE_unconditional fuel env venv ps bs G e ty e' T :
  VEnvSound env venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  check fuel env ps {| bound_context := bs; free_context := [] |} e ty = Accept tt ->
  trE ps e = Some e' ->
  trE ps ty = Some T ->
  VHasType venv (List.length ps) G e' T.
Proof.
  intros Hves Hbs HG Hchk He Hty.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_of_TrBCtx env Hwf Hbs HG) as Hctx.
  destruct (check_full_sound Hves Hctx Hchk)
    as [e1 [ty1 [u' [[e0 [He0 H01]] [[t0 [Ht0 H02]] [_ He1_ty1]]]]]].
  unfold vl_ctx in H01, H02, He1_ty1; simpl in H01, H02, He1_ty1;
    rewrite vlentries_to_ctx_of_lams, app_nil_r in H01, H02, He1_ty1.
  assert (Hbv : forall i v t,
      vl_bvar {| vl_free := []; vl_bound := vl_of_ctx_lams G |} i = Some (v, t) -> v = VBVar i).
  { intros i v t Hlk. unfold vl_bvar in Hlk; simpl in Hlk.
    pose proof (vl_lookup_bound_of_lams_inv Hlk) as Hv.
    rewrite Nat.add_0_r in Hv. exact Hv. }
  pose proof (VTrExprS_eq_trE He0 eq_refl Hbv He) as ->.
  pose proof (VTrExprS_eq_trE Ht0 eq_refl Hbv Hty) as ->.
  eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact HG | | apply VIsDefEqU_symm; exact H02].
  eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact HG | exact He1_ty1 |
    apply VIsDefEqU_symm; exact H01].
Qed.

Theorem check_defeq_sound_trE_unconditional fuel env venv ps bs G t s t' s' :
  VEnvSound env venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  check_defeq fuel env ps {| bound_context := bs; free_context := [] |} t s = Accept tt ->
  trE ps t = Some t' ->
  trE ps s = Some s' ->
  exists T, VIsDefEq venv (List.length ps) G t' s' T.
Proof.
  intros Hves Hbs HG Hcd Ht Hs.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VTrCtx_of_TrBCtx env Hwf Hbs HG) as Hctx.
  destruct (check_defeq_full_sound Hves Hctx Hcd)
    as [t1 [s1 [T [[t0 [Ht0 H01]] [[s0 [Hs0 H02]] Hts]]]]].
  unfold vl_ctx in H01, H02, Hts; simpl in H01, H02, Hts;
    rewrite vlentries_to_ctx_of_lams, app_nil_r in H01, H02, Hts.
  assert (Hbv : forall i v ty0,
      vl_bvar {| vl_free := []; vl_bound := vl_of_ctx_lams G |} i = Some (v, ty0) -> v = VBVar i).
  { intros i v ty0 Hlk. unfold vl_bvar in Hlk; simpl in Hlk.
    pose proof (vl_lookup_bound_of_lams_inv Hlk) as Hv.
    rewrite Nat.add_0_r in Hv. exact Hv. }
  pose proof (VTrExprS_eq_trE Ht0 eq_refl Hbv Ht) as ->.
  pose proof (VTrExprS_eq_trE Hs0 eq_refl Hbv Hs) as ->.
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact H01 |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
    exists T; exact Hts | apply VIsDefEqU_symm; exact H02].
Qed.

(* ========================================================================= *)
(* 9. Composing with `DefEqCache.v` and `EquivManager`                       *)
(* ========================================================================= *)

Theorem cached_defeq_full_sound fuel env venv ps g cache L t s t' s' :
  VEnvSound env venv ->
  cache_sound_for fuel env ps cache ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  snd (cached_defeq fuel env ps g cache t s) = Accept true ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hcs Hctx Ht Hs Hcd.
  rewrite (cached_defeq_refines_uncached g t s Hcs) in Hcd.
  eapply defeq_full_sound; eassumption.
Qed.

Definition sem_defeq_rel (env : environment) (venv : VEnv) (ps : list name)
    (g : context) (t s : expr) : Prop :=
  forall L t' s',
    VTrCtx env venv ps g L ->
    VTrExpr env venv ps L t t' ->
    VTrExpr env venv ps L s s' ->
    VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.

Theorem em_is_equiv_ro_hashed_VIsDefEqU env venv ps m h1 h2 g L t s t' s' :
  em_sound_for (sem_defeq_rel env venv ps) m ->
  em_is_equiv_ro_hashed m h1 h2 g t s = true ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hm Hchk Hctx Ht Hs.
  pose proof (@em_is_equiv_ro_hashed_sound (sem_defeq_rel env venv ps) m h1 h2 g t s Hm Hchk)
    as Hrel.
  exact (Hrel L t' s' Hctx Ht Hs).
Qed.

Theorem em_is_equiv_ro_VIsDefEqU env venv ps m g L t s t' s' :
  VEnvSound env venv ->
  em_sound_for (sem_defeq_rel env venv ps) m ->
  em_is_equiv_ro m g t s = true ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L t t' ->
  VTrExpr env venv ps L s s' ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) t' s'.
Proof.
  intros Hves Hm Hchk Hctx Ht Hs.
  pose proof (@em_is_equiv_ro_sound (sem_defeq_rel env venv ps) m g t s
    (fun g0 a b Hab L0 a' b' Hctx0 Ha Hb =>
       VTrExpr_expr_eqb Hves (VTrCtx_to_VLCtxWF Hctx0) Hab Ha Hb)
    Hm Hchk) as Hrel.
  exact (Hrel L t' s' Hctx Ht Hs).
Qed.

Print Assumptions core_beta_sound.
Print Assumptions core_unfold_sound.
Print Assumptions core_reduce_nat_sound.
Print Assumptions core_reduce_quotient_sound.
Print Assumptions core_reduce_recursor_sound.
Print Assumptions core_reduce_projection_with_sound.
Print Assumptions whnf_loop_sound.
Print Assumptions infer_step_sound_true.
Print Assumptions infer_step_sound_false.
Print Assumptions defeq_step_sound.
Print Assumptions checker_mode_sound.
Print Assumptions infer_full_sound.
Print Assumptions whnf_full_sound.
Print Assumptions defeq_full_sound.
Print Assumptions check_full_sound.
Print Assumptions check_defeq_full_sound.
Print Assumptions defeq_types_sound_unconditional.
Print Assumptions infer_sound_trE_unconditional.
Print Assumptions check_sound_trE_unconditional.
Print Assumptions check_defeq_sound_trE_unconditional.
Print Assumptions cached_defeq_full_sound.
Print Assumptions em_is_equiv_ro_VIsDefEqU.
