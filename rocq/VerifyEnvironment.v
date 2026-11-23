(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end soundness of the executable kernel environment & admission stack
   (`Primitives.v`, `Declarations.v`, `Safety.v`, `Quotient.v`, `Inductive.v`,
   `InductiveSafety.v`, `PersistentAdmission.v`) against the declarative
   environment theory (`DeclarativeTyping.v`, `EnvDeclTheory.v`) via the
   verified type checker (`VerifyTypeChecker.v`) and translation (`VerifyExpr.v`).

   Covers all upstream `Lean4Lean/Verify/Environment/` modules:
   - `Verify/Environment/Basic.lean`: environment monotonicity & `VEnvSound`
     preservation for fresh extensions.
   - `Verify/Environment/Declarations.lean`: `check_header`, `check_proposition`,
     `checked_constant`, `admit`, `check_declarations`.
   - `Verify/Environment/Primitives.lean`: `primitive_eq_closed`,
     `primitive_check_closed`, `primitive_check_equations`, `classify_primitive`.
   - `Verify/Environment/Safety.lean`: `admit_extended`, `admit_mutual`,
     `admit_inductive_extended` safety isolation (`DUnsafe`/`DPartial` leave
     the safe declarative `VEnv` and `VEnvSound` intact).
   - `Verify/Environment/Quotient.lean`: exact computational bridge between
     `Quotient.canonical_quotient` / `quotient_check_eq` and
     `EnvDeclTheory.eqConst` / `quotConst` / `quotMkConst` / `quotLiftConst` /
     `quotIndConst` / `addQuot_WF` / `addQuot_quotInd_iota`.
   - `Verify/Environment/Inductive.lean`: connection to `EnvDeclTheory.addInduct_WF`
     and unsafe inductive isolation.
   - `Verify/Environment/Persistent.lean`: `reference_batch`, `state_step`,
     `transaction` (rollback soundness), and `state_stream` soundness from
     `initial_state` / `VEnvSound_empty`.

   Zero axioms, zero `Admitted`. *)

From Stdlib Require Import List Bool Arith PeanoNat NArith Lia String.
From LeanPort Require Import
  Syntax Universes UniverseSoundness Checker Primitives Declarations Safety
  InductiveUtils Quotient Inductive NestedAdmission InductiveSafety
  DagScope DagArena DagAdmission DagTheoremOpaque PersistentIndex
  CombinedAdmissionRefinement PersistentAdmission SemanticModel DeclarativeTyping
  TypingLemmas StrongTyping PatternConfluence EnvDeclTheory InferSoundness
  VerifyExpr VerifyTypeChecker.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Environment Extension & Monotonicity for `VTrExpr` / `VEnvSound`       *)
(* ========================================================================= *)

Definition env_extends (env1 env2 : environment) : Prop :=
  (forall n d, find_decl n env1 = Some d -> find_decl n env2 = Some d) /\
  (core_nat_ready env1 = true -> core_nat_ready env2 = true) /\
  (core_bool_ready env1 = true -> core_bool_ready env2 = true) /\
  (core_string_ready env1 = true -> core_string_ready env2 = true).

Lemma find_decl_cons_fresh env d n d0 :
  find_decl (decl_name d) env = None ->
  find_decl n env = Some d0 ->
  find_decl n (d :: env) = Some d0.
Proof.
  intros Hfresh Hfind. simpl.
  destruct (name_eqb n (decl_name d)) eqn:En.
  - apply name_eqb_eq in En. subst n. rewrite Hfresh in Hfind. discriminate.
  - exact Hfind.
Qed.

Lemma core_inductive_extends env1 env2 owner info :
  (forall n d, find_decl n env1 = Some d -> find_decl n env2 = Some d) ->
  core_inductive env1 owner = Some info ->
  core_inductive env2 owner = Some info.
Proof.
  intros Hext Hi. unfold core_inductive in *.
  destruct (find_decl owner env1) as [d|] eqn:Hf; [|discriminate].
  rewrite (Hext _ _ Hf). exact Hi.
Qed.

Lemma core_constructor_extends env1 env2 cn ci :
  (forall n d, find_decl n env1 = Some d -> find_decl n env2 = Some d) ->
  core_constructor env1 cn = Some ci ->
  core_constructor env2 cn = Some ci.
Proof.
  intros Hext Hc. unfold core_constructor in *.
  destruct (find_decl cn env1) as [d|] eqn:Hf; [|discriminate].
  rewrite (Hext _ _ Hf). exact Hc.
Qed.

Lemma core_ctor_shape_extends env1 env2 n parent idx flds ty :
  (forall m d, find_decl m env1 = Some d -> find_decl m env2 = Some d) ->
  core_ctor_shape env1 n parent idx flds ty = true ->
  core_ctor_shape env2 n parent idx flds ty = true.
Proof.
  intros Hext H. unfold core_ctor_shape in *.
  destruct (find_decl n env1) as [d|] eqn:Hf; [|discriminate].
  rewrite (Hext _ _ Hf). exact H.
Qed.

Lemma env_extends_cons_fresh env d :
  find_decl (decl_name d) env = None ->
  env_extends env (d :: env).
Proof.
  intros Hfresh.
  assert (Hfind : forall n d0, find_decl n env = Some d0 -> find_decl n (d :: env) = Some d0)
    by (intros n d0 H; eapply find_decl_cons_fresh; eassumption).
  assert (Hnat : core_nat_ready env = true -> core_nat_ready (d :: env) = true).
  { unfold core_nat_ready.
    destruct (find_decl core_nat_name env) as [d0|] eqn:Hf; [|discriminate].
    rewrite (Hfind _ _ Hf).
    destruct (decl_kind_of d0); try discriminate.
    intros H. repeat (apply andb_true_iff in H; destruct H).
    repeat (apply andb_true_iff; split); try assumption;
      eapply core_ctor_shape_extends; eassumption. }
  assert (Hbool : core_bool_ready env = true -> core_bool_ready (d :: env) = true).
  { unfold core_bool_ready.
    destruct (find_decl core_bool_name env) as [d0|] eqn:Hf; [|discriminate].
    rewrite (Hfind _ _ Hf).
    destruct (decl_kind_of d0); try discriminate.
    intros H. repeat (apply andb_true_iff in H; destruct H).
    repeat (apply andb_true_iff; split); try assumption;
      eapply core_ctor_shape_extends; eassumption. }
  assert (Hstr : core_string_ready env = true -> core_string_ready (d :: env) = true).
  { unfold core_string_ready.
    destruct (find_decl core_char_of_nat env) as [dc|] eqn:Hfc; [|discriminate].
    destruct (find_decl core_string_of_list env) as [ds|] eqn:Hfs; [|discriminate].
    rewrite (Hfind _ _ Hfc), (Hfind _ _ Hfs).
    destruct (decl_kind_of dc); try discriminate. destruct p; try discriminate.
    destruct (decl_kind_of ds); try discriminate. destruct p; try discriminate.
    exact Hnat. }
  repeat split; assumption.
Qed.

Lemma VTrProj_extend_env env1 env2 venv1 venv2 U G owner idx sv pv fty :
  env_extends env1 env2 ->
  venv_ordered venv1 venv2 ->
  VTrProj env1 venv1 U G owner idx sv pv fty ->
  VTrProj env2 venv2 U G owner idx sv pv fty.
Proof.
  intros [Hfind _] Hord H.
  destruct H as [info ctor c d us ps idxs Hi Hc Hd Hk Hlt Hlp Hli Hw Hlu Hst Hpv Hty].
  eapply VTrProj_intro;
    [eapply core_inductive_extends; [exact Hfind | exact Hi]
    | exact Hc
    | exact (Hfind _ _ Hd)
    | exact Hk | exact Hlt | exact Hlp | exact Hli | exact Hw | exact Hlu
    | eapply VEnvOrdered_preserve_VHasType; [exact Hord | exact Hst]
    | exact Hpv
    | eapply VEnvOrdered_preserve_VHasType; [exact Hord | exact Hty]].
Qed.

Lemma VTrExprS_extend_env env1 env2 venv1 venv2 ps L e e' :
  env_extends env1 env2 ->
  venv_ordered venv1 venv2 ->
  VTrExprS env1 venv1 ps L e e' ->
  VTrExprS env2 venv2 ps L e e'.
Proof.
  intros Hext Hord H.
  destruct Hext as [Hfind [Hnat [Hbool Hstr]]].
  assert (Hext' : env_extends env1 env2) by (repeat split; assumption).
  induction H.
  - eapply VTrExprS_bvar; [exact H | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - eapply VTrExprS_fvar; [exact H | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - constructor; exact H.
  - eapply VTrExprS_const; [exact (venv_ord_const Hord H) | exact H0 | exact H1].
  - eapply VTrExprS_app;
      [eapply VEnvOrdered_preserve_VHasType; eassumption
      | eapply VEnvOrdered_preserve_VHasType; eassumption
      | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_lam;
      [eapply VEnvOrdered_preserve_VIsType; eassumption
      | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_pi;
      [eapply VEnvOrdered_preserve_VIsType; eassumption
      | eapply VEnvOrdered_preserve_VIsType; eassumption
      | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_let;
      [eapply VEnvOrdered_preserve_VHasType; eassumption
      | exact IHVTrExprS1 | exact IHVTrExprS2 | exact IHVTrExprS3].
  - eapply VTrExprS_proj; [exact IHVTrExprS | eapply VTrProj_extend_env; eassumption].
  - eapply VTrExprS_natlit; [exact (Hnat H) | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - eapply VTrExprS_strlit;
      [exact (Hstr H) | exact H0 | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - constructor; exact IHVTrExprS.
Qed.

Lemma VTrExpr_extend_env env1 env2 venv1 venv2 ps L e e' :
  env_extends env1 env2 ->
  venv_ordered venv1 venv2 ->
  VTrExpr env1 venv1 ps L e e' ->
  VTrExpr env2 venv2 ps L e e'.
Proof.
  intros Hext Hord [e0 [He0 [A HA]]].
  exists e0. split.
  - eapply VTrExprS_extend_env; eassumption.
  - exists A. eapply VEnvOrdered_preserve_VIsDefEq; eassumption.
Qed.

Lemma VTrExpr_empty_ctx_wf env venv ps :
  VEnvWF venv ->
  VTrCtx env venv ps empty_context vl_empty.
Proof.
  intros _. split; constructor.
Qed.

(* ========================================================================= *)
(* 2. Checking Helpers (`check_header`, `check_proposition`, `check_value`)  *)
(* ========================================================================= *)

Theorem check_header_sound fuel env venv n ps ty :
  VEnvSound env venv ->
  check_header fuel env n ps ty = Accept tt ->
  find_decl n env = None /\
  names_unique ps = true /\
  scoped 0 ty = true /\
  exists ty' u',
    VTrExpr env venv ps vl_empty ty ty' /\
    VHasType venv (List.length ps) [] ty' (VSort u') /\
    VConstantWF venv {| vc_uvars := List.length ps; vc_type := ty' |}.
Proof.
  intros Hves Hhdr.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  unfold check_header in Hhdr.
  destruct (find_decl n env) eqn:Hfind; [discriminate |].
  destruct (names_unique ps) eqn:Huniq; simpl in Hhdr; [|discriminate].
  destruct (scoped 0 ty) eqn:Hsc; simpl in Hhdr; [|discriminate].
  destruct (infer fuel env ps empty_context ty) as [inf|err|why] eqn:Hinf;
    simpl in Hhdr; try discriminate.
  destruct (whnf fuel env ps empty_context inf) as [red|err|why] eqn:Hw;
    simpl in Hhdr; try discriminate.
  destruct red as [| | |u| | | | | | | |]; try discriminate.
  pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
  destruct (infer_full_sound Hves Hctx Hinf) as [ty' [inf' [Hty_tr [Hinf_tr Hty_inf]]]].
  pose proof (whnf_full_sound Hves Hctx Hinf_tr Hw) as Hred_tr.
  destruct (VTrExpr_inv_sort Hred_tr) as [u' [Hu [Hu_wf Heq_u]]].
  assert (Hty_u : VHasType venv (List.length ps) [] ty' (VSort u')).
  { eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact I | exact Hty_inf |
      apply VIsDefEqU_symm; exact Heq_u]. }
  assert (Hty_cl : vclosed ty').
  { destruct (VIsDefEq_closedN Hcl Hty_u (I : VCtxClosed [])) as [H1 _]. exact H1. }
  split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
  exists ty', u'. split; [exact Hty_tr | split; [exact Hty_u |]].
  split; [exists u'; exact Hty_u | exact Hty_cl].
Qed.

Theorem check_proposition_sound fuel env venv ps ty :
  VEnvSound env venv ->
  check_proposition fuel env ps ty = Accept tt ->
  exists ty',
    VTrExpr env venv ps vl_empty ty ty' /\
    VHasType venv (List.length ps) [] ty' (VSort VLZero).
Proof.
  intros Hves Hprop.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  unfold check_proposition in Hprop.
  destruct (infer fuel env ps empty_context ty) as [inf|err|why] eqn:Hinf;
    simpl in Hprop; try discriminate.
  destruct (whnf fuel env ps empty_context inf) as [red|err|why] eqn:Hw;
    simpl in Hprop; try discriminate.
  destruct red as [| | |u| | | | | | | |]; try discriminate.
  destruct (level_equiv fuel u LZero) as [isz|err|why] eqn:Hz;
    simpl in Hprop; try discriminate.
  destruct isz; [|discriminate].
  pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
  destruct (infer_full_sound Hves Hctx Hinf) as [ty' [inf' [Hty_tr [Hinf_tr Hty_inf]]]].
  pose proof (whnf_full_sound Hves Hctx Hinf_tr Hw) as Hred_tr.
  destruct (VTrExpr_inv_sort Hred_tr) as [u' [Hu [Hu_wf Heq_u]]].
  assert (Hty_u : VHasType venv (List.length ps) [] ty' (VSort u')).
  { eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact I | exact Hty_inf |
      apply VIsDefEqU_symm; exact Heq_u]. }
  exists ty'. split; [exact Hty_tr |].
  eapply VDF_defeqDF;
    [eapply VDF_sortDF; [exact Hu_wf | exact I |
       eapply level_equiv_sound_vlevel with (v := LZero); [exact Hu | reflexivity | exact Hz]]
    | exact Hty_u].
Qed.

Theorem check_value_sound fuel env venv ps ty val :
  VEnvSound env venv ->
  check_value fuel env ps ty val = Accept tt ->
  scoped 0 val = true /\
  exists val' ty' u',
    VTrExpr env venv ps vl_empty val val' /\
    VTrExpr env venv ps vl_empty ty ty' /\
    VHasType venv (List.length ps) [] ty' (VSort u') /\
    VHasType venv (List.length ps) [] val' ty'.
Proof.
  intros Hves Hcv.
  pose proof (ves_wf Hves) as Hwf.
  unfold check_value in Hcv.
  destruct (scoped 0 val) eqn:Hsc; simpl in Hcv; [|discriminate].
  split; [reflexivity |].
  pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
  exact (check_full_sound Hves Hctx Hcv).
Qed.

(* ========================================================================= *)
(* 3. Primitive Verification Soundness (`Primitives.v` -> `VIsDefEq`)        *)
(* ========================================================================= *)

Theorem primitive_eq_closed_sound fuel env venv (a b : PQ.term) :
  VEnvSound env venv ->
  primitive_eq_closed fuel env a b = Accept tt ->
  exists a' b' T,
    VTrExpr env venv [] vl_empty (PQ.run a) a' /\
    VTrExpr env venv [] vl_empty (PQ.run b) b' /\
    VIsDefEq venv 0 [] a' b' T.
Proof.
  intros Hves Hpe.
  unfold primitive_eq_closed in Hpe.
  pose proof (VTrExpr_empty_ctx_wf env [] (ves_wf Hves)) as Hctx.
  exact (check_defeq_full_sound Hves Hctx Hpe).
Qed.

Theorem primitive_check_closed_sound fuel env venv (a ty : PQ.term) :
  VEnvSound env venv ->
  primitive_check_closed fuel env a ty = Accept tt ->
  exists a' ty' u',
    VTrExpr env venv [] vl_empty (PQ.run a) a' /\
    VTrExpr env venv [] vl_empty (PQ.run ty) ty' /\
    VHasType venv 0 [] ty' (VSort u') /\
    VHasType venv 0 [] a' ty'.
Proof.
  intros Hves Hpc.
  unfold primitive_check_closed in Hpc.
  pose proof (VTrExpr_empty_ctx_wf env [] (ves_wf Hves)) as Hctx.
  exact (check_full_sound Hves Hctx Hpc).
Qed.

Theorem primitive_check_equations_sound steps fuel env venv equations :
  VEnvSound env venv ->
  primitive_check_equations steps fuel env equations = Accept tt ->
  Forall (fun eq =>
    forall L,
      VTrCtx env venv [] (primitive_context eq) L ->
      exists lhs' rhs' T,
        VTrExpr env venv [] L (primitive_lhs eq) lhs' /\
        VTrExpr env venv [] L (primitive_rhs eq) rhs' /\
        VIsDefEq venv 0 (vl_ctx L) lhs' rhs' T) equations.
Proof.
  intros Hves Hchk.
  pose proof (primitive_check_equations_accepts _ _ _ _ Hchk) as Hall.
  eapply Forall_impl; [| exact Hall].
  intros eq Hcd L Hctx.
  exact (check_defeq_full_sound Hves Hctx Hcd).
Qed.

Theorem classify_primitive_sound fuel env venv n ps ty body op :
  VEnvSound env venv ->
  classify_primitive fuel env n ps ty body = Accept (Some op) ->
  primitive_lookup n = Some op /\
  find_decl n env = None /\
  ps = [] /\
  ((primitive_is_text op = false /\
    primitive_check_nat_equations fuel env op body = Accept tt) \/
   (primitive_is_text op = true /\
    primitive_check_text_interface fuel env op = Accept tt)).
Proof.
  intros Hves Hcls.
  pose proof (classify_primitive_metadata_requires_certificate _ _ _ _ _ _ _ Hcls)
    as [Hlk Hcert].
  unfold classify_primitive in Hcls. rewrite Hlk in Hcls.
  destruct (find_decl n env) eqn:Hfind; simpl in Hcls; try discriminate.
  destruct (Nat.eqb (List.length ps) 0) eqn:Hlen; simpl in Hcls; try discriminate.
  apply Nat.eqb_eq in Hlen. destruct ps; simpl in Hlen; try lia.
  repeat split; try assumption.
Qed.

(* ========================================================================= *)
(* 4. Core Declaration Admission (`Declarations.v` -> `VEnvWF` & `VEnvSound`) *)
(* ========================================================================= *)

(* Freshness of `n` in `venv` whenever `n` is fresh in `env` *)
Definition VEnvNamesAligned (env : environment) (venv : VEnv) : Prop :=
  forall n, find_decl n env = None -> venv_constants venv n = None.

Lemma VEnvNamesAligned_empty : VEnvNamesAligned [] venv_empty.
Proof. intros n _. reflexivity. Qed.

Lemma venv_add_const_exists env n ci :
  venv_constants env n = None ->
  exists env',
    venv_add_const env n ci = Some env' /\
    venv_ordered env env' /\
    venv_constants env' n = Some ci.
Proof.
  intros Hnone. unfold venv_add_const. rewrite Hnone.
  eexists. split; [reflexivity | split].
  - constructor; simpl; [| intros df Hdf; exact Hdf].
    intros m ci0 Hm. destruct (name_eqb m n) eqn:Emn; [| exact Hm].
    apply name_eqb_eq in Emn. subst m. rewrite Hnone in Hm. discriminate.
  - simpl. rewrite name_eqb_refl. reflexivity.
Qed.

Ltac split_and := repeat match goal with |- _ /\ _ => split end.

(* Checked constant admission preserving `VEnvNamesAligned` *)
Theorem checked_constant_sound_aligned fuel env venv n ps ty body kind next :
  VEnvSound env venv ->
  VEnvNamesAligned env venv ->
  checked_constant fuel env n ps ty body kind = Accept next ->
  let d := {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
              decl_type := ty; decl_value := body; decl_kind_of := kind |} in
  next = d :: env /\
  find_decl n env = None /\
  exists ci venv',
    vc_uvars ci = List.length ps /\
    VTrExpr env venv ps vl_empty ty (vc_type ci) /\
    VTrExpr next venv' ps vl_empty ty (vc_type ci) /\
    VIsType venv' (vc_uvars ci) [] (vc_type ci) /\
    vclosed (vc_type ci) /\
    venv_ordered venv venv' /\
    VEnvWF venv' /\
    venv_constants venv' n = Some ci /\
    VEnvNamesAligned next venv' /\
    match body with
    | None => venv_defeqs venv' = venv_defeqs venv
    | Some val =>
        exists val',
          VTrExpr env venv ps vl_empty val val' /\
          VTrExpr next venv' ps vl_empty val val' /\
          VHasType venv' (vc_uvars ci) [] val' (vc_type ci) /\
          vclosed val' /\
          match kind with
          | DDefinition | DTheorem | DPrimitive _ =>
              venv_defeqs venv'
                {| vdf_uvars := vc_uvars ci;
                   vdf_lhs := VConst n (vlevel_params (vc_uvars ci));
                   vdf_rhs := val';
                   vdf_type := vc_type ci |}
          | _ => venv_defeqs venv' = venv_defeqs venv
          end
    end.
Proof.
  intros Hves Halign Hcc.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  unfold checked_constant in Hcc.
  destruct (check_header fuel env n ps ty) as [[]|err|why] eqn:Hhdr;
    simpl in Hcc; try discriminate.
  destruct (check_header_sound Hves Hhdr)
    as [Hfresh [Huniq [Hsc [ty' [u' [Hty_tr [Hty_u Hcwf]]]]]]].
  pose proof (Halign n Hfresh) as Hnone.
  set (ci := {| vc_uvars := List.length ps; vc_type := ty' |}).
  destruct (venv_add_const_exists ci Hnone) as [venv1 [Hadd1 [Hord1 Hc1]]].
  assert (Hwf1 : VEnvWF venv1) by (eapply VEnvWF_add_const; eassumption).
  assert (Hother1 : forall m, m <> n -> venv_constants venv1 m = venv_constants venv m).
  { intros m Hneq. unfold venv_add_const in Hadd1. rewrite Hnone in Hadd1.
    inversion Hadd1; subst venv1; simpl.
    destruct (name_eqb m n) eqn:Emn; [apply name_eqb_eq in Emn; contradiction | reflexivity]. }
  assert (Halign1 : forall d0, decl_name d0 = n -> VEnvNamesAligned (d0 :: env) venv1).
  { intros d0 Hd0 m Hm. simpl in Hm. rewrite Hd0 in Hm.
    destruct (name_eqb m n) eqn:Emn; [discriminate |].
    rewrite Hother1 by (intro Heq; subst; rewrite name_eqb_refl in Emn; discriminate).
    exact (Halign m Hm). }
  destruct body as [val|].
  - destruct (scoped 0 val) eqn:Hscv; [|discriminate].
    destruct (check fuel env ps empty_context val ty) as [[]|err|why] eqn:Hchk;
      simpl in Hcc; try discriminate.
    inversion Hcc; subst next; clear Hcc.
    pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
    destruct (check_full_sound Hves Hctx Hchk) as [val' [ty2' [u2' [Hval_tr [Hty2_tr [_ Hval_ty2]]]]]].
    pose proof (VTrExpr_uniq Hves (VTrCtx_to_VLCtxWF Hctx) Hty2_tr Hty_tr) as Hty_eq.
    assert (Hval_ty : VHasType venv (List.length ps) [] val' ty')
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact I | exact Hval_ty2 | exact Hty_eq]).
    assert (Hval_ty1 : VHasType venv1 (List.length ps) [] val' ty')
      by (eapply VEnvOrdered_preserve_VHasType; [exact Hord1 | exact Hval_ty]).
    assert (Hval_cl : vclosed val')
      by (destruct (VIsDefEq_closedN Hcl Hval_ty (I : VCtxClosed [])) as [Hv _]; exact Hv).
    assert (Hty_cl : vclosed ty') by (exact (proj2 Hcwf)).
    set (d := {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
                 decl_type := ty; decl_value := Some val; decl_kind_of := kind |}).
    pose proof (@env_extends_cons_fresh env d Hfresh) as Hext.
    split; [reflexivity | split; [exact Hfresh |]].
    destruct kind eqn:Hkind.
    all: try (
      exists ci, venv1; split_and;
      [ reflexivity
      | exact Hty_tr
      | eapply VTrExpr_extend_env; [exact Hext | exact Hord1 | exact Hty_tr]
      | exists u'; eapply VEnvOrdered_preserve_VHasType; [exact Hord1 | exact Hty_u]
      | exact Hty_cl
      | exact Hord1
      | exact Hwf1
      | exact Hc1
      | exact (Halign1 d eq_refl)
      | exists val'; split_and;
        [ exact Hval_tr
        | eapply VTrExpr_extend_env; [exact Hext | exact Hord1 | exact Hval_tr]
        | exact Hval_ty1
        | exact Hval_cl
        | unfold venv_add_const in Hadd1; rewrite Hnone in Hadd1;
          inversion Hadd1; reflexivity ] ]).
    all: (
      set (dv := {| vdv_const := {| vcv_name := n; vcv_const := ci |}; vdv_value := val' |});
      assert (Hdfwf : VDefEqWF venv1 (vdef_to_defeq dv))
        by (apply VDefValWF_to_VDefEqWF; [exact Hwf1 | exact Hc1 | exact Hval_ty1]);
      set (venv2 := venv_add_defeq venv1 (vdef_to_defeq dv));
      assert (Hord12 : venv_ordered venv1 venv2) by (apply venv_add_defeq_ordered);
      assert (Hord2 : venv_ordered venv venv2) by (eapply venv_ordered_trans; eassumption);
      assert (Hwf2 : VEnvWF venv2) by (eapply VEnvWF_add_defeq; [exact Hwf1 | exact Hdfwf]);
      exists ci, venv2; split_and;
      [ reflexivity
      | exact Hty_tr
      | eapply VTrExpr_extend_env; [exact Hext | exact Hord2 | exact Hty_tr]
      | exists u'; eapply VEnvOrdered_preserve_VHasType; [exact Hord2 | exact Hty_u]
      | exact Hty_cl
      | exact Hord2
      | exact Hwf2
      | exact Hc1
      | exact (Halign1 d eq_refl)
      | exists val'; split_and;
        [ exact Hval_tr
        | eapply VTrExpr_extend_env; [exact Hext | exact Hord2 | exact Hval_tr]
        | eapply VEnvOrdered_preserve_VHasType; [exact Hord12 | exact Hval_ty1]
        | exact Hval_cl
        | left; reflexivity ] ]).
  - inversion Hcc; subst next; clear Hcc.
    set (d := {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
                 decl_type := ty; decl_value := None; decl_kind_of := kind |}).
    pose proof (@env_extends_cons_fresh env d Hfresh) as Hext.
    split; [reflexivity | split; [exact Hfresh |]].
    exists ci, venv1. split_and;
      [ reflexivity
      | exact Hty_tr
      | eapply VTrExpr_extend_env; [exact Hext | exact Hord1 | exact Hty_tr]
      | exists u'; eapply VEnvOrdered_preserve_VHasType; [exact Hord1 | exact Hty_u]
      | exact (proj2 Hcwf)
      | exact Hord1
      | exact Hwf1
      | exact Hc1
      | exact (Halign1 d eq_refl)
      | unfold venv_add_const in Hadd1; rewrite Hnone in Hadd1; inversion Hadd1; reflexivity ].
Qed.

Theorem admit_sound fuel env venv input next :
  VEnvSound env venv ->
  VEnvNamesAligned env venv ->
  admit fuel env input = Accept next ->
  exists d ci venv',
    next = d :: env /\
    find_decl (decl_name d) env = None /\
    vc_uvars ci = List.length (decl_params d) /\
    VTrExpr next venv' (decl_params d) vl_empty (decl_type d) (vc_type ci) /\
    VIsType venv' (vc_uvars ci) [] (vc_type ci) /\
    vclosed (vc_type ci) /\
    venv_ordered venv venv' /\
    VEnvWF venv' /\
    venv_constants venv' (decl_name d) = Some ci /\
    VEnvNamesAligned next venv' /\
    match decl_kind_of d, decl_value d with
    | DDefinition, Some val | DTheorem, Some val | DPrimitive _, Some val =>
        exists val',
          VTrExpr next venv' (decl_params d) vl_empty val val' /\
          VHasType venv' (vc_uvars ci) [] val' (vc_type ci) /\
          vclosed val' /\
          venv_defeqs venv'
            {| vdf_uvars := vc_uvars ci;
               vdf_lhs := VConst (decl_name d) (vlevel_params (vc_uvars ci));
               vdf_rhs := val';
               vdf_type := vc_type ci |} /\
          (decl_kind_of d = DTheorem -> VHasType venv' (vc_uvars ci) [] (vc_type ci) (VSort VLZero))
    | _, _ => True
    end.
Proof.
  intros Hves Halign Hadm.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  destruct input as [n ps ty unsafe | hints n ps ty body safety | n ps ty body | n ps ty body unsafe |];
    cbn [admit] in Hadm; try discriminate.
  - (* InputAxiom *)
    destruct unsafe; [discriminate |].
    destruct (name_mem n reserved_names); [discriminate |].
    destruct (checked_constant_sound_aligned Hves Halign Hadm)
      as [Hnext [Hfresh [ci [venv' [Huv [_ [Hty_tr [Hty_is [Hty_cl [Hord [Hwf' [Hc' [Halign' _]]]]]]]]]]]]].
    eexists _, ci, venv'.
    split_and; try eassumption; exact I.
  - (* InputDefinition *)
    destruct safety; try discriminate.
    destruct (check_header fuel env n ps ty) as [[]|err|why] eqn:Hhdr;
      simpl in Hadm; try discriminate.
    destruct (scoped 0 body) eqn:Hscb; simpl in Hadm; [|discriminate].
    destruct (check fuel env ps empty_context body ty) as [[]|err|why] eqn:Hchk;
      simpl in Hadm; try discriminate.
    destruct (classify_primitive fuel env n ps ty body) as [prim|err|why] eqn:Hprim;
      simpl in Hadm; try discriminate.
    inversion Hadm; subst next; clear Hadm.
    destruct (check_header_sound Hves Hhdr)
      as [Hfresh [Huniq [Hsc [ty' [u' [Hty_tr [Hty_u Hcwf]]]]]]].
    pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
    destruct (check_full_sound Hves Hctx Hchk)
      as [val' [ty2' [u2' [Hval_tr [Hty2_tr [_ Hval_ty2]]]]]].
    pose proof (VTrExpr_uniq Hves (VTrCtx_to_VLCtxWF Hctx) Hty2_tr Hty_tr) as Hty_eq.
    assert (Hval_ty : VHasType venv (List.length ps) [] val' ty')
      by (eapply VHasType_conv_U; [exact Hwf | exact Hinj | exact I | exact Hval_ty2 | exact Hty_eq]).
    assert (Hval_cl : vclosed val')
      by (destruct (VIsDefEq_closedN Hcl Hval_ty (I : VCtxClosed [])) as [Hv _]; exact Hv).
    pose proof (Halign n Hfresh) as Hnone.
    set (ci := {| vc_uvars := List.length ps; vc_type := ty' |}).
    destruct (venv_add_const_exists ci Hnone) as [venv1 [Hadd1 [Hord1 Hc1]]].
    assert (Hwf1 : VEnvWF venv1) by (eapply VEnvWF_add_const; eassumption).
    assert (Hval_ty1 : VHasType venv1 (List.length ps) [] val' ty')
      by (eapply VEnvOrdered_preserve_VHasType; [exact Hord1 | exact Hval_ty]).
    set (dv := {| vdv_const := {| vcv_name := n; vcv_const := ci |}; vdv_value := val' |}).
    assert (Hdfwf : VDefEqWF venv1 (vdef_to_defeq dv))
      by (apply VDefValWF_to_VDefEqWF; [exact Hwf1 | exact Hc1 | exact Hval_ty1]).
    set (venv2 := venv_add_defeq venv1 (vdef_to_defeq dv)).
    assert (Hord12 : venv_ordered venv1 venv2) by (apply venv_add_defeq_ordered).
    assert (Hord2 : venv_ordered venv venv2) by (eapply venv_ordered_trans; eassumption).
    assert (Hwf2 : VEnvWF venv2) by (eapply VEnvWF_add_defeq; [exact Hwf1 | exact Hdfwf]).
    set (knd := match prim with Some p => DPrimitive p | None => DDefinition end).
    set (d := {| decl_hints := hints; decl_name := n; decl_params := ps;
                 decl_type := ty; decl_value := Some body; decl_kind_of := knd |}).
    pose proof (@env_extends_cons_fresh env d Hfresh) as Hext.
    assert (Halign2 : VEnvNamesAligned (d :: env) venv2).
    { intros m Hm. simpl in Hm. destruct (name_eqb m n) eqn:Emn; [discriminate |].
      unfold venv2, venv_add_defeq; simpl.
      unfold venv_add_const in Hadd1. rewrite Hnone in Hadd1.
      inversion Hadd1; simpl. rewrite Emn. exact (Halign m Hm). }
    exists d, ci, venv2.
    split; [reflexivity | split; [exact Hfresh | split; [reflexivity |
    split; [eapply VTrExpr_extend_env; [exact Hext | exact Hord2 | exact Hty_tr] |
    split; [exists u'; eapply VEnvOrdered_preserve_VHasType; [exact Hord2 | exact Hty_u] |
    split; [exact (proj2 Hcwf) | split; [exact Hord2 | split; [exact Hwf2 |
    split; [exact Hc1 | split; [exact Halign2 |]]]]]]]]]].
    destruct prim as [p|]; simpl;
      (exists val'; split_and;
       [ eapply VTrExpr_extend_env; [exact Hext | exact Hord2 | exact Hval_tr]
       | eapply VEnvOrdered_preserve_VHasType; [exact Hord12 | exact Hval_ty1]
       | exact Hval_cl
       | left; reflexivity
       | intros Hdisc; discriminate ]).
  - (* InputTheorem *)
    destruct (name_mem n reserved_names); [discriminate |].
    destruct (check_header fuel env n ps ty) as [[]|err|why] eqn:Hhdr;
      simpl in Hadm; try discriminate.
    destruct (check_proposition fuel env ps ty) as [[]|err|why] eqn:Hprop;
      simpl in Hadm; try discriminate.
    destruct (checked_constant_sound_aligned Hves Halign Hadm)
      as [Hnext [Hfresh [ci [venv' [Huv [Hty_old [Hty_tr [Hty_is [Hty_cl [Hord [Hwf' [Hc' [Halign'
            [val' [Hval_old [Hval_tr [Hval_ty [Hval_cl Hdf]]]]]]]]]]]]]]]]]].
    destruct (check_proposition_sound Hves Hprop) as [ty_p [Htyp_tr Htyp_prop]].
    pose proof (VTrExpr_empty_ctx_wf env ps Hwf) as Hctx.
    pose proof (VTrExpr_uniq Hves (VTrCtx_to_VLCtxWF Hctx) Htyp_tr Hty_old) as Hpeq.
    assert (Hty_prop : VHasType venv (List.length ps) [] (vc_type ci) (VSort VLZero))
      by (eapply VIsDefEqU_hasType_r; [exact Hwf | exact Hinj | exact I | exact Htyp_prop | exact Hpeq]).
    eexists _, ci, venv'.
    split; [exact Hnext | split; [exact Hfresh | split; [exact Huv |
    split; [exact Hty_tr | split; [exact Hty_is | split; [exact Hty_cl |
    split; [exact Hord | split; [exact Hwf' | split; [exact Hc' | split; [exact Halign' |]]]]]]]]]].
    simpl. exists val'.
    split; [exact Hval_tr | split; [exact Hval_ty | split; [exact Hval_cl | split; [exact Hdf |]]]].
    intros _. rewrite Huv. eapply VEnvOrdered_preserve_VHasType; [exact Hord | exact Hty_prop].
  - (* InputOpaque *)
    destruct unsafe; [discriminate |].
    destruct (name_mem n reserved_names); [discriminate |].
    destruct (checked_constant_sound_aligned Hves Halign Hadm)
      as [Hnext [Hfresh [ci [venv' [Huv [_ [Hty_tr [Hty_is [Hty_cl [Hord [Hwf' [Hc' [Halign' _]]]]]]]]]]]]].
    eexists _, ci, venv'.
    split_and; try eassumption; exact I.
Qed.

(* Pure-constant environments (no inductives/constructors/recursors/quotients/primitives):
   ALL 18 fields of `VEnvSound` are preserved across `admit` and `check_declarations`
   with ONLY `DefEqInjectivity venv'`! *)
Definition PureConstEnv (env : environment) : Prop :=
  forall n d, find_decl n env = Some d ->
    match decl_kind_of d with
    | DAssumption | DDefinition | DTheorem | DOpaque | DUnsupported | DUnsafe _ | DPartial => True
    | _ => False
    end.

Lemma PureConstEnv_empty : PureConstEnv [].
Proof. intros n d H. discriminate. Qed.

Lemma PureConstEnv_no_ind env owner :
  PureConstEnv env -> core_inductive env owner = None.
Proof.
  intros Hpure. unfold core_inductive.
  destruct (find_decl owner env) as [d|] eqn:Hf; [|reflexivity].
  specialize (Hpure _ _ Hf). destruct (decl_kind_of d); try contradiction; reflexivity.
Qed.

Lemma PureConstEnv_no_ctor env cn :
  PureConstEnv env -> core_constructor env cn = None.
Proof.
  intros Hpure. unfold core_constructor.
  destruct (find_decl cn env) as [d|] eqn:Hf; [|reflexivity].
  specialize (Hpure _ _ Hf). destruct (decl_kind_of d); try contradiction; reflexivity.
Qed.

Lemma PureConstEnv_prims env venv :
  PureConstEnv env -> HasPrimitives env venv.
Proof.
  intros Hpure.
  assert (Hn : core_nat_ready env = false).
  { unfold core_nat_ready. destruct (find_decl core_nat_name env) as [d|] eqn:Hf; [|reflexivity].
    specialize (Hpure _ _ Hf). destruct (decl_kind_of d); try contradiction; reflexivity. }
  assert (Hb : core_bool_ready env = false).
  { unfold core_bool_ready. destruct (find_decl core_bool_name env) as [d|] eqn:Hf; [|reflexivity].
    specialize (Hpure _ _ Hf). destruct (decl_kind_of d); try contradiction; reflexivity. }
  assert (Hs : core_string_ready env = false).
  { unfold core_string_ready. destruct (find_decl core_char_of_nat env) as [dc|] eqn:Hfc; [|reflexivity].
    destruct (find_decl core_string_of_list env); [|reflexivity].
    specialize (Hpure _ _ Hfc). destruct (decl_kind_of dc); try contradiction; reflexivity. }
  constructor;
    try (rewrite Hn; discriminate);
    try (rewrite Hb; discriminate);
    try (rewrite Hs; discriminate).
Qed.

Theorem VEnvSound_pure_admit fuel env venv input next :
  PureConstEnv env ->
  VEnvSound env venv ->
  VEnvNamesAligned env venv ->
  admit fuel env input = Accept next ->
  (forall n ps ty body hints, input = InputDefinition hints n ps ty body InputSafe ->
     classify_primitive fuel env n ps ty body = Accept None) ->
  exists venv',
    PureConstEnv next /\
    venv_ordered venv venv' /\
    VEnvWF venv' /\
    VEnvNamesAligned next venv' /\
    (DefEqInjectivity venv' -> VEnvSound next venv').
Proof.
  intros Hpure Hves Halign Hadm Hnoprim.
  destruct (admit_sound Hves Halign Hadm)
    as [d [ci [venv' [Hnext [Hfresh [Huv [Hty_tr [Hty_is [Hty_cl [Hord [Hwf' [Hc' [Halign' Hval]]]]]]]]]]]]].
  subst next.
  assert (Hkind_pure :
    match decl_kind_of d with
    | DAssumption | DDefinition | DTheorem | DOpaque | DUnsupported | DUnsafe _ | DPartial => True
    | _ => False
    end).
  { destruct input as [n ps ty unsafe | hints n ps ty body safety | n ps ty body | n ps ty body unsafe |];
      cbn [admit] in Hadm; try discriminate.
    - destruct unsafe; [discriminate |]. destruct (name_mem n reserved_names); [discriminate |].
      unfold checked_constant in Hadm.
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; subst d; exact I.
    - destruct safety; try discriminate.
      specialize (Hnoprim _ _ _ _ _ eq_refl).
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (scoped 0 body); simpl in Hadm; try discriminate.
      destruct (check fuel env ps empty_context body ty) as [[]| |]; simpl in Hadm; try discriminate.
      rewrite Hnoprim in Hadm; simpl in Hadm.
      inversion Hadm; subst d; exact I.
    - destruct (name_mem n reserved_names); [discriminate |].
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_proposition fuel env ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      unfold checked_constant in Hadm.
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (scoped 0 body); simpl in Hadm; try discriminate.
      destruct (check fuel env ps empty_context body ty) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; subst d; exact I.
    - destruct unsafe; [discriminate |]. destruct (name_mem n reserved_names); [discriminate |].
      unfold checked_constant in Hadm.
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (scoped 0 body); simpl in Hadm; try discriminate.
      destruct (check fuel env ps empty_context body ty) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; subst d; exact I. }
  assert (Hpure' : PureConstEnv (d :: env)).
  { intros n0 d0 Hf0. simpl in Hf0.
    destruct (name_eqb n0 (decl_name d)); [inversion Hf0; subst d0; exact Hkind_pure | exact (Hpure _ _ Hf0)]. }
  assert (Hext : env_extends env (d :: env)) by (exact (@env_extends_cons_fresh env d Hfresh)).
  exists venv'. split_and; try assumption.
  intros Hinj'.
  constructor;
    try exact Hwf';
    try exact Hinj';
    try (apply PureConstEnv_prims; exact Hpure').
  - (* ves_ind_inj *)
    intros U G ind1 ind2 i1 i2 us1 us2 a1 a2 _ Hi1.
    rewrite PureConstEnv_no_ind in Hi1 by exact Hpure'. discriminate.
  - (* ves_constants *)
    intros n0 d0 Hf0. simpl in Hf0.
    destruct (name_eqb n0 (decl_name d)) eqn:En.
    + apply name_eqb_eq in En. subst n0. inversion Hf0; subst d0; clear Hf0.
      destruct (decl_kind_of d); try exact I;
        exists ci; split_and; assumption.
    + pose proof (ves_constants Hves Hf0) as Hc0.
      destruct (decl_kind_of d0); try exact I;
        (destruct Hc0 as [ci0 [Hci0 [Huv0 [Ht0 [His0 Hcl0]]]]];
         exists ci0; split_and;
         [ exact (venv_ord_const Hord Hci0)
         | exact Huv0
         | eapply VTrExpr_extend_env; [exact Hext | exact Hord | exact Ht0]
         | eapply VEnvOrdered_preserve_VIsType; [exact Hord | exact His0]
         | exact Hcl0 ]).
  - (* ves_delta *)
    intros n0 d0 val0 Hf0 Hk0 Hv0. simpl in Hf0.
    destruct (name_eqb n0 (decl_name d)) eqn:En.
    + apply name_eqb_eq in En. subst n0. inversion Hf0; subst d0; clear Hf0.
      rewrite Hv0 in Hval.
      destruct (decl_kind_of d); try contradiction;
        destruct Hval as [val' [Hvt [_ [Hvc [Hdf _]]]]];
        exists ci, val'; split_and; assumption.
    + destruct (ves_delta Hves Hf0 Hk0 Hv0) as [ci0 [val' [Hci0 [Huv0 [Hvt [Hvc Hdf]]]]]].
      exists ci0, val'; split_and;
        [ exact (venv_ord_const Hord Hci0)
        | exact Huv0
        | eapply VTrExpr_extend_env; [exact Hext | exact Hord | exact Hvt]
        | exact Hvc
        | exact (venv_ord_defeq Hord Hdf) ].
  - (* ves_quot_red *)
    intros U G n0 d0 cn cd us cus args rep idx fn a1 a2 _ Hf0 Hk0.
    specialize (Hpure' _ _ Hf0).
    destruct Hk0 as [[Hk0 _]|[Hk0 _]]; rewrite Hk0 in Hpure'; contradiction.
  - (* ves_recursor_iota *)
    intros U G rname d0 info rus args mj own cn ci0 cus fs rule rhs_v _ Hf0 Hk0.
    specialize (Hpure' _ _ Hf0). rewrite Hk0 in Hpure'; contradiction.
  - (* ves_recursor_rhs *)
    intros rname d0 info rule Hf0 Hk0.
    specialize (Hpure' _ _ Hf0). rewrite Hk0 in Hpure'; contradiction.
  - (* ves_recursor_k_fields *)
    intros rname d0 info own oinfo ctor ci0 Hf0 Hk0.
    specialize (Hpure' _ _ Hf0). rewrite Hk0 in Hpure'; contradiction.
  - (* ves_proj_const *)
    intros own info ctor c d0 idx Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_proj_iota *)
    intros U G own info ctor c d0 idx us cus ps0 idxs fs fv sv _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_proj_telescope *)
    intros U G own info ctor c d0 ci_c idx us ps0 idxs sv usort typ fty mp _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_struct_eta *)
    intros U G own info ctor c d0 us ps0 sv _ _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_ctor_type_head *)
    intros U G cn ci0 cus args T _ Hc0.
    rewrite PureConstEnv_no_ctor in Hc0 by exact Hpure'. discriminate.
  - (* ves_ind_shape *)
    intros own info d_ind ctor c d_ctor Hf0 Hk0.
    specialize (Hpure' _ _ Hf0). rewrite Hk0 in Hpure'; contradiction.
  - (* ves_ind_type_arity *)
    intros U G own info us args usort _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_ctor_params_wf *)
    intros U G own info ctor c d0 us ps0 idxs T _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
  - (* ves_ind_weakN *)
    intros U n0 k G G' own info T0 us args _ _ Hi.
    rewrite PureConstEnv_no_ind in Hi by exact Hpure'. discriminate.
Qed.

(* ========================================================================= *)
(* 5. Safety Isolation (`Safety.v` & `InductiveSafety.v`)                    *)
(* ========================================================================= *)

Definition is_restricted_kind (k : decl_kind) : Prop :=
  match k with DUnsafe _ | DPartial => True | _ => False end.

Lemma find_decl_cons_restricted_ind env d owner :
  find_decl (decl_name d) env = None ->
  is_restricted_kind (decl_kind_of d) ->
  core_inductive (d :: env) owner = core_inductive env owner.
Proof.
  intros Hfresh Hres. unfold core_inductive; simpl.
  destruct (name_eqb owner (decl_name d)) eqn:Eo.
  - apply name_eqb_eq in Eo. subst owner. rewrite Hfresh.
    destruct (decl_kind_of d); try contradiction; reflexivity.
  - reflexivity.
Qed.

Lemma find_decl_cons_restricted_ctor env d cn :
  find_decl (decl_name d) env = None ->
  is_restricted_kind (decl_kind_of d) ->
  core_constructor (d :: env) cn = core_constructor env cn.
Proof.
  intros Hfresh Hres. unfold core_constructor; simpl.
  destruct (name_eqb cn (decl_name d)) eqn:Ec.
  - apply name_eqb_eq in Ec. subst cn. rewrite Hfresh.
    destruct (decl_kind_of d); try contradiction; reflexivity.
  - reflexivity.
Qed.

(* Adding a fresh restricted (`DUnsafe _`/`DPartial`) declaration leaves the
   ENTIRE `VEnvSound` relation completely intact on the SAME `venv`! *)
Theorem VEnvSound_prepend_restricted env venv d :
  VEnvSound env venv ->
  find_decl (decl_name d) env = None ->
  is_restricted_kind (decl_kind_of d) ->
  VEnvSound (d :: env) venv.
Proof.
  intros Hves Hfresh Hres.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (@env_extends_cons_fresh env d Hfresh) as Hext.
  assert (Hind_eq : forall owner, core_inductive (d :: env) owner = core_inductive env owner)
    by (intros; apply find_decl_cons_restricted_ind; assumption).
  assert (Hctor_eq : forall cn, core_constructor (d :: env) cn = core_constructor env cn)
    by (intros; apply find_decl_cons_restricted_ctor; assumption).
  assert (Hcs_eq : forall n p i f ty,
    core_ctor_shape (d :: env) n p i f ty = core_ctor_shape env n p i f ty).
  { intros n p i f ty. unfold core_ctor_shape; simpl.
    destruct (name_eqb n (decl_name d)) eqn:En; [|reflexivity].
    apply name_eqb_eq in En. subst n. rewrite Hfresh.
    destruct (decl_kind_of d); try contradiction; reflexivity. }
  assert (Hnat_eq : core_nat_ready (d :: env) = core_nat_ready env).
  { unfold core_nat_ready; cbn [find_decl].
    destruct (name_eqb core_nat_name (decl_name d)) eqn:En.
    - apply name_eqb_eq in En. rewrite En, Hfresh.
      destruct (decl_kind_of d); try contradiction; reflexivity.
    - destruct (find_decl core_nat_name env) as [d0|]; [|reflexivity].
      destruct (decl_kind_of d0); try reflexivity.
      rewrite !Hcs_eq. reflexivity. }
  assert (Hbool_eq : core_bool_ready (d :: env) = core_bool_ready env).
  { unfold core_bool_ready; cbn [find_decl].
    destruct (name_eqb core_bool_name (decl_name d)) eqn:En.
    - apply name_eqb_eq in En. rewrite En, Hfresh.
      destruct (decl_kind_of d); try contradiction; reflexivity.
    - destruct (find_decl core_bool_name env) as [d0|]; [|reflexivity].
      destruct (decl_kind_of d0); try reflexivity.
      rewrite !Hcs_eq. reflexivity. }
  assert (Hstr_eq : core_string_ready (d :: env) = core_string_ready env).
  { unfold core_string_ready; cbn [find_decl].
    destruct (name_eqb core_char_of_nat (decl_name d)) eqn:Ec.
    - apply name_eqb_eq in Ec. rewrite Ec, Hfresh.
      destruct (decl_kind_of d); try contradiction;
        destruct (if name_eqb core_string_of_list (decl_name d) then Some d
                  else find_decl core_string_of_list env); reflexivity.
    - destruct (name_eqb core_string_of_list (decl_name d)) eqn:Es.
      + apply name_eqb_eq in Es. rewrite Es, Hfresh.
        destruct (find_decl core_char_of_nat env) as [dc|]; [|reflexivity].
        destruct (decl_kind_of dc), (decl_kind_of d); try contradiction; try reflexivity;
          destruct p; reflexivity.
      + destruct (find_decl core_char_of_nat env) as [dc|]; [|reflexivity].
        destruct (find_decl core_string_of_list env) as [ds|]; [|reflexivity].
        destruct (decl_kind_of dc), (decl_kind_of ds); try reflexivity.
        destruct p, p0; try reflexivity; exact Hnat_eq. }
  assert (Hstruct_eq : forall owner, core_structure (d :: env) owner = core_structure env owner)
    by (intros; unfold core_structure; rewrite Hind_eq; reflexivity).
  assert (Hfind_nonres : forall n d0,
    find_decl n (d :: env) = Some d0 ->
    ~ is_restricted_kind (decl_kind_of d0) ->
    find_decl n env = Some d0).
  { intros n d0 Hf Hnr. simpl in Hf.
    destruct (name_eqb n (decl_name d)) eqn:En; [inversion Hf; subst d0; contradiction | exact Hf]. }
  assert (Htr_back : forall ps L e e',
    VTrExprS (d :: env) venv ps L e e' -> VTrExprS env venv ps L e e').
  { intros ps L e e' H. induction H.
    - eapply VTrExprS_bvar; eassumption.
    - eapply VTrExprS_fvar; eassumption.
    - constructor; assumption.
    - eapply VTrExprS_const; eassumption.
    - eapply VTrExprS_app; eassumption.
    - eapply VTrExprS_lam; eassumption.
    - eapply VTrExprS_pi; eassumption.
    - eapply VTrExprS_let; eassumption.
    - eapply VTrExprS_proj; [exact IHVTrExprS |].
      destruct H0 as [info ctor c d0 us ps0 idxs Hi Hc Hd Hk Hlt Hlp Hli Hw Hlu Hst Hpv Hty].
      rewrite Hind_eq in Hi.
      assert (Hd' : find_decl ctor env = Some d0)
        by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hc'; exact Hc']).
      eapply VTrProj_intro; eassumption.
    - rewrite Hnat_eq in H. eapply VTrExprS_natlit; eassumption.
    - rewrite Hstr_eq in H. eapply VTrExprS_strlit; eassumption.
    - constructor; exact IHVTrExprS. }
  assert (Hpt_back : forall U G owner us ps0 sv mp skip idx ty fty,
    VProjTelescope (d :: env) venv U G owner us ps0 sv mp skip idx ty fty ->
    VProjTelescope env venv U G owner us ps0 sv mp skip idx ty fty).
  { intros U G owner us ps0 sv mp skip idx ty fty H.
    induction H; [eapply VPT_zero; eassumption | eapply VPT_succ; eassumption]. }
  assert (Hproj_fwd : forall U G owner idx sv pv fty,
    VTrProj env venv U G owner idx sv pv fty ->
    VTrProj (d :: env) venv U G owner idx sv pv fty)
    by (intros; eapply VTrProj_extend_env; [exact Hext | apply venv_ordered_refl | eassumption]).
  constructor.
  - exact Hwf.
  - exact (ves_inj Hves).
  - (* ves_ind_inj *)
    intros U G i1 i2 info1 info2 us1 us2 a1 a2 HG Hi1 Hi2 Heq.
    rewrite Hind_eq in Hi1, Hi2. exact (ves_ind_inj Hves HG Hi1 Hi2 Heq).
  - (* ves_prims *)
    constructor.
    + rewrite Hnat_eq. exact (hp_nat (ves_prims Hves)).
    + rewrite Hbool_eq. exact (hp_bool (ves_prims Hves)).
    + rewrite Hstr_eq. exact (hp_string (ves_prims Hves)).
    + intros n d0 Hn Hf Hk a. rewrite Hnat_eq in Hn.
      eapply hp_pred; [exact (ves_prims Hves) | exact Hn | | exact Hk].
      eapply Hfind_nonres; [exact Hf | rewrite Hk; intro Hc'; exact Hc'].
    + intros n d0 op Hn Hf Hk a b res rty Hsp Hb.
      rewrite Hnat_eq in Hn. rewrite Hbool_eq in Hb.
      eapply hp_binary; [exact (ves_prims Hves) | exact Hn | | exact Hk | exact Hsp | exact Hb].
      eapply Hfind_nonres; [exact Hf | rewrite Hk; intro Hc'; exact Hc'].
  - (* ves_constants *)
    intros n d0 Hf. simpl in Hf.
    destruct (name_eqb n (decl_name d)) eqn:En.
    + inversion Hf; subst d0. destruct (decl_kind_of d); try contradiction; exact I.
    + pose proof (ves_constants Hves Hf) as Hc.
      destruct (decl_kind_of d0); try exact I;
        (destruct Hc as [ci [Hci [Huv [Htr [His Hcl]]]]];
         exists ci; split_and; try assumption;
         eapply VTrExpr_extend_env; [exact Hext | apply venv_ordered_refl | exact Htr]).
  - (* ves_delta *)
    intros n d0 val Hf Hk Hv.
    assert (Hf' : find_decl n env = Some d0).
    { eapply Hfind_nonres; [exact Hf | destruct (decl_kind_of d0); try contradiction; intro Hc; exact Hc]. }
    destruct (ves_delta Hves Hf' Hk Hv) as [ci [val' [Hci [Huv [Htr [Hcl Hdf]]]]]].
    exists ci, val'; split_and; try assumption.
    eapply VTrExpr_extend_env; [exact Hext | apply venv_ordered_refl | exact Htr].
  - (* ves_quot_red *)
    intros U G n d0 cn cd us cus args rep idx fn a1 a2 HG Hf Hk Hfc Hkc Hm Hfn Hwfe.
    assert (Hf' : find_decl n env = Some d0).
    { eapply Hfind_nonres; [exact Hf | destruct Hk as [[Hk _]|[Hk _]]; rewrite Hk; intro Hx; exact Hx]. }
    assert (Hfc' : find_decl cn env = Some cd)
      by (eapply Hfind_nonres; [exact Hfc | rewrite Hkc; intro Hx; exact Hx]).
    eapply ves_quot_red; eassumption.
  - (* ves_recursor_iota *)
    intros U G rname d0 info rus args mj own cn ci cus fs rule rhs_v HG Hf Hk Hmj Hown Hmaj Hrule Hci Ho Hlf Hnf Hlu Hwus Hrhs Hwfe.
    assert (Hf' : find_decl rname env = Some d0)
      by (eapply Hfind_nonres; [exact Hf | rewrite Hk; intro Hx; exact Hx]).
    rewrite Hctor_eq in Hci.
    assert (Hrhs' : VTrExpr env venv (decl_params d0) vl_empty (rule_rhs rule) rhs_v)
      by (destruct Hrhs as [e0 [He0 Heq]]; exists e0; split; [apply Htr_back; exact He0 | exact Heq]).
    eapply ves_recursor_iota; eassumption.
  - (* ves_recursor_rhs *)
    intros rname d0 info rule Hf Hk Hin.
    assert (Hf' : find_decl rname env = Some d0)
      by (eapply Hfind_nonres; [exact Hf | rewrite Hk; intro Hx; exact Hx]).
    destruct (ves_recursor_rhs Hves Hf' Hk Hin) as [rhs_v Hrhs].
    exists rhs_v. eapply VTrExpr_extend_env; [exact Hext | apply venv_ordered_refl | exact Hrhs].
  - (* ves_recursor_k_fields *)
    intros rname d0 info own oinfo ctor ci Hf Hk Hrk Hown Hi Hct Hci.
    assert (Hf' : find_decl rname env = Some d0)
      by (eapply Hfind_nonres; [exact Hf | rewrite Hk; intro Hx; exact Hx]).
    rewrite Hind_eq in Hi. rewrite Hctor_eq in Hci.
    eapply ves_recursor_k_fields; eassumption.
  - (* ves_proj_const *)
    intros own info ctor c d0 idx Hi Hct Hd Hk Hlt.
    rewrite Hind_eq in Hi.
    assert (Hd' : find_decl ctor env = Some d0)
      by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hx; exact Hx]).
    eapply ves_proj_const; eassumption.
  - (* ves_proj_iota *)
    intros U G own info ctor c d0 idx us cus ps0 idxs fs fval sv HG Hi Hct Hd Hk.
    rewrite Hind_eq in Hi.
    assert (Hd' : find_decl ctor env = Some d0)
      by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hx; exact Hx]).
    eapply ves_proj_iota; eassumption.
  - (* ves_proj_telescope *)
    intros U G own info ctor c d0 ci_c idx us ps0 idxs sv usort typ fty mp HG Hi Hct Hd Hk Hcic Hlt Hlp Hli Hwus Hlu Hsv Hown Hmp Hctyp Hpt.
    rewrite Hind_eq in Hi.
    assert (Hd' : find_decl ctor env = Some d0)
      by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hx; exact Hx]).
    eapply ves_proj_telescope; [exact Hves | exact HG | exact Hi | exact Hct | exact Hd' | exact Hk |
      exact Hcic | exact Hlt | exact Hlp | exact Hli | exact Hwus | exact Hlu |
      exact Hsv | exact Hown | exact Hmp | exact Hctyp | exact (Hpt_back _ _ _ _ _ _ _ _ _ _ _ Hpt)].
  - (* ves_struct_eta *)
    intros U G own info ctor c d0 us ps0 sv HG Hst Hi Hct Hd Hk Hlp Hcnp Hwus Hlu Hsv.
    rewrite Hstruct_eq in Hst. rewrite Hind_eq in Hi.
    assert (Hd' : find_decl ctor env = Some d0)
      by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hx; exact Hx]).
    destruct (ves_struct_eta Hves HG Hst Hi Hct Hd' Hk Hlp Hcnp Hwus Hlu Hsv) as [Hps Heta].
    split; [| exact Heta].
    intros i Hi_lt. destruct (Hps i Hi_lt) as [fty Hp]. exists fty. apply Hproj_fwd. exact Hp.
  - (* ves_ctor_type_head *)
    intros U G cn ci cus args T HG Hc Hlen Ht.
    rewrite Hctor_eq in Hc.
    destruct (ves_ctor_type_head Hves HG Hc Hlen Ht) as [oinfo [idxs [Hi [Hcnp [Hli Heq]]]]].
    exists oinfo, idxs. rewrite Hind_eq. split_and; assumption.
  - (* ves_ind_shape *)
    intros own info d_ind ctor c d_ctor Hfi Hki Hfc Hkc.
    assert (Hfi' : find_decl own env = Some d_ind)
      by (eapply Hfind_nonres; [exact Hfi | rewrite Hki; intro Hx; exact Hx]).
    assert (Hfc' : find_decl ctor env = Some d_ctor)
      by (eapply Hfind_nonres; [exact Hfc | rewrite Hkc; intro Hx; exact Hx]).
    exact (ves_ind_shape Hves Hfi' Hki Hfc' Hkc).
  - (* ves_ind_type_arity *)
    intros U G own info us args usort HG Hi Ht.
    rewrite Hind_eq in Hi. eapply ves_ind_type_arity; eassumption.
  - (* ves_ctor_params_wf *)
    intros U G own info ctor c d0 us ps0 idxs T HG Hi Hct Hd Hk.
    rewrite Hind_eq in Hi.
    assert (Hd' : find_decl ctor env = Some d0)
      by (eapply Hfind_nonres; [exact Hd | rewrite Hk; intro Hx; exact Hx]).
    eapply ves_ctor_params_wf; eassumption.
  - (* ves_ind_weakN *)
    intros U n k G G' own info T0 us args HG W Hi Ht.
    rewrite Hind_eq in Hi. eapply ves_ind_weakN; eassumption.
Qed.

Lemma find_decl_safety_environment_none mode env n :
  find_decl n (safety_environment mode env) = None ->
  find_decl n env = None.
Proof.
  unfold safety_environment.
  induction env as [|d rest IH]; simpl; [intros _; reflexivity |].
  destruct (name_eqb n (decl_name d)); [discriminate | exact IH].
Qed.

Theorem admit_extended_restricted_sound fuel env venv input next :
  VEnvSound env venv ->
  match input with
  | InputAxiom _ _ _ true
  | InputDefinition _ _ _ _ _ InputUnsafe
  | InputDefinition _ _ _ _ _ InputPartial
  | InputOpaque _ _ _ _ true => True
  | _ => False
  end ->
  admit_extended fuel env input = Accept next ->
  VEnvSound next venv /\ VEnvWF venv.
Proof.
  intros Hves Hres Hadm.
  destruct input as [n ps ty [|] | hints n ps ty val [| |] | n ps ty body | n ps ty val [|] |];
    try contradiction; simpl in Hadm.
  - (* InputAxiom unsafe = true *)
    destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
    destruct (check_header fuel (safety_environment InputUnsafe env) n ps ty) as [[]| |] eqn:Hh;
      simpl in Hadm; try discriminate.
    inversion Hadm; subst next.
    assert (Hfr : find_decl n env = None).
    { apply (@find_decl_safety_environment_none InputUnsafe).
      unfold check_header in Hh. destruct (find_decl n (safety_environment InputUnsafe env));
        [discriminate | reflexivity]. }
    split; [apply VEnvSound_prepend_restricted; [exact Hves | exact Hfr | exact I] | exact (ves_wf Hves)].
  - (* InputDefinition InputPartial *)
    destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
    destruct (check_header fuel env n ps ty) as [[]| |] eqn:Hh; simpl in Hadm; try discriminate.
    destruct (check_value fuel env ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
    inversion Hadm; subst next.
    assert (Hfr : find_decl n env = None)
      by (unfold check_header in Hh; destruct (find_decl n env); [discriminate | reflexivity]).
    split; [apply VEnvSound_prepend_restricted; [exact Hves | exact Hfr | exact I] | exact (ves_wf Hves)].
  - (* InputDefinition InputUnsafe *)
    destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
    destruct (check_header fuel (safety_environment InputUnsafe env) n ps ty) as [[]| |] eqn:Hh;
      simpl in Hadm; try discriminate.
    destruct (check_value fuel _ ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
    inversion Hadm; subst next.
    assert (Hfr : find_decl n env = None).
    { apply (@find_decl_safety_environment_none InputUnsafe).
      unfold check_header in Hh. destruct (find_decl n (safety_environment InputUnsafe env));
        [discriminate | reflexivity]. }
    split; [apply VEnvSound_prepend_restricted; [exact Hves | exact Hfr | exact I] | exact (ves_wf Hves)].
  - (* InputOpaque unsafe = true *)
    destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
    destruct (check_header fuel env n ps ty) as [[]| |] eqn:Hh; simpl in Hadm; try discriminate.
    destruct (check_value fuel env ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
    inversion Hadm; subst next.
    assert (Hfr : find_decl n env = None)
      by (unfold check_header in Hh; destruct (find_decl n env); [discriminate | reflexivity]).
    split; [apply VEnvSound_prepend_restricted; [exact Hves | exact Hfr | exact I] | exact (ves_wf Hves)].
Qed.

Lemma VEnvSound_prepend_restricted_list env venv ds :
  VEnvSound env venv ->
  Forall (fun d => find_decl (decl_name d) env = None /\ is_restricted_kind (decl_kind_of d)) ds ->
  names_unique (map decl_name ds) = true ->
  VEnvSound (ds ++ env) venv.
Proof.
  intros Hves. induction ds as [|d rest IH]; simpl; [intros _ _; exact Hves |].
  intros Hall Huniq.
  inversion Hall as [| ? ? [Hfr Hres] Hrest]; subst.
  apply andb_true_iff in Huniq as [Hnotmem Huniq_r].
  apply VEnvSound_prepend_restricted; [apply IH; assumption | | exact Hres].
  clear -Hfr Hnotmem.
  induction rest as [|r rs IHr]; simpl in *; [exact Hfr |].
  destruct (name_eqb (decl_name d) (decl_name r)) eqn:Edr; simpl in Hnotmem; [discriminate |].
  exact (IHr Hnotmem).
Qed.

Lemma check_mutual_headers_names fuel view ps mode inputs phs :
  check_mutual_headers fuel view ps mode inputs = Accept phs ->
  Forall (fun inp =>
    match inp with
    | InputDefinition _ n _ _ _ s =>
        safety_eqb s mode = true /\ find_decl n view = None
    | _ => False
    end) inputs.
Proof.
  revert phs. induction inputs as [|inp rest IH]; intros phs H; simpl in H; [constructor |].
  destruct inp as [|hints n qs ty val s| | |]; try discriminate.
  destruct (safety_eqb s mode && list_eqb name_eqb qs ps) eqn:Echk; simpl in H; [|discriminate].
  apply andb_true_iff in Echk as [Hs _].
  destruct (safe_name n) as [[]| |]; simpl in H; try discriminate.
  destruct (check_header fuel view n ps ty) as [[]| |] eqn:Hh; simpl in H; try discriminate.
  destruct (check_mutual_headers fuel view ps mode rest) as [rphs| |] eqn:Hr; simpl in H; try discriminate.
  constructor.
  - split; [exact Hs | unfold check_header in Hh; destruct (find_decl n view); [discriminate | reflexivity]].
  - exact (IH rphs eq_refl).
Qed.

Lemma check_mutual_values_generated fuel view mode inputs gen :
  mode <> InputSafe ->
  Forall (fun inp =>
    match inp with
    | InputDefinition _ n _ _ _ s =>
        safety_eqb s mode = true /\ find_decl n view = None
    | _ => False
    end) inputs ->
  check_mutual_values fuel view inputs = Accept gen ->
  map decl_name gen = map mutual_name inputs /\
  Forall (fun d => find_decl (decl_name d) view = None /\ is_restricted_kind (decl_kind_of d)) gen.
Proof.
  intros Hns. revert gen.
  induction inputs as [|inp rest IH]; intros gen Hall H; simpl in H.
  - inversion H; subst gen. split; [reflexivity | constructor].
  - destruct inp as [|hints n qs ty val s| | |]; try discriminate.
    inversion Hall as [| ? ? Hhd Hrest]; subst; destruct Hhd as [Hsm Hfr].
    destruct (check_value fuel view qs ty val) as [[]| |]; simpl in H; try discriminate.
    destruct (check_mutual_values fuel view rest) as [rgen| |] eqn:Hr; simpl in H; try discriminate.
    inversion H; subst gen; clear H.
    destruct (IH rgen Hrest eq_refl) as [Hmap Hfor].
    split; [simpl; f_equal; exact Hmap |].
    constructor; [| exact Hfor].
    split; [exact Hfr |].
    destruct s; destruct mode; simpl in Hsm; try discriminate; try contradiction; exact I.
Qed.

Theorem admit_mutual_sound fuel env venv inputs next :
  VEnvSound env venv ->
  admit_mutual fuel env inputs = Accept next ->
  VEnvSound next venv /\ VEnvWF venv.
Proof.
  intros Hves Hadm.
  unfold admit_mutual in Hadm.
  destruct inputs as [|inp0 rest]; [discriminate |].
  destruct inp0 as [|h0 n0 ps ty0 v0 mode| | |]; try discriminate.
  cbn [bind require] in Hadm.
  destruct (negb (safety_eqb mode InputSafe)) eqn:Hns; cbn [bind require] in Hadm; [|discriminate].
  destruct (names_unique (map mutual_name (InputDefinition h0 n0 ps ty0 v0 mode :: rest)))
    eqn:Huniq; cbn [bind require] in Hadm; [|discriminate].
  destruct (check_mutual_headers fuel (safety_environment mode env) ps mode
              (InputDefinition h0 n0 ps ty0 v0 mode :: rest)) as [phs| |] eqn:Hhdr;
    cbn [bind require] in Hadm; try discriminate.
  destruct (check_mutual_values fuel (phs ++ safety_environment mode env)
              (InputDefinition h0 n0 ps ty0 v0 mode :: rest)) as [gen| |] eqn:Hvals;
    cbn [bind require] in Hadm; try discriminate.
  inversion Hadm; subst next; clear Hadm.
  pose proof (check_mutual_headers_names Hhdr) as Hhdr_all.
  assert (Hmode_ns : mode <> InputSafe) by (destruct mode; simpl in Hns; try discriminate; intro; discriminate).
  assert (Hvals_info :
    map decl_name gen = map mutual_name (InputDefinition h0 n0 ps ty0 v0 mode :: rest) /\
    Forall (fun d => find_decl (decl_name d) (safety_environment mode env) = None /\
                     is_restricted_kind (decl_kind_of d)) gen).
  { clear Hhdr Huniq Hns.
    revert gen Hvals Hhdr_all.
    generalize (InputDefinition h0 n0 ps ty0 v0 mode :: rest) as inps.
    intros inps. induction inps as [|inp rs IHi]; intros gen Hv Hall; simpl in Hv.
    - inversion Hv; subst. split; [reflexivity | constructor].
    - destruct inp as [|h n qs ty v s| | |]; try discriminate.
      inversion Hall as [| ? ? Hhd Hrest_all]; subst; destruct Hhd as [Hsm Hfr].
      destruct (check_value fuel (phs ++ safety_environment mode env) qs ty v) as [[]| |];
        simpl in Hv; try discriminate.
      destruct (check_mutual_values fuel (phs ++ safety_environment mode env) rs) as [rgen| |] eqn:Hr;
        simpl in Hv; try discriminate.
      inversion Hv; subst gen; clear Hv.
      destruct (IHi rgen eq_refl Hrest_all) as [Hm Hf].
      split; [simpl; f_equal; exact Hm |].
      constructor; [| exact Hf].
      split; [exact Hfr | destruct s; destruct mode; simpl in Hsm; try discriminate; try contradiction; exact I]. }
  destruct Hvals_info as [Hmap Hfor].
  split; [| exact (ves_wf Hves)].
  apply VEnvSound_prepend_restricted_list; [exact Hves | | rewrite Hmap; exact Huniq].
  eapply Forall_impl; [| exact Hfor].
  intros d [Hfr Hrk]. split; [exact (@find_decl_safety_environment_none mode env (decl_name d) Hfr) | exact Hrk].
Qed.

(* Unsafe inductives leave the safe semantic `venv` completely untouched *)
Theorem admit_inductive_extended_unsafe_sound fuel env venv types ctors recs next :
  VEnvSound env venv ->
  inductive_input_unsafe types = true ->
  admit_inductive_extended fuel env types ctors recs = Accept next ->
  VEnvWF venv /\
  exists added,
    next = added ++ env /\
    Forall (fun d => match decl_kind_of d with DUnsafe _ => True | _ => False end) added.
Proof.
  intros Hves Huns Hadm.
  split; [exact (ves_wf Hves) |].
  unfold admit_inductive_extended in Hadm. rewrite Huns in Hadm.
  destruct (admit_inductive_nested fuel (safety_environment InputUnsafe env) types ctors recs)
    as [checked| |] eqn:Hchk; cbn [bind] in Hadm; try discriminate.
  inversion Hadm; subst next; clear Hadm.
  eexists. split; [reflexivity |].
  apply Forall_map. apply Forall_forall. intros d _.
  unfold mark_unsafe_inductive; simpl.
  exact I.
Qed.

(* ========================================================================= *)
(* 6. Quotient Admission Soundness (`Quotient.v` <-> `EnvDeclTheory.v`)      *)
(* ========================================================================= *)

(* Computational identity between executable `Quotient.v` types and
   declarative `EnvDeclTheory.v` constants! *)
Lemma trE_quotient_eq_type u :
  trE [u] (quotient_eq_type (LParam u)) = Some (vc_type eqConst).
Proof.
  unfold quotient_eq_type, q_local, q_arrow, eqConst; simpl.
  rewrite name_eqb_refl. reflexivity.
Qed.

Lemma trE_canonical_quotient_QType :
  trE (decl_params (canonical_quotient QType)) (decl_type (canonical_quotient QType)) =
  Some (vc_type quotConst).
Proof. vm_compute. reflexivity. Qed.

Lemma trE_canonical_quotient_QCtor :
  trE (decl_params (canonical_quotient QCtor)) (decl_type (canonical_quotient QCtor)) =
  Some (vc_type quotMkConst).
Proof. vm_compute. reflexivity. Qed.

Lemma trE_canonical_quotient_QLift :
  trE (decl_params (canonical_quotient QLift)) (decl_type (canonical_quotient QLift)) =
  Some (vc_type quotLiftConst).
Proof. vm_compute. reflexivity. Qed.

Lemma trE_canonical_quotient_QInd :
  trE (decl_params (canonical_quotient QInd)) (decl_type (canonical_quotient QInd)) =
  Some (vc_type quotIndConst).
Proof. vm_compute. reflexivity. Qed.

Theorem quotient_check_eq_sound env venv :
  VEnvSound env venv ->
  quotient_check_eq env = Accept tt ->
  exists d info u ci,
    find_decl q_eq_name env = Some d /\
    decl_kind_of d = DInductive info /\
    decl_params d = [u] /\
    venv_constants venv q_eq_name = Some ci /\
    vc_uvars ci = 1 /\
    VIsDefEqU venv 1 [] (vc_type ci) (vc_type eqConst).
Proof.
  intros Hves Hchk.
  pose proof (ves_wf Hves) as Hwf.
  unfold quotient_check_eq in Hchk.
  destruct (find_decl q_eq_name env) as [d|] eqn:Hf; [|discriminate].
  destruct (decl_kind_of d) as [| | | | |info| | | | | |] eqn:Hk; try discriminate.
  destruct (decl_params d) as [|u [|? ?]] eqn:Hp; try discriminate.
  destruct (expr_eqb (decl_type d) (quotient_eq_type (LParam u))) eqn:Heq;
    simpl in Hchk; [|discriminate].
  pose proof (ves_constants Hves Hf) as Hc. rewrite Hk, Hp in Hc.
  destruct Hc as [ci [Hci [Huv [Htr [His _]]]]].
  exists d, info, u, ci.
  split_and; try assumption; try reflexivity.
  destruct Htr as [e0 [He0 H01]].
  pose proof (VTrExprS_eq_trE He0 eq_refl (fun _ _ _ H => ltac:(discriminate H))) as Hsy.
  pose proof (expr_eqb_trE [u] Heq) as Htre.
  rewrite trE_quotient_eq_type in Htre.
  specialize (Hsy (vc_type eqConst) Htre). subst e0.
  apply VIsDefEqU_symm. exact H01.
Qed.

Theorem admit_quotient_sound fuel env venv n ps ty kind next :
  VEnvSound env venv ->
  admit_quotient fuel env n ps ty kind = Accept next ->
  let generated := canonical_quotient kind in
  next = generated :: env /\
  find_decl n env = None /\
  n = decl_name generated /\
  List.length ps = List.length (decl_params generated) /\
  (exists ty' u',
     VTrExpr env venv ps vl_empty ty ty' /\
     VHasType venv (List.length ps) [] ty' (VSort u') /\
     VConstantWF venv {| vc_uvars := List.length ps; vc_type := ty' |}) /\
  (VQuotReady venv ->
     venv_constants venv q_name = None ->
     venv_constants venv q_mk_name = None ->
     venv_constants venv q_lift_name = None ->
     venv_constants venv q_ind_name = None ->
     exists venv_q,
       venv_add_quot venv = Some venv_q /\
       venv_ordered venv venv_q /\
       VEnvWF venv_q /\
       venv_constants venv_q q_name = Some quotConst /\
       venv_constants venv_q q_mk_name = Some quotMkConst /\
       venv_constants venv_q q_lift_name = Some quotLiftConst /\
       venv_constants venv_q q_ind_name = Some quotIndConst /\
       venv_defeqs venv_q quotDefEq).
Proof.
  intros Hves Haq.
  unfold admit_quotient in Haq.
  destruct (quotient_check_eq env) as [[]| |] eqn:Heq; simpl in Haq; try discriminate.
  destruct (check_header fuel env n ps ty) as [[]| |] eqn:Hhdr; simpl in Haq; try discriminate.
  destruct (name_eqb n (decl_name (canonical_quotient kind)) &&
            Nat.eqb (List.length ps) (List.length (decl_params (canonical_quotient kind))))
    eqn:Enl; simpl in Haq; [|discriminate].
  apply andb_true_iff in Enl as [En Hl].
  apply name_eqb_eq in En. apply Nat.eqb_eq in Hl.
  destruct (expr_eqb (subst_levels ps (map LParam (decl_params (canonical_quotient kind))) ty)
              (decl_type (canonical_quotient kind))) eqn:Ety;
    simpl in Haq; [|discriminate].
  destruct (quotient_dependencies env kind) eqn:Hdep; simpl in Haq; [|discriminate].
  inversion Haq; subst next; clear Haq.
  destruct (check_header_sound Hves Hhdr) as [Hfresh [_ [_ [ty' [u' [Htr [Hht [His Hcl]]]]]]]].
  cbv zeta. split_and; try assumption; try reflexivity.
  - exists ty', u'. split_and; [exact Htr | exact Hht | split; [exact His | exact Hcl]].
  - intros Hqr Hn1 Hn2 Hn3 Hn4.
    destruct (exists_addQuot Hn1 Hn2 Hn3 Hn4) as [venv_q Hadd].
    exists venv_q. split_and.
    + exact Hadd.
    + exact (addQuot_ordered Hadd).
    + exact (proj1 (addQuot_WF (ves_wf Hves) Hqr Hadd)).
    + exact (addQuot_quot Hadd).
    + exact (addQuot_quotMk Hadd).
    + exact (addQuot_quotLift Hadd).
    + exact (addQuot_quotInd Hadd).
    + exact (addQuot_defeq Hadd).
Qed.

(* ========================================================================= *)
(* 7. Inductive Admission Bridge (`Inductive.v` <-> `EnvDeclTheory.v`)       *)
(* ========================================================================= *)

Theorem declarative_inductive_admit_sound env venv decl :
  VEnvSound env venv ->
  VInductDeclWF venv decl ->
  exists venv',
    venv_add_induct venv decl = Some venv' /\
    venv_ordered venv venv' /\
    VEnvWF venv' /\
    (forall cv, In cv (ind_all_consts decl) -> venv_constants venv' (vcv_name cv) = Some (vcv_const cv)) /\
    (forall df, In df (vid_iotas decl) -> venv_defeqs venv' df).
Proof.
  intros Hves Hdwf.
  destruct (exists_addInduct Hdwf) as [venv' Hadd].
  destruct (addInduct_WF (ves_wf Hves) Hdwf Hadd) as [Hwf' Hord].
  exists venv'. split_and.
  - exact Hadd.
  - exact Hord.
  - exact Hwf'.
  - intros cv Hin. exact (addInduct_consts Hadd Hin).
  - intros df Hin. exact (addInduct_iotas Hadd Hin).
Qed.

(* ========================================================================= *)
(* 8. Persistent State, Transactions, and Stream Soundness                   *)
(* ========================================================================= *)

(* Soundness of DAG admission batches (`BatchDag`): refines directly to `admit`! *)
Theorem batch_dag_sound hash fuel (s next : indexed_state hash) venv kind budget n ps rows tr br :
  VEnvSound (state_environment s) venv ->
  VEnvNamesAligned (state_environment s) venv ->
  state_step fuel s (BatchDag kind budget n ps rows tr br) = Accept next ->
  exists d ci venv',
    state_environment next = d :: state_environment s /\
    find_decl (decl_name d) (state_environment s) = None /\
    vc_uvars ci = List.length (decl_params d) /\
    VTrExpr (state_environment next) venv' (decl_params d) vl_empty (decl_type d) (vc_type ci) /\
    VIsType venv' (vc_uvars ci) [] (vc_type ci) /\
    vclosed (vc_type ci) /\
    venv_ordered venv venv' /\
    VEnvWF venv' /\
    venv_constants venv' (decl_name d) = Some ci /\
    VEnvNamesAligned (state_environment next) venv'.
Proof.
  intros Hves Halign Hstep.
  pose proof (persistent_dag_refines_new_ordinary fuel s kind budget n ps rows tr br) as Href.
  rewrite Hstep in Href. unfold project_result in Href; simpl in Href.
  symmetry in Href.
  unfold new_ordinary_decode_admit in Href.
  destruct (arena_build empty_arena rows) as [arena| |]; simpl in Href; try discriminate.
  destruct (scope_ref (arena_scope arena) tr) as [sty| |]; simpl in Href; try discriminate.
  destruct (scope_ref (arena_scope arena) br) as [sbody| |]; simpl in Href; try discriminate.
  destruct (admit_sound Hves Halign Href)
    as [d [ci [venv' [Hnext [Hfr [Huv [Htr [His [Hcl [Hord [Hwf' [Hc' [Halign' _]]]]]]]]]]]]].
  exists d, ci, venv'. split_and; assumption.
Qed.

(* Soundness of ordinary batches (`BatchOrdinary`): covers both safe & restricted inputs *)
Theorem batch_ordinary_sound hash fuel (s next : indexed_state hash) venv input :
  VEnvSound (state_environment s) venv ->
  VEnvNamesAligned (state_environment s) venv ->
  state_step fuel s (BatchOrdinary input) = Accept next ->
  exists venv',
    venv_ordered venv venv' /\
    VEnvWF venv'.
Proof.
  intros Hves Halign Hstep.
  pose proof (state_step_refines fuel s (BatchOrdinary input)) as Href.
  rewrite Hstep in Href. unfold project_result in Href; simpl in Href.
  symmetry in Href.
  destruct input as [n ps ty [|] | hints n ps ty val [| |] | n ps ty body | n ps ty val [|] |].
  - destruct (admit_extended_restricted_sound (input := InputAxiom n ps ty true) Hves I Href) as [_ Hwf'].
    exists venv. split; [apply venv_ordered_refl | exact Hwf'].
  - destruct (admit_sound Hves Halign Href) as [_ [_ [venv' [_ [_ [_ [_ [_ [_ [Hord [Hwf' _]]]]]]]]]]].
    exists venv'. split; assumption.
  - destruct (admit_sound Hves Halign Href) as [_ [_ [venv' [_ [_ [_ [_ [_ [_ [Hord [Hwf' _]]]]]]]]]]].
    exists venv'. split; assumption.
  - destruct (admit_extended_restricted_sound (input := InputDefinition hints n ps ty val InputPartial) Hves I Href) as [_ Hwf'].
    exists venv. split; [apply venv_ordered_refl | exact Hwf'].
  - destruct (admit_extended_restricted_sound (input := InputDefinition hints n ps ty val InputUnsafe) Hves I Href) as [_ Hwf'].
    exists venv. split; [apply venv_ordered_refl | exact Hwf'].
  - destruct (admit_sound Hves Halign Href) as [_ [_ [venv' [_ [_ [_ [_ [_ [_ [Hord [Hwf' _]]]]]]]]]]].
    exists venv'. split; assumption.
  - destruct (admit_extended_restricted_sound (input := InputOpaque n ps ty val true) Hves I Href) as [_ Hwf'].
    exists venv. split; [apply venv_ordered_refl | exact Hwf'].
  - destruct (admit_sound Hves Halign Href) as [_ [_ [venv' [_ [_ [_ [_ [_ [_ [Hord [Hwf' _]]]]]]]]]]].
    exists venv'. split; assumption.
  - simpl in Href. discriminate.
Qed.

(* Soundness of mutual batches (`BatchMutual`): preserves `VEnvSound` & `VEnvWF` on same `venv` *)
Theorem batch_mutual_sound hash fuel (s next : indexed_state hash) venv inputs :
  VEnvSound (state_environment s) venv ->
  state_step fuel s (BatchMutual inputs) = Accept next ->
  VEnvSound (state_environment next) venv /\ VEnvWF venv.
Proof.
  intros Hves Hstep.
  pose proof (state_step_refines fuel s (BatchMutual inputs)) as Href.
  rewrite Hstep in Href. unfold project_result in Href; simpl in Href.
  symmetry in Href.
  exact (admit_mutual_sound Hves Href).
Qed.

(* Transaction rollback soundness: failed/declined transactions preserve state & `VEnvSound` *)
Theorem transaction_preserves_soundness hash fuel (s s' : indexed_state hash) venv request r :
  VEnvSound (state_environment s) venv ->
  transaction fuel s request = (s', r) ->
  r <> Accept tt ->
  s' = s /\ VEnvSound (state_environment s') venv /\ VEnvWF venv.
Proof.
  intros Hves Htx Hne.
  unfold transaction in Htx.
  destruct (state_step fuel s request) as [nxt|reason|reason] eqn:Hst.
  - inversion Htx; subst. contradiction.
  - inversion Htx; subst. split; [reflexivity | split; [exact Hves | exact (ves_wf Hves)]].
  - inversion Htx; subst. split; [reflexivity | split; [exact Hves | exact (ves_wf Hves)]].
Qed.

(* End-to-end pure declaration stream soundness starting from `initial_state`! *)
Definition pure_request (fuel : nat) (req : admission_batch) : Prop :=
  match req with
  | BatchOrdinary input =>
      match input with
      | InputDefinition hints n ps ty body InputSafe =>
          forall env, classify_primitive fuel env n ps ty body = Accept None
      | _ => True
      end
  | BatchMutual _ => True
  | _ => False
  end.

Lemma admit_extended_restricted_pure_step fuel env venv input mid :
  PureConstEnv env ->
  VEnvSound env venv ->
  VEnvNamesAligned env venv ->
  match input with
  | InputAxiom _ _ _ true
  | InputDefinition _ _ _ _ _ InputUnsafe
  | InputDefinition _ _ _ _ _ InputPartial
  | InputOpaque _ _ _ _ true => True
  | _ => False
  end ->
  admit_extended fuel env input = Accept mid ->
  PureConstEnv mid /\
  venv_ordered venv venv /\
  VEnvWF venv /\
  VEnvSound mid venv /\
  VEnvNamesAligned mid venv.
Proof.
  intros Hpure Hves Halign Hres Hadm.
  destruct (admit_extended_restricted_sound Hves Hres Hadm) as [Hves1 Hwf1].
  assert (Hmid_info : exists d, mid = d :: env /\ is_restricted_kind (decl_kind_of d)).
  { destruct input as [n ps ty [|] | hints n ps ty val [| |] | n ps ty body | n ps ty val [|] |];
      try contradiction; simpl in Hadm.
    - destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_header fuel (safety_environment InputUnsafe env) n ps ty) as [[]| |];
        simpl in Hadm; try discriminate.
      inversion Hadm; eexists; split; [reflexivity | exact I].
    - destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_value fuel env ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; eexists; split; [reflexivity | exact I].
    - destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_header fuel (safety_environment InputUnsafe env) n ps ty) as [[]| |];
        simpl in Hadm; try discriminate.
      destruct (check_value fuel _ ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; eexists; split; [reflexivity | exact I].
    - destruct (safe_name n) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_header fuel env n ps ty) as [[]| |]; simpl in Hadm; try discriminate.
      destruct (check_value fuel env ps ty val) as [[]| |]; simpl in Hadm; try discriminate.
      inversion Hadm; eexists; split; [reflexivity | exact I]. }
  destruct Hmid_info as [d [Hmid_eq Hrk]].
  split_and; [| apply venv_ordered_refl | exact Hwf1 | exact Hves1 |].
  - intros m d0 Hf. rewrite Hmid_eq in Hf. simpl in Hf.
    destruct (name_eqb m (decl_name d)).
    + inversion Hf; subst d0. destruct (decl_kind_of d); try contradiction; exact I.
    + exact (Hpure _ _ Hf).
  - intros m Hm. rewrite Hmid_eq in Hm. simpl in Hm.
    destruct (name_eqb m (decl_name d)); [discriminate | exact (Halign m Hm)].
Qed.

Theorem reference_stream_pure_sound fuel requests :
  (forall v, VEnvWF v -> DefEqInjectivity v) ->
  Forall (pure_request fuel) requests ->
  forall env venv next,
    PureConstEnv env ->
    VEnvSound env venv ->
    VEnvNamesAligned env venv ->
    reference_stream fuel env requests = Accept next ->
    exists venv',
      PureConstEnv next /\
      venv_ordered venv venv' /\
      VEnvWF venv' /\
      VEnvSound next venv' /\
      VEnvNamesAligned next venv'.
Proof.
  intros Hinj_all.
  induction requests as [|req rest IH]; intros Hall env venv next Hpure Hves Halign Hstr;
    simpl in Hstr.
  - inversion Hstr; subst next.
    exists venv. split_and; [exact Hpure | apply venv_ordered_refl | exact (ves_wf Hves) | exact Hves | exact Halign].
  - inversion Hall as [| ? ? Hreq Hrest]; subst.
    destruct (reference_batch fuel env req) as [mid| |] eqn:Hstep; simpl in Hstr; try discriminate.
    assert (Hmid : exists venv1,
      PureConstEnv mid /\
      venv_ordered venv venv1 /\
      VEnvWF venv1 /\
      VEnvSound mid venv1 /\
      VEnvNamesAligned mid venv1).
    { destruct req as [|inp| | |inps]; try contradiction; simpl in Hstep.
      - destruct inp as [n ps ty [|] | hints n ps ty val [| |] | n ps ty body | n ps ty val [|] |].
        + (* InputAxiom unsafe *)
          exists venv.
          exact (admit_extended_restricted_pure_step (input := InputAxiom n ps ty true) Hpure Hves Halign I Hstep).
        + (* InputAxiom safe *)
          destruct (VEnvSound_pure_admit Hpure Hves Halign Hstep (fun _ _ _ _ _ H => ltac:(discriminate)))
            as [venv1 [Hp1 [Ho1 [Hw1 [Ha1 Hs1]]]]].
          exists venv1. split_and; [exact Hp1 | exact Ho1 | exact Hw1 | exact (Hs1 (Hinj_all _ Hw1)) | exact Ha1].
        + (* InputDefinition InputSafe *)
          destruct (VEnvSound_pure_admit Hpure Hves Halign Hstep
                      (fun n0 ps0 ty0 b0 h0 Heq => ltac:(inversion Heq; subst; exact (Hreq env))))
            as [venv1 [Hp1 [Ho1 [Hw1 [Ha1 Hs1]]]]].
          exists venv1. split_and; [exact Hp1 | exact Ho1 | exact Hw1 | exact (Hs1 (Hinj_all _ Hw1)) | exact Ha1].
        + (* InputDefinition InputPartial *)
          exists venv.
          exact (admit_extended_restricted_pure_step (input := InputDefinition hints n ps ty val InputPartial) Hpure Hves Halign I Hstep).
        + (* InputDefinition InputUnsafe *)
          exists venv.
          exact (admit_extended_restricted_pure_step (input := InputDefinition hints n ps ty val InputUnsafe) Hpure Hves Halign I Hstep).
        + (* InputTheorem *)
          destruct (VEnvSound_pure_admit Hpure Hves Halign Hstep (fun _ _ _ _ _ H => ltac:(discriminate)))
            as [venv1 [Hp1 [Ho1 [Hw1 [Ha1 Hs1]]]]].
          exists venv1. split_and; [exact Hp1 | exact Ho1 | exact Hw1 | exact (Hs1 (Hinj_all _ Hw1)) | exact Ha1].
        + (* InputOpaque unsafe *)
          exists venv.
          exact (admit_extended_restricted_pure_step (input := InputOpaque n ps ty val true) Hpure Hves Halign I Hstep).
        + (* InputOpaque safe *)
          destruct (VEnvSound_pure_admit Hpure Hves Halign Hstep (fun _ _ _ _ _ H => ltac:(discriminate)))
            as [venv1 [Hp1 [Ho1 [Hw1 [Ha1 Hs1]]]]].
          exists venv1. split_and; [exact Hp1 | exact Ho1 | exact Hw1 | exact (Hs1 (Hinj_all _ Hw1)) | exact Ha1].
        + simpl in Hstep. discriminate.
      - (* BatchMutual *)
        destruct (admit_mutual_sound Hves Hstep) as [Hves1 Hwf1].
        assert (Hmut_info : exists gen,
          mid = gen ++ env /\
          Forall (fun d => is_restricted_kind (decl_kind_of d)) gen).
        { unfold admit_mutual in Hstep.
          destruct inps as [|i0 rs]; [discriminate |].
          destruct i0 as [|h0 n0 ps0 t0 v0 mode| | |]; try discriminate.
          cbn [bind require] in Hstep.
          destruct (negb (safety_eqb mode InputSafe)) eqn:Hns; cbn [bind require] in Hstep; [|discriminate].
          destruct (names_unique _) eqn:Hu; cbn [bind require] in Hstep; [|discriminate].
          destruct (check_mutual_headers fuel (safety_environment mode env) ps0 mode _)
            as [phs| |] eqn:Hhdr; cbn [bind require] in Hstep; try discriminate.
          destruct (check_mutual_values fuel (phs ++ safety_environment mode env) _)
            as [gen| |] eqn:Hvals; cbn [bind require] in Hstep; try discriminate.
          inversion Hstep; subst mid; clear Hstep.
          exists gen. split; [reflexivity |].
          pose proof (check_mutual_headers_names Hhdr) as Hha.
          clear -Hns Hha Hvals.
          revert gen Hvals Hha.
          generalize (InputDefinition h0 n0 ps0 t0 v0 mode :: rs) as xs.
          intros xs. induction xs as [|x xs IH]; intros gen Hv Hall; simpl in Hv.
          - inversion Hv; subst. constructor.
          - destruct x as [|h n q t v s| | |]; try discriminate.
            inversion Hall as [| ? ? Hhd Hhr]; subst; destruct Hhd as [Hsm _].
            destruct (check_value fuel _ q t v) as [[]| |]; simpl in Hv; try discriminate.
            destruct (check_mutual_values fuel _ xs) as [rg| |] eqn:Hrg; simpl in Hv; try discriminate.
            inversion Hv; subst. constructor; [| exact (IH rg eq_refl Hhr)].
            destruct s; destruct mode; simpl in Hsm, Hns; try discriminate; exact I. }
        destruct Hmut_info as [gen [Hmid_eq Hgen_rk]].
        exists venv. split_and; [| apply venv_ordered_refl | exact Hwf1 | exact Hves1 |].
        + intros m d0 Hf. rewrite Hmid_eq in Hf.
          clear -Hpure Hgen_rk Hf.
          induction gen as [|g0 gs IH]; simpl in Hf; [exact (Hpure _ _ Hf) |].
          inversion Hgen_rk as [| ? ? Hrk Hrest]; subst.
          destruct (name_eqb m (decl_name g0));
            [inversion Hf; subst d0; destruct (decl_kind_of g0); try contradiction; exact I | exact (IH Hrest Hf)].
        + intros m Hm. rewrite Hmid_eq in Hm.
          clear -Halign Hm. induction gen as [|g0 gs IH]; simpl in Hm; [exact (Halign m Hm) |].
          destruct (name_eqb m (decl_name g0)); [discriminate | exact (IH Hm)]. }
    destruct Hmid as [venv1 [Hpure1 [Hord1 [Hwf1 [Hves1 Halign1]]]]].
    destruct (IH Hrest mid venv1 next Hpure1 Hves1 Halign1 Hstr)
      as [venv2 [Hpure2 [Hord2 [Hwf2 [Hves2 Halign2]]]]].
    exists venv2. split_and; [exact Hpure2 | eapply venv_ordered_trans; eassumption |
      exact Hwf2 | exact Hves2 | exact Halign2].
Qed.

Theorem state_stream_from_initial_sound fuel requests final :
  (forall v, VEnvWF v -> DefEqInjectivity v) ->
  Forall (pure_request fuel) requests ->
  state_stream fuel initial_state requests = Accept final ->
  exists venv',
    VEnvWF venv' /\
    VEnvSound (state_environment final) venv'.
Proof.
  intros Hinj_all Hall Hstr.
  pose proof (state_stream_refines fuel requests initial_state) as Href.
  rewrite Hstr in Href. unfold project_result in Href; simpl in Href.
  symmetry in Href.
  destruct (reference_stream_pure_sound Hinj_all Hall PureConstEnv_empty
              (VEnvSound_empty (Hinj_all _ VEnvWF_empty)) VEnvNamesAligned_empty Href)
    as [venv' [_ [_ [Hwf' [Hves' _]]]]].
  exists venv'. split; assumption.
Qed.

Print Assumptions check_header_sound.
Print Assumptions check_proposition_sound.
Print Assumptions check_value_sound.
Print Assumptions primitive_eq_closed_sound.
Print Assumptions primitive_check_closed_sound.
Print Assumptions primitive_check_equations_sound.
Print Assumptions classify_primitive_sound.
Print Assumptions checked_constant_sound_aligned.
Print Assumptions admit_sound.
Print Assumptions VEnvSound_pure_admit.
Print Assumptions VEnvSound_prepend_restricted.
Print Assumptions admit_extended_restricted_sound.
Print Assumptions admit_mutual_sound.
Print Assumptions admit_inductive_extended_unsafe_sound.
Print Assumptions trE_quotient_eq_type.
Print Assumptions trE_canonical_quotient_QType.
Print Assumptions trE_canonical_quotient_QCtor.
Print Assumptions trE_canonical_quotient_QLift.
Print Assumptions trE_canonical_quotient_QInd.
Print Assumptions quotient_check_eq_sound.
Print Assumptions admit_quotient_sound.
Print Assumptions declarative_inductive_admit_sound.
Print Assumptions batch_dag_sound.
Print Assumptions batch_ordinary_sound.
Print Assumptions batch_mutual_sound.
Print Assumptions transaction_preserves_soundness.
Print Assumptions reference_stream_pure_sound.
Print Assumptions state_stream_from_initial_sound.
