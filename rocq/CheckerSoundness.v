(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq formalization of Lean4Lean/Verify/{Typing/Expr.lean, Typing/CondTyped.lean,
   TypeChecker/*.lean, Environment/*.lean}: the verification bridge connecting
   executable kernel syntax, WHNF reduction, definitional equality, type
   inference/checking, declaration admission, structure projections (TrProj),
   and addInductive / recursor iota-reduction to the declarative VEnv/VIsDefEq
   model. Zero axioms. *)
From Stdlib Require Import List Bool Arith PeanoNat NArith String Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness Checker Declarations
  Inductive SemanticModel DeclarativeTyping.
Import ListNotations.
Open Scope nat_scope.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Semantic Spine Helpers & Universe Instantiation Distribution           *)
(* ========================================================================= *)

Definition vapps (f : VExpr) (args : list VExpr) : VExpr :=
  List.fold_left VApp args f.

Lemma vapps_nil f : vapps f [] = f.
Proof. reflexivity. Qed.

Lemma vapps_cons f a args : vapps f (a :: args) = vapps (VApp f a) args.
Proof. reflexivity. Qed.

Lemma vapps_app f args1 args2 :
  vapps f (args1 ++ args2) = vapps (vapps f args1) args2.
Proof.
  unfold vapps. apply List.fold_left_app.
Qed.

Lemma vinstL_vapps ls f args :
  vinstL ls (vapps f args) = vapps (vinstL ls f) (List.map (vinstL ls) args).
Proof.
  unfold vapps. revert f.
  induction args as [|a rest IH]; intros f; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma vliftN_vapps n k f args :
  vliftN n k (vapps f args) = vapps (vliftN n k f) (List.map (vliftN n k) args).
Proof.
  unfold vapps. revert f.
  induction args as [|a rest IH]; intros f; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma vclosedN_vapps k f args :
  vclosedN k f ->
  Forall (vclosedN k) args ->
  vclosedN k (vapps f args).
Proof.
  intros Hf Hargs. unfold vapps. revert f Hf.
  induction Hargs as [|a rest Ha Hrest IH]; intros f Hf; simpl.
  - exact Hf.
  - apply IH. simpl. split; [exact Hf | exact Ha].
Qed.

(* ========================================================================= *)
(* 2. Structure Projections (TrProj) & Projection Iota Soundness in VEnv     *)
(* ========================================================================= *)

Definition proj_const_name (s : name) (idx : nat) : name :=
  NameNum (NameStr s "_proj") (N.of_nat idx).

Definition vproj_expr (s : name) (idx : nat) (us : list VLevel)
    (params : list VExpr) (struct_v : VExpr) : VExpr :=
  VApp (vapps (VConst (proj_const_name s idx) us) params) struct_v.

Record VProjRuleSpec : Type := {
  vprs_uvars : nat;
  vprs_owner : name;
  vprs_ctor : name;
  vprs_idx : nat;
  vprs_us : list VLevel;
  vprs_params : list VExpr;
  vprs_fields : list VExpr;
  vprs_field_val : VExpr;
  vprs_field_ty : VExpr
}.

Definition vproj_defeq_of_spec (spec : VProjRuleSpec) : VDefEq :=
  {| vdf_uvars := vprs_uvars spec;
     vdf_lhs := vproj_expr (vprs_owner spec) (vprs_idx spec) (vprs_us spec)
                  (vprs_params spec)
                  (vapps (VConst (vprs_ctor spec) (vprs_us spec))
                    (vprs_params spec ++ vprs_fields spec));
     vdf_rhs := vprs_field_val spec;
     vdf_type := vprs_field_ty spec |}.

(* Unconditional declarative projection typing relation (Lean4Lean TrProj) *)
Inductive TrProj (env : VEnv) (uvars : nat) (G : list VExpr)
    (s : name) (idx : nat) (struct_v proj_v field_ty : VExpr) : Prop :=
| TrProj_intro : forall struct_ty,
    VHasType env uvars G struct_v struct_ty ->
    VHasType env uvars G proj_v field_ty ->
    VIsType env uvars G field_ty ->
    TrProj env uvars G s idx struct_v proj_v field_ty.

Theorem TrProj_has_type env uvars G s idx struct_v proj_v field_ty :
  TrProj env uvars G s idx struct_v proj_v field_ty ->
  VHasType env uvars G proj_v field_ty.
Proof.
  intros [st Hst Hpr Hty]. exact Hpr.
Qed.

Theorem TrProj_monotonic_env env1 env2 uvars G s idx struct_v proj_v field_ty :
  venv_ordered env1 env2 ->
  TrProj env1 uvars G s idx struct_v proj_v field_ty ->
  TrProj env2 uvars G s idx struct_v proj_v field_ty.
Proof.
  intros Hord [st Hst Hpr Hty].
  eapply TrProj_intro.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
  - eapply VEnvOrdered_preserve_VIsType; eassumption.
Qed.

Theorem vproj_iota_defeq_sound env uvars G (spec : VProjRuleSpec) (ls : list VLevel) :
  venv_defeqs env (vproj_defeq_of_spec spec) ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = vprs_uvars spec ->
  nth_error (vprs_fields spec) (vprs_idx spec) = Some (vprs_field_val spec) ->
  VIsDefEq env uvars G
    (vproj_expr (vprs_owner spec) (vprs_idx spec)
      (List.map (vlevel_inst ls) (vprs_us spec))
      (List.map (vinstL ls) (vprs_params spec))
      (vapps (VConst (vprs_ctor spec) (List.map (vlevel_inst ls) (vprs_us spec)))
        (List.map (vinstL ls) (vprs_params spec) ++
         List.map (vinstL ls) (vprs_fields spec))))
    (vinstL ls (vprs_field_val spec))
    (vinstL ls (vprs_field_ty spec)).
Proof.
  intros Hmem Hwf Hlen Hnth.
  pose proof (@VDF_extra env uvars G (vproj_defeq_of_spec spec) ls Hmem Hwf Hlen) as Hext.
  unfold vproj_defeq_of_spec in Hext. simpl in Hext.
  unfold vproj_expr in *.
  rewrite !vinstL_vapps in Hext. simpl in Hext.
  rewrite List.map_app in Hext.
  exact Hext.
Qed.

(* ========================================================================= *)
(* 3. Level and Expression Translation Relations (Lean4Lean/Verify/Typing)   *)
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

(* Syntactic-to-Semantic Expression Translation (TrExprS / TrExpr)
   including unconditional TrExprS_proj (structure projections) and literals *)
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
| TrExprS_proj : forall G s idx e e' proj' field_ty,
    TrExprS env ps G e e' ->
    TrProj env (List.length ps) G s idx e' proj' field_ty ->
    TrExprS env ps G (EProj s idx e) proj'
| TrExprS_lit : forall G lit lit' lit_ty,
    VHasType env (List.length ps) G lit' lit_ty ->
    TrExprS env ps G (ELit lit) lit'
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
(* 4. Metatheoretic Properties of TrExprS / TrExpr / TrTyping (Incl. Proj)   *)
(* ========================================================================= *)

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
  - exists field_ty. eapply TrProj_has_type; exact H0.
  - exists lit_ty. exact H.
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

Theorem TrExpr_proj_unconditional env ps G s idx e e' proj' field_ty :
  TrExprS env ps G e e' ->
  TrProj env (List.length ps) G s idx e' proj' field_ty ->
  TrExpr env ps G (EProj s idx e) proj' /\
  VHasType env (List.length ps) G proj' field_ty.
Proof.
  intros He Hproj.
  split.
  - apply TrExprS_to_TrExpr. eapply TrExprS_proj; eassumption.
  - eapply TrProj_has_type; exact Hproj.
Qed.

Theorem TrTyping_proj_unconditional env ps G s idx e ty e' proj' field_ty :
  TrExprS env ps G e e' ->
  TrProj env (List.length ps) G s idx e' proj' field_ty ->
  TrExpr env ps G ty field_ty ->
  TrTyping env ps G (EProj s idx e) ty proj' field_ty.
Proof.
  intros He Hproj Hty.
  destruct (TrExpr_proj_unconditional He Hproj) as [Htr_proj Hhas_proj].
  repeat split; assumption.
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
  - eapply TrExprS_proj; [exact IHTrExprS | eapply TrProj_monotonic_env; eassumption].
  - eapply TrExprS_lit. eapply VEnvOrdered_preserve_VHasType; eassumption.
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
(* 5. Unconditional addInductive & Recursor Iota-Reduction Soundness in VEnv *)
(* ========================================================================= *)

Record VIotaRuleSpec : Type := {
  virs_uvars : nat;
  virs_rec_name : name;
  virs_ctor_name : name;
  virs_us : list VLevel;
  virs_prefix_args : list VExpr;
  virs_indices : list VExpr;
  virs_ctor_params : list VExpr;
  virs_ctor_fields : list VExpr;
  virs_rhs : VExpr;
  virs_type : VExpr
}.

Definition viota_lhs (spec : VIotaRuleSpec) : VExpr :=
  vapps (VConst (virs_rec_name spec) (virs_us spec))
    (virs_prefix_args spec ++ virs_indices spec ++
     [vapps (VConst (virs_ctor_name spec) (virs_us spec))
       (virs_ctor_params spec ++ virs_ctor_fields spec)]).

Definition viota_rhs (spec : VIotaRuleSpec) : VExpr :=
  vapps (virs_rhs spec) (virs_prefix_args spec ++ virs_ctor_fields spec).

Definition viota_defeq_of_spec (spec : VIotaRuleSpec) : VDefEq :=
  {| vdf_uvars := virs_uvars spec;
     vdf_lhs := viota_lhs spec;
     vdf_rhs := viota_rhs spec;
     vdf_type := virs_type spec |}.

Theorem recursor_iota_defeq_sound_venv env uvars G (spec : VIotaRuleSpec) (ls : list VLevel) :
  venv_defeqs env (viota_defeq_of_spec spec) ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = virs_uvars spec ->
  VIsDefEq env uvars G
    (vapps (VConst (virs_rec_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
      (List.map (vinstL ls) (virs_prefix_args spec) ++
       List.map (vinstL ls) (virs_indices spec) ++
       [vapps (VConst (virs_ctor_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
         (List.map (vinstL ls) (virs_ctor_params spec) ++
          List.map (vinstL ls) (virs_ctor_fields spec))]))
    (vapps (vinstL ls (virs_rhs spec))
      (List.map (vinstL ls) (virs_prefix_args spec) ++
       List.map (vinstL ls) (virs_ctor_fields spec)))
    (vinstL ls (virs_type spec)).
Proof.
  intros Hmem Hwf Hlen.
  pose proof (@VDF_extra env uvars G (viota_defeq_of_spec spec) ls Hmem Hwf Hlen) as Hext.
  unfold viota_defeq_of_spec, viota_lhs, viota_rhs in Hext. simpl in Hext.
  rewrite !vinstL_vapps in Hext. simpl in Hext.
  rewrite !List.map_app in Hext. simpl in Hext.
  rewrite vinstL_vapps in Hext. simpl in Hext.
  rewrite List.map_app in Hext.
  exact Hext.
Qed.

(* Adding an inductive block (type formers, constructors, recursors, and
   their iota-reduction rules) to VEnv preserves VEnvOrdered and VEnvWF *)
Fixpoint venv_add_consts_list (env : VEnv) (decls : list (name * VConstant)) : option VEnv :=
  match decls with
  | [] => Some env
  | (n, ci) :: rest =>
      match venv_add_const env n ci with
      | Some env1 => venv_add_consts_list env1 rest
      | None => None
      end
  end.

Fixpoint venv_add_defeqs_list (env : VEnv) (dfs : list VDefEq) : VEnv :=
  match dfs with
  | [] => env
  | df :: rest => venv_add_defeqs_list (venv_add_defeq env df) rest
  end.

Definition venv_add_inductive_block (env : VEnv)
    (decls : list (name * VConstant)) (iota_specs : list VIotaRuleSpec) : option VEnv :=
  match venv_add_consts_list env decls with
  | Some env1 => Some (venv_add_defeqs_list env1 (List.map viota_defeq_of_spec iota_specs))
  | None => None
  end.

Lemma venv_add_consts_list_ordered decls : forall env env',
  venv_add_consts_list env decls = Some env' ->
  venv_ordered env env'.
Proof.
  induction decls as [|[n ci] rest IH]; intros env env' Hadd; simpl in Hadd.
  - inversion Hadd; subst. apply venv_ordered_refl.
  - destruct (venv_add_const env n ci) as [env1|] eqn:H1; [|discriminate].
    eapply venv_ordered_trans.
    + eapply venv_add_const_ordered; exact H1.
    + eapply IH; exact Hadd.
Qed.

Lemma venv_add_defeqs_list_ordered dfs : forall env,
  venv_ordered env (venv_add_defeqs_list env dfs).
Proof.
  induction dfs as [|df rest IH]; intros env; simpl.
  - apply venv_ordered_refl.
  - eapply venv_ordered_trans.
    + apply venv_add_defeq_ordered.
    + apply IH.
Qed.

Theorem venv_add_inductive_block_ordered env decls iota_specs env' :
  venv_add_inductive_block env decls iota_specs = Some env' ->
  venv_ordered env env'.
Proof.
  unfold venv_add_inductive_block.
  destruct (venv_add_consts_list env decls) as [env1|] eqn:H1; [|discriminate].
  intros H2. inversion H2; subst env'.
  eapply venv_ordered_trans.
  - eapply venv_add_consts_list_ordered; exact H1.
  - apply venv_add_defeqs_list_ordered.
Qed.

Lemma venv_add_defeqs_list_mem df dfs : forall env,
  In df dfs ->
  venv_defeqs (venv_add_defeqs_list env dfs) df.
Proof.
  induction dfs as [|d rest IH]; intros env Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst d.
      pose proof (venv_add_defeqs_list_ordered rest (venv_add_defeq env df)) as Hord.
      apply (venv_ord_defeq Hord).
      simpl. left. reflexivity.
    + apply IH. exact Hin.
Qed.

Theorem addInductive_iota_rule_in_venv env decls iota_specs env' spec :
  venv_add_inductive_block env decls iota_specs = Some env' ->
  In spec iota_specs ->
  venv_defeqs env' (viota_defeq_of_spec spec).
Proof.
  unfold venv_add_inductive_block.
  destruct (venv_add_consts_list env decls) as [env1|] eqn:H1; [|discriminate].
  intros H2 Hin. inversion H2; subst env'.
  apply venv_add_defeqs_list_mem.
  apply in_map. exact Hin.
Qed.

Theorem addInductive_recursor_iota_sound env decls iota_specs env' uvars G spec ls :
  venv_add_inductive_block env decls iota_specs = Some env' ->
  In spec iota_specs ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = virs_uvars spec ->
  VIsDefEq env' uvars G
    (vapps (VConst (virs_rec_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
      (List.map (vinstL ls) (virs_prefix_args spec) ++
       List.map (vinstL ls) (virs_indices spec) ++
       [vapps (VConst (virs_ctor_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
         (List.map (vinstL ls) (virs_ctor_params spec) ++
          List.map (vinstL ls) (virs_ctor_fields spec))]))
    (vapps (vinstL ls (virs_rhs spec))
      (List.map (vinstL ls) (virs_prefix_args spec) ++
       List.map (vinstL ls) (virs_ctor_fields spec)))
    (vinstL ls (virs_type spec)).
Proof.
  intros Hblock Hin Hwf Hlen.
  eapply recursor_iota_defeq_sound_venv; [| exact Hwf | exact Hlen].
  eapply addInductive_iota_rule_in_venv; eassumption.
Qed.

(* Executable Checker Bridges for core_reduce_projection_with & core_reduce_recursor *)
Theorem core_reduce_projection_sound_bridge
    rec reduce env venv g owner idx value rhs uvars G spec ls :
  core_reduce_projection_with rec reduce env g owner idx value = Accept (Some rhs) ->
  venv_defeqs venv (vproj_defeq_of_spec spec) ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = vprs_uvars spec ->
  vprs_owner spec = owner ->
  vprs_idx spec = idx ->
  nth_error (vprs_fields spec) idx = Some (vprs_field_val spec) ->
  exists reduced ctor_name ctor_us ctor_args ci,
    fst (core_spine reduced []) = EConst ctor_name ctor_us /\
    snd (core_spine reduced []) = ctor_args /\
    core_constructor env ctor_name = Some ci /\
    ctor_induct ci = owner /\
    idx < ctor_num_fields ci /\
    List.length ctor_args = ctor_num_params ci + ctor_num_fields ci /\
    nth_error ctor_args (ctor_num_params ci + idx) = Some rhs /\
    VIsDefEq venv uvars G
      (vproj_expr owner idx
        (List.map (vlevel_inst ls) (vprs_us spec))
        (List.map (vinstL ls) (vprs_params spec))
        (vapps (VConst (vprs_ctor spec) (List.map (vlevel_inst ls) (vprs_us spec)))
          (List.map (vinstL ls) (vprs_params spec) ++
           List.map (vinstL ls) (vprs_fields spec))))
      (vinstL ls (vprs_field_val spec))
      (vinstL ls (vprs_field_ty spec)).
Proof.
  intros Hred Hmem Hwf Hlen Howner Hidx Hnth.
  unfold core_reduce_projection_with in Hred.
  destruct (reduce g value) as [r0|err|why]; simpl in Hred; [|discriminate..].
  set (step2 := match r0 with
                | ELit (LitString s) =>
                    expanded <- core_expand_string s ;; whnf_method rec g expanded
                | _ => Accept r0
                end) in *.
  destruct step2 as [reduced|err|why]; simpl in Hred; [|discriminate..].
  destruct (core_spine reduced []) as [head args] eqn:Hsp.
  destruct head as [| | | |cname cus| | | | | | |]; try discriminate.
  destruct (core_constructor env cname) as [ci|] eqn:Hci; [|discriminate].
  destruct (name_eqb (ctor_induct ci) owner && (idx <? ctor_num_fields ci) &&
            Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci))
    eqn:Hcond; [|discriminate].
  inversion Hred as [Hnth_rhs].
  apply andb_true_iff in Hcond as [Hcond1 Hlen_args].
  apply andb_true_iff in Hcond1 as [Hname_eq Hlt].
  apply name_eqb_eq in Hname_eq.
  apply Nat.ltb_lt in Hlt.
  apply Nat.eqb_eq in Hlen_args.
  exists reduced, cname, cus, args, ci.
  rewrite Hsp. simpl.
  repeat split; try assumption.
  subst idx. rewrite <- Howner.
  eapply vproj_iota_defeq_sound; eassumption.
Qed.

Theorem core_reduce_recursor_sound_bridge
    rec fuel env venv g e rhs uvars G spec ls :
  core_reduce_recursor rec fuel env g e = Accept (Some rhs) ->
  venv_defeqs venv (viota_defeq_of_spec spec) ->
  Forall (vlevel_wf uvars) ls ->
  List.length ls = virs_uvars spec ->
  exists rec_name rec_us args d info major owner major_whnf ctor_name ctor_us fields rule ci,
    core_spine e [] = (EConst rec_name rec_us, args) /\
    find_decl rec_name env = Some d /\
    decl_kind_of d = DRecursor info /\
    nth_error args (rec_num_params info + rec_num_motives info + rec_num_minors info + rec_num_indices info) = Some major /\
    core_major_induct (rec_num_params info + rec_num_motives info + rec_num_minors info + rec_num_indices info) (decl_type d) = Some owner /\
    core_to_constructor rec fuel env g owner (rec_k info) major = Accept major_whnf /\
    core_spine major_whnf [] = (EConst ctor_name ctor_us, fields) /\
    core_find_rule ctor_name (rec_rules info) = Some rule /\
    core_constructor env ctor_name = Some ci /\
    rhs = core_apps (subst_levels (decl_params d) rec_us (rule_rhs rule))
            (firstn (rec_num_params info + rec_num_motives info + rec_num_minors info) args ++
             skipn (ctor_num_params ci) fields ++
             skipn (S (rec_num_params info + rec_num_motives info + rec_num_minors info + rec_num_indices info)) args) /\
    VIsDefEq venv uvars G
      (vapps (VConst (virs_rec_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
        (List.map (vinstL ls) (virs_prefix_args spec) ++
         List.map (vinstL ls) (virs_indices spec) ++
         [vapps (VConst (virs_ctor_name spec) (List.map (vlevel_inst ls) (virs_us spec)))
           (List.map (vinstL ls) (virs_ctor_params spec) ++
            List.map (vinstL ls) (virs_ctor_fields spec))]))
      (vapps (vinstL ls (virs_rhs spec))
        (List.map (vinstL ls) (virs_prefix_args spec) ++
         List.map (vinstL ls) (virs_ctor_fields spec)))
      (vinstL ls (virs_type spec)).
Proof.
  intros Hred Hmem Hwf Hlen.
  unfold core_reduce_recursor in Hred.
  destruct (core_spine e []) as [head args] eqn:Hsp.
  destruct head as [| | | |rname rus| | | | | | |]; try discriminate.
  destruct (find_decl rname env) as [d|] eqn:Hd; [|discriminate].
  destruct (decl_kind_of d) eqn:Hkind; try discriminate.
  rename r into info.
  set (first_idx := rec_num_params info + rec_num_motives info + rec_num_minors info) in *.
  set (major_idx := first_idx + rec_num_indices info) in *.
  destruct (nth_error args major_idx) as [major|] eqn:Hmaj; [|discriminate].
  destruct (core_major_induct major_idx (decl_type d)) as [owner|] eqn:Hown; [|discriminate].
  destruct (core_to_constructor rec fuel env g owner (rec_k info) major)
    as [major_whnf|err|why] eqn:Htoc; simpl in Hred; [|discriminate..].
  destruct (core_spine major_whnf []) as [ctor fields] eqn:Hsp_maj.
  destruct ctor as [| | | |cname cus| | | | | | |]; try discriminate.
  destruct (core_find_rule cname (rec_rules info)) as [rule|] eqn:Hrule; [|discriminate].
  destruct (core_constructor env cname) as [ci|] eqn:Hci; [|discriminate].
  destruct (negb (name_eqb (ctor_induct ci) owner &&
                  Nat.eqb (List.length fields) (ctor_num_params ci + ctor_num_fields ci) &&
                  Nat.eqb (rule_nfields rule) (ctor_num_fields ci) &&
                  Nat.eqb (List.length rus) (List.length (decl_params d))));
    [discriminate|].
  inversion Hred as [Hrhs].
  exists rname, rus, args, d, info, major, owner, major_whnf, cname, cus, fields, rule, ci.
  repeat split; try reflexivity; try assumption.
  eapply recursor_iota_defeq_sound_venv; eassumption.
Qed.

(* ========================================================================= *)
(* 6. Soundness Bridge for Kernel Type Inference, WHNF, DefEq & Admission    *)
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

Theorem infer_proj_sound_bridge rec fuel env venv ps checking g owner idx val fty G val' proj' fty' :
  infer_step rec fuel env ps checking g (EProj owner idx val) = Accept fty ->
  TrExprS venv ps G val val' ->
  TrProj venv (List.length ps) G owner idx val' proj' fty' ->
  TrExpr venv ps G fty fty' ->
  exists info,
    core_inductive env owner = Some info /\
    core_infer_projection (if checking then rec else inference_only rec) fuel env g owner idx val = Accept fty /\
    TrTyping venv ps G (EProj owner idx val) fty proj' fty'.
Proof.
  intros Hinf Hval Hproj Hfty.
  simpl in Hinf.
  destruct (core_inductive env owner) as [info|] eqn:Hind; [|discriminate].
  exists info. split; [reflexivity |]. split; [exact Hinf |].
  split; [| split].
  - apply TrExprS_to_TrExpr. eapply TrExprS_proj; eassumption.
  - exact Hfty.
  - eapply TrProj_has_type; exact Hproj.
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

Print Assumptions vinstL_vapps.
Print Assumptions vliftN_vapps.
Print Assumptions vclosedN_vapps.
Print Assumptions TrProj_has_type.
Print Assumptions TrProj_monotonic_env.
Print Assumptions vproj_iota_defeq_sound.
Print Assumptions check_levels_sound_TrLevels.
Print Assumptions levels_equiv_sound_TrLevels.
Print Assumptions VHasType_vinst0_from_beta.
Print Assumptions TrExprS_has_type.
Print Assumptions TrExpr_proj_unconditional.
Print Assumptions TrTyping_proj_unconditional.
Print Assumptions TrExpr_monotonic_env.
Print Assumptions TrTyping_monotonic_env.
Print Assumptions recursor_iota_defeq_sound_venv.
Print Assumptions venv_add_inductive_block_ordered.
Print Assumptions addInductive_iota_rule_in_venv.
Print Assumptions addInductive_recursor_iota_sound.
Print Assumptions core_reduce_projection_sound_bridge.
Print Assumptions core_reduce_recursor_sound_bridge.
Print Assumptions get_constant_sound_bridge.
Print Assumptions infer_sort_sound_bridge.
Print Assumptions infer_const_sound_bridge.
Print Assumptions infer_proj_sound_bridge.
Print Assumptions check_bridge_soundness.
Print Assumptions checked_constant_extends_venv_wf.
