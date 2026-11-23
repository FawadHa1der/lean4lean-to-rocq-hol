(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.

   End-to-end Lean4Lean/Verify/ foundation in Rocq:
   - Hybrid local contexts VLCtx (VLLam + VLLet for both EBVar and EFVar),
   - Exact literal translations (natLit, trCharList, trStrLit),
   - Genuine non-vacuous structure projection relation (VTrProj & VProjTelescope),
   - Semantic primitives specification (HasPrimitives),
   - Full 12-constructor VTrExprS / VTrExpr / VTrTyping and VTrCtx,
   - Environment soundness invariant (VEnvSound) with unconditional empty model,
   - Full lifting (VLBoundLift), single & simultaneous substitution
     (VLBoundInstLam, VLBoundInstLet, subst_many), universe instantiation,
     context conversion, uniqueness up to VIsDefEqU, alpha-equality, and
     exact embedding of InferSoundness.trE / TrBCtx.
   Zero axioms. *)
From Stdlib Require Import List Bool Arith PeanoNat NArith String Ascii Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness EagerPolicy Checker
  Primitives Declarations SemanticModel DeclarativeTyping TypingLemmas
  InferSoundness CheckerSoundness SubstTheory StrongTyping EnvDeclTheory
  PatternConfluence.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma vliftN_add_le e n m k :
  k <= n -> vliftN m k (vliftN n 0 e) = vliftN (m + n) 0 e.
Proof. intros H. apply vliftN_vliftN; lia. Qed.

Lemma vinst_vliftN_ge e v n k :
  k <= n -> vinst (vliftN (S n) 0 e) v k = vliftN n 0 e.
Proof. intros H. apply vinst_vliftN_gen; lia. Qed.

Lemma vinst_vliftN_le e v n j :
  vliftN n 0 (vinst e v j) = vinst (vliftN n 0 e) v (n + j).
Proof. apply vliftN_vinst_lo; lia. Qed.

Lemma vliftN_closed_eq e n k k0 :
  vclosedN k0 e -> k0 <= k -> vliftN n k e = e.
Proof. intros Hc Hle. apply vclosedN_vliftN_eq. eapply vclosedN_mono; eassumption. Qed.

(* ========================================================================= *)
(* 1. Hybrid Local Contexts (VLCtx): VLLam + VLLet for EBVar & EFVar         *)
(* ========================================================================= *)

Inductive VLCtxEntry : Type :=
| VLLam (ty : VExpr)
| VLLet (ty val : VExpr).

Record VLCtx : Type := {
  vl_free : list (name * VLCtxEntry);
  vl_bound : list VLCtxEntry
}.

Definition vl_empty : VLCtx := {| vl_free := []; vl_bound := [] |}.

Definition vl_push_lam (L : VLCtx) (ty : VExpr) : VLCtx :=
  {| vl_free := vl_free L; vl_bound := VLLam ty :: vl_bound L |}.

Definition vl_push_let (L : VLCtx) (ty val : VExpr) : VLCtx :=
  {| vl_free := vl_free L; vl_bound := VLLet ty val :: vl_bound L |}.

Definition vl_push_free_lam (L : VLCtx) (n : name) (ty : VExpr) : VLCtx :=
  {| vl_free := (n, VLLam ty) :: vl_free L; vl_bound := vl_bound L |}.

Definition vl_push_free_let (L : VLCtx) (n : name) (ty val : VExpr) : VLCtx :=
  {| vl_free := (n, VLLet ty val) :: vl_free L; vl_bound := vl_bound L |}.

Fixpoint vlentries_to_ctx (es : list VLCtxEntry) : list VExpr :=
  match es with
  | [] => []
  | VLLam ty :: rest => ty :: vlentries_to_ctx rest
  | VLLet _ _ :: rest => vlentries_to_ctx rest
  end.

Definition vl_free_ctx (fs : list (name * VLCtxEntry)) : list VExpr :=
  vlentries_to_ctx (map snd fs).

Definition vl_ctx (L : VLCtx) : list VExpr :=
  vlentries_to_ctx (vl_bound L) ++ vl_free_ctx (vl_free L).

Definition vl_bound_lams (L : VLCtx) : nat :=
  List.length (vlentries_to_ctx (vl_bound L)).

Lemma vlentries_to_ctx_app es1 es2 :
  vlentries_to_ctx (es1 ++ es2) = vlentries_to_ctx es1 ++ vlentries_to_ctx es2.
Proof.
  induction es1 as [|[ty|ty val] rest IH]; simpl; [reflexivity | f_equal |]; exact IH.
Qed.

Lemma vl_ctx_push_lam L ty : vl_ctx (vl_push_lam L ty) = ty :: vl_ctx L.
Proof. reflexivity. Qed.

Lemma vl_ctx_push_let L ty val : vl_ctx (vl_push_let L ty val) = vl_ctx L.
Proof. reflexivity. Qed.

Lemma vl_bound_lams_push_lam L ty :
  vl_bound_lams (vl_push_lam L ty) = S (vl_bound_lams L).
Proof. reflexivity. Qed.

Lemma vl_bound_lams_push_let L ty val :
  vl_bound_lams (vl_push_let L ty val) = vl_bound_lams L.
Proof. reflexivity. Qed.

Fixpoint vl_lookup_bound (es : list VLCtxEntry) (i : nat) (lam_depth : nat)
    : option (VExpr * VExpr) :=
  match es, i with
  | [], _ => None
  | VLLam ty :: _, 0 => Some (VBVar lam_depth, vliftN (S lam_depth) 0 ty)
  | VLLet ty val :: _, 0 => Some (vliftN lam_depth 0 val, vliftN lam_depth 0 ty)
  | VLLam _ :: rest, S i => vl_lookup_bound rest i (S lam_depth)
  | VLLet _ _ :: rest, S i => vl_lookup_bound rest i lam_depth
  end.

Fixpoint vl_lookup_free (fs : list (name * VLCtxEntry)) (n : name) (lam_depth : nat)
    : option (VExpr * VExpr) :=
  match fs with
  | [] => None
  | (m, VLLam ty) :: rest =>
      if name_eqb n m then Some (VBVar lam_depth, vliftN (S lam_depth) 0 ty)
      else vl_lookup_free rest n (S lam_depth)
  | (m, VLLet ty val) :: rest =>
      if name_eqb n m then Some (vliftN lam_depth 0 val, vliftN lam_depth 0 ty)
      else vl_lookup_free rest n lam_depth
  end.

Definition vl_bvar (L : VLCtx) (i : nat) : option (VExpr * VExpr) :=
  vl_lookup_bound (vl_bound L) i 0.

Definition vl_fvar (L : VLCtx) (n : name) : option (VExpr * VExpr) :=
  vl_lookup_free (vl_free L) n (vl_bound_lams L).

Lemma vl_lookup_bound_shift_at es : forall i d n k e ty,
  k <= d ->
  vl_lookup_bound es i d = Some (e, ty) ->
  vl_lookup_bound es i (n + d) = Some (vliftN n k e, vliftN n k ty).
Proof.
  induction es as [|[A|A v] rest IH]; intros [|i] d n k e ty Hkd H; simpl in *;
    try discriminate.
  - inversion H; subst; clear H.
    f_equal. f_equal.
    + simpl. unfold vliftVar. destruct (Nat.ltb_spec d k); [lia | reflexivity].
    + rewrite vliftN_add_le by lia. f_equal. lia.
  - replace (S (n + d)) with (n + S d) by lia.
    apply IH; [lia | exact H].
  - inversion H; subst; clear H.
    f_equal. f_equal; rewrite vliftN_add_le by lia; reflexivity.
  - apply IH; assumption.
Qed.

Lemma vl_lookup_free_shift_at fs n : forall d m k e ty,
  k <= d ->
  vl_lookup_free fs n d = Some (e, ty) ->
  vl_lookup_free fs n (m + d) = Some (vliftN m k e, vliftN m k ty).
Proof.
  induction fs as [|[nm [A|A v]] rest IH]; intros d m k e ty Hkd H; simpl in *;
    try discriminate.
  - destruct (name_eqb n nm).
    + inversion H; subst; clear H.
      f_equal. f_equal.
      * simpl. unfold vliftVar. destruct (Nat.ltb_spec d k); [lia | reflexivity].
      * rewrite vliftN_add_le by lia. f_equal. lia.
    + replace (S (m + d)) with (m + S d) by lia.
      apply IH; [lia | exact H].
  - destruct (name_eqb n nm).
    + inversion H; subst; clear H.
      f_equal. f_equal; rewrite vliftN_add_le by lia; reflexivity.
    + apply IH; assumption.
Qed.

Lemma vl_lookup_bound_app_l es1 es2 : forall i d,
  i < List.length es1 ->
  vl_lookup_bound (es1 ++ es2) i d = vl_lookup_bound es1 i d.
Proof.
  induction es1 as [|[A|A v] rest IH]; intros [|i] d Hlt; simpl in *; try lia; auto.
  - apply IH. lia.
  - apply IH. lia.
Qed.

Lemma vl_lookup_bound_app_r es1 es2 : forall i d,
  vl_lookup_bound (es1 ++ es2) (List.length es1 + i) d =
  vl_lookup_bound es2 i (List.length (vlentries_to_ctx es1) + d).
Proof.
  induction es1 as [|[A|A v] rest IH]; intros i d; simpl.
  - reflexivity.
  - rewrite IH. f_equal. lia.
  - exact (IH i d).
Qed.

Inductive VLCtxEntriesWF (env : VEnv) (U : nat) (base : list VExpr)
    : list VLCtxEntry -> Prop :=
| VLCtxEntriesWF_nil : VLCtxEntriesWF env U base []
| VLCtxEntriesWF_lam : forall ty rest,
    VLCtxEntriesWF env U base rest ->
    VIsType env U (vlentries_to_ctx rest ++ base) ty ->
    VLCtxEntriesWF env U base (VLLam ty :: rest)
| VLCtxEntriesWF_let : forall ty val rest,
    VLCtxEntriesWF env U base rest ->
    VHasType env U (vlentries_to_ctx rest ++ base) val ty ->
    VLCtxEntriesWF env U base (VLLet ty val :: rest).

Definition VLCtxWF (env : VEnv) (U : nat) (L : VLCtx) : Prop :=
  VLCtxEntriesWF env U [] (map snd (vl_free L)) /\
  VLCtxEntriesWF env U (vl_free_ctx (vl_free L)) (vl_bound L).

Lemma VLCtxEntriesWF_to_VCtxWF env U base es :
  VCtxWF env U base ->
  VLCtxEntriesWF env U base es ->
  VCtxWF env U (vlentries_to_ctx es ++ base).
Proof.
  intros Hbase Hwf. induction Hwf; simpl; auto.
Qed.

Lemma VLCtxWF_to_VCtxWF env U L :
  VLCtxWF env U L -> VCtxWF env U (vl_ctx L).
Proof.
  intros [Hfree Hbound].
  unfold vl_ctx. apply VLCtxEntriesWF_to_VCtxWF; [|exact Hbound].
  unfold vl_free_ctx.
  rewrite <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L)))).
  apply VLCtxEntriesWF_to_VCtxWF; [exact I | exact Hfree].
Qed.

Lemma VLCtxWF_empty env U : VLCtxWF env U vl_empty.
Proof. split; constructor. Qed.

Lemma VLCtxWF_push_lam env U L ty :
  VLCtxWF env U L ->
  VIsType env U (vl_ctx L) ty ->
  VLCtxWF env U (vl_push_lam L ty).
Proof.
  intros [Hf Hb] Hty. split; [exact Hf |].
  constructor; assumption.
Qed.

Lemma VLCtxWF_push_let env U L ty val :
  VLCtxWF env U L ->
  VHasType env U (vl_ctx L) val ty ->
  VLCtxWF env U (vl_push_let L ty val).
Proof.
  intros [Hf Hb] Hv. split; [exact Hf |].
  constructor; assumption.
Qed.

Lemma VLCtxEntriesWF_mono env1 env2 U base es :
  venv_ordered env1 env2 ->
  VLCtxEntriesWF env1 U base es ->
  VLCtxEntriesWF env2 U base es.
Proof.
  intros Hord H. induction H; constructor; auto.
  - eapply VEnvOrdered_preserve_VIsType; eassumption.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
Qed.

Lemma VLCtxWF_mono env1 env2 U L :
  venv_ordered env1 env2 ->
  VLCtxWF env1 U L ->
  VLCtxWF env2 U L.
Proof.
  intros Hord [Hf Hb]. split; eapply VLCtxEntriesWF_mono; eassumption.
Qed.

Lemma VCtxLiftN_app_prefix pre G :
  VCtxLiftN (List.length pre) 0 G (pre ++ G).
Proof. apply VCtxLiftN_zero. reflexivity. Qed.

Lemma VLookup_app_prefix pre G A :
  VLookup (pre ++ A :: G) (List.length pre) (vliftN (S (List.length pre)) 0 A).
Proof.
  induction pre as [|B pre IH]; simpl.
  - change (vliftN 1 0 A) with (vlift A). constructor.
  - pose proof (VLookupSucc B IH) as Hs.
    unfold vlift in Hs. rewrite vliftN_comp in Hs. exact Hs.
Qed.

Lemma vl_lookup_bound_has_type_gen env U base es :
  VEnvClosed env ->
  VLCtxEntriesWF env U base es ->
  forall pre i e ty,
    vl_lookup_bound es i (List.length pre) = Some (e, ty) ->
    VHasType env U (pre ++ vlentries_to_ctx es ++ base) e ty.
Proof.
  intros Hcl Hwf. induction Hwf as [| A rest Hrest IH HA | A v rest Hrest IH Hv];
    intros pre [|i] e ty Hlk; simpl in *; try discriminate.
  - inversion Hlk; subst e ty; clear Hlk.
    apply VDF_bvar. apply VLookup_app_prefix.
  - specialize (IH (pre ++ [A]) i e ty).
    rewrite List.length_app in IH. simpl in IH.
    replace (List.length pre + 1) with (S (List.length pre)) in IH by lia.
    rewrite <- app_assoc in IH. simpl in IH.
    exact (IH Hlk).
  - inversion Hlk; subst e ty; clear Hlk.
    eapply VIsDefEq_weakN; [exact Hcl | exact Hv | apply VCtxLiftN_app_prefix].
  - exact (IH pre i e ty Hlk).
Qed.

Lemma vl_lookup_bound_has_type env U L i e ty :
  VEnvClosed env ->
  VLCtxWF env U L ->
  vl_bvar L i = Some (e, ty) ->
  VHasType env U (vl_ctx L) e ty.
Proof.
  intros Hcl [_ Hb] Hlk.
  unfold vl_ctx.
  change (vlentries_to_ctx (vl_bound L) ++ vl_free_ctx (vl_free L))
    with ([] ++ vlentries_to_ctx (vl_bound L) ++ vl_free_ctx (vl_free L)).
  eapply vl_lookup_bound_has_type_gen; [exact Hcl | exact Hb | exact Hlk].
Qed.

Lemma vl_lookup_free_has_type_gen env U fs :
  VEnvClosed env ->
  VLCtxEntriesWF env U [] (map snd fs) ->
  forall pre n e ty,
    vl_lookup_free fs n (List.length pre) = Some (e, ty) ->
    VHasType env U (pre ++ vl_free_ctx fs) e ty.
Proof.
  intros Hcl.
  induction fs as [|[m [A|A v]] rest IH]; intros Hwf pre n e ty Hlk; simpl in *;
    try discriminate.
  - inversion Hwf as [| ? ? Hrest Hty |]; subst.
    destruct (name_eqb n m).
    + inversion Hlk; subst e ty; clear Hlk.
      apply VDF_bvar. unfold vl_free_ctx. simpl. apply VLookup_app_prefix.
    + specialize (IH Hrest (pre ++ [A]) n e ty).
      rewrite List.length_app in IH. simpl in IH.
      replace (List.length pre + 1) with (S (List.length pre)) in IH by lia.
      unfold vl_free_ctx in *. simpl.
      rewrite <- app_assoc in IH. simpl in IH.
      exact (IH Hlk).
  - inversion Hwf as [| | ? ? ? Hrest Hv]; subst.
    destruct (name_eqb n m).
    + inversion Hlk; subst e ty; clear Hlk.
      unfold vl_free_ctx. simpl.
      rewrite app_nil_r in Hv.
      eapply VIsDefEq_weakN; [exact Hcl | exact Hv | apply VCtxLiftN_app_prefix].
    + exact (IH Hrest pre n e ty Hlk).
Qed.

Lemma vl_lookup_free_has_type env U L n e ty :
  VEnvClosed env ->
  VLCtxWF env U L ->
  vl_fvar L n = Some (e, ty) ->
  VHasType env U (vl_ctx L) e ty.
Proof.
  intros Hcl [Hf _] Hlk.
  unfold vl_ctx, vl_fvar, vl_bound_lams in *.
  eapply vl_lookup_free_has_type_gen; [exact Hcl | exact Hf | exact Hlk].
Qed.

Inductive VLCtxEntriesDefEq (env : VEnv) (U : nat) (base1 base2 : list VExpr)
    : list VLCtxEntry -> list VLCtxEntry -> Prop :=
| VLCtxEntriesDefEq_nil : VLCtxEntriesDefEq env U base1 base2 [] []
| VLCtxEntriesDefEq_lam : forall A1 A2 rest1 rest2 u,
    VLCtxEntriesDefEq env U base1 base2 rest1 rest2 ->
    VIsDefEq env U (vlentries_to_ctx rest1 ++ base1) A1 A2 (VSort u) ->
    VLCtxEntriesDefEq env U base1 base2 (VLLam A1 :: rest1) (VLLam A2 :: rest2)
| VLCtxEntriesDefEq_let : forall A1 v1 A2 v2 rest1 rest2 u,
    VLCtxEntriesDefEq env U base1 base2 rest1 rest2 ->
    VIsDefEq env U (vlentries_to_ctx rest1 ++ base1) A1 A2 (VSort u) ->
    VIsDefEq env U (vlentries_to_ctx rest1 ++ base1) v1 v2 A1 ->
    VLCtxEntriesDefEq env U base1 base2 (VLLet A1 v1 :: rest1) (VLLet A2 v2 :: rest2).

Definition VLCtxDefEq (env : VEnv) (U : nat) (L1 L2 : VLCtx) : Prop :=
  map fst (vl_free L1) = map fst (vl_free L2) /\
  VLCtxEntriesDefEq env U [] [] (map snd (vl_free L1)) (map snd (vl_free L2)) /\
  VLCtxEntriesDefEq env U (vl_free_ctx (vl_free L1)) (vl_free_ctx (vl_free L2))
    (vl_bound L1) (vl_bound L2).

Lemma VLCtxEntriesDefEq_len_ctx env U b1 b2 es1 es2 :
  VLCtxEntriesDefEq env U b1 b2 es1 es2 ->
  List.length (vlentries_to_ctx es1) = List.length (vlentries_to_ctx es2).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma VLCtxEntriesDefEq_to_VIsDefEqCtx env U b1 b2 es1 es2 :
  VIsDefEqCtx env U [] b1 b2 ->
  VLCtxEntriesDefEq env U b1 b2 es1 es2 ->
  VIsDefEqCtx env U [] (vlentries_to_ctx es1 ++ b1) (vlentries_to_ctx es2 ++ b2).
Proof.
  intros Hb H. induction H; simpl; auto.
  econstructor; eassumption.
Qed.

Lemma VLCtxDefEq_to_VIsDefEqCtx env U L1 L2 :
  VLCtxDefEq env U L1 L2 ->
  VIsDefEqCtx env U [] (vl_ctx L1) (vl_ctx L2).
Proof.
  intros [_ [Hf Hb]].
  unfold vl_ctx. apply VLCtxEntriesDefEq_to_VIsDefEqCtx; [|exact Hb].
  unfold vl_free_ctx.
  rewrite <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L1)))),
          <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L2)))).
  apply VLCtxEntriesDefEq_to_VIsDefEqCtx; [constructor | exact Hf].
Qed.

Lemma VLCtxEntriesDefEq_refl env U base es :
  VEnvWF env ->
  VCtxWF env U base ->
  VLCtxEntriesWF env U base es ->
  VLCtxEntriesDefEq env U base base es es.
Proof.
  intros Hwf Hbase H. induction H.
  - constructor.
  - destruct H0 as [u Hu]. econstructor; eassumption.
  - destruct (VIsDefEq_isType Hwf (VLCtxEntriesWF_to_VCtxWF Hbase H) H0) as [u Hu].
    econstructor; eassumption.
Qed.

Lemma VLCtxDefEq_refl env U L :
  VEnvWF env ->
  VLCtxWF env U L ->
  VLCtxDefEq env U L L.
Proof.
  intros Hwf [Hf Hb]. repeat split.
  - apply VLCtxEntriesDefEq_refl; [exact Hwf | exact I | exact Hf].
  - apply VLCtxEntriesDefEq_refl; [exact Hwf | | exact Hb].
    unfold vl_free_ctx.
    rewrite <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L)))).
    apply VLCtxEntriesWF_to_VCtxWF; [exact I | exact Hf].
Qed.

Lemma VLCtxEntriesDefEq_symm env U b1 b2 es1 es2 :
  VEnvClosed env ->
  VIsDefEqCtx env U [] b1 b2 ->
  VLCtxEntriesDefEq env U b1 b2 es1 es2 ->
  VLCtxEntriesDefEq env U b2 b1 es2 es1.
Proof.
  intros Hcl Hb H. induction H.
  - constructor.
  - pose proof (VLCtxEntriesDefEq_to_VIsDefEqCtx Hb H) as Hctx.
    econstructor; [exact IHVLCtxEntriesDefEq |].
    apply VDF_symm. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact H0].
  - pose proof (VLCtxEntriesDefEq_to_VIsDefEqCtx Hb H) as Hctx.
    econstructor; [exact IHVLCtxEntriesDefEq | |].
    + apply VDF_symm. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact H0].
    + apply VDF_symm. eapply VDF_defeqDF;
        [eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact H0] |].
      eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact H1].
Qed.

Lemma VLCtxDefEq_symm env U L1 L2 :
  VEnvClosed env ->
  VLCtxDefEq env U L1 L2 ->
  VLCtxDefEq env U L2 L1.
Proof.
  intros Hcl [Hn [Hf Hb]].
  assert (Hfc : VIsDefEqCtx env U [] (vl_free_ctx (vl_free L1)) (vl_free_ctx (vl_free L2))).
  { unfold vl_free_ctx.
    rewrite <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L1)))),
            <- (app_nil_r (vlentries_to_ctx (map snd (vl_free L2)))).
    apply VLCtxEntriesDefEq_to_VIsDefEqCtx; [constructor | exact Hf]. }
  repeat split.
  - symmetry. exact Hn.
  - apply VLCtxEntriesDefEq_symm; [exact Hcl | constructor | exact Hf].
  - apply VLCtxEntriesDefEq_symm; [exact Hcl | exact Hfc | exact Hb].
Qed.

Lemma vl_lookup_bound_defeq_gen env U b1 b2 es1 es2 :
  VEnvClosed env ->
  VLCtxEntriesDefEq env U b1 b2 es1 es2 ->
  forall pre i e1 ty1,
    vl_lookup_bound es1 i (List.length pre) = Some (e1, ty1) ->
    exists e2 ty2,
      vl_lookup_bound es2 i (List.length pre) = Some (e2, ty2) /\
      VIsDefEq env U (pre ++ vlentries_to_ctx es1 ++ b1) e1 e2 ty1.
Proof.
  intros Hcl.
  induction 1 as [| A1 A2 r1 r2 u Hr IH HA | A1 v1 A2 v2 r1 r2 u Hr IH HA Hv];
    intros pre [|i] e1 ty1 Hlk; simpl in *; try discriminate.
  - inversion Hlk; subst e1 ty1; clear Hlk.
    exists (VBVar (List.length pre)), (vliftN (S (List.length pre)) 0 A2).
    split; [reflexivity | apply VDF_bvar; apply VLookup_app_prefix].
  - specialize (IH (pre ++ [A1]) i e1 ty1).
    rewrite List.length_app in IH. simpl in IH.
    replace (List.length pre + 1) with (S (List.length pre)) in IH by lia.
    rewrite <- app_assoc in IH. simpl in IH.
    exact (IH Hlk).
  - inversion Hlk; subst e1 ty1; clear Hlk.
    exists (vliftN (List.length pre) 0 v2), (vliftN (List.length pre) 0 A2).
    split; [reflexivity |].
    eapply VIsDefEq_weakN; [exact Hcl | exact Hv | apply VCtxLiftN_app_prefix].
  - exact (IH pre i e1 ty1 Hlk).
Qed.

Lemma vl_lookup_bound_defeq env U L1 L2 i e1 ty1 :
  VEnvClosed env ->
  VLCtxDefEq env U L1 L2 ->
  vl_bvar L1 i = Some (e1, ty1) ->
  exists e2 ty2,
    vl_bvar L2 i = Some (e2, ty2) /\
    VIsDefEq env U (vl_ctx L1) e1 e2 ty1.
Proof.
  intros Hcl [_ [_ Hb]] Hlk.
  unfold vl_ctx, vl_bvar in *.
  change (vlentries_to_ctx (vl_bound L1) ++ vl_free_ctx (vl_free L1))
    with ([] ++ vlentries_to_ctx (vl_bound L1) ++ vl_free_ctx (vl_free L1)).
  eapply vl_lookup_bound_defeq_gen with (pre := []); [exact Hcl | exact Hb | exact Hlk].
Qed.

Lemma vl_lookup_free_defeq_gen env U fs1 : forall fs2,
  VEnvClosed env ->
  map fst fs1 = map fst fs2 ->
  VLCtxEntriesDefEq env U [] [] (map snd fs1) (map snd fs2) ->
  forall pre n e1 ty1,
    vl_lookup_free fs1 n (List.length pre) = Some (e1, ty1) ->
    exists e2 ty2,
      vl_lookup_free fs2 n (List.length pre) = Some (e2, ty2) /\
      VIsDefEq env U (pre ++ vl_free_ctx fs1) e1 e2 ty1.
Proof.
  induction fs1 as [|[m1 [A1|A1 v1]] r1 IH]; intros [|[m2 e2'] r2] Hcl Hnames Hdef pre n e1 ty1 Hlk;
    simpl in *; try discriminate.
  - injection Hnames as Hnm Hnr; subst m2.
    inversion Hdef as [| ? A2 ? ? u Hdr HA |]; subst; clear Hdef.
    destruct (name_eqb n m1).
    + inversion Hlk; subst e1 ty1; clear Hlk.
      exists (VBVar (List.length pre)), (vliftN (S (List.length pre)) 0 A2).
      split; [reflexivity | apply VDF_bvar; unfold vl_free_ctx; simpl; apply VLookup_app_prefix].
    + specialize (IH r2 Hcl Hnr Hdr (pre ++ [A1]) n e1 ty1).
      rewrite List.length_app in IH. simpl in IH.
      replace (List.length pre + 1) with (S (List.length pre)) in IH by lia.
      unfold vl_free_ctx in *. simpl.
      rewrite <- app_assoc in IH. simpl in IH.
      exact (IH Hlk).
  - injection Hnames as Hnm Hnr; subst m2.
    inversion Hdef as [| | ? ? A2 v2 ? ? u Hdr HA Hv]; subst; clear Hdef.
    destruct (name_eqb n m1).
    + inversion Hlk; subst e1 ty1; clear Hlk.
      exists (vliftN (List.length pre) 0 v2), (vliftN (List.length pre) 0 A2).
      split; [reflexivity |].
      unfold vl_free_ctx. simpl.
      rewrite app_nil_r in Hv.
      eapply VIsDefEq_weakN; [exact Hcl | exact Hv | apply VCtxLiftN_app_prefix].
    + exact (IH r2 Hcl Hnr Hdr pre n e1 ty1 Hlk).
Qed.

Lemma vl_lookup_free_defeq env U L1 L2 n e1 ty1 :
  VEnvClosed env ->
  VLCtxDefEq env U L1 L2 ->
  vl_fvar L1 n = Some (e1, ty1) ->
  exists e2 ty2,
    vl_fvar L2 n = Some (e2, ty2) /\
    VIsDefEq env U (vl_ctx L1) e1 e2 ty1.
Proof.
  intros Hcl [Hn [Hf Hb]] Hlk.
  unfold vl_fvar, vl_bound_lams in *.
  rewrite <- (VLCtxEntriesDefEq_len_ctx Hb).
  unfold vl_ctx.
  apply vl_lookup_free_defeq_gen with (fs1 := vl_free L1); assumption.
Qed.

(* ========================================================================= *)
(* 2. Exact Literal Translations (natLit, trCharList, trStrLit)              *)
(* ========================================================================= *)

Definition natLit (n : N) : VExpr :=
  N.peano_rect (fun _ => VExpr)
    (VConst core_zero_name [])
    (fun _ acc => VApp (VConst core_succ_name []) acc)
    n.

Lemma natLit_0 : natLit 0%N = VConst core_zero_name [].
Proof. reflexivity. Qed.

Lemma natLit_succ n : natLit (N.succ n) = VApp (VConst core_succ_name []) (natLit n).
Proof. unfold natLit. rewrite N.peano_rect_succ. reflexivity. Qed.

Lemma natLit_pred_succ n :
  (n <> 0)%N ->
  natLit n = VApp (VConst core_succ_name []) (natLit (N.pred n)).
Proof.
  intros Hnz. rewrite <- (N.succ_pred n Hnz) at 1. apply natLit_succ.
Qed.

Lemma natLit_closed k n : vclosedN k (natLit n).
Proof.
  induction n using N.peano_ind; [rewrite natLit_0; exact I |].
  rewrite natLit_succ. simpl. split; [exact I | exact IHn].
Qed.

Lemma vliftN_natLit m k n : vliftN m k (natLit n) = natLit n.
Proof.
  induction n using N.peano_ind; [rewrite natLit_0; reflexivity |].
  rewrite natLit_succ. simpl. rewrite IHn. reflexivity.
Qed.

Lemma vinst_natLit n v k : vinst (natLit n) v k = natLit n.
Proof.
  induction n using N.peano_ind; [rewrite natLit_0; reflexivity |].
  rewrite natLit_succ. simpl. rewrite IHn. reflexivity.
Qed.

Lemma vinstL_natLit ls n : vinstL ls (natLit n) = natLit n.
Proof.
  induction n using N.peano_ind; [rewrite natLit_0; reflexivity |].
  rewrite natLit_succ. simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint trCharList (cs : list N) : VExpr :=
  let ch := VConst core_char_name [] in
  match cs with
  | [] => VApp (VConst (NameStr core_list_name "nil") [VLZero]) ch
  | c :: rest =>
      vapps (VConst (NameStr core_list_name "cons") [VLZero])
        [ch; VApp (VConst core_char_of_nat []) (natLit c); trCharList rest]
  end.

Definition trStrLit (s : string) : option VExpr :=
  match core_utf8 s with
  | Some cs => Some (VApp (VConst core_string_of_list []) (trCharList cs))
  | None => None
  end.

Lemma trCharList_closed k cs : vclosedN k (trCharList cs).
Proof.
  induction cs as [|c rest IH]; simpl; [split; exact I |].
  repeat split; try exact I; [apply natLit_closed | exact IH].
Qed.

Lemma vliftN_trCharList m k cs : vliftN m k (trCharList cs) = trCharList cs.
Proof.
  induction cs as [|c rest IH]; simpl; [reflexivity |].
  rewrite vliftN_natLit, IH. reflexivity.
Qed.

Lemma vinst_trCharList cs v k : vinst (trCharList cs) v k = trCharList cs.
Proof.
  induction cs as [|c rest IH]; simpl; [reflexivity |].
  rewrite vinst_natLit, IH. reflexivity.
Qed.

Lemma vinstL_trCharList ls cs : vinstL ls (trCharList cs) = trCharList cs.
Proof.
  induction cs as [|c rest IH]; simpl; [reflexivity |].
  rewrite vinstL_natLit, IH. reflexivity.
Qed.

Lemma trStrLit_closed k s e : trStrLit s = Some e -> vclosedN k e.
Proof.
  unfold trStrLit. destruct (core_utf8 s) as [cs|]; [|discriminate].
  intros H. inversion H; subst. simpl. split; [exact I | apply trCharList_closed].
Qed.

Lemma vliftN_trStrLit m k s e : trStrLit s = Some e -> vliftN m k e = e.
Proof.
  unfold trStrLit. destruct (core_utf8 s) as [cs|]; [|discriminate].
  intros H. inversion H; subst. simpl. rewrite vliftN_trCharList. reflexivity.
Qed.

Lemma vinst_trStrLit s e v k : trStrLit s = Some e -> vinst e v k = e.
Proof.
  unfold trStrLit. destruct (core_utf8 s) as [cs|]; [|discriminate].
  intros H. inversion H; subst. simpl. rewrite vinst_trCharList. reflexivity.
Qed.

Lemma vinstL_trStrLit ls s e : trStrLit s = Some e -> vinstL ls e = e.
Proof.
  unfold trStrLit. destruct (core_utf8 s) as [cs|]; [|discriminate].
  intros H. inversion H; subst. simpl. rewrite vinstL_trCharList. reflexivity.
Qed.

(* ========================================================================= *)
(* 3. Genuine Structure Projections (VTrProj & VProjTelescope)               *)
(* ========================================================================= *)

Inductive VTrProj (env : environment) (venv : VEnv) (U : nat) (G : list VExpr)
    (owner : name) (idx : nat) (struct_v proj_v field_ty : VExpr) : Prop :=
| VTrProj_intro : forall info ctor c d us params indices,
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    idx < ctor_num_fields c ->
    List.length params = ind_num_params info ->
    List.length indices = ind_num_indices info ->
    Forall (vlevel_wf U) us ->
    List.length us = List.length (decl_params d) ->
    VHasType venv U G struct_v (vapps (VConst owner us) (params ++ indices)) ->
    proj_v = vproj_expr owner idx us params struct_v ->
    VHasType venv U G proj_v field_ty ->
    VTrProj env venv U G owner idx struct_v proj_v field_ty.

Inductive VProjTelescope (env : environment) (venv : VEnv) (U : nat) (G : list VExpr)
    (owner : name) (us : list VLevel) (params : list VExpr) (sv : VExpr)
    (maybe_prop : bool) : nat -> nat -> VExpr -> VExpr -> Prop :=
| VPT_zero : forall idx ty dom body,
    VIsDefEqU venv U G ty (VForallE dom body) ->
    (maybe_prop = true -> VHasType venv U G dom (VSort VLZero)) ->
    VProjTelescope env venv U G owner us params sv maybe_prop 0 idx ty dom
| VPT_succ : forall skip idx ty dom body res,
    VIsDefEqU venv U G ty (VForallE dom body) ->
    (maybe_prop = true -> (forall b0, body <> vlift b0) -> VHasType venv U G dom (VSort VLZero)) ->
    VProjTelescope env venv U G owner us params sv maybe_prop skip (S idx)
      (vinst0 body (vproj_expr owner idx us params sv)) res ->
    VProjTelescope env venv U G owner us params sv maybe_prop (S skip) idx ty res.

Lemma VTrProj_has_type env venv U G owner idx sv pv fty :
  VTrProj env venv U G owner idx sv pv fty ->
  VHasType venv U G pv fty.
Proof. intros []. assumption. Qed.

Lemma VTrProj_monotonic_env env venv1 venv2 U G owner idx sv pv fty :
  venv_ordered venv1 venv2 ->
  VTrProj env venv1 U G owner idx sv pv fty ->
  VTrProj env venv2 U G owner idx sv pv fty.
Proof.
  intros Hord [info ctor c d us params indices H1 H2 H3 H4 H5 H6 H7 H8 H9 Hst Hpv Hty].
  eapply VTrProj_intro; try eassumption.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
  - eapply VEnvOrdered_preserve_VHasType; eassumption.
Qed.

Lemma VTrProj_weakN env venv U n k G G' owner idx sv pv fty :
  VEnvClosed venv ->
  VCtxLiftN n k G G' ->
  VTrProj env venv U G owner idx sv pv fty ->
  VTrProj env venv U G' owner idx (vliftN n k sv) (vliftN n k pv) (vliftN n k fty).
Proof.
  intros Hcl W [info ctor c d us params indices H1 H2 H3 H4 H5 H6 H7 H8 H9 Hst Hpv Hty].
  subst pv.
  eapply VTrProj_intro with
    (info := info) (ctor := ctor) (c := c) (d := d) (us := us)
    (params := map (vliftN n k) params) (indices := map (vliftN n k) indices);
    try eassumption; try (rewrite List.length_map; assumption).
  - pose proof (VIsDefEq_weakN Hcl Hst W) as Hw.
    rewrite vliftN_vapps, map_app in Hw. exact Hw.
  - unfold vproj_expr. simpl. rewrite vliftN_vapps. reflexivity.
  - eapply VIsDefEq_weakN; eassumption.
Qed.

Lemma vinst_vapps f args e0 k :
  vinst (vapps f args) e0 k = vapps (vinst f e0 k) (map (fun x => vinst x e0 k) args).
Proof.
  revert f. induction args as [|a r IH]; intros f; simpl; auto.
Qed.

Lemma VTrProj_instN env venv U G0 e0 A0 k G1 G owner idx sv pv fty :
  VEnvClosed venv ->
  VHasType venv U G0 e0 A0 ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VTrProj env venv U G1 owner idx sv pv fty ->
  VTrProj env venv U G owner idx
    (vinst sv e0 k) (vinst pv e0 k) (vinst fty e0 k).
Proof.
  intros Hcl He0 Hci [info ctor c d us params indices H1 H2 H3 H4 H5 H6 H7 H8 H9 Hst Hpv Hty].
  subst pv.
  eapply VTrProj_intro with
    (info := info) (ctor := ctor) (c := c) (d := d) (us := us)
    (params := map (fun x => vinst x e0 k) params)
    (indices := map (fun x => vinst x e0 k) indices);
    try eassumption; try (rewrite List.length_map; assumption).
  - pose proof (VIsDefEq_instN Hcl He0 Hst Hci) as Hi.
    rewrite vinst_vapps, map_app in Hi. exact Hi.
  - unfold vproj_expr. simpl. rewrite vinst_vapps. reflexivity.
  - eapply VIsDefEq_instN; eassumption.
Qed.

Lemma VTrProj_instL env venv U U' ls G owner idx sv pv fty :
  Forall (vlevel_wf U') ls ->
  VTrProj env venv U G owner idx sv pv fty ->
  VTrProj env venv U' (map (vinstL ls) G) owner idx
    (vinstL ls sv) (vinstL ls pv) (vinstL ls fty).
Proof.
  intros Hls [info ctor c d us params indices H1 H2 H3 H4 H5 H6 H7 H8 H9 Hst Hpv Hty].
  subst pv.
  eapply VTrProj_intro with
    (info := info) (ctor := ctor) (c := c) (d := d)
    (us := map (vlevel_inst ls) us)
    (params := map (vinstL ls) params)
    (indices := map (vinstL ls) indices);
    try eassumption; try (rewrite List.length_map; assumption).
  - apply Forall_vlevel_inst_wf; assumption.
  - pose proof (VIsDefEq_instL Hls Hst) as Hi.
    rewrite vinstL_vapps, map_app in Hi. exact Hi.
  - unfold vproj_expr. simpl. rewrite vinstL_vapps. reflexivity.
  - eapply VIsDefEq_instL; eassumption.
Qed.

Lemma VTrProj_defeq_ctx env venv U G0 G1 G2 owner idx sv pv fty :
  VEnvClosed venv ->
  VIsDefEqCtx venv U G0 G1 G2 ->
  VTrProj env venv U G1 owner idx sv pv fty ->
  VTrProj env venv U G2 owner idx sv pv fty.
Proof.
  intros Hcl Hctx [info ctor c d us params indices H1 H2 H3 H4 H5 H6 H7 H8 H9 Hst Hpv Hty].
  eapply VTrProj_intro; try eassumption.
  - eapply VIsDefEq_defeqDFC; eassumption.
  - eapply VIsDefEq_defeqDFC; eassumption.
Qed.

(* ========================================================================= *)
(* 4. Primitives Semantic Specification (HasPrimitives)                      *)
(* ========================================================================= *)

Definition vnat_ty : VExpr := VConst core_nat_name [].
Definition vbool_ty : VExpr := VConst core_bool_name [].
Definition vchar_ty : VExpr := VConst core_char_name [].
Definition vstring_ty : VExpr := VConst core_string_name [].
Definition vlist_char_ty : VExpr := VApp (VConst core_list_name [VLZero]) vchar_ty.
Definition vboolLit (b : bool) : VExpr :=
  VConst (if b then core_true_name else core_false_name) [].

Definition vbinary_prim_spec (op : primitive_kind) (a b : N) : option (VExpr * VExpr) :=
  match op with
  | PNatAdd => Some (natLit (N.add a b), vnat_ty)
  | PNatSub => Some (natLit (N.sub a b), vnat_ty)
  | PNatMul => Some (natLit (N.mul a b), vnat_ty)
  | PNatPow => Some (natLit (N.pow a b), vnat_ty)
  | PNatGcd => Some (natLit (N.gcd a b), vnat_ty)
  | PNatMod => Some (natLit (N.modulo a b), vnat_ty)
  | PNatDiv => Some (natLit (N.div a b), vnat_ty)
  | PNatBEq => Some (vboolLit (N.eqb a b), vbool_ty)
  | PNatBLE => Some (vboolLit (N.leb a b), vbool_ty)
  | PNatLAnd => Some (natLit (N.land a b), vnat_ty)
  | PNatLOr => Some (natLit (N.lor a b), vnat_ty)
  | PNatXor => Some (natLit (N.lxor a b), vnat_ty)
  | PNatShiftLeft => Some (natLit (N.shiftl a b), vnat_ty)
  | PNatShiftRight => Some (natLit (N.shiftr a b), vnat_ty)
  | _ => None
  end.

Record HasPrimitives (env : environment) (venv : VEnv) : Prop := {
  hp_nat : core_nat_ready env = true ->
    VHasType venv 0 [] vnat_ty (VSort (VLSucc VLZero)) /\
    VHasType venv 0 [] (VConst core_zero_name []) vnat_ty /\
    VHasType venv 0 [] (VConst core_succ_name []) (VForallE vnat_ty vnat_ty);
  hp_bool : core_bool_ready env = true ->
    VHasType venv 0 [] vbool_ty (VSort (VLSucc VLZero)) /\
    VHasType venv 0 [] (VConst core_false_name []) vbool_ty /\
    VHasType venv 0 [] (VConst core_true_name []) vbool_ty;
  hp_string : core_string_ready env = true ->
    VHasType venv 0 [] vchar_ty (VSort (VLSucc VLZero)) /\
    VHasType venv 0 [] vstring_ty (VSort (VLSucc VLZero)) /\
    VHasType venv 0 [] (VConst core_char_of_nat []) (VForallE vnat_ty vchar_ty) /\
    VHasType venv 0 [] (VConst core_string_of_list []) (VForallE vlist_char_ty vstring_ty) /\
    VHasType venv 0 [] (VApp (VConst (NameStr core_list_name "nil") [VLZero]) vchar_ty) vlist_char_ty /\
    VHasType venv 0 [] (VApp (VConst (NameStr core_list_name "cons") [VLZero]) vchar_ty)
      (VForallE vchar_ty (VForallE vlist_char_ty vlist_char_ty));
  hp_pred : forall n d,
    core_nat_ready env = true ->
    find_decl n env = Some d ->
    decl_kind_of d = DPrimitive PNatPred ->
    forall a : N,
      VIsDefEq venv 0 [] (VApp (VConst n []) (natLit a)) (natLit (N.pred a)) vnat_ty;
  hp_binary : forall n d op,
    core_nat_ready env = true ->
    find_decl n env = Some d ->
    decl_kind_of d = DPrimitive op ->
    forall a b res rty,
      vbinary_prim_spec op a b = Some (res, rty) ->
      (rty = vbool_ty -> core_bool_ready env = true) ->
      VIsDefEq venv 0 [] (vapps (VConst n []) [natLit a; natLit b]) res rty
}.

Lemma HasPrimitives_empty : HasPrimitives [] venv_empty.
Proof. constructor; simpl; intros; discriminate. Qed.

Lemma HasPrimitives_mono_venv env venv1 venv2 :
  venv_ordered venv1 venv2 ->
  HasPrimitives env venv1 ->
  HasPrimitives env venv2.
Proof.
  intros Hord H. constructor.
  - intros Hr. destruct (hp_nat H Hr) as [H1 [H2 H3]].
    repeat split; eapply VEnvOrdered_preserve_VHasType; eassumption.
  - intros Hr. destruct (hp_bool H Hr) as [H1 [H2 H3]].
    repeat split; eapply VEnvOrdered_preserve_VHasType; eassumption.
  - intros Hr. destruct (hp_string H Hr) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    repeat split; eapply VEnvOrdered_preserve_VHasType; eassumption.
  - intros n d Hr Hf Hk a.
    eapply VEnvOrdered_preserve_VIsDefEq; [exact Hord | eapply hp_pred; eassumption].
  - intros n d op Hr Hf Hk a b res rty Hs Hb.
    eapply VEnvOrdered_preserve_VIsDefEq; [exact Hord | eapply hp_binary; eassumption].
Qed.

Lemma natLit_has_type env venv U G n :
  VEnvClosed venv ->
  HasPrimitives env venv ->
  core_nat_ready env = true ->
  VHasType venv U G (natLit n) vnat_ty.
Proof.
  intros Hcl Hp Hr.
  destruct (hp_nat Hp Hr) as [_ [Hz Hs]].
  assert (Hz' : VHasType venv U G (VConst core_zero_name []) vnat_ty).
  { pose proof (VIsDefEq_instL (U':=U) (ls:=[]) (Forall_nil _) Hz) as Hi.
    simpl in Hi. exact (VIsDefEq_weak0 G Hcl Hi). }
  assert (Hs' : VHasType venv U G (VConst core_succ_name []) (VForallE vnat_ty vnat_ty)).
  { pose proof (VIsDefEq_instL (U':=U) (ls:=[]) (Forall_nil _) Hs) as Hi.
    simpl in Hi. exact (VIsDefEq_weak0 G Hcl Hi). }
  induction n using N.peano_ind.
  - rewrite natLit_0. exact Hz'.
  - rewrite natLit_succ.
    change vnat_ty with (vinst0 vnat_ty (natLit n)).
    eapply VDF_appDF; [exact Hs' | exact IHn].
Qed.

Lemma trCharList_has_type env venv U G cs :
  VEnvClosed venv ->
  HasPrimitives env venv ->
  core_string_ready env = true ->
  VHasType venv U G (trCharList cs) vlist_char_ty.
Proof.
  intros Hcl Hp Hr.
  assert (Hnat : core_nat_ready env = true).
  { unfold core_string_ready in Hr.
    destruct (find_decl core_char_of_nat env); try discriminate.
    destruct (find_decl core_string_of_list env); try discriminate.
    destruct (decl_kind_of d); try discriminate.
    destruct p; try discriminate.
    destruct (decl_kind_of d0); try discriminate.
    destruct p; try discriminate. exact Hr. }
  destruct (hp_string Hp Hr) as [_ [_ [Hcof [_ [Hnil Hcons]]]]].
  assert (Hlift0 : forall e A, vinstL [] e = e -> vinstL [] A = A ->
      VHasType venv 0 [] e A -> VHasType venv U G e A).
  { intros e A He HA Hty.
    pose proof (VIsDefEq_instL (U':=U) (ls:=[]) (Forall_nil _) Hty) as Hi.
    simpl in Hi. rewrite He, HA in Hi. exact (VIsDefEq_weak0 G Hcl Hi). }
  assert (Hcof' : VHasType venv U G (VConst core_char_of_nat []) (VForallE vnat_ty vchar_ty))
    by (apply Hlift0; auto).
  assert (Hnil' : VHasType venv U G (VApp (VConst (NameStr core_list_name "nil") [VLZero]) vchar_ty) vlist_char_ty)
    by (apply Hlift0; auto).
  assert (Hcons' : VHasType venv U G (VApp (VConst (NameStr core_list_name "cons") [VLZero]) vchar_ty)
      (VForallE vchar_ty (VForallE vlist_char_ty vlist_char_ty)))
    by (apply Hlift0; auto).
  induction cs as [|c rest IH]; simpl.
  - exact Hnil'.
  - change vlist_char_ty with (vinst0 vlist_char_ty (trCharList rest)).
    eapply VDF_appDF; [| exact IH].
    change (VForallE vlist_char_ty vlist_char_ty)
      with (vinst0 (VForallE vlist_char_ty vlist_char_ty) (VApp (VConst core_char_of_nat []) (natLit c))).
    eapply VDF_appDF; [exact Hcons' |].
    change vchar_ty with (vinst0 vchar_ty (natLit c)).
    eapply VDF_appDF; [exact Hcof' | eapply natLit_has_type; eassumption].
Qed.

Lemma trStrLit_has_type env venv U G s e :
  VEnvClosed venv ->
  HasPrimitives env venv ->
  core_string_ready env = true ->
  trStrLit s = Some e ->
  VHasType venv U G e vstring_ty.
Proof.
  intros Hcl Hp Hr Htr.
  unfold trStrLit in Htr. destruct (core_utf8 s) as [cs|] eqn:Hu; [|discriminate].
  inversion Htr; subst e; clear Htr.
  destruct (hp_string Hp Hr) as [_ [_ [_ [Hsof _]]]].
  assert (Hsof' : VHasType venv U G (VConst core_string_of_list []) (VForallE vlist_char_ty vstring_ty)).
  { pose proof (VIsDefEq_instL (U':=U) (ls:=[]) (Forall_nil _) Hsof) as Hi.
    simpl in Hi. exact (VIsDefEq_weak0 G Hcl Hi). }
  change vstring_ty with (vinst0 vstring_ty (trCharList cs)).
  eapply VDF_appDF; [exact Hsof' | eapply trCharList_has_type; eassumption].
Qed.

(* ========================================================================= *)
(* 5. Full 12-Constructor VTrExprS / VTrExpr / VTrTyping & VTrCtx            *)
(* ========================================================================= *)

Inductive VTrExprS (env : environment) (venv : VEnv) (ps : list name)
    : VLCtx -> expr -> VExpr -> Prop :=
| VTrExprS_bvar : forall L i e' ty',
    vl_bvar L i = Some (e', ty') ->
    VHasType venv (List.length ps) (vl_ctx L) e' ty' ->
    VTrExprS env venv ps L (EBVar i) e'
| VTrExprS_fvar : forall L n e' ty',
    vl_fvar L n = Some (e', ty') ->
    VHasType venv (List.length ps) (vl_ctx L) e' ty' ->
    VTrExprS env venv ps L (EFVar n) e'
| VTrExprS_sort : forall L u u',
    TrLevel ps u u' ->
    VTrExprS env venv ps L (ESort u) (VSort u')
| VTrExprS_const : forall L c ci us us',
    venv_constants venv c = Some ci ->
    TrLevels ps us us' ->
    List.length us = vc_uvars ci ->
    VTrExprS env venv ps L (EConst c us) (VConst c us')
| VTrExprS_app : forall L f a f' a' A B,
    VHasType venv (List.length ps) (vl_ctx L) f' (VForallE A B) ->
    VHasType venv (List.length ps) (vl_ctx L) a' A ->
    VTrExprS env venv ps L f f' ->
    VTrExprS env venv ps L a a' ->
    VTrExprS env venv ps L (EApp f a) (VApp f' a')
| VTrExprS_lam : forall L n bi ty body ty' body',
    VIsType venv (List.length ps) (vl_ctx L) ty' ->
    VTrExprS env venv ps L ty ty' ->
    VTrExprS env venv ps (vl_push_lam L ty') body body' ->
    VTrExprS env venv ps L (ELam n bi ty body) (VLam ty' body')
| VTrExprS_pi : forall L n bi ty body ty' body',
    VIsType venv (List.length ps) (vl_ctx L) ty' ->
    VIsType venv (List.length ps) (ty' :: vl_ctx L) body' ->
    VTrExprS env venv ps L ty ty' ->
    VTrExprS env venv ps (vl_push_lam L ty') body body' ->
    VTrExprS env venv ps L (EPi n bi ty body) (VForallE ty' body')
| VTrExprS_let : forall L n ty val body nd ty' val' body',
    VHasType venv (List.length ps) (vl_ctx L) val' ty' ->
    VTrExprS env venv ps L ty ty' ->
    VTrExprS env venv ps L val val' ->
    VTrExprS env venv ps (vl_push_let L ty' val') body body' ->
    VTrExprS env venv ps L (ELet n ty val body nd) body'
| VTrExprS_proj : forall L owner idx e e' proj' field_ty,
    VTrExprS env venv ps L e e' ->
    VTrProj env venv (List.length ps) (vl_ctx L) owner idx e' proj' field_ty ->
    VTrExprS env venv ps L (EProj owner idx e) proj'
| VTrExprS_natlit : forall L n,
    core_nat_ready env = true ->
    VHasType venv (List.length ps) (vl_ctx L) (natLit n) vnat_ty ->
    VTrExprS env venv ps L (ELit (LitNat n)) (natLit n)
| VTrExprS_strlit : forall L s s',
    core_string_ready env = true ->
    trStrLit s = Some s' ->
    VHasType venv (List.length ps) (vl_ctx L) s' vstring_ty ->
    VTrExprS env venv ps L (ELit (LitString s)) s'
| VTrExprS_mdata : forall L e e',
    VTrExprS env venv ps L e e' ->
    VTrExprS env venv ps L (EMData e) e'.

Definition VTrExpr (env : environment) (venv : VEnv) (ps : list name)
    (L : VLCtx) (e : expr) (e' : VExpr) : Prop :=
  exists e0, VTrExprS env venv ps L e e0 /\ VIsDefEqU venv (List.length ps) (vl_ctx L) e0 e'.

Definition VTrTyping (env : environment) (venv : VEnv) (ps : list name)
    (L : VLCtx) (e ty : expr) (e' ty' : VExpr) : Prop :=
  VTrExpr env venv ps L e e' /\
  VTrExpr env venv ps L ty ty' /\
  VHasType venv (List.length ps) (vl_ctx L) e' ty'.

Lemma VTrExprS_has_type env venv ps L e e' :
  VTrExprS env venv ps L e e' ->
  exists A, VHasType venv (List.length ps) (vl_ctx L) e' A.
Proof.
  induction 1.
  - exists ty'. exact H0.
  - exists ty'. exact H0.
  - exists (VSort (VLSucc u')). apply VHasType_sort.
    eapply vlevel_of_level_wf; exact H.
  - exists (vinstL us' (vc_type ci)).
    eapply VHasType_const; [exact H | eapply TrLevels_wf; exact H0 |].
    rewrite <- (TrLevels_length H0). exact H1.
  - exists (vinst0 B a'). eapply VDF_appDF; eassumption.
  - destruct H as [u Hu]. destruct IHVTrExprS2 as [B HB].
    exists (VForallE ty' B). eapply VDF_lamDF; eassumption.
  - destruct H as [u Hu]. destruct H0 as [v Hv].
    exists (VSort (VLIMax u v)). eapply VDF_forallEDF; eassumption.
  - exact IHVTrExprS3.
  - exists field_ty. eapply VTrProj_has_type; exact H0.
  - exists vnat_ty. exact H0.
  - exists vstring_ty. exact H1.
  - exact IHVTrExprS.
Qed.

Lemma VTrExprS_to_VTrExpr env venv ps L e e' :
  VTrExprS env venv ps L e e' ->
  VTrExpr env venv ps L e e'.
Proof.
  intros H. destruct (VTrExprS_has_type H) as [A HA].
  exists e'. split; [exact H | exists A; exact HA].
Qed.

Lemma VTrExpr_has_type env venv ps L e e' :
  VTrExpr env venv ps L e e' ->
  exists A, VHasType venv (List.length ps) (vl_ctx L) e' A.
Proof.
  intros [e0 [_ [A H]]]. exists A. eapply VIsDefEq_refl_r; exact H.
Qed.

Lemma VTrExpr_defeq_r env venv ps L e e1 e2 :
  VEnvWF venv ->
  DefEqInjectivity venv ->
  VCtxWF venv (List.length ps) (vl_ctx L) ->
  VTrExpr env venv ps L e e1 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) e1 e2 ->
  VTrExpr env venv ps L e e2.
Proof.
  intros Hwf Hinj HG [e0 [Htr H01]] H12.
  exists e0. split; [exact Htr |].
  eapply VIsDefEqU_trans; eassumption.
Qed.

Lemma VTrExprS_monotonic_env env venv1 venv2 ps L e e' :
  venv_ordered venv1 venv2 ->
  VTrExprS env venv1 ps L e e' ->
  VTrExprS env venv2 ps L e e'.
Proof.
  intros Hord H. induction H.
  - eapply VTrExprS_bvar; [exact H | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - eapply VTrExprS_fvar; [exact H | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - eapply VTrExprS_sort; exact H.
  - eapply VTrExprS_const; [apply (venv_ord_const Hord); eassumption | exact H0 | exact H1].
  - eapply VTrExprS_app;
      [eapply VEnvOrdered_preserve_VHasType; eassumption |
       eapply VEnvOrdered_preserve_VHasType; eassumption | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_lam;
      [eapply VEnvOrdered_preserve_VIsType; eassumption | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_pi;
      [eapply VEnvOrdered_preserve_VIsType; eassumption |
       eapply VEnvOrdered_preserve_VIsType; eassumption | exact IHVTrExprS1 | exact IHVTrExprS2].
  - eapply VTrExprS_let;
      [eapply VEnvOrdered_preserve_VHasType; eassumption | exact IHVTrExprS1 |
       exact IHVTrExprS2 | exact IHVTrExprS3].
  - eapply VTrExprS_proj; [exact IHVTrExprS | eapply VTrProj_monotonic_env; eassumption].
  - eapply VTrExprS_natlit; [exact H | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - eapply VTrExprS_strlit; [exact H | exact H0 | eapply VEnvOrdered_preserve_VHasType; eassumption].
  - apply VTrExprS_mdata; exact IHVTrExprS.
Qed.

Lemma VTrExpr_monotonic_env env venv1 venv2 ps L e e' :
  venv_ordered venv1 venv2 ->
  VTrExpr env venv1 ps L e e' ->
  VTrExpr env venv2 ps L e e'.
Proof.
  intros Hord [e0 [Htr Hdef]].
  exists e0. split; [eapply VTrExprS_monotonic_env | eapply VEnvOrdered_preserve_VIsDefEqU];
    eassumption.
Qed.

Inductive VTrFreeCtx (env : environment) (venv : VEnv) (ps : list name)
    : list (name * binding) -> list (name * VLCtxEntry) -> Prop :=
| VTrFreeCtx_nil : VTrFreeCtx env venv ps [] []
| VTrFreeCtx_lam : forall n ty fs ty' fs',
    VTrFreeCtx env venv ps fs fs' ->
    ~ In n (map fst fs') ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := [] |} ty ty' ->
    VIsType venv (List.length ps) (vl_free_ctx fs') ty' ->
    VTrFreeCtx env venv ps ((n, {| binding_type := ty; binding_value := None |}) :: fs)
                           ((n, VLLam ty') :: fs')
| VTrFreeCtx_let : forall n ty val fs ty' val' fs',
    VTrFreeCtx env venv ps fs fs' ->
    ~ In n (map fst fs') ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := [] |} ty ty' ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := [] |} val val' ->
    VHasType venv (List.length ps) (vl_free_ctx fs') val' ty' ->
    VTrFreeCtx env venv ps ((n, {| binding_type := ty; binding_value := Some val |}) :: fs)
                           ((n, VLLet ty' val') :: fs').

Inductive VTrBoundCtx (env : environment) (venv : VEnv) (ps : list name)
    (fs' : list (name * VLCtxEntry))
    : list binding -> list VLCtxEntry -> Prop :=
| VTrBoundCtx_nil : VTrBoundCtx env venv ps fs' [] []
| VTrBoundCtx_lam : forall ty bs ty' bs',
    VTrBoundCtx env venv ps fs' bs bs' ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := bs' |} ty ty' ->
    VIsType venv (List.length ps) (vlentries_to_ctx bs' ++ vl_free_ctx fs') ty' ->
    VTrBoundCtx env venv ps fs'
      ({| binding_type := ty; binding_value := None |} :: bs)
      (VLLam ty' :: bs')
| VTrBoundCtx_let : forall ty val bs ty' val' bs',
    VTrBoundCtx env venv ps fs' bs bs' ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := bs' |} ty ty' ->
    VTrExpr env venv ps {| vl_free := fs'; vl_bound := bs' |} val val' ->
    VHasType venv (List.length ps) (vlentries_to_ctx bs' ++ vl_free_ctx fs') val' ty' ->
    VTrBoundCtx env venv ps fs'
      ({| binding_type := ty; binding_value := Some val |} :: bs)
      (VLLet ty' val' :: bs').

Definition VTrCtx (env : environment) (venv : VEnv) (ps : list name)
    (g : context) (L : VLCtx) : Prop :=
  VTrFreeCtx env venv ps (free_context g) (vl_free L) /\
  VTrBoundCtx env venv ps (vl_free L) (bound_context g) (vl_bound L).

Lemma VTrFreeCtx_to_VLCtxEntriesWF env venv ps fs fs' :
  VTrFreeCtx env venv ps fs fs' ->
  VLCtxEntriesWF venv (List.length ps) [] (map snd fs').
Proof.
  induction 1; simpl; constructor; try assumption.
  - rewrite app_nil_r. exact H2.
  - rewrite app_nil_r. exact H3.
Qed.

Lemma VTrBoundCtx_to_VLCtxEntriesWF env venv ps fs' bs bs' :
  VTrBoundCtx env venv ps fs' bs bs' ->
  VLCtxEntriesWF venv (List.length ps) (vl_free_ctx fs') bs'.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma VTrCtx_to_VLCtxWF env venv ps g L :
  VTrCtx env venv ps g L -> VLCtxWF venv (List.length ps) L.
Proof.
  intros [Hf Hb]. split.
  - eapply VTrFreeCtx_to_VLCtxEntriesWF; exact Hf.
  - eapply VTrBoundCtx_to_VLCtxEntriesWF; exact Hb.
Qed.

Lemma VTrCtx_to_VCtxWF env venv ps g L :
  VTrCtx env venv ps g L -> VCtxWF venv (List.length ps) (vl_ctx L).
Proof. intros H. apply VLCtxWF_to_VCtxWF. eapply VTrCtx_to_VLCtxWF; exact H. Qed.

Lemma VTrCtx_empty env venv ps :
  VTrCtx env venv ps empty_context vl_empty.
Proof. split; constructor. Qed.

Lemma VTrCtx_push_lam env venv ps g L ty ty' :
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L ty ty' ->
  VIsType venv (List.length ps) (vl_ctx L) ty' ->
  VTrCtx env venv ps (push_binding g ty None) (vl_push_lam L ty').
Proof.
  intros [Hf Hb] Hty His. split; [exact Hf |].
  simpl. destruct L as [fs' bs']. simpl in *.
  constructor; assumption.
Qed.

Lemma VTrCtx_push_let env venv ps g L ty val ty' val' :
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L ty ty' ->
  VTrExpr env venv ps L val val' ->
  VHasType venv (List.length ps) (vl_ctx L) val' ty' ->
  VTrCtx env venv ps (push_binding g ty (Some val)) (vl_push_let L ty' val').
Proof.
  intros [Hf Hb] Hty Hval Hhas. split; [exact Hf |].
  simpl. destruct L as [fs' bs']. simpl in *.
  constructor; assumption.
Qed.

Lemma VTrCtx_push_free_lam env venv ps g L n ty ty' :
  bound_context g = [] ->
  vl_bound L = [] ->
  ~ In n (map fst (vl_free L)) ->
  VTrCtx env venv ps g L ->
  VTrExpr env venv ps L ty ty' ->
  VIsType venv (List.length ps) (vl_ctx L) ty' ->
  VTrCtx env venv ps
    {| bound_context := [];
       free_context := (n, {| binding_type := ty; binding_value := None |}) :: free_context g |}
    (vl_push_free_lam L n ty').
Proof.
  intros Hbg Hbl Hfresh [Hf Hb] Hty His.
  destruct L as [fs' bs']. simpl in *. subst bs'.
  split; [| constructor].
  simpl in *. constructor; assumption.
Qed.

(* ========================================================================= *)
(* 6. VEnvSound: Complete Environment Soundness Invariant                    *)
(* ========================================================================= *)

Definition VIndHeadInj (env : environment) (venv : VEnv) : Prop :=
  forall U G ind1 ind2 i1 i2 us1 us2 args1 args2,
    VCtxWF venv U G ->
    core_inductive env ind1 = Some i1 ->
    core_inductive env ind2 = Some i2 ->
    VIsDefEqU venv U G
      (vapps (VConst ind1 us1) args1)
      (vapps (VConst ind2 us2) args2) ->
    ind1 = ind2 /\
    Forall2 vlevel_equiv us1 us2 /\
    Forall2 (VIsDefEqU venv U G) args1 args2.

Record VEnvSound (env : environment) (venv : VEnv) : Prop := {
  ves_wf : VEnvWF venv;
  ves_inj : DefEqInjectivity venv;
  ves_ind_inj : VIndHeadInj env venv;
  ves_prims : HasPrimitives env venv;
  ves_constants : forall n d,
    find_decl n env = Some d ->
    match decl_kind_of d with
    | DUnsupported | DUnsafe _ | DPartial => True
    | _ =>
        exists ci,
          venv_constants venv n = Some ci /\
          vc_uvars ci = List.length (decl_params d) /\
          VTrExpr env venv (decl_params d) vl_empty (decl_type d) (vc_type ci) /\
          VIsType venv (vc_uvars ci) [] (vc_type ci) /\
          vclosed (vc_type ci)
    end;
  ves_delta : forall n d val,
    find_decl n env = Some d ->
    match decl_kind_of d with
    | DDefinition | DTheorem | DPrimitive _ => True
    | _ => False
    end ->
    decl_value d = Some val ->
    exists ci val',
      venv_constants venv n = Some ci /\
      vc_uvars ci = List.length (decl_params d) /\
      VTrExpr env venv (decl_params d) vl_empty val val' /\
      vclosed val' /\
      venv_defeqs venv
        {| vdf_uvars := vc_uvars ci;
           vdf_lhs := VConst n (vlevel_params (vc_uvars ci));
           vdf_rhs := val';
           vdf_type := vc_type ci |};
  ves_quot_red : forall U G n d cn cd us cus args rep index fn a1 a2,
    VCtxWF venv U G ->
    find_decl n env = Some d ->
    (decl_kind_of d = DQuotient QLift /\ index = 5 \/
     decl_kind_of d = DQuotient QInd /\ index = 4) ->
    find_decl cn env = Some cd ->
    decl_kind_of cd = DQuotient QCtor ->
    nth_error args index = Some (vapps (VConst cn cus) [a1; a2; rep]) ->
    nth_error args 3 = Some fn ->
    VExprWF venv U G (vapps (VConst n us) args) ->
    VIsDefEqU venv U G
      (vapps (VConst n us) args)
      (vapps (VApp fn rep) (skipn (S index) args));
  ves_recursor_iota : forall U G rname d info rus args major_idx owner cn ci cus fields rule rhs_v,
    VCtxWF venv U G ->
    find_decl rname env = Some d ->
    decl_kind_of d = DRecursor info ->
    major_idx = rec_num_params info + rec_num_motives info + rec_num_minors info + rec_num_indices info ->
    core_major_induct major_idx (decl_type d) = Some owner ->
    nth_error args major_idx = Some (vapps (VConst cn cus) fields) ->
    core_find_rule cn (rec_rules info) = Some rule ->
    core_constructor env cn = Some ci ->
    ctor_induct ci = owner ->
    List.length fields = ctor_num_params ci + ctor_num_fields ci ->
    rule_nfields rule = ctor_num_fields ci ->
    List.length rus = List.length (decl_params d) ->
    Forall (vlevel_wf U) rus ->
    VTrExpr env venv (decl_params d) vl_empty (rule_rhs rule) rhs_v ->
    VExprWF venv U G (vapps (VConst rname rus) args) ->
    VIsDefEqU venv U G
      (vapps (VConst rname rus) args)
      (vapps (vinstL rus rhs_v)
        (firstn (rec_num_params info + rec_num_motives info + rec_num_minors info) args ++
         skipn (ctor_num_params ci) fields ++
         skipn (S major_idx) args));
  ves_recursor_rhs : forall rname d info rule,
    find_decl rname env = Some d ->
    decl_kind_of d = DRecursor info ->
    In rule (rec_rules info) ->
    exists rhs_v, VTrExpr env venv (decl_params d) vl_empty (rule_rhs rule) rhs_v;
  ves_recursor_k_fields : forall rname d info owner oinfo ctor ci,
    find_decl rname env = Some d ->
    decl_kind_of d = DRecursor info ->
    rec_k info = true ->
    core_major_induct
      (rec_num_params info + rec_num_motives info + rec_num_minors info + rec_num_indices info)
      (decl_type d) = Some owner ->
    core_inductive env owner = Some oinfo ->
    ind_ctors oinfo = [ctor] ->
    core_constructor env ctor = Some ci ->
    ctor_num_fields ci = 0;
  ves_proj_const : forall owner info ctor c d idx,
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    idx < ctor_num_fields c ->
    exists pci,
      venv_constants venv (proj_const_name owner idx) = Some pci /\
      vc_uvars pci = List.length (decl_params d);
  ves_proj_iota : forall U G owner info ctor c d idx us cus params indices fields fval sv,
    VCtxWF venv U G ->
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    idx < ctor_num_fields c ->
    List.length params = ind_num_params info ->
    List.length indices = ind_num_indices info ->
    List.length fields = ctor_num_params c + ctor_num_fields c ->
    ctor_num_params c = ind_num_params info ->
    nth_error fields (ctor_num_params c + idx) = Some fval ->
    VHasType venv U G sv (vapps (VConst owner us) (params ++ indices)) ->
    VIsDefEqU venv U G sv (vapps (VConst ctor cus) fields) ->
    VExprWF venv U G (vproj_expr owner idx us params sv) ->
    VIsDefEqU venv U G (vproj_expr owner idx us params sv) fval;
  ves_proj_telescope : forall U G owner info ctor c d ci_c idx us params indices sv u_sort ty_p fty maybe_prop,
    VCtxWF venv U G ->
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    venv_constants venv ctor = Some ci_c ->
    idx < ctor_num_fields c ->
    List.length params = ind_num_params info ->
    List.length indices = ind_num_indices info ->
    Forall (vlevel_wf U) us ->
    List.length us = List.length (decl_params d) ->
    VHasType venv U G sv (vapps (VConst owner us) (params ++ indices)) ->
    VHasType venv U G (vapps (VConst owner us) (params ++ indices)) (VSort u_sort) ->
    (maybe_prop = false -> ~ vlevel_equiv u_sort VLZero) ->
    VHasType venv U G (vapps (VConst ctor us) params) ty_p ->
    VProjTelescope env venv U G owner us params sv maybe_prop idx 0 ty_p fty ->
    VHasType venv U G (vproj_expr owner idx us params sv) fty;
  ves_struct_eta : forall U G owner info ctor c d us params sv,
    VCtxWF venv U G ->
    core_structure env owner = true ->
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    List.length params = ind_num_params info ->
    ctor_num_params c = ind_num_params info ->
    Forall (vlevel_wf U) us ->
    List.length us = List.length (decl_params d) ->
    VHasType venv U G sv (vapps (VConst owner us) params) ->
    (forall i, i < ctor_num_fields c ->
       exists fty, VTrProj env venv U G owner i sv (vproj_expr owner i us params sv) fty) /\
    VIsDefEq venv U G sv
      (vapps (VConst ctor us)
        (params ++ map (fun i => vproj_expr owner i us params sv) (seq 0 (ctor_num_fields c))))
      (vapps (VConst owner us) params);
  ves_ctor_type_head : forall U G cn ci cus args T,
    VCtxWF venv U G ->
    core_constructor env cn = Some ci ->
    List.length args = ctor_num_params ci + ctor_num_fields ci ->
    VHasType venv U G (vapps (VConst cn cus) args) T ->
    exists oinfo indices,
      core_inductive env (ctor_induct ci) = Some oinfo /\
      ctor_num_params ci = ind_num_params oinfo /\
      List.length indices = ind_num_indices oinfo /\
      VIsDefEqU venv U G T
        (vapps (VConst (ctor_induct ci) cus) (firstn (ctor_num_params ci) args ++ indices));
  ves_ind_shape : forall owner info d_ind ctor c d_ctor,
    find_decl owner env = Some d_ind ->
    decl_kind_of d_ind = DInductive info ->
    find_decl ctor env = Some d_ctor ->
    decl_kind_of d_ctor = DConstructor c ->
    (In ctor (ind_ctors info) <-> ctor_induct c = owner) /\
    (In ctor (ind_ctors info) ->
      ctor_num_params c = ind_num_params info /\
      List.length (decl_params d_ctor) = List.length (decl_params d_ind));
  ves_ind_type_arity : forall U G owner info us args u_sort,
    VCtxWF venv U G ->
    core_inductive env owner = Some info ->
    VHasType venv U G (vapps (VConst owner us) args) (VSort u_sort) ->
    List.length args = ind_num_params info + ind_num_indices info;
  ves_ctor_params_wf : forall U G owner info ctor c d us params indices T,
    VCtxWF venv U G ->
    core_inductive env owner = Some info ->
    ind_ctors info = [ctor] ->
    find_decl ctor env = Some d ->
    decl_kind_of d = DConstructor c ->
    List.length params = ind_num_params info ->
    List.length indices = ind_num_indices info ->
    VHasType venv U G (vapps (VConst owner us) (params ++ indices)) T ->
    VExprWF venv U G (vapps (VConst ctor us) params);
  ves_ind_weakN : forall U n k G G' owner info T0 us args,
    VCtxWF venv U G' ->
    VCtxLiftN n k G G' ->
    core_inductive env owner = Some info ->
    VIsDefEqU venv U G' (vliftN n k T0) (vapps (VConst owner us) args) ->
    exists args0,
      List.length args0 = List.length args /\
      VIsDefEqU venv U G T0 (vapps (VConst owner us) args0)
}.

Theorem VEnvSound_empty :
  DefEqInjectivity venv_empty ->
  VEnvSound [] venv_empty.
Proof.
  intros Hinj.
  constructor.
  - constructor.
  - exact Hinj.
  - unfold VIndHeadInj. intros U G i1 i2 info1 info2 us1 us2 a1 a2 _ H1.
    unfold core_inductive in H1. simpl in H1. discriminate.
  - exact HasPrimitives_empty.
  - intros n d H. simpl in H. discriminate.
  - intros n d val H. simpl in H. discriminate.
  - intros U G n d cn cd us cus args rep idx fn a1 a2 _ H. simpl in H. discriminate.
  - intros U G r d info rus args midx own cn ci cus fs rule rhs _ H. simpl in H. discriminate.
  - intros r d info rule H. simpl in H. discriminate.
  - intros r d info own oinfo ctor ci H. simpl in H. discriminate.
  - intros own info ctor c d idx H. unfold core_inductive in H. simpl in H. discriminate.
  - intros U G own info ctor c d idx us cus ps idxs fs fv sv _ H.
    unfold core_inductive in H. simpl in H. discriminate.
  - intros U G own info ctor c d ci_c idx us ps idxs sv usrt typ fty mp _ H.
    unfold core_inductive in H. simpl in H. discriminate.
  - intros U G own info ctor c d us ps sv _ _ H.
    unfold core_inductive in H. simpl in H. discriminate.
  - intros U G cn ci cus args T _ H.
    unfold core_constructor in H. simpl in H. discriminate.
  - intros own info d_ind ctor c d_ctor H. simpl in H. discriminate.
  - intros U G own info us args usrt _ H. unfold core_inductive in H. simpl in H. discriminate.
  - intros U G own info ctor c d us ps idxs T _ H. unfold core_inductive in H. simpl in H. discriminate.
  - intros U n k G G' own info T0 us args _ _ H. unfold core_inductive in H. simpl in H. discriminate.
Qed.

(* ========================================================================= *)
(* 7. Spine Helpers & Projection Congruence                                  *)
(* ========================================================================= *)

Lemma vapps_defeq_congr env U G :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  forall xs ys f1 f2,
    VExprWF env U G (vapps f1 xs) ->
    VExprWF env U G (vapps f2 ys) ->
    VIsDefEqU env U G f1 f2 ->
    Forall2 (VIsDefEqU env U G) xs ys ->
    VIsDefEqU env U G (vapps f1 xs) (vapps f2 ys).
Proof.
  intros Hwf Hinj HG xs.
  induction xs as [|x xs IH]; intros ys f1 f2 Hwf1 Hwf2 Hf Hargs;
    inversion Hargs as [| ? y ? l' Hxy Hrest]; subst; simpl in *.
  - exact Hf.
  - assert (Hwf_app1 : VExprWF env U G (VApp f1 x)).
    { clear IH Hwf2 Hf Hargs Hxy Hrest. revert Hwf1.
      generalize (VApp f1 x) as h. induction xs as [|z zs IHz]; intros h Hh; [exact Hh |].
      destruct (IHz (VApp h z) Hh) as [T HT].
      destruct (VHasType_app_inv Hwf HG HT) as [A [B [Hh' _]]].
      exists (VForallE A B). exact Hh'. }
    assert (Hwf_app2 : VExprWF env U G (VApp f2 y)).
    { clear IH Hwf1 Hf Hargs Hxy Hrest. revert Hwf2.
      generalize (VApp f2 y) as h. induction l' as [|z zs IHz]; intros h Hh; [exact Hh |].
      destruct (IHz (VApp h z) Hh) as [T HT].
      destruct (VHasType_app_inv Hwf HG HT) as [A [B [Hh' _]]].
      exists (VForallE A B). exact Hh'. }
    apply IH; try assumption.
    destruct Hwf_app1 as [T1 HT1].
    destruct (VHasType_app_inv Hwf HG HT1) as [A1 [B1 [Hf1 Hx1]]].
    destruct Hf as [Tf Hf12].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hf1 (VIsDefEq_refl_l Hf12)) as [uf Hconvf].
    destruct Hxy as [Tx Hxy].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hx1 (VIsDefEq_refl_l Hxy)) as [ux Hconvx].
    exists (vinst0 B1 x).
    eapply VDF_appDF.
    + eapply VDF_defeqDF; [exact (VDF_symm Hconvf) | exact Hf12].
    + eapply VDF_defeqDF; [exact (VDF_symm Hconvx) | exact Hxy].
Qed.

Lemma VTrProj_congr env venv U G owner1 owner2 idx sv1 sv2 pv1 pv2 fty1 fty2 :
  VEnvSound env venv ->
  VCtxWF venv U G ->
  VTrProj env venv U G owner1 idx sv1 pv1 fty1 ->
  VTrProj env venv U G owner2 idx sv2 pv2 fty2 ->
  VIsDefEqU venv U G sv1 sv2 ->
  VIsDefEqU venv U G pv1 pv2.
Proof.
  intros Hves HG Hp1 Hp2 Hsv.
  destruct Hp1 as [info1 ctor1 c1 d1 us1 ps1 idxs1 Hi1 Hc1 Hd1 Hk1 Hlt1 Hlp1 Hli1 Hw1 Hlu1 Hst1 Hpv1 Hty1].
  destruct Hp2 as [info2 ctor2 c2 d2 us2 ps2 idxs2 Hi2 Hc2 Hd2 Hk2 Hlt2 Hlp2 Hli2 Hw2 Hlu2 Hst2 Hpv2 Hty2].
  subst pv1 pv2.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  destruct Hsv as [Tsv Hsv_eq].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG Hst1 Hsv_eq) as [ut1 Hct1].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG (VIsDefEq_refl_r Hsv_eq) Hst2) as [ut2 Hct2].
  assert (Hty_eq : VIsDefEqU venv U G
    (vapps (VConst owner1 us1) (ps1 ++ idxs1))
    (vapps (VConst owner2 us2) (ps2 ++ idxs2))).
  { eapply VIsDefEqU_trans;
      [exact Hwf | exact Hinj | exact HG | exists (VSort ut1); exact Hct1 | exists (VSort ut2); exact Hct2]. }
  destruct (ves_ind_inj Hves HG Hi1 Hi2 Hty_eq) as [Heq_own [Hus Hargs]].
  subst owner2.
  rewrite Hi1 in Hi2. inversion Hi2; subst info2; clear Hi2.
  assert (Hps_eq : Forall2 (VIsDefEqU venv U G) ps1 ps2).
  { assert (Hlen : List.length ps1 = List.length ps2) by lia.
    clear -Hargs Hlen.
    revert ps2 Hlen Hargs.
    induction ps1 as [|p1 r1 IH]; intros [|p2 r2] Hlen Hargs; simpl in *; try lia;
      [constructor |].
    inversion Hargs as [| ? ? ? ? Hp Hr]; subst.
    constructor; [exact Hp | apply IH; [lia | exact Hr]]. }
  destruct (ves_proj_const Hves Hi1 Hc1 Hd1 Hk1 Hlt1) as [pci [Hpci Huv]].
  unfold vproj_expr in *.
  assert (Hhead : VIsDefEqU venv U G
    (VConst (proj_const_name owner1 idx) us1)
    (VConst (proj_const_name owner1 idx) us2)).
  { exists (vinstL us1 (vc_type pci)).
    eapply VDF_constDF; [exact Hpci | exact Hw1 | exact Hw2 | lia | exact Hus]. }
  assert (Hwf1 : VExprWF venv U G (vapps (VConst (proj_const_name owner1 idx) us1) (ps1 ++ [sv1]))).
  { rewrite vapps_app. simpl. exists fty1. exact Hty1. }
  assert (Hwf2 : VExprWF venv U G (vapps (VConst (proj_const_name owner1 idx) us2) (ps2 ++ [sv2]))).
  { rewrite vapps_app. simpl. exists fty2. exact Hty2. }
  assert (Hall : Forall2 (VIsDefEqU venv U G) (ps1 ++ [sv1]) (ps2 ++ [sv2])).
  { apply Forall2_app; [exact Hps_eq | constructor; [exists Tsv; exact Hsv_eq | constructor]]. }
  pose proof (vapps_defeq_congr Hwf Hinj HG Hwf1 Hwf2 Hhead Hall) as Hres.
  rewrite !vapps_app in Hres. exact Hres.
Qed.

(* ========================================================================= *)
(* 8. Context Conversion & Uniqueness Across All 12 Constructors             *)
(* ========================================================================= *)

Lemma VTrExprS_defeq_ctx_uniq env venv ps :
  VEnvSound env venv ->
  forall L1 e e1,
    VTrExprS env venv ps L1 e e1 ->
    forall L2,
      VLCtxWF venv (List.length ps) L1 ->
      VLCtxWF venv (List.length ps) L2 ->
      VLCtxDefEq venv (List.length ps) L1 L2 ->
      exists e2,
        VTrExprS env venv ps L2 e e2 /\
        VIsDefEqU venv (List.length ps) (vl_ctx L1) e1 e2.
Proof.
  intros Hves.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  intros L1 e e1 Htr.
  induction Htr as
    [ L1 i e1 ty1 Hlk1 Hty1
    | L1 n e1 ty1 Hlk1 Hty1
    | L1 u u' Htr_u
    | L1 c ci us us' Hci Htr_us Hlen_us
    | L1 f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L1 nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L1 nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L1 nm ty val body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L1 owner idx a a' proj' field_ty Htr_a IHa Hproj
    | L1 n Hnat Hnty
    | L1 s s' Hstr Htrs Hsty
    | L1 a a' Htr_a IHa ];
    intros L2 Hwf1 Hwf2 Hceq;
    pose proof (VLCtxWF_to_VCtxWF Hwf1) as HG1;
    pose proof (VLCtxWF_to_VCtxWF Hwf2) as HG2;
    pose proof (VLCtxDefEq_to_VIsDefEqCtx Hceq) as Hctx.
  - destruct (vl_lookup_bound_defeq Hcl Hceq Hlk1) as [e2 [ty2 [Hlk2 Heq]]].
    exists e2. split.
    + eapply VTrExprS_bvar; [exact Hlk2 | eapply vl_lookup_bound_has_type; eassumption].
    + exists ty1. exact Heq.
  - destruct (vl_lookup_free_defeq Hcl Hceq Hlk1) as [e2 [ty2 [Hlk2 Heq]]].
    exists e2. split.
    + eapply VTrExprS_fvar; [exact Hlk2 | eapply vl_lookup_free_has_type; eassumption].
    + exists ty1. exact Heq.
  - exists (VSort u'). split; [constructor; exact Htr_u |].
    exists (VSort (VLSucc u')). apply VHasType_sort. eapply vlevel_of_level_wf; exact Htr_u.
  - exists (VConst c us'). split; [econstructor; eassumption |].
    exists (vinstL us' (vc_type ci)).
    eapply VHasType_const; [exact Hci | eapply TrLevels_wf; exact Htr_us |].
    rewrite <- (TrLevels_length Htr_us). exact Hlen_us.
  - destruct (IHf L2 Hwf1 Hwf2 Hceq) as [f2 [Hf2 [Tf Heqf]]].
    destruct (IHa L2 Hwf1 Hwf2 Hceq) as [a2 [Ha2 [Ta Heqa]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hf_ty (VIsDefEq_refl_l Heqf)) as [uf Hcf].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Ha_ty (VIsDefEq_refl_l Heqa)) as [ua Hca].
    assert (Heqf' : VIsDefEq venv (List.length ps) (vl_ctx L1) f' f2 (VForallE A B))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcf) | exact Heqf]).
    assert (Heqa' : VIsDefEq venv (List.length ps) (vl_ctx L1) a' a2 A)
      by (eapply VDF_defeqDF; [exact (VDF_symm Hca) | exact Heqa]).
    exists (VApp f2 a2). split.
    + eapply VTrExprS_app.
      * eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r Heqf')].
      * eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r Heqa')].
      * exact Hf2.
      * exact Ha2.
    + exists (vinst0 B a'). eapply VDF_appDF; [exact Heqf' | exact Heqa'].
  - destruct (IHA L2 Hwf1 Hwf2 Hceq) as [ty2 [Hty2 [TA HeqA]]].
    destruct Hty_is as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hu (VIsDefEq_refl_l HeqA)) as [uA HcA].
    assert (HeqA' : VIsDefEq venv (List.length ps) (vl_ctx L1) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HeqA]).
    assert (Hty2_is : VIsType venv (List.length ps) (vl_ctx L2) ty2).
    { exists u. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r HeqA')]. }
    assert (Hwf1' : VLCtxWF venv (List.length ps) (vl_push_lam L1 ty'))
      by (apply VLCtxWF_push_lam; [exact Hwf1 | exists u; exact Hu]).
    assert (Hwf2' : VLCtxWF venv (List.length ps) (vl_push_lam L2 ty2))
      by (apply VLCtxWF_push_lam; [exact Hwf2 | exact Hty2_is]).
    assert (Hceq' : VLCtxDefEq venv (List.length ps) (vl_push_lam L1 ty') (vl_push_lam L2 ty2)).
    { destruct Hceq as [Hn [Hf Hb]]. repeat split; simpl; auto.
      econstructor; [exact Hb | exact HeqA']. }
    destruct (IHb _ Hwf1' Hwf2' Hceq') as [body2 [Hbody2 [TB Heqb]]].
    exists (VLam ty2 body2). split.
    + eapply VTrExprS_lam; [exact Hty2_is | exact Hty2 | exact Hbody2].
    + exists (VForallE ty' TB). eapply VDF_lamDF; [exact HeqA' | exact Heqb].
  - destruct (IHA L2 Hwf1 Hwf2 Hceq) as [ty2 [Hty2 [TA HeqA]]].
    destruct Hty_is as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hu (VIsDefEq_refl_l HeqA)) as [uA HcA].
    assert (HeqA' : VIsDefEq venv (List.length ps) (vl_ctx L1) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HeqA]).
    assert (Hty2_is : VIsType venv (List.length ps) (vl_ctx L2) ty2).
    { exists u. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r HeqA')]. }
    assert (Hwf1' : VLCtxWF venv (List.length ps) (vl_push_lam L1 ty'))
      by (apply VLCtxWF_push_lam; [exact Hwf1 | exists u; exact Hu]).
    assert (Hwf2' : VLCtxWF venv (List.length ps) (vl_push_lam L2 ty2))
      by (apply VLCtxWF_push_lam; [exact Hwf2 | exact Hty2_is]).
    assert (Hceq' : VLCtxDefEq venv (List.length ps) (vl_push_lam L1 ty') (vl_push_lam L2 ty2)).
    { destruct Hceq as [Hn [Hf Hb]]. repeat split; simpl; auto.
      econstructor; [exact Hb | exact HeqA']. }
    destruct (IHB _ Hwf1' Hwf2' Hceq') as [body2 [Hbody2 [TB Heqb]]].
    destruct Hbody_is as [v Hv].
    assert (HG1' : VCtxWF venv (List.length ps) (ty' :: vl_ctx L1))
      by (split; [exact HG1 | exists u; exact Hu]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1' Hv (VIsDefEq_refl_l Heqb)) as [vB HcB].
    assert (Heqb' : VIsDefEq venv (List.length ps) (ty' :: vl_ctx L1) body' body2 (VSort v))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcB) | exact Heqb]).
    assert (Hctx' : VIsDefEqCtx venv (List.length ps) [] (ty' :: vl_ctx L1) (ty2 :: vl_ctx L2))
      by (econstructor; [exact Hctx | exact HeqA']).
    exists (VForallE ty2 body2). split.
    + eapply VTrExprS_pi; [exact Hty2_is | | exact Hty2 | exact Hbody2].
      exists v. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx' | exact (VIsDefEq_refl_r Heqb')].
    + exists (VSort (VLIMax u v)). eapply VDF_forallEDF; [exact HeqA' | exact Heqb'].
  - destruct (IHA L2 Hwf1 Hwf2 Hceq) as [ty2 [Hty2 [TA HeqA]]].
    destruct (IHv L2 Hwf1 Hwf2 Hceq) as [val2 [Hval2 [Tv Heqv]]].
    destruct (VIsDefEq_isType Hwf HG1 Hval_ty) as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hu (VIsDefEq_refl_l HeqA)) as [uA HcA].
    assert (HeqA' : VIsDefEq venv (List.length ps) (vl_ctx L1) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HeqA]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hval_ty (VIsDefEq_refl_l Heqv)) as [uv Hcv].
    assert (Heqv' : VIsDefEq venv (List.length ps) (vl_ctx L1) val' val2 ty')
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv) | exact Heqv]).
    assert (Hv2_ty2 : VHasType venv (List.length ps) (vl_ctx L2) val2 ty2).
    { eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx |].
      eapply VDF_defeqDF; [exact HeqA' | exact (VIsDefEq_refl_r Heqv')]. }
    assert (Hwf1' : VLCtxWF venv (List.length ps) (vl_push_let L1 ty' val'))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hwf2' : VLCtxWF venv (List.length ps) (vl_push_let L2 ty2 val2))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hceq' : VLCtxDefEq venv (List.length ps)
        (vl_push_let L1 ty' val') (vl_push_let L2 ty2 val2)).
    { destruct Hceq as [Hn [Hf Hb]]. repeat split; simpl; auto.
      econstructor; [exact Hb | exact HeqA' | exact Heqv']. }
    destruct (IHb _ Hwf1' Hwf2' Hceq') as [body2 [Hbody2 Heqb]].
    exists body2. split; [eapply VTrExprS_let; eassumption | exact Heqb].
  - destruct (IHa L2 Hwf1 Hwf2 Hceq) as [e2 [He2 [Te Heqe]]].
    destruct Hproj as [info ctor c d us ps_e idxs Hi Hc Hd Hk Hlt Hlp Hli Hw Hlu Hst Hpv Hty].
    subst proj'.
    destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hst (VIsDefEq_refl_l Heqe)) as [ue Hce].
    assert (Heqe' : VIsDefEq venv (List.length ps) (vl_ctx L1) a' e2
        (vapps (VConst owner us) (ps_e ++ idxs)))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hce) | exact Heqe]).
    assert (Hst2 : VHasType venv (List.length ps) (vl_ctx L2) e2
        (vapps (VConst owner us) (ps_e ++ idxs)))
      by (eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r Heqe')]).
    assert (Hpv_eq : VIsDefEqU venv (List.length ps) (vl_ctx L1)
        (vproj_expr owner idx us ps_e a')
        (vproj_expr owner idx us ps_e e2)).
    { unfold vproj_expr in *.
      destruct (VHasType_app_inv Hwf HG1 Hty) as [Ap [Bp [Hpf Hpe]]].
      destruct (VIsDefEq_uniq_same Hwf Hinj HG1 Hpe (VIsDefEq_refl_l Heqe')) as [up Hcp].
      exists (vinst0 Bp a').
      eapply VDF_appDF; [exact Hpf | eapply VDF_defeqDF; [exact (VDF_symm Hcp) | exact Heqe']]. }
    destruct Hpv_eq as [Tpv Hpv_eq'].
    exists (vproj_expr owner idx us ps_e e2). split.
    + eapply VTrExprS_proj; [exact He2 |].
      eapply VTrProj_intro; try eassumption; [reflexivity |].
      eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact (VIsDefEq_refl_r Hpv_eq')].
    + exists Tpv. exact Hpv_eq'.
  - exists (natLit n). split.
    + eapply VTrExprS_natlit; [exact Hnat | eapply VIsDefEq_defeqDFC; eassumption].
    + exists vnat_ty. exact Hnty.
  - exists s'. split.
    + eapply VTrExprS_strlit; [exact Hstr | exact Htrs | eapply VIsDefEq_defeqDFC; eassumption].
    + exists vstring_ty. exact Hsty.
  - destruct (IHa L2 Hwf1 Hwf2 Hceq) as [e2 [He2 Heq]].
    exists e2. split; [constructor; exact He2 | exact Heq].
Qed.

Theorem VTrExprS_uniq env venv ps L e e1 e2 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExprS env venv ps L e e1 ->
  VTrExprS env venv ps L e e2 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) e1 e2.
Proof.
  intros Hves HwfL H1.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  revert HwfL e2.
  induction H1 as
    [ L i e1 ty1 Hlk1 Hty1
    | L n e1 ty1 Hlk1 Hty1
    | L u u' Htr_u
    | L c ci us us' Hci Htr_us Hlen_us
    | L f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L nm ty val body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L owner idx a a' proj' field_ty Htr_a IHa Hproj
    | L n Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros HwfL e2 H2;
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  - inversion H2 as [? ? ? ty2 Hlk2 Hty2 | | | | | | | | | | |]; subst.
    rewrite Hlk1 in Hlk2. inversion Hlk2; subst e2 ty2. exists ty1. exact Hty1.
  - inversion H2 as [| ? ? ? ty2 Hlk2 Hty2 | | | | | | | | | |]; subst.
    rewrite Hlk1 in Hlk2. inversion Hlk2; subst e2 ty2. exists ty1. exact Hty1.
  - inversion H2 as [| | ? ? u2 Htr_u2 | | | | | | | | |]; subst.
    unfold TrLevel in *. rewrite Htr_u in Htr_u2. inversion Htr_u2; subst u2.
    exists (VSort (VLSucc u')). apply VHasType_sort. eapply vlevel_of_level_wf; exact Htr_u.
  - inversion H2 as [| | | ? ? ci2 ? us2 Hci2 Htr_us2 Hlen_us2 | | | | | | | |]; subst.
    assert (Hus : us' = us2).
    { clear -Htr_us Htr_us2. revert us2 Htr_us2.
      induction Htr_us as [| l l' ls ls' Hl Hls IH]; intros us2 H;
        inversion H as [| ? l2 ? ls2 Hl2 Hls2]; subst; auto.
      unfold TrLevel in *. rewrite Hl in Hl2. inversion Hl2; subst. f_equal. auto. }
    subst us2.
    exists (vinstL us' (vc_type ci)).
    eapply VHasType_const; [exact Hci | eapply TrLevels_wf; exact Htr_us |].
    rewrite <- (TrLevels_length Htr_us). exact Hlen_us.
  - inversion H2 as [| | | | ? ? ? f2 a2 A2 B2 Hf2_ty Ha2_ty Htr_f2 Htr_a2 | | | | | | |]; subst.
    pose proof (IHf HwfL f2 Htr_f2) as [Tf Hfeq].
    pose proof (IHa HwfL a2 Htr_a2) as [Ta Haeq].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hf_ty (VIsDefEq_refl_l Hfeq)) as [uf Hcf].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Ha_ty (VIsDefEq_refl_l Haeq)) as [ua Hca].
    exists (vinst0 B a').
    eapply VDF_appDF.
    + eapply VDF_defeqDF; [exact (VDF_symm Hcf) | exact Hfeq].
    + eapply VDF_defeqDF; [exact (VDF_symm Hca) | exact Haeq].
  - inversion H2 as [| | | | | ? ? ? ? ? ty2 body2 Hty2_is Htr_ty2 Htr_body2 | | | | | |]; subst.
    pose proof (IHA HwfL ty2 Htr_ty2) as [TA HAeq].
    destruct Hty_is as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_l HAeq)) as [uA HcA].
    assert (HAeq' : VIsDefEq venv (List.length ps) (vl_ctx L) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq]).
    assert (HwfL1 : VLCtxWF venv (List.length ps) (vl_push_lam L ty'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact Hu]).
    assert (HwfL2 : VLCtxWF venv (List.length ps) (vl_push_lam L ty2))
      by (apply VLCtxWF_push_lam; [exact HwfL | exact Hty2_is]).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L ty') (vl_push_lam L ty2)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact HAeq']. }
    destruct (VTrExprS_defeq_ctx_uniq Hves Htr_body HwfL1 HwfL2 Hceq) as [body_t [Hbt Heqb1]].
    pose proof (VTrExprS_defeq_ctx_uniq Hves Htr_body2 HwfL2 HwfL1 (VLCtxDefEq_symm Hcl Hceq))
      as [body2_1 [Hbt2_1 Heqb2_1']].
    pose proof (IHb HwfL1 body2_1 Hbt2_1) as Heqb12.
    assert (Hctx : VIsDefEqCtx venv (List.length ps) [] (ty' :: vl_ctx L) (ty2 :: vl_ctx L))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    destruct Heqb2_1' as [TB2 Heqb2_1''].
    assert (Heqb2_rev : VIsDefEqU venv (List.length ps) (ty' :: vl_ctx L) body2_1 body2).
    { exists TB2. apply VDF_symm.
      eapply VIsDefEq_defeqDFC; [exact Hcl | apply VIsDefEqCtx_symm; [exact Hcl | exact Hctx] | exact Heqb2_1'']. }
    assert (HG' : VCtxWF venv (List.length ps) (ty' :: vl_ctx L))
      by (split; [exact HG | exists u; exact Hu]).
    destruct (VIsDefEqU_trans Hwf Hinj HG' Heqb12 Heqb2_rev) as [TB Heqb].
    exists (VForallE ty' TB). eapply VDF_lamDF; [exact HAeq' | exact Heqb].
  - inversion H2 as [| | | | | | ? ? ? ? ? ty2 body2 Hty2_is Hbody2_is Htr_ty2 Htr_body2 | | | | |]; subst.
    pose proof (IHA HwfL ty2 Htr_ty2) as [TA HAeq].
    destruct Hty_is as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_l HAeq)) as [uA HcA].
    assert (HAeq' : VIsDefEq venv (List.length ps) (vl_ctx L) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq]).
    assert (HwfL1 : VLCtxWF venv (List.length ps) (vl_push_lam L ty'))
      by (apply VLCtxWF_push_lam; [exact HwfL | exists u; exact Hu]).
    assert (HwfL2 : VLCtxWF venv (List.length ps) (vl_push_lam L ty2))
      by (apply VLCtxWF_push_lam; [exact HwfL | exact Hty2_is]).
    assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_lam L ty') (vl_push_lam L ty2)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact HAeq']. }
    pose proof (VTrExprS_defeq_ctx_uniq Hves Htr_body2 HwfL2 HwfL1 (VLCtxDefEq_symm Hcl Hceq))
      as [body2_1 [Hbt2_1 Heqb2_1']].
    pose proof (IHB HwfL1 body2_1 Hbt2_1) as Heqb12.
    assert (Hctx : VIsDefEqCtx venv (List.length ps) [] (ty' :: vl_ctx L) (ty2 :: vl_ctx L))
      by (exact (VLCtxDefEq_to_VIsDefEqCtx Hceq)).
    destruct Heqb2_1' as [TB2 Heqb2_1''].
    assert (Heqb2_rev : VIsDefEqU venv (List.length ps) (ty' :: vl_ctx L) body2_1 body2).
    { exists TB2. apply VDF_symm.
      eapply VIsDefEq_defeqDFC; [exact Hcl | apply VIsDefEqCtx_symm; [exact Hcl | exact Hctx] | exact Heqb2_1'']. }
    assert (HG' : VCtxWF venv (List.length ps) (ty' :: vl_ctx L))
      by (split; [exact HG | exists u; exact Hu]).
    destruct (VIsDefEqU_trans Hwf Hinj HG' Heqb12 Heqb2_rev) as [TB Heqb].
    destruct Hbody_is as [v Hv].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG' Hv (VIsDefEq_refl_l Heqb)) as [vB HcB].
    exists (VSort (VLIMax u v)).
    eapply VDF_forallEDF; [exact HAeq' | eapply VDF_defeqDF; [exact (VDF_symm HcB) | exact Heqb]].
  - inversion H2 as [| | | | | | | ? ? ? ? ? ? ty2 val2 body2 Hval2_ty Htr_ty2 Htr_val2 Htr_body2 | | | |]; subst.
    pose proof (IHA HwfL ty2 Htr_ty2) as [TA HAeq].
    pose proof (IHv HwfL val2 Htr_val2) as [Tv Hveq].
    destruct (VIsDefEq_isType Hwf HG Hval_ty) as [u Hu].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hu (VIsDefEq_refl_l HAeq)) as [uA HcA].
    assert (HAeq' : VIsDefEq venv (List.length ps) (vl_ctx L) ty' ty2 (VSort u))
      by (eapply VDF_defeqDF; [exact (VDF_symm HcA) | exact HAeq]).
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hval_ty (VIsDefEq_refl_l Hveq)) as [uv Hcv].
    assert (Hveq' : VIsDefEq venv (List.length ps) (vl_ctx L) val' val2 ty')
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcv) | exact Hveq]).
    assert (HwfL1 : VLCtxWF venv (List.length ps) (vl_push_let L ty' val'))
      by (apply VLCtxWF_push_let; assumption).
    assert (HwfL2 : VLCtxWF venv (List.length ps) (vl_push_let L ty2 val2))
      by (apply VLCtxWF_push_let; assumption).
    assert (Hceq : VLCtxDefEq venv (List.length ps)
        (vl_push_let L ty' val') (vl_push_let L ty2 val2)).
    { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
      repeat split; simpl; auto. econstructor; [exact Hb | exact HAeq' | exact Hveq']. }
    pose proof (VTrExprS_defeq_ctx_uniq Hves Htr_body2 HwfL2 HwfL1 (VLCtxDefEq_symm Hcl Hceq))
      as [b2_1 [Hb2_1 [TB2 Heqb2_1]]].
    pose proof (IHb HwfL1 b2_1 Hb2_1) as Heqb12.
    eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact Heqb12 |].
    exists TB2. apply VDF_symm. exact Heqb2_1.
  - inversion H2 as [| | | | | | | | ? ? ? ? a2 proj2 fty2 Htr_a2 Hproj2 | | |]; subst.
    pose proof (IHa HwfL a2 Htr_a2) as Heq.
    eapply VTrProj_congr; eassumption.
  - inversion H2; subst. exists vnat_ty. exact Hnty.
  - inversion H2 as [| | | | | | | | | | ? ? s2 Hstr2 Htrs2 Hsty2 |]; subst.
    rewrite Htrs in Htrs2. inversion Htrs2; subst e2. exists vstring_ty. exact Hsty.
  - inversion H2 as [| | | | | | | | | | | ? ? a2 Htr_a2]; subst.
    exact (IHa HwfL e2 Htr_a2).
Qed.

Theorem VTrExpr_uniq env venv ps L e e1 e2 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VTrExpr env venv ps L e e1 ->
  VTrExpr env venv ps L e e2 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) e1 e2.
Proof.
  intros Hves HwfL [e01 [H1 Hd1]] [e02 [H2 Hd2]].
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  pose proof (VTrExprS_uniq Hves HwfL H1 H2) as H012.
  destruct Hd1 as [A1 Hd1'].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exists A1; exact (VDF_symm Hd1') |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exact H012 | exact Hd2].
Qed.

Theorem VTrExpr_defeq_ctx env venv ps L1 L2 e e1 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L1 ->
  VLCtxWF venv (List.length ps) L2 ->
  VLCtxDefEq venv (List.length ps) L1 L2 ->
  VTrExpr env venv ps L1 e e1 ->
  VTrExpr env venv ps L2 e e1.
Proof.
  intros Hves Hwf1 Hwf2 Hceq [e0 [Htr [A Heq]]].
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF Hwf2) as HG2.
  pose proof (VLCtxDefEq_to_VIsDefEqCtx Hceq) as Hctx.
  destruct (VTrExprS_defeq_ctx_uniq Hves Htr Hwf1 Hwf2 Hceq) as [e2 [Htr2 [B Heq02]]].
  exists e2. split; [exact Htr2 |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG2 | |].
  - exists B. apply VDF_symm. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact Heq02].
  - exists A. eapply VIsDefEq_defeqDFC; [exact Hcl | exact Hctx | exact Heq].
Qed.

(* ========================================================================= *)
(* 9. Hybrid Lifting, Single & Simultaneous Substitution, Universe Inst      *)
(* ========================================================================= *)

(* Inserting a block `ins` of hybrid bound entries at bound depth `idx`
   (corresponding to lambda depth `k` in `vl_ctx`) lifts all entries above it. *)
Inductive VLBoundLift (ins : list VLCtxEntry) : nat -> nat -> list VLCtxEntry -> list VLCtxEntry -> Prop :=
| VLBoundLift_base : forall suf,
    VLBoundLift ins 0 0 suf (ins ++ suf)
| VLBoundLift_lam : forall idx k A bs bs',
    VLBoundLift ins idx k bs bs' ->
    VLBoundLift ins (S idx) (S k)
      (VLLam A :: bs)
      (VLLam (vliftN (List.length (vlentries_to_ctx ins)) k A) :: bs')
| VLBoundLift_let : forall idx k A v bs bs',
    VLBoundLift ins idx k bs bs' ->
    VLBoundLift ins (S idx) k
      (VLLet A v :: bs)
      (VLLet (vliftN (List.length (vlentries_to_ctx ins)) k A)
             (vliftN (List.length (vlentries_to_ctx ins)) k v) :: bs').

Lemma VLBoundLift_to_VCtxLiftN ins idx k bs bs' base :
  VLBoundLift ins idx k bs bs' ->
  VCtxLiftN (List.length (vlentries_to_ctx ins)) k
    (vlentries_to_ctx bs ++ base)
    (vlentries_to_ctx bs' ++ base).
Proof.
  induction 1; simpl.
  - rewrite vlentries_to_ctx_app, <- app_assoc. apply VCtxLiftN_app_prefix.
  - constructor. exact IHVLBoundLift.
  - exact IHVLBoundLift.
Qed.

Lemma VLBoundLift_lams ins idx k bs bs' :
  VLBoundLift ins idx k bs bs' ->
  List.length (vlentries_to_ctx bs') =
    List.length (vlentries_to_ctx ins) + List.length (vlentries_to_ctx bs) /\
  k <= List.length (vlentries_to_ctx bs).
Proof.
  induction 1; simpl.
  - rewrite vlentries_to_ctx_app, List.length_app. lia.
  - lia.
  - lia.
Qed.

Lemma VLBoundLift_lookup ins idx k bs bs' :
  VLBoundLift ins idx k bs bs' ->
  forall i d e ty,
    vl_lookup_bound bs i d = Some (e, ty) ->
    vl_lookup_bound bs' (if idx <=? i then List.length ins + i else i) d =
      Some (vliftN (List.length (vlentries_to_ctx ins)) (k + d) e,
            vliftN (List.length (vlentries_to_ctx ins)) (k + d) ty).
Proof.
  induction 1 as [suf | idx k A bs bs' H IH | idx k A v bs bs' H IH];
    intros i d e ty Hlk.
  - simpl.
    rewrite vl_lookup_bound_app_r.
    apply vl_lookup_bound_shift_at; [lia | exact Hlk].
  - destruct i as [|i]; simpl in *.
    + inversion Hlk; subst e ty; clear Hlk.
      f_equal. f_equal.
      * simpl. unfold vliftVar. destruct (Nat.ltb_spec d (S (k + d))); [reflexivity | lia].
      * replace (S (k + d)) with (S d + k) by lia.
        rewrite vliftN_comm by lia. reflexivity.
    + specialize (IH i (S d) e ty Hlk).
      replace (S (k + d)) with (k + S d) by lia.
      destruct (idx <=? i); simpl in *; [replace (List.length ins + S i) with (S (List.length ins + i)) by lia |];
        exact IH.
  - destruct i as [|i]; simpl in *.
    + inversion Hlk; subst e ty; clear Hlk.
      f_equal. f_equal; replace (k + d) with (d + k) by lia; rewrite vliftN_comm by lia; reflexivity.
    + specialize (IH i d e ty Hlk).
      destruct (idx <=? i); simpl in *; [replace (List.length ins + S i) with (S (List.length ins + i)) by lia |];
        exact IH.
Qed.

Lemma VTrExprS_lift_L env venv ps :
  VEnvClosed venv ->
  forall L e e',
    VTrExprS env venv ps L e e' ->
    forall ins idx k bs',
      VLBoundLift ins idx k (vl_bound L) bs' ->
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := bs' |}
        (lift (List.length ins) idx e)
        (vliftN (List.length (vlentries_to_ctx ins)) k e').
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
    | L n Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros ins idx k bs' Hbl;
    pose proof (VLBoundLift_to_VCtxLiftN (vl_free_ctx (vl_free L)) Hbl) as W;
    simpl in *.
  - pose proof (VLBoundLift_lookup Hbl (d:=0) Hlk) as Hlk'.
    rewrite Nat.add_0_r in Hlk'.
    eapply VTrExprS_bvar; [exact Hlk' | eapply VIsDefEq_weakN; [exact Hcl | exact Hty | exact W]].
  - destruct (VLBoundLift_lams Hbl) as [Hlams Hkle].
    unfold vl_fvar, vl_bound_lams in Hlk.
    pose proof (vl_lookup_free_shift_at (List.length (vlentries_to_ctx ins)) Hkle Hlk) as Hlk'.
    rewrite <- Hlams in Hlk'.
    eapply VTrExprS_fvar; [exact Hlk' | eapply VIsDefEq_weakN; [exact Hcl | exact Hty | exact W]].
  - constructor; exact Htr_u.
  - econstructor; eassumption.
  - eapply VTrExprS_app with
      (A := vliftN (List.length (vlentries_to_ctx ins)) k A)
      (B := vliftN (List.length (vlentries_to_ctx ins)) (S k) B).
    + exact (VIsDefEq_weakN Hcl Hf_ty W).
    + exact (VIsDefEq_weakN Hcl Ha_ty W).
    + exact (IHf ins idx k bs' Hbl).
    + exact (IHa ins idx k bs' Hbl).
  - eapply VTrExprS_lam.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_weakN Hcl Hu W).
    + exact (IHA ins idx k bs' Hbl).
    + exact (IHb ins (S idx) (S k) (VLLam (vliftN (List.length (vlentries_to_ctx ins)) k ty') :: bs')
               (VLBoundLift_lam ty' Hbl)).
  - eapply VTrExprS_pi.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_weakN Hcl Hu W).
    + destruct Hbody_is as [v Hv]. exists v.
      exact (VIsDefEq_weakN Hcl Hv (VCtxLiftN_succ _ W)).
    + exact (IHA ins idx k bs' Hbl).
    + exact (IHB ins (S idx) (S k) (VLLam (vliftN (List.length (vlentries_to_ctx ins)) k ty') :: bs')
               (VLBoundLift_lam ty' Hbl)).
  - eapply VTrExprS_let with
      (ty' := vliftN (List.length (vlentries_to_ctx ins)) k ty')
      (val' := vliftN (List.length (vlentries_to_ctx ins)) k val').
    + exact (VIsDefEq_weakN Hcl Hval_ty W).
    + exact (IHA ins idx k bs' Hbl).
    + exact (IHv ins idx k bs' Hbl).
    + exact (IHb ins (S idx) k
               (VLLet (vliftN (List.length (vlentries_to_ctx ins)) k ty')
                      (vliftN (List.length (vlentries_to_ctx ins)) k val') :: bs')
               (VLBoundLift_let ty' val' Hbl)).
  - eapply VTrExprS_proj; [exact (IHa ins idx k bs' Hbl) |].
    eapply VTrProj_weakN; [exact Hcl | exact W | exact Hproj].
  - rewrite vliftN_natLit.
    eapply VTrExprS_natlit; [exact Hnat |].
    pose proof (VIsDefEq_weakN Hcl Hnty W) as Hw.
    rewrite vliftN_natLit in Hw. exact Hw.
  - rewrite (vliftN_trStrLit _ _ Htrs).
    eapply VTrExprS_strlit; [exact Hstr | exact Htrs |].
    pose proof (VIsDefEq_weakN Hcl Hsty W) as Hw.
    rewrite (vliftN_trStrLit _ _ Htrs) in Hw. exact Hw.
  - constructor. exact (IHa ins idx k bs' Hbl).
Qed.

Lemma VTrExprS_lift env venv ps :
  VEnvClosed venv ->
  forall e fs ins idx k bs bs' e',
    VLBoundLift ins idx k bs bs' ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := bs |} e e' ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := bs' |}
      (lift (List.length ins) idx e)
      (vliftN (List.length (vlentries_to_ctx ins)) k e').
Proof.
  intros Hcl e fs ins idx k bs bs' e' Hbl Htr.
  exact (VTrExprS_lift_L Hcl Htr Hbl).
Qed.

Corollary VTrExpr_lift env venv ps fs ins idx k bs bs' e e' :
  VEnvClosed venv ->
  VLBoundLift ins idx k bs bs' ->
  VTrExpr env venv ps {| vl_free := fs; vl_bound := bs |} e e' ->
  VTrExpr env venv ps {| vl_free := fs; vl_bound := bs' |}
    (lift (List.length ins) idx e)
    (vliftN (List.length (vlentries_to_ctx ins)) k e').
Proof.
  intros Hcl Hbl [e0 [Htr [A Hdef]]].
  exists (vliftN (List.length (vlentries_to_ctx ins)) k e0). split.
  - eapply VTrExprS_lift; eassumption.
  - exists (vliftN (List.length (vlentries_to_ctx ins)) k A).
    eapply VIsDefEq_weakN; [exact Hcl | exact Hdef | exact (VLBoundLift_to_VCtxLiftN (vl_free_ctx fs) Hbl)].
Qed.

Corollary VTrExpr_lift_lam env venv ps L A e e' :
  VEnvClosed venv ->
  VTrExpr env venv ps L e e' ->
  VTrExpr env venv ps (vl_push_lam L A) (lift 1 0 e) (vlift e').
Proof.
  intros Hcl H. destruct L as [fs bs]. unfold vl_push_lam. simpl.
  change (lift 1 0 e) with (lift (List.length [VLLam A]) 0 e).
  change (vlift e') with (vliftN (List.length (vlentries_to_ctx [VLLam A])) 0 e').
  eapply VTrExpr_lift; [exact Hcl | exact (VLBoundLift_base [VLLam A] bs) | exact H].
Qed.

Corollary VTrExpr_lift_let env venv ps L A v e e' :
  VEnvClosed venv ->
  VTrExpr env venv ps L e e' ->
  VTrExpr env venv ps (vl_push_let L A v) (lift 1 0 e) e'.
Proof.
  intros Hcl H. destruct L as [fs bs].
  pose proof (@VTrExpr_lift env venv ps fs [VLLet A v] 0 0 bs ([VLLet A v] ++ bs) e e'
    Hcl (VLBoundLift_base _ _) H) as Hl.
  simpl in Hl. rewrite vliftN_zero in Hl. exact Hl.
Qed.

Corollary VTrExpr_lift_from_free env venv ps fs bs e e' :
  VEnvClosed venv ->
  VTrExpr env venv ps {| vl_free := fs; vl_bound := [] |} e e' ->
  VTrExpr env venv ps {| vl_free := fs; vl_bound := bs |}
    (lift (List.length bs) 0 e)
    (vliftN (List.length (vlentries_to_ctx bs)) 0 e').
Proof.
  intros Hcl H.
  pose proof (@VTrExpr_lift env venv ps fs bs 0 0 [] (bs ++ []) e e'
    Hcl (VLBoundLift_base _ _) H) as Hl.
  rewrite app_nil_r in Hl. exact Hl.
Qed.


(* Single-variable substitution eliminating a VLLam entry *)
Inductive VLBoundInstLam (A0 e0 : VExpr) (suf : list VLCtxEntry)
    : nat -> nat -> list VLCtxEntry -> list VLCtxEntry -> Prop :=
| VLBoundInstLam_base :
    VLBoundInstLam A0 e0 suf 0 0 (VLLam A0 :: suf) suf
| VLBoundInstLam_lam : forall idx k A bs bs',
    VLBoundInstLam A0 e0 suf idx k bs bs' ->
    VLBoundInstLam A0 e0 suf (S idx) (S k)
      (VLLam A :: bs)
      (VLLam (vinst A e0 k) :: bs')
| VLBoundInstLam_let : forall idx k A v bs bs',
    VLBoundInstLam A0 e0 suf idx k bs bs' ->
    VLBoundInstLam A0 e0 suf (S idx) k
      (VLLet A v :: bs)
      (VLLet (vinst A e0 k) (vinst v e0 k) :: bs').

Lemma VLBoundInstLam_to_VCtxInstN A0 e0 suf idx k bs bs' base :
  VLBoundInstLam A0 e0 suf idx k bs bs' ->
  VCtxInstN (vlentries_to_ctx suf ++ base) e0 A0 k
    (vlentries_to_ctx bs ++ base) (vlentries_to_ctx bs' ++ base) /\
  List.length (vlentries_to_ctx bs) = S (List.length (vlentries_to_ctx bs')) /\
  k <= List.length (vlentries_to_ctx bs').
Proof.
  induction 1; simpl.
  - split; [apply VCtxInstN_zero | split; lia].
  - destruct IHVLBoundInstLam as [Hci [Hl Hle]].
    split; [apply VCtxInstN_succ; exact Hci | split; lia].
  - destruct IHVLBoundInstLam as [Hci [Hl Hle]].
    split; [exact Hci | split; lia].
Qed.

Lemma VLBoundInstLam_to_lift A0 e0 suf idx k bs bs' :
  VLBoundInstLam A0 e0 suf idx k bs bs' ->
  exists pre,
    bs' = pre ++ suf /\
    List.length pre = idx /\
    List.length (vlentries_to_ctx pre) = k /\
    VLBoundLift pre 0 0 suf bs'.
Proof.
  induction 1; simpl.
  - exists []. repeat split; try reflexivity. apply (VLBoundLift_base [] suf).
  - destruct IHVLBoundInstLam as [pre [Heq [Hl1 [Hl2 _]]]].
    exists (VLLam (vinst A e0 k) :: pre).
    rewrite Heq at 1. repeat split; simpl; try lia; try reflexivity.
    rewrite Heq. apply (VLBoundLift_base (VLLam (vinst A e0 k) :: pre) suf).
  - destruct IHVLBoundInstLam as [pre [Heq [Hl1 [Hl2 _]]]].
    exists (VLLet (vinst A e0 k) (vinst v e0 k) :: pre).
    rewrite Heq at 1. repeat split; simpl; try lia; try reflexivity.
    rewrite Heq. apply (VLBoundLift_base (VLLet (vinst A e0 k) (vinst v e0 k) :: pre) suf).
Qed.

Lemma VLBoundInstLam_lookup A0 e0 suf idx k bs bs' :
  VLBoundInstLam A0 e0 suf idx k bs bs' ->
  forall i d e ty,
    vl_lookup_bound bs i d = Some (e, ty) ->
    (i = idx -> e = VBVar (k + d) /\ ty = vliftN (S (k + d)) 0 A0) /\
    (i <> idx ->
      vl_lookup_bound bs' (if idx <? i then pred i else i) d =
        Some (vinst e e0 (k + d), vinst ty e0 (k + d))).
Proof.
  induction 1 as [| idx k A bs bs' H IH | idx k A v bs bs' H IH];
    intros i d e ty Hlk.
  - split.
    + intros ->. simpl in Hlk. inversion Hlk; subst; auto.
    + intros Hne. destruct i as [|i]; [contradiction |].
      simpl in *.
      assert (Hdown : forall es j d0 k0 e1 t1,
        k0 <= d0 ->
        vl_lookup_bound es j (S d0) = Some (e1, t1) ->
        vl_lookup_bound es j d0 = Some (vinst e1 e0 k0, vinst t1 e0 k0)).
      { clear. induction es as [|[B|B w] r IHr]; intros [|j] d0 k0 e1 t1 Hkd H0; simpl in *; try discriminate.
        - inversion H0; subst. f_equal. f_equal.
          + simpl. unfold vinstVar.
            replace (S d0 <? k0) with false by (symmetry; apply Nat.ltb_ge; lia).
            replace (Nat.eqb (S d0) k0) with false by (symmetry; apply Nat.eqb_neq; lia).
            reflexivity.
          + rewrite vinst_vliftN_ge by lia. reflexivity.
        - apply (IHr j (S d0) k0 e1 t1); [lia | exact H0].
        - inversion H0; subst. f_equal. f_equal; rewrite vinst_vliftN_ge by lia; reflexivity.
        - exact (IHr j d0 k0 e1 t1 Hkd H0). }
      apply Hdown; [lia | exact Hlk].
  - destruct i as [|i]; simpl in *.
    + split; [lia |]. intros _.
      inversion Hlk; subst e ty; clear Hlk. f_equal. f_equal.
      * simpl. unfold vinstVar.
        replace (d <? S (k + d)) with true by (symmetry; apply Nat.ltb_lt; lia).
        reflexivity.
      * rewrite vinst_vliftN_le. f_equal. lia.
    + specialize (IH i (S d) e ty Hlk).
      replace (S (k + d)) with (k + S d) by lia.
      destruct IH as [Heq Hneq]. split.
      * intros H0. apply Heq. lia.
      * intros H0. assert (Hne' : i <> idx) by lia. specialize (Hneq Hne').
        destruct (Nat.ltb_spec idx i); simpl in *.
        -- replace (S idx <? S i) with true by (symmetry; apply Nat.ltb_lt; lia).
           destruct i as [|i']; [lia | exact Hneq].
        -- replace (S idx <? S i) with false by (symmetry; apply Nat.ltb_ge; lia).
           exact Hneq.
  - destruct i as [|i]; simpl in *.
    + split; [lia |]. intros _.
      inversion Hlk; subst e ty; clear Hlk. f_equal. f_equal;
        rewrite vinst_vliftN_le; f_equal; lia.
    + specialize (IH i d e ty Hlk).
      destruct IH as [Heq Hneq]. split.
      * intros H0. apply Heq. lia.
      * intros H0. assert (Hne' : i <> idx) by lia. specialize (Hneq Hne').
        destruct (Nat.ltb_spec idx i); simpl in *.
        -- replace (S idx <? S i) with true by (symmetry; apply Nat.ltb_lt; lia).
           destruct i as [|i']; [lia | exact Hneq].
        -- replace (S idx <? S i) with false by (symmetry; apply Nat.ltb_ge; lia).
           exact Hneq.
Qed.

Lemma vl_lookup_free_inst_down fs n e0 : forall d k e ty,
  k <= d ->
  vl_lookup_free fs n (S d) = Some (e, ty) ->
  vl_lookup_free fs n d = Some (vinst e e0 k, vinst ty e0 k).
Proof.
  induction fs as [|[m [B|B w]] r IH]; intros d k e ty Hkd H; simpl in *; try discriminate.
  - destruct (name_eqb n m).
    + inversion H; subst. f_equal. f_equal.
      * simpl. unfold vinstVar.
        replace (S d <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
        replace (Nat.eqb (S d) k) with false by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity.
      * rewrite vinst_vliftN_ge by lia. reflexivity.
    + apply IH; [lia | exact H].
  - destruct (name_eqb n m).
    + inversion H; subst. f_equal. f_equal; rewrite vinst_vliftN_ge by lia; reflexivity.
    + apply IH; assumption.
Qed.

Lemma VTrExprS_subst_lam_L env venv ps :
  VEnvClosed venv ->
  forall L e e',
    VTrExprS env venv ps L e e' ->
    forall A0 val e0 suf idx k bs',
      VLBoundInstLam A0 e0 suf idx k (vl_bound L) bs' ->
      VHasType venv (List.length ps) (vl_ctx {| vl_free := vl_free L; vl_bound := suf |}) e0 A0 ->
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := suf |} val e0 ->
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := bs' |}
        (subst idx val e) (vinst e' e0 k).
Proof.
  intros Hcl L e e' Htr.
  induction Htr as
    [ L i e1 ty1 Hlk Hty
    | L nm e1 ty1 Hlk Hty
    | L u u' Htr_u
    | L c ci us us' Hconst Htr_us Hlen_us
    | L f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L nm ty val0 body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L owner idx0 a a' proj' field_ty Htr_a IHa Hproj
    | L n Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros A0 val e0 suf idx k bs' Hbi He0 Hval;
    pose proof (VLBoundInstLam_to_VCtxInstN (vl_free_ctx (vl_free L)) Hbi) as [Hci [Hl_ctx Hle_k]];
    simpl in *.
  - (* EBVar *)
    destruct (VLBoundInstLam_lookup Hbi (d:=0) Hlk) as [Hsame Hdiff].
    rewrite Nat.add_0_r in Hsame, Hdiff.
    destruct (Nat.eqb_spec i idx) as [-> | Hne].
    + destruct (Hsame eq_refl) as [-> ->].
      simpl. unfold vinstVar. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      destruct (VLBoundInstLam_to_lift Hbi) as [pre [Hbs'_eq [Hl1 [Hl2 Hbl]]]].
      destruct idx as [|idx'].
      * destruct pre; simpl in Hl1; try lia.
        simpl in Hbs'_eq, Hl2. subst bs' k. rewrite vliftN_zero. exact Hval.
      * rewrite <- Hl1, <- Hl2.
        eapply VTrExprS_lift; [exact Hcl | exact Hbl | exact Hval].
    + specialize (Hdiff Hne).
      eapply VTrExprS_bvar; [exact Hdiff |].
      eapply VIsDefEq_instN; [exact Hcl | exact He0 | exact Hty | exact Hci].
  - (* EFVar *)
    unfold vl_fvar, vl_bound_lams in *. simpl in *.
    rewrite Hl_ctx in Hlk.
    pose proof (vl_lookup_free_inst_down e0 Hle_k Hlk) as Hlk'.
    eapply VTrExprS_fvar; [exact Hlk' |].
    eapply VIsDefEq_instN; [exact Hcl | exact He0 | exact Hty | exact Hci].
  - constructor; exact Htr_u.
  - econstructor; eassumption.
  - eapply VTrExprS_app with (A := vinst A e0 k) (B := vinst B e0 (S k)).
    + exact (VIsDefEq_instN Hcl He0 Hf_ty Hci).
    + exact (VIsDefEq_instN Hcl He0 Ha_ty Hci).
    + exact (IHf A0 val e0 suf idx k bs' Hbi He0 Hval).
    + exact (IHa A0 val e0 suf idx k bs' Hbi He0 Hval).
  - eapply VTrExprS_lam.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_instN Hcl He0 Hu Hci).
    + exact (IHA A0 val e0 suf idx k bs' Hbi He0 Hval).
    + exact (IHb A0 val e0 suf (S idx) (S k) (VLLam (vinst ty' e0 k) :: bs')
               (VLBoundInstLam_lam ty' Hbi) He0 Hval).
  - eapply VTrExprS_pi.
    + destruct Hty_is as [u Hu]. exists u. exact (VIsDefEq_instN Hcl He0 Hu Hci).
    + destruct Hbody_is as [v Hv]. exists v.
      exact (VIsDefEq_instN Hcl He0 Hv (VCtxInstN_succ _ Hci)).
    + exact (IHA A0 val e0 suf idx k bs' Hbi He0 Hval).
    + exact (IHB A0 val e0 suf (S idx) (S k) (VLLam (vinst ty' e0 k) :: bs')
               (VLBoundInstLam_lam ty' Hbi) He0 Hval).
  - eapply VTrExprS_let with (ty' := vinst ty' e0 k) (val' := vinst val' e0 k).
    + exact (VIsDefEq_instN Hcl He0 Hval_ty Hci).
    + exact (IHA A0 val e0 suf idx k bs' Hbi He0 Hval).
    + exact (IHv A0 val e0 suf idx k bs' Hbi He0 Hval).
    + exact (IHb A0 val e0 suf (S idx) k (VLLet (vinst ty' e0 k) (vinst val' e0 k) :: bs')
               (VLBoundInstLam_let ty' val' Hbi) He0 Hval).
  - eapply VTrExprS_proj; [exact (IHa A0 val e0 suf idx k bs' Hbi He0 Hval) |].
    exact (VTrProj_instN Hcl He0 Hci Hproj).
  - rewrite vinst_natLit.
    eapply VTrExprS_natlit; [exact Hnat |].
    pose proof (VIsDefEq_instN Hcl He0 Hnty Hci) as Hi. rewrite vinst_natLit in Hi. exact Hi.
  - rewrite (vinst_trStrLit e0 k Htrs).
    eapply VTrExprS_strlit; [exact Hstr | exact Htrs |].
    pose proof (VIsDefEq_instN Hcl He0 Hsty Hci) as Hi. rewrite (vinst_trStrLit e0 k Htrs) in Hi. exact Hi.
  - constructor. exact (IHa A0 val e0 suf idx k bs' Hbi He0 Hval).
Qed.

Lemma VTrExprS_subst_lam env venv ps :
  VEnvClosed venv ->
  forall e fs A0 val e0 suf idx k bs bs' e',
    VLBoundInstLam A0 e0 suf idx k bs bs' ->
    VHasType venv (List.length ps) (vl_ctx {| vl_free := fs; vl_bound := suf |}) e0 A0 ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := suf |} val e0 ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := bs |} e e' ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := bs' |}
      (subst idx val e) (vinst e' e0 k).
Proof.
  intros Hcl e fs A0 val e0 suf idx k bs bs' e' Hbi He0 Hval Htr.
  exact (VTrExprS_subst_lam_L Hcl Htr Hbi He0 Hval).
Qed.

Corollary VTrExpr_instantiate_lam env venv ps L A0 val e0 body body' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VHasType venv (List.length ps) (vl_ctx L) e0 A0 ->
  VTrExpr env venv ps L val e0 ->
  VTrExpr env venv ps (vl_push_lam L A0) body body' ->
  VTrExpr env venv ps L (instantiate body val) (vinst0 body' e0).
Proof.
  intros Hves HwfL He0 [v0 [Hv0 [Tv Hveq]]] [b0 [Hb0 [Tb Hbeq]]].
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG He0 (VIsDefEq_refl_r Hveq)) as [uv Hcv].
  assert (Hveq' : VIsDefEq venv (List.length ps) (vl_ctx L) v0 e0 A0)
    by (eapply VDF_defeqDF; [exact (VDF_symm Hcv) | exact Hveq]).
  assert (Hv0_A0 : VHasType venv (List.length ps) (vl_ctx L) v0 A0)
    by (exact (VIsDefEq_refl_l Hveq')).
  destruct L as [fs bs].
  pose proof (@VTrExprS_subst_lam env venv ps Hcl body fs A0 val v0 bs 0 0 (VLLam A0 :: bs) bs b0
    (VLBoundInstLam_base A0 v0 bs) Hv0_A0 Hv0 Hb0) as Hsub.
  exists (vinst b0 v0 0). split; [exact Hsub |].
  pose proof (VIsDefEq_instN Hcl Hv0_A0 Hbeq (VCtxInstN_zero _ _ _)) as Hi1.
  assert (Hlam_b' : VHasType venv (List.length ps) (vl_ctx {| vl_free := fs; vl_bound := bs |})
      (VLam A0 body') (VForallE A0 Tb)).
  { destruct (VIsDefEq_isType Hwf HG He0) as [uA HuA].
    eapply VDF_lamDF; [exact HuA | exact (VIsDefEq_refl_r Hbeq)]. }
  assert (Happ_eq : VIsDefEq venv (List.length ps) (vl_ctx {| vl_free := fs; vl_bound := bs |})
      (VApp (VLam A0 body') v0) (VApp (VLam A0 body') e0) (vinst0 Tb v0)).
  { eapply VDF_appDF; [exact Hlam_b' | exact Hveq']. }
  assert (Hb1 : VIsDefEq venv (List.length ps) (vl_ctx {| vl_free := fs; vl_bound := bs |})
      (VApp (VLam A0 body') v0) (vinst0 body' v0) (vinst0 Tb v0))
    by (eapply VDF_beta; [exact (VIsDefEq_refl_r Hbeq) | exact Hv0_A0]).
  assert (Hb2 : VIsDefEq venv (List.length ps) (vl_ctx {| vl_free := fs; vl_bound := bs |})
      (VApp (VLam A0 body') e0) (vinst0 body' e0) (vinst0 Tb e0))
    by (eapply VDF_beta; [exact (VIsDefEq_refl_r Hbeq) | exact He0]).
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG | exists (vinst Tb v0 0); exact Hi1 |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
    exists (vinst0 Tb v0); exact (VDF_symm Hb1) |].
  eapply VIsDefEqU_trans; [exact Hwf | exact Hinj | exact HG |
    exists (vinst0 Tb v0); exact Happ_eq | exists (vinst0 Tb e0); exact Hb2].
Qed.

(* Single-variable substitution eliminating a VLLet entry — vl_ctx and e' are UNCHANGED! *)
Lemma VTrExprS_subst_let_L env venv ps :
  VEnvClosed venv ->
  forall L e e',
    VTrExprS env venv ps L e e' ->
    forall A0 val e0 pre suf,
      vl_bound L = pre ++ VLLet A0 e0 :: suf ->
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := suf |} val e0 ->
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := pre ++ suf |}
        (subst (List.length pre) val e) e'.
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
    | L nm ty val0 body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L owner idx0 a a' proj' field_ty Htr_a IHa Hproj
    | L n Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros A0 val e0 pre suf Hbnd Hval;
    assert (Hctx_eq : vl_ctx L = vl_ctx {| vl_free := vl_free L; vl_bound := pre ++ suf |})
      by (unfold vl_ctx; simpl; rewrite Hbnd, !vlentries_to_ctx_app; reflexivity);
    simpl in *.
  - (* EBVar *)
    destruct (Nat.eqb_spec i (List.length pre)) as [-> | Hne].
    + unfold vl_bvar in Hlk. rewrite Hbnd in Hlk.
      replace (List.length pre) with (List.length pre + 0) in Hlk by lia.
      rewrite vl_lookup_bound_app_r in Hlk. simpl in Hlk.
      rewrite Nat.add_0_r in Hlk. inversion Hlk; subst e1 ty1; clear Hlk.
      destruct pre as [|p0 pre'].
      * simpl. rewrite vliftN_zero. exact Hval.
      * change (S (List.length pre')) with (List.length (p0 :: pre')).
        eapply VTrExprS_lift; [exact Hcl | apply (VLBoundLift_base (p0 :: pre') suf) | exact Hval].
    + assert (Hlk' : vl_bvar {| vl_free := vl_free L; vl_bound := pre ++ suf |}
                       (if List.length pre <? i then pred i else i) = Some (e1, ty1)).
      { unfold vl_bvar in *. simpl in *. rewrite Hbnd in Hlk.
        destruct (Nat.ltb_spec (List.length pre) i) as [Hgt | Hle].
        - replace i with (List.length pre + S (pred i - List.length pre)) in Hlk by lia.
          rewrite vl_lookup_bound_app_r in Hlk. simpl in Hlk.
          replace (pred i) with (List.length pre + (pred i - List.length pre)) by lia.
          rewrite vl_lookup_bound_app_r. exact Hlk.
        - rewrite vl_lookup_bound_app_l in Hlk by lia.
          rewrite vl_lookup_bound_app_l by lia. exact Hlk. }
      eapply VTrExprS_bvar; [exact Hlk' | rewrite <- Hctx_eq; exact Hty].
  - unfold vl_fvar, vl_bound_lams in Hlk.
    rewrite Hbnd, !vlentries_to_ctx_app in Hlk. simpl in Hlk.
    rewrite <- vlentries_to_ctx_app in Hlk.
    eapply VTrExprS_fvar; [exact Hlk | rewrite <- Hctx_eq; exact Hty].
  - constructor; exact Htr_u.
  - econstructor; eassumption.
  - eapply VTrExprS_app; [rewrite <- Hctx_eq; exact Hf_ty | rewrite <- Hctx_eq; exact Ha_ty |
      exact (IHf A0 val e0 pre suf Hbnd Hval) | exact (IHa A0 val e0 pre suf Hbnd Hval)].
  - eapply VTrExprS_lam; [rewrite <- Hctx_eq; exact Hty_is | exact (IHA A0 val e0 pre suf Hbnd Hval) |].
    eapply (IHb A0 val e0 (VLLam ty' :: pre) suf); [simpl; rewrite Hbnd; reflexivity | exact Hval].
  - eapply VTrExprS_pi; [rewrite <- Hctx_eq; exact Hty_is | rewrite <- Hctx_eq; exact Hbody_is |
      exact (IHA A0 val e0 pre suf Hbnd Hval) |].
    eapply (IHB A0 val e0 (VLLam ty' :: pre) suf); [simpl; rewrite Hbnd; reflexivity | exact Hval].
  - eapply VTrExprS_let; [rewrite <- Hctx_eq; exact Hval_ty | exact (IHA A0 val e0 pre suf Hbnd Hval) |
      exact (IHv A0 val e0 pre suf Hbnd Hval) |].
    eapply (IHb A0 val e0 (VLLet ty' val' :: pre) suf); [simpl; rewrite Hbnd; reflexivity | exact Hval].
  - eapply VTrExprS_proj; [exact (IHa A0 val e0 pre suf Hbnd Hval) | rewrite <- Hctx_eq; exact Hproj].
  - eapply VTrExprS_natlit; [exact Hnat | rewrite <- Hctx_eq; exact Hnty].
  - eapply VTrExprS_strlit; [exact Hstr | exact Htrs | rewrite <- Hctx_eq; exact Hsty].
  - constructor. exact (IHa A0 val e0 pre suf Hbnd Hval).
Qed.

Lemma VTrExprS_subst_let env venv ps :
  VEnvClosed venv ->
  forall e fs A0 val e0 pre suf e',
    VTrExprS env venv ps {| vl_free := fs; vl_bound := suf |} val e0 ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := pre ++ VLLet A0 e0 :: suf |} e e' ->
    VTrExprS env venv ps {| vl_free := fs; vl_bound := pre ++ suf |}
      (subst (List.length pre) val e) e'.
Proof.
  intros Hcl e fs A0 val e0 pre suf e' Hval Htr.
  exact (VTrExprS_subst_let_L Hcl Htr (pre:=pre) (suf:=suf) eq_refl Hval).
Qed.

Corollary VTrExpr_instantiate_let env venv ps L A0 val e0 body body' :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  VHasType venv (List.length ps) (vl_ctx L) e0 A0 ->
  VTrExpr env venv ps L val e0 ->
  VTrExpr env venv ps (vl_push_let L A0 e0) body body' ->
  VTrExpr env venv ps L (instantiate body val) body'.
Proof.
  intros Hves HwfL He0 [v0 [Hv0 [Tv Hveq]]] Hbody.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG He0 (VIsDefEq_refl_r Hveq)) as [uv Hcv].
  assert (Hveq' : VIsDefEq venv (List.length ps) (vl_ctx L) v0 e0 A0)
    by (eapply VDF_defeqDF; [exact (VDF_symm Hcv) | exact Hveq]).
  assert (Hv0_A0 : VHasType venv (List.length ps) (vl_ctx L) v0 A0)
    by (exact (VIsDefEq_refl_l Hveq')).
  assert (Hwf1 : VLCtxWF venv (List.length ps) (vl_push_let L A0 e0))
    by (apply VLCtxWF_push_let; assumption).
  assert (Hwf2 : VLCtxWF venv (List.length ps) (vl_push_let L A0 v0))
    by (apply VLCtxWF_push_let; assumption).
  assert (Hceq : VLCtxDefEq venv (List.length ps) (vl_push_let L A0 e0) (vl_push_let L A0 v0)).
  { destruct (VLCtxDefEq_refl Hwf HwfL) as [Hn [Hf Hb]].
    destruct (VIsDefEq_isType Hwf HG He0) as [uA HuA].
    repeat split; simpl; auto. econstructor; [exact Hb | exact HuA | exact (VDF_symm Hveq')]. }
  pose proof (VTrExpr_defeq_ctx Hves Hwf1 Hwf2 Hceq Hbody) as [b0 [Hb0 Hbeq]].
  destruct L as [fs bs].
  exists b0. split; [| exact Hbeq].
  exact (@VTrExprS_subst_let env venv ps Hcl body fs A0 val v0 [] bs b0 Hv0 Hb0).
Qed.

(* Relating subst_many to iterated single-variable subst *)
Lemma lift_lift_eq m n k e :
  lift m k (lift n k e) = lift (m + n) k e.
Proof.
  revert k.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA v IHv b IHb nd|l|s idx a IHa|a IHa];
    intros k; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity);
    try (rewrite IHA, IHv, IHb; reflexivity);
    try (rewrite IHa; reflexivity).
  destruct (Nat.leb_spec k i).
  - destruct (Nat.leb_spec k (n + i)); [f_equal; lia | lia].
  - destruct (Nat.leb_spec k i); [lia | reflexivity].
Qed.

Lemma subst_lift_skip idx v e :
  subst idx v (lift (S idx) 0 e) = lift idx 0 e.
Proof.
  assert (Hgen : forall m d k e0, k <= d -> m = d - k ->
    subst d v (lift (S m) k e0) = lift m k e0).
  { intros m d k e0. revert m d k.
    induction e0 as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                     |nm A IHA w IHw b IHb nd|l|s j a IHa|a IHa];
      intros m d k Hkd Hm; simpl; try reflexivity;
      try (rewrite (IHf m d k), (IHa m d k) by lia; reflexivity);
      try (rewrite (IHA m d k), (IHb m (S d) (S k)) by lia; reflexivity);
      try (rewrite (IHA m d k), (IHB m (S d) (S k)) by lia; reflexivity);
      try (rewrite (IHA m d k), (IHw m d k), (IHb m (S d) (S k)) by lia; reflexivity);
      try (rewrite (IHa m d k) by lia; reflexivity).
    destruct (Nat.leb_spec k i).
    - replace (Nat.eqb (S (m + i)) d) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (d <? S (m + i)) with true by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
    - replace (Nat.eqb i d) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (d <? i) with false by (symmetry; apply Nat.ltb_ge; lia).
      reflexivity. }
  apply (Hgen idx idx 0 e); lia.
Qed.

Lemma lift_0_id e : forall k, lift 0 k e = e.
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s j a IHa|a IHa];
    intros k; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity);
    try (rewrite IHA, IHw, IHb; reflexivity);
    try (rewrite IHa; reflexivity).
  destruct (k <=? i); reflexivity.
Qed.

Lemma subst_many_nil e : forall idx, subst_many idx [] e = e.
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s j a IHa|a IHa];
    intros idx; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity);
    try (rewrite IHA, IHw, IHb; reflexivity);
    try (rewrite IHa; reflexivity).
  destruct (i <? idx); [reflexivity |].
  rewrite nth_error_nil. f_equal. lia.
Qed.

Lemma subst_many_cons e : forall idx v vs,
  subst_many idx (v :: vs) e = subst idx v (subst_many (S idx) vs e).
Proof.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s j a IHa|a IHa];
    intros idx v vs; simpl; try reflexivity;
    try (rewrite IHf, IHa; reflexivity);
    try (rewrite IHA, IHb; reflexivity);
    try (rewrite IHA, IHB; reflexivity);
    try (rewrite IHA, IHw, IHb; reflexivity);
    try (rewrite IHa; reflexivity).
  destruct (Nat.ltb_spec i idx) as [Hlt | Hge].
  - replace (i <? S idx) with true by (symmetry; apply Nat.ltb_lt; lia).
    simpl.
    replace (Nat.eqb i idx) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (idx <? i) with false by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
  - destruct (Nat.eqb_spec i idx) as [-> | Hne].
    + replace (idx <? S idx) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite Nat.sub_diag. simpl. rewrite Nat.eqb_refl. reflexivity.
    + replace (i <? S idx) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (i - idx) with (S (i - S idx)) by lia. simpl.
      destruct (nth_error vs (i - S idx)) as [w|] eqn:Hw.
      * rewrite subst_lift_skip. destruct idx; [rewrite lift_0_id |]; reflexivity.
      * simpl.
        assert (Hlen : List.length vs <= i - S idx) by (apply nth_error_None; exact Hw).
        replace (Nat.eqb (i - List.length vs) idx) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (idx <? i - List.length vs) with true by (symmetry; apply Nat.ltb_lt; lia).
        f_equal. replace (i - List.length vs) with (S (i - S (List.length vs))) by lia. reflexivity.
Qed.

(* Universe instantiation on VTrExprS / VTrExpr (for closed constant types/values) *)
Lemma VTrExprS_subst_levels env venv params ps us us' :
  List.length us = List.length params ->
  TrLevels ps us us' ->
  forall e e',
    VTrExprS env venv params vl_empty e e' ->
    VTrExprS env venv ps vl_empty (subst_levels params us e) (vinstL us' e').
Proof.
  intros Hlen Hus.
  assert (Hwf_us : Forall (vlevel_wf (List.length ps)) us') by (eapply TrLevels_wf; exact Hus).
  assert (Hls : trLs ps us = Some us').
  { clear -Hus. induction Hus; simpl; [reflexivity | rewrite H, IHHus; reflexivity]. }
  set (mapE := fun x : VLCtxEntry => match x with
    | VLLam A => VLLam (vinstL us' A)
    | VLLet A v => VLLet (vinstL us' A) (vinstL us' v)
    end).
  set (mapL := fun L0 : VLCtx =>
    {| vl_free := map (fun p => (fst p, mapE (snd p))) (vl_free L0);
       vl_bound := map mapE (vl_bound L0) |}).
  assert (Hgen : forall e L e',
    VTrExprS env venv params L e e' ->
    VTrExprS env venv ps (mapL L)
      (subst_levels params us e) (vinstL us' e')).
  { intros e L e' Htr.
    assert (Hctx_map : forall es,
      vlentries_to_ctx (map mapE es) = map (vinstL us') (vlentries_to_ctx es)).
    { induction es as [|[A|A v] r IH]; simpl; [reflexivity | f_equal |]; exact IH. }
    assert (Hfctx_map : forall fs,
      vl_free_ctx (map (fun p => (fst p, mapE (snd p))) fs) =
      map (vinstL us') (vl_free_ctx fs)).
    { intros fs. unfold vl_free_ctx. rewrite map_map. simpl.
      rewrite <- (map_map snd mapE fs). apply Hctx_map. }
    assert (Hvl_ctx_map : forall L0, vl_ctx (mapL L0) = map (vinstL us') (vl_ctx L0)).
    { intros L0. unfold vl_ctx, mapL. simpl. rewrite Hctx_map, Hfctx_map, map_app. reflexivity. }
    induction Htr; simpl.
    - assert (Hlk : vl_bvar (mapL L) i = Some (vinstL us' e', vinstL us' ty')).
      { unfold vl_bvar, mapL, mapE in *. simpl in *.
        clear -H. revert i e' ty' H. generalize 0 as d.
        induction (vl_bound L) as [|[A|A v] r IH]; intros d [|i] e' ty' H0; simpl in *;
          try discriminate; auto.
        - inversion H0; subst. rewrite vinstL_vliftN. reflexivity.
        - inversion H0; subst. rewrite !vinstL_vliftN. reflexivity. }
      eapply VTrExprS_bvar; [exact Hlk |].
      rewrite Hvl_ctx_map. eapply VIsDefEq_instL; eassumption.
    - assert (Hlk : vl_fvar (mapL L) n = Some (vinstL us' e', vinstL us' ty')).
      { unfold vl_fvar, vl_bound_lams, mapL in *. simpl in *.
        rewrite Hctx_map, List.length_map. unfold mapE.
        clear -H. revert e' ty' H.
        generalize (List.length (vlentries_to_ctx (vl_bound L))) as d.
        induction (vl_free L) as [|[m [A|A v]] r IH]; intros d e' ty' H0; simpl in *;
          try discriminate; destruct (name_eqb n m); auto.
        - inversion H0; subst. rewrite vinstL_vliftN. reflexivity.
        - inversion H0; subst. rewrite !vinstL_vliftN. reflexivity. }
      eapply VTrExprS_fvar; [exact Hlk |].
      rewrite Hvl_ctx_map. eapply VIsDefEq_instL; eassumption.
    - constructor. unfold TrLevel in *. eapply trL_subst; eassumption.
    - econstructor; [exact H | | rewrite List.length_map; exact H1].
      clear -H0 Hlen Hls.
      induction H0; constructor; [eapply trL_subst; eassumption | exact IHTrLevels].
    - eapply VTrExprS_app with (A := vinstL us' A) (B := vinstL us' B);
        [rewrite Hvl_ctx_map; exact (VIsDefEq_instL Hwf_us H) |
         rewrite Hvl_ctx_map; exact (VIsDefEq_instL Hwf_us H0) |
         exact IHHtr1 | exact IHHtr2].
    - eapply VTrExprS_lam; [| exact IHHtr1 | exact IHHtr2].
      destruct H as [u Hu]. exists (vlevel_inst us' u).
      rewrite Hvl_ctx_map. exact (VIsDefEq_instL Hwf_us Hu).
    - eapply VTrExprS_pi; [| | exact IHHtr1 | exact IHHtr2].
      + destruct H as [u Hu]. exists (vlevel_inst us' u).
        rewrite Hvl_ctx_map. exact (VIsDefEq_instL Hwf_us Hu).
      + destruct H0 as [v Hv]. exists (vlevel_inst us' v).
        rewrite Hvl_ctx_map.
        exact (VIsDefEq_instL (G := ty' :: vl_ctx L) Hwf_us Hv).
    - eapply VTrExprS_let with (ty' := vinstL us' ty') (val' := vinstL us' val');
        [rewrite Hvl_ctx_map; exact (VIsDefEq_instL Hwf_us H) |
         exact IHHtr1 | exact IHHtr2 | exact IHHtr3].
    - eapply VTrExprS_proj; [exact IHHtr |].
      rewrite Hvl_ctx_map. eapply VTrProj_instL; eassumption.
    - rewrite vinstL_natLit.
      eapply VTrExprS_natlit; [exact H |].
      rewrite Hvl_ctx_map.
      pose proof (VIsDefEq_instL Hwf_us H0) as Hi.
      rewrite vinstL_natLit in Hi. exact Hi.
    - rewrite (vinstL_trStrLit us' H0).
      eapply VTrExprS_strlit; [exact H | exact H0 |].
      rewrite Hvl_ctx_map.
      pose proof (VIsDefEq_instL Hwf_us H1) as Hi.
      rewrite (vinstL_trStrLit us' H0) in Hi. exact Hi.
    - constructor. exact IHHtr. }
  intros e e' Htr. exact (Hgen e vl_empty e' Htr).
Qed.

Corollary VTrExpr_subst_levels env venv params ps us us' e e' :
  List.length us = List.length params ->
  TrLevels ps us us' ->
  VTrExpr env venv params vl_empty e e' ->
  VTrExpr env venv ps vl_empty (subst_levels params us e) (vinstL us' e').
Proof.
  intros Hlen Hus [e0 [Htr [A Hdef]]].
  exists (vinstL us' e0). split.
  - eapply VTrExprS_subst_levels; eassumption.
  - exists (vinstL us' A).
    change (vl_ctx vl_empty) with (map (vinstL us') (vl_ctx vl_empty)).
    eapply VIsDefEq_instL; [eapply TrLevels_wf; exact Hus | exact Hdef].
Qed.

(* Weakening closed empty-context expressions into any VLCtx L *)
Lemma VCtxLiftN_closed_suffix env U bs0 G :
  VEnvWF env ->
  VLCtxEntriesWF env U [] bs0 ->
  VCtxLiftN (List.length G) (List.length (vlentries_to_ctx bs0))
    (vlentries_to_ctx bs0) (vlentries_to_ctx bs0 ++ G).
Proof.
  intros Hwf Hbs.
  assert (Hcl : VEnvClosed env) by (apply VEnvWF_closed; exact Hwf).
  induction Hbs as [| ty rest Hr IH Hty | ty val rest Hr IH Hv]; simpl.
  - pose proof (VCtxLiftN_app_prefix G []) as W.
    rewrite app_nil_r in W. exact W.
  - destruct Hty as [u Hu].
    rewrite app_nil_r in Hu.
    assert (Hcw : VCtxClosed (vlentries_to_ctx rest)).
    { apply VCtxWF_closed with (env := env) (U := U); [exact Hcl |].
      rewrite <- (app_nil_r (vlentries_to_ctx rest)).
      apply VLCtxEntriesWF_to_VCtxWF; [exact I | exact Hr]. }
    destruct (VIsDefEq_closedN Hcl Hu Hcw) as [Hcty _].
    replace ty with (vliftN (List.length G) (List.length (vlentries_to_ctx rest)) ty) at 2
      by (eapply vliftN_closed_eq; [exact Hcty | lia]).
    constructor. exact IH.
  - exact IH.
Qed.

Lemma vl_lookup_bound_lt es : forall i d r,
  vl_lookup_bound es i d = Some r -> i < List.length es.
Proof.
  induction es as [|[A|A v] rest IH]; intros [|i] d r H; simpl in *; try discriminate; try lia.
  - specialize (IH i (S d) r H). lia.
  - specialize (IH i d r H). lia.
Qed.

Lemma VTrExprS_closed_to_any_L env venv ps :
  VEnvWF venv ->
  forall L0 e e',
    VTrExprS env venv ps L0 e e' ->
    vl_free L0 = [] ->
    VLCtxEntriesWF venv (List.length ps) [] (vl_bound L0) ->
    forall L,
      VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := vl_bound L0 ++ vl_bound L |} e e'.
Proof.
  intros Hwf L0 e e' Htr.
  assert (Hcl : VEnvClosed venv) by (apply VEnvWF_closed; exact Hwf).
  induction Htr as
    [ L0 i e1 ty1 Hlk Hty
    | L0 nm e1 ty1 Hlk Hty
    | L0 u u' Htr_u
    | L0 c ci us us' Hci Htr_us Hlen_us
    | L0 f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L0 nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L0 nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L0 nm ty val0 body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L0 owner idx0 a a' proj' field_ty Htr_a IHa Hproj
    | L0 n Hnat Hnty
    | L0 s s' Hstr Htrs Hsty
    | L0 a a' Htr_a IHa ];
    intros Hfr Hbs L;
    pose proof (VCtxLiftN_closed_suffix (vl_ctx L) Hwf Hbs) as W0;
    assert (W : VCtxLiftN (List.length (vl_ctx L)) (List.length (vlentries_to_ctx (vl_bound L0)))
                  (vl_ctx L0)
                  (vl_ctx {| vl_free := vl_free L; vl_bound := vl_bound L0 ++ vl_bound L |}))
      by (unfold vl_ctx, vl_free_ctx; simpl; rewrite Hfr; simpl;
          rewrite app_nil_r, vlentries_to_ctx_app, <- app_assoc; exact W0);
    assert (Hcw : VCtxClosed (vl_ctx L0))
      by (apply VCtxWF_closed with (env := venv) (U := List.length ps);
          [exact Hcl |
           unfold vl_ctx, vl_free_ctx; rewrite Hfr; simpl;
           apply VLCtxEntriesWF_to_VCtxWF; [exact I | exact Hbs]]);
    assert (Hwk_has : forall x T,
      VHasType venv (List.length ps) (vl_ctx L0) x T ->
      VHasType venv (List.length ps)
        (vl_ctx {| vl_free := vl_free L; vl_bound := vl_bound L0 ++ vl_bound L |}) x T) by
      (intros x T Hx;
       destruct (VIsDefEq_closedN Hcl Hx Hcw) as [Hcx [_ HcT]];
       unfold vl_ctx, vl_free_ctx in Hcx, HcT; rewrite Hfr in Hcx, HcT; simpl in Hcx, HcT;
       rewrite app_nil_r in Hcx, HcT;
       pose proof (VIsDefEq_weakN Hcl Hx W) as Hw;
       rewrite (vliftN_closed_eq _ Hcx (Nat.le_refl _)),
               (vliftN_closed_eq _ HcT (Nat.le_refl _)) in Hw; exact Hw).
  - assert (Hlt : i < List.length (vl_bound L0)) by (eapply vl_lookup_bound_lt; exact Hlk).
    eapply VTrExprS_bvar.
    + unfold vl_bvar in *. simpl in *. rewrite vl_lookup_bound_app_l by exact Hlt. exact Hlk.
    + apply Hwk_has. exact Hty.
  - unfold vl_fvar in Hlk. rewrite Hfr in Hlk. simpl in Hlk. discriminate.
  - constructor; exact Htr_u.
  - econstructor; eassumption.
  - eapply VTrExprS_app; [apply Hwk_has; exact Hf_ty | apply Hwk_has; exact Ha_ty |
      exact (IHf Hfr Hbs L) | exact (IHa Hfr Hbs L)].
  - eapply VTrExprS_lam.
    + destruct Hty_is as [u Hu]. exists u. apply Hwk_has. exact Hu.
    + exact (IHA Hfr Hbs L).
    + unfold vl_push_lam in *. simpl in *.
      apply (IHb Hfr); [constructor; [exact Hbs | unfold vl_ctx, vl_free_ctx in Hty_is; rewrite Hfr in Hty_is; exact Hty_is]].
  - eapply VTrExprS_pi.
    + destruct Hty_is as [u Hu]. exists u. apply Hwk_has. exact Hu.
    + destruct Hbody_is as [v Hv]. exists v.
      assert (Hbs' : VLCtxEntriesWF venv (List.length ps) [] (VLLam ty' :: vl_bound L0)).
      { constructor; [exact Hbs | unfold vl_ctx, vl_free_ctx in Hty_is; rewrite Hfr in Hty_is; exact Hty_is]. }
      pose proof (VCtxLiftN_closed_suffix (vl_ctx L) Hwf Hbs') as W'.
      assert (Hcw' : VCtxClosed (ty' :: vlentries_to_ctx (vl_bound L0))).
      { apply VCtxWF_closed with (env := venv) (U := List.length ps); [exact Hcl |].
        rewrite <- (app_nil_r (ty' :: vlentries_to_ctx (vl_bound L0))).
        exact (VLCtxEntriesWF_to_VCtxWF (env:=venv) (U:=List.length ps) (base:=[]) I Hbs'). }
      unfold vl_ctx, vl_free_ctx in Hv; rewrite Hfr in Hv; simpl in Hv; rewrite app_nil_r in Hv.
      destruct (VIsDefEq_closedN Hcl Hv Hcw') as [Hcb _].
      pose proof (VIsDefEq_weakN Hcl Hv W') as Hw.
      simpl in Hcb, Hw. rewrite (vliftN_closed_eq _ Hcb (Nat.le_refl _)) in Hw.
      unfold vl_ctx; simpl; rewrite vlentries_to_ctx_app, <- app_assoc. exact Hw.
    + exact (IHA Hfr Hbs L).
    + unfold vl_push_lam in *. simpl in *.
      apply (IHB Hfr); [constructor; [exact Hbs | unfold vl_ctx, vl_free_ctx in Hty_is; rewrite Hfr in Hty_is; exact Hty_is]].
  - eapply VTrExprS_let; [apply Hwk_has; exact Hval_ty | exact (IHA Hfr Hbs L) | exact (IHv Hfr Hbs L) |].
    unfold vl_push_let in *. simpl in *.
    apply (IHb Hfr).
    constructor; [exact Hbs | unfold vl_ctx, vl_free_ctx in Hval_ty; rewrite Hfr in Hval_ty; exact Hval_ty].
  - eapply VTrExprS_proj; [exact (IHa Hfr Hbs L) |].
    destruct Hproj as [info ctor c d us ps_e idxs Hi Hc Hd Hk Hlt Hlp Hli Hw Hlu Hst Hpv Hty].
    subst proj'.
    eapply VTrProj_intro; try eassumption; [apply Hwk_has; exact Hst | reflexivity | apply Hwk_has; exact Hty].
  - eapply VTrExprS_natlit; [exact Hnat | apply Hwk_has; exact Hnty].
  - eapply VTrExprS_strlit; [exact Hstr | exact Htrs | apply Hwk_has; exact Hsty].
  - constructor. exact (IHa Hfr Hbs L).
Qed.

Lemma VTrExprS_closed_to_any_gen env venv ps :
  VEnvWF venv ->
  forall e bs L e',
    VLCtxEntriesWF venv (List.length ps) [] bs ->
    VTrExprS env venv ps {| vl_free := []; vl_bound := bs |} e e' ->
    VTrExprS env venv ps {| vl_free := vl_free L; vl_bound := bs ++ vl_bound L |} e e'.
Proof.
  intros Hwf e bs L e' Hbs Htr.
  exact (VTrExprS_closed_to_any_L Hwf Htr eq_refl Hbs L).
Qed.

Corollary VTrExpr_closed_to_any env venv ps L e e' :
  VEnvWF venv ->
  VTrExpr env venv ps vl_empty e e' ->
  VTrExpr env venv ps L e e'.
Proof.
  intros Hwf [e0 [Htr [A Hdef]]].
  assert (Hcl : VEnvClosed venv) by (apply VEnvWF_closed; exact Hwf).
  exists e0. split.
  - pose proof (VTrExprS_closed_to_any_gen Hwf L (VLCtxEntriesWF_nil _ _ _) Htr) as Hw.
    destruct L; exact Hw.
  - exists A. exact (VIsDefEq_weak0 (vl_ctx L) Hcl Hdef).
Qed.

(* ========================================================================= *)
(* 10. Alpha Equality, Core Spine, and InferSoundness.trE Embedding          *)
(* ========================================================================= *)

Lemma literal_eqb_true a b : literal_eqb a b = true -> a = b.
Proof.
  destruct a, b; simpl; intro H; try discriminate.
  - apply N.eqb_eq in H. subst. reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
Qed.

Lemma VTrExprS_expr_eqb env venv ps :
  forall L e1 v1,
    VTrExprS env venv ps L e1 v1 ->
    forall e2,
      expr_eqb e1 e2 = true ->
      VTrExprS env venv ps L e2 v1.
Proof.
  intros L e1 v1 Htr.
  induction Htr as
    [ L i e1 ty1 Hlk Hty
    | L n e1 ty1 Hlk Hty
    | L u u' Htr_u
    | L c ci us us' Hci Htr_us Hlen_us
    | L f a f' a' A B Hf_ty Ha_ty Htr_f IHf Htr_a IHa
    | L nm bi ty body ty' body' Hty_is Htr_ty IHA Htr_body IHb
    | L nm bi ty body ty' body' Hty_is Hbody_is Htr_ty IHA Htr_body IHB
    | L nm ty val body nd ty' val' body' Hval_ty Htr_ty IHA Htr_val IHv Htr_body IHb
    | L owner idx a a' proj' field_ty Htr_a IHa Hproj
    | L n Hnat Hnty
    | L s s' Hstr Htrs Hsty
    | L a a' Htr_a IHa ];
    intros [j|y1|y2|v|d vs|g z|n1 b1 C1 c1|n2 b2 C2 c2|n3 C3 w3 c3 nd3|l'|own' idx' z'|z''] Heq;
    simpl in Heq; try discriminate.
  - apply Nat.eqb_eq in Heq. subst. eapply VTrExprS_bvar; eassumption.
  - apply name_eqb_eq in Heq. subst. eapply VTrExprS_fvar; eassumption.
  - apply level_eqb_true in Heq. subst. constructor; exact Htr_u.
  - apply andb_true_iff in Heq as [Hn Hl].
    apply name_eqb_eq in Hn. apply list_level_eqb_true in Hl. subst.
    econstructor; eassumption.
  - apply andb_true_iff in Heq as [Hf Ha].
    eapply VTrExprS_app; [exact Hf_ty | exact Ha_ty | exact (IHf _ Hf) | exact (IHa _ Ha)].
  - apply andb_true_iff in Heq as [HA Hb].
    eapply VTrExprS_lam; [exact Hty_is | exact (IHA _ HA) | exact (IHb _ Hb)].
  - apply andb_true_iff in Heq as [HA HB].
    eapply VTrExprS_pi; [exact Hty_is | exact Hbody_is | exact (IHA _ HA) | exact (IHB _ HB)].
  - apply andb_true_iff in Heq as [H1' Hb].
    apply andb_true_iff in H1' as [HA Hw].
    eapply VTrExprS_let; [exact Hval_ty | exact (IHA _ HA) | exact (IHv _ Hw) | exact (IHb _ Hb)].
  - apply andb_true_iff in Heq as [H1' Ha].
    apply andb_true_iff in H1' as [Ho Hi].
    apply name_eqb_eq in Ho. apply Nat.eqb_eq in Hi. subst.
    eapply VTrExprS_proj; [exact (IHa _ Ha) | exact Hproj].
  - destruct l' as [m|s']; [|discriminate]. apply N.eqb_eq in Heq. subst. eapply VTrExprS_natlit; eassumption.
  - destruct l' as [m|s2]; [discriminate|]. apply String.eqb_eq in Heq. subst. eapply VTrExprS_strlit; eassumption.
  - constructor. exact (IHa _ Heq).
Qed.

Theorem VTrExpr_expr_eqb env venv ps L e1 e2 v1 v2 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  expr_eqb e1 e2 = true ->
  VTrExpr env venv ps L e1 v1 ->
  VTrExpr env venv ps L e2 v2 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) v1 v2.
Proof.
  intros Hves HwfL Heq [e0 [Htr1 Hd1]] Htr2.
  assert (Htr1' : VTrExpr env venv ps L e2 v1).
  { exists e0. split; [eapply VTrExprS_expr_eqb; eassumption | exact Hd1]. }
  eapply VTrExpr_uniq; eassumption.
Qed.

Corollary VTrExpr_core_alpha_eq env venv ps L e1 e2 v1 v2 :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  core_alpha_eq e1 e2 = true ->
  VTrExpr env venv ps L e1 v1 ->
  VTrExpr env venv ps L e2 v2 ->
  VIsDefEqU venv (List.length ps) (vl_ctx L) v1 v2.
Proof.
  intros Hves HwfL Ha H1 H2.
  unfold core_alpha_eq in Ha.
  destruct (core_alpha 256 e1 e2) as [ok rem] eqn:E. simpl in Ha. subst ok.
  eapply VTrExpr_expr_eqb; [exact Hves | exact HwfL | eapply core_alpha_sound; exact E | exact H1 | exact H2].
Qed.

(* Spine decomposition & reconstruction on VTrExpr *)
Lemma core_spine_core_apps e : forall acc,
  core_apps (fst (core_spine e acc)) (snd (core_spine e acc)) = core_apps e acc.
Proof.
  induction e; intros acc; simpl; try reflexivity.
  rewrite IHe1. reflexivity.
Qed.

Lemma VTrExprS_core_apps_inv env venv ps L args : forall f e',
  VTrExprS env venv ps L (core_apps f args) e' ->
  exists f' args',
    e' = vapps f' args' /\
    VTrExprS env venv ps L f f' /\
    Forall2 (VTrExprS env venv ps L) args args'.
Proof.
  induction args as [|a rest IH]; intros f e' Htr; simpl in *.
  - exists e', []. repeat split; [exact Htr | constructor].
  - destruct (IH (EApp f a) e' Htr) as [fa' [rest' [-> [Hfa Hrest]]]].
    inversion Hfa as [| | | | ? ? ? f' a' A B Hf_ty Ha_ty Htr_f Htr_a | | | | | | |]; subst.
    exists f', (a' :: rest'). repeat split; [exact Htr_f | constructor; assumption].
Qed.

Lemma VTrExpr_core_apps_inv env venv ps L f args e' :
  VTrExpr env venv ps L (core_apps f args) e' ->
  exists f' args',
    VIsDefEqU venv (List.length ps) (vl_ctx L) (vapps f' args') e' /\
    VTrExprS env venv ps L f f' /\
    Forall2 (VTrExprS env venv ps L) args args'.
Proof.
  intros [e0 [Htr Heq]].
  destruct (VTrExprS_core_apps_inv Htr) as [f' [args' [-> [Hf Hargs]]]].
  exists f', args'. auto.
Qed.

Lemma VTrExpr_core_apps env venv ps L args :
  VEnvSound env venv ->
  VLCtxWF venv (List.length ps) L ->
  forall f f' args',
    VTrExpr env venv ps L f f' ->
    Forall2 (VTrExpr env venv ps L) args args' ->
    VExprWF venv (List.length ps) (vl_ctx L) (vapps f' args') ->
    VTrExpr env venv ps L (core_apps f args) (vapps f' args').
Proof.
  intros Hves HwfL.
  pose proof (ves_wf Hves) as Hwf.
  pose proof (ves_inj Hves) as Hinj.
  pose proof (VLCtxWF_to_VCtxWF HwfL) as HG.
  induction args as [|a rest IH]; intros f f' args' Hf Hargs Hwf_app;
    inversion Hargs as [| ? y ? l' Hy Hrest]; subst; simpl in *.
  - exact Hf.
  - assert (Hwf_fa : VExprWF venv (List.length ps) (vl_ctx L) (VApp f' y)).
    { clear -Hwf HG Hwf_app. revert Hwf_app. generalize (VApp f' y) as h.
      induction l' as [|z zs IHz]; intros h Hh; [exact Hh |].
      destruct (IHz (VApp h z) Hh) as [T HT].
      destruct (VHasType_app_inv Hwf HG HT) as [A [B [Hh' _]]].
      exists (VForallE A B). exact Hh'. }
    apply IH; [| exact Hrest | exact Hwf_app].
    destruct Hf as [f0 [Hf0 [Tf Hfeq]]].
    destruct Hy as [a0 [Ha0 [Ta Haeq]]].
    destruct Hwf_fa as [Tfa HTfa].
    destruct (VHasType_app_inv Hwf HG HTfa) as [A [B [Hf'_ty Ha'_ty]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Hf'_ty (VIsDefEq_refl_r Hfeq)) as [uf Hcf].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG Ha'_ty (VIsDefEq_refl_r Haeq)) as [ua Hca].
    assert (Hfeq' : VIsDefEq venv (List.length ps) (vl_ctx L) f0 f' (VForallE A B))
      by (eapply VDF_defeqDF; [exact (VDF_symm Hcf) | exact Hfeq]).
    assert (Haeq' : VIsDefEq venv (List.length ps) (vl_ctx L) a0 y A)
      by (eapply VDF_defeqDF; [exact (VDF_symm Hca) | exact Haeq]).
    exists (VApp f0 a0). split.
    + eapply VTrExprS_app;
        [exact (VIsDefEq_refl_l Hfeq') | exact (VIsDefEq_refl_l Haeq') | exact Hf0 | exact Ha0].
    + exists (vinst0 B a0). eapply VDF_appDF; [exact Hfeq' | exact Haeq'].
Qed.

(* Exact embedding of InferSoundness.TrBCtx and InferSoundness.trE *)
Lemma VTrExprS_of_trE env venv ps :
  VEnvWF venv ->
  forall e L e',
    VLCtxWF venv (List.length ps) L ->
    (forall i T, VLookup (vl_ctx L) i T -> vl_bvar L i = Some (VBVar i, T)) ->
    trE ps e = Some e' ->
    VExprWF venv (List.length ps) (vl_ctx L) e' ->
    VTrExprS env venv ps L e e'.
Proof.
  intros Hwf.
  induction e as [i|x|x|u|c us|f IHf a IHa|nm bi A IHA b IHb|nm bi A IHA B IHB
                  |nm A IHA w IHw b IHb nd|l|s idx a IHa|a IHa];
    intros L e' HwfL Hlk_b Htr [T HT];
    pose proof (VLCtxWF_to_VCtxWF HwfL) as HG;
    simpl in Htr; try discriminate.
  - (* EBVar *)
    inversion Htr; subst e'; clear Htr.
    destruct (VHasType_bvar_inv Hwf HG HT) as [T0 Hlk].
    eapply VTrExprS_bvar; [apply Hlk_b; exact Hlk | apply VDF_bvar; exact Hlk].
  - (* ESort *)
    destruct (vlevel_of_level ps u) as [u'|] eqn:Hu; simpl in Htr; [|discriminate].
    inversion Htr; subst e'. constructor. exact Hu.
  - (* EConst *)
    destruct (trLs ps us) as [us'|] eqn:Hus; simpl in Htr; [|discriminate].
    inversion Htr; subst e'.
    destruct (VHasType_const_inv Hwf HG HT) as [ci [Hci [_ Hlen]]].
    assert (Htrls : TrLevels ps us us').
    { clear -Hus. revert us' Hus. induction us as [|u r IH]; intros us' H; simpl in H.
      - inversion H; constructor.
      - destruct (vlevel_of_level ps u) eqn:Hu; destruct (trLs ps r) eqn:Hr; try discriminate.
        inversion H; subst. constructor; [exact Hu | apply IH; reflexivity]. }
    eapply VTrExprS_const; [exact Hci | exact Htrls |].
    rewrite (TrLevels_length Htrls). exact Hlen.
  - (* EApp *)
    destruct (trE ps f) as [f'|] eqn:Hf; destruct (trE ps a) as [a'|] eqn:Ha; try discriminate.
    inversion Htr; subst e'.
    destruct (VHasType_app_inv Hwf HG HT) as [A [B [Hf_ty Ha_ty]]].
    eapply VTrExprS_app; [exact Hf_ty | exact Ha_ty | |].
    + apply IHf; [exact HwfL | exact Hlk_b | reflexivity | exists (VForallE A B); exact Hf_ty].
    + apply IHa; [exact HwfL | exact Hlk_b | reflexivity | exists A; exact Ha_ty].
  - (* ELam *)
    destruct (trE ps A) as [A'|] eqn:HA; destruct (trE ps b) as [b'|] eqn:Hb; try discriminate.
    inversion Htr; subst e'.
    destruct (VHasType_lam_inv Hwf HG HT) as [HA_is Hb_wf].
    eapply VTrExprS_lam; [exact HA_is | |].
    + destruct HA_is as [u Hu]. apply IHA; [exact HwfL | exact Hlk_b | reflexivity | exists (VSort u); exact Hu].
    + apply IHb; [apply VLCtxWF_push_lam; assumption | | reflexivity | exact Hb_wf].
      intros [|i] T0 Hlk; simpl in *.
      * inversion Hlk; subst. reflexivity.
      * inversion Hlk as [| ? ? ? ? Hlk']; subst.
        specialize (Hlk_b i _ Hlk').
        unfold vl_bvar in Hlk_b.
        exact (vl_lookup_bound_shift_at 1 (Nat.le_0_l 0) Hlk_b).
  - (* EPi *)
    destruct (trE ps A) as [A'|] eqn:HA; destruct (trE ps B) as [B'|] eqn:HB; try discriminate.
    inversion Htr; subst e'.
    destruct (VHasType_forallE_inv Hwf HT) as [HA_is HB_is].
    eapply VTrExprS_pi; [exact HA_is | exact HB_is | |].
    + destruct HA_is as [u Hu]. apply IHA; [exact HwfL | exact Hlk_b | reflexivity | exists (VSort u); exact Hu].
    + destruct HB_is as [v Hv]. apply IHB; [apply VLCtxWF_push_lam; assumption | | reflexivity | exists (VSort v); exact Hv].
      intros [|i] T0 Hlk; simpl in *.
      * inversion Hlk; subst. reflexivity.
      * inversion Hlk as [| ? ? ? ? Hlk']; subst.
        specialize (Hlk_b i _ Hlk').
        unfold vl_bvar in Hlk_b.
        exact (vl_lookup_bound_shift_at 1 (Nat.le_0_l 0) Hlk_b).
  - (* EMData *)
    constructor. apply IHa; [exact HwfL | exact Hlk_b | exact Htr | exists T; exact HT].
Qed.

Fixpoint vl_of_ctx_lams (G : list VExpr) : list VLCtxEntry :=
  match G with
  | [] => []
  | A :: rest => VLLam A :: vl_of_ctx_lams rest
  end.

Lemma vlentries_to_ctx_of_lams G : vlentries_to_ctx (vl_of_ctx_lams G) = G.
Proof. induction G as [|A G IH]; simpl; [reflexivity | f_equal; exact IH]. Qed.

Lemma vl_lookup_bound_of_lams G i T :
  VLookup G i T ->
  forall d,
    vl_lookup_bound (vl_of_ctx_lams G) i d = Some (VBVar (i + d), vliftN d 0 T).
Proof.
  induction 1; intros d; simpl.
  - unfold vlift. rewrite vliftN_comp. f_equal. f_equal. f_equal. lia.
  - rewrite IHVLookup. replace (i + S d) with (S i + d) by lia.
    unfold vlift. rewrite vliftN_comp. f_equal. f_equal. f_equal. lia.
Qed.

Lemma VTrCtx_of_TrBCtx env venv ps bs G :
  VEnvWF venv ->
  TrBCtx ps bs G ->
  VCtxWF venv (List.length ps) G ->
  VTrCtx env venv ps {| bound_context := bs; free_context := [] |}
                     {| vl_free := []; vl_bound := vl_of_ctx_lams G |}.
Proof.
  intros Hwf Htr HG. split; [constructor |].
  simpl. induction Htr as [| ty bs T G Hty Hbs IH]; simpl in *.
  - constructor.
  - destruct HG as [HG [u Hu]].
    specialize (IH HG).
    assert (HwfL : VLCtxWF venv (List.length ps) {| vl_free := []; vl_bound := vl_of_ctx_lams G |}).
    { split; [constructor |]. eapply VTrBoundCtx_to_VLCtxEntriesWF; exact IH. }
    constructor; [exact IH | | rewrite vlentries_to_ctx_of_lams, app_nil_r; exists u; exact Hu].
    apply VTrExprS_to_VTrExpr.
    apply VTrExprS_of_trE; [exact Hwf | exact HwfL | | exact Hty |].
    + intros i T0 Hlk. unfold vl_ctx in Hlk; simpl in Hlk; rewrite vlentries_to_ctx_of_lams, app_nil_r in Hlk.
      unfold vl_bvar; simpl. rewrite (vl_lookup_bound_of_lams Hlk 0), Nat.add_0_r, vliftN_zero.
      reflexivity.
    + unfold vl_ctx; simpl; rewrite vlentries_to_ctx_of_lams, app_nil_r. exists (VSort u). exact Hu.
Qed.

Print Assumptions VEnvSound_empty.
Print Assumptions VTrProj_congr.
Print Assumptions VTrExprS_uniq.
Print Assumptions VTrExpr_uniq.
Print Assumptions VTrExpr_defeq_ctx.
Print Assumptions VTrExpr_lift.
Print Assumptions VTrExpr_instantiate_lam.
Print Assumptions VTrExpr_instantiate_let.
Print Assumptions subst_many_cons.
Print Assumptions VTrExpr_subst_levels.
Print Assumptions VTrExpr_closed_to_any.
Print Assumptions VTrExpr_core_alpha_eq.
Print Assumptions VTrExprS_of_trE.
Print Assumptions VTrCtx_of_TrBCtx.

