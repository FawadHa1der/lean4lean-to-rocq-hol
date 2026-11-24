(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/{VDecl,Quot,Inductive}.lean and
   Lean4Lean/Theory/Typing/{Env,QuotLemmas,InductiveLemmas,EnvLemmas}.lean:
   semantic constant/definition/inductive/quotient declarations, environment
   extension combinators, constructive semantic quotient & inductive soundness,
   Quot.lift & Quot.ind computation rules (with Quot.ind derived automatically
   via VDF_proofIrrel), and unconditional declaration-trace environment
   well-formedness (VEnvDeclsWF -> VEnvWF). *)

From Stdlib Require Import List String Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel
  DeclarativeTyping TypingLemmas SubstTheory StrongTyping Quotient.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Semantic Declarations (Lean4Lean/Theory/VDecl.lean)                    *)
(* ========================================================================= *)

Record VConstVal : Type := {
  vcv_const : VConstant;
  vcv_name  : name
}.

Definition vcv_uvars (cv : VConstVal) : nat := vc_uvars (vcv_const cv).
Definition vcv_type (cv : VConstVal) : VExpr := vc_type (vcv_const cv).

Record VDefVal : Type := {
  vdv_const : VConstVal;
  vdv_value : VExpr
}.

Definition vdv_to_constant (dv : VDefVal) : VConstant := vcv_const (vdv_const dv).
Definition vdv_name (dv : VDefVal) : name := vcv_name (vdv_const dv).
Definition vdv_uvars (dv : VDefVal) : nat := vcv_uvars (vdv_const dv).
Definition vdv_type (dv : VDefVal) : VExpr := vcv_type (vdv_const dv).

Definition vdef_to_defeq (dv : VDefVal) : VDefEq := {|
  vdf_uvars := vdv_uvars dv;
  vdf_lhs   := VConst (vdv_name dv) (vlevel_params (vdv_uvars dv));
  vdf_rhs   := vdv_value dv;
  vdf_type  := vdv_type dv
|}.

Record VInductiveType : Type := {
  vit_const : VConstVal;
  vit_ctors : list VConstVal
}.

(* Constructive semantic inductive block: carries universe count, parameter
   count, inductive type formers with their constructors, generated recursor
   constants, and their semantic iota-reduction equations. *)
Record VInductDecl : Type := {
  vid_uvars   : nat;
  vid_nparams : nat;
  vid_types   : list VInductiveType;
  vid_recs    : list VConstVal;
  vid_iotas   : list VDefEq
}.

Inductive VDecl : Type :=
| VDAxiom     : VConstVal -> VDecl
| VDDef       : VDefVal -> VDecl
| VDOpaque    : VDefVal -> VDecl
| VDExample   : VDefVal -> VDecl
| VDQuot      : VDecl
| VDInduct    : VInductDecl -> VDecl
| VDMutualDef : list VDefVal -> VDecl.

(* ========================================================================= *)
(* 2. Universe & Environment Lookup Helpers                                  *)
(* ========================================================================= *)

Arguments venv_ord_const {env1 env2} _ {n ci} _.
Arguments venv_ord_defeq {env1 env2} _ {df} _.

Lemma vinst_vliftN_zero e v k :
  vinst (vliftN (S k) 0 e) v k = vliftN k 0 e.
Proof.
  replace (S k) with (1 + k) by lia.
  rewrite <- (@vliftN_vliftN e k 1 0 k ltac:(lia) ltac:(lia)).
  rewrite vinst_vliftN, vliftN_zero. reflexivity.
Qed.

Lemma vlookup_0 A G T : vlift A = T -> VLookup (A :: G) 0 T.
Proof. intros <-. apply VLookupZero. Qed.

Lemma vlookup_S A G i B T : VLookup G i B -> vlift B = T -> VLookup (A :: G) (S i) T.
Proof. intros H <-. apply VLookupSucc; exact H. Qed.

Ltac vlk :=
  match goal with
  | |- VLookup ?G _ _ => is_var G; unfold G; vlk
  | |- VLookup (_ :: _) 0 _ =>
      eapply vlookup_0; cbn [vlift vliftN vliftVar Nat.ltb Nat.leb]; reflexivity
  | |- VLookup (_ :: _) (S _) _ =>
      eapply vlookup_S; [vlk | cbn [vlift vliftN vliftVar Nat.ltb Nat.leb]; reflexivity]
  end.

Lemma venv_add_const_lookup_other env n m ci env' :
  venv_add_const env n ci = Some env' ->
  m <> n ->
  venv_constants env' m = venv_constants env m.
Proof.
  intros Hadd Hneq.
  unfold venv_add_const in Hadd.
  destruct (venv_constants env n); [discriminate |].
  inversion Hadd; subst; simpl.
  destruct (name_eqb m n) eqn:Heq.
  - apply name_eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma venv_add_const_constants_eq env n ci env' m :
  venv_add_const env n ci = Some env' ->
  venv_constants env' m = if name_eqb m n then Some ci else venv_constants env m.
Proof.
  unfold venv_add_const.
  destruct (venv_constants env n); [discriminate |].
  intros H; inversion H; subst; reflexivity.
Qed.

Lemma venv_add_const_eq_none env n ci :
  venv_constants env n = None ->
  exists env', venv_add_const env n ci = Some env'.
Proof.
  intros Hn. unfold venv_add_const. rewrite Hn. eexists; reflexivity.
Qed.

(* ========================================================================= *)
(* 3. Semantic Quotients (Lean4Lean/Theory/Quot.lean & QuotLemmas.lean)      *)
(* ========================================================================= *)

Definition vrel_type (alpha : VExpr) : VExpr :=
  VForallE alpha (VForallE (vlift alpha) (VSort VLZero)).

Definition veq_app (u : VLevel) (alpha x y : VExpr) : VExpr :=
  VApp (VApp (VApp (VConst q_eq_name [u]) alpha) x) y.

Definition vquot_app (u : VLevel) (alpha r : VExpr) : VExpr :=
  VApp (VApp (VConst q_name [u]) alpha) r.

Definition vquot_mk_app (u : VLevel) (alpha r a : VExpr) : VExpr :=
  VApp (VApp (VApp (VConst q_mk_name [u]) alpha) r) a.

Definition vquot_lift_app (u v : VLevel) (alpha r beta f c q : VExpr) : VExpr :=
  VApp (VApp (VApp (VApp (VApp (VApp (VConst q_lift_name [u; v]) alpha) r) beta) f) c) q.

Definition vquot_ind_app (u : VLevel) (alpha r beta h q : VExpr) : VExpr :=
  VApp (VApp (VApp (VApp (VApp (VConst q_ind_name [u]) alpha) r) beta) h) q.

(* Eq.{u} : {alpha : Sort u} -> alpha -> alpha -> Prop *)
Definition eqConst : VConstant := {|
  vc_uvars := 1;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (VBVar 0)
        (VForallE (VBVar 1) (VSort VLZero)))
|}.

(* Quot.{u} : {alpha : Sort u} -> (alpha -> alpha -> Prop) -> Sort u *)
Definition quotConst : VConstant := {|
  vc_uvars := 1;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (vrel_type (VBVar 0))
        (VSort (VLParam 0)))
|}.

(* Quot.mk.{u} : {alpha : Sort u} -> (r : alpha -> alpha -> Prop) -> alpha -> Quot.{u} alpha r *)
Definition quotMkConst : VConstant := {|
  vc_uvars := 1;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (vrel_type (VBVar 0))
        (VForallE (VBVar 1)
          (vquot_app (VLParam 0) (VBVar 2) (VBVar 1))))
|}.

(* Shared sanity-premise binder type for Quot.lift and quotDefEq *)
Definition ql_sanity_type (u1 : VLevel) : VExpr :=
  VForallE (VBVar 3)
    (VForallE (VBVar 4)
      (VForallE (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0))
        (veq_app u1 (VBVar 4) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))).

(* Quot.lift.{u, v} :
     {alpha : Sort u} -> {r : alpha -> alpha -> Prop} -> {beta : Sort v} ->
     (f : alpha -> beta) -> (forall a b, r a b -> Eq.{v} beta (f a) (f b)) ->
     Quot.{u} alpha r -> beta *)
Definition quotLiftConst : VConstant := {|
  vc_uvars := 2;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (vrel_type (VBVar 0))
        (VForallE (VSort (VLParam 1))
          (VForallE (VForallE (VBVar 2) (VBVar 1))
            (VForallE (ql_sanity_type (VLParam 1))
              (VForallE (vquot_app (VLParam 0) (VBVar 4) (VBVar 3))
                (VBVar 3))))))
|}.

(* Quot.ind.{u} :
     {alpha : Sort u} -> {r : alpha -> alpha -> Prop} ->
     {beta : Quot.{u} alpha r -> Prop} ->
     (forall a : alpha, beta (Quot.mk.{u} alpha r a)) ->
     forall q : Quot.{u} alpha r, beta q *)
Definition quotIndConst : VConstant := {|
  vc_uvars := 1;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (vrel_type (VBVar 0))
        (VForallE (VForallE (vquot_app (VLParam 0) (VBVar 1) (VBVar 0)) (VSort VLZero))
          (VForallE (VForallE (VBVar 2)
                      (VApp (VBVar 1) (vquot_mk_app (VLParam 0) (VBVar 3) (VBVar 2) (VBVar 0))))
            (VForallE (vquot_app (VLParam 0) (VBVar 3) (VBVar 2))
              (VApp (VBVar 2) (VBVar 0))))))
|}.

(* quotDefEq :
     (fun alpha r beta f c a => Quot.lift.{u,v} alpha r beta f c (Quot.mk.{u} alpha r a))
     ===
     (fun alpha r beta f c a => f a) *)
Definition quotDefEq : VDefEq := {|
  vdf_uvars := 2;
  vdf_lhs :=
    VLam (VSort (VLParam 0))
      (VLam (vrel_type (VBVar 0))
        (VLam (VSort (VLParam 1))
          (VLam (VForallE (VBVar 2) (VBVar 1))
            (VLam (ql_sanity_type (VLParam 1))
              (VLam (VBVar 4)
                (vquot_lift_app (VLParam 0) (VLParam 1)
                  (VBVar 5) (VBVar 4) (VBVar 3) (VBVar 2) (VBVar 1)
                  (vquot_mk_app (VLParam 0) (VBVar 5) (VBVar 4) (VBVar 0))))))) );
  vdf_rhs :=
    VLam (VSort (VLParam 0))
      (VLam (vrel_type (VBVar 0))
        (VLam (VSort (VLParam 1))
          (VLam (VForallE (VBVar 2) (VBVar 1))
            (VLam (ql_sanity_type (VLParam 1))
              (VLam (VBVar 4)
                (VApp (VBVar 2) (VBVar 0)))))));
  vdf_type :=
    VForallE (VSort (VLParam 0))
      (VForallE (vrel_type (VBVar 0))
        (VForallE (VSort (VLParam 1))
          (VForallE (VForallE (VBVar 2) (VBVar 1))
            (VForallE (ql_sanity_type (VLParam 1))
              (VForallE (VBVar 4)
                (VBVar 3))))))
|}.

Definition VQuotReady (env : VEnv) : Prop :=
  venv_constants env q_eq_name = Some eqConst.

Definition venv_add_quot (env : VEnv) : option VEnv :=
  match venv_add_const env q_name quotConst with
  | None => None
  | Some env1 =>
    match venv_add_const env1 q_mk_name quotMkConst with
    | None => None
    | Some env2 =>
      match venv_add_const env2 q_lift_name quotLiftConst with
      | None => None
      | Some env3 =>
        match venv_add_const env3 q_ind_name quotIndConst with
        | None => None
        | Some env4 => Some (venv_add_defeq env4 quotDefEq)
        end
      end
    end
  end.

(* Typing helpers for semantic Eq and Quotient applications *)

Lemma VHasType_vrel_type env U G alpha u :
  VEnvClosed env ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G (vrel_type alpha) (VSort (VLIMax u (VLIMax u (VLSucc VLZero)))).
Proof.
  intros Hcl Halpha.
  unfold vrel_type.
  eapply VDF_forallEDF; [exact Halpha |].
  eapply VDF_forallEDF; [exact (VIsDefEq_weak alpha Hcl Halpha) |].
  apply VHasType_sort. exact I.
Qed.

Lemma VHasType_eq_app env U G u alpha x y :
  venv_constants env q_eq_name = Some eqConst ->
  vlevel_wf U u ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G x alpha ->
  VHasType env U G y alpha ->
  VHasType env U G (veq_app u alpha x y) (VSort VLZero).
Proof.
  intros Heq Hu Halpha Hx Hy.
  unfold veq_app.
  assert (Hc : VHasType env U G (VConst q_eq_name [u])
                 (VForallE (VSort u) (VForallE (VBVar 0) (VForallE (VBVar 1) (VSort VLZero))))).
  { apply (@VDF_constDF env U G q_eq_name eqConst [u] [u] Heq);
      [constructor; [exact Hu | constructor]
      |constructor; [exact Hu | constructor]
      |reflexivity
      |constructor; [apply vlevel_equiv_refl | constructor]]. }
  pose proof (VDF_appDF Hc Halpha) as H1.
  replace (vinst0 (VForallE (VBVar 0) (VForallE (VBVar 1) (VSort VLZero))) alpha)
    with (VForallE alpha (VForallE (vliftN 1 0 alpha) (VSort VLZero))) in H1.
  2: { unfold vinst0; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb]. rewrite vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H1 Hx) as H2.
  replace (vinst0 (VForallE (vliftN 1 0 alpha) (VSort VLZero)) x)
    with (VForallE alpha (VSort VLZero)) in H2.
  2: { unfold vinst0; cbn [vinst]. rewrite vinst_vliftN_zero, vliftN_zero. reflexivity. }
  exact (VDF_appDF H2 Hy).
Qed.

Lemma VHasType_quot_app env U G u alpha r :
  venv_constants env q_name = Some quotConst ->
  vlevel_wf U u ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G r (vrel_type alpha) ->
  VHasType env U G (vquot_app u alpha r) (VSort u).
Proof.
  intros Hq Hu Halpha Hr.
  unfold vquot_app.
  assert (Hc : VHasType env U G (VConst q_name [u])
                 (VForallE (VSort u) (VForallE (vrel_type (VBVar 0)) (VSort u)))).
  { apply (@VDF_constDF env U G q_name quotConst [u] [u] Hq);
      [constructor; [exact Hu | constructor]
      |constructor; [exact Hu | constructor]
      |reflexivity
      |constructor; [apply vlevel_equiv_refl | constructor]]. }
  pose proof (VDF_appDF Hc Halpha) as H1.
  replace (vinst0 (VForallE (vrel_type (VBVar 0)) (VSort u)) alpha)
    with (VForallE (vrel_type alpha) (VSort u)) in H1.
  2: { unfold vinst0, vrel_type, vlift; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite vliftN_zero. reflexivity. }
  exact (VDF_appDF H1 Hr).
Qed.

Lemma VHasType_quot_mk_app env U G u alpha r a :
  venv_constants env q_mk_name = Some quotMkConst ->
  vlevel_wf U u ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G r (vrel_type alpha) ->
  VHasType env U G a alpha ->
  VHasType env U G (vquot_mk_app u alpha r a) (vquot_app u alpha r).
Proof.
  intros Hmk Hu Halpha Hr Ha.
  unfold vquot_mk_app.
  assert (Hc : VHasType env U G (VConst q_mk_name [u])
                 (VForallE (VSort u)
                   (VForallE (vrel_type (VBVar 0))
                     (VForallE (VBVar 1) (vquot_app u (VBVar 2) (VBVar 1)))))).
  { apply (@VDF_constDF env U G q_mk_name quotMkConst [u] [u] Hmk);
      [constructor; [exact Hu | constructor]
      |constructor; [exact Hu | constructor]
      |reflexivity
      |constructor; [apply vlevel_equiv_refl | constructor]]. }
  pose proof (VDF_appDF Hc Halpha) as H1.
  replace (vinst0 (VForallE (vrel_type (VBVar 0))
                    (VForallE (VBVar 1) (vquot_app u (VBVar 2) (VBVar 1)))) alpha)
    with (VForallE (vrel_type alpha)
           (VForallE (vliftN 1 0 alpha) (vquot_app u (vliftN 2 0 alpha) (VBVar 1)))) in H1.
  2: { unfold vinst0, vrel_type, vlift, vquot_app; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H1 Hr) as H2.
  replace (vinst0 (VForallE (vliftN 1 0 alpha) (vquot_app u (vliftN 2 0 alpha) (VBVar 1))) r)
    with (VForallE alpha (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r))) in H2.
  2: { unfold vinst0, vquot_app; cbn [vinst].
       rewrite !vinst_vliftN_zero, vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H2 Ha) as H3.
  replace (vinst0 (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r)) a)
    with (vquot_app u alpha r) in H3.
  2: { unfold vinst0, vquot_app; cbn [vinst].
       rewrite !vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  exact H3.
Qed.

Lemma VHasType_ql_sanity env U G u0 u1 :
  venv_constants env q_eq_name = Some eqConst ->
  vlevel_wf U u0 ->
  vlevel_wf U u1 ->
  VLookup G 3 (VSort u0) ->
  VLookup G 2 (vrel_type (VBVar 3)) ->
  VLookup G 1 (VSort u1) ->
  VLookup G 0 (VForallE (VBVar 3) (VBVar 2)) ->
  VHasType env U G (ql_sanity_type u1)
    (VSort (VLIMax u0 (VLIMax u0 (VLIMax VLZero VLZero)))).
Proof.
  intros Heq Hu0 Hu1 Hlk3 Hlk2 Hlk1 Hlk0.
  unfold ql_sanity_type.
  eapply VDF_forallEDF; [apply VDF_bvar; exact Hlk3 |].
  set (G1 := VBVar 3 :: G).
  assert (Ha_ty : VLookup G1 4 (VSort u0)) by (exact (VLookupSucc _ Hlk3)).
  eapply VDF_forallEDF; [apply VDF_bvar; exact Ha_ty |].
  set (G2 := VBVar 4 :: G1).
  assert (Hr_lk : VLookup G2 4 (vrel_type (VBVar 5))).
  { pose proof (VLookupSucc (VBVar 4) (VLookupSucc (VBVar 3) Hlk2)) as H.
    cbn [vlift vliftN vliftVar Nat.ltb Nat.leb] in H. exact H. }
  assert (Hb1 : VLookup G2 1 (VBVar 5))
    by (exact (VLookupSucc (VBVar 4) (VLookupZero (VBVar 3) G))).
  assert (Hb0 : VLookup G2 0 (VBVar 5))
    by (exact (VLookupZero (VBVar 4) G1)).
  assert (Hrab : VHasType env U G2 (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0)) (VSort VLZero)).
  { pose proof (VDF_appDF (@VDF_bvar env U _ _ _ Hr_lk) (@VDF_bvar env U _ _ _ Hb1)) as H1.
    cbn [vinst0 vinst vinstVar Nat.ltb Nat.leb Nat.eqb vlift vliftN vliftVar] in H1.
    exact (VDF_appDF H1 (@VDF_bvar env U _ _ _ Hb0)). }
  eapply VDF_forallEDF; [exact Hrab |].
  set (G3 := VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0) :: G2).
  assert (Hbeta_lk : VLookup G3 4 (VSort u1))
    by (exact (VLookupSucc _ (VLookupSucc _ (VLookupSucc _ Hlk1)))).
  assert (Hf_lk : VLookup G3 3 (VForallE (VBVar 6) (VBVar 5))).
  { pose proof (VLookupSucc (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0))
                 (VLookupSucc (VBVar 4) (VLookupSucc (VBVar 3) Hlk0))) as H.
    cbn [vlift vliftN vliftVar Nat.ltb Nat.leb] in H. exact H. }
  assert (Ha_lk : VLookup G3 2 (VBVar 6))
    by (exact (VLookupSucc _ Hb1)).
  assert (Hb_lk : VLookup G3 1 (VBVar 6))
    by (exact (VLookupSucc _ Hb0)).
  assert (Hfa : VHasType env U G3 (VApp (VBVar 3) (VBVar 2)) (VBVar 4))
    by (exact (VDF_appDF (@VDF_bvar env U _ _ _ Hf_lk) (@VDF_bvar env U _ _ _ Ha_lk))).
  assert (Hfb : VHasType env U G3 (VApp (VBVar 3) (VBVar 1)) (VBVar 4))
    by (exact (VDF_appDF (@VDF_bvar env U _ _ _ Hf_lk) (@VDF_bvar env U _ _ _ Hb_lk))).
  exact (VHasType_eq_app Heq Hu1 (@VDF_bvar env U _ _ _ Hbeta_lk) Hfa Hfb).
Qed.

(* Constant & DefEq Well-Formedness of Quotient Primitives *)

Lemma VConstantWF_eqConst env :
  VConstantWF env eqConst.
Proof.
  split.
  - eexists. unfold eqConst; simpl.
    assert (Hu0 : vlevel_wf 1 (VLParam 0)) by (simpl; lia).
    eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
    eapply VDF_forallEDF; [apply VDF_bvar; vlk |].
    eapply VDF_forallEDF; [apply VDF_bvar; vlk |].
    apply VHasType_sort; exact I.
  - unfold vclosed, eqConst; cbn; repeat split; lia.
Qed.

Lemma VConstantWF_quotConst env :
  VEnvClosed env ->
  VConstantWF env quotConst.
Proof.
  intros Hcl. split.
  - eexists. unfold quotConst; simpl.
    assert (Hu0 : vlevel_wf 1 (VLParam 0)) by (simpl; lia).
    eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
    eapply VDF_forallEDF.
    + exact (VHasType_vrel_type Hcl (@VDF_bvar env 1 _ _ _ (VLookupZero (VSort (VLParam 0)) []))).
    + apply VHasType_sort; exact Hu0.
  - unfold vclosed, quotConst, vrel_type, vlift; cbn; repeat split; lia.
Qed.

Lemma VConstantWF_quotMkConst env :
  VEnvClosed env ->
  venv_constants env q_name = Some quotConst ->
  VConstantWF env quotMkConst.
Proof.
  intros Hcl Hq. split.
  - eexists. unfold quotMkConst; simpl.
    assert (Hu0 : vlevel_wf 1 (VLParam 0)) by (simpl; lia).
    eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
    eapply VDF_forallEDF.
    + exact (VHasType_vrel_type Hcl (@VDF_bvar env 1 _ _ _ (VLookupZero (VSort (VLParam 0)) []))).
    + eapply VDF_forallEDF; [apply VDF_bvar; vlk |].
      apply VHasType_quot_app;
        [exact Hq | exact Hu0 | apply VDF_bvar; vlk | apply VDF_bvar; vlk].
  - unfold vclosed, quotMkConst, vrel_type, vlift, vquot_app; cbn; repeat split; lia.
Qed.

Lemma VConstantWF_quotLiftConst env :
  VEnvClosed env ->
  venv_constants env q_eq_name = Some eqConst ->
  venv_constants env q_name = Some quotConst ->
  VConstantWF env quotLiftConst.
Proof.
  intros Hcl Heq Hq. split.
  - eexists. unfold quotLiftConst; simpl.
    assert (Hu0 : vlevel_wf 2 (VLParam 0)) by (simpl; lia).
    assert (Hu1 : vlevel_wf 2 (VLParam 1)) by (simpl; lia).
    eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
    eapply VDF_forallEDF.
    + exact (VHasType_vrel_type Hcl (@VDF_bvar env 2 _ _ _ (VLookupZero (VSort (VLParam 0)) []))).
    + eapply VDF_forallEDF; [apply VHasType_sort; exact Hu1 |].
      eapply VDF_forallEDF.
      * eapply VDF_forallEDF; [apply VDF_bvar; vlk | apply VDF_bvar; vlk].
      * eapply VDF_forallEDF.
        -- eapply VHasType_ql_sanity with (u0 := VLParam 0);
             [exact Heq | exact Hu0 | exact Hu1 | vlk | vlk | vlk | vlk].
        -- eapply VDF_forallEDF.
           ++ apply VHasType_quot_app;
                [exact Hq | exact Hu0 | apply VDF_bvar; vlk | apply VDF_bvar; vlk].
           ++ apply VDF_bvar; vlk.
  - unfold vclosed, quotLiftConst, vrel_type, ql_sanity_type, veq_app, vquot_app, vlift;
      cbn; repeat split; lia.
Qed.

Lemma VConstantWF_quotIndConst env :
  VEnvClosed env ->
  venv_constants env q_name = Some quotConst ->
  venv_constants env q_mk_name = Some quotMkConst ->
  VConstantWF env quotIndConst.
Proof.
  intros Hcl Hq Hmk. split.
  - eexists. unfold quotIndConst; simpl.
    assert (Hu0 : vlevel_wf 1 (VLParam 0)) by (simpl; lia).
    eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
    eapply VDF_forallEDF.
    + exact (VHasType_vrel_type Hcl (@VDF_bvar env 1 _ _ _ (VLookupZero (VSort (VLParam 0)) []))).
    + assert (Hq_2 : VHasType env 1 [vrel_type (VBVar 0); VSort (VLParam 0)]
                       (vquot_app (VLParam 0) (VBVar 1) (VBVar 0)) (VSort (VLParam 0))).
      { apply VHasType_quot_app;
          [exact Hq | exact Hu0 | apply VDF_bvar; vlk | apply VDF_bvar; vlk]. }
      eapply VDF_forallEDF.
      * eapply VDF_forallEDF; [exact Hq_2 | apply VHasType_sort; exact I].
      * set (G3 := VForallE (vquot_app (VLParam 0) (VBVar 1) (VBVar 0)) (VSort VLZero)
                   :: vrel_type (VBVar 0) :: VSort (VLParam 0) :: []).
        assert (Hall : VHasType env 1 G3
                         (VForallE (VBVar 2)
                           (VApp (VBVar 1) (vquot_mk_app (VLParam 0) (VBVar 3) (VBVar 2) (VBVar 0))))
                         (VSort (VLIMax (VLParam 0) VLZero))).
        { eapply VDF_forallEDF; [apply VDF_bvar; vlk |].
          set (G4 := VBVar 2 :: G3).
          assert (Hb_lk : VLookup G4 1 (VForallE (vquot_app (VLParam 0) (VBVar 3) (VBVar 2)) (VSort VLZero)))
            by vlk.
          assert (Hmk_app : VHasType env 1 G4
                              (vquot_mk_app (VLParam 0) (VBVar 3) (VBVar 2) (VBVar 0))
                              (vquot_app (VLParam 0) (VBVar 3) (VBVar 2))).
          { apply VHasType_quot_mk_app;
              [exact Hmk | exact Hu0 | apply VDF_bvar; vlk | apply VDF_bvar; vlk | apply VDF_bvar; vlk]. }
          exact (VDF_appDF (@VDF_bvar env 1 _ _ _ Hb_lk) Hmk_app). }
        eapply VDF_forallEDF; [exact Hall |].
        set (G4' := VForallE (VBVar 2)
                      (VApp (VBVar 1) (vquot_mk_app (VLParam 0) (VBVar 3) (VBVar 2) (VBVar 0))) :: G3).
        assert (Hq_4 : VHasType env 1 G4'
                         (vquot_app (VLParam 0) (VBVar 3) (VBVar 2)) (VSort (VLParam 0))).
        { apply VHasType_quot_app;
            [exact Hq | exact Hu0 | apply VDF_bvar; vlk | apply VDF_bvar; vlk]. }
        eapply VDF_forallEDF; [exact Hq_4 |].
        set (G5 := vquot_app (VLParam 0) (VBVar 3) (VBVar 2) :: G4').
        assert (Hb_lk5 : VLookup G5 2 (VForallE (vquot_app (VLParam 0) (VBVar 4) (VBVar 3)) (VSort VLZero)))
          by vlk.
        assert (Hq_lk5 : VLookup G5 0 (vquot_app (VLParam 0) (VBVar 4) (VBVar 3)))
          by vlk.
        exact (VDF_appDF (@VDF_bvar env 1 _ _ _ Hb_lk5) (@VDF_bvar env 1 _ _ _ Hq_lk5)).
  - unfold vclosed, quotIndConst, vrel_type, vquot_app, vquot_mk_app, vlift;
      cbn; repeat split; lia.
Qed.

Lemma VHasType_quot_lift_app env U G u v alpha r beta f c q :
  venv_constants env q_lift_name = Some quotLiftConst ->
  vlevel_wf U u ->
  vlevel_wf U v ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G r (vrel_type alpha) ->
  VHasType env U G beta (VSort v) ->
  VHasType env U G f (VForallE alpha (vlift beta)) ->
  VHasType env U G c
    (VForallE alpha
      (VForallE (vlift alpha)
        (VForallE (VApp (VApp (vliftN 2 0 r) (VBVar 1)) (VBVar 0))
          (veq_app v (vliftN 3 0 beta)
            (VApp (vliftN 3 0 f) (VBVar 2))
            (VApp (vliftN 3 0 f) (VBVar 1)))))) ->
  VHasType env U G q (vquot_app u alpha r) ->
  VHasType env U G (vquot_lift_app u v alpha r beta f c q) beta.
Proof.
  intros Hlift Hu Hv Halpha Hr Hbeta Hf Hc Hq.
  unfold vquot_lift_app.
  assert (Hconst : VHasType env U G (VConst q_lift_name [u; v])
                     (vinstL [u; v] (vc_type quotLiftConst))).
  { apply (@VDF_constDF env U G q_lift_name quotLiftConst [u; v] [u; v] Hlift);
      [constructor; [exact Hu | constructor; [exact Hv | constructor]]
      |constructor; [exact Hu | constructor; [exact Hv | constructor]]
      |reflexivity
      |apply Forall2_vlevel_equiv_refl]. }
  cbn [vc_type quotLiftConst vinstL map vlevel_inst nth vrel_type vlift vliftN vliftVar Nat.ltb Nat.leb Nat.add ql_sanity_type veq_app vquot_app] in Hconst.
  pose proof (VDF_appDF Hconst Halpha) as H1.
  replace (vinst0
    (VForallE (VForallE (VBVar 0) (VForallE (VBVar 1) (VSort VLZero)))
      (VForallE (VSort v)
        (VForallE (VForallE (VBVar 2) (VBVar 1))
          (VForallE
            (VForallE (VBVar 3)
              (VForallE (VBVar 4)
                (VForallE (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0))
                  (VApp (VApp (VApp (VConst q_eq_name [v]) (VBVar 4)) (VApp (VBVar 3) (VBVar 2)))
                        (VApp (VBVar 3) (VBVar 1))))))
            (VForallE (VApp (VApp (VConst q_name [u]) (VBVar 4)) (VBVar 3)) (VBVar 3))))))
    alpha)
    with (VForallE (vrel_type alpha)
           (VForallE (VSort v)
             (VForallE (VForallE (vliftN 2 0 alpha) (VBVar 1))
               (VForallE
                 (VForallE (vliftN 3 0 alpha)
                   (VForallE (vliftN 4 0 alpha)
                     (VForallE (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0))
                       (veq_app v (VBVar 4) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
                 (VForallE (vquot_app u (vliftN 4 0 alpha) (VBVar 3)) (VBVar 3)))))) in H1.
  2: { unfold vinst0, vrel_type, vlift, veq_app, vquot_app;
       cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H1 Hr) as H2.
  replace (vinst0
    (VForallE (VSort v)
      (VForallE (VForallE (vliftN 2 0 alpha) (VBVar 1))
        (VForallE
          (VForallE (vliftN 3 0 alpha)
            (VForallE (vliftN 4 0 alpha)
              (VForallE (VApp (VApp (VBVar 4) (VBVar 1)) (VBVar 0))
                (veq_app v (VBVar 4) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
          (VForallE (vquot_app u (vliftN 4 0 alpha) (VBVar 3)) (VBVar 3)))))
    r)
    with (VForallE (VSort v)
           (VForallE (VForallE (vliftN 1 0 alpha) (VBVar 1))
             (VForallE
               (VForallE (vliftN 2 0 alpha)
                 (VForallE (vliftN 3 0 alpha)
                   (VForallE (VApp (VApp (vliftN 4 0 r) (VBVar 1)) (VBVar 0))
                     (veq_app v (VBVar 4) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
               (VForallE (vquot_app u (vliftN 3 0 alpha) (vliftN 3 0 r)) (VBVar 3))))) in H2.
  2: { unfold vinst0, veq_app, vquot_app; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H2 Hbeta) as H3.
  replace (vinst0
    (VForallE (VForallE (vliftN 1 0 alpha) (VBVar 1))
      (VForallE
        (VForallE (vliftN 2 0 alpha)
          (VForallE (vliftN 3 0 alpha)
            (VForallE (VApp (VApp (vliftN 4 0 r) (VBVar 1)) (VBVar 0))
              (veq_app v (VBVar 4) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
        (VForallE (vquot_app u (vliftN 3 0 alpha) (vliftN 3 0 r)) (VBVar 3))))
    beta)
    with (VForallE (VForallE alpha (vlift beta))
           (VForallE
             (VForallE (vliftN 1 0 alpha)
               (VForallE (vliftN 2 0 alpha)
                 (VForallE (VApp (VApp (vliftN 3 0 r) (VBVar 1)) (VBVar 0))
                   (veq_app v (vliftN 4 0 beta) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
             (VForallE (vquot_app u (vliftN 2 0 alpha) (vliftN 2 0 r)) (vliftN 3 0 beta)))) in H3.
  2: { unfold vinst0, veq_app, vquot_app, vlift; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero, vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H3 Hf) as H4.
  replace (vinst0
    (VForallE
      (VForallE (vliftN 1 0 alpha)
        (VForallE (vliftN 2 0 alpha)
          (VForallE (VApp (VApp (vliftN 3 0 r) (VBVar 1)) (VBVar 0))
            (veq_app v (vliftN 4 0 beta) (VApp (VBVar 3) (VBVar 2)) (VApp (VBVar 3) (VBVar 1))))))
      (VForallE (vquot_app u (vliftN 2 0 alpha) (vliftN 2 0 r)) (vliftN 3 0 beta)))
    f)
    with (VForallE
           (VForallE alpha
             (VForallE (vlift alpha)
               (VForallE (VApp (VApp (vliftN 2 0 r) (VBVar 1)) (VBVar 0))
                 (veq_app v (vliftN 3 0 beta)
                   (VApp (vliftN 3 0 f) (VBVar 2))
                   (VApp (vliftN 3 0 f) (VBVar 1))))))
           (VForallE (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r)) (vliftN 2 0 beta))) in H4.
  2: { unfold vinst0, veq_app, vquot_app, vlift; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero, vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H4 Hc) as H5.
  replace (vinst0 (VForallE (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r)) (vliftN 2 0 beta)) c)
    with (VForallE (vquot_app u alpha r) (vliftN 1 0 beta)) in H5.
  2: { unfold vinst0, vquot_app; cbn [vinst].
       rewrite !vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H5 Hq) as H6.
  replace (vinst0 (vliftN 1 0 beta) q) with beta in H6.
  2: { unfold vinst0. rewrite vinst_vliftN_zero, vliftN_zero. reflexivity. }
  exact H6.
Qed.

Lemma VHasType_quot_ind_app env U G u alpha r beta h q :
  venv_constants env q_ind_name = Some quotIndConst ->
  vlevel_wf U u ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G r (vrel_type alpha) ->
  VHasType env U G beta (VForallE (vquot_app u alpha r) (VSort VLZero)) ->
  VHasType env U G h
    (VForallE alpha
      (VApp (vlift beta) (vquot_mk_app u (vlift alpha) (vlift r) (VBVar 0)))) ->
  VHasType env U G q (vquot_app u alpha r) ->
  VHasType env U G (vquot_ind_app u alpha r beta h q) (VApp beta q).
Proof.
  intros Hind Hu Halpha Hr Hbeta Hh Hq.
  unfold vquot_ind_app.
  assert (Hconst : VHasType env U G (VConst q_ind_name [u])
                     (vinstL [u] (vc_type quotIndConst))).
  { apply (@VDF_constDF env U G q_ind_name quotIndConst [u] [u] Hind);
      [constructor; [exact Hu | constructor]
      |constructor; [exact Hu | constructor]
      |reflexivity
      |apply Forall2_vlevel_equiv_refl]. }
  cbn [vc_type quotIndConst vinstL map vlevel_inst nth vrel_type vlift vliftN vliftVar Nat.ltb Nat.leb Nat.add vquot_app vquot_mk_app] in Hconst.
  pose proof (VDF_appDF Hconst Halpha) as H1.
  replace (vinst0
    (VForallE (VForallE (VBVar 0) (VForallE (VBVar 1) (VSort VLZero)))
      (VForallE (VForallE (VApp (VApp (VConst q_name [u]) (VBVar 1)) (VBVar 0)) (VSort VLZero))
        (VForallE
          (VForallE (VBVar 2)
            (VApp (VBVar 1) (VApp (VApp (VApp (VConst q_mk_name [u]) (VBVar 3)) (VBVar 2)) (VBVar 0))))
          (VForallE (VApp (VApp (VConst q_name [u]) (VBVar 3)) (VBVar 2))
            (VApp (VBVar 2) (VBVar 0))))))
    alpha)
    with (VForallE (vrel_type alpha)
           (VForallE (VForallE (vquot_app u (vliftN 1 0 alpha) (VBVar 0)) (VSort VLZero))
             (VForallE
               (VForallE (vliftN 2 0 alpha)
                 (VApp (VBVar 1) (vquot_mk_app u (vliftN 3 0 alpha) (VBVar 2) (VBVar 0))))
               (VForallE (vquot_app u (vliftN 3 0 alpha) (VBVar 2))
                 (VApp (VBVar 2) (VBVar 0)))))) in H1.
  2: { unfold vinst0, vrel_type, vlift, vquot_app, vquot_mk_app;
       cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H1 Hr) as H2.
  replace (vinst0
    (VForallE (VForallE (vquot_app u (vliftN 1 0 alpha) (VBVar 0)) (VSort VLZero))
      (VForallE
        (VForallE (vliftN 2 0 alpha)
          (VApp (VBVar 1) (vquot_mk_app u (vliftN 3 0 alpha) (VBVar 2) (VBVar 0))))
        (VForallE (vquot_app u (vliftN 3 0 alpha) (VBVar 2))
          (VApp (VBVar 2) (VBVar 0)))))
    r)
    with (VForallE (VForallE (vquot_app u alpha r) (VSort VLZero))
           (VForallE
             (VForallE (vliftN 1 0 alpha)
               (VApp (VBVar 1) (vquot_mk_app u (vliftN 2 0 alpha) (vliftN 2 0 r) (VBVar 0))))
             (VForallE (vquot_app u (vliftN 2 0 alpha) (vliftN 2 0 r))
               (VApp (VBVar 2) (VBVar 0))))) in H2.
  2: { unfold vinst0, vquot_app, vquot_mk_app; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H2 Hbeta) as H3.
  replace (vinst0
    (VForallE
      (VForallE (vliftN 1 0 alpha)
        (VApp (VBVar 1) (vquot_mk_app u (vliftN 2 0 alpha) (vliftN 2 0 r) (VBVar 0))))
      (VForallE (vquot_app u (vliftN 2 0 alpha) (vliftN 2 0 r))
        (VApp (VBVar 2) (VBVar 0))))
    beta)
    with (VForallE
           (VForallE alpha
             (VApp (vlift beta) (vquot_mk_app u (vlift alpha) (vlift r) (VBVar 0))))
           (VForallE (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r))
             (VApp (vliftN 2 0 beta) (VBVar 0)))) in H3.
  2: { unfold vinst0, vquot_app, vquot_mk_app, vlift; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero, vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H3 Hh) as H4.
  replace (vinst0 (VForallE (vquot_app u (vliftN 1 0 alpha) (vliftN 1 0 r))
                    (VApp (vliftN 2 0 beta) (VBVar 0))) h)
    with (VForallE (vquot_app u alpha r) (VApp (vliftN 1 0 beta) (VBVar 0))) in H4.
  2: { unfold vinst0, vquot_app; cbn [vinst].
       rewrite !vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  pose proof (VDF_appDF H4 Hq) as H5.
  replace (vinst0 (VApp (vliftN 1 0 beta) (VBVar 0)) q) with (VApp beta q) in H5.
  2: { unfold vinst0; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  exact H5.
Qed.

Lemma VDefEqWF_quotDefEq env :
  VEnvClosed env ->
  venv_constants env q_eq_name = Some eqConst ->
  venv_constants env q_name = Some quotConst ->
  venv_constants env q_mk_name = Some quotMkConst ->
  venv_constants env q_lift_name = Some quotLiftConst ->
  VDefEqWF env quotDefEq.
Proof.
  intros Hcl Heq Hq Hmk Hlift.
  assert (Hu0 : vlevel_wf 2 (VLParam 0)) by (simpl; lia).
  assert (Hu1 : vlevel_wf 2 (VLParam 1)) by (simpl; lia).
  set (A0 := VSort (VLParam 0)).
  set (A1 := vrel_type (VBVar 0)).
  set (A2 := VSort (VLParam 1)).
  set (A3 := VForallE (VBVar 2) (VBVar 1)).
  set (A4 := ql_sanity_type (VLParam 1)).
  set (A5 := VBVar 4).
  assert (HA0 : VHasType env 2 [] A0 (VSort (VLSucc (VLParam 0))))
    by (apply VHasType_sort; exact Hu0).
  assert (HA1 : VHasType env 2 [A0] A1
                  (VSort (VLIMax (VLParam 0) (VLIMax (VLParam 0) (VLSucc VLZero)))))
    by (exact (VHasType_vrel_type Hcl (@VDF_bvar env 2 _ _ _ (VLookupZero A0 [])))).
  assert (HA2 : VHasType env 2 [A1; A0] A2 (VSort (VLSucc (VLParam 1))))
    by (apply VHasType_sort; exact Hu1).
  assert (HA3 : VHasType env 2 [A2; A1; A0] A3 (VSort (VLIMax (VLParam 0) (VLParam 1)))).
  { unfold A3, A2, A1, A0; eapply VDF_forallEDF; [apply VDF_bvar; vlk | apply VDF_bvar; vlk]. }
  assert (HA4 : VHasType env 2 [A3; A2; A1; A0] A4
                  (VSort (VLIMax (VLParam 0) (VLIMax (VLParam 0) (VLIMax VLZero VLZero))))).
  { unfold A4, A3, A2, A1, A0;
    eapply VHasType_ql_sanity with (u0 := VLParam 0);
      [exact Heq | exact Hu0 | exact Hu1 | vlk | vlk | vlk | vlk]. }
  assert (HA5 : VHasType env 2 [A4; A3; A2; A1; A0] A5 (VSort (VLParam 0)))
    by (unfold A5, A4, A3, A2, A1, A0; apply VDF_bvar; vlk).
  set (G6 := [A5; A4; A3; A2; A1; A0]).
  assert (Hv5 : VHasType env 2 G6 (VBVar 5) (VSort (VLParam 0)))
    by (unfold G6, A5, A4, A3, A2, A1, A0; apply VDF_bvar; vlk).
  assert (Hv4 : VHasType env 2 G6 (VBVar 4) (vrel_type (VBVar 5)))
    by (unfold G6, A5, A4, A3, A2, A1, A0, vrel_type, vlift; apply VDF_bvar; vlk).
  assert (Hv3 : VHasType env 2 G6 (VBVar 3) (VSort (VLParam 1)))
    by (unfold G6, A5, A4, A3, A2, A1, A0; apply VDF_bvar; vlk).
  assert (Hv2 : VHasType env 2 G6 (VBVar 2) (VForallE (VBVar 5) (vlift (VBVar 3))))
    by (unfold G6, A5, A4, A3, A2, A1, A0, vlift; apply VDF_bvar; vlk).
  assert (Hv1 : VHasType env 2 G6 (VBVar 1)
                  (VForallE (VBVar 5)
                    (VForallE (vlift (VBVar 5))
                      (VForallE (VApp (VApp (vliftN 2 0 (VBVar 4)) (VBVar 1)) (VBVar 0))
                        (veq_app (VLParam 1) (vliftN 3 0 (VBVar 3))
                          (VApp (vliftN 3 0 (VBVar 2)) (VBVar 2))
                          (VApp (vliftN 3 0 (VBVar 2)) (VBVar 1))))))).
  { unfold G6, A5, A4, A3, A2, A1, A0, ql_sanity_type, veq_app, vlift;
    cbn [vliftN vliftVar Nat.ltb Nat.leb]; apply VDF_bvar; vlk. }
  assert (Hv0 : VHasType env 2 G6 (VBVar 0) (VBVar 5))
    by (unfold G6, A5, A4, A3, A2, A1, A0; apply VDF_bvar; vlk).
  assert (Hmk_g6 : VHasType env 2 G6
                     (vquot_mk_app (VLParam 0) (VBVar 5) (VBVar 4) (VBVar 0))
                     (vquot_app (VLParam 0) (VBVar 5) (VBVar 4)))
    by (exact (VHasType_quot_mk_app Hmk Hu0 Hv5 Hv4 Hv0)).
  assert (Hlhs_body : VHasType env 2 G6
                        (vquot_lift_app (VLParam 0) (VLParam 1)
                          (VBVar 5) (VBVar 4) (VBVar 3) (VBVar 2) (VBVar 1)
                          (vquot_mk_app (VLParam 0) (VBVar 5) (VBVar 4) (VBVar 0)))
                        (VBVar 3))
    by (exact (VHasType_quot_lift_app Hlift Hu0 Hu1 Hv5 Hv4 Hv3 Hv2 Hv1 Hmk_g6)).
  assert (Hrhs_body : VHasType env 2 G6 (VApp (VBVar 2) (VBVar 0)) (VBVar 3)).
  { pose proof (VDF_appDF Hv2 Hv0) as Happ.
    cbn [vinst0 vinst vinstVar Nat.ltb Nat.leb Nat.eqb vlift vliftN vliftVar] in Happ.
    exact Happ. }
  split; [|split].
  - unfold quotDefEq; simpl.
    eapply VDF_lamDF; [exact HA0 |].
    eapply VDF_lamDF; [exact HA1 |].
    eapply VDF_lamDF; [exact HA2 |].
    eapply VDF_lamDF; [exact HA3 |].
    eapply VDF_lamDF; [exact HA4 |].
    eapply VDF_lamDF; [exact HA5 | exact Hlhs_body].
  - unfold quotDefEq; simpl.
    eapply VDF_lamDF; [exact HA0 |].
    eapply VDF_lamDF; [exact HA1 |].
    eapply VDF_lamDF; [exact HA2 |].
    eapply VDF_lamDF; [exact HA3 |].
    eapply VDF_lamDF; [exact HA4 |].
    eapply VDF_lamDF; [exact HA5 | exact Hrhs_body].
  - unfold quotDefEq, vclosed, vrel_type, ql_sanity_type, veq_app,
      vquot_lift_app, vquot_mk_app, vlift;
      cbn; repeat split; lia.
Qed.

(* Structural lookup & monotonicity lemmas for venv_add_quot *)

Lemma addQuot_decomp env env' :
  venv_add_quot env = Some env' ->
  exists env1 env2 env3 env4,
    venv_add_const env q_name quotConst = Some env1 /\
    venv_add_const env1 q_mk_name quotMkConst = Some env2 /\
    venv_add_const env2 q_lift_name quotLiftConst = Some env3 /\
    venv_add_const env3 q_ind_name quotIndConst = Some env4 /\
    env' = venv_add_defeq env4 quotDefEq.
Proof.
  unfold venv_add_quot.
  destruct (venv_add_const env q_name quotConst) as [env1|] eqn:H1; [|discriminate].
  destruct (venv_add_const env1 q_mk_name quotMkConst) as [env2|] eqn:H2; [|discriminate].
  destruct (venv_add_const env2 q_lift_name quotLiftConst) as [env3|] eqn:H3; [|discriminate].
  destruct (venv_add_const env3 q_ind_name quotIndConst) as [env4|] eqn:H4; [|discriminate].
  intros H; inversion H; subst.
  exists env1, env2, env3, env4. auto.
Qed.

Theorem addQuot_ordered env env' :
  venv_add_quot env = Some env' -> venv_ordered env env'.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 ->]]]]]]]].
  eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H1) |].
  eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H2) |].
  eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H3) |].
  eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H4) |].
  apply venv_add_defeq_ordered.
Qed.

Theorem addQuot_quot env env' :
  venv_add_quot env = Some env' -> venv_constants env' q_name = Some quotConst.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 ->]]]]]]]].
  assert (Ho1 : venv_ordered e1 (venv_add_defeq e4 quotDefEq)).
  { eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H2) |].
    eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H3) |].
    eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H4) |].
    apply venv_add_defeq_ordered. }
  exact (venv_ord_const Ho1 (venv_add_const_lookup_self _ _ _ H1)).
Qed.

Theorem addQuot_quotMk env env' :
  venv_add_quot env = Some env' -> venv_constants env' q_mk_name = Some quotMkConst.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [_ [H2 [H3 [H4 ->]]]]]]]].
  assert (Ho2 : venv_ordered e2 (venv_add_defeq e4 quotDefEq)).
  { eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H3) |].
    eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H4) |].
    apply venv_add_defeq_ordered. }
  exact (venv_ord_const Ho2 (venv_add_const_lookup_self _ _ _ H2)).
Qed.

Theorem addQuot_quotLift env env' :
  venv_add_quot env = Some env' -> venv_constants env' q_lift_name = Some quotLiftConst.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [_ [_ [H3 [H4 ->]]]]]]]].
  assert (Ho3 : venv_ordered e3 (venv_add_defeq e4 quotDefEq)).
  { eapply venv_ordered_trans; [exact (venv_add_const_ordered _ _ _ H4) |].
    apply venv_add_defeq_ordered. }
  exact (venv_ord_const Ho3 (venv_add_const_lookup_self _ _ _ H3)).
Qed.

Theorem addQuot_quotInd env env' :
  venv_add_quot env = Some env' -> venv_constants env' q_ind_name = Some quotIndConst.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [_ [_ [_ [H4 ->]]]]]]]].
  exact (venv_add_const_lookup_self _ _ _ H4).
Qed.

Theorem addQuot_defeq env env' :
  venv_add_quot env = Some env' -> venv_defeqs env' quotDefEq.
Proof.
  intros Hadd.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [_ [_ [_ [_ ->]]]]]]]].
  simpl. left. reflexivity.
Qed.

Theorem exists_addQuot env :
  venv_constants env q_name = None ->
  venv_constants env q_mk_name = None ->
  venv_constants env q_lift_name = None ->
  venv_constants env q_ind_name = None ->
  exists env', venv_add_quot env = Some env'.
Proof.
  intros Hq Hmk Hlift Hind.
  unfold venv_add_quot.
  destruct (venv_add_const_eq_none quotConst Hq) as [e1 H1]. rewrite H1.
  assert (Hmk1 : venv_constants e1 q_mk_name = None)
    by (rewrite (venv_add_const_lookup_other (m := q_mk_name) H1 ltac:(discriminate)); exact Hmk).
  destruct (venv_add_const_eq_none quotMkConst Hmk1) as [e2 H2]. rewrite H2.
  assert (Hlift2 : venv_constants e2 q_lift_name = None).
  { rewrite (venv_add_const_lookup_other (m := q_lift_name) H2 ltac:(discriminate)).
    rewrite (venv_add_const_lookup_other (m := q_lift_name) H1 ltac:(discriminate)).
    exact Hlift. }
  destruct (venv_add_const_eq_none quotLiftConst Hlift2) as [e3 H3]. rewrite H3.
  assert (Hind3 : venv_constants e3 q_ind_name = None).
  { rewrite (venv_add_const_lookup_other (m := q_ind_name) H3 ltac:(discriminate)).
    rewrite (venv_add_const_lookup_other (m := q_ind_name) H2 ltac:(discriminate)).
    rewrite (venv_add_const_lookup_other (m := q_ind_name) H1 ltac:(discriminate)).
    exact Hind. }
  destruct (venv_add_const_eq_none quotIndConst Hind3) as [e4 H4]. rewrite H4.
  eexists. reflexivity.
Qed.

Theorem addQuot_WF env env' :
  VEnvWF env ->
  VQuotReady env ->
  venv_add_quot env = Some env' ->
  VEnvWF env' /\ venv_ordered env env'.
Proof.
  intros Hwf Hqr Hadd.
  pose proof (addQuot_ordered Hadd) as Hord_all.
  destruct (addQuot_decomp Hadd) as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 ->]]]]]]]].
  pose proof (venv_add_const_ordered _ _ _ H1) as Ho1.
  pose proof (venv_add_const_ordered _ _ _ H2) as Ho2.
  pose proof (venv_add_const_ordered _ _ _ H3) as Ho3.
  pose proof (venv_add_const_ordered _ _ _ H4) as Ho4.
  assert (Hwf1 : VEnvWF e1)
    by (eapply VEnvWF_add_const; [exact Hwf | exact (VConstantWF_quotConst (VEnvWF_closed Hwf)) | exact H1]).
  assert (Hq1 : venv_constants e1 q_name = Some quotConst)
    by (exact (venv_add_const_lookup_self _ _ _ H1)).
  assert (Hwf2 : VEnvWF e2)
    by (eapply VEnvWF_add_const; [exact Hwf1 | exact (VConstantWF_quotMkConst (VEnvWF_closed Hwf1) Hq1) | exact H2]).
  assert (Heq2 : venv_constants e2 q_eq_name = Some eqConst)
    by (exact (venv_ord_const Ho2 (venv_ord_const Ho1 Hqr))).
  assert (Hq2 : venv_constants e2 q_name = Some quotConst)
    by (exact (venv_ord_const Ho2 Hq1)).
  assert (Hmk2 : venv_constants e2 q_mk_name = Some quotMkConst)
    by (exact (venv_add_const_lookup_self _ _ _ H2)).
  assert (Hwf3 : VEnvWF e3)
    by (eapply VEnvWF_add_const; [exact Hwf2 | exact (VConstantWF_quotLiftConst (VEnvWF_closed Hwf2) Heq2 Hq2) | exact H3]).
  assert (Hq3 : venv_constants e3 q_name = Some quotConst)
    by (exact (venv_ord_const Ho3 Hq2)).
  assert (Hmk3 : venv_constants e3 q_mk_name = Some quotMkConst)
    by (exact (venv_ord_const Ho3 Hmk2)).
  assert (Hwf4 : VEnvWF e4)
    by (eapply VEnvWF_add_const; [exact Hwf3 | exact (VConstantWF_quotIndConst (VEnvWF_closed Hwf3) Hq3 Hmk3) | exact H4]).
  assert (Heq4 : venv_constants e4 q_eq_name = Some eqConst)
    by (exact (venv_ord_const Ho4 (venv_ord_const Ho3 Heq2))).
  assert (Hq4 : venv_constants e4 q_name = Some quotConst)
    by (exact (venv_ord_const Ho4 Hq3)).
  assert (Hmk4 : venv_constants e4 q_mk_name = Some quotMkConst)
    by (exact (venv_ord_const Ho4 Hmk3)).
  assert (Hlift4 : venv_constants e4 q_lift_name = Some quotLiftConst)
    by (exact (venv_ord_const Ho4 (venv_add_const_lookup_self _ _ _ H3))).
  split; [|exact Hord_all].
  apply VEnvWF_add_defeq; [exact Hwf4 |].
  exact (VDefEqWF_quotDefEq (VEnvWF_closed Hwf4) Heq4 Hq4 Hmk4 Hlift4).
Qed.

(* Quot.ind computation rule holds automatically via proof irrelevance! *)
Theorem quotInd_iota_defeq env U G u alpha r beta h a :
  venv_constants env q_mk_name = Some quotMkConst ->
  venv_constants env q_ind_name = Some quotIndConst ->
  vlevel_wf U u ->
  VHasType env U G alpha (VSort u) ->
  VHasType env U G r (vrel_type alpha) ->
  VHasType env U G beta (VForallE (vquot_app u alpha r) (VSort VLZero)) ->
  VHasType env U G h
    (VForallE alpha
      (VApp (vlift beta) (vquot_mk_app u (vlift alpha) (vlift r) (VBVar 0)))) ->
  VHasType env U G a alpha ->
  VIsDefEq env U G
    (vquot_ind_app u alpha r beta h (vquot_mk_app u alpha r a))
    (VApp h a)
    (VApp beta (vquot_mk_app u alpha r a)).
Proof.
  intros Hmk Hind Hu Halpha Hr Hbeta Hh Ha.
  pose proof (VHasType_quot_mk_app Hmk Hu Halpha Hr Ha) as Hmk_a.
  pose proof (VDF_appDF Hbeta Hmk_a) as Hprop.
  cbn [vinst0 vinst] in Hprop.
  pose proof (VHasType_quot_ind_app Hind Hu Halpha Hr Hbeta Hh Hmk_a) as Hlhs.
  pose proof (VDF_appDF Hh Ha) as Hrhs.
  replace (vinst0 (VApp (vlift beta) (vquot_mk_app u (vlift alpha) (vlift r) (VBVar 0))) a)
    with (VApp beta (vquot_mk_app u alpha r a)) in Hrhs.
  2: { unfold vinst0, vlift, vquot_mk_app; cbn [vinst vinstVar Nat.ltb Nat.leb Nat.eqb].
       rewrite !vinst_vliftN_zero, !vliftN_zero. reflexivity. }
  exact (VDF_proofIrrel Hprop Hlhs Hrhs).
Qed.

Corollary addQuot_quotInd_iota env env' U G u alpha r beta h a :
  venv_add_quot env = Some env' ->
  vlevel_wf U u ->
  VHasType env' U G alpha (VSort u) ->
  VHasType env' U G r (vrel_type alpha) ->
  VHasType env' U G beta (VForallE (vquot_app u alpha r) (VSort VLZero)) ->
  VHasType env' U G h
    (VForallE alpha
      (VApp (vlift beta) (vquot_mk_app u (vlift alpha) (vlift r) (VBVar 0)))) ->
  VHasType env' U G a alpha ->
  VIsDefEq env' U G
    (vquot_ind_app u alpha r beta h (vquot_mk_app u alpha r a))
    (VApp h a)
    (VApp beta (vquot_mk_app u alpha r a)).
Proof.
  intros Hadd.
  exact (quotInd_iota_defeq (addQuot_quotMk Hadd) (addQuot_quotInd Hadd)).
Qed.

(* ========================================================================= *)
(* 4. Multi-Constant & Multi-DefEq Combinators (Env.lean & EnvLemmas.lean)   *)
(* ========================================================================= *)

Definition VDefValWF (env : VEnv) (dv : VDefVal) : Prop :=
  VHasType env (vdv_uvars dv) [] (vdv_value dv) (vdv_type dv).

Lemma VDefValWF_mono env1 env2 dv :
  venv_ordered env1 env2 -> VDefValWF env1 dv -> VDefValWF env2 dv.
Proof. apply VEnvOrdered_preserve_VHasType. Qed.

Lemma VDefValWF_to_VConstantWF env dv :
  VEnvWF env -> VDefValWF env dv -> VConstantWF env (vdv_to_constant dv).
Proof.
  intros Hwf Hdv. split.
  - exact (VIsDefEq_isType Hwf (I : VCtxWF env _ []) Hdv).
  - destruct (VIsDefEq_closedN (VEnvWF_closed Hwf) Hdv (I : VCtxClosed [])) as [_ [_ Hty]].
    exact Hty.
Qed.

Lemma VDefValWF_to_VDefEqWF env dv :
  VEnvWF env ->
  venv_constants env (vdv_name dv) = Some (vdv_to_constant dv) ->
  VDefValWF env dv ->
  VDefEqWF env (vdef_to_defeq dv).
Proof.
  intros Hwf Hc Hdv.
  destruct (VIsDefEq_closedN (VEnvWF_closed Hwf) Hdv (I : VCtxClosed [])) as [Hval [_ Hty]].
  split; [|split].
  - unfold vdef_to_defeq; simpl.
    exact (VHasType_const0 Hwf Hc).
  - unfold vdef_to_defeq; simpl. exact Hdv.
  - unfold vdef_to_defeq, vclosed; simpl. auto.
Qed.

Fixpoint venv_add_const_vals (env : VEnv) (cvs : list VConstVal) : option VEnv :=
  match cvs with
  | [] => Some env
  | cv :: rest =>
    match venv_add_const env (vcv_name cv) (vcv_const cv) with
    | None => None
    | Some env1 => venv_add_const_vals env1 rest
    end
  end.

Definition venv_add_consts (env : VEnv) (cis : list VDefVal) : option VEnv :=
  venv_add_const_vals env (map vdv_const cis).

Fixpoint venv_add_raw_defeqs (env : VEnv) (dfs : list VDefEq) : VEnv :=
  match dfs with
  | [] => env
  | df :: rest => venv_add_raw_defeqs (venv_add_defeq env df) rest
  end.

Definition venv_add_defeqs (env : VEnv) (cis : list VDefVal) : VEnv :=
  venv_add_raw_defeqs env (map vdef_to_defeq cis).

Theorem venv_add_const_vals_ordered env cvs env' :
  venv_add_const_vals env cvs = Some env' ->
  venv_ordered env env'.
Proof.
  revert env env'.
  induction cvs as [|cv rest IH]; simpl; intros env env' Hadd.
  - inversion Hadd; subst. apply venv_ordered_refl.
  - destruct (venv_add_const env (vcv_name cv) (vcv_const cv)) as [env1|] eqn:H1; [|discriminate].
    exact (venv_ordered_trans (venv_add_const_ordered _ _ _ H1) (IH _ _ Hadd)).
Qed.

Theorem venv_add_const_vals_wf env cvs env' :
  VEnvWF env ->
  (forall cv, In cv cvs -> VConstantWF env (vcv_const cv)) ->
  venv_add_const_vals env cvs = Some env' ->
  VEnvWF env' /\ venv_ordered env env'.
Proof.
  intros Hwf Hall Hadd.
  split; [|exact (venv_add_const_vals_ordered Hadd)].
  revert env Hwf Hall Hadd.
  induction cvs as [|cv rest IH]; simpl; intros env Hwf Hall Hadd.
  - inversion Hadd; subst. exact Hwf.
  - destruct (venv_add_const env (vcv_name cv) (vcv_const cv)) as [env1|] eqn:H1; [|discriminate].
    pose proof (venv_add_const_ordered _ _ _ H1) as Ho1.
    assert (Hwf1 : VEnvWF env1)
      by (eapply VEnvWF_add_const; [exact Hwf | exact (Hall cv (or_introl eq_refl)) | exact H1]).
    apply (IH env1 Hwf1); [|exact Hadd].
    intros c Hc. exact (VConstantWF_mono Ho1 (Hall c (or_intror Hc))).
Qed.

Theorem venv_add_const_vals_constants env cvs env' :
  venv_add_const_vals env cvs = Some env' ->
  forall cv, In cv cvs -> venv_constants env' (vcv_name cv) = Some (vcv_const cv).
Proof.
  revert env env'.
  induction cvs as [|cv0 rest IH]; simpl; intros env env' Hadd cv Hmem.
  - contradiction.
  - destruct (venv_add_const env (vcv_name cv0) (vcv_const cv0)) as [env1|] eqn:H1; [|discriminate].
    destruct Hmem as [-> | Hmem].
    + exact (venv_ord_const (venv_add_const_vals_ordered Hadd)
               (venv_add_const_lookup_self _ _ _ H1)).
    + exact (IH _ _ Hadd cv Hmem).
Qed.

Theorem exists_addConstVals env cvs :
  (forall cv, In cv cvs -> venv_constants env (vcv_name cv) = None) ->
  NoDup (map vcv_name cvs) ->
  exists env', venv_add_const_vals env cvs = Some env'.
Proof.
  revert env.
  induction cvs as [|cv rest IH]; simpl; intros env Hfresh Hnd.
  - exists env. reflexivity.
  - inversion Hnd as [|x xs Hnin Hnd']; subst.
    destruct (venv_add_const_eq_none (vcv_const cv) (Hfresh cv (or_introl eq_refl))) as [env1 H1].
    rewrite H1. apply IH; [|exact Hnd'].
    intros c Hc.
    rewrite (venv_add_const_constants_eq (vcv_name c) H1).
    destruct (name_eqb (vcv_name c) (vcv_name cv)) eqn:Heq.
    + apply name_eqb_eq in Heq. exfalso. apply Hnin.
      rewrite <- Heq. apply in_map. exact Hc.
    + exact (Hfresh c (or_intror Hc)).
Qed.

(* Specializations to list VDefVal matching upstream EnvLemmas.lean *)

Theorem venv_add_consts_ordered env cis env' :
  venv_add_consts env cis = Some env' ->
  venv_ordered env env'.
Proof.
  unfold venv_add_consts. apply venv_add_const_vals_ordered.
Qed.

Theorem venv_add_consts_wf env cis env' :
  VEnvWF env ->
  (forall ci, In ci cis -> VConstantWF env (vdv_to_constant ci)) ->
  venv_add_consts env cis = Some env' ->
  VEnvWF env' /\ venv_ordered env env'.
Proof.
  intros Hwf Hall Hadd.
  eapply (venv_add_const_vals_wf Hwf); [|exact Hadd].
  intros cv Hcv. apply in_map_iff in Hcv as [ci [<- Hci]].
  exact (Hall ci Hci).
Qed.

Theorem venv_add_consts_constants env cis env' :
  venv_add_consts env cis = Some env' ->
  forall ci, In ci cis -> venv_constants env' (vdv_name ci) = Some (vdv_to_constant ci).
Proof.
  intros Hadd ci Hci.
  exact (venv_add_const_vals_constants Hadd (in_map vdv_const cis ci Hci)).
Qed.

Theorem venv_add_consts_congr env cis cis' :
  Forall2 (fun a b => vdv_const a = vdv_const b) cis cis' ->
  venv_add_consts env cis = venv_add_consts env cis'.
Proof.
  intros H. unfold venv_add_consts.
  f_equal. induction H; simpl; congruence.
Qed.

Theorem exists_addConsts env cis :
  (forall ci, In ci cis -> venv_constants env (vdv_name ci) = None) ->
  NoDup (map vdv_name cis) ->
  exists env', venv_add_consts env cis = Some env'.
Proof.
  intros Hfresh Hnd.
  unfold venv_add_consts. apply exists_addConstVals.
  - intros cv Hcv. apply in_map_iff in Hcv as [ci [<- Hci]]. exact (Hfresh ci Hci).
  - rewrite map_map. exact Hnd.
Qed.

(* Multi-defeq lemmas *)

Theorem venv_add_raw_defeqs_ordered env dfs :
  venv_ordered env (venv_add_raw_defeqs env dfs).
Proof.
  revert env.
  induction dfs as [|df rest IH]; simpl; intros env.
  - apply venv_ordered_refl.
  - exact (venv_ordered_trans (venv_add_defeq_ordered env df) (IH _)).
Qed.

Theorem venv_add_raw_defeqs_mem env dfs df :
  In df dfs -> venv_defeqs (venv_add_raw_defeqs env dfs) df.
Proof.
  revert env.
  induction dfs as [|df0 rest IH]; simpl; intros env Hmem; [contradiction |].
  destruct Hmem as [-> | Hmem].
  - apply (venv_ord_defeq (venv_add_raw_defeqs_ordered (venv_add_defeq env df) rest)).
    simpl. left. reflexivity.
  - exact (IH _ Hmem).
Qed.

Theorem venv_add_raw_defeqs_wf env dfs :
  VEnvWF env ->
  (forall df, In df dfs -> VDefEqWF env df) ->
  VEnvWF (venv_add_raw_defeqs env dfs) /\ venv_ordered env (venv_add_raw_defeqs env dfs).
Proof.
  intros Hwf Hall.
  split; [|apply venv_add_raw_defeqs_ordered].
  revert env Hwf Hall.
  induction dfs as [|df rest IH]; simpl; intros env Hwf Hall; [exact Hwf |].
  pose proof (venv_add_defeq_ordered env df) as Ho.
  assert (Hwf1 : VEnvWF (venv_add_defeq env df))
    by (apply VEnvWF_add_defeq; [exact Hwf | exact (Hall df (or_introl eq_refl))]).
  apply (IH _ Hwf1).
  intros d Hd. exact (VDefEqWF_mono Ho (Hall d (or_intror Hd))).
Qed.

Theorem venv_add_defeqs_ordered env cis :
  venv_ordered env (venv_add_defeqs env cis).
Proof.
  unfold venv_add_defeqs. apply venv_add_raw_defeqs_ordered.
Qed.

Theorem venv_add_defeqs_wf env cis :
  VEnvWF env ->
  (forall ci, In ci cis -> venv_constants env (vdv_name ci) = Some (vdv_to_constant ci)) ->
  (forall ci, In ci cis -> VDefValWF env ci) ->
  VEnvWF (venv_add_defeqs env cis) /\ venv_ordered env (venv_add_defeqs env cis).
Proof.
  intros Hwf Hmem Hval.
  unfold venv_add_defeqs.
  eapply (venv_add_raw_defeqs_wf Hwf).
  intros df Hdf. apply in_map_iff in Hdf as [ci [<- Hci]].
  exact (VDefValWF_to_VDefEqWF Hwf (Hmem ci Hci) (Hval ci Hci)).
Qed.

(* ========================================================================= *)
(* 5. Constructive Semantic Inductives (Inductive.lean & InductiveLemmas)    *)
(* ========================================================================= *)

Definition ind_type_consts (decl : VInductDecl) : list VConstVal :=
  map vit_const (vid_types decl).

Definition ind_ctor_consts (decl : VInductDecl) : list VConstVal :=
  flat_map vit_ctors (vid_types decl).

Definition ind_all_consts (decl : VInductDecl) : list VConstVal :=
  ind_type_consts decl ++ ind_ctor_consts decl ++ vid_recs decl.

Definition venv_add_induct (env : VEnv) (decl : VInductDecl) : option VEnv :=
  match venv_add_const_vals env (ind_type_consts decl) with
  | None => None
  | Some env1 =>
    match venv_add_const_vals env1 (ind_ctor_consts decl) with
    | None => None
    | Some env2 =>
      match venv_add_const_vals env2 (vid_recs decl) with
      | None => None
      | Some env3 => Some (venv_add_raw_defeqs env3 (vid_iotas decl))
      end
    end
  end.

Record VInductDeclWF (env : VEnv) (decl : VInductDecl) : Prop := {
  vid_wf_fresh :
    forall cv, In cv (ind_all_consts decl) -> venv_constants env (vcv_name cv) = None;
  vid_wf_nodup :
    NoDup (map vcv_name (ind_all_consts decl));
  vid_wf_uvars :
    forall cv, In cv (ind_type_consts decl ++ ind_ctor_consts decl) ->
      vcv_uvars cv = vid_uvars decl;
  vid_wf_types :
    forall cv, In cv (ind_type_consts decl) -> VConstantWF env (vcv_const cv);
  vid_wf_ctors :
    forall env1,
      venv_add_const_vals env (ind_type_consts decl) = Some env1 ->
      forall cv, In cv (ind_ctor_consts decl) -> VConstantWF env1 (vcv_const cv);
  vid_wf_recs :
    forall env1 env2,
      venv_add_const_vals env (ind_type_consts decl) = Some env1 ->
      venv_add_const_vals env1 (ind_ctor_consts decl) = Some env2 ->
      forall cv, In cv (vid_recs decl) -> VConstantWF env2 (vcv_const cv);
  vid_wf_iotas :
    forall env1 env2 env3,
      venv_add_const_vals env (ind_type_consts decl) = Some env1 ->
      venv_add_const_vals env1 (ind_ctor_consts decl) = Some env2 ->
      venv_add_const_vals env2 (vid_recs decl) = Some env3 ->
      forall df, In df (vid_iotas decl) -> VDefEqWF env3 df
}.

Lemma venv_add_const_vals_lookup_none env cvs env' m :
  venv_add_const_vals env cvs = Some env' ->
  ~ In m (map vcv_name cvs) ->
  venv_constants env' m = venv_constants env m.
Proof.
  revert env env'.
  induction cvs as [|cv rest IH]; simpl; intros env env' Hadd Hnin.
  - inversion Hadd; subst. reflexivity.
  - destruct (venv_add_const env (vcv_name cv) (vcv_const cv)) as [env1|] eqn:H1; [|discriminate].
    rewrite (IH _ _ Hadd ltac:(tauto)).
    exact (venv_add_const_lookup_other (m := m) H1 (fun Heq => Hnin (or_introl (eq_sym Heq)))).
Qed.

Lemma NoDup_app_split (A : Type) (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros Hnd.
  - repeat split; [constructor | exact Hnd | tauto].
  - inversion Hnd as [|x xs Hnin Hnd']; subst.
    rewrite in_app_iff in Hnin.
    destruct (IH Hnd') as [H1 [H2 Hdisj]].
    repeat split.
    + constructor; [tauto | exact H1].
    + exact H2.
    + intros y [<- | Hy]; [tauto | exact (Hdisj y Hy)].
Qed.

Theorem exists_addInduct env decl :
  VInductDeclWF env decl ->
  exists env', venv_add_induct env decl = Some env'.
Proof.
  intros Hdecl.
  pose proof (vid_wf_nodup Hdecl) as Hnd.
  unfold ind_all_consts in Hnd.
  rewrite !map_app in Hnd.
  destruct (NoDup_app_split Hnd) as [Hnd_t [Hnd_cr Hdisj_t]].
  destruct (NoDup_app_split Hnd_cr) as [Hnd_c [Hnd_r Hdisj_c]].
  unfold venv_add_induct.
  destruct (exists_addConstVals (cvs := ind_type_consts decl) (env := env)) as [env1 H1].
  - intros cv Hcv. apply (vid_wf_fresh Hdecl). unfold ind_all_consts. apply in_or_app; left; exact Hcv.
  - exact Hnd_t.
  - rewrite H1.
    destruct (exists_addConstVals (cvs := ind_ctor_consts decl) (env := env1)) as [env2 H2].
    + intros cv Hcv.
      rewrite (venv_add_const_vals_lookup_none (m := vcv_name cv) H1).
      * apply (vid_wf_fresh Hdecl). unfold ind_all_consts.
        apply in_or_app; right; apply in_or_app; left; exact Hcv.
      * intros Hin. apply (Hdisj_t (vcv_name cv) Hin).
        apply in_or_app; left; apply in_map; exact Hcv.
    + exact Hnd_c.
    + rewrite H2.
      destruct (exists_addConstVals (cvs := vid_recs decl) (env := env2)) as [env3 H3].
      * intros cv Hcv.
        rewrite (venv_add_const_vals_lookup_none (m := vcv_name cv) H2).
        -- rewrite (venv_add_const_vals_lookup_none (m := vcv_name cv) H1).
           ++ apply (vid_wf_fresh Hdecl). unfold ind_all_consts.
              apply in_or_app; right; apply in_or_app; right; exact Hcv.
           ++ intros Hin. apply (Hdisj_t (vcv_name cv) Hin).
              apply in_or_app; right; apply in_map; exact Hcv.
        -- intros Hin. exact (Hdisj_c (vcv_name cv) Hin (in_map vcv_name _ _ Hcv)).
      * exact Hnd_r.
      * rewrite H3. eexists; reflexivity.
Qed.

Theorem addInduct_WF env decl env' :
  VEnvWF env ->
  VInductDeclWF env decl ->
  venv_add_induct env decl = Some env' ->
  VEnvWF env' /\ venv_ordered env env'.
Proof.
  intros Hwf Hdecl Hadd.
  unfold venv_add_induct in Hadd.
  destruct (venv_add_const_vals env (ind_type_consts decl)) as [env1|] eqn:H1; [|discriminate].
  destruct (venv_add_const_vals env1 (ind_ctor_consts decl)) as [env2|] eqn:H2; [|discriminate].
  destruct (venv_add_const_vals env2 (vid_recs decl)) as [env3|] eqn:H3; [|discriminate].
  inversion Hadd; subst env'. clear Hadd.
  destruct (venv_add_const_vals_wf Hwf (vid_wf_types Hdecl) H1) as [Hwf1 Ho1].
  destruct (venv_add_const_vals_wf Hwf1 (vid_wf_ctors Hdecl H1) H2) as [Hwf2 Ho2].
  destruct (venv_add_const_vals_wf Hwf2 (vid_wf_recs Hdecl H1 H2) H3) as [Hwf3 Ho3].
  destruct (venv_add_raw_defeqs_wf Hwf3 (vid_wf_iotas Hdecl H1 H2 H3)) as [Hwf4 Ho4].
  split; [exact Hwf4 |].
  exact (venv_ordered_trans Ho1 (venv_ordered_trans Ho2 (venv_ordered_trans Ho3 Ho4))).
Qed.

Theorem addInduct_consts env decl env' cv :
  venv_add_induct env decl = Some env' ->
  In cv (ind_all_consts decl) ->
  venv_constants env' (vcv_name cv) = Some (vcv_const cv).
Proof.
  intros Hadd Hmem.
  unfold venv_add_induct in Hadd.
  destruct (venv_add_const_vals env (ind_type_consts decl)) as [env1|] eqn:H1; [|discriminate].
  destruct (venv_add_const_vals env1 (ind_ctor_consts decl)) as [env2|] eqn:H2; [|discriminate].
  destruct (venv_add_const_vals env2 (vid_recs decl)) as [env3|] eqn:H3; [|discriminate].
  inversion Hadd; subst env'. clear Hadd.
  pose proof (venv_add_const_vals_ordered H2) as Ho2.
  pose proof (venv_add_const_vals_ordered H3) as Ho3.
  pose proof (venv_add_raw_defeqs_ordered env3 (vid_iotas decl)) as Ho4.
  unfold ind_all_consts in Hmem.
  apply in_app_or in Hmem as [Ht | Hcr].
  - exact (venv_ord_const Ho4 (venv_ord_const Ho3 (venv_ord_const Ho2
             (venv_add_const_vals_constants H1 Ht)))).
  - apply in_app_or in Hcr as [Hc | Hr].
    + exact (venv_ord_const Ho4 (venv_ord_const Ho3
               (venv_add_const_vals_constants H2 Hc))).
    + exact (venv_ord_const Ho4 (venv_add_const_vals_constants H3 Hr)).
Qed.

Theorem addInduct_iotas env decl env' df :
  venv_add_induct env decl = Some env' ->
  In df (vid_iotas decl) ->
  venv_defeqs env' df.
Proof.
  intros Hadd Hmem.
  unfold venv_add_induct in Hadd.
  destruct (venv_add_const_vals env (ind_type_consts decl)) as [env1|]; [|discriminate].
  destruct (venv_add_const_vals env1 (ind_ctor_consts decl)) as [env2|]; [|discriminate].
  destruct (venv_add_const_vals env2 (vid_recs decl)) as [env3|]; [|discriminate].
  inversion Hadd; subst env'.
  exact (venv_add_raw_defeqs_mem env3 Hmem).
Qed.

(* ========================================================================= *)
(* 6. Declaration & Environment Traces (VDeclWF, VEnvDeclsWF -> VEnvWF)      *)
(* ========================================================================= *)

Inductive VDeclWF : VEnv -> VDecl -> VEnv -> Prop :=
| VDeclWF_axiom : forall env env' ci,
    VConstantWF env (vcv_const ci) ->
    venv_add_const env (vcv_name ci) (vcv_const ci) = Some env' ->
    VDeclWF env (VDAxiom ci) env'
| VDeclWF_def : forall env env' ci,
    VDefValWF env ci ->
    venv_add_const env (vdv_name ci) (vdv_to_constant ci) = Some env' ->
    VDeclWF env (VDDef ci) (venv_add_defeq env' (vdef_to_defeq ci))
| VDeclWF_mutualDef : forall env env' cis,
    (forall ci, In ci cis -> VConstantWF env (vdv_to_constant ci)) ->
    venv_add_consts env cis = Some env' ->
    (forall ci, In ci cis -> VDefValWF env' ci) ->
    VDeclWF env (VDMutualDef cis) (venv_add_defeqs env' cis)
| VDeclWF_opaque : forall env env' ci,
    VDefValWF env ci ->
    venv_add_const env (vdv_name ci) (vdv_to_constant ci) = Some env' ->
    VDeclWF env (VDOpaque ci) env'
| VDeclWF_example : forall env ci,
    VDefValWF env ci ->
    VDeclWF env (VDExample ci) env
| VDeclWF_quot : forall env env',
    VQuotReady env ->
    venv_add_quot env = Some env' ->
    VDeclWF env VDQuot env'
| VDeclWF_induct : forall env env' decl,
    VInductDeclWF env decl ->
    venv_add_induct env decl = Some env' ->
    VDeclWF env (VDInduct decl) env'.

Inductive VEnvDeclsWF : list VDecl -> VEnv -> Prop :=
| VEnvDeclsWF_empty : VEnvDeclsWF [] venv_empty
| VEnvDeclsWF_decl : forall env env' d ds,
    VDeclWF env d env' ->
    VEnvDeclsWF ds env ->
    VEnvDeclsWF (d :: ds) env'.

Definition VEnvTraceWF (env : VEnv) : Prop :=
  exists ds, VEnvDeclsWF ds env.

Theorem VDeclWF_wf env d env' :
  VEnvWF env ->
  VDeclWF env d env' ->
  VEnvWF env' /\ venv_ordered env env'.
Proof.
  intros Hwf Hdecl.
  inversion Hdecl; subst.
  - split; [eapply VEnvWF_add_const; eassumption | exact (venv_add_const_ordered _ _ _ H0)].
  - pose proof (venv_add_const_ordered _ _ _ H0) as Ho.
    assert (Hwf1 : VEnvWF env'0)
      by (eapply VEnvWF_add_const; [exact Hwf | exact (VDefValWF_to_VConstantWF Hwf H) | exact H0]).
    split.
    + apply VEnvWF_add_defeq; [exact Hwf1 |].
      exact (VDefValWF_to_VDefEqWF Hwf1 (venv_add_const_lookup_self _ _ _ H0)
               (VDefValWF_mono Ho H)).
    + exact (venv_ordered_trans Ho (venv_add_defeq_ordered _ _)).
  - destruct (venv_add_consts_wf Hwf H H0) as [Hwf1 Ho1].
    destruct (venv_add_defeqs_wf Hwf1 (venv_add_consts_constants H0) H1) as [Hwf2 Ho2].
    split; [exact Hwf2 | exact (venv_ordered_trans Ho1 Ho2)].
  - split; [eapply VEnvWF_add_const; [exact Hwf | exact (VDefValWF_to_VConstantWF Hwf H) | exact H0]
           | exact (venv_add_const_ordered _ _ _ H0)].
  - split; [exact Hwf | apply venv_ordered_refl].
  - exact (addQuot_WF Hwf H H0).
  - exact (addInduct_WF Hwf H H0).
Qed.

Theorem VEnvDeclsWF_to_VEnvWF ds env :
  VEnvDeclsWF ds env -> VEnvWF env.
Proof.
  induction 1 as [|env env' d ds Hdecl Hds IH].
  - constructor.
  - exact (proj1 (VDeclWF_wf IH Hdecl)).
Qed.

Corollary VEnvTraceWF_to_VEnvWF env :
  VEnvTraceWF env -> VEnvWF env.
Proof.
  intros [ds Hds]. exact (VEnvDeclsWF_to_VEnvWF Hds).
Qed.

(* ========================================================================= *)
(* 7. Concrete Non-Vacuity: Inductive Eq + Quotients from venv_empty         *)
(* ========================================================================= *)

Definition q_eq_refl_name : name := NameStr q_eq_name "refl".

(* Eq.refl.{u} : {alpha : Sort u} -> (a : alpha) -> Eq.{u} alpha a a *)
Definition eqReflConst : VConstant := {|
  vc_uvars := 1;
  vc_type  :=
    VForallE (VSort (VLParam 0))
      (VForallE (VBVar 0)
        (veq_app (VLParam 0) (VBVar 1) (VBVar 0) (VBVar 0)))
|}.

Definition eqInductDecl : VInductDecl := {|
  vid_uvars   := 1;
  vid_nparams := 2;
  vid_types   := [{|
    vit_const := {| vcv_const := eqConst; vcv_name := q_eq_name |};
    vit_ctors := [{| vcv_const := eqReflConst; vcv_name := q_eq_refl_name |}]
  |}];
  vid_recs    := [];
  vid_iotas   := []
|}.

Lemma eqInductDecl_WF_empty :
  VInductDeclWF venv_empty eqInductDecl.
Proof.
  constructor.
  - intros cv _. reflexivity.
  - unfold eqInductDecl, ind_all_consts, ind_type_consts, ind_ctor_consts; simpl.
    constructor; [simpl; intros [Heq | []]; discriminate |].
    constructor; [simpl; tauto | constructor].
  - intros cv Hcv.
    unfold eqInductDecl, ind_type_consts, ind_ctor_consts in Hcv; simpl in Hcv.
    destruct Hcv as [<- | [<- | []]]; reflexivity.
  - intros cv Hcv.
    unfold eqInductDecl, ind_type_consts in Hcv; simpl in Hcv.
    destruct Hcv as [<- | []]; apply VConstantWF_eqConst.
  - intros env1 H1 cv Hcv.
    unfold eqInductDecl, ind_type_consts in H1; simpl in H1.
    unfold eqInductDecl, ind_ctor_consts in Hcv; simpl in Hcv.
    destruct Hcv as [<- | []]; simpl.
    assert (Heq : venv_constants env1 q_eq_name = Some eqConst)
      by (inversion H1; subst; reflexivity).
    split.
    + eexists. unfold eqReflConst; simpl.
      assert (Hu0 : vlevel_wf 1 (VLParam 0)) by (simpl; lia).
      eapply VDF_forallEDF; [apply VHasType_sort; exact Hu0 |].
      eapply VDF_forallEDF; [apply VDF_bvar; vlk |].
      apply VHasType_eq_app;
        [exact Heq | exact Hu0
        | apply VDF_bvar; vlk
        | apply VDF_bvar; vlk
        | apply VDF_bvar; vlk].
    + unfold vclosed, eqReflConst, veq_app; cbn; repeat split; lia.
  - intros ? ? ? ? cv Hcv. inversion Hcv.
  - intros ? ? ? ? ? ? df Hdf. inversion Hdf.
Qed.

Theorem nonvacuous_eq_and_quot_trace :
  exists env_quot,
    VEnvDeclsWF [VDQuot; VDInduct eqInductDecl] env_quot /\
    VEnvWF env_quot /\
    venv_constants env_quot q_eq_name = Some eqConst /\
    venv_constants env_quot q_name = Some quotConst /\
    venv_constants env_quot q_mk_name = Some quotMkConst /\
    venv_constants env_quot q_lift_name = Some quotLiftConst /\
    venv_constants env_quot q_ind_name = Some quotIndConst /\
    venv_defeqs env_quot quotDefEq.
Proof.
  destruct (exists_addInduct eqInductDecl_WF_empty) as [env_eq Heq_add].
  assert (Hqr : VQuotReady env_eq).
  { unfold VQuotReady.
    exact (addInduct_consts Heq_add (or_introl eq_refl)). }
  assert (Hfresh : forall m, m <> q_eq_name -> m <> q_eq_refl_name -> venv_constants env_eq m = None).
  { intros m Hm1 Hm2.
    unfold venv_add_induct in Heq_add.
    destruct (venv_add_const_vals venv_empty (ind_type_consts eqInductDecl)) as [e1|] eqn:H1; [|discriminate].
    destruct (venv_add_const_vals e1 (ind_ctor_consts eqInductDecl)) as [e2|] eqn:H2; [|discriminate].
    destruct (venv_add_const_vals e2 (vid_recs eqInductDecl)) as [e3|] eqn:H3; [|discriminate].
    inversion Heq_add; subst env_eq. simpl.
    rewrite (venv_add_const_vals_lookup_none (m := m) H3) by (simpl; tauto).
    rewrite (venv_add_const_vals_lookup_none (m := m) H2) by (simpl; intros [Heq | []]; congruence).
    rewrite (venv_add_const_vals_lookup_none (m := m) H1) by (simpl; intros [Heq | []]; congruence).
    reflexivity. }
  destruct (exists_addQuot
              (Hfresh q_name ltac:(discriminate) ltac:(discriminate))
              (Hfresh q_mk_name ltac:(discriminate) ltac:(discriminate))
              (Hfresh q_lift_name ltac:(discriminate) ltac:(discriminate))
              (Hfresh q_ind_name ltac:(discriminate) ltac:(discriminate)))
    as [env_quot Hq_add].
  exists env_quot.
  assert (Htrace : VEnvDeclsWF [VDQuot; VDInduct eqInductDecl] env_quot).
  { eapply VEnvDeclsWF_decl; [exact (VDeclWF_quot Hqr Hq_add) |].
    eapply VEnvDeclsWF_decl; [exact (VDeclWF_induct eqInductDecl_WF_empty Heq_add) |].
    exact VEnvDeclsWF_empty. }
  repeat split.
  - exact Htrace.
  - exact (VEnvDeclsWF_to_VEnvWF Htrace).
  - exact (venv_ord_const (addQuot_ordered Hq_add) Hqr).
  - exact (addQuot_quot Hq_add).
  - exact (addQuot_quotMk Hq_add).
  - exact (addQuot_quotLift Hq_add).
  - exact (addQuot_quotInd Hq_add).
  - exact (addQuot_defeq Hq_add).
Qed.

(* ========================================================================= *)
(* Axiom Audit                                                               *)
(* ========================================================================= *)

Print Assumptions addQuot_WF.
Print Assumptions quotInd_iota_defeq.
Print Assumptions addQuot_quotInd_iota.
Print Assumptions venv_add_consts_wf.
Print Assumptions venv_add_defeqs_wf.
Print Assumptions exists_addConsts.
Print Assumptions exists_addInduct.
Print Assumptions addInduct_WF.
Print Assumptions VDeclWF_wf.
Print Assumptions VEnvDeclsWF_to_VEnvWF.
Print Assumptions nonvacuous_eq_and_quot_trace.
