(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/Typing/{Pattern,Injectivity,UniqueTyping,
   ChurchRosser,HeadReduction}.lean:
   orthogonal higher-order pattern matching, parameterized Pi/Sort injectivity,
   uniqueness of typing modulo definitional equality, typed parallel reduction,
   Takahashi complete development, typed Church-Rosser confluence, weak head
   reduction determinism, Kashima standardization, syntax-directed type
   inference, and unconditional non-vacuity on venv_empty. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel
  DeclarativeTyping TypingLemmas SubstTheory StrongTyping.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* ========================================================================= *)
(* 1. Patterns & Orthogonal Matching (Lean4Lean/Theory/Typing/Pattern.lean)  *)
(* ========================================================================= *)

Lemma name_eq_dec (a b : name) : {a = b} + {a <> b}.
Proof.
  destruct (name_eqb a b) eqn:E.
  - left. apply name_eqb_eq; exact E.
  - right. intros ->. rewrite name_eqb_refl in E. discriminate.
Qed.

Inductive VPattern : Type :=
| VPConst : name -> VPattern
| VPApp   : VPattern -> VPattern -> VPattern
| VPVar   : VPattern -> VPattern.

Lemma VPattern_eq_dec (p1 p2 : VPattern) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality; apply name_eq_dec.
Qed.

Fixpoint vpattern_varN (p : VPattern) (n : nat) : VPattern :=
  match n with
  | 0 => p
  | S n' => VPVar (vpattern_varN p n')
  end.

Fixpoint vpattern_size (p : VPattern) : nat :=
  match p with
  | VPConst _ => 1
  | VPApp f a => 1 + vpattern_size f + vpattern_size a
  | VPVar f => 1 + vpattern_size f
  end.

Inductive VSubpattern (p : VPattern) : VPattern -> Prop :=
| VSub_refl : VSubpattern p p
| VSub_appL : forall f a, VSubpattern p f -> VSubpattern p (VPApp f a)
| VSub_appR : forall f a, VSubpattern p a -> VSubpattern p (VPApp f a)
| VSub_varL : forall f, VSubpattern p f -> VSubpattern p (VPVar f).

Theorem VSubpattern_varN p f n :
  VSubpattern p f -> VSubpattern p (vpattern_varN f n).
Proof.
  intros H. induction n as [|n IH]; simpl; [exact H | apply VSub_varL; exact IH].
Qed.

Theorem VSubpattern_trans p1 p2 p3 :
  VSubpattern p1 p2 -> VSubpattern p2 p3 -> VSubpattern p1 p3.
Proof.
  intros H1 H2. induction H2.
  - exact H1.
  - apply VSub_appL; exact IHVSubpattern.
  - apply VSub_appR; exact IHVSubpattern.
  - apply VSub_varL; exact IHVSubpattern.
Qed.

Theorem VSubpattern_size_le p1 p2 :
  VSubpattern p1 p2 -> vpattern_size p1 <= vpattern_size p2.
Proof.
  induction 1; simpl; lia.
Qed.

Theorem VSubpattern_antisymm p1 p2 :
  VSubpattern p1 p2 -> VSubpattern p2 p1 -> p2 = p1.
Proof.
  intros H1 H2. inversion H2; subst; [reflexivity | ..];
    pose proof (VSubpattern_size_le H1);
    pose proof (VSubpattern_size_le H);
    simpl in *; lia.
Qed.

Theorem VSubpattern_varN_const p c n :
  VSubpattern p (vpattern_varN (VPConst c) n) ->
  exists m, p = vpattern_varN (VPConst c) m.
Proof.
  remember (vpattern_varN (VPConst c) n) as p' eqn:Heq.
  intros H. revert n Heq.
  induction H; intros n Heq.
  - exists n. exact Heq.
  - destruct n; simpl in Heq; discriminate.
  - destruct n; simpl in Heq; discriminate.
  - destruct n as [|n]; simpl in Heq; [discriminate |].
    inversion Heq; subst. exact (IHVSubpattern n eq_refl).
Qed.

Inductive VArity (p : VPattern) : nat -> VPattern -> Prop :=
| VArity_refl : VArity p 0 p
| VArity_app  : forall n f a, VArity p n f -> VArity p (S n) (VPApp f a)
| VArity_var  : forall n f, VArity p n f -> VArity p (S n) (VPVar f).

Theorem VArity_subpattern p n p' :
  VArity p n p' -> VSubpattern p p'.
Proof.
  induction 1.
  - apply VSub_refl.
  - apply VSub_appL; exact IHVArity.
  - apply VSub_varL; exact IHVArity.
Qed.

Fixpoint vpattern_inter (p q : VPattern) : option VPattern :=
  match p, q with
  | VPConst c, VPConst c' =>
      if name_eqb c c' then Some (VPConst c) else None
  | VPApp f a, VPApp f' a' =>
      match vpattern_inter f f', vpattern_inter a a' with
      | Some fi, Some ai => Some (VPApp fi ai)
      | _, _ => None
      end
  | VPVar f, VPVar f' =>
      match vpattern_inter f f' with
      | Some fi => Some (VPVar fi)
      | None => None
      end
  | VPApp f a, VPVar f' =>
      match vpattern_inter f f' with
      | Some fi => Some (VPApp fi a)
      | None => None
      end
  | VPVar f, VPApp f' a' =>
      match vpattern_inter f f' with
      | Some fi => Some (VPApp fi a')
      | None => None
      end
  | _, _ => None
  end.

Theorem vpattern_inter_self p :
  vpattern_inter p p = Some p.
Proof.
  induction p as [c | f IHf a IHa | f IHf]; simpl.
  - rewrite name_eqb_refl. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHf. reflexivity.
Qed.

Lemma name_eqb_sym a b : name_eqb a b = name_eqb b a.
Proof.
  destruct (name_eqb a b) eqn:E1, (name_eqb b a) eqn:E2; auto.
  - apply name_eqb_eq in E1; subst. rewrite name_eqb_refl in E2; discriminate.
  - apply name_eqb_eq in E2; subst. rewrite name_eqb_refl in E1; discriminate.
Qed.

Theorem vpattern_inter_comm p q :
  vpattern_inter p q = vpattern_inter q p.
Proof.
  revert q.
  induction p as [c | f IHf a IHa | f IHf]; destruct q as [c' | f' a' | f'];
    simpl; auto.
  - rewrite name_eqb_sym. destruct (name_eqb c' c) eqn:E; [|reflexivity].
    apply name_eqb_eq in E; subst; reflexivity.
  - rewrite (IHf f'), (IHa a'). reflexivity.
  - rewrite (IHf f'). reflexivity.
  - rewrite (IHf f'). reflexivity.
  - rewrite (IHf f'). reflexivity.
Qed.

Inductive VPatternLE : VPattern -> VPattern -> Prop :=
| VPLE_refl    : forall p, VPatternLE p p
| VPLE_var     : forall f f', VPatternLE f f' -> VPatternLE (VPVar f) (VPVar f')
| VPLE_app     : forall f f' a a', VPatternLE f f' -> VPatternLE a a' -> VPatternLE (VPApp f a) (VPApp f' a')
| VPLE_app_var : forall f f' a, VPatternLE f f' -> VPatternLE (VPApp f a) (VPVar f').

(* Reified finite match environments (eliminates functional extensionality!) *)

Fixpoint VPatternPath (p : VPattern) : Type :=
  match p with
  | VPConst _ => Empty_set
  | VPApp f a => (VPatternPath f + VPatternPath a)%type
  | VPVar f   => option (VPatternPath f)
  end.

Fixpoint VMatchEnv (p : VPattern) : Type :=
  match p with
  | VPConst _ => unit
  | VPApp f a => (VMatchEnv f * VMatchEnv a)%type
  | VPVar f   => (VExpr * VMatchEnv f)%type
  end.

Fixpoint vpath_get (p : VPattern) : VMatchEnv p -> VPatternPath p -> VExpr :=
  match p with
  | VPConst _ => fun _ x => match x with end
  | VPApp f a => fun m x =>
      match x with
      | inl xf => vpath_get (fst m) xf
      | inr xa => vpath_get (snd m) xa
      end
  | VPVar f => fun m x =>
      match x with
      | None    => fst m
      | Some xf => vpath_get (snd m) xf
      end
  end.

Fixpoint vmenv_map (g : VExpr -> VExpr) (p : VPattern) : VMatchEnv p -> VMatchEnv p :=
  match p with
  | VPConst _ => fun _ => tt
  | VPApp f a => fun m => (vmenv_map g (fst m), vmenv_map g (snd m))
  | VPVar f   => fun m => (g (fst m), vmenv_map g (snd m))
  end.

Fixpoint vmenv_build (p : VPattern) : (VPatternPath p -> VExpr) -> VMatchEnv p :=
  match p with
  | VPConst _ => fun _ => tt
  | VPApp f a => fun h => (vmenv_build (fun x => h (inl x)), vmenv_build (fun x => h (inr x)))
  | VPVar f   => fun h => (h None, vmenv_build (fun x => h (Some x)))
  end.

Theorem vmenv_ext p (m1 m2 : VMatchEnv p) :
  (forall x, vpath_get m1 x = vpath_get m2 x) -> m1 = m2.
Proof.
  induction p as [c | f IHf a IHa | f IHf]; simpl; intros H.
  - destruct m1, m2; reflexivity.
  - destruct m1 as [mf1 ma1], m2 as [mf2 ma2]; f_equal.
    + apply IHf; intros x; exact (H (inl x)).
    + apply IHa; intros x; exact (H (inr x)).
  - destruct m1 as [e1 mf1], m2 as [e2 mf2]; f_equal.
    + exact (H None).
    + apply IHf; intros x; exact (H (Some x)).
Qed.

Theorem vpath_get_map g p (m : VMatchEnv p) x :
  vpath_get (vmenv_map g m) x = g (vpath_get m x).
Proof.
  induction p as [c | f IHf a IHa | f IHf]; simpl.
  - destruct x.
  - destruct x as [xf | xa]; [apply IHf | apply IHa].
  - destruct x as [xf |]; [apply IHf | reflexivity].
Qed.

Theorem vpath_get_build p (h : VPatternPath p -> VExpr) x :
  vpath_get (vmenv_build h) x = h x.
Proof.
  induction p as [c | f IHf a IHa | f IHf]; simpl.
  - destruct x.
  - destruct x as [xf | xa]; [apply IHf | apply IHa].
  - destruct x as [xf |]; [apply IHf | reflexivity].
Qed.

Lemma vmenv_rel_choice p (R : VPatternPath p -> VExpr -> Prop) :
  (forall x, exists y, R x y) ->
  exists m : VMatchEnv p, forall x, R x (vpath_get m x).
Proof.
  induction p as [c | f IHf a IHa | f IHf]; simpl; intros H.
  - exists tt. intros [].
  - destruct (IHf (fun x => R (inl x)) (fun x => H (inl x))) as [mf Hmf].
    destruct (IHa (fun x => R (inr x)) (fun x => H (inr x))) as [ma Hma].
    exists (mf, ma). intros [xf | xa]; simpl; [apply Hmf | apply Hma].
  - destruct (H None) as [y0 Hy0].
    destruct (IHf (fun x => R (Some x)) (fun x => H (Some x))) as [mf Hmf].
    exists (y0, mf). intros [xf |]; simpl; [apply Hmf | exact Hy0].
Qed.

(* Structural Fixpoint definition of Pattern.Matches over p : VPattern:
   avoids dependent inversion / UIP / Eqdep_dec completely! *)

Fixpoint VPatternMatches (p : VPattern) (e : VExpr) (ls : list VLevel)
  : VMatchEnv p -> Prop :=
  match p return VMatchEnv p -> Prop with
  | VPConst c => fun m =>
      match e with
      | VConst c' ls' => c = c' /\ ls = ls' /\ m = tt
      | _ => False
      end
  | VPApp f a => fun m =>
      match e with
      | VApp f' a' =>
          @VPatternMatches f f' ls (fst m) /\
          exists ls2, @VPatternMatches a a' ls2 (snd m)
      | _ => False
      end
  | VPVar f => fun m =>
      match e with
      | VApp f' a' =>
          fst m = a' /\ @VPatternMatches f f' ls (snd m)
      | _ => False
      end
  end.

Arguments VPatternMatches : clear implicits.

Lemma VPM_const c ls :
  VPatternMatches (VPConst c) (VConst c ls) ls tt.
Proof.
  simpl; auto.
Qed.

Lemma VPM_var f f' a' ls mf :
  VPatternMatches f f' ls mf ->
  VPatternMatches (VPVar f) (VApp f' a') ls (a', mf).
Proof.
  intros Hf; simpl; auto.
Qed.

Lemma VPM_app f a f' a' ls1 ls2 mf ma :
  VPatternMatches f f' ls1 mf ->
  VPatternMatches a a' ls2 ma ->
  VPatternMatches (VPApp f a) (VApp f' a') ls1 (mf, ma).
Proof.
  intros Hf Ha; simpl; split; [exact Hf | exists ls2; exact Ha].
Qed.

Theorem VPatternMatches_uniq p e m1 m2 m1' m2' :
  VPatternMatches p e m1 m2 ->
  VPatternMatches p e m1' m2' ->
  m1 = m1' /\ m2 = m2'.
Proof.
  revert e m1 m2 m1' m2'.
  induction p as [c | f IHf a IHa | f IHf];
    intros e m1 m2 m1' m2' H1 H2; destruct e; simpl in *; try contradiction.
  - destruct H1 as [Hc1 [Hls1 Hm1]], H2 as [Hc2 [Hls2 Hm2]].
    subst; auto.
  - destruct m2 as [mf ma], m2' as [mf' ma']; simpl in *.
    destruct H1 as [Hf [ls2 Ha]], H2 as [Hf' [ls2' Ha']].
    destruct (IHf _ _ _ _ _ Hf Hf') as [-> ->].
    destruct (IHa _ _ _ _ _ Ha Ha') as [_ ->].
    auto.
  - destruct m2 as [ea mf], m2' as [ea' mf']; simpl in *.
    destruct H1 as [-> Hf], H2 as [-> Hf'].
    destruct (IHf _ _ _ _ _ Hf Hf') as [-> ->].
    auto.
Qed.

Theorem VPatternMatches_determ p e m1 m2 m1' m2' :
  VPatternMatches p e m1 m2 ->
  VPatternMatches p e m1' m2' ->
  m1 = m1' /\ m2 = m2'.
Proof.
  exact (@VPatternMatches_uniq p e m1 m2 m1' m2').
Qed.

Fixpoint vexpr_size (e : VExpr) : nat :=
  match e with
  | VBVar _ | VSort _ | VConst _ _ => 1
  | VApp f a | VLam f a | VForallE f a => 1 + vexpr_size f + vexpr_size a
  end.

Lemma VPatternMatches_path_size p e ls (m : VMatchEnv p) (x : VPatternPath p) :
  VPatternMatches p e ls m ->
  vexpr_size (vpath_get m x) < vexpr_size e.
Proof.
  revert e ls m x.
  induction p as [c | f IHf a IHa | f IHf]; simpl; intros e ls m x H.
  - destruct x.
  - destruct e; simpl in *; try contradiction.
    destruct H as [Hf [ls2 Ha]].
    destruct x as [xf | xa].
    + pose proof (IHf _ _ _ xf Hf); lia.
    + pose proof (IHa _ _ _ xa Ha); lia.
  - destruct e; simpl in *; try contradiction.
    destruct H as [-> Hf].
    destruct x as [xf |].
    + pose proof (IHf _ _ _ xf Hf); lia.
    + lia.
Qed.

Fixpoint VPatternOnArgs (P : VExpr -> Prop) (p : VPattern) : Prop :=
  match p with
  | VPConst _ => True
  | VPVar f => VPatternOnArgs P f
  | VPApp f a =>
      VPatternOnArgs P f /\ VPatternOnArgs P a /\
      forall e m1 m2, VPatternMatches a e m1 m2 -> P e
  end.

Inductive VPatternRHS (p : VPattern) : Type :=
| VRHS_fixed : forall c : VExpr, vclosed c -> VPatternRHS p
| VRHS_app   : VPatternRHS p -> VPatternRHS p -> VPatternRHS p
| VRHS_var   : VPatternPath p -> VPatternRHS p.

Arguments VRHS_fixed {p} c _.
Arguments VRHS_app {p} _ _.
Arguments VRHS_var {p} _.

Inductive VPatternCheck (p : VPattern) : Type :=
| VCheck_true  : VPatternCheck p
| VCheck_defeq : VPatternRHS p -> VPatternRHS p -> VPatternCheck p -> VPatternCheck p.

Arguments VCheck_true {p}.
Arguments VCheck_defeq {p} _ _ _.

Fixpoint vrhs_apply {p : VPattern} (m1 : list VLevel) (m2 : VMatchEnv p)
    (r : VPatternRHS p) : VExpr :=
  match r with
  | VRHS_fixed c _ => vinstL m1 c
  | VRHS_var path => vpath_get m2 path
  | VRHS_app f a => VApp (vrhs_apply m1 m2 f) (vrhs_apply m1 m2 a)
  end.

Theorem vrhs_apply_vlift' p (m1 : list VLevel) (m2 : VMatchEnv p)
    (r : VPatternRHS p) rho :
  vlift' rho (vrhs_apply m1 m2 r) =
  vrhs_apply m1 (vmenv_map (vlift' rho) m2) r.
Proof.
  induction r as [c Hcl | f IHf a IHa | path]; simpl.
  - apply (@vclosedN_vlift'_eq 0 rho).
    + apply vinstL_preserves_vclosedN. exact Hcl.
    + apply vlift_fixes_zero.
  - rewrite IHf, IHa. reflexivity.
  - symmetry. apply vpath_get_map.
Qed.

Theorem vrhs_apply_vliftN p (m1 : list VLevel) (m2 : VMatchEnv p)
    (r : VPatternRHS p) n k :
  vliftN n k (vrhs_apply m1 m2 r) =
  vrhs_apply m1 (vmenv_map (vliftN n k) m2) r.
Proof.
  induction r as [c Hcl | f IHf a IHa | path]; simpl.
  - apply vclosedN_vliftN_eq.
    apply (@vclosedN_mono _ 0 k (le_0_n _)).
    apply vinstL_preserves_vclosedN. exact Hcl.
  - rewrite IHf, IHa. reflexivity.
  - symmetry. apply vpath_get_map.
Qed.

Theorem vrhs_apply_vinst p (m1 : list VLevel) (m2 : VMatchEnv p)
    (r : VPatternRHS p) e0 k :
  vinst (vrhs_apply m1 m2 r) e0 k =
  vrhs_apply m1 (vmenv_map (fun x => vinst x e0 k) m2) r.
Proof.
  induction r as [c Hcl | f IHf a IHa | path]; simpl.
  - apply vclosedN_vinst_eq.
    apply (@vclosedN_mono _ 0 k (le_0_n _)).
    apply vinstL_preserves_vclosedN. exact Hcl.
  - rewrite IHf, IHa. reflexivity.
  - symmetry. apply vpath_get_map.
Qed.

Lemma VPatternMatches_vlift'_fwd p rho e m1 m2 :
  VPatternMatches p e m1 m2 ->
  VPatternMatches p (vlift' rho e) m1 (vmenv_map (vlift' rho) m2).
Proof.
  revert e m1 m2.
  induction p as [c | f IHf a IHa | f IHf];
    intros e m1 m2 H; destruct e; simpl in *; try contradiction.
  - destruct H as [-> [-> _]]; auto.
  - destruct H as [Hf [ls2 Ha]].
    split; [apply IHf; exact Hf | exists ls2; apply IHa; exact Ha].
  - destruct H as [<- Hf].
    split; [reflexivity | apply IHf; exact Hf].
Qed.

Theorem VPatternMatches_vlift' p rho e m1 m2' :
  VPatternMatches p (vlift' rho e) m1 m2' <->
  exists m2, VPatternMatches p e m1 m2 /\ m2' = vmenv_map (vlift' rho) m2.
Proof.
  split.
  - revert e m1 m2'.
    induction p as [c | f IHf a IHa | f IHf];
      intros e m1 m2' H; destruct e; simpl in *; try contradiction.
    + destruct H as [Hc [Hls ->]]. exists tt; simpl; auto.
    + destruct m2' as [mf' ma']; simpl in *.
      destruct H as [Hf [ls2 Ha]].
      destruct (IHf _ _ _ Hf) as [mf [Hmf ->]].
      destruct (IHa _ _ _ Ha) as [ma [Hma ->]].
      exists (mf, ma); simpl; split; [split; [exact Hmf | exists ls2; exact Hma] | reflexivity].
    + destruct m2' as [ea' mf']; simpl in *.
      destruct H as [-> Hf].
      destruct (IHf _ _ _ Hf) as [mf [Hmf ->]].
      exists (e2, mf); simpl; auto.
  - intros [m2 [Hm ->]]. apply VPatternMatches_vlift'_fwd; exact Hm.
Qed.

Theorem VPatternMatches_vliftN p n k e m1 m2' :
  VPatternMatches p (vliftN n k e) m1 m2' <->
  exists m2, VPatternMatches p e m1 m2 /\ m2' = vmenv_map (vliftN n k) m2.
Proof.
  rewrite <- vlift'_consN_skipN.
  rewrite VPatternMatches_vlift'.
  split; intros [m2 [Hm ->]]; exists m2; split; try exact Hm;
    apply vmenv_ext; intros x; rewrite !vpath_get_map, vlift'_consN_skipN; reflexivity.
Qed.

Theorem VPatternMatches_vinst p e m1 m2 e0 k :
  VPatternMatches p e m1 m2 ->
  VPatternMatches p (vinst e e0 k) m1 (vmenv_map (fun x => vinst x e0 k) m2).
Proof.
  revert e m1 m2.
  induction p as [c | f IHf a IHa | f IHf];
    intros e m1 m2 H; destruct e; simpl in *; try contradiction.
  - destruct H as [-> [-> _]]; auto.
  - destruct H as [Hf [ls2 Ha]].
    split; [apply IHf; exact Hf | exists ls2; apply IHa; exact Ha].
  - destruct H as [<- Hf].
    split; [reflexivity | apply IHf; exact Hf].
Qed.

Theorem VPatternMatches_inter p q e :
  ((exists m1 m2, VPatternMatches p e m1 m2) /\
   (exists m1 m2, VPatternMatches q e m1 m2)) <->
  (exists r m1 m2, vpattern_inter p q = Some r /\ VPatternMatches r e m1 m2).
Proof.
  split.
  - revert q e.
    induction p as [c | f IHf a IHa | f IHf];
      intros [c' | f' a' | f'] e [[m1 [m2 Hp]] [m3 [m4 Hq]]];
      destruct e; simpl in *; try contradiction.
    + destruct Hp as [? [? _]], Hq as [? [? _]]; subst.
      rewrite name_eqb_refl. eexists (VPConst _), _, tt; simpl; auto.
    + destruct Hp as [Hf [ls2 Ha]], Hq as [Hf' [ls2' Ha']].
      destruct (IHf f' e1 (conj (ex_intro _ m1 (ex_intro _ (fst m2) Hf))
                                (ex_intro _ m3 (ex_intro _ (fst m4) Hf'))))
        as [rf [mrf1 [mrf2 [Hif Hmf]]]].
      destruct (IHa a' e2 (conj (ex_intro _ ls2 (ex_intro _ (snd m2) Ha))
                                (ex_intro _ ls2' (ex_intro _ (snd m4) Ha'))))
        as [ra [mra1 [mra2 [Hia Hma]]]].
      rewrite Hif, Hia.
      exists (VPApp rf ra), mrf1, (mrf2, mra2); simpl; split; [reflexivity |].
      split; [exact Hmf | exists mra1; exact Hma].
    + destruct Hp as [Hf [ls2 Ha]], Hq as [_ Hf'].
      destruct (IHf f' e1 (conj (ex_intro _ m1 (ex_intro _ (fst m2) Hf))
                                (ex_intro _ m3 (ex_intro _ (snd m4) Hf'))))
        as [rf [mrf1 [mrf2 [Hif Hmf]]]].
      rewrite Hif.
      exists (VPApp rf a), mrf1, (mrf2, snd m2); simpl; split; [reflexivity |].
      split; [exact Hmf | exists ls2; exact Ha].
    + destruct Hp as [_ Hf], Hq as [Hf' [ls2' Ha']].
      destruct (IHf f' e1 (conj (ex_intro _ m1 (ex_intro _ (snd m2) Hf))
                                (ex_intro _ m3 (ex_intro _ (fst m4) Hf'))))
        as [rf [mrf1 [mrf2 [Hif Hmf]]]].
      rewrite Hif.
      exists (VPApp rf a'), mrf1, (mrf2, snd m4); simpl; split; [reflexivity |].
      split; [exact Hmf | exists ls2'; exact Ha'].
    + destruct Hp as [_ Hf], Hq as [_ Hf'].
      destruct (IHf f' e1 (conj (ex_intro _ m1 (ex_intro _ (snd m2) Hf))
                                (ex_intro _ m3 (ex_intro _ (snd m4) Hf'))))
        as [rf [mrf1 [mrf2 [Hif Hmf]]]].
      rewrite Hif.
      exists (VPVar rf), mrf1, (e2, mrf2); simpl; auto.
  - revert q e.
    induction p as [c | f IHf a IHa | f IHf];
      intros [c' | f' a' | f'] e [r [m1 [m2 [Hi Hr]]]];
      simpl in Hi; try discriminate.
    + destruct (name_eqb c c') eqn:E; [|discriminate].
      apply name_eqb_eq in E; subst c'.
      inversion Hi; subst r.
      destruct e; simpl in Hr; try contradiction.
      destruct Hr as [? [? _]]; subst.
      split; eexists _, tt; simpl; auto.
    + destruct (vpattern_inter f f') as [fi|] eqn:Hif; [|discriminate].
      destruct (vpattern_inter a a') as [ai|] eqn:Hia; [|discriminate].
      inversion Hi; subst r.
      destruct e; simpl in Hr; try contradiction.
      destruct Hr as [Hmf [ls2 Hma]].
      destruct (IHf f' e1 (ex_intro _ fi (ex_intro _ m1 (ex_intro _ (fst m2) (conj Hif Hmf)))))
        as [[mf1 [mf2 Hpf]] [mf1' [mf2' Hqf]]].
      destruct (IHa a' e2 (ex_intro _ ai (ex_intro _ ls2 (ex_intro _ (snd m2) (conj Hia Hma)))))
        as [[ma1 [ma2 Hpa]] [ma1' [ma2' Hqa]]].
      split.
      * exists mf1, (mf2, ma2); simpl; split; [exact Hpf | exists ma1; exact Hpa].
      * exists mf1', (mf2', ma2'); simpl; split; [exact Hqf | exists ma1'; exact Hqa].
    + destruct (vpattern_inter f f') as [fi|] eqn:Hif; [|discriminate].
      inversion Hi; subst r.
      destruct e; simpl in Hr; try contradiction.
      destruct Hr as [Hmf [ls2 Hma]].
      destruct (IHf f' e1 (ex_intro _ fi (ex_intro _ m1 (ex_intro _ (fst m2) (conj Hif Hmf)))))
        as [[mf1 [mf2 Hpf]] [mf1' [mf2' Hqf]]].
      split.
      * exists mf1, (mf2, snd m2); simpl; split; [exact Hpf | exists ls2; exact Hma].
      * exists mf1', (e2, mf2'); simpl; auto.
    + destruct (vpattern_inter f f') as [fi|] eqn:Hif; [|discriminate].
      inversion Hi; subst r.
      destruct e; simpl in Hr; try contradiction.
      destruct Hr as [Hmf [ls2 Hma]].
      destruct (IHf f' e1 (ex_intro _ fi (ex_intro _ m1 (ex_intro _ (fst m2) (conj Hif Hmf)))))
        as [[mf1 [mf2 Hpf]] [mf1' [mf2' Hqf]]].
      split.
      * exists mf1, (e2, mf2); simpl; auto.
      * exists mf1', (mf2', snd m2); simpl; split; [exact Hqf | exists ls2; exact Hma].
    + destruct (vpattern_inter f f') as [fi|] eqn:Hif; [|discriminate].
      inversion Hi; subst r.
      destruct e; simpl in Hr; try contradiction.
      destruct Hr as [_ Hmf].
      destruct (IHf f' e1 (ex_intro _ fi (ex_intro _ m1 (ex_intro _ (snd m2) (conj Hif Hmf)))))
        as [[mf1 [mf2 Hpf]] [mf1' [mf2' Hqf]]].
      split.
      * exists mf1, (e2, mf2); simpl; auto.
      * exists mf1', (e2, mf2'); simpl; auto.
Qed.

Fixpoint VPatternCheckOK (defeq : VExpr -> VExpr -> Prop) {p : VPattern}
    (m1 : list VLevel) (m2 : VMatchEnv p) (ck : VPatternCheck p) : Prop :=
  match ck with
  | VCheck_true => True
  | VCheck_defeq a b rest =>
      defeq (vrhs_apply m1 m2 a) (vrhs_apply m1 m2 b) /\
      VPatternCheckOK defeq m1 m2 rest
  end.

Theorem VPatternCheckOK_map (df df' : VExpr -> VExpr -> Prop) p
    (ck : VPatternCheck p) m1 m2 m1' m2' :
  (forall a b : VPatternRHS p,
     df (vrhs_apply m1 m2 a) (vrhs_apply m1 m2 b) ->
     df' (vrhs_apply m1' m2' a) (vrhs_apply m1' m2' b)) ->
  VPatternCheckOK df m1 m2 ck ->
  VPatternCheckOK df' m1' m2' ck.
Proof.
  intros Hmap.
  induction ck as [| a b rest IH]; simpl; auto.
  intros [Hab Hrest]. split; [apply Hmap; exact Hab | apply IH; exact Hrest].
Qed.

Inductive VSimplePattern : Type :=
| VSP_iota : name -> nat -> name -> nat -> VSimplePattern
| VSP_defn : name -> VSimplePattern.

Definition vsimple_to_pattern (sp : VSimplePattern) : VPattern :=
  match sp with
  | VSP_defn c => VPConst c
  | VSP_iota r m c n => VPApp (vpattern_varN (VPConst r) m) (vpattern_varN (VPConst c) n)
  end.

(* ========================================================================= *)
(* 2. Injectivity & Uniqueness of Typing                                     *)
(*    (Lean4Lean/Theory/Typing/{Injectivity,UniqueTyping}.lean)              *)
(* ========================================================================= *)

Lemma nat_strong_ind (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros Hstep n.
  assert (H : forall k m, m <= k -> P m).
  { induction k as [|k IH]; intros m Hm.
    - apply Hstep. intros m0 Hm0. lia.
    - destruct (Nat.eq_dec m (S k)) as [-> | Hne].
      + apply Hstep. intros m0 Hm0. apply IH. lia.
      + apply IH. lia. }
  exact (H n n (Nat.le_refl n)).
Qed.

(* Transparent Record parameterizing the 4 structural properties of
   Injectivity.lean and UniqueTyping.lean (ZERO Axioms!). *)

Record DefEqInjectivity (env : VEnv) : Prop := {
  defeq_sort_inv : forall {U G u v},
    VCtxWF env U G ->
    VIsDefEqU env U G (VSort u) (VSort v) ->
    vlevel_equiv u v;
  defeq_forallE_inv_stratified : forall {U G A B A' B' V V' n n'},
    VCtxWF env U G ->
    VIsDefEqU env U G (VForallE A B) (VForallE A' B') ->
    VHasTypeStratified env U G (VForallE A B) V true n ->
    VHasTypeStratified env U G (VForallE A' B') V' true n' ->
    (exists u, VIsDefEq env U G A A' (VSort u) /\
       VHasTypeStratified env U G A (VSort u) true n) /\
    (exists u, VIsDefEq env U (A :: G) B B' (VSort u) /\
       VHasTypeStratified env U (A :: G) B (VSort u) true n /\
       VHasTypeStratified env U (A' :: G) B' (VSort u) true n');
  defeq_sort_forallE_inv : forall {U G u A B},
    VCtxWF env U G ->
    ~ VIsDefEqU env U G (VSort u) (VForallE A B);
  defeq_weakN_iff : forall {U n k G G' e1 e2},
    VCtxWF env U G' ->
    VCtxLiftN n k G G' ->
    (VIsDefEqU env U G' (vliftN n k e1) (vliftN n k e2) <->
     VIsDefEqU env U G e1 e2)
}.

Theorem VIsDefEqU_sort_inv env U G u v :
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G (VSort u) (VSort v) ->
  vlevel_equiv u v.
Proof.
  intros Hinj HG H. exact (defeq_sort_inv Hinj HG H).
Qed.

Theorem VIsDefEqU_forallE_inv env U G A B A' B' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G (VForallE A B) (VForallE A' B') ->
  (exists u, VIsDefEq env U G A A' (VSort u)) /\
  (exists v, VIsDefEq env U (A :: G) B B' (VSort v)).
Proof.
  intros Hwf Hinj HG H1.
  destruct H1 as [T Heq].
  destruct (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG Heq)) as [Hs1 Hs2].
  destruct (VHasTypeStrong_stratify Hs1) as [n Hst1].
  destruct (VHasTypeStrong_stratify Hs2) as [n' Hst2].
  destruct (defeq_forallE_inv_stratified Hinj HG (ex_intro _ T Heq) Hst1 Hst2)
    as [[u [HA _]] [v [HB _]]].
  split; [exists u; exact HA | exists v; exact HB].
Qed.

Theorem VIsDefEqU_sort_forallE_inv env U G {u A B} :
  DefEqInjectivity env ->
  VCtxWF env U G ->
  ~ VIsDefEqU env U G (VSort u) (VForallE A B).
Proof.
  intros Hinj HG. exact (defeq_sort_forallE_inv Hinj HG).
Qed.

Theorem VIsDefEqU_weakN_iff env U n k G G' {e1 e2} :
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VIsDefEqU env U G' (vliftN n k e1) (vliftN n k e2) <->
   VIsDefEqU env U G e1 e2).
Proof.
  intros Hinj HG' W. exact (defeq_weakN_iff Hinj HG' W).
Qed.

(* Uniqueness of typing up to definitional equality (UniqueTyping.lean) *)

Lemma VIsDefEq_sort_inv_r env U G e1 u V :
  VIsDefEq env U G e1 (VSort u) V -> vlevel_wf U u.
Proof.
  intros H. exact (VIsDefEq_sort_inv' H (or_intror eq_refl)).
Qed.

Lemma VIsDefEq_uniq_stratified env U :
  VEnvWF env ->
  DefEqInjectivity env ->
  forall n G e A B b n1 n2,
    VCtxWF env U G ->
    n1 <= n ->
    n2 <= n ->
    VHasTypeStratified env U G e A b n1 ->
    VHasTypeStratified env U G e B b n2 ->
    exists u, VIsDefEq env U G A B (VSort u) /\
      exists v, vlevel_equiv u v /\
        VHasTypeStratified env U G A (VSort u) true (n - 1) /\
        VHasTypeStratified env U G B (VSort v) true (n - 1).
Proof.
  intros Hwf Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  apply (@nat_strong_ind (fun n =>
    forall G e A B b n1 n2,
      VCtxWF env U G ->
      n1 <= n -> n2 <= n ->
      VHasTypeStratified env U G e A b n1 ->
      VHasTypeStratified env U G e B b n2 ->
      exists u, VIsDefEq env U G A B (VSort u) /\
        exists v, vlevel_equiv u v /\
          VHasTypeStratified env U G A (VSort u) true (n - 1) /\
          VHasTypeStratified env U G B (VSort v) true (n - 1))).
  intros n IH G e A B b n1 n2 HG le1 le2 H1.
  revert B n2 n le1 le2 IH HG.
  induction H1 as
    [ G i A u m a1 a2 IHa2
    | G l l' m a1 a2 a3
    | G c ci ls u m a1 a2 a3 a4 IHa4
    | G A B f a u v m a1 a2 a3 IHa3 a4 IHa4 a5 IHa5 a6 IHa6 a7 IHa7
    | G A B body u v m a1 IHa1 a2 IHa2 a3 IHa3 a4 IHa4
    | G A body u v m a1 a2 a3 IHa3 a4 IHa4
    | G e A m a1 IHa1
    | G e A' A u m a1 a2 a3 IHa3 a4 IHa4 a5 IHa5 ];
    intros B0 n2 n0 le1 le2 IH HG H2.
  - (* bvar *)
    inversion H2 as [G' i' B' u' m' b1 b2 HeqG Heqi HeqA Heqb Heqn | | | | | | |]; subst.
    pose proof (VLookup_deterministic a1 b1) as ->.
    exists u'. split; [exact (VHasTypeStratified_hasType b2) |].
    exists u'. split; [apply vlevel_equiv_refl |].
    split; eapply VHasTypeStratified_mono; try exact b2; lia.
  - (* sort' *)
    inversion H2 as [| G' l0 l2' m' b1 b2 b3 HeqG Heqe HeqB Heqb Heqn | | | | | |]; subst.
    pose proof (vlevel_succ_congr (vlevel_equiv_trans (vlevel_equiv_symm b3) a3)) as Hsucc.
    exists (VLSucc (VLSucc l2')). split.
    + apply VDF_symm. apply VDF_sortDF; [exact b2 | exact a2 | exact Hsucc].
    + exists (VLSucc (VLSucc l')). split; [apply vlevel_succ_congr; exact Hsucc |].
      split; apply VHTSt_base; apply VHTSt_sort';
        [exact a2 | exact b2 | apply vlevel_equiv_symm; exact Hsucc
        |exact b2 | exact a2 | exact Hsucc].
  - (* const *)
    inversion H2 as [| | G' c' ci' ls' u' m' b1 b2 b3 b4 HeqG Heqe HeqB Heqb Heqn | | | | |]; subst.
    rewrite a1 in b1; inversion b1; subst ci'.
    exists u. split; [exact (VHasTypeStratified_hasType a4) |].
    exists u. split; [apply vlevel_equiv_refl |].
    split; eapply VHasTypeStratified_mono; try exact a4; lia.
  - (* app *)
    inversion H2 as [| | | G' A' B' f' a' u' v' m' b1 b2 b3 b4 b5 b6 b7 HeqG Heqe HeqB Heqb Heqn | | | |]; subst.
    destruct (IHa5 (VForallE A' B') m' n0 ltac:(lia) ltac:(lia) IH HG b5)
      as [w [c1 [w' [_ [c3 c4]]]]].
    destruct (defeq_forallE_inv_stratified Hinj HG (ex_intro _ _ c1) c3 c4)
      as [_ [u0 [d3 [d4 d5]]]].
    destruct n0 as [|k]; [lia |].
    replace (S k - 1) with k in * by lia.
    assert (HG1 : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VHasTypeStratified_hasType a3)]).
    destruct (IH k ltac:(lia) (A :: G) B (VSort v) (VSort u0) true m k HG1
                ltac:(lia) (Nat.le_refl k) a4 d4)
      as [s1 [hs1 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG1 (ex_intro _ _ hs1)) as e3.
    pose proof (VIsDefEq_sort_r Hwf HG1 (VHasTypeStratified_hasType d4)) as e4.
    assert (HG2 : VCtxWF env U (A' :: G))
      by (split; [exact HG | exists u'; exact (VHasTypeStratified_hasType b3)]).
    destruct (IH k ltac:(lia) (A' :: G) B' (VSort v') (VSort u0) true m' k HG2
                ltac:(lia) (Nat.le_refl k) b4 d5)
      as [s2 [hs2 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG2 (ex_intro _ _ hs2)) as e5.
    exists v. split.
    + eapply VDF_defeqDF.
      * apply VDF_sortDF; [exact e4 | exact a2 | apply vlevel_equiv_symm; exact e3].
      * exact (VIsDefEq_inst0 Hcl d3 (VHasTypeStratified_hasType a6)).
    + exists v'. split; [exact (vlevel_equiv_trans e3 (vlevel_equiv_symm e5)) |].
      split; eapply VHasTypeStratified_mono; [| exact a7 | | exact b7]; lia.
  - (* lam *)
    inversion H2 as [| | | | G' A' B' body' u' v' m' b1 b2 b3 b4 HeqG Heqe HeqB Heqb Heqn | | |]; subst.
    assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VHasTypeStratified_hasType a1)]).
    destruct (IHa3 B' m' n0 ltac:(lia) ltac:(lia) IH HG' b3)
      as [u1 [c1 [u2 [c2 [c3 c4]]]]].
    destruct n0 as [|k]; [lia |].
    replace (S k - 1) with k in * by lia.
    destruct (IH k ltac:(lia) G A (VSort u) (VSort u') true m m' HG
                ltac:(lia) ltac:(lia) a1 b1)
      as [s1 [hs1 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG (ex_intro _ _ hs1)) as e1.
    destruct (IH k ltac:(lia) (A :: G) B (VSort v) (VSort u1) true m k HG'
                ltac:(lia) (Nat.le_refl k) a2 c3)
      as [s2 [hs2 _]].
    pose proof (VIsDefEq_sort_inv_l hs2) as f1.
    pose proof (VIsDefEq_sort_inv_r hs2) as f2.
    pose proof (VIsDefEqU_sort_inv Hinj HG' (ex_intro _ _ hs2)) as e2.
    destruct (IH k ltac:(lia) (A :: G) B' (VSort v') (VSort u2) true m' k HG'
                ltac:(lia) (Nat.le_refl k) b2 c4)
      as [s3 [hs3 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG' (ex_intro _ _ hs3)) as e3.
    exists (VLIMax u v). split.
    + apply VDF_forallEDF; [exact (VHasTypeStratified_hasType a1) |].
      eapply VDF_defeqDF;
        [apply VDF_symm; apply VDF_sortDF; [exact f1 | exact f2 | exact e2]
        |exact c1].
    + exists (VLIMax u' v'). split.
      * apply vlevel_imax_congr; [exact e1 |].
        exact (vlevel_equiv_trans e2 (vlevel_equiv_trans c2 (vlevel_equiv_symm e3))).
      * split; eapply VHasTypeStratified_mono; [| exact a4 | | exact b4]; lia.
  - (* forallE *)
    inversion H2 as [| | | | | G' A' body' u' v' m' b1 b2 b3 b4 HeqG Heqe HeqB Heqb Heqn | |]; subst.
    destruct n0 as [|k]; [lia |].
    replace (S k - 1) with k in * by lia.
    destruct (IH k ltac:(lia) G A (VSort u) (VSort u') true m m' HG
                ltac:(lia) ltac:(lia) a3 b3)
      as [s1 [hs1 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG (ex_intro _ _ hs1)) as e1.
    assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VHasTypeStratified_hasType a3)]).
    destruct (IH k ltac:(lia) (A :: G) body (VSort v) (VSort v') true m m' HG'
                ltac:(lia) ltac:(lia) a4 b4)
      as [s2 [hs2 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG' (ex_intro _ _ hs2)) as e2.
    pose proof (vlevel_imax_congr e1 e2) as Himax.
    exists (VLSucc (VLIMax u v)). split.
    + apply VDF_sortDF; [simpl; auto | simpl; auto | exact Himax].
    + exists (VLSucc (VLIMax u v)). split; [apply vlevel_equiv_refl |].
      split; apply VHTSt_base; apply VHTSt_sort';
        [simpl; auto | simpl; auto | apply vlevel_equiv_refl
        |simpl; auto | simpl; auto | apply vlevel_equiv_symm; exact Himax].
  - (* base *)
    remember true as b_true eqn:Hb.
    revert a1 IHa1 n0 le1 le2 IH HG.
    induction H2 as
      [ | | | | |
      | G e B0 m' b1 IHb1
      | G e B_mid B0 u' m' b1 b2 b3 _ b4 _ b5 IHb5 ];
      intros a1 IHa1 n0 le1 le2 IH HG; try discriminate.
    + exact (IHa1 B0 m' n0 le1 le2 IH HG b1).
    + destruct (IHb5 Hb a1 IHa1 n0 le1 ltac:(lia) IH HG)
        as [u1 [c1 [u2 [c2 [c3 c4]]]]].
      destruct n0 as [|k]; [lia |].
      replace (S k - 1) with k in * by lia.
      destruct (IH k ltac:(lia) G B_mid (VSort u') (VSort u2) true m' k HG
                  ltac:(lia) (Nat.le_refl k) b3 c4)
        as [s1 [d1 _]].
      pose proof (VIsDefEqU_sort_inv Hinj HG (ex_intro _ _ d1)) as e1.
      pose proof (VIsDefEq_sort_r Hwf HG (VHasTypeStratified_hasType c3)) as e2.
      pose proof (vlevel_equiv_trans c2 (vlevel_equiv_symm e1)) as Hequ.
      exists u1. split.
      * eapply VDF_trans; [exact c1 |].
        eapply VDF_defeqDF;
          [apply VDF_symm; apply VDF_sortDF; [exact e2 | exact b1 | exact Hequ]
          |exact b2].
      * exists u'. split; [exact Hequ |].
        split; [exact c3 | eapply VHasTypeStratified_mono; [| exact b4]; lia].
  - (* defeq *)
    destruct (IHa5 B0 n2 n0 ltac:(lia) le2 IH HG H2)
      as [u1 [c1 [u2 [c2 [c3 c4]]]]].
    destruct n0 as [|k]; [lia |].
    replace (S k - 1) with k in * by lia.
    destruct (IH k ltac:(lia) G A' (VSort u) (VSort u1) true m k HG
                ltac:(lia) (Nat.le_refl k) a3 c3)
      as [s1 [d1 _]].
    pose proof (VIsDefEqU_sort_inv Hinj HG (ex_intro _ _ d1)) as e1.
    pose proof (VIsDefEq_sort_r Hwf HG (VHasTypeStratified_hasType c3)) as e2.
    pose proof (vlevel_equiv_trans e1 c2) as Hequ.
    exists u. split.
    + eapply VDF_trans; [exact (VDF_symm a2) |].
      eapply VDF_defeqDF;
        [apply VDF_symm; apply VDF_sortDF; [exact a1 | exact e2 | exact e1]
        |exact c1].
    + exists u2. split; [exact Hequ |].
      split; [eapply VHasTypeStratified_mono; [| exact a4]; lia | exact c4].
Qed.

Theorem VIsDefEq_uniq_same env U G e1 e2 e3 A1 A2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A1 ->
  VIsDefEq env U G e2 e3 A2 ->
  exists u, VIsDefEq env U G A1 A2 (VSort u).
Proof.
  intros Hwf Hinj HG H1 H2.
  destruct (VHasTypeStrong_stratify
              (proj2 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H1))))
    as [n1 Hst1].
  destruct (VHasTypeStrong_stratify
              (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H2))))
    as [n2 Hst2].
  destruct (@VIsDefEq_uniq_stratified env U Hwf Hinj (Nat.max n1 n2)
              G e2 A1 A2 true n1 n2 HG (Nat.le_max_l n1 n2) (Nat.le_max_r n1 n2)
              Hst1 Hst2)
    as [u [Hu _]].
  exists u; exact Hu.
Qed.

Theorem VIsDefEq_uniq env U G0 G1 G2 e1 e2 e3 A1 A2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G1 ->
  VCtxWF env U G2 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VIsDefEq env U G1 e1 e2 A1 ->
  VIsDefEq env U G2 e2 e3 A2 ->
  exists u, VIsDefEq env U G1 A1 A2 (VSort u).
Proof.
  intros Hwf Hinj HG1 _ W H1 H2.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VIsDefEq_defeqDFC Hcl (VIsDefEqCtx_symm Hcl W) H2) as H2'.
  exact (VIsDefEq_uniq_same Hwf Hinj HG1 H1 H2').
Qed.

Theorem VIsDefEq_uniqU env U G e1 e2 e3 A B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U G e2 e3 B ->
  VIsDefEqU env U G A B.
Proof.
  intros Hwf Hinj HG H1 H2.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG H1 H2) as [u Hu].
  exists (VSort u); exact Hu.
Qed.

Theorem VIsDefEq_iff env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  (VIsDefEq env U G e1 e2 A <->
   (VHasType env U G e1 A /\ VHasType env U G e2 A /\ VIsDefEqU env U G e1 e2)).
Proof.
  intros Hwf Hinj HG. split.
  - intros H. split; [exact (VIsDefEq_refl_l H) |].
    split; [exact (VIsDefEq_refl_r H) | exists A; exact H].
  - intros [_ [H2 [B H3]]].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG H3 H2) as [u Hu].
    exact (VDF_defeqDF Hu H3).
Qed.

Theorem VIsDefEq_trans_r env U G e1 e2 e3 A B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U G e2 e3 B ->
  VIsDefEq env U G e1 e3 B.
Proof.
  intros Hwf Hinj HG H1 H2.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG H1 H2) as [u Hu].
  exact (VDF_trans (VDF_defeqDF Hu H1) H2).
Qed.

Theorem VIsDefEq_trans_l env U G e1 e2 e3 A B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U G e2 e3 B ->
  VIsDefEq env U G e1 e3 A.
Proof.
  intros Hwf Hinj HG H1 H2.
  destruct (VIsDefEq_uniq_same Hwf Hinj HG H1 H2) as [u Hu].
  exact (VDF_trans H1 (VDF_defeqDF (VDF_symm Hu) H2)).
Qed.

Theorem VIsDefEq_transU_r env U G e1 e2 e3 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G e1 e2 ->
  VIsDefEq env U G e2 e3 A ->
  VIsDefEq env U G e1 e3 A.
Proof.
  intros Hwf Hinj HG [B H1] H2.
  exact (VIsDefEq_trans_r Hwf Hinj HG H1 H2).
Qed.

Theorem VIsDefEq_transU_l env U G e1 e2 e3 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEqU env U G e2 e3 ->
  VIsDefEq env U G e1 e3 A.
Proof.
  intros Hwf Hinj HG H1 [B H2].
  exact (VIsDefEq_trans_l Hwf Hinj HG H1 H2).
Qed.

Theorem VIsDefEqU_defeqDF env U G e1 e2 A B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G A B ->
  VIsDefEq env U G e1 e2 A ->
  VIsDefEq env U G e1 e2 B.
Proof.
  intros Hwf Hinj HG [T H1] H2.
  destruct (VIsDefEq_isType Hwf HG H2) as [u HA].
  exact (VDF_defeqDF (VIsDefEq_trans_l Hwf Hinj HG HA H1) H2).
Qed.

Theorem VIsDefEqU_of_l env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G e1 e2 ->
  VHasType env U G e1 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hwf Hinj HG [B H1] H2.
  exact (VIsDefEq_trans_l Hwf Hinj HG H2 H1).
Qed.

Theorem VHasType_defeqU_l env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G e1 e2 ->
  VHasType env U G e1 A ->
  VHasType env U G e2 A.
Proof.
  intros Hwf Hinj HG H1 H2.
  exact (VIsDefEq_refl_r (VIsDefEqU_of_l Hwf Hinj HG H1 H2)).
Qed.

Theorem VIsType_defeqU_l env U G A1 A2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G A1 A2 ->
  VIsType env U G A1 ->
  VIsType env U G A2.
Proof.
  intros Hwf Hinj HG H1 [u H2].
  exists u. exact (VHasType_defeqU_l Hwf Hinj HG H1 H2).
Qed.

Theorem VIsDefEqU_of_r env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G e1 e2 ->
  VHasType env U G e2 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hwf Hinj HG H1 H2.
  exact (VDF_symm (VIsDefEqU_of_l Hwf Hinj HG (VIsDefEqU_symm H1) H2)).
Qed.

Theorem VHasType_defeqU_r env U G e A1 A2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G A1 A2 ->
  VHasType env U G e A1 ->
  VHasType env U G e A2.
Proof.
  intros Hwf Hinj HG H1 H2.
  exact (VIsDefEqU_defeqDF Hwf Hinj HG H1 H2).
Qed.

Theorem VIsDefEqU_trans env U G e1 e2 e3 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VIsDefEqU env U G e1 e2 ->
  VIsDefEqU env U G e2 e3 ->
  VIsDefEqU env U G e1 e3.
Proof.
  intros Hwf Hinj HG [A H1] [B H2].
  exists A. exact (VIsDefEq_trans_l Hwf Hinj HG H1 H2).
Qed.

Theorem VExprWF_weakN_iff env U n k G G' {e} :
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VExprWF env U G' (vliftN n k e) <-> VExprWF env U G e).
Proof.
  intros Hinj HG' W.
  exact (VIsDefEqU_weakN_iff Hinj HG' W (e1 := e) (e2 := e)).
Qed.

Theorem VIsDefEq_skips env U n k G G' e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  VIsDefEq env U G' e1 e2 A ->
  VSkips n k e1 ->
  VSkips n k e2 ->
  exists B, VIsDefEq env U G' e1 e2 B /\ VSkips n k B.
Proof.
  intros Hwf Hinj HG' W H h1 h2.
  apply vskips_iff_exists in h1 as [e1' ->].
  apply vskips_iff_exists in h2 as [e2' ->].
  destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG' W) (ex_intro _ A H)) as [B0 HB0].
  exists (vliftN n k B0). split.
  - exact (VIsDefEq_weakN (VEnvWF_closed Hwf) HB0 W).
  - apply VSkips_vliftN.
Qed.

Theorem VIsDefEq_weakN_iff' env U n k G G' {e1 e2 A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxWF env U G ->
  VCtxLiftN n k G G' ->
  (VIsDefEq env U G' (vliftN n k e1) (vliftN n k e2) (vliftN n k A) <->
   VIsDefEq env U G e1 e2 A).
Proof.
  intros Hwf Hinj HG' HG W.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  split.
  - intros H.
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG' W) (ex_intro _ _ H)) as [B HB].
    eapply (VIsDefEqU_defeqDF Hwf Hinj HG); [| exact HB].
    apply (proj1 (VIsDefEqU_weakN_iff Hinj HG' W)).
    exact (VIsDefEq_uniqU Hwf Hinj HG' (VIsDefEq_weakN Hcl HB W) (VDF_symm H)).
  - intros H. exact (VIsDefEq_weakN Hcl H W).
Qed.

Theorem VCtxWF_weakN_inv env U n k G G' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxLiftN n k G G' ->
  VCtxWF env U G' ->
  VCtxWF env U G.
Proof.
  intros Hwf Hinj W.
  induction W as [As G Hlen | k G G' A W IH].
  - clear Hlen. induction As as [|B As IHAs]; simpl; [exact (fun H => H) | intros [H _]; exact (IHAs H)].
  - simpl. intros [HG' [u HA]].
    pose proof (IH HG') as HG.
    split; [exact HG |].
    exists u.
    exact (proj1 (@VIsDefEq_weakN_iff' env U n k G G' A A (VSort u) Hwf Hinj HG' HG W) HA).
Qed.

Theorem VIsDefEq_weakN_iff env U n k G G' {e1 e2 A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VIsDefEq env U G' (vliftN n k e1) (vliftN n k e2) (vliftN n k A) <->
   VIsDefEq env U G e1 e2 A).
Proof.
  intros Hwf Hinj HG' W.
  exact (VIsDefEq_weakN_iff' Hwf Hinj HG' (VCtxWF_weakN_inv Hwf Hinj W HG') W).
Qed.

Theorem VHasType_weakN_iff env U n k G G' {e A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VHasType env U G' (vliftN n k e) (vliftN n k A) <->
   VHasType env U G e A).
Proof.
  intros Hwf Hinj HG' W.
  exact (VIsDefEq_weakN_iff Hwf Hinj HG' W (e1 := e) (e2 := e) (A := A)).
Qed.

Theorem VIsType_weakN_iff env U n k G G' {A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VIsType env U G' (vliftN n k A) <-> VIsType env U G A).
Proof.
  intros Hwf Hinj HG' W. split; intros [u Hu]; exists u.
  - exact (proj1 (@VHasType_weakN_iff env U n k G G' A (VSort u) Hwf Hinj HG' W) Hu).
  - exact (proj2 (@VHasType_weakN_iff env U n k G G' A (VSort u) Hwf Hinj HG' W) Hu).
Qed.

Theorem VHasType_skips env U n k G G' e A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  VHasType env U G' e A ->
  VSkips n k e ->
  exists B, VHasType env U G' e B /\ VSkips n k B.
Proof.
  intros Hwf Hinj HG' W H1 H2.
  exact (VIsDefEq_skips Hwf Hinj HG' W H1 H2 H2).
Qed.

Theorem VIsDefEqU_weak'_iff env U l G G' {e1 e2} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' l G G' ->
  (VIsDefEqU env U G' (vlift' l e1) (vlift' l e2) <->
   VIsDefEqU env U G e1 e2).
Proof.
  intros Hwf Hinj HG' W.
  remember (vlift_depth l) as d eqn:Hd.
  symmetry in Hd.
  revert l G' Hd HG' W.
  induction d as [|d IH]; intros l G' Hd HG' W.
  - rewrite !vlift'_depth_zero by exact Hd.
    rewrite (VCtxLift'_depth_zero Hd W). tauto.
  - destruct (vlift_depth_succ Hd) as [l0 [k [Hd0 ->]]].
    destruct (VCtxLift'_of_cons_skip W) as [G1 [W1 W2]].
    rewrite vlift_consN_skip_eq, !vlift'_comp.
    replace (VLSkip VLRefl) with (vlift_skipN VLRefl 1) by reflexivity.
    rewrite !vlift'_consN_skipN.
    rewrite (VIsDefEqU_weakN_iff Hinj HG' W2).
    apply (IH (vlift_consN l0 k) G1).
    + rewrite vlift_depth_consN; exact Hd0.
    + exact (VCtxWF_weakN_inv Hwf Hinj W2 HG').
    + exact W1.
Qed.

Theorem VIsDefEq_weak'_iff env U l G G' {e1 e2 A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' l G G' ->
  (VIsDefEq env U G' (vlift' l e1) (vlift' l e2) (vlift' l A) <->
   VIsDefEq env U G e1 e2 A).
Proof.
  intros Hwf Hinj HG' W.
  remember (vlift_depth l) as d eqn:Hd.
  symmetry in Hd.
  revert l G' Hd HG' W.
  induction d as [|d IH]; intros l G' Hd HG' W.
  - rewrite !vlift'_depth_zero by exact Hd.
    rewrite (VCtxLift'_depth_zero Hd W). tauto.
  - destruct (vlift_depth_succ Hd) as [l0 [k [Hd0 ->]]].
    destruct (VCtxLift'_of_cons_skip W) as [G1 [W1 W2]].
    rewrite vlift_consN_skip_eq, !vlift'_comp.
    replace (VLSkip VLRefl) with (vlift_skipN VLRefl 1) by reflexivity.
    rewrite !vlift'_consN_skipN.
    rewrite (VIsDefEq_weakN_iff Hwf Hinj HG' W2).
    apply (IH (vlift_consN l0 k) G1).
    + rewrite vlift_depth_consN; exact Hd0.
    + exact (VCtxWF_weakN_inv Hwf Hinj W2 HG').
    + exact W1.
Qed.

Theorem VHasType_weak'_iff env U l G G' {e A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' l G G' ->
  (VHasType env U G' (vlift' l e) (vlift' l A) <->
   VHasType env U G e A).
Proof.
  intros Hwf Hinj HG' W.
  exact (VIsDefEq_weak'_iff Hwf Hinj HG' W (e1 := e) (e2 := e) (A := A)).
Qed.

Theorem VIsType_weak'_iff env U l G G' {A} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' l G G' ->
  (VIsType env U G' (vlift' l A) <-> VIsType env U G A).
Proof.
  intros Hwf Hinj HG' W. split; intros [u Hu]; exists u.
  - exact (proj1 (@VHasType_weak'_iff env U l G G' A (VSort u) Hwf Hinj HG' W) Hu).
  - exact (proj2 (@VHasType_weak'_iff env U l G G' A (VSort u) Hwf Hinj HG' W) Hu).
Qed.

Theorem VExprWF_weak'_iff env U l G G' {e} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' l G G' ->
  (VExprWF env U G' (vlift' l e) <-> VExprWF env U G e).
Proof.
  intros Hwf Hinj HG' W.
  exact (VIsDefEqU_weak'_iff Hwf Hinj HG' W (e1 := e) (e2 := e)).
Qed.

Theorem VCtxWF_weak'_inv env U rho G G' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxLift' rho G G' ->
  VCtxWF env U G' ->
  VCtxWF env U G.
Proof.
  intros Hwf Hinj W HG'.
  remember (vlift_depth rho) as d eqn:Hd.
  symmetry in Hd.
  revert rho G' Hd W HG'.
  induction d as [|d IH]; intros rho G' Hd W HG'.
  - rewrite (VCtxLift'_depth_zero Hd W). exact HG'.
  - destruct (vlift_depth_succ Hd) as [l0 [k [Hd0 ->]]].
    destruct (VCtxLift'_of_cons_skip W) as [G1 [W1 W2]].
    apply (IH (vlift_consN l0 k) G1).
    + rewrite vlift_depth_consN; exact Hd0.
    + exact W1.
    + exact (VCtxWF_weakN_inv Hwf Hinj W2 HG').
Qed.

(* ========================================================================= *)
(* 3. Typed Parallel Reduction & Church-Rosser Confluence                    *)
(*    (Lean4Lean/Theory/Typing/ChurchRosser.lean)                            *)
(* ========================================================================= *)

Arguments VDF_bvar {env uvars G i ty} _.
Arguments VHasType_const {env uvars} G {c ci ls} _ _ _.

Lemma vctx_cons env U G A u :
  VCtxWF env U G ->
  VHasType env U G A (VSort u) ->
  VCtxWF env U (A :: G).
Proof.
  intros HG HA. split; [exact HG | exists u; exact HA].
Qed.

Lemma vlevel_imax_zero u :
  vlevel_equiv (VLIMax u VLZero) VLZero.
Proof.
  intros ls; reflexivity.
Qed.

Lemma vlevel_imax_eq_zero u v :
  vlevel_equiv (VLIMax u v) VLZero -> vlevel_equiv v VLZero.
Proof.
  intros H ls. specialize (H ls). simpl in H.
  destruct (vlevel_eval ls v) as [|n]; [reflexivity | simpl in H; lia].
Qed.

(* Reflexive-transitive closure with snoc/tail constructor (matching Lean's
   ReflTransGen) plus constructive head induction! *)

Inductive VRTClosure {X : Type} (R : X -> X -> Prop) (x : X) : X -> Prop :=
| VRTC_rfl  : VRTClosure R x x
| VRTC_tail : forall y z, VRTClosure R x y -> R y z -> VRTClosure R x z.

Arguments VRTC_rfl {X R x}.
Arguments VRTC_tail {X R x y z} _ _.

Lemma VRTC_single {X : Type} {R : X -> X -> Prop} {x y : X} :
  R x y -> VRTClosure R x y.
Proof.
  intros H. exact (VRTC_tail VRTC_rfl H).
Qed.

Lemma VRTC_trans {X : Type} {R : X -> X -> Prop} {x y z : X} :
  VRTClosure R x y -> VRTClosure R y z -> VRTClosure R x z.
Proof.
  intros H1 H2. induction H2 as [| y' z' _ IH Hstep].
  - exact H1.
  - exact (VRTC_tail IH Hstep).
Qed.

Lemma VRTC_head {X : Type} {R : X -> X -> Prop} {x y z : X} :
  R x y -> VRTClosure R y z -> VRTClosure R x z.
Proof.
  intros H1 H2. exact (VRTC_trans (VRTC_single H1) H2).
Qed.

Inductive VRTC_hd {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
| VRTCH_rfl  : forall x, VRTC_hd R x x
| VRTCH_head : forall x y z, R x y -> VRTC_hd R y z -> VRTC_hd R x z.

Lemma VRTCH_snoc {X : Type} {R : X -> X -> Prop} {x y z : X} :
  VRTC_hd R x y -> R y z -> VRTC_hd R x z.
Proof.
  intros H1 H2. induction H1 as [x | x w y Hxw _ IH].
  - exact (VRTCH_head H2 (VRTCH_rfl R z)).
  - exact (VRTCH_head Hxw (IH H2)).
Qed.

Lemma VRTC_to_hd {X : Type} {R : X -> X -> Prop} {x z : X} :
  VRTClosure R x z -> VRTC_hd R x z.
Proof.
  induction 1 as [| y z _ IH Hyz].
  - apply VRTCH_rfl.
  - exact (VRTCH_snoc IH Hyz).
Qed.

Lemma VRTC_of_hd {X : Type} {R : X -> X -> Prop} {x z : X} :
  VRTC_hd R x z -> VRTClosure R x z.
Proof.
  induction 1 as [x | x y z Hxy _ IH].
  - exact VRTC_rfl.
  - exact (VRTC_head Hxy IH).
Qed.

Lemma VRTC_head_ind {X : Type} (R : X -> X -> Prop) (P : X -> X -> Prop) :
  (forall x, P x x) ->
  (forall x y z, R x y -> VRTClosure R y z -> P y z -> P x z) ->
  forall x z, VRTClosure R x z -> P x z.
Proof.
  intros Hrfl Hhd x z H.
  apply VRTC_to_hd in H.
  induction H as [x | x y z Hxy Hyz IH].
  - apply Hrfl.
  - exact (Hhd x y z Hxy (VRTC_of_hd Hyz) IH).
Qed.

(* Pattern RHS and Matches typing helpers *)

Theorem VIsDefEq_apply_pat env U G p (m1 : list VLevel) (m2 m2' : VMatchEnv p)
    (r : VPatternRHS p) A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  (forall a B, VHasType env U G (vpath_get m2 a) B ->
     VIsDefEqU env U G (vpath_get m2 a) (vpath_get m2' a)) ->
  VHasType env U G (vrhs_apply m1 m2 r) A ->
  VIsDefEq env U G (vrhs_apply m1 m2 r) (vrhs_apply m1 m2' r) A.
Proof.
  intros Hwf Hinj HG Hih.
  revert A.
  induction r as [c Hcl | rf IHf ra IHa | path]; intros A He; simpl in *.
  - exact He.
  - destruct (VHasType_app_inv Hwf HG He) as [A0 [B0 [Hf Ha]]].
    exact (VIsDefEq_trans_l Hwf Hinj HG He (VDF_appDF (IHf _ Hf) (IHa _ Ha))).
  - exact (VIsDefEqU_of_l Hwf Hinj HG (Hih path A He) He).
Qed.

Theorem VPatternMatches_hasType env U G p e m1 (m2 : VMatchEnv p) V
    (a : VPatternPath p) :
  VEnvWF env ->
  VCtxWF env U G ->
  VPatternMatches p e m1 m2 ->
  VHasType env U G e V ->
  exists A, VHasType env U G (vpath_get m2 a) A.
Proof.
  intros Hwf HG Hm Hty.
  revert e m1 m2 V a Hm Hty.
  induction p as [c | pf IHf pa IHa | pf IHf];
    intros e m1 m2 V a Hm Hty; simpl in *.
  - destruct a.
  - destruct e; simpl in Hm; try contradiction.
    destruct Hm as [Hmf [ls2 Hma]].
    destruct (VHasType_app_inv Hwf HG Hty) as [A0 [B0 [Hf Ha]]].
    destruct a as [xf | xa].
    + exact (IHf _ _ _ _ xf Hmf Hf).
    + exact (IHa _ _ _ _ xa Hma Ha).
  - destruct e; simpl in Hm; try contradiction.
    destruct Hm as [-> Hmf].
    destruct (VHasType_app_inv Hwf HG Hty) as [A0 [B0 [Hf Ha]]].
    destruct a as [xf |].
    + exact (IHf _ _ _ _ xf Hmf Hf).
    + exists A0; exact Ha.
Qed.

(* NormalEq: Equivalence on normal/neutral forms up to universes, eta, and
   proof irrelevance (ChurchRosser.lean lines 81-465) *)

Inductive VNormalEq (env : VEnv) (U : nat) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VN_refl : forall G e A,
    VHasType env U G e A ->
    VNormalEq env U G e e
| VN_sortDF : forall G l1 l2,
    vlevel_wf U l1 ->
    vlevel_wf U l2 ->
    vlevel_equiv l1 l2 ->
    VNormalEq env U G (VSort l1) (VSort l2)
| VN_constDF : forall G c ci ls ls',
    venv_constants env c = Some ci ->
    Forall (vlevel_wf U) ls ->
    Forall (vlevel_wf U) ls' ->
    List.length ls = vc_uvars ci ->
    Forall2 vlevel_equiv ls ls' ->
    VNormalEq env U G (VConst c ls) (VConst c ls')
| VN_appDF : forall G f1 f2 a1 a2 A B,
    VHasType env U G f1 (VForallE A B) ->
    VHasType env U G f2 (VForallE A B) ->
    VHasType env U G a1 A ->
    VHasType env U G a2 A ->
    VNormalEq env U G f1 f2 ->
    VNormalEq env U G a1 a2 ->
    VNormalEq env U G (VApp f1 a1) (VApp f2 a2)
| VN_lamDF : forall G A A1 A2 body1 body2 u,
    VIsDefEq env U G A A1 (VSort u) ->
    VIsDefEq env U G A A2 (VSort u) ->
    VNormalEq env U (A :: G) body1 body2 ->
    VNormalEq env U G (VLam A1 body1) (VLam A2 body2)
| VN_forallEDF : forall G A A1 A2 B1 B2 u v,
    VIsDefEq env U G A A1 (VSort u) ->
    VNormalEq env U G A1 A2 ->
    VHasType env U (A :: G) B1 (VSort v) ->
    VNormalEq env U (A :: G) B1 B2 ->
    VNormalEq env U G (VForallE A1 B1) (VForallE A2 B2)
| VN_etaL : forall G e' A B e,
    VHasType env U G e' (VForallE A B) ->
    VNormalEq env U (A :: G) e (VApp (vlift e') (VBVar 0)) ->
    VNormalEq env U G (VLam A e) e'
| VN_etaR : forall G e' A B e,
    VHasType env U G e' (VForallE A B) ->
    VNormalEq env U (A :: G) (VApp (vlift e') (VBVar 0)) e ->
    VNormalEq env U G e' (VLam A e)
| VN_proofIrrel : forall G p h h',
    VHasType env U G p (VSort VLZero) ->
    VHasType env U G h p ->
    VHasType env U G h' p ->
    VNormalEq env U G h h'.

Arguments VN_sortDF {env U} G {l1 l2} _ _ _.
Arguments VN_constDF {env U G c ci ls ls'} _ _ _ _ _.

Theorem VNormalEq_defeq env U G e1 e2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VIsDefEqU env U G e1 e2.
Proof.
  intros Hwf Hinj HG H.
  revert HG.
  induction H as
    [ G e A h
    | G l1 l2 h1 h2 h3
    | G c ci ls ls' h1 h2 h3 h4 h5
    | G f1 f2 a1 a2 A B hf1 hf2 ha1 ha2 _ ih1 _ ih2
    | G A A1 A2 b1 b2 u hA1 hA2 _ ihB
    | G A A1 A2 B1 B2 u v hA1 _ ihA hB1 _ ihB
    | G e' A B e h1 _ ih
    | G e' A B e h1 _ ih
    | G p h h' h1 h2 h3 ];
    intros HG.
  - exists A; exact h.
  - exists (VSort (VLSucc l1)); apply VDF_sortDF; assumption.
  - exists (vinstL ls (vc_type ci)); eapply VDF_constDF; eassumption.
  - exists (vinst0 B a1).
    eapply VDF_appDF.
    + exact (VIsDefEqU_of_l Hwf Hinj HG (ih1 HG) hf1).
    + exact (VIsDefEqU_of_l Hwf Hinj HG (ih2 HG) ha1).
  - assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VIsDefEq_refl_l hA1)]).
    destruct (ihB HG') as [B hB].
    exists (VForallE A B).
    eapply VDF_trans.
    + apply VDF_symm. exact (VDF_lamDF hA1 (VDF_symm hB)).
    + exact (VDF_lamDF hA2 (VIsDefEq_refl_r hB)).
  - assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VIsDefEq_refl_l hA1)]).
    exists (VSort (VLIMax u v)).
    eapply VDF_trans.
    + apply VDF_symm. exact (VDF_forallEDF hA1 hB1).
    + exact (VDF_forallEDF (VIsDefEq_transU_l Hwf Hinj HG hA1 (ihA HG))
                           (VIsDefEqU_of_l Hwf Hinj HG' (ihB HG') hB1)).
  - destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG h1)) as [[u hA] _].
    assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact hA]).
    destruct (ih HG') as [C he].
    exists (VForallE A B).
    exact (VIsDefEq_transU_r Hwf Hinj HG (ex_intro _ _ (VDF_lamDF hA he)) (VDF_eta h1)).
  - destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG h1)) as [[u hA] _].
    assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact hA]).
    destruct (ih HG') as [C he].
    exists (VForallE A B).
    exact (VIsDefEq_transU_l Hwf Hinj HG (VDF_symm (VDF_eta h1)) (ex_intro _ _ (VDF_lamDF hA he))).
  - exists p; exact (VDF_proofIrrel h1 h2 h3).
Qed.

Theorem VNormalEq_symm env U G e1 e2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VNormalEq env U G e2 e1.
Proof.
  intros Hwf Hinj HG H.
  revert HG.
  induction H as
    [ G e A h
    | G l1 l2 h1 h2 h3
    | G c ci ls ls' h1 h2 h3 h4 h5
    | G f1 f2 a1 a2 A B h1 h2 h3 h4 _ ih1 _ ih2
    | G A A1 A2 b1 b2 u h1 h2 _ ih1
    | G A A1 A2 B1 B2 u v h1 h2 ih1 h4 h5 ih2
    | G e' A B e h1 _ ih
    | G e' A B e h1 _ ih
    | G p h h' h1 h2 h3 ];
    intros HG.
  - exact (VN_refl h).
  - exact (VN_sortDF G h2 h1 (vlevel_equiv_symm h3)).
  - eapply VN_constDF; [exact h1 | exact h3 | exact h2 | | exact (Forall2_vlevel_equiv_symm h5)].
    rewrite <- (Forall2_length_eq h5); exact h4.
  - exact (VN_appDF h2 h1 h4 h3 (ih1 HG) (ih2 HG)).
  - exact (VN_lamDF h2 h1 (ih1 (conj HG (ex_intro _ u (VIsDefEq_refl_l h1))))).
  - assert (HG' : VCtxWF env U (A :: G))
      by (split; [exact HG | exists u; exact (VIsDefEq_refl_l h1)]).
    exact (VN_forallEDF
             (VIsDefEq_transU_l Hwf Hinj HG h1 (VNormalEq_defeq Hwf Hinj HG h2))
             (ih1 HG)
             (VHasType_defeqU_l Hwf Hinj HG' (VNormalEq_defeq Hwf Hinj HG' h5) h4)
             (ih2 HG')).
  - destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG h1)) as [hA _].
    exact (VN_etaR h1 (ih (conj HG hA))).
  - destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG h1)) as [hA _].
    exact (VN_etaL h1 (ih (conj HG hA))).
  - exact (VN_proofIrrel h1 h3 h2).
Qed.

Theorem VNormalEq_weakN env U n k G G' e1 e2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VNormalEq env U G e1 e2 ->
  VNormalEq env U G' (vliftN n k e1) (vliftN n k e2).
Proof.
  intros Hwf W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert k G' W.
  induction H; intros k G' W; simpl.
  - exact (VN_refl (VIsDefEq_weakN Hcl H W)).
  - exact (VN_sortDF G' H H0 H1).
  - eapply VN_constDF; eassumption.
  - exact (VN_appDF (VIsDefEq_weakN Hcl H W) (VIsDefEq_weakN Hcl H0 W)
                    (VIsDefEq_weakN Hcl H1 W) (VIsDefEq_weakN Hcl H2 W)
                    (IHVNormalEq1 _ _ W) (IHVNormalEq2 _ _ W)).
  - exact (VN_lamDF (VIsDefEq_weakN Hcl H W) (VIsDefEq_weakN Hcl H0 W)
                    (IHVNormalEq _ _ (VCtxLiftN_succ A W))).
  - exact (VN_forallEDF (VIsDefEq_weakN Hcl H W) (IHVNormalEq1 _ _ W)
                        (VIsDefEq_weakN Hcl H1 (VCtxLiftN_succ A W))
                        (IHVNormalEq2 _ _ (VCtxLiftN_succ A W))).
  - eapply VN_etaL; [exact (VIsDefEq_weakN Hcl H W) |].
    pose proof (IHVNormalEq (S k) (vliftN n k A :: G') (VCtxLiftN_succ A W)) as ih.
    simpl in ih. rewrite <- vlift_vliftN_succ in ih. exact ih.
  - eapply VN_etaR; [exact (VIsDefEq_weakN Hcl H W) |].
    pose proof (IHVNormalEq (S k) (vliftN n k A :: G') (VCtxLiftN_succ A W)) as ih.
    simpl in ih. rewrite <- vlift_vliftN_succ in ih. exact ih.
  - exact (VN_proofIrrel (VIsDefEq_weakN Hcl H W)
                         (VIsDefEq_weakN Hcl H0 W)
                         (VIsDefEq_weakN Hcl H1 W)).
Qed.

Theorem VNormalEq_instN env U G0 e0 A0 k G1 G e1 e2 :
  VEnvWF env ->
  VHasType env U G0 e0 A0 ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VNormalEq env U G1 e1 e2 ->
  VNormalEq env U G (vinst e1 e0 k) (vinst e2 e0 k).
Proof.
  intros Hwf He0 W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert k G W.
  induction H; intros k G' W; simpl.
  - exact (VN_refl (VIsDefEq_instN Hcl He0 H W)).
  - exact (VN_sortDF G' H H0 H1).
  - eapply VN_constDF; eassumption.
  - pose proof (VIsDefEq_instN Hcl He0 H W) as h1; simpl in h1.
    pose proof (VIsDefEq_instN Hcl He0 H0 W) as h2; simpl in h2.
    exact (VN_appDF h1 h2
                    (VIsDefEq_instN Hcl He0 H1 W) (VIsDefEq_instN Hcl He0 H2 W)
                    (IHVNormalEq1 _ _ W) (IHVNormalEq2 _ _ W)).
  - exact (VN_lamDF (VIsDefEq_instN Hcl He0 H W) (VIsDefEq_instN Hcl He0 H0 W)
                    (IHVNormalEq _ _ (VCtxInstN_succ A W))).
  - exact (VN_forallEDF (VIsDefEq_instN Hcl He0 H W) (IHVNormalEq1 _ _ W)
                        (VIsDefEq_instN Hcl He0 H1 (VCtxInstN_succ A W))
                        (IHVNormalEq2 _ _ (VCtxInstN_succ A W))).
  - pose proof (VIsDefEq_instN Hcl He0 H W) as h1; simpl in h1.
    eapply VN_etaL; [exact h1 |].
    pose proof (IHVNormalEq (S k) _ (VCtxInstN_succ A W)) as ih.
    simpl in ih. rewrite vinst_vlift_succ in ih. exact ih.
  - pose proof (VIsDefEq_instN Hcl He0 H W) as h1; simpl in h1.
    eapply VN_etaR; [exact h1 |].
    pose proof (IHVNormalEq (S k) _ (VCtxInstN_succ A W)) as ih.
    simpl in ih. rewrite vinst_vlift_succ in ih. exact ih.
  - exact (VN_proofIrrel (VIsDefEq_instN Hcl He0 H W)
                         (VIsDefEq_instN Hcl He0 H0 W)
                         (VIsDefEq_instN Hcl He0 H1 W)).
Qed.

Theorem VNormalEq_instN_r env U G0 e0 e0' A0 k G1 G e A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G1 ->
  VHasType env U G0 e0 A0 ->
  VNormalEq env U G0 e0 e0' ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VHasType env U G1 e A ->
  VNormalEq env U G (vinst e e0 k) (vinst e e0' k).
Proof.
  intros Hwf Hinj HG1 H0 Hnorm0 W Hty.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert G1 G k A HG1 W Hty.
  induction e as [i | u | c ls | fn IHf arg IHa | dom IHA body IHb | dom IHA cod IHB];
    intros G1 G k A HG1 W Hty; simpl.
  - destruct (VHasType_bvar_inv Hwf HG1 Hty) as [ty Hlk].
    clear Hty HG1 A.
    revert i ty Hlk.
    induction W as [| k G1 G C W IHW]; intros i ty Hlk.
    + inversion Hlk as [A' G' Heq1 Heq2 | A' G' j B' Hj Heq1 Heq2]; subst; simpl.
      * unfold vinstVar; simpl. rewrite !vliftN_zero. exact Hnorm0.
      * unfold vinstVar; simpl. exact (VN_refl (VDF_bvar Hj)).
    + inversion Hlk as [A' G' Heq1 Heq2 | A' G' j B' Hj Heq1 Heq2]; subst.
      * unfold vinstVar; simpl. exact (VN_refl (VDF_bvar (VLookupZero _ _))).
      * rewrite !vinstVar_succ.
        exact (VNormalEq_weakN Hwf (VCtxLiftN_one _ _) (IHW j B' Hj)).
  - exact (VN_refl (VHasType_sort env U G u (VIsDefEq_sort_inv_l Hty))).
  - destruct (VHasType_const_inv Hwf HG1 Hty) as [ci [Hc [Hls Hlen]]].
    exact (VN_refl (VHasType_const G Hc Hls Hlen)).
  - destruct (VHasType_app_inv Hwf HG1 Hty) as [A1 [B1 [hf1 ha1]]].
    pose proof (IHf _ _ _ _ HG1 W hf1) as ih1.
    pose proof (IHa _ _ _ _ HG1 W ha1) as ih2.
    pose proof (VHasType_instN Hcl W hf1 H0) as hf. simpl in hf.
    pose proof (VHasType_instN Hcl W ha1 H0) as ha.
    destruct (VCtxInstN_wf Hcl H0 W HG1) as [_ HG].
    exact (VN_appDF hf (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG ih1) hf)
                    ha (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG ih2) ha)
                    ih1 ih2).
  - destruct (VHasType_lam_inv Hwf HG1 Hty) as [[u1 h1] [B1 h2]].
    pose proof (VHasType_instN Hcl W h1 H0) as hA. simpl in hA.
    destruct (VCtxInstN_wf Hcl H0 W HG1) as [_ HG].
    pose proof (IHA _ _ _ _ HG1 W h1) as ih1.
    exact (VN_lamDF hA (VIsDefEqU_of_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG ih1) hA)
                    (IHb _ _ _ _ (vctx_cons HG1 h1) (VCtxInstN_succ dom W) h2)).
  - destruct (VHasType_forallE_inv Hwf Hty) as [[u1 h1] [v1 h2]].
    pose proof (VHasType_instN Hcl W h1 H0) as hA. simpl in hA.
    pose proof (VHasType_instN Hcl (VCtxInstN_succ dom W) h2 H0) as hB. simpl in hB.
    exact (VN_forallEDF hA (IHA _ _ _ _ HG1 W h1) hB
                        (IHB _ _ _ _ (vctx_cons HG1 h1) (VCtxInstN_succ dom W) h2)).
Qed.

Theorem VNormalEq_defeqDFC env U G0 G1 G2 e1 e2 :
  VEnvWF env ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VNormalEq env U G1 e1 e2 ->
  VNormalEq env U G2 e1 e2.
Proof.
  intros Hwf HG0 W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert G2 W.
  induction H; intros G2 W.
  - exact (VN_refl (VIsDefEq_defeqDFC Hcl W H)).
  - exact (VN_sortDF G2 H H0 H1).
  - eapply VN_constDF; eassumption.
  - exact (VN_appDF (VIsDefEq_defeqDFC Hcl W H) (VIsDefEq_defeqDFC Hcl W H0)
                    (VIsDefEq_defeqDFC Hcl W H1) (VIsDefEq_defeqDFC Hcl W H2)
                    (IHVNormalEq1 _ W) (IHVNormalEq2 _ W)).
  - exact (VN_lamDF (VIsDefEq_defeqDFC Hcl W H) (VIsDefEq_defeqDFC Hcl W H0)
                    (IHVNormalEq _ (VIsDefEqCtx_succ W (VIsDefEq_refl_l H)))).
  - exact (VN_forallEDF (VIsDefEq_defeqDFC Hcl W H) (IHVNormalEq1 _ W)
                        (VIsDefEq_defeqDFC Hcl (VIsDefEqCtx_succ W (VIsDefEq_refl_l H)) H1)
                        (IHVNormalEq2 _ (VIsDefEqCtx_succ W (VIsDefEq_refl_l H)))).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG1 H)) as [[u hA] _].
    exact (VN_etaL (VIsDefEq_defeqDFC Hcl W H) (IHVNormalEq _ (VIsDefEqCtx_succ W hA))).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG1 H)) as [[u hA] _].
    exact (VN_etaR (VIsDefEq_defeqDFC Hcl W H) (IHVNormalEq _ (VIsDefEqCtx_succ W hA))).
  - exact (VN_proofIrrel (VIsDefEq_defeqDFC Hcl W H)
                         (VIsDefEq_defeqDFC Hcl W H0)
                         (VIsDefEq_defeqDFC Hcl W H1)).
Qed.

Theorem VNormalEq_defeq_l env U G A A' u e1 e2 :
  VEnvWF env ->
  VCtxWF env U G ->
  VIsDefEq env U G A A' (VSort u) ->
  VNormalEq env U (A :: G) e1 e2 ->
  VNormalEq env U (A' :: G) e1 e2.
Proof.
  intros Hwf HG W H.
  exact (VNormalEq_defeqDFC Hwf HG (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) W) H).
Qed.

Theorem VNormalEq_weakN_inv_DFC env U n k G G0 G1 G2 e1 e2 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G0 ->
  VCtxLiftN n k G G2 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VNormalEq env U G1 (vliftN n k e1) (vliftN n k e2) ->
  VNormalEq env U G e1 e2.
Proof.
  intros Hwf Hinj HG0 W W2 H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  remember (vliftN n k e1) as e1' eqn:Heq1.
  remember (vliftN n k e2) as e2' eqn:Heq2.
  revert G G2 e1 e2 k W W2 Heq1 Heq2.
  induction H as
    [ G1 e A h
    | G1 l1 l2 h1 h2 h3
    | G1 c ci ls ls' h1 h2 h3 h4 h5
    | G1 f1' f2' a1' a2' A' B' h1 h2 h3 h4 _ ih1 _ ih2
    | G1 A' A1' A2' b1' b2' u h1 h2 _ ih1
    | G1 A' A1' A2' B1' B2' u v h1 _ ih1 h3 _ ih2
    | G1 e2' A' B' b1' h1 _ ih
    | G1 e1' A' B' b2' h1 _ ih
    | G1 p x1 x2 h1 h2 h3 ];
    intros G G2 e1 e2 k W W2 Heq1 Heq2.
  - subst e. apply vliftN_inj in Heq2; subst e2.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl W2)) as HG2.
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG2 W)
                (ex_intro _ A (VIsDefEq_defeqDFC Hcl W2 h))) as [B h'].
    exact (VN_refl h').
  - destruct e1; simpl in Heq1; try discriminate.
    destruct e2; simpl in Heq2; try discriminate.
    inversion Heq1; inversion Heq2; subst.
    exact (VN_sortDF G h1 h2 h3).
  - destruct e1; simpl in Heq1; try discriminate.
    destruct e2; simpl in Heq2; try discriminate.
    inversion Heq1; inversion Heq2; subst.
    eapply VN_constDF; eassumption.
  - destruct e1; simpl in Heq1; try discriminate.
    destruct e2; simpl in Heq2; try discriminate.
    inversion Heq1; inversion Heq2; subst.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h1) as h1'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h2) as h2'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h3) as h3'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h4) as h4'.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl W2)) as HG2.
    pose proof (VCtxWF_weakN_inv Hwf Hinj W HG2) as HG.
    destruct (VExprWF_app_inv Hwf HG
                (proj1 (@VExprWF_weakN_iff env U n k G G2 (VApp e1_1 e1_2) Hinj HG2 W)
                       (ex_intro _ _ (VHasType_app h1' h3'))))
      as [Al [Bl [l1 l2]]].
    destruct (VExprWF_app_inv Hwf HG
                (proj1 (@VExprWF_weakN_iff env U n k G G2 (VApp e2_1 e2_2) Hinj HG2 W)
                       (ex_intro _ _ (VHasType_app h2' h4'))))
      as [Ar [Br [r1 r2]]].
    pose proof (proj1 (@VIsDefEqU_weakN_iff env U n k G G2 (VForallE Al Bl) (VForallE Ar Br) Hinj HG2 W)
                  (VIsDefEqU_trans Hwf Hinj HG2
                    (VIsDefEq_uniqU Hwf Hinj HG2 (VIsDefEq_weakN Hcl l1 W) h1')
                    (VIsDefEq_uniqU Hwf Hinj HG2 h2' (VIsDefEq_weakN Hcl r1 W))))
      as Hpi_eq.
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG Hpi_eq) as [[u0 h5] _].
    exact (VN_appDF (VHasType_defeqU_r Hwf Hinj HG Hpi_eq l1) r1
                    (VHasType_defeqU_r Hwf Hinj HG (ex_intro _ _ h5) l2) r2
                    (ih1 _ _ _ _ _ W W2 eq_refl eq_refl)
                    (ih2 _ _ _ _ _ W W2 eq_refl eq_refl)).
  - destruct e1; simpl in Heq1; try discriminate.
    destruct e2; simpl in Heq2; try discriminate.
    inversion Heq1; inversion Heq2; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl W2)) as HG2.
    pose proof (proj1 (@VIsDefEq_weakN_iff env U n k G G2 e2_1 e1_1 (VSort u) Hwf Hinj HG2 W)
                  (VIsDefEq_defeqDFC Hcl W2 (VDF_trans (VDF_symm h2) h1))) as hA_eq.
    exact (VN_lamDF hA_eq (VIsDefEq_refl_l hA_eq)
                    (ih1 _ _ _ _ _ (VCtxLiftN_succ e2_1 W) (VIsDefEqCtx_succ W2 h2) eq_refl eq_refl)).
  - destruct e1; simpl in Heq1; try discriminate.
    destruct e2; simpl in Heq2; try discriminate.
    inversion Heq1; inversion Heq2; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl (VIsDefEqCtx_succ W2 h1))) as HG2'.
    pose proof (proj1 (@VHasType_weakN_iff env U n (S k) (e1_1 :: G) (vliftN n k e1_1 :: G2) e1_2 (VSort v) Hwf Hinj HG2' (VCtxLiftN_succ e1_1 W))
                  (VIsDefEq_defeqDFC Hcl (VIsDefEqCtx_succ W2 h1) h3)) as h4.
    pose proof (proj1 (@VHasType_weakN_iff env U n k G G2 e1_1 (VSort u) Hwf Hinj (proj1 HG2') W)
                  (VIsDefEq_defeqDFC Hcl W2 (VIsDefEq_refl_r h1))) as hA.
    exact (VN_forallEDF hA (ih1 _ _ _ _ _ W W2 eq_refl eq_refl)
                        h4 (ih2 _ _ _ _ _ (VCtxLiftN_succ e1_1 W) (VIsDefEqCtx_succ W2 h1) eq_refl eq_refl)).
  - destruct e1; simpl in Heq1; try discriminate.
    inversion Heq1; subst A' b1' e2'.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W2) as HG1.
    destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG1 h1)) as [[u hA] [v hB]].
    pose proof (VIsDefEq_defeqDFC Hcl W2 h1) as h1'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 hA) as hA'.
    pose proof (VHasType_app (VIsDefEq_weak (vliftN n k e1_1) Hcl h1')
                             (VDF_bvar (VLookupZero (vliftN n k e1_1) G2))) as Happ.
    unfold vinst0 in Happ. rewrite vinst_vliftN_bvar0 in Happ.
    rewrite vlift_vliftN_succ in Happ.
    change (VApp (vliftN n (S k) (vlift e2)) (VBVar 0))
      with (vliftN n (S k) (VApp (vlift e2) (VBVar 0))) in Happ.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl (VIsDefEqCtx_succ W2 hA))) as HG2'.
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG2' (VCtxLiftN_succ e1_1 W))
                (ex_intro _ B' Happ)) as [C hC].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG2' Happ
                (VIsDefEq_weakN Hcl hC (VCtxLiftN_succ e1_1 W))) as [w hu].
    pose proof (proj1 (@VHasType_weakN_iff env U n k G G2 e2 (VForallE e1_1 C) Hwf Hinj (proj1 HG2') W)
                  (VDF_defeqDF (VDF_forallEDF hA' hu) h1')) as he2.
    apply (VN_etaL he2).
    refine (ih _ _ _ _ _ (VCtxLiftN_succ e1_1 W) (VIsDefEqCtx_succ W2 hA) eq_refl _).
    simpl. rewrite vlift_vliftN_succ. reflexivity.
  - destruct e2; simpl in Heq2; try discriminate.
    inversion Heq2; subst A' b2' e1'.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W2) as HG1.
    destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG1 h1)) as [[u hA] [v hB]].
    pose proof (VIsDefEq_defeqDFC Hcl W2 h1) as h1'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 hA) as hA'.
    pose proof (VHasType_app (VIsDefEq_weak (vliftN n k e2_1) Hcl h1')
                             (VDF_bvar (VLookupZero (vliftN n k e2_1) G2))) as Happ.
    unfold vinst0 in Happ. rewrite vinst_vliftN_bvar0 in Happ.
    rewrite vlift_vliftN_succ in Happ.
    change (VApp (vliftN n (S k) (vlift e1)) (VBVar 0))
      with (vliftN n (S k) (VApp (vlift e1) (VBVar 0))) in Happ.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl (VIsDefEqCtx_succ W2 hA))) as HG2'.
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG2' (VCtxLiftN_succ e2_1 W))
                (ex_intro _ B' Happ)) as [C hC].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG2' Happ
                (VIsDefEq_weakN Hcl hC (VCtxLiftN_succ e2_1 W))) as [w hu].
    pose proof (proj1 (@VHasType_weakN_iff env U n k G G2 e1 (VForallE e2_1 C) Hwf Hinj (proj1 HG2') W)
                  (VDF_defeqDF (VDF_forallEDF hA' hu) h1')) as he1.
    apply (VN_etaR he1).
    refine (ih _ _ _ _ _ (VCtxLiftN_succ e2_1 W) (VIsDefEqCtx_succ W2 hA) _ eq_refl).
    simpl. rewrite vlift_vliftN_succ. reflexivity.
  - subst.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h1) as h1'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h2) as h2'.
    pose proof (VIsDefEq_defeqDFC Hcl W2 h3) as h3'.
    pose proof (VIsDefEqCtx_wf Hcl HG0 (VIsDefEqCtx_symm Hcl W2)) as HG2.
    destruct (proj1 (VIsDefEqU_weakN_iff Hinj HG2 W) (ex_intro _ p h2')) as [p0 hp0].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG2 h2' (VIsDefEq_weakN Hcl hp0 W)) as [w hw].
    exact (VN_proofIrrel
             (proj1 (@VHasType_weakN_iff env U n k G G2 p0 (VSort VLZero) Hwf Hinj HG2 W)
                    (VHasType_defeqU_l Hwf Hinj HG2 (ex_intro _ _ hw) h1'))
             (proj1 (@VHasType_weakN_iff env U n k G G2 e1 p0 Hwf Hinj HG2 W)
                    (VDF_defeqDF hw h2'))
             (proj1 (@VHasType_weakN_iff env U n k G G2 e2 p0 Hwf Hinj HG2 W)
                    (VDF_defeqDF hw h3'))).
Qed.

Theorem VNormalEq_weakN_iff env U n k G G' {e1 e2} :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  (VNormalEq env U G' (vliftN n k e1) (vliftN n k e2) <->
   VNormalEq env U G e1 e2).
Proof.
  intros Hwf Hinj HG' W. split.
  - intros H. exact (VNormalEq_weakN_inv_DFC Hwf Hinj HG' W (VIsDefEqCtx_zero env U G') H).
  - intros H. exact (VNormalEq_weakN Hwf W H).
Qed.

Fixpoint vnorm_meas (e : VExpr) : nat :=
  match e with
  | VApp f a | VForallE f a => vnorm_meas f + vnorm_meas a + 1
  | VBVar _ | VConst _ _ | VSort _ => 0
  | VLam A e => vnorm_meas A + vnorm_meas e + 3
  end.

Lemma vnorm_meas_vliftN n k e :
  vnorm_meas (vliftN n k e) = vnorm_meas e.
Proof.
  revert k; induction e; intros k; simpl; auto.
Qed.

Lemma vnorm_meas_vlift e :
  vnorm_meas (vlift e) = vnorm_meas e.
Proof.
  apply vnorm_meas_vliftN.
Qed.

Theorem VNormalEq_trans env U G e1 e2 e3 :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VNormalEq env U G e2 e3 ->
  VNormalEq env U G e1 e3.
Proof.
  intros Hwf Hinj HG H1 H2.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  assert (Hmain : forall m G e1 e2 e3,
    vnorm_meas e1 + vnorm_meas e2 + vnorm_meas e3 <= m ->
    VCtxWF env U G ->
    VNormalEq env U G e1 e2 ->
    VNormalEq env U G e2 e3 ->
    VNormalEq env U G e1 e3).
  { apply (@nat_strong_ind (fun m =>
      forall G e1 e2 e3,
        vnorm_meas e1 + vnorm_meas e2 + vnorm_meas e3 <= m ->
        VCtxWF env U G ->
        VNormalEq env U G e1 e2 ->
        VNormalEq env U G e2 e3 ->
        VNormalEq env U G e1 e3)).
    intros m IH.
    assert (HetaR : forall G0 d1 d2 A B e,
      vnorm_meas d1 + vnorm_meas d2 + vnorm_meas (VLam A e) <= m ->
      VCtxWF env U G0 ->
      VNormalEq env U G0 d1 d2 ->
      VHasType env U G0 d2 (VForallE A B) ->
      VNormalEq env U (A :: G0) (VApp (vlift d2) (VBVar 0)) e ->
      VNormalEq env U G0 d1 (VLam A e)).
    { intros G0 d1 d2 A B e Hm HG0 Hd12 Hr1 Hih.
      destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 Hr1)) as [[u hA] _].
      pose proof (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 Hd12)) as H21_eq.
      pose proof (VHasType_defeqU_l Hwf Hinj HG0 H21_eq Hr1) as Hd1_ty.
      apply (VN_etaR Hd1_ty).
      eapply (IH (vnorm_meas (VApp (vlift d1) (VBVar 0)) +
                  vnorm_meas (VApp (vlift d2) (VBVar 0)) + vnorm_meas e)).
      - simpl in Hm |- *. rewrite !vnorm_meas_vlift. lia.
      - apply Nat.le_refl.
      - exact (vctx_cons HG0 hA).
      - exact (VN_appDF (VIsDefEq_weak A Hcl Hd1_ty) (VIsDefEq_weak A Hcl Hr1)
                        (VDF_bvar (VLookupZero A G0)) (VDF_bvar (VLookupZero A G0))
                        (VNormalEq_weakN Hwf (VCtxLiftN_one A G0) Hd12)
                        (VN_refl (VDF_bvar (VLookupZero A G0)))).
      - exact Hih. }
    intros G0 d1 d2 d3 Hm HG0 Hd12 Hd23.
    destruct Hd12 as
      [ G0 d h
      | G0 l1 l2 l_wf1 l_wf2 l_eq
      | G0 c ci ls1 ls2 l1 l2 l3 l4 l5
      | G0 f1 f2 a1 a2 A B l1 l2 l3 l4 l5 l6
      | G0 A A1 A2 b1 b2 u l1 l2 l3
      | G0 A A1 A2 B1 B2 u v l1 l2 l3 l4
      | G0 d2 A B e l1 ihl
      | G0 d1 A B e l1 ihl
      | G0 p h1 h2 l1 l2 l3 ].
    - (* refl on left *)
      exact Hd23.
    - (* sortDF on left *)
      inversion Hd23 as
        [ G' d' A' hr | G' r1 r2 rw1 rw2 req | | | | |
        | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_sortDF G0 l_wf1 l_wf2 l_eq).
      + exact (VN_sortDF G0 l_wf1 rw2 (vlevel_equiv_trans l_eq req)).
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_sortDF G0 l_wf1 l_wf2 l_eq) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_sortDF G0 l_wf1 l_wf2 l_eq))) p2) p3).
    - (* constDF on left *)
      inversion Hd23 as
        [ G' d' A' hr | | G' c' ci' rs1 rs2 r1 r2 r3 r4 r5 | | | |
        | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_constDF l1 l2 l3 l4 l5).
      + exact (VN_constDF l1 l2 r3 l4 (Forall2_vlevel_equiv_trans l5 r5)).
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_constDF l1 l2 l3 l4 l5) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_constDF l1 l2 l3 l4 l5))) p2) p3).
    - (* appDF on left *)
      inversion Hd23 as
        [ G' d' A' hr | | | G' g2 f3 b2 a3 A' B' r1 r2 r3 r4 r5 r6 | | |
        | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_appDF l1 l2 l3 l4 l5 l6).
      + exact (VN_appDF l1
                 (VIsDefEqU_defeqDF Hwf Hinj HG0 (VIsDefEq_uniqU Hwf Hinj HG0 r1 l2) r2)
                 l3
                 (VIsDefEqU_defeqDF Hwf Hinj HG0 (VIsDefEq_uniqU Hwf Hinj HG0 r3 l4) r4)
                 (IH (vnorm_meas f1 + vnorm_meas f2 + vnorm_meas f3)
                     ltac:(simpl in Hm; lia) _ _ _ _ (Nat.le_refl _) HG0 l5 r5)
                 (IH (vnorm_meas a1 + vnorm_meas a2 + vnorm_meas a3)
                     ltac:(simpl in Hm; lia) _ _ _ _ (Nat.le_refl _) HG0 l6 r6)).
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_appDF l1 l2 l3 l4 l5 l6) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_appDF l1 l2 l3 l4 l5 l6))) p2) p3).
    - (* lamDF on left *)
      inversion Hd23 as
        [ G' d' A' hr | | | | G' A' A2' A3 b2' b3 u' r1 r2 r3 |
        | G' d3' A' B' e' r1 ihr | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_lamDF l1 l2 l3).
      + pose proof (VIsDefEq_trans_r Hwf Hinj HG0 r1 (VDF_symm l2)) as aa.
        exact (VN_lamDF l1 (VIsDefEq_trans_l Hwf Hinj HG0 (VDF_symm aa) r2)
                 (IH (vnorm_meas b1 + vnorm_meas b2 + vnorm_meas b3)
                     ltac:(simpl in Hm; lia) _ _ _ _ (Nat.le_refl _)
                     (vctx_cons HG0 (VIsDefEq_refl_l l1))
                     l3 (VNormalEq_defeq_l Hwf HG0 aa r3))).
      + destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 r1)) as [_ [v hB]].
        pose proof (VDF_trans (VDF_symm l2) l1) as HeqA.
        apply (VN_etaL (VDF_defeqDF (VDF_forallEDF HeqA hB) r1)).
        exact (IH (vnorm_meas b1 + vnorm_meas b2 + vnorm_meas (VApp (vlift d3) (VBVar 0)))
                  ltac:(simpl in Hm |- *; rewrite vnorm_meas_vlift; lia)
                  _ _ _ _ (Nat.le_refl _)
                  (vctx_cons HG0 (VIsDefEq_refl_r l1))
                  (VNormalEq_defeq_l Hwf HG0 l1 l3)
                  (VNormalEq_defeq_l Hwf HG0 HeqA ihr)).
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_lamDF l1 l2 l3) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_lamDF l1 l2 l3))) p2) p3).
    - (* forallEDF on left *)
      inversion Hd23 as
        [ G' d' A' hr | | | | | G' A' A2' A3 B2' B3 u' v' r1 r2 r3 r4 |
        | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_forallEDF l1 l2 l3 l4).
      + pose proof (VIsDefEq_trans_l Hwf Hinj HG0
                      (VIsDefEq_transU_l Hwf Hinj HG0 r1 (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 l2)))
                      (VDF_symm l1)) as rA_eq.
        exact (VN_forallEDF l1
                 (IH (vnorm_meas A1 + vnorm_meas A2 + vnorm_meas A3)
                     ltac:(simpl in Hm; lia) _ _ _ _ (Nat.le_refl _) HG0 l2 r2)
                 l3
                 (IH (vnorm_meas B1 + vnorm_meas B2 + vnorm_meas B3)
                     ltac:(simpl in Hm; lia) _ _ _ _ (Nat.le_refl _)
                     (vctx_cons HG0 (VIsDefEq_refl_l l1))
                     l4 (VNormalEq_defeq_l Hwf HG0 rA_eq r4))).
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_forallEDF l1 l2 l3 l4) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_forallEDF l1 l2 l3 l4))) p2) p3).
    - (* etaL on left *)
      destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 l1)) as [[u hA] _].
      pose proof (VNormalEq_defeq Hwf Hinj HG0 Hd23) as H23_eq.
      apply (VN_etaL (VHasType_defeqU_l Hwf Hinj HG0 H23_eq l1)).
      exact (IH (vnorm_meas e + vnorm_meas (VApp (vlift d2) (VBVar 0)) +
                 vnorm_meas (VApp (vlift d3) (VBVar 0)))
                ltac:(simpl in Hm |- *; rewrite !vnorm_meas_vlift; lia)
                _ _ _ _ (Nat.le_refl _)
                (vctx_cons HG0 hA)
                ihl
                (VN_appDF (VIsDefEq_weak A Hcl l1)
                          (VIsDefEq_weak A Hcl (VHasType_defeqU_l Hwf Hinj HG0 H23_eq l1))
                          (VDF_bvar (VLookupZero A G0)) (VDF_bvar (VLookupZero A G0))
                          (VNormalEq_weakN Hwf (VCtxLiftN_one A G0) Hd23)
                          (VN_refl (VDF_bvar (VLookupZero A G0))))).
    - (* etaR on left *)
      inversion Hd23 as
        [ G' d' A' hr | | | | G' A' A1' A2 b1' b2 u r1 r2 r3 |
        | G' d3' A' B' e' r1 ihr | G' d2' A' B' e' r1 ihr | G' p' x1 x2 p1 p2 p3 ]; subst; clear Hd23.
      + exact (VN_etaR l1 ihl).
      + destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 l1)) as [_ [v hB]].
        pose proof (VDF_trans (VDF_symm r1) r2) as HeqA.
        apply (VN_etaR (VDF_defeqDF (VDF_forallEDF HeqA hB) l1)).
        exact (IH (vnorm_meas (VApp (vlift d1) (VBVar 0)) + vnorm_meas e + vnorm_meas b2)
                  ltac:(simpl in Hm |- *; rewrite vnorm_meas_vlift; lia)
                  _ _ _ _ (Nat.le_refl _)
                  (vctx_cons HG0 (VIsDefEq_refl_r r2))
                  (VNormalEq_defeq_l Hwf HG0 HeqA ihl)
                  (VNormalEq_defeq_l Hwf HG0 r2 r3)).
      + (* etaR + etaL! *)
        destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 l1)) as [[u hA] _].
        pose proof (vctx_cons HG0 hA) as HG'.
        pose proof (IH (vnorm_meas (VApp (vlift d1) (VBVar 0)) + vnorm_meas e +
                        vnorm_meas (VApp (vlift d3) (VBVar 0)))
                       ltac:(simpl in Hm |- *; rewrite !vnorm_meas_vlift; lia)
                       _ _ _ _ (Nat.le_refl _) HG' ihl ihr) as Hmid.
        inversion Hmid as
          [ G' x T hr HeqG Heql Heqr | |
          | G' g1 g2 y1 y2 A0 B0 c1 c2 c3 c4 c5 c6 HeqG Heql Heqr | | | |
          | G' p0 x1 x2 p1 p2 p3 HeqG Heql Heqr ]; subst.
        * apply vliftN_inj in Heqr; subst d3.
          exact (VN_refl r1).
        * exact (proj1 (@VNormalEq_weakN_iff env U 1 0 G0 (A :: G0) d1 d3 Hwf Hinj HG'
                          (VCtxLiftN_one A G0)) c5).
        * pose proof (VIsDefEq_sort_r Hwf HG0 hA) as Hu.
          refine (VN_proofIrrel
                    (VIsDefEqU_defeqDF Hwf Hinj HG0 _ (VHasType_forallE hA p1))
                    (VHasType_defeqU_l Hwf Hinj HG0 (ex_intro _ _ (VDF_eta l1)) (VHasType_lam hA p2))
                    (VHasType_defeqU_l Hwf Hinj HG0 (ex_intro _ _ (VDF_eta r1)) (VHasType_lam hA p3))).
          exists (VSort (VLSucc (VLIMax u VLZero))).
          apply VDF_sortDF; [simpl; auto | exact I | apply vlevel_imax_zero].
      + exact (HetaR G0 _ _ _ _ _ Hm HG0 (VN_etaR l1 ihl) r1 ihr).
      + exact (VN_proofIrrel p1 (VHasType_defeqU_l Hwf Hinj HG0
                  (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG0 (VN_etaR l1 ihl))) p2) p3).
    - (* proofIrrel on left *)
      exact (VN_proofIrrel l1 l2
               (VHasType_defeqU_l Hwf Hinj HG0 (VNormalEq_defeq Hwf Hinj HG0 Hd23) l3)). }
  exact (Hmain _ G e1 e2 e3 (Nat.le_refl _) HG H1 H2).
Qed.

Theorem VNormalEq_apply_pat env U G p (m1 : list VLevel) (m2 m2' : VMatchEnv p)
    (r : VPatternRHS p) A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  (forall a B, VHasType env U G (vpath_get m2 a) B ->
     VNormalEq env U G (vpath_get m2 a) (vpath_get m2' a)) ->
  VHasType env U G (vrhs_apply m1 m2 r) A ->
  VNormalEq env U G (vrhs_apply m1 m2 r) (vrhs_apply m1 m2' r).
Proof.
  intros Hwf Hinj HG Hih.
  revert A.
  induction r as [c Hcl | rf IHf ra IHa | path]; intros A He; simpl in *.
  - exact (VN_refl He).
  - destruct (VHasType_app_inv Hwf HG He) as [A0 [B0 [h1 h2]]].
    pose proof (IHf _ h1) as ih1.
    pose proof (IHa _ h2) as ih2.
    exact (VN_appDF h1 (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG ih1) h1)
                    h2 (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG ih2) h2)
                    ih1 ih2).
  - exact (Hih path A He).
Qed.

Lemma VEqUpToLevels_vinstL_any U ls ls' e :
  Forall (vlevel_wf U) ls ->
  Forall (vlevel_wf U) ls' ->
  Forall2 vlevel_equiv ls ls' ->
  VEqUpToLevels U (vinstL ls e) (vinstL ls' e).
Proof.
  intros Hls Hls' Heq.
  induction e as [i | u | c us | f IHf a IHa | A IHA b IHb | A IHA B IHB]; simpl.
  - apply VEUL_bvar.
  - apply VEUL_sort; [apply vlevel_inst_wf_any; exact Hls | apply vlevel_inst_wf_any; exact Hls' |].
    apply vlevel_inst_congr; [exact Heq | apply vlevel_equiv_refl].
  - apply VEUL_const; [apply Forall_vlevel_inst_wf; exact Hls | apply Forall_vlevel_inst_wf; exact Hls' |].
    apply Forall2_map_vlevel_inst_congr; exact Heq.
  - apply VEUL_app; assumption.
  - apply VEUL_lam; assumption.
  - apply VEUL_forallE; assumption.
Qed.

Lemma VEqUpToLevels_vrhs_const U c ls ls' (r : VPatternRHS (VPConst c)) :
  Forall (vlevel_wf U) ls ->
  Forall (vlevel_wf U) ls' ->
  Forall2 vlevel_equiv ls ls' ->
  VEqUpToLevels U (@vrhs_apply (VPConst c) ls tt r) (@vrhs_apply (VPConst c) ls' tt r).
Proof.
  intros Hls Hls' Heq.
  induction r as [d Hcl | f IHf a IHa | path]; simpl.
  - apply VEqUpToLevels_vinstL_any; assumption.
  - apply VEUL_app; assumption.
  - destruct path.
Qed.

Theorem VEqUpToLevels_normalEq env U G e1 e2 A :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G ->
  VEqUpToLevels U e1 e2 ->
  VHasType env U G e1 A ->
  VNormalEq env U G e1 e2.
Proof.
  intros Hwf Hinj HG Heul.
  revert G A HG.
  induction Heul as
    [ i
    | c ls ls' h1 h2 h3
    | l l' h1 h2 h3
    | f f' a a' _ IHf _ IHa
    | A1 A2 b1 b2 _ IHA _ IHb
    | A1 A2 B1 B2 _ IHA _ IHB ];
    intros G T HG Hty.
  - exact (VN_refl Hty).
  - destruct (VHasType_const_inv Hwf HG Hty) as [ci [Hc [_ Hlen]]].
    exact (VN_constDF Hc h1 h2 Hlen h3).
  - exact (VN_sortDF G h1 h2 h3).
  - destruct (VHasType_app_inv Hwf HG Hty) as [A0 [B0 [hf1 ha1]]].
    pose proof (IHf _ _ HG hf1) as nf.
    pose proof (IHa _ _ HG ha1) as na.
    exact (VN_appDF hf1 (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG nf) hf1)
                    ha1 (VHasType_defeqU_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG na) ha1)
                    nf na).
  - destruct (VHasType_lam_inv Hwf HG Hty) as [[u hA1] [B0 hb1]].
    pose proof (IHA _ _ HG hA1) as nA.
    exact (VN_lamDF hA1 (VIsDefEqU_of_l Hwf Hinj HG (VNormalEq_defeq Hwf Hinj HG nA) hA1)
                    (IHb _ _ (vctx_cons HG hA1) hb1)).
  - destruct (VHasType_forallE_inv Hwf Hty) as [[u hA1] [v hB1]].
    exact (VN_forallEDF hA1 (IHA _ _ HG hA1) hB1
                        (IHB _ _ (vctx_cons HG hA1) hB1)).
Qed.
(* ========================================================================= *)
(* 3b. Typed Parallel Reduction, Takahashi Complete Development,             *)
(*     PatternParams, and Typed Church-Rosser Confluence                     *)
(* ========================================================================= *)

Definition VPatRel : Type :=
  forall p : VPattern, (VPatternRHS p * VPatternCheck p)%type -> Prop.

Inductive VParRedT (env : VEnv) (U : nat) (Pat : VPatRel) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VPRT_bvar : forall G i,
    VParRedT env U Pat G (VBVar i) (VBVar i)
| VPRT_sort : forall G u,
    VParRedT env U Pat G (VSort u) (VSort u)
| VPRT_const : forall G c ls,
    VParRedT env U Pat G (VConst c ls) (VConst c ls)
| VPRT_app : forall G f f' a a',
    VParRedT env U Pat G f f' ->
    VParRedT env U Pat G a a' ->
    VParRedT env U Pat G (VApp f a) (VApp f' a')
| VPRT_lam : forall G A A' body body',
    VParRedT env U Pat G A A' ->
    VParRedT env U Pat (A :: G) body body' ->
    VParRedT env U Pat G (VLam A body) (VLam A' body')
| VPRT_forallE : forall G A A' B B',
    VParRedT env U Pat G A A' ->
    VParRedT env U Pat (A :: G) B B' ->
    VParRedT env U Pat G (VForallE A B) (VForallE A' B')
| VPRT_beta : forall G A e1 e1' e2 e2',
    VParRedT env U Pat (A :: G) e1 e1' ->
    VParRedT env U Pat G e2 e2' ->
    VParRedT env U Pat G (VApp (VLam A e1) e2) (vinst0 e1' e2')
| VPRT_extra : forall G p r e m1 (m2 m2' : VMatchEnv p),
    Pat p r ->
    VPatternMatches p e m1 m2 ->
    VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) ->
    (forall a, VParRedT env U Pat G (vpath_get m2 a) (vpath_get m2' a)) ->
    VParRedT env U Pat G e (@vrhs_apply p m1 m2' (fst r)).

Arguments VPRT_bvar {env U Pat} G i.
Arguments VPRT_sort {env U Pat} G u.
Arguments VPRT_const {env U Pat} G c ls.

Definition VNonNeutral (env : VEnv) (U : nat) (Pat : VPatRel)
    (G : list VExpr) (e : VExpr) : Prop :=
  (exists A e1 e2, e = VApp (VLam A e1) e2) \/
  (exists p r m1 m2,
     Pat p r /\ VPatternMatches p e m1 m2 /\
     VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r)).

Inductive VCParRedT (env : VEnv) (U : nat) (Pat : VPatRel) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VCPRT_bvar : forall G i,
    VCParRedT env U Pat G (VBVar i) (VBVar i)
| VCPRT_sort : forall G u,
    VCParRedT env U Pat G (VSort u) (VSort u)
| VCPRT_const : forall G c ls,
    ~ VNonNeutral env U Pat G (VConst c ls) ->
    VCParRedT env U Pat G (VConst c ls) (VConst c ls)
| VCPRT_app : forall G f f' a a',
    ~ VNonNeutral env U Pat G (VApp f a) ->
    VCParRedT env U Pat G f f' ->
    VCParRedT env U Pat G a a' ->
    VCParRedT env U Pat G (VApp f a) (VApp f' a')
| VCPRT_lam : forall G A A' body body',
    VCParRedT env U Pat G A A' ->
    VCParRedT env U Pat (A :: G) body body' ->
    VCParRedT env U Pat G (VLam A body) (VLam A' body')
| VCPRT_forallE : forall G A A' B B',
    VCParRedT env U Pat G A A' ->
    VCParRedT env U Pat (A :: G) B B' ->
    VCParRedT env U Pat G (VForallE A B) (VForallE A' B')
| VCPRT_beta : forall G A e1 e1' e2 e2',
    VCParRedT env U Pat (A :: G) e1 e1' ->
    VCParRedT env U Pat G e2 e2' ->
    VCParRedT env U Pat G (VApp (VLam A e1) e2) (vinst0 e1' e2')
| VCPRT_extra : forall G p r e m1 (m2 m2' : VMatchEnv p),
    Pat p r ->
    VPatternMatches p e m1 m2 ->
    VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) ->
    (forall a, VCParRedT env U Pat G (vpath_get m2 a) (vpath_get m2' a)) ->
    VCParRedT env U Pat G e (@vrhs_apply p m1 m2' (fst r)).

Arguments VCPRT_bvar {env U Pat} G i.
Arguments VCPRT_sort {env U Pat} G u.

Definition VParRedTS (env : VEnv) (U : nat) (Pat : VPatRel)
    (G : list VExpr) : VExpr -> VExpr -> Prop :=
  VRTClosure (VParRedT env U Pat G).

Definition VCRDefEq (env : VEnv) (U : nat) (Pat : VPatRel)
    (G : list VExpr) (e1 e2 : VExpr) : Prop :=
  (exists A, VHasType env U G e1 A) /\
  (exists A, VHasType env U G e2 A) /\
  exists e1' e2',
    VParRedTS env U Pat G e1 e1' /\
    VParRedTS env U Pat G e2 e2' /\
    VNormalEq env U G e1' e2'.

(* Orthogonal higher-order pattern specification for an environment env *)

Record PatternParamsFor (env : VEnv) (Pat : VPatRel) : Prop := {
  pp_wf : VEnvWF env;
  pp_inj : DefEqInjectivity env;
  pp_simple : forall {p r},
    Pat p r -> exists sp : VSimplePattern, p = vsimple_to_pattern sp;
  pp_uniq : forall {p1 p2 p3 p4 r r'},
    Pat p1 r ->
    Pat p2 r' ->
    VSubpattern p3 p1 ->
    vpattern_inter p2 p3 = Some p4 ->
    p1 = p2 /\ p2 = p3;
  pp_rhs_uniq : forall {p r r'},
    Pat p r ->
    Pat p r' ->
    r = r';
  pp_pat_wf : forall {U G p r e m1 m2 A},
    Pat p r ->
    VPatternMatches p e m1 m2 ->
    VHasType env U G e A ->
    VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) ->
    VIsDefEqU env U G e (@vrhs_apply p m1 m2 (fst r));
  pp_app_l : forall {p r p1 p2 p3 p4},
    Pat p r ->
    VSubpattern (VPApp p1 p2) p ->
    ~ VSubpattern (VPApp p3 p4) p1;
  pp_app_l_uniq : forall {p p' r r' p1 p2 p1' p2' p3},
    Pat p r ->
    Pat p' r' ->
    VSubpattern (VPApp p1 p2) p ->
    VSubpattern (VPApp p1' p2') p' ->
    VSubpattern (VPVar p3) p1 ->
    vpattern_inter p1' p3 = None;
  pp_app_uniq : forall {p p' r r' p1 p2 p1' p2' p3 p3'},
    Pat p r ->
    Pat p' r' ->
    VSubpattern (VPApp p1 p2) p ->
    VSubpattern (VPApp p1' p2') p' ->
    VSubpattern p3 p1 ->
    VSubpattern p3' p2' ->
    vpattern_inter p3 p3' = None;
  pp_extra_pat : forall {U G df ls},
    venv_defeqs env df ->
    Forall (vlevel_wf U) ls ->
    List.length ls = vdf_uvars df ->
    exists p r m1 m2,
      Pat p r /\
      VPatternMatches p (vinstL ls (vdf_lhs df)) m1 m2 /\
      VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) /\
      vinstL ls (vdf_rhs df) = @vrhs_apply p m1 m2 (fst r);
  pp_extra_dec : forall {U G e A},
    VCtxWF env U G ->
    VHasType env U G e A ->
    (exists p r m1 m2,
       Pat p r /\ VPatternMatches p e m1 m2 /\
       VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r)) \/
    ~ (exists p r m1 m2,
         Pat p r /\ VPatternMatches p e m1 m2 /\
         VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r));
  pp_norm_app : forall {U G f1 f2 a1 a2 A B p r m1 m2 m2'},
    VCtxWF env U G ->
    VHasType env U G f1 (VForallE A B) ->
    VHasType env U G f2 (VForallE A B) ->
    VHasType env U G a1 A ->
    VHasType env U G a2 A ->
    VNormalEq env U G f1 f2 ->
    VNormalEq env U G a1 a2 ->
    Pat p r ->
    VPatternMatches p (VApp f2 a2) m1 m2 ->
    VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) ->
    (forall x, VParRedT env U Pat G (vpath_get m2 x) (vpath_get m2' x)) ->
    exists e1',
      VParRedTS env U Pat G (VApp f1 a1) e1' /\
      VNormalEq env U G e1' (@vrhs_apply p m1 m2' (fst r))
}.

Definition PatternParams (env : VEnv) : Prop :=
  exists Pat : VPatRel, PatternParamsFor env Pat.

Theorem Params_pat_not_var env Pat p r :
  PatternParamsFor env Pat ->
  ~ Pat (VPVar p) r.
Proof.
  intros Hpp Hpat.
  destruct (pp_simple Hpp Hpat) as [[rec maj c args | hd] Heq]; discriminate.
Qed.

Lemma VPatternMatches_not_bvar p i m1 m2 :
  ~ VPatternMatches p (VBVar i) m1 m2.
Proof.
  destruct p; simpl; tauto.
Qed.
Arguments VPatternMatches_not_bvar : clear implicits.

Lemma VPatternMatches_not_sort p u m1 m2 :
  ~ VPatternMatches p (VSort u) m1 m2.
Proof.
  destruct p; simpl; tauto.
Qed.
Arguments VPatternMatches_not_sort : clear implicits.

Lemma VPatternMatches_not_lam p A b m1 m2 :
  ~ VPatternMatches p (VLam A b) m1 m2.
Proof.
  destruct p; simpl; tauto.
Qed.
Arguments VPatternMatches_not_lam : clear implicits.

Lemma VPatternMatches_not_forallE p A B m1 m2 :
  ~ VPatternMatches p (VForallE A B) m1 m2.
Proof.
  destruct p; simpl; tauto.
Qed.
Arguments VPatternMatches_not_forallE : clear implicits.

Lemma VPatternMatches_not_app_lam p A e1 e2 m1 m2 :
  ~ VPatternMatches p (VApp (VLam A e1) e2) m1 m2.
Proof.
  destruct p as [c | f a | f]; simpl.
  - tauto.
  - intros [Hf _]; exact (VPatternMatches_not_lam f _ _ _ _ Hf).
  - intros [_ Hf]; exact (VPatternMatches_not_lam f _ _ _ _ Hf).
Qed.
Arguments VPatternMatches_not_app_lam : clear implicits.

Theorem VPatternCheckOK_weakN env U n k G G' p (ck : VPatternCheck p) m1 m2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VPatternCheckOK (VIsDefEqU env U G) m1 m2 ck ->
  VPatternCheckOK (VIsDefEqU env U G') m1 (vmenv_map (vliftN n k) m2) ck.
Proof.
  intros Hwf W Hck.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  eapply VPatternCheckOK_map; [| exact Hck].
  intros a b [T HT].
  rewrite <- !vrhs_apply_vliftN.
  exists (vliftN n k T). exact (VIsDefEq_weakN Hcl HT W).
Qed.

Theorem VPatternCheckOK_instN env U G0 e0 A0 k G1 G p (ck : VPatternCheck p) m1 m2 :
  VEnvWF env ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VHasType env U G0 e0 A0 ->
  VPatternCheckOK (VIsDefEqU env U G1) m1 m2 ck ->
  VPatternCheckOK (VIsDefEqU env U G) m1 (vmenv_map (fun x => vinst x e0 k) m2) ck.
Proof.
  intros Hwf W H0 Hck.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  eapply VPatternCheckOK_map; [| exact Hck].
  intros a b [T HT].
  rewrite <- !vrhs_apply_vinst.
  exact (VIsDefEqU_instN Hcl W (ex_intro _ T HT) H0).
Qed.

Theorem VParRedT_refl env U Pat G e :
  VParRedT env U Pat G e e.
Proof.
  revert G.
  induction e as [i | u | c ls | f IHf a IHa | A IHA b IHb | A IHA B IHB]; intros G.
  - apply VPRT_bvar.
  - apply VPRT_sort.
  - apply VPRT_const.
  - exact (VPRT_app (IHf G) (IHa G)).
  - exact (VPRT_lam (IHA G) (IHb (A :: G))).
  - exact (VPRT_forallE (IHA G) (IHB (A :: G))).
Qed.

Theorem VParRedT_weakN env U Pat n k G G' e1 e2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VParRedT env U Pat G e1 e2 ->
  VParRedT env U Pat G' (vliftN n k e1) (vliftN n k e2).
Proof.
  intros Hwf W H.
  revert k G' W.
  induction H as
    [ G i
    | G u
    | G c ls
    | G f f' a a' _ IHf _ IHa
    | G A A' body body' _ IHA _ IHb
    | G A A' B B' _ IHA _ IHB
    | G A e1 e1' e2 e2' _ IH1 _ IH2
    | G p r e m1 m2 m2' h1 h2 h3 _ IH ];
    intros k G' W; simpl.
  - apply VPRT_bvar.
  - apply VPRT_sort.
  - apply VPRT_const.
  - exact (VPRT_app (IHf _ _ W) (IHa _ _ W)).
  - exact (VPRT_lam (IHA _ _ W) (IHb _ _ (VCtxLiftN_succ A W))).
  - exact (VPRT_forallE (IHA _ _ W) (IHB _ _ (VCtxLiftN_succ A W))).
  - rewrite vliftN_vinst0.
    exact (VPRT_beta (IH1 _ _ (VCtxLiftN_succ A W)) (IH2 _ _ W)).
  - rewrite vrhs_apply_vliftN.
    eapply VPRT_extra.
    + exact h1.
    + apply VPatternMatches_vliftN. exists m2; split; [exact h2 | reflexivity].
    + exact (VPatternCheckOK_weakN Hwf W h3).
    + intros a. rewrite !vpath_get_map. exact (IH a _ _ W).
Qed.

Theorem VParRedT_instN env U Pat G0 a1 a2 A0 k G1 G e1 e2 :
  VEnvWF env ->
  VParRedT env U Pat G0 a1 a2 ->
  VHasType env U G0 a1 A0 ->
  VCtxInstN G0 a1 A0 k G1 G ->
  VParRedT env U Pat G1 e1 e2 ->
  VParRedT env U Pat G (vinst e1 a1 k) (vinst e2 a2 k).
Proof.
  intros Hwf Ha Ha_ty W H.
  revert k G W.
  induction H as
    [ G1 i
    | G1 u
    | G1 c ls
    | G1 f f' a a' _ IHf _ IHa
    | G1 A A' body body' _ IHA _ IHb
    | G1 A A' B B' _ IHA _ IHB
    | G1 A e1 e1' e2 e2' _ IH1 _ IH2
    | G1 p r e m1 m2 m2' h1 h2 h3 _ IH ];
    intros k G W; simpl.
  - revert i.
    induction W as [| k G1 G C W IHW]; intros i; simpl.
    + destruct i as [|i]; unfold vinstVar; simpl.
      * rewrite !vliftN_zero; exact Ha.
      * apply VPRT_bvar.
    + destruct i as [|i]; simpl.
      * unfold vinstVar; simpl; apply VPRT_bvar.
      * rewrite !vinstVar_succ.
        exact (VParRedT_weakN Hwf (VCtxLiftN_one _ _) (IHW i)).
  - apply VPRT_sort.
  - apply VPRT_const.
  - exact (VPRT_app (IHf _ _ W) (IHa _ _ W)).
  - exact (VPRT_lam (IHA _ _ W) (IHb _ _ (VCtxInstN_succ A W))).
  - exact (VPRT_forallE (IHA _ _ W) (IHB _ _ (VCtxInstN_succ A W))).
  - rewrite vinst0_vinst_hi.
    exact (VPRT_beta (IH1 _ _ (VCtxInstN_succ A W)) (IH2 _ _ W)).
  - rewrite vrhs_apply_vinst.
    eapply VPRT_extra.
    + exact h1.
    + exact (VPatternMatches_vinst _ _ h2).
    + exact (VPatternCheckOK_instN Hwf W Ha_ty h3).
    + intros a. rewrite !vpath_get_map. exact (IH a _ _ W).
Qed.

Theorem VParRedT_defeq env U Pat G e e' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VParRedT env U Pat G e e' ->
  VHasType env U G e A ->
  VIsDefEq env U G e e' A.
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  revert A HG.
  induction H as
    [ G i
    | G u
    | G c ls
    | G f f' a a' _ IHf _ IHa
    | G A0 A0' body body' _ IHA _ IHb
    | G A0 A0' B0 B0' _ IHA _ IHB
    | G A0 e1 e1' e2 e2' _ IH1 _ IH2
    | G p r e m1 m2 m2' h1 h2 h3 _ IH ];
    intros A HG He.
  - exact He.
  - exact He.
  - exact He.
  - destruct (VHasType_app_inv Hwf HG He) as [A0 [B0 [h1 h2]]].
    exact (VIsDefEq_trans_l Hwf Hinj HG He
             (VDF_appDF (IHf _ HG h1) (IHa _ HG h2))).
  - destruct (VHasType_lam_inv Hwf HG He) as [[u h1] [B0 h2]].
    exact (VIsDefEq_trans_l Hwf Hinj HG He
             (VDF_lamDF (IHA _ HG h1) (IHb _ (vctx_cons HG h1) h2))).
  - destruct (VHasType_forallE_inv Hwf He) as [[u h1] [v h2]].
    exact (VIsDefEq_trans_l Hwf Hinj HG He
             (VDF_forallEDF (IHA _ HG h1) (IHB _ (vctx_cons HG h1) h2))).
  - destruct (VHasType_app_inv Hwf HG He) as [A1 [B1 [hf ha]]].
    destruct (VHasType_lam_inv Hwf HG hf) as [[u hA] [B2 hb]].
    pose proof (VHasType_lam hA hb) as hf'.
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG (VIsDefEq_uniqU Hwf Hinj HG hf hf'))
      as [[w u1] _].
    pose proof (VHasType_defeqU_r Hwf Hinj HG (ex_intro _ _ u1) ha) as ha'.
    pose proof (IH1 _ (vctx_cons HG hA) hb) as ih1.
    pose proof (IH2 _ HG ha') as ih2.
    eapply (VIsDefEq_trans_l Hwf Hinj HG He).
    eapply VDF_trans.
    + apply VDF_symm.
      exact (VDF_appDF (VDF_symm (VDF_lamDF hA ih1)) (VDF_symm ih2)).
    + exact (VDF_beta (VIsDefEq_refl_r ih1) (VIsDefEq_refl_r ih2)).
  - pose proof (pp_pat_wf Hpp h1 h2 He h3) as Hpat_eq.
    eapply (VIsDefEq_trans_l Hwf Hinj HG He).
    apply (VIsDefEq_transU_r Hwf Hinj HG Hpat_eq).
    apply (VIsDefEq_apply_pat Hwf Hinj HG).
    + intros a B Ha_ty. exists B. exact (IH a _ HG Ha_ty).
    + exact (VHasType_defeqU_l Hwf Hinj HG Hpat_eq He).
Qed.

Theorem VParRedT_hasType env U Pat G e e' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VParRedT env U Pat G e e' ->
  VHasType env U G e A ->
  VHasType env U G e' A.
Proof.
  intros Hpp HG H He.
  exact (VIsDefEq_refl_r (VParRedT_defeq Hpp HG H He)).
Qed.

Theorem VParRedT_defeqDFC env U Pat G0 G1 G2 e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VHasType env U G1 e1 A ->
  VParRedT env U Pat G1 e1 e2 ->
  VParRedT env U Pat G2 e1 e2.
Proof.
  intros Hpp HG0 W Hty H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert G2 A W Hty.
  induction H as
    [ G1 i
    | G1 u
    | G1 c ls
    | G1 f f' a a' _ IHf _ IHa
    | G1 A0 A0' body body' _ IHA _ IHb
    | G1 A0 A0' B0 B0' _ IHA _ IHB
    | G1 A0 e1 e1' e2 e2' _ IH1 _ IH2
    | G1 p r e m1 m2 m2' h1 h2 h3 _ IH ];
    intros G2 A W Hty.
  - apply VPRT_bvar.
  - apply VPRT_sort.
  - apply VPRT_const.
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_app_inv Hwf HG1 Hty) as [A0 [B0 [hf ha]]].
    exact (VPRT_app (IHf _ _ W hf) (IHa _ _ W ha)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_lam_inv Hwf HG1 Hty) as [[u hA] [B0 he]].
    exact (VPRT_lam (IHA _ _ W hA) (IHb _ _ (VIsDefEqCtx_succ W hA) he)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_forallE_inv Hwf Hty) as [[u hA] [v hB]].
    exact (VPRT_forallE (IHA _ _ W hA) (IHB _ _ (VIsDefEqCtx_succ W hA) hB)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_app_inv Hwf HG1 Hty) as [A1 [B1 [hf ha]]].
    destruct (VHasType_lam_inv Hwf HG1 hf) as [[u hA] [B2 hb]].
    exact (VPRT_beta (IH1 _ _ (VIsDefEqCtx_succ W hA) hb) (IH2 _ _ W ha)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    eapply VPRT_extra; [exact h1 | exact h2 | |].
    + eapply VPatternCheckOK_map; [| exact h3].
      intros a b [T HT]. exists T. exact (VIsDefEq_defeqDFC Hcl W HT).
    + intros a.
      destruct (VPatternMatches_hasType a Hwf HG1 h2 Hty) as [Ta HTa].
      exact (IH a _ _ W HTa).
Qed.

Theorem VParRedT_apply_pat env U Pat G p (r : VPatternRHS p) m1 (m2 m3 : VMatchEnv p) :
  (forall a, VParRedT env U Pat G (vpath_get m2 a) (vpath_get m3 a)) ->
  VParRedT env U Pat G (@vrhs_apply p m1 m2 r) (@vrhs_apply p m1 m3 r).
Proof.
  intros H.
  induction r as [c Hcl | f IHf a IHa | path]; simpl.
  - apply VParRedT_refl.
  - exact (VPRT_app IHf IHa).
  - exact (H path).
Qed.

Theorem VParRedT_weakN_inv env U Pat n k G G' e1 e2' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G' ->
  VCtxLiftN n k G G' ->
  VHasType env U G' (vliftN n k e1) A ->
  VParRedT env U Pat G' (vliftN n k e1) e2' ->
  exists e2, VParRedT env U Pat G e1 e2 /\ e2' = vliftN n k e2.
Proof.
  intros Hpp HG' W Hty H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  remember (vliftN n k e1) as e1' eqn:Heq.
  revert e1 G k A HG' W Hty Heq.
  induction H as
    [ G' i
    | G' u
    | G' c ls
    | G' f f' a a' _ IHf _ IHa
    | G' A0 A0' body body' _ IHA _ IHb
    | G' A0 A0' B0 B0' _ IHA _ IHB
    | G' A0 b0 b0' a0 a0' _ IH1 _ IH2
    | G' p r e m1 m2 m2' h1 h2 h3 h4 IH ];
    intros e1 G k A HG' W Hty Heq.
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eexists (VBVar _); split; [apply VPRT_bvar | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eexists (VSort _); split; [apply VPRT_sort | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eexists (VConst _ _); split; [apply VPRT_const | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (VHasType_app_inv Hwf HG' Hty) as [A1 [B1 [hf ha]]].
    destruct (IHf _ _ _ _ HG' W hf eq_refl) as [f2 [hf2 ->]].
    destruct (IHa _ _ _ _ HG' W ha eq_refl) as [a2 [ha2 ->]].
    exists (VApp f2 a2); split; [exact (VPRT_app hf2 ha2) | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (VHasType_lam_inv Hwf HG' Hty) as [[u hA] [B1 hb]].
    destruct (IHA _ _ _ _ HG' W hA eq_refl) as [A2 [hA2 ->]].
    destruct (IHb _ _ _ _ (vctx_cons HG' hA) (VCtxLiftN_succ e1_1 W) hb eq_refl) as [b2 [hb2 ->]].
    exists (VLam A2 b2); split; [exact (VPRT_lam hA2 hb2) | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (VHasType_forallE_inv Hwf Hty) as [[u hA] [v hB]].
    destruct (IHA _ _ _ _ HG' W hA eq_refl) as [A2 [hA2 ->]].
    destruct (IHB _ _ _ _ (vctx_cons HG' hA) (VCtxLiftN_succ e1_1 W) hB eq_refl) as [B2 [hB2 ->]].
    exists (VForallE A2 B2); split; [exact (VPRT_forallE hA2 hB2) | reflexivity].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq as [[Hfn Ha0]]. subst a0.
    destruct e1_1; simpl in Hfn; try discriminate.
    inversion Hfn; subst A0 b0.
    destruct (VHasType_app_inv Hwf HG' Hty) as [A1 [B1 [hf ha]]].
    destruct (VHasType_lam_inv Hwf HG' hf) as [[u hA] [B2 hb]].
    destruct (IH1 _ _ _ _ (vctx_cons HG' hA) (VCtxLiftN_succ e1_1_1 W) hb eq_refl) as [b2 [hb2 ->]].
    destruct (IH2 _ _ _ _ HG' W ha eq_refl) as [a2 [ha2 ->]].
    exists (vinst0 b2 a2); split; [exact (VPRT_beta hb2 ha2) | symmetry; apply vliftN_vinst0].
  - subst e.
    destruct (proj1 (@VPatternMatches_vliftN p n k e1 m1 m2) h2) as [m3 [Hm3 ->]].
    assert (Hex : forall a : VPatternPath p,
      exists y : VExpr,
        VParRedT env U Pat G (vpath_get m3 a) y /\
        vpath_get m2' a = vliftN n k y).
    { intros a.
      destruct (VPatternMatches_hasType a Hwf HG' h2 Hty) as [Ta HTa].
      exact (IH a (vpath_get m3 a) G k Ta HG' W HTa
                (vpath_get_map (vliftN n k) m3 a)). }
    destruct (vmenv_rel_choice Hex) as [m3' Hm3'].
    assert (Hm2'_eq : m2' = vmenv_map (vliftN n k) m3').
    { apply vmenv_ext; intros a.
      rewrite vpath_get_map. exact (proj2 (Hm3' a)). }
    subst m2'.
    exists (@vrhs_apply p m1 m3' (fst r)). split.
    + eapply VPRT_extra; [exact h1 | exact Hm3 | | intros a; exact (proj1 (Hm3' a))].
      eapply VPatternCheckOK_map; [| exact h3].
      intros a b Hab.
      rewrite <- !vrhs_apply_vliftN in Hab.
      exact (proj1 (VIsDefEqU_weakN_iff Hinj HG' W) Hab).
    + symmetry. apply vrhs_apply_vliftN.
Qed.

Theorem VCParRedT_to_VParRedT env U Pat G e e' :
  VCParRedT env U Pat G e e' ->
  VParRedT env U Pat G e e'.
Proof.
  induction 1.
  - apply VPRT_bvar.
  - apply VPRT_sort.
  - apply VPRT_const.
  - exact (VPRT_app IHVCParRedT1 IHVCParRedT2).
  - exact (VPRT_lam IHVCParRedT1 IHVCParRedT2).
  - exact (VPRT_forallE IHVCParRedT1 IHVCParRedT2).
  - exact (VPRT_beta IHVCParRedT1 IHVCParRedT2).
  - eapply VPRT_extra; eassumption.
Qed.

Lemma is_beta_redex_dec (e : VExpr) :
  (exists A e1 e2, e = VApp (VLam A e1) e2) \/
  ~ (exists A e1 e2, e = VApp (VLam A e1) e2).
Proof.
  destruct e; try (right; intros [? [? [? H]]]; discriminate).
  destruct e1; try (right; intros [? [? [? H]]]; injection H; discriminate).
  left; repeat eexists.
Qed.

Lemma VNonNeutral_dec env U Pat G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VNonNeutral env U Pat G e \/ ~ VNonNeutral env U Pat G e.
Proof.
  intros Hpp HG Hty.
  unfold VNonNeutral.
  destruct (is_beta_redex_dec e) as [Hb | Hnb].
  - left; left; exact Hb.
  - destruct (pp_extra_dec Hpp HG Hty) as [He | Hne].
    + left; right; exact He.
    + right; intros [Hb | He]; [exact (Hnb Hb) | exact (Hne He)].
Qed.

Theorem VCParRedT_exists env U Pat G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  exists e', VCParRedT env U Pat G e e'.
Proof.
  intros Hpp HG Hty.
  pose proof (pp_wf Hpp) as Hwf.
  assert (Hmain : forall sz e G A,
    vexpr_size e <= sz ->
    VCtxWF env U G ->
    VHasType env U G e A ->
    exists e', VCParRedT env U Pat G e e').
  { apply (@nat_strong_ind (fun sz =>
      forall e G A,
        vexpr_size e <= sz ->
        VCtxWF env U G ->
        VHasType env U G e A ->
        exists e', VCParRedT env U Pat G e e')).
    intros sz IH e0 G0 A0 Hsz HG0 Hty0.
    assert (Hneut : VNonNeutral env U Pat G0 e0 ->
                    exists e', VCParRedT env U Pat G0 e0 e').
    { intros [[dom [b0 [a0 ->]]] | [p [r [m1 [m2 [hp [hm hck]]]]]]].
      - destruct (VHasType_app_inv Hwf HG0 Hty0) as [A1 [B1 [hf ha]]].
        destruct (VHasType_lam_inv Hwf HG0 hf) as [[u hA] [B2 hb]].
        destruct (IH (vexpr_size b0) ltac:(simpl in Hsz; lia)
                     b0 (dom :: G0) B2 (Nat.le_refl _) (vctx_cons HG0 hA) hb)
          as [b0' hb'].
        destruct (IH (vexpr_size a0) ltac:(simpl in Hsz; lia)
                     a0 G0 A1 (Nat.le_refl _) HG0 ha)
          as [a0' ha'].
        exists (vinst0 b0' a0'). exact (VCPRT_beta hb' ha').
      - assert (Hm_ex : forall x : VPatternPath p,
                  exists y : VExpr, VCParRedT env U Pat G0 (vpath_get m2 x) y).
        { intros x.
          destruct (VPatternMatches_hasType x Hwf HG0 hm Hty0) as [Tx HTx].
          pose proof (VPatternMatches_path_size x hm) as Hlt.
          exact (IH (vexpr_size (vpath_get m2 x)) ltac:(lia)
                    (vpath_get m2 x) G0 Tx (Nat.le_refl _) HG0 HTx). }
        destruct (vmenv_rel_choice Hm_ex) as [m2' Hm2'].
        exists (@vrhs_apply p m1 m2' (fst r)).
        exact (VCPRT_extra hp hm hck Hm2'). }
    destruct e0 as [i | u | c ls | f a | dom body | dom cod].
    - exists (VBVar i); apply VCPRT_bvar.
    - exists (VSort u); apply VCPRT_sort.
    - destruct (VNonNeutral_dec Hpp HG0 Hty0) as [Hn | Hnn].
      + exact (Hneut Hn).
      + exists (VConst c ls); exact (VCPRT_const Hnn).
    - destruct (VNonNeutral_dec Hpp HG0 Hty0) as [Hn | Hnn].
      + exact (Hneut Hn).
      + destruct (VHasType_app_inv Hwf HG0 Hty0) as [A1 [B1 [hf ha]]].
        destruct (IH (vexpr_size f) ltac:(simpl in Hsz; lia)
                     f G0 _ (Nat.le_refl _) HG0 hf) as [f' hf'].
        destruct (IH (vexpr_size a) ltac:(simpl in Hsz; lia)
                     a G0 _ (Nat.le_refl _) HG0 ha) as [a' ha'].
        exists (VApp f' a'); exact (VCPRT_app Hnn hf' ha').
    - destruct (VHasType_lam_inv Hwf HG0 Hty0) as [[u hA] [B1 hb]].
      destruct (IH (vexpr_size dom) ltac:(simpl in Hsz; lia)
                   dom G0 _ (Nat.le_refl _) HG0 hA) as [dom' hdom'].
      destruct (IH (vexpr_size body) ltac:(simpl in Hsz; lia)
                   body (dom :: G0) _ (Nat.le_refl _) (vctx_cons HG0 hA) hb) as [body' hbody'].
      exists (VLam dom' body'); exact (VCPRT_lam hdom' hbody').
    - destruct (VHasType_forallE_inv Hwf Hty0) as [[u hA] [v hB]].
      destruct (IH (vexpr_size dom) ltac:(simpl in Hsz; lia)
                   dom G0 _ (Nat.le_refl _) HG0 hA) as [dom' hdom'].
      destruct (IH (vexpr_size cod) ltac:(simpl in Hsz; lia)
                   cod (dom :: G0) _ (Nat.le_refl _) (vctx_cons HG0 hA) hB) as [cod' hcod'].
      exists (VForallE dom' cod'); exact (VCPRT_forallE hdom' hcod'). }
  exact (Hmain _ e G A (Nat.le_refl _) HG Hty).
Qed.

Theorem VParRedT_triangle env U Pat G e e' o A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VParRedT env U Pat G e e' ->
  VCParRedT env U Pat G e o ->
  exists o', VParRedT env U Pat G e' o' /\ VNormalEq env U G o' o.
Proof.
  intros Hpp HG Hty H Hc.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  assert (Hmain : forall sz G e e' o A,
    vexpr_size e <= sz ->
    VCtxWF env U G ->
    VHasType env U G e A ->
    VParRedT env U Pat G e e' ->
    VCParRedT env U Pat G e o ->
    exists o', VParRedT env U Pat G e' o' /\ VNormalEq env U G o' o).
  { apply (@nat_strong_ind (fun sz =>
      forall G e e' o A,
        vexpr_size e <= sz ->
        VCtxWF env U G ->
        VHasType env U G e A ->
        VParRedT env U Pat G e e' ->
        VCParRedT env U Pat G e o ->
        exists o', VParRedT env U Pat G e' o' /\ VNormalEq env U G o' o)).
    intros sz IH G0 e0 e0' o0 A0 Hsz HG0 Hty0 Hpar Hcpar.
    revert e0' A0 Hsz HG0 Hty0 Hpar.
    induction Hcpar as
      [ G0 i
      | G0 u
      | G0 c ls Hnn
      | G0 f f_o a a_o Hnn hcf IHcf hca IHca
      | G0 dom dom_o body body_o hcA IHcA hcb IHcb
      | G0 dom dom_o cod cod_o hcA IHcA hcB IHcB
      | G0 dom e1 e1_o e2 e2_o hc1 _ hc2 _
      | G0 p r e0 m1 m2 m2' l1 l2 l3 l4 _ ];
      intros e0' A0 Hsz HG0 Hty0 Hpar.
    - (* bvar *)
      inversion Hpar as [| | | | | | | G' p' r' e_x m1' m2_x m2'_x hp hm]; subst.
      + exists (VBVar i); split; [apply VParRedT_refl | exact (VN_refl Hty0)].
      + exfalso; exact (VPatternMatches_not_bvar _ _ _ _ hm).
    - (* sort *)
      inversion Hpar as [| | | | | | | G' p' r' e_x m1' m2_x m2'_x hp hm]; subst.
      + exists (VSort u); split; [apply VParRedT_refl | exact (VN_refl Hty0)].
      + exfalso; exact (VPatternMatches_not_sort _ _ _ _ hm).
    - (* const *)
      inversion Hpar as [| | | | | | | G' p' r' e_x m1' m2_x m2'_x hp hm hck]; subst.
      + exists (VConst c ls); split; [apply VParRedT_refl | exact (VN_refl Hty0)].
      + exfalso; apply Hnn; right; exists p', r', m1', m2_x; auto.
    - (* app *)
      destruct (VHasType_app_inv Hwf HG0 Hty0) as [A1 [B1 [l1_ty l2_ty]]].
      inversion Hpar as
        [ | | | G' f1 f' a1 a' r1 r2 | |
        | G' dom0 b0 b0' a1 a' rb1 rb2
        | G' p' r' e_x m1' m2_x m2'_x hp hm hck ]; subst.
      + destruct (IHcf f' _ ltac:(simpl in Hsz; lia) HG0 l1_ty r1) as [of' [p1 n1]].
        destruct (IHca a' _ ltac:(simpl in Hsz; lia) HG0 l2_ty r2) as [oa' [p2 n2]].
        pose proof (VParRedT_hasType Hpp HG0 p1 (VParRedT_hasType Hpp HG0 r1 l1_ty)) as o1_ty.
        pose proof (VParRedT_hasType Hpp HG0 p2 (VParRedT_hasType Hpp HG0 r2 l2_ty)) as o2_ty.
        exists (VApp of' oa'); split; [exact (VPRT_app p1 p2) |].
        exact (VN_appDF o1_ty
                 (VHasType_defeqU_l Hwf Hinj HG0 (VNormalEq_defeq Hwf Hinj HG0 n1) o1_ty)
                 o2_ty
                 (VHasType_defeqU_l Hwf Hinj HG0 (VNormalEq_defeq Hwf Hinj HG0 n2) o2_ty)
                 n1 n2).
      + exfalso; apply Hnn; left; exists dom0, b0, a; reflexivity.
      + exfalso; apply Hnn; right; exists p', r', m1', m2_x; auto.
    - (* lam *)
      destruct (VHasType_lam_inv Hwf HG0 Hty0) as [[u l1_ty] [B1 l2_ty]].
      inversion Hpar as
        [ | | | | G' dom1 dom' bd1 bd' r1 r2 | |
        | G' p' r' e_x m1' m2_x m2'_x hp hm ]; subst.
      + destruct (IHcA dom' _ ltac:(simpl in Hsz; lia) HG0 l1_ty r1) as [odom' [p1 n1]].
        pose proof (vctx_cons HG0 l1_ty) as HG0'.
        destruct (IHcb bd' _ ltac:(simpl in Hsz; lia) HG0' l2_ty r2) as [obd' [p2 n2]].
        pose proof (VDF_trans (VParRedT_defeq Hpp HG0 r1 l1_ty)
                              (VParRedT_defeq Hpp HG0 p1 (VParRedT_hasType Hpp HG0 r1 l1_ty)))
          as Hdom_eq.
        exists (VLam odom' obd'); split.
        * apply (VPRT_lam p1).
          exact (VParRedT_defeqDFC Hpp HG0
                   (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G0) (VParRedT_defeq Hpp HG0 r1 l1_ty))
                   (VParRedT_hasType Hpp HG0' r2 l2_ty) p2).
        * exact (VN_lamDF Hdom_eq
                   (VIsDefEq_transU_l Hwf Hinj HG0 Hdom_eq (VNormalEq_defeq Hwf Hinj HG0 n1))
                   n2).
      + exfalso; exact (VPatternMatches_not_lam _ _ _ _ _ hm).
    - (* forallE *)
      destruct (VHasType_forallE_inv Hwf Hty0) as [[u l1_ty] [v l2_ty]].
      inversion Hpar as
        [ | | | | | G' dom1 dom' cod1 cod' r1 r2 |
        | G' p' r' e_x m1' m2_x m2'_x hp hm ]; subst.
      + destruct (IHcA dom' _ ltac:(simpl in Hsz; lia) HG0 l1_ty r1) as [odom' [p1 n1]].
        pose proof (vctx_cons HG0 l1_ty) as HG0'.
        destruct (IHcB cod' _ ltac:(simpl in Hsz; lia) HG0' l2_ty r2) as [ocod' [p2 n2]].
        pose proof (VDF_trans (VParRedT_defeq Hpp HG0 r1 l1_ty)
                              (VParRedT_defeq Hpp HG0 p1 (VParRedT_hasType Hpp HG0 r1 l1_ty)))
          as Hdom_eq.
        exists (VForallE odom' ocod'); split.
        * apply (VPRT_forallE p1).
          exact (VParRedT_defeqDFC Hpp HG0
                   (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G0) (VParRedT_defeq Hpp HG0 r1 l1_ty))
                   (VParRedT_hasType Hpp HG0' r2 l2_ty) p2).
        * exact (VN_forallEDF Hdom_eq n1
                   (VParRedT_hasType Hpp HG0' p2 (VParRedT_hasType Hpp HG0' r2 l2_ty))
                   n2).
      + exfalso; exact (VPatternMatches_not_forallE _ _ _ _ _ hm).
    - (* beta *)
      destruct (VHasType_app_inv Hwf HG0 Hty0) as [A1 [B1 [lf la]]].
      destruct (VHasType_lam_inv Hwf HG0 lf) as [[u lA] [B2 le]].
      destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                  (VIsDefEq_uniqU Hwf Hinj HG0 lf (VHasType_lam lA le)))
        as [[w hw] _].
      pose proof (VDF_defeqDF hw la) as la'.
      pose proof (vctx_cons HG0 lA) as HG0'.
      inversion Hpar as
        [ | | | G' f1 f' a1 a' rf ra | |
        | G' dom1 b1 b1' a1 a' re ra
        | G' p' r' e_x m1' m2_x m2'_x hp hm ]; subst.
      + (* app vs beta *)
        destruct (IH (vexpr_size e2) ltac:(simpl in Hsz; lia)
                     G0 e2 a' e2_o A1 (Nat.le_refl _) HG0 la ra hc2)
          as [oa' [p3 n3]].
        inversion rf as
          [ | | | | G'' dom2 rA' bd2 re' rA re | |
          | G'' p'' r'' e_y m1'' m2_y m2'_y hp'' hm'' ]; subst.
        * destruct (IH (vexpr_size e1) ltac:(simpl in Hsz; lia)
                       (dom :: G0) e1 re' e1_o B2 (Nat.le_refl _) HG0' le re hc1)
            as [oe' [p2 n2]].
          exists (vinst0 oe' oa'); split.
          -- apply (VPRT_beta
                      (VParRedT_defeqDFC Hpp HG0
                         (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G0) (VParRedT_defeq Hpp HG0 rA lA))
                         (VParRedT_hasType Hpp HG0' re le) p2)
                      p3).
          -- apply (VNormalEq_trans Hwf Hinj HG0
                      (e2 := vinst0 oe' e2_o)).
             ++ exact (VNormalEq_instN_r Hwf Hinj HG0'
                         (VParRedT_hasType Hpp HG0 p3 (VParRedT_hasType Hpp HG0 ra la'))
                         n3 (VCtxInstN_zero G0 oa' dom)
                         (VParRedT_hasType Hpp HG0' p2 (VParRedT_hasType Hpp HG0' re le))).
             ++ exact (VNormalEq_instN Hwf
                         (VParRedT_hasType Hpp HG0 (VCParRedT_to_VParRedT hc2) la')
                         (VCtxInstN_zero G0 e2_o dom) n2).
        * exfalso; exact (VPatternMatches_not_lam _ _ _ _ _ hm'').
      + (* beta vs beta *)
        destruct (IH (vexpr_size e1) ltac:(simpl in Hsz; lia)
                     (dom :: G0) e1 b1' e1_o B2 (Nat.le_refl _) HG0' le re hc1)
          as [oe' [p2 n2]].
        destruct (IH (vexpr_size e2) ltac:(simpl in Hsz; lia)
                     G0 e2 a' e2_o A1 (Nat.le_refl _) HG0 la ra hc2)
          as [oa' [p3 n3]].
        exists (vinst0 oe' oa'); split.
        * exact (VParRedT_instN Hwf p3 (VParRedT_hasType Hpp HG0 ra la')
                   (VCtxInstN_zero G0 a' dom) p2).
        * apply (VNormalEq_trans Hwf Hinj HG0 (e2 := vinst0 oe' e2_o)).
          -- exact (VNormalEq_instN_r Hwf Hinj HG0'
                      (VParRedT_hasType Hpp HG0 p3 (VParRedT_hasType Hpp HG0 ra la'))
                      n3 (VCtxInstN_zero G0 oa' dom)
                      (VParRedT_hasType Hpp HG0' p2 (VParRedT_hasType Hpp HG0' re le))).
          -- exact (VNormalEq_instN Hwf
                      (VParRedT_hasType Hpp HG0 (VCParRedT_to_VParRedT hc2) la')
                      (VCtxInstN_zero G0 e2_o dom) n2).
      + exfalso; exact (VPatternMatches_not_app_lam _ _ _ _ _ _ hm).
    - (* extra *)
      assert (Hcases :
        (exists m3 m3' : VMatchEnv p,
           VPatternMatches p e0' m1 m3 /\
           (forall a, VParRedT env U Pat G0 (vpath_get m2 a) (vpath_get m3 a)) /\
           (forall a, VParRedT env U Pat G0 (vpath_get m3 a) (vpath_get m3' a)) /\
           (forall a, VNormalEq env U G0 (vpath_get m3' a) (vpath_get m2' a))) \/
        (exists p1 e1' e1 m1_1 m2_1,
           VSubpattern p1 p /\
           (p1 = p -> e1 = e0 /\ e1' = e0') /\
           VPatternMatches p1 e1 m1_1 m2_1 /\
           exists p' r' m1' (m2_r m3 : VMatchEnv p'),
             Pat p' r' /\
             VPatternMatches p' e1 m1' m2_r /\
             (forall a, VParRedT env U Pat G0 (vpath_get m2_r a) (vpath_get m3 a)) /\
             e1' = @vrhs_apply p' m1' m3 (fst r'))).
      { clear l1 l3 r.
        revert p m1 m2 m2' A0 Hsz HG0 Hty0 l2 l4.
        induction Hpar as
          [ G_x i
          | G_x u
          | G_x c ls
          | G_x f f' a a' hf IHf ha IHa
          | G_x dom dom' bd bd' _ _ _ _
          | G_x dom dom' cod cod' _ _ _ _
          | G_x dom b1 b1' b2 b2' _ _ _ _
          | G_x p' r' e_x m1' m2_r m3 r1 r2 _ r4 _ ];
          intros p m1 m2 m2' A0 Hsz HG0 Hty0 l2 l4.
        - exfalso; exact (VPatternMatches_not_bvar _ _ _ _ l2).
        - exfalso; exact (VPatternMatches_not_sort _ _ _ _ l2).
        - destruct p as [c0 | |]; simpl in l2; try contradiction.
          destruct l2 as [Hc0 [Hls Hm2]]. subst c0 m1 m2.
          destruct m2'.
          left; exists tt, tt.
          split; [simpl; auto |].
          split; [intros [] | split; [intros [] | intros []]].
        - (* app *)
          destruct (VHasType_app_inv Hwf HG0 Hty0) as [A1 [B1 [Hf Ha]]].
          destruct p as [c0 | pf pa | pf]; simpl in l2; try contradiction.
          + (* VPApp pf pa *)
            destruct m2 as [mf ma], m2' as [mf' ma']; simpl in *.
            destruct l2 as [lf [ls2 la]].
            destruct (IHf pf m1 mf mf' _ ltac:(simpl in Hsz; lia) HG0 Hf lf
                          (fun x => l4 (inl x)))
              as [[mf3 [mf3' [f1 [f2 [f3 f4]]]]]
                 |[p1 [e1' [e1 [m1_1 [m2_1 [hsub [_ hrest]]]]]]]].
            * destruct (IHa pa ls2 ma ma' _ ltac:(simpl in Hsz; lia) HG0 Ha la
                            (fun x => l4 (inr x)))
                as [[ma3 [ma3' [a1 [a2 [a3 a4]]]]]
                   |[p1 [e1' [e1 [m1_1 [m2_1 [hsub [_ hrest]]]]]]]].
              -- left; exists (mf3, ma3), (mf3', ma3'); simpl.
                 split; [split; [exact f1 | exists ls2; exact a1] |].
                 split; [intros [x | x]; simpl; [apply f2 | apply a2] |].
                 split; [intros [x | x]; simpl; [apply f3 | apply a3]
                        |intros [x | x]; simpl; [apply f4 | apply a4]].
              -- right; exists p1, e1', e1, m1_1, m2_1.
                 split; [exact (VSub_appR pf hsub) |].
                 split; [| exact hrest].
                 intros ->.
                 pose proof (VSubpattern_size_le hsub); simpl in *; lia.
            * right; exists p1, e1', e1, m1_1, m2_1.
              split; [exact (VSub_appL pa hsub) |].
              split; [| exact hrest].
              intros ->.
              pose proof (VSubpattern_size_le hsub); simpl in *; lia.
          + (* VPVar pf *)
            destruct m2 as [ea mf], m2' as [ea' mf']; simpl in *.
            destruct l2 as [-> lf].
            destruct (IHf pf m1 mf mf' _ ltac:(simpl in Hsz; lia) HG0 Hf lf
                          (fun x => l4 (Some x)))
              as [[mf3 [mf3' [f1 [f2 [f3 f4]]]]]
                 |[p1 [e1' [e1 [m1_1 [m2_1 [hsub [_ hrest]]]]]]]].
            * destruct (IH (vexpr_size a) ltac:(simpl in Hsz; lia)
                           G_x a a' ea' A1 (Nat.le_refl _) HG0 Ha ha (l4 None))
                as [a3' [a3 a4]].
              left; exists (a', mf3), (a3', mf3'); simpl.
              split; [auto |].
              split; [intros [x |]; simpl; [apply f2 | exact ha] |].
              split; [intros [x |]; simpl; [apply f3 | exact a3]
                     |intros [x |]; simpl; [apply f4 | exact a4]].
            * right; exists p1, e1', e1, m1_1, m2_1.
              split; [exact (VSub_varL hsub) |].
              split; [| exact hrest].
              intros ->.
              pose proof (VSubpattern_size_le hsub); simpl in *; lia.
        - exfalso; exact (VPatternMatches_not_lam _ _ _ _ _ l2).
        - exfalso; exact (VPatternMatches_not_forallE _ _ _ _ _ l2).
        - exfalso; exact (VPatternMatches_not_app_lam _ _ _ _ _ _ l2).
        - right; exists p, (@vrhs_apply p' m1' m3 (fst r')), e_x, m1, m2.
          split; [apply VSub_refl |].
          split; [intros _; auto |].
          split; [exact l2 |].
          exists p', r', m1', m2_r, m3; auto. }
      destruct Hcases as
        [ [m3 [m3' [h1 [h2 [h3 h4]]]]]
        | [p1 [e1' [e1 [m1_1 [m2_1 [h1 [h2 [l2' [p' [r' [m1' [m2_r [m3 [r1 [r2 [r4 He1']]]]]]]]]]]]]]]] ].
      + assert (Hck3 : VPatternCheckOK (VIsDefEqU env U G0) m1 m3 (snd r)).
        { eapply VPatternCheckOK_map; [| exact l3].
          intros a b [T HT].
          pose proof (VIsDefEq_apply_pat Hwf Hinj HG0
                        (fun x B Hx => ex_intro _ B (VParRedT_defeq Hpp HG0 (h2 x) Hx))
                        (VIsDefEq_refl_l HT)) as Ha_eq.
          pose proof (VIsDefEq_apply_pat Hwf Hinj HG0
                        (fun x B Hx => ex_intro _ B (VParRedT_defeq Hpp HG0 (h2 x) Hx))
                        (VIsDefEq_refl_r HT)) as Hb_eq.
          exists T.
          exact (VDF_trans (VDF_symm Ha_eq) (VDF_trans HT Hb_eq)). }
        pose proof (VPRT_extra l1 h1 Hck3 h3) as Hstep.
        exists (@vrhs_apply p m1 m3' (fst r)); split; [exact Hstep |].
        exact (VNormalEq_apply_pat Hwf Hinj HG0
                 (fun a _ _ => h4 a)
                 (VParRedT_hasType Hpp HG0 Hstep (VParRedT_hasType Hpp HG0 Hpar Hty0))).
      + destruct (proj1 (VPatternMatches_inter p' p1 e1)
                    (conj (ex_intro _ m1' (ex_intro _ m2_r r2))
                          (ex_intro _ m1_1 (ex_intro _ m2_1 l2'))))
          as [p4 [_ [_ [hr _]]]].
        destruct (pp_uniq Hpp l1 r1 h1 hr) as [Hp_eq Hp'_eq].
        subst p' p1.
        pose proof (pp_rhs_uniq Hpp l1 r1) as Hr_eq; subst r'.
        destruct (h2 eq_refl) as [He1 He1'_eq]; subst e1 e0' e1'.
        destruct (VPatternMatches_uniq l2 r2) as [Hm1_eq Hm2_eq]; subst m1' m2_r.
        assert (Hex : forall a : VPatternPath p,
          exists y : VExpr,
            VParRedT env U Pat G0 (vpath_get m3 a) y /\
            VNormalEq env U G0 y (vpath_get m2' a)).
        { intros a.
          destruct (VPatternMatches_hasType a Hwf HG0 l2 Hty0) as [Ta HTa].
          pose proof (VPatternMatches_path_size a l2) as Hlt.
          exact (IH (vexpr_size (vpath_get m2 a)) ltac:(lia)
                    G0 (vpath_get m2 a) (vpath_get m3 a) (vpath_get m2' a) Ta
                    (Nat.le_refl _) HG0 HTa (r4 a) (l4 a)). }
        destruct (vmenv_rel_choice Hex) as [m3' Hm3'].
        pose proof (VParRedT_apply_pat (fst r) m1 (fun a => proj1 (Hm3' a))) as Hstep.
        exists (@vrhs_apply p m1 m3' (fst r)); split; [exact Hstep |].
        exact (VNormalEq_apply_pat Hwf Hinj HG0
                 (fun a _ _ => proj2 (Hm3' a))
                 (VParRedT_hasType Hpp HG0 Hstep (VParRedT_hasType Hpp HG0 Hpar Hty0))). }
  exact (Hmain _ G e e' o A (Nat.le_refl _) HG Hty H Hc).
Qed.

Theorem VParRedT_church_rosser env U Pat G e e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VParRedT env U Pat G e e1 ->
  VParRedT env U Pat G e e2 ->
  exists e1' e2',
    VParRedT env U Pat G e1 e1' /\
    VParRedT env U Pat G e2 e2' /\
    VNormalEq env U G e1' e2'.
Proof.
  intros Hpp HG Hty H1 H2.
  destruct (VCParRedT_exists Hpp HG Hty) as [o Ho].
  destruct (VParRedT_triangle Hpp HG Hty H1 Ho) as [e1' [l1 l2]].
  destruct (VParRedT_triangle Hpp HG Hty H2 Ho) as [e2' [r1 r2]].
  exists e1', e2'.
  split; [exact l1 | split; [exact r1 |]].
  exact (VNormalEq_trans (pp_wf Hpp) (pp_inj Hpp) HG l2
           (VNormalEq_symm (pp_wf Hpp) (pp_inj Hpp) HG r2)).
Qed.

(* Multi-step Typed Parallel Reduction VParRedTS *)

Theorem VParRedTS_hasType env U Pat G e e' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VParRedTS env U Pat G e e' ->
  VHasType env U G e A ->
  VHasType env U G e' A.
Proof.
  intros Hpp HG H.
  induction H as [| y z _ IH Hstep]; intros Hty.
  - exact Hty.
  - exact (VParRedT_hasType Hpp HG Hstep (IH Hty)).
Qed.

Theorem VParRedTS_defeq env U Pat G e e' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VParRedTS env U Pat G e e' ->
  VHasType env U G e A ->
  VIsDefEq env U G e e' A.
Proof.
  intros Hpp HG H Hty.
  induction H as [| y z h1 IH h2].
  - exact Hty.
  - exact (VDF_trans IH (VParRedT_defeq Hpp HG h2 (VParRedTS_hasType Hpp HG h1 Hty))).
Qed.

Theorem VParRedTS_defeqDFC env U Pat G0 G1 G2 e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VHasType env U G1 e1 A ->
  VParRedTS env U Pat G1 e1 e2 ->
  VParRedTS env U Pat G2 e1 e2.
Proof.
  intros Hpp HG0 W Hty H.
  pose proof (VIsDefEqCtx_wf (VEnvWF_closed (pp_wf Hpp)) HG0 W) as HG1.
  induction H as [| y z h1 IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VParRedT_defeqDFC Hpp HG0 W (VParRedTS_hasType Hpp HG1 h1 Hty) h2)).
Qed.

Theorem VParRedTS_app env U Pat G f f' a a' :
  VParRedTS env U Pat G f f' ->
  VParRedTS env U Pat G a a' ->
  VParRedTS env U Pat G (VApp f a) (VApp f' a').
Proof.
  intros hf ha.
  assert (H1 : VParRedTS env U Pat G (VApp f a) (VApp f a')).
  { induction ha as [| y z _ IH h2]; [exact VRTC_rfl |].
    exact (VRTC_tail IH (VPRT_app (VParRedT_refl env U Pat G f) h2)). }
  apply (VRTC_trans H1); clear H1 ha.
  induction hf as [| y z _ IH h2]; [exact VRTC_rfl |].
  exact (VRTC_tail IH (VPRT_app h2 (VParRedT_refl env U Pat G a'))).
Qed.

Theorem VParRedTS_lam env U Pat G A A' body body' :
  VParRedTS env U Pat G A A' ->
  VParRedTS env U Pat (A :: G) body body' ->
  VParRedTS env U Pat G (VLam A body) (VLam A' body').
Proof.
  intros hf ha.
  assert (H1 : VParRedTS env U Pat G (VLam A body) (VLam A body')).
  { induction ha as [| y z _ IH h2]; [exact VRTC_rfl |].
    exact (VRTC_tail IH (VPRT_lam (VParRedT_refl env U Pat G A) h2)). }
  apply (VRTC_trans H1); clear H1 ha.
  induction hf as [| y z _ IH h2]; [exact VRTC_rfl |].
  exact (VRTC_tail IH (VPRT_lam h2 (VParRedT_refl env U Pat (y :: G) body'))).
Qed.

Theorem VParRedTS_forallE env U Pat G A A' body body' :
  VParRedTS env U Pat G A A' ->
  VParRedTS env U Pat (A :: G) body body' ->
  VParRedTS env U Pat G (VForallE A body) (VForallE A' body').
Proof.
  intros hf ha.
  assert (H1 : VParRedTS env U Pat G (VForallE A body) (VForallE A body')).
  { induction ha as [| y z _ IH h2]; [exact VRTC_rfl |].
    exact (VRTC_tail IH (VPRT_forallE (VParRedT_refl env U Pat G A) h2)). }
  apply (VRTC_trans H1); clear H1 ha.
  induction hf as [| y z _ IH h2]; [exact VRTC_rfl |].
  exact (VRTC_tail IH (VPRT_forallE h2 (VParRedT_refl env U Pat (y :: G) body'))).
Qed.

Theorem VParRedTS_inst env U Pat G f f' a a' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G a A ->
  VParRedTS env U Pat (A :: G) f f' ->
  VParRedTS env U Pat G a a' ->
  VParRedTS env U Pat G (vinst0 f a) (vinst0 f' a').
Proof.
  intros Hpp HG Ha hf ha.
  pose proof (pp_wf Hpp) as Hwf.
  assert (H1 : VParRedTS env U Pat G (vinst0 f a) (vinst0 f a')).
  { induction ha as [| y z h1 IH h2]; [exact VRTC_rfl |].
    exact (VRTC_tail IH
             (VParRedT_instN Hwf h2 (VParRedTS_hasType Hpp HG h1 Ha)
                (VCtxInstN_zero G y A) (VParRedT_refl env U Pat (A :: G) f))). }
  pose proof (VParRedTS_hasType Hpp HG ha Ha) as Ha'.
  apply (VRTC_trans H1); clear H1 ha Ha.
  induction hf as [| y z _ IH h2]; [exact VRTC_rfl |].
  exact (VRTC_tail IH
           (VParRedT_instN Hwf (VParRedT_refl env U Pat G a') Ha'
              (VCtxInstN_zero G a' A) h2)).
Qed.

Theorem VParRedTS_weakN env U Pat n k G G' e e' :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VParRedTS env U Pat G e e' ->
  VParRedTS env U Pat G' (vliftN n k e) (vliftN n k e').
Proof.
  intros Hwf W H.
  induction H as [| y z _ IH h2]; [exact VRTC_rfl |].
  exact (VRTC_tail IH (VParRedT_weakN Hwf W h2)).
Qed.

(* ParRedExt & beta simulation under eta-expanded neutral chains *)

Inductive VParRedExt : Type :=
| VPE_base : VParRedExt
| VPE_lift : VParRedExt -> VParRedExt
| VPE_app  : VParRedExt -> VParRedExt.

Fixpoint vpe_depth (l : VParRedExt) : nat :=
  match l with
  | VPE_base => 0
  | VPE_lift l' | VPE_app l' => vpe_depth l' + 1
  end.

Fixpoint vpe_apply (l : VParRedExt) (e : VExpr) : VExpr :=
  match l with
  | VPE_base => e
  | VPE_lift l' => vlift (vpe_apply l' e)
  | VPE_app l' => VApp (vlift (vpe_apply l' e)) (VBVar 0)
  end.

Fixpoint vpe_meas (l : VParRedExt) : nat :=
  match l with
  | VPE_base => 0
  | VPE_lift l' => vpe_meas l' + 1
  | VPE_app l' => vpe_meas l' + 2
  end.

Definition VIsApp (e : VExpr) : Prop :=
  match e with
  | VApp _ _ => True
  | _ => False
  end.

Lemma vpe_isApp l f a e' :
  vpe_apply l (VApp f a) = e' -> VIsApp e'.
Proof.
  revert e'.
  induction l as [| l IH | l _]; intros e' H; simpl in H.
  - subst e'; exact I.
  - specialize (IH _ eq_refl).
    destruct (vpe_apply l (VApp f a)); simpl in *; try contradiction.
    subst e'; exact I.
  - subst e'; exact I.
Qed.

Theorem hasType_app_bvar0 env U G A e B :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U (A :: G) ->
  VHasType env U (A :: G) (VApp (vlift e) (VBVar 0)) B ->
  exists B', VHasType env U G e (VForallE A B').
Proof.
  intros Hwf Hinj HG H.
  destruct (VHasType_app_inv Hwf HG H) as [A0 [B0 [c1 c2]]].
  destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG c1)) as [_ [v d3]].
  destruct (VIsDefEq_uniq_same Hwf Hinj HG c2 (VDF_bvar (VLookupZero A G))) as [u d4].
  pose proof (VHasType_defeqU_r Hwf Hinj HG
                (ex_intro _ _ (VDF_forallEDF d4 d3)) c1) as c1'.
  pose proof (VDF_eta c1') as Heta.
  assert (Heq_lam :
    VLam (vlift A) (VApp (vlift (vlift e)) (VBVar 0)) =
    vlift (VLam A (VApp (vlift e) (VBVar 0)))).
  { unfold vlift. simpl.
    rewrite (@vliftN_vliftN e 1 1 0 1 ltac:(lia) ltac:(lia)).
    rewrite vliftN_comp. reflexivity. }
  rewrite Heq_lam in Heta.
  destruct (proj1 (@VIsDefEqU_weakN_iff env U 1 0 G (A :: G)
                     (VLam A (VApp (vlift e) (VBVar 0))) e Hinj HG (VCtxLiftN_one A G))
              (ex_intro _ _ Heta))
    as [T f1].
  destruct (VHasType_lam_inv Hwf (proj1 HG) (VIsDefEq_refl_l f1))
    as [[w f2] [B' f3]].
  exists B'.
  exact (VHasType_defeqU_l Hwf Hinj (proj1 HG) (ex_intro _ T f1) (VHasType_lam f2 f3)).
Qed.

Lemma vpe_app_decomp l A e' f' a' :
  vpe_apply l (VApp (vlift (VLam A e')) (VBVar 0)) = VApp f' a' ->
  exists n,
    a' = VBVar n /\
    ((f' = vliftN (n + 1) 0 (VLam A e') /\ vpe_apply l e' = vliftN n 0 e') \/
     (exists l',
        vpe_depth l' <= vpe_depth l /\
        f' = vpe_apply l' (VApp (vlift (VLam A e')) (VBVar 0)) /\
        vpe_apply l e' = VApp (vpe_apply l' e') (VBVar n))).
Proof.
  revert f' a'.
  induction l as [| l IH | l _]; intros f' a' Heq; simpl in Heq.
  - inversion Heq; subst.
    exists 0; split; [reflexivity |].
    left; split; [reflexivity | simpl; symmetry; apply vliftN_zero].
  -destruct (vpe_apply l (VApp (vlift (VLam A e')) (VBVar 0))) eqn:Heq';
      simpl in Heq; try discriminate.
    inversion Heq; subst f' a'.
    destruct (IH _ _ eq_refl) as [n [-> [[-> Happly] | [l' [Hdep [-> Happly]]]]]].
    + exists (1 + n); split; [reflexivity |].
      left; split.
      * rewrite vliftN_comp; reflexivity.
      * simpl; rewrite Happly; unfold vlift; rewrite vliftN_comp; reflexivity.
    + exists (1 + n); split; [reflexivity |].
      right; exists (VPE_lift l'); simpl.
      split; [lia | split; [reflexivity | rewrite Happly; reflexivity]].
  - inversion Heq; subst.
    exists 0; split; [reflexivity |].
    right; exists (VPE_lift l); simpl; split; [lia | split; reflexivity].
Qed.

Theorem VParRedExt_parRed_beta env U Pat G f A e' a B :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VNormalEq env U G f (VLam A e') ->
  VHasType env U G (VApp f a) B ->
  exists e,
    VParRedTS env U Pat G (VApp f a) e /\
    VNormalEq env U G e (vinst0 e' a).
Proof.
  intros Hpp HG Hnorm Happ_ty.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  assert (Hboth : forall sz f G A e',
    vexpr_size f <= sz ->
    VCtxWF env U G ->
    (VNormalEq env U G f (VLam A e') ->
     forall a B, VHasType env U G (VApp f a) B ->
       exists e, VParRedTS env U Pat G (VApp f a) e /\
                 VNormalEq env U G e (vinst0 e' a)) /\
    (forall l : VParRedExt,
       vpe_depth l <= List.length G ->
       VNormalEq env U G f (vpe_apply l (VApp (vlift (VLam A e')) (VBVar 0))) ->
       exists e, VParRedTS env U Pat G f e /\
                 VNormalEq env U G e (vpe_apply l e'))).
  { apply (@nat_strong_ind (fun sz =>
      forall f G A e',
        vexpr_size f <= sz ->
        VCtxWF env U G ->
        (VNormalEq env U G f (VLam A e') ->
         forall a B, VHasType env U G (VApp f a) B ->
           exists e, VParRedTS env U Pat G (VApp f a) e /\
                     VNormalEq env U G e (vinst0 e' a)) /\
        (forall l : VParRedExt,
           vpe_depth l <= List.length G ->
           VNormalEq env U G f (vpe_apply l (VApp (vlift (VLam A e')) (VBVar 0))) ->
           exists e, VParRedTS env U Pat G f e /\
                     VNormalEq env U G e (vpe_apply l e')))).
    intros sz IH f0 G0 A0 e0' Hsz HG0.
    split.
    - (* Part 1: f0 ≡ₚ VLam A0 e0' *)
      intros h1 a0 B0 h2.
      inversion h1 as
        [ G' x T Hrefl
        | | |
        | G' A_base A1 A2 b1 b2 u a1 a2 a3
        |
        | G' e_r A' B' e_body a1 a2
        | G' e_l A' B' e_body a1 a2
        | G' p x1 x2 a1 a2 a3 ]; subst.
      + pose proof (VPRT_beta (VParRedT_refl env U Pat (A0 :: G0) e0')
                              (VParRedT_refl env U Pat G0 a0)) as hstep.
        exists (vinst0 e0' a0); split.
        * exact (VRTC_single hstep).
        * exact (VN_refl (VParRedT_hasType Hpp HG0 hstep h2)).
      + destruct (VHasType_app_inv Hwf HG0 h2) as [A_f [B_f [H1 H2]]].
        destruct (VHasType_lam_inv Hwf HG0 H1) as [[u_f H3] [B_b H4]].
        destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                    (VIsDefEq_uniqU Hwf Hinj HG0 (VHasType_lam H3 H4) H1))
          as [[w u1] _].
        exists (vinst0 b1 a0); split.
        * exact (VRTC_single (VPRT_beta (VParRedT_refl env U Pat (A1 :: G0) b1)
                                        (VParRedT_refl env U Pat G0 a0))).
        * exact (VNormalEq_instN Hwf
                   (VDF_defeqDF (VDF_symm (VIsDefEq_trans_l Hwf Hinj HG0 a1 u1)) H2)
                   (VCtxInstN_zero G0 a0 A_base) a3).
      + (* etaL *)
        destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 a1)) as [[u_a hA] _].
        destruct (proj2 (IH (vexpr_size e_body) ltac:(simpl in Hsz; lia)
                            e_body (A' :: G0) A0 e0' (Nat.le_refl _) (vctx_cons HG0 hA))
                    VPE_base (le_0_n _) a2)
          as [d [d1 d2]].
        simpl in d2.
        destruct (VHasType_app_inv Hwf HG0 h2) as [A_f [B_f [c3 c4]]].
        destruct (VHasType_lam_inv Hwf HG0 c3) as [[u_c c1] [B_c c2]].
        destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                    (VIsDefEq_uniqU Hwf Hinj HG0 (VHasType_lam c1 c2) c3))
          as [[w u1] _].
        exists (vinst0 d a0); split.
        * exact (VRTC_tail
                   (VParRedTS_app (VParRedTS_lam VRTC_rfl d1) VRTC_rfl)
                   (VPRT_beta (VParRedT_refl env U Pat (A' :: G0) d)
                              (VParRedT_refl env U Pat G0 a0))).
        * exact (VNormalEq_instN Hwf (VDF_defeqDF (VDF_symm u1) c4)
                   (VCtxInstN_zero G0 a0 A') d2).
      + (* etaR *)
        destruct (VHasType_app_inv Hwf HG0 h2) as [A_f [B_f [H1 H2]]].
        destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0 (VIsDefEq_uniqU Hwf Hinj HG0 H1 a1))
          as [[w u1] _].
        pose proof (VNormalEq_instN Hwf (VDF_defeqDF u1 H2)
                      (VCtxInstN_zero G0 a0 A0) a2) as Hinst.
        simpl in Hinst.
        change (vinst (vlift f0) a0 0) with (vinst0 (vlift f0) a0) in Hinst.
        rewrite vinst0_vlift in Hinst.
        unfold vinstVar in Hinst; simpl in Hinst; rewrite vliftN_zero in Hinst.
        exists (VApp f0 a0); split; [exact VRTC_rfl | exact Hinst].
      + (* proofIrrel *)
        destruct (VHasType_app_inv Hwf HG0 h2) as [A_f [B_f [H1 H2]]].
        pose proof (VIsDefEq_uniqU Hwf Hinj HG0 a2 H1) as hf.
        pose proof (VHasType_defeqU_l Hwf Hinj HG0 hf a1) as Hp_pi.
        destruct (VHasType_forallE_inv Hwf Hp_pi) as [[u_b b1] [v_b b2]].
        pose proof (VIsDefEqU_sort_inv Hinj HG0
                      (VIsDefEq_uniqU Hwf Hinj HG0 (VHasType_forallE b1 b2) Hp_pi))
          as Himax0.
        pose proof (VIsDefEq_sort_r Hwf (vctx_cons HG0 b1) b2) as b3.
        pose proof (VDF_defeqDF (@VDF_sortDF env U (A_f :: G0) v_b VLZero b3 I (vlevel_imax_eq_zero Himax0)) b2) as b2_zero.
        destruct (VHasType_lam_inv Hwf HG0 a3) as [[u_c c1] [B_c c2]].
        destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                    (VIsDefEqU_trans Hwf Hinj HG0
                       (VIsDefEq_uniqU Hwf Hinj HG0 (VHasType_lam c1 c2) a3) hf))
          as [[w1 u1] [w2 u2]].
        exists (VApp f0 a0); split; [exact VRTC_rfl |].
        exact (VN_proofIrrel
                 (VHasType_instN Hcl (VCtxInstN_zero G0 a0 A_f) b2_zero H2)
                 (VHasType_app H1 H2)
                 (VHasType_instN Hcl (VCtxInstN_zero G0 a0 A0)
                    (VDF_defeqDF u2 c2) (VDF_defeqDF (VDF_symm u1) H2))).
    - (* Part 2: f0 ≡ₚ vpe_apply l ((VLam A0 e0').lift.app (bvar 0)) *)
      intros l W h1.
      remember (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0))) as s eqn:Heqs.
      symmetry in Heqs.
      inversion h1 as
        [ G' x B_r Hrefl
        | G' l1 l2 _ _ _
        | G' c ci ls1 ls2 _ _ _ _ _
        | G' f1 f' a1 a' A' B' a_1 a_2 a_3 a_4 a_5 a_6
        | G' A_b A1 A2 b1 b2 u _ _ _
        | G' A_b A1 A2 B1 B2 u v _ _ _ _
        | G' s' A' B' f_body a_1 a_2
        | G' f_l A' B' e_r _ _
        | G' p x1 x2 a_1 a_2 a_3 ]; subst.
      + (* refl *)
        clear IH Hsz h1.
        assert (Hrefl_ind : forall m l G0 B_r,
          vpe_meas l <= m ->
          VCtxWF env U G0 ->
          vpe_depth l <= List.length G0 ->
          VHasType env U G0 (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0))) B_r ->
          exists e,
            VParRedTS env U Pat G0 (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0))) e /\
            VNormalEq env U G0 e (vpe_apply l e0')).
        { apply (@nat_strong_ind (fun m =>
            forall l G0 B_r,
              vpe_meas l <= m ->
              VCtxWF env U G0 ->
              vpe_depth l <= List.length G0 ->
              VHasType env U G0 (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0))) B_r ->
              exists e,
                VParRedTS env U Pat G0 (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0))) e /\
                VNormalEq env U G0 e (vpe_apply l e0'))).
          intros m IHm [| l0 | l0] G1 B1 Hm HG1 Hdep Hty1; simpl in *.
          - pose proof (VPRT_beta
                          (VParRedT_refl env U Pat (vliftN 1 0 A0 :: G1) (vliftN 1 1 e0'))
                          (VParRedT_refl env U Pat G1 (VBVar 0))) as hstep.
            unfold vinst0 in hstep. rewrite vinst_vliftN_bvar0 in hstep.
            exists e0'; split;
              [exact (VRTC_single hstep)
              |exact (VN_refl (VParRedT_hasType Hpp HG1 hstep Hty1))].
          - destruct G1 as [| C G1']; [simpl in Hdep; lia |].
            destruct (proj1 (@VIsDefEqU_weakN_iff env U 1 0 G1' (C :: G1')
                               (vpe_apply l0 (VApp (vlift (VLam A0 e0')) (VBVar 0)))
                               (vpe_apply l0 (VApp (vlift (VLam A0 e0')) (VBVar 0)))
                               Hinj HG1 (VCtxLiftN_one C G1'))
                        (ex_intro _ B1 Hty1))
              as [B1' a1].
            destruct (IHm (vpe_meas l0) ltac:(lia) l0 G1' B1' (Nat.le_refl _)
                          (proj1 HG1) ltac:(simpl in Hdep; lia) a1)
              as [e_sub [a2 a3]].
            exists (vlift e_sub); split.
            + exact (VParRedTS_weakN Hwf (VCtxLiftN_one C G1') a2).
            + exact (VNormalEq_weakN Hwf (VCtxLiftN_one C G1') a3).
          - destruct G1 as [| C G1']; [simpl in Hdep; lia |].
            destruct (VHasType_app_inv Hwf HG1 Hty1) as [A_app [B_app [H1 H2]]].
            destruct (IHm (vpe_meas (VPE_lift l0)) ltac:(simpl; lia)
                          (VPE_lift l0) (C :: G1') _ (Nat.le_refl _) HG1 Hdep H1)
              as [e_sub [a1 a2]].
            simpl in a1, a2.
            pose proof (VParRedTS_hasType Hpp HG1 a1 H1) as Hsub_ty.
            exists (VApp e_sub (VBVar 0)); split.
            + exact (VParRedTS_app a1 VRTC_rfl).
            + exact (VN_appDF Hsub_ty
                       (VHasType_defeqU_l Hwf Hinj HG1 (VNormalEq_defeq Hwf Hinj HG1 a2) Hsub_ty)
                       H2 H2 a2 (VN_refl H2)). }
        exact (Hrefl_ind _ l G0 B_r (Nat.le_refl _) HG0 W Hrefl).
      + exfalso; exact (vpe_isApp Heqs).
      + exfalso; exact (vpe_isApp Heqs).
      + (* appDF *)
        assert (Hdec : exists n : nat,
          a' = VBVar n /\
          ((f' = vliftN (n + 1) 0 (VLam A0 e0') /\
            vpe_apply l e0' = vliftN n 0 e0') \/
           (exists l' : VParRedExt,
              vpe_depth l' <= vpe_depth l /\
              f' = vpe_apply l' (VApp (vlift (VLam A0 e0')) (VBVar 0)) /\
              vpe_apply l e0' = VApp (vpe_apply l' e0') (VBVar n)))).
        { match goal with
          | H : vpe_apply l _ = VApp _ _ |- _ => exact (vpe_app_decomp H)
          | H : VApp _ _ = vpe_apply l _ |- _ => symmetry in H; exact (vpe_app_decomp H)
          end. }
        destruct Hdec as [n [-> [[-> Happly] | [l' [W' [-> Happly]]]]]].
        * simpl in a_2, a_5.
          pose proof (VHasType_defeqU_l Hwf Hinj HG0 (VNormalEq_defeq Hwf Hinj HG0 a_5) a_1) as Hf1_lam.
          destruct (VHasType_lam_inv Hwf HG0 a_2) as [[u_c c1] [B_c c2]].
          destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                      (VIsDefEq_uniqU Hwf Hinj HG0 a_2 (VHasType_lam c1 c2)))
            as [[w1 u1] _].
          destruct (proj1 (IH (vexpr_size f1) ltac:(simpl in Hsz; lia)
                              f1 G0 (vliftN (n + 1) 0 A0) (vliftN (n + 1) 1 e0')
                              (Nat.le_refl _) HG0)
                      a_5 a1 _ (VHasType_app a_1 a_3))
            as [e_res [b1 b2]].
          pose proof (VNormalEq_instN_r Hwf Hinj (vctx_cons HG0 c1)
                        (VHasType_defeqU_r Hwf Hinj HG0 (ex_intro _ _ u1) a_3)
                        a_6 (VCtxInstN_zero G0 a1 (vliftN (n + 1) 0 A0)) c2)
            as b2_inst.
          pose proof (VNormalEq_trans Hwf Hinj HG0 b2 b2_inst) as b2'.
          assert (Heq_inst : vinst0 (vliftN (n + 1) 1 e0') (VBVar n) = vliftN n 0 e0').
          { pose proof (f_equal (vliftN n 0) (vinst_vliftN_bvar0 e0' 0)) as H0.
            change (vinst (vliftN 1 1 e0') (VBVar 0) 0)
              with (vinst0 (vliftN 1 1 e0') (VBVar 0)) in H0.
            rewrite vliftN_vinst0, vliftN_comp in H0.
            simpl in H0.
            replace (vliftVar n 0 0) with n in H0 by (cbv [vliftVar]; simpl; lia).
            replace (n + 0) with n in H0 by lia.
            exact H0. }
          unfold vinst0 in b2' |- *.
          change (vinst (vliftN (n + 1) 1 e0') (VBVar n) 0)
            with (vinst0 (vliftN (n + 1) 1 e0') (VBVar n)) in b2'.
          rewrite Heq_inst, <- Happly in b2'.
          exists e_res; split; [exact b1 | exact b2'].
        * destruct (proj2 (IH (vexpr_size f1) ltac:(simpl in Hsz; lia)
                              f1 G0 A0 e0' (Nat.le_refl _) HG0)
                      l' (Nat.le_trans _ _ _ W' W) a_5)
            as [e_res [b1 b2]].
          rewrite Happly.
          pose proof (VParRedTS_hasType Hpp HG0 b1 a_1) as Hres_ty.
          exists (VApp e_res a1); split.
          -- exact (VParRedTS_app b1 VRTC_rfl).
          -- exact (VN_appDF Hres_ty
                      (VHasType_defeqU_l Hwf Hinj HG0 (VNormalEq_defeq Hwf Hinj HG0 b2) Hres_ty)
                      a_3 a_4 b2 a_6).
      + exfalso; match goal with
        | H : vpe_apply l _ = VLam _ _ |- _ => exact (vpe_isApp H)
        | H : VLam _ _ = vpe_apply l _ |- _ => symmetry in H; exact (vpe_isApp H)
        end.
      + exfalso; match goal with
        | H : vpe_apply l _ = VForallE _ _ |- _ => exact (vpe_isApp H)
        | H : VForallE _ _ = vpe_apply l _ |- _ => symmetry in H; exact (vpe_isApp H)
        end.
      + (* etaL *)
        destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG0 a_1)) as [[u_a hA] _].
        pose proof (vctx_cons HG0 hA) as HG0'.
        destruct (proj2 (IH (vexpr_size f_body) ltac:(simpl in Hsz; lia)
                            f_body (A' :: G0) A0 e0' (Nat.le_refl _) HG0')
                    (VPE_app l) ltac:(simpl; lia) a_2)
          as [b_res [b1 b2]].
        destruct (VNormalEq_defeq Hwf Hinj HG0' b2) as [T_c c1].
        simpl in c1.
        destruct (hasType_app_bvar0 Hwf Hinj HG0' (VIsDefEq_refl_r c1)) as [B_new b3].
        exists (VLam A' b_res); split.
        * exact (VParRedTS_lam VRTC_rfl b1).
        * exact (VN_etaL b3 b2).
      + exfalso; match goal with
        | H : vpe_apply l _ = VLam _ _ |- _ => exact (vpe_isApp H)
        | H : VLam _ _ = vpe_apply l _ |- _ => symmetry in H; exact (vpe_isApp H)
        end.
      + (* proofIrrel *)
        exists f0; split; [exact VRTC_rfl |].
        apply (VN_proofIrrel a_1 a_2).
        clear a_2 h1 IH Hsz f0.
        revert G0 HG0 p W a_1 a_3.
        induction l as [| l IHl | l IHl]; intros G0 HG0 p W a_1 a_3; simpl in *.
        * destruct (VHasType_app_inv Hwf HG0 a_3) as [A_app [B_app [b1 b2]]].
          destruct (VHasType_lam_inv Hwf HG0 b1) as [[u_b b3] [B_b b4]].
          destruct (VIsDefEqU_forallE_inv Hwf Hinj HG0
                      (VIsDefEq_uniqU Hwf Hinj HG0 (VHasType_lam b3 b4) b1))
            as [[w1 u1] _].
          pose proof (VDF_beta b4 (VDF_defeqDF (VDF_symm u1) b2)) as Hbeta.
          unfold vinst0 in Hbeta. rewrite vinst_vliftN_bvar0 in Hbeta.
          exact (VHasType_defeqU_l Hwf Hinj HG0 (ex_intro _ _ Hbeta) a_3).
        * destruct G0 as [| C G0']; [simpl in W; lia |].
          destruct (proj1 (@VIsDefEqU_weakN_iff env U 1 0 G0' (C :: G0')
                             (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0)))
                             (vpe_apply l (VApp (vlift (VLam A0 e0')) (VBVar 0)))
                             Hinj HG0 (VCtxLiftN_one C G0'))
                      (ex_intro _ p a_3))
            as [p0 b1].
          pose proof (VIsDefEq_uniqU Hwf Hinj HG0 a_3 (VIsDefEq_weak C Hcl b1)) as u1.
          pose proof (proj1 (@VHasType_weakN_iff env U 1 0 G0' (C :: G0')
                               p0 (VSort VLZero) Hwf Hinj HG0 (VCtxLiftN_one C G0'))
                        (VHasType_defeqU_l Hwf Hinj HG0 u1 a_1)) as hp0.
          pose proof (IHl G0' (proj1 HG0) p0 ltac:(simpl in W; lia) hp0 b1) as hsub.
          exact (VHasType_defeqU_r Hwf Hinj HG0 (VIsDefEqU_symm u1)
                   (VIsDefEq_weak C Hcl hsub)).
        * destruct G0 as [| C G0']; [simpl in W; lia |].
          destruct (hasType_app_bvar0 Hwf Hinj HG0 a_3) as [B_p b1].
          pose proof (VHasType_app (VIsDefEq_weak C Hcl b1) (VDF_bvar (VLookupZero C G0')))
            as Happ_b1.
          unfold vinst0 in Happ_b1. rewrite vinst_vliftN_bvar0 in Happ_b1.
          pose proof (VIsDefEq_uniqU Hwf Hinj HG0 a_3 Happ_b1) as Hp_eq.
          destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf (proj1 HG0) b1))
            as [[u_c b2] _].
          pose proof (VIsDefEq_sort_r Hwf (proj1 HG0) b2) as Hwf_uc.
          pose proof (VDF_defeqDF
                        (@VDF_sortDF env U G0' (VLIMax u_c VLZero) VLZero (conj Hwf_uc I) I (vlevel_imax_zero u_c))
                        (VHasType_forallE b2 (VHasType_defeqU_l Hwf Hinj HG0 Hp_eq a_1)))
            as Hpi_zero.
          pose proof (IHl G0' (proj1 HG0) _ ltac:(simpl in W; lia) Hpi_zero b1) as hsub.
          pose proof (VHasType_app (VIsDefEq_weak C Hcl hsub) (VDF_bvar (VLookupZero C G0')))
            as Happ_res.
          unfold vinst0 in Happ_res. rewrite vinst_vliftN_bvar0 in Happ_res.
          exact (VHasType_defeqU_r Hwf Hinj HG0 (VIsDefEqU_symm Hp_eq) Happ_res). }
  exact (proj1 (Hboth _ f G A e' (Nat.le_refl _) HG) Hnorm a B Happ_ty).
Qed.

(* NormalEq.parRed — BOTH upstream .extra cases proved axiom-free! *)

Theorem VNormalEq_parRed env U Pat G e1 e2 e2' :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VParRedT env U Pat G e2 e2' ->
  exists e1',
    VParRedTS env U Pat G e1 e1' /\
    VNormalEq env U G e1' e2'.
Proof.
  intros Hpp HG H1 H2.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  revert e2' HG H2.
  induction H1 as
    [ G e A l1
    | G l1 l2 lw1 lw2 leq
    | G c ci ls ls' l1 l2 l3 l4 l5
    | G f1 f2 a1 a2 A B l1 l2 l3 l4 l5 ih1 l6 ih2
    | G A A1 A2 b1 b2 u l1 l2 l3 ih1
    | G A A1 A2 B1 B2 u v l1 l2 ih1 l3 l4 ih2
    | G e2 A B e l1 l2 ih1
    | G e1 A B e l1 l2 ih1
    | G p h1 h2 l1 l2 l3 ];
    intros e2' HG H2.
  - (* refl *)
    exists e2'; split;
      [exact (VRTC_single H2) | exact (VN_refl (VParRedT_hasType Hpp HG H2 l1))].
  - (* sortDF *)
    inversion H2 as [| | | | | | | G' p r e_x m1 m2 m2' r1 r2]; subst.
    + exists (VSort l1); split;
        [exact (VRTC_single (VPRT_sort G l1)) | exact (VN_sortDF G lw1 lw2 leq)].
    + exfalso; exact (VPatternMatches_not_sort _ _ _ _ r2).
  - (* constDF — including upstream's first .extra sorry, proved unconditionally! *)
    inversion H2 as [| | | | | | | G' p r e_x m1 m2 m2' r1 r2 r3 r4]; subst.
    + exists (VConst c ls); split;
        [exact (VRTC_single (VPRT_const G c ls)) | exact (VN_constDF l1 l2 l3 l4 l5)].
    + destruct p as [c0 | |]; simpl in r2; try contradiction.
      destruct r2 as [Hc0 [Hm1 Hm2]]; subst c0 m1 m2.
      destruct m2'.
      assert (Hck_ls : @VPatternCheckOK (VIsDefEqU env U G) (VPConst c) ls tt (snd r)).
      { eapply VPatternCheckOK_map; [| exact r3].
        intros a b [T HT].
        pose proof (Forall2_vlevel_equiv_symm l5) as l5_sym.
        pose proof (VEqUpToLevels_vrhs_const a l3 l2 l5_sym) as Heul_a.
        pose proof (VEqUpToLevels_vrhs_const b l3 l2 l5_sym) as Heul_b.
        pose proof (VIsDefEq_eqUpToLevels Hwf HG HT Heul_b) as HT1.
        pose proof (VDF_symm (VIsDefEq_eqUpToLevels Hwf HG (VDF_symm HT1) Heul_a)) as HT2.
        exists T; exact HT2. }
      pose proof (@VPRT_extra env U Pat G (VPConst c) r (VConst c ls) ls tt tt
                    r1 (VPM_const c ls) Hck_ls
                    (fun x : VPatternPath (VPConst c) => match x with end)) as Hstep.
      pose proof (VHasType_const G l1 l2 l4) as Hty_ls.
      pose proof (VParRedT_hasType Hpp HG Hstep Hty_ls) as Hty_rhs.
      exists (@vrhs_apply (VPConst c) ls tt (fst r)); split.
      * exact (VRTC_single Hstep).
      * exact (VEqUpToLevels_normalEq Hwf Hinj HG
                 (VEqUpToLevels_vrhs_const (fst r) l2 l3 l5) Hty_rhs).
  - (* appDF *)
    inversion H2 as
      [ | | | G' g2 f2' b2 a2' r1 r2 | |
      | G' dom e b_res b2 b2' r1 r2
      | G' p r e_x m1 m2 m2' r1 r2 r3 r4 ]; subst.
    + destruct (ih1 _ HG r1) as [f1' [a_1 a_2]].
      destruct (ih2 _ HG r2) as [a1' [b_1 b_2]].
      exists (VApp f1' a1'); split; [exact (VParRedTS_app a_1 b_1) |].
      exact (VN_appDF (VParRedTS_hasType Hpp HG a_1 l1)
                      (VParRedT_hasType Hpp HG r1 l2)
                      (VParRedTS_hasType Hpp HG b_1 l3)
                      (VParRedT_hasType Hpp HG r2 l4)
                      a_2 b_2).
    + (* beta *)
      destruct (ih1 _ HG (VPRT_lam (VParRedT_refl env U Pat G dom) r1)) as [f' [a_1 a_2]].
      destruct (ih2 _ HG r2) as [a' [b_1 b_2]].
      destruct (VHasType_lam_inv Hwf HG l2) as [[u_d d1] [B_d d2]].
      destruct (VIsDefEqU_forallE_inv Hwf Hinj HG
                  (VIsDefEq_uniqU Hwf Hinj HG (VHasType_lam d1 d2) l2))
        as [[w1 u1] [w2 u2]].
      pose proof (vctx_cons HG d1) as HG'.
      pose proof (VParRedT_hasType Hpp HG' r1 (VDF_defeqDF u2 d2)) as d2'.
      pose proof (VParRedTS_hasType Hpp HG b_1 (VDF_defeqDF (VDF_symm u1) l3)) as l3'.
      destruct (VParRedExt_parRed_beta Hpp HG a_2
                  (VHasType_app
                     (VHasType_defeqU_l Hwf Hinj HG
                        (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG a_2))
                        (VHasType_lam d1 d2'))
                     l3'))
        as [e_res [h_1 h_2]].
      exists e_res; split.
      * exact (VRTC_trans (VParRedTS_app a_1 b_1) h_1).
      * exact (VNormalEq_trans Hwf Hinj HG h_2
                 (VNormalEq_instN_r Hwf Hinj HG' l3' b_2 (VCtxInstN_zero G a' dom) d2')).
    + (* extra *)
      exact (pp_norm_app Hpp HG l1 l2 l3 l4 l5 l6 r1 r2 r3 r4).
  - (* lamDF *)
    inversion H2 as
      [ | | | | G' dom2 A2' bd2 b2' r1 r2 | |
      | G' p r e_x m1 m2 m2' r1 r2 ]; subst.
    + pose proof (vctx_cons HG (VIsDefEq_refl_l l1)) as HG'.
      destruct (VNormalEq_defeq Hwf Hinj HG' l3) as [B0 h_1].
      pose proof (VHasType_defeqU_l Hwf Hinj HG'
                    (VNormalEq_defeq Hwf Hinj HG' l3) (VIsDefEq_refl_l h_1))
        as h_2.
      pose proof (VParRedT_defeqDFC Hpp HG
                    (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) (VDF_symm l2))
                    (VIsDefEq_defeqDFC (VEnvWF_closed Hwf)
                       (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) l2) h_2)
                    r2)
        as r2'.
      destruct (ih1 _ HG' r2') as [b1' [b_1 b_2]].
      exists (VLam A1 b1'); split.
      * exact (VParRedTS_lam VRTC_rfl
                 (VParRedTS_defeqDFC Hpp HG
                    (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) l1)
                    (VIsDefEq_refl_l h_1) b_1)).
      * exact (VN_lamDF l1
                 (VDF_trans l2
                    (VParRedT_defeq Hpp HG r1
                       (VHasType_defeqU_l Hwf Hinj HG (ex_intro _ _ l2) (VIsDefEq_refl_l l1))))
                 b_2).
    + exfalso; exact (VPatternMatches_not_lam _ _ _ _ _ r2).
  - (* forallEDF *)
    inversion H2 as
      [ | | | | | G' dom2 A2' cod2 B2' r1 r2 |
      | G' p r e_x m1 m2 m2' r1 r2 ]; subst.
    + destruct (ih1 _ HG r1) as [A1' [a_1 a_2]].
      pose proof (vctx_cons HG (VIsDefEq_refl_l l1)) as HG'.
      pose proof (VHasType_defeqU_l Hwf Hinj HG' (VNormalEq_defeq Hwf Hinj HG' l4) l3) as h_2.
      pose proof (VIsDefEq_transU_l Hwf Hinj HG l1 (VNormalEq_defeq Hwf Hinj HG l2)) as W_eq.
      pose proof (VParRedT_defeqDFC Hpp HG
                    (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) (VDF_symm W_eq))
                    (VIsDefEq_defeqDFC (VEnvWF_closed Hwf)
                       (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) W_eq) h_2)
                    r2)
        as r2'.
      destruct (ih2 _ HG' r2') as [B1' [b_1 b_2]].
      pose proof (VParRedT_defeq Hpp HG r1
                    (VHasType_defeqU_l Hwf Hinj HG (ex_intro _ _ W_eq) (VIsDefEq_refl_l l1)))
        as Hr1_eq.
      exists (VForallE A1' B1'); split.
      * exact (VParRedTS_forallE a_1
                 (VParRedTS_defeqDFC Hpp HG
                    (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) l1)
                    l3 b_1)).
      * exact (VN_forallEDF
                 (VIsDefEq_transU_l Hwf Hinj HG (VDF_trans W_eq Hr1_eq)
                    (VIsDefEqU_symm (VNormalEq_defeq Hwf Hinj HG a_2)))
                 a_2
                 (VParRedTS_hasType Hpp HG' b_1 l3)
                 b_2).
    + exfalso; exact (VPatternMatches_not_forallE _ _ _ _ _ r2).
  - (* etaL *)
    destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG l1)) as [[u hA] _].
    pose proof (vctx_cons HG hA) as HG'.
    destruct (ih1 _ HG'
                (VPRT_app (VParRedT_weakN Hwf (VCtxLiftN_one A G) H2)
                          (VPRT_bvar (A :: G) 0)))
      as [e_res [a_1 a_2]].
    exists (VLam A e_res); split.
    + exact (VParRedTS_lam VRTC_rfl a_1).
    + exact (VN_etaL (VParRedT_hasType Hpp HG H2 l1) a_2).
  - (* etaR *)
    inversion H2 as
      [ | | | | G' dom A' bd body' r1 r2 | |
      | G' p r e_x m1 m2 m2' r1 r2 ]; subst.
    + destruct (VIsType_forallE_inv Hwf (VIsDefEq_isType Hwf HG l1)) as [[u hA] _].
      pose proof (vctx_cons HG hA) as HG'.
      destruct (ih1 _ HG' r2) as [t [a_1 a_2]].
      assert (Hsplit :
        (exists A0, VParRedTS env U Pat G e1 (VLam A0 t) /\ VIsDefEqU env U G A0 A) \/
        (exists e', VParRedTS env U Pat G e1 e' /\ t = VApp (vlift e') (VBVar 0))).
      { clear H2 l2 ih1 a_2 r1 r2 body'.
        remember (VApp (vlift e1) (VBVar 0)) as start eqn:Hstart.
        revert e1 l1 Hstart.
        induction a_1 as [| y z h_rtc IHrtc h_step]; intros e1 l1 Hstart; subst.
        - right; exists e1; split; [exact VRTC_rfl | reflexivity].
        - destruct (IHrtc e1 l1 eq_refl) as [[A0 [h_1 h_2]] | [e' [h_1 ->]]].
          + pose proof (VIsDefEqU_of_r Hwf Hinj HG h_2 hA) as h_2'.
            destruct (VHasType_lam_inv Hwf HG (VParRedTS_hasType Hpp HG h_1 l1))
              as [_ [B_d d2]].
            left; exists A0; split; [| exact h_2].
            apply (VRTC_tail h_1).
            apply (VPRT_lam (VParRedT_refl env U Pat G A0)).
            exact (VParRedT_defeqDFC Hpp HG
                     (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) (VDF_symm h_2'))
                     (VIsDefEq_defeqDFC (VEnvWF_closed Hwf)
                        (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) h_2') d2)
                     h_step).
          + inversion h_step as
              [ | | | G'' f_s f_s' a_s a_s' b1 b2 | |
              | G'' dom_b bd_b bd_b' a_s a_s' b1 b2
              | G'' p_e r_e e_e m1_e m2_e m2'_e b1 b2 ]; subst.
            * inversion b2 as [| | | | | | | G3 p3 r3 e3 m1_3 m2_3 m2'_3 _ hm3]; subst.
              -- destruct (VParRedT_weakN_inv Hpp HG' (VCtxLiftN_one A G)
                             (VIsDefEq_weak A (VEnvWF_closed Hwf)
                                (VParRedTS_hasType Hpp HG h_1 l1))
                             b1)
                   as [e'' [b1' ->]].
                 right; exists e''; split; [exact (VRTC_tail h_1 b1') | reflexivity].
              -- exfalso; exact (VPatternMatches_not_bvar _ _ _ _ hm3).
            * inversion b2 as [| | | | | | | G3 p3 r3 e3 m1_3 m2_3 m2'_3 _ hm3]; subst.
              -- destruct e' as [| | | | dom0 bd0 |];
                 match goal with
                 | Heq_lam : VLam _ _ = vlift _ |- _ =>
                     unfold vlift in Heq_lam; simpl in Heq_lam;
                     try discriminate;
                     inversion Heq_lam; subst dom_b bd_b; clear Heq_lam
                 | Heq_lam : vlift _ = VLam _ _ |- _ =>
                     unfold vlift in Heq_lam; simpl in Heq_lam;
                     try discriminate;
                     inversion Heq_lam; subst dom_b bd_b; clear Heq_lam
                 end.
                 pose proof (VParRedTS_hasType Hpp HG h_1 l1) as l1'.
                 destruct (VHasType_lam_inv Hwf HG l1') as [[u_c c1] [B_c c2]].
                 destruct (VParRedT_weakN_inv Hpp
                             (vctx_cons HG' (VIsDefEq_weak A (VEnvWF_closed Hwf) c1))
                             (VCtxLiftN_succ dom0 (VCtxLiftN_one A G))
                             (VIsDefEq_weakN (VEnvWF_closed Hwf) c2
                                (VCtxLiftN_succ dom0 (VCtxLiftN_one A G)))
                             b1)
                   as [bd0' [b1' ->]].
                 unfold vinst0. rewrite vinst_vliftN_bvar0.
                 destruct (VIsDefEqU_forallE_inv Hwf Hinj HG
                             (VIsDefEq_uniqU Hwf Hinj HG (VHasType_lam c1 c2) l1'))
                   as [[w1 u1] _].
                 left; exists dom0; split.
                 ++ exact (VRTC_tail h_1
                             (VPRT_lam (VParRedT_refl env U Pat G dom0) b1')).
                 ++ exists (VSort w1); exact u1.
              -- exfalso; exact (VPatternMatches_not_bvar _ _ _ _ hm3).
            * exfalso.
              destruct p_e as [c_e | pf_e pa_e | pf_e]; simpl in b2.
              -- exact b2.
              -- destruct b2 as [_ [ls2_e hma_e]].
                 exact (VPatternMatches_not_bvar _ _ _ _ hma_e).
              -- exact (Params_pat_not_var Hpp b1). }
      destruct Hsplit as [[A0 [h_1 h_2]] | [e' [h_1 ->]]].
      * exists (VLam A0 t); split; [exact h_1 |].
        exact (VN_lamDF (VDF_symm (VIsDefEqU_of_r Hwf Hinj HG h_2 hA))
                        (VParRedT_defeq Hpp HG r1 hA) a_2).
      * pose proof (VN_etaR (VParRedTS_hasType Hpp HG h_1 l1) a_2) as Heta_r.
        destruct (VNormalEq_defeq Hwf Hinj HG' a_2) as [T_b a_3].
        exists e'; split; [exact h_1 |].
        exact (VNormalEq_trans Hwf Hinj HG Heta_r
                 (VN_lamDF hA (VParRedT_defeq Hpp HG r1 hA)
                           (VN_refl (VIsDefEq_refl_r a_3)))).
    + exfalso; exact (VPatternMatches_not_lam _ _ _ _ _ r2).
  - (* proofIrrel *)
    exists h1; split; [exact VRTC_rfl | exact (VN_proofIrrel l1 l2 (VParRedT_hasType Hpp HG H2 l3))].
Qed.

Theorem VNormalEq_parRedS env U Pat G e1 e2 e2' :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VParRedTS env U Pat G e2 e2' ->
  exists e1',
    VParRedTS env U Pat G e1 e1' /\
    VNormalEq env U G e1' e2'.
Proof.
  intros Hpp HG H1 H2.
  induction H2 as [| y z _ IH h2].
  - exists e1; split; [exact VRTC_rfl | exact H1].
  - destruct IH as [e1_mid [a1 a2]].
    destruct (VNormalEq_parRed Hpp HG a2 h2) as [e1' [b1 b2]].
    exists e1'; split; [exact (VRTC_trans a1 b1) | exact b2].
Qed.

Theorem VParRedTS_church_rosser env U Pat G e e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VParRedTS env U Pat G e e1 ->
  VParRedTS env U Pat G e e2 ->
  VCRDefEq env U Pat G e1 e2.
Proof.
  intros Hpp HG Hty H1 H2.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  split; [exists A; exact (VParRedTS_hasType Hpp HG H1 Hty) |].
  split; [exists A; exact (VParRedTS_hasType Hpp HG H2 Hty) |].
  induction H2 as [| b c h1 IH H2_step].
  - exists e1, e1; split; [exact VRTC_rfl | split; [exact H1 |]].
    exact (VN_refl (VParRedTS_hasType Hpp HG H1 Hty)).
  - pose proof (VParRedTS_hasType Hpp HG h1 Hty) as Hb_ty.
    destruct IH as [A1 [A2 [a1 [a2 a3]]]].
    assert (Hstrip :
      exists d1 d2,
        VParRedT env U Pat G A2 d1 /\
        VParRedTS env U Pat G c d2 /\
        VNormalEq env U G d1 d2).
    { clear a3 A1 a1.
      induction a2 as [| x y hx IHa2 hxy].
      - exists c, c; split; [exact H2_step | split; [exact VRTC_rfl |]].
        exact (VN_refl (VParRedT_hasType Hpp HG H2_step Hb_ty)).
      - destruct IHa2 as [u1 [u2 [p1 [p2 p3]]]].
        destruct (VParRedT_church_rosser Hpp HG (VParRedTS_hasType Hpp HG hx Hb_ty) p1 hxy)
          as [v1 [v2 [q1 [q2 q3]]]].
        destruct (VNormalEq_parRed Hpp HG (VNormalEq_symm Hwf Hinj HG p3) q1)
          as [w2 [s1 s2]].
        exists v2, w2; split; [exact q2 | split; [exact (VRTC_trans p2 s1) |]].
        exact (VNormalEq_symm Hwf Hinj HG (VNormalEq_trans Hwf Hinj HG s2 q3)). }
    destruct Hstrip as [d1 [d2 [b1 [b2 b3]]]].
    destruct (VNormalEq_parRed Hpp HG a3 b1) as [e1' [c1 c2]].
    exists e1', d2; split; [exact (VRTC_trans a1 c1) | split; [exact b2 |]].
    exact (VNormalEq_trans Hwf Hinj HG c2 b3).
Qed.

(* VCRDefEq equivalence relation and IsDefEq.church_rosser *)

Theorem VCRDefEq_normalEq env U Pat G e1 e2 :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VNormalEq env U G e1 e2 ->
  VCRDefEq env U Pat G e1 e2.
Proof.
  intros Hpp HG H.
  destruct (VNormalEq_defeq (pp_wf Hpp) (pp_inj Hpp) HG H) as [A HA].
  split; [exists A; exact (VIsDefEq_refl_l HA) |].
  split; [exists A; exact (VIsDefEq_refl_r HA) |].
  exists e1, e2; split; [exact VRTC_rfl | split; [exact VRTC_rfl | exact H]].
Qed.

Theorem VCRDefEq_refl env U Pat G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VCRDefEq env U Pat G e e.
Proof.
  intros Hpp HG Hty.
  exact (VCRDefEq_normalEq Hpp HG (VN_refl Hty)).
Qed.

Theorem VCRDefEq_defeq env U Pat G e1 e2 :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VCRDefEq env U Pat G e1 e2 ->
  VIsDefEqU env U G e1 e2.
Proof.
  intros Hpp HG [[A1 h1] [[A2 h2] [e1' [e2' [h3 [h4 h5]]]]]].
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  exists A1.
  exact (VIsDefEq_trans_l Hwf Hinj HG
           (VParRedTS_defeq Hpp HG h3 h1)
           (VIsDefEq_transU_r Hwf Hinj HG
              (VNormalEq_defeq Hwf Hinj HG h5)
              (VDF_symm (VParRedTS_defeq Hpp HG h4 h2)))).
Qed.

Theorem VCRDefEq_symm env U Pat G e1 e2 :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VCRDefEq env U Pat G e1 e2 ->
  VCRDefEq env U Pat G e2 e1.
Proof.
  intros Hpp HG [h1 [h2 [e1' [e2' [h3 [h4 h5]]]]]].
  split; [exact h2 | split; [exact h1 |]].
  exists e2', e1'; split; [exact h4 | split; [exact h3 |]].
  exact (VNormalEq_symm (pp_wf Hpp) (pp_inj Hpp) HG h5).
Qed.

Theorem VCRDefEq_trans env U Pat G e1 e2 e3 :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VCRDefEq env U Pat G e1 e2 ->
  VCRDefEq env U Pat G e2 e3 ->
  VCRDefEq env U Pat G e1 e3.
Proof.
  intros Hpp HG [l1 [[A2 l2] [l_e1' [l_e2' [l3 [l4 l5]]]]]]
                [_ [r2 [r_e2' [r_e3' [r3 [r4 r5]]]]]].
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  destruct (VParRedTS_church_rosser Hpp HG l2 l4 r3)
    as [_ [_ [m_1 [m_2 [m1 [m2 m3]]]]]].
  destruct (VNormalEq_parRedS Hpp HG l5 m1) as [a_e1 [a1 a2]].
  destruct (VNormalEq_parRedS Hpp HG (VNormalEq_symm Hwf Hinj HG r5) m2)
    as [b_e3 [b1 b2]].
  split; [exact l1 | split; [exact r2 |]].
  exists a_e1, b_e3.
  split; [exact (VRTC_trans l3 a1) | split; [exact (VRTC_trans r4 b1) |]].
  exact (VNormalEq_trans Hwf Hinj HG a2
           (VNormalEq_trans Hwf Hinj HG m3 (VNormalEq_symm Hwf Hinj HG b2))).
Qed.

Theorem VIsDefEq_church_rosser env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  VCRDefEq env U Pat G e1 e2.
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  assert (Hmk : forall G0 d1 d2 T d1' d2',
    VIsDefEq env U G0 d1 d2 T ->
    VParRedTS env U Pat G0 d1 d1' ->
    VParRedTS env U Pat G0 d2 d2' ->
    VNormalEq env U G0 d1' d2' ->
    VCRDefEq env U Pat G0 d1 d2).
  { intros G0 d1 d2 T d1' d2' Hd hr1 hr2 hn.
    split; [exists T; exact (VIsDefEq_refl_l Hd) |].
    split; [exists T; exact (VIsDefEq_refl_r Hd) |].
    exists d1', d2'; auto. }
  revert HG.
  induction H as
    [ G i ty h
    | G e1 e2 ty _ ih
    | G e1 e2 e3 ty _ ih1 _ ih2
    | G l1 l2 h1 h2 h3
    | G c ci ls1 ls2 h1 h2 h3 h4 h5
    | G f1 f2 a1 a2 A B h1 ih1 h2 ih2
    | G A1 A2 b1 b2 u B h1 ih1 h2 ih2
    | G A1 A2 B1 B2 u v h1 ih1 h2 ih2
    | G e1 e2 A B u _ _ _ ih2
    | G A e a B h1 _ h2 _
    | G e A B h1 _
    | G p h h' h1 _ h2 _ h3 _
    | G df ls h1 h2 h3 ];
    intros HG.
  - exact (VCRDefEq_refl Hpp HG (VDF_bvar h)).
  - exact (VCRDefEq_symm Hpp HG (ih HG)).
  - exact (VCRDefEq_trans Hpp HG (ih1 HG) (ih2 HG)).
  - exact (VCRDefEq_normalEq Hpp HG (VN_sortDF G h1 h2 h3)).
  - exact (VCRDefEq_normalEq Hpp HG (VN_constDF h1 h2 h3 h4 h5)).
  - destruct (ih1 HG) as [_ [_ [f1' [f2' [a_1 [a_2 a_3]]]]]].
    destruct (ih2 HG) as [_ [_ [a1' [a2' [b_1 [b_2 b_3]]]]]].
    refine (Hmk _ _ _ _ _ _ (VDF_appDF h1 h2)
               (VParRedTS_app a_1 b_1) (VParRedTS_app a_2 b_2) _).
    exact (VN_appDF (VParRedTS_hasType Hpp HG a_1 (VIsDefEq_refl_l h1))
                    (VParRedTS_hasType Hpp HG a_2 (VIsDefEq_refl_r h1))
                    (VParRedTS_hasType Hpp HG b_1 (VIsDefEq_refl_l h2))
                    (VParRedTS_hasType Hpp HG b_2 (VIsDefEq_refl_r h2))
                    a_3 b_3).
  - destruct (ih1 HG) as [_ [_ [A1' [A2' [a_1 [a_2 a_3]]]]]].
    pose proof (vctx_cons HG (VIsDefEq_refl_l h1)) as HG'.
    destruct (ih2 HG') as [_ [_ [b1' [b2' [b_1 [b_2 b_3]]]]]].
    pose proof (VParRedTS_defeqDFC Hpp HG
                  (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) h1)
                  (VIsDefEq_refl_r h2) b_2) as b_2'.
    pose proof (VParRedTS_defeq Hpp HG a_1 (VIsDefEq_refl_l h1)) as hA1_eq.
    refine (Hmk _ _ _ _ _ _ (VDF_lamDF h1 h2)
               (VParRedTS_lam a_1 b_1) (VParRedTS_lam a_2 b_2') _).
    exact (VN_lamDF hA1_eq
                    (VIsDefEq_transU_l Hwf Hinj HG hA1_eq (VNormalEq_defeq Hwf Hinj HG a_3))
                    b_3).
  - destruct (ih1 HG) as [_ [_ [A1' [A2' [a_1 [a_2 a_3]]]]]].
    pose proof (vctx_cons HG (VIsDefEq_refl_l h1)) as HG'.
    destruct (ih2 HG') as [_ [_ [B1' [B2' [b_1 [b_2 b_3]]]]]].
    pose proof (VParRedTS_defeqDFC Hpp HG
                  (VIsDefEqCtx_succ (VIsDefEqCtx_zero env U G) h1)
                  (VIsDefEq_refl_r h2) b_2) as b_2'.
    refine (Hmk _ _ _ _ _ _ (VDF_forallEDF h1 h2)
               (VParRedTS_forallE a_1 b_1) (VParRedTS_forallE a_2 b_2') _).
    exact (VN_forallEDF (VParRedTS_defeq Hpp HG a_1 (VIsDefEq_refl_l h1))
                        a_3
                        (VParRedTS_hasType Hpp HG' b_1 (VIsDefEq_refl_l h2))
                        b_3).
  - exact (ih2 HG).
  - pose proof (VDF_beta h1 h2) as hbeta.
    refine (Hmk _ _ _ _ _ _ hbeta
               (VRTC_single (VPRT_beta (VParRedT_refl env U Pat (A :: G) e)
                                       (VParRedT_refl env U Pat G a)))
               VRTC_rfl _).
    exact (VN_refl (VIsDefEq_refl_r hbeta)).
  - pose proof (VIsDefEq_refl_l h1) as he_ty.
    exact (VCRDefEq_normalEq Hpp HG
             (VN_etaL he_ty
                (VN_refl (VHasType_app (VIsDefEq_weak A Hcl he_ty)
                                       (VDF_bvar (VLookupZero A G)))))).
  - exact (VCRDefEq_normalEq Hpp HG
             (VN_proofIrrel (VIsDefEq_refl_l h1) (VIsDefEq_refl_l h2) (VIsDefEq_refl_l h3))).
  - destruct (@pp_extra_pat env Pat Hpp U G df ls h1 h2 h3)
      as [p [r [m1 [m2 [a_1 [a_2 [a_3 a_4]]]]]]].
    pose proof (@VDF_extra env U G df ls h1 h2 h3) as hextra.
    refine (Hmk _ _ _ _ _ _ hextra
               (VRTC_single (VPRT_extra a_1 a_2 a_3
                               (fun x => VParRedT_refl env U Pat G (vpath_get m2 x))))
               VRTC_rfl _).
    rewrite <- a_4.
    exact (VN_refl (VIsDefEq_refl_r hextra)).
Qed.

Corollary VIsDefEq_church_rosser_params env U G e1 e2 A :
  PatternParams env ->
  VCtxWF env U G ->
  VIsDefEq env U G e1 e2 A ->
  exists Pat, PatternParamsFor env Pat /\ VCRDefEq env U Pat G e1 e2.
Proof.
  intros [Pat Hpp] HG H.
  exists Pat; split; [exact Hpp | exact (VIsDefEq_church_rosser Hpp HG H)].
Qed.

(* ========================================================================= *)
(* 4. Weak Head Reduction, Kashima Standardization, and Type Inference       *)
(*    (Lean4Lean/Theory/Typing/HeadReduction.lean)                           *)
(* ========================================================================= *)

Theorem Params_simple_app env Pat p r p1 p2 :
  PatternParamsFor env Pat ->
  Pat p r ->
  VSubpattern (VPApp p1 p2) p ->
  VPApp p1 p2 = p.
Proof.
  intros Hpp H Hsub.
  destruct (pp_simple Hpp H) as [[rec m c n | hd] ->]; simpl in Hsub.
  - inversion Hsub as [| f0 a0 Hsub0 | f0 a0 Hsub0 |]; subst.
    + reflexivity.
    + destruct (VSubpattern_varN_const Hsub0) as [[|k] Hk]; discriminate.
    + destruct (VSubpattern_varN_const Hsub0) as [[|k] Hk]; discriminate.
  - inversion Hsub.
Qed.

Definition VIsMajorPremise (Pat : VPatRel) (e : VExpr) : Prop :=
  exists p, (exists r, Pat p r) /\
    exists p1 p2, VSubpattern (VPApp p1 p2) p /\
      exists m1 m2, VPatternMatches p1 e m1 m2.

Theorem VIsMajorPremise_lift' Pat rho e :
  VIsMajorPremise Pat (vlift' rho e) <-> VIsMajorPremise Pat e.
Proof.
  split.
  - intros [p [h1 [p1 [p2 [h2 [m1 [m2' h3]]]]]]].
    destruct (proj1 (@VPatternMatches_vlift' p1 rho e m1 m2') h3) as [m2 [h4 _]].
    exists p; split; [exact h1 | exists p1, p2; split; [exact h2 | exists m1, m2; exact h4]].
  - intros [p [h1 [p1 [p2 [h2 [m1 [m2 h3]]]]]]].
    exists p; split; [exact h1 | exists p1, p2; split; [exact h2 |]].
    exists m1, (vmenv_map (vlift' rho) m2).
    apply VPatternMatches_vlift'. exists m2; split; [exact h3 | reflexivity].
Qed.

Theorem VIsMajorPremise_instN Pat e1 a k :
  VIsMajorPremise Pat e1 ->
  VIsMajorPremise Pat (vinst e1 a k).
Proof.
  intros [p [h1 [p1 [p2 [h2 [m1 [m2 h3]]]]]]].
  exists p; split; [exact h1 | exists p1, p2; split; [exact h2 |]].
  exists m1, (vmenv_map (fun x => vinst x a k) m2).
  exact (VPatternMatches_vinst a k h3).
Qed.

Theorem VIsMajorPremise_lam Pat A e :
  ~ VIsMajorPremise Pat (VLam A e).
Proof.
  intros [p [_ [p1 [_ [_ [m1 [m2 hm]]]]]]].
  exact (VPatternMatches_not_lam p1 A e m1 m2 hm).
Qed.

Theorem VPatternCheckOK_weak' env U rho G G' p (ck : VPatternCheck p) m1 m2 :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VPatternCheckOK (VIsDefEqU env U G) m1 m2 ck ->
  VPatternCheckOK (VIsDefEqU env U G') m1 (vmenv_map (vlift' rho) m2) ck.
Proof.
  intros Hwf W Hck.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  eapply VPatternCheckOK_map; [| exact Hck].
  intros a b [T HT].
  rewrite <- !vrhs_apply_vlift'.
  exists (vlift' rho T).
  exact (VIsDefEq_weak' Hcl W HT).
Qed.

(* Weak Head Reduction *)

Inductive VWHRed (env : VEnv) (U : nat) (Pat : VPatRel) (G : list VExpr) :
    VExpr -> VExpr -> Prop :=
| VWHR_app : forall f f' a,
    VWHRed env U Pat G f f' ->
    VWHRed env U Pat G (VApp f a) (VApp f' a)
| VWHR_major : forall f a a',
    VIsMajorPremise Pat f ->
    VWHRed env U Pat G a a' ->
    VWHRed env U Pat G (VApp f a) (VApp f a')
| VWHR_beta : forall A e a,
    VWHRed env U Pat G (VApp (VLam A e) a) (vinst0 e a)
| VWHR_extra : forall p r e m1 (m2 : VMatchEnv p),
    Pat p r ->
    VPatternMatches p e m1 m2 ->
    VPatternCheckOK (VIsDefEqU env U G) m1 m2 (snd r) ->
    VWHRed env U Pat G e (@vrhs_apply p m1 m2 (fst r)).

Arguments VWHR_beta {env U Pat} G A e a.

Theorem VWHRed_defeqDFC env U Pat G0 G1 G2 e1 e2 :
  VEnvWF env ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VWHRed env U Pat G1 e1 e2 ->
  VWHRed env U Pat G2 e1 e2.
Proof.
  intros Hwf W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  induction H as [f f' a _ IH | f a a' h1 _ IH | A e a | p r e m1 m2 h1 h2 h3].
  - exact (VWHR_app a IH).
  - exact (VWHR_major h1 IH).
  - apply VWHR_beta.
  - refine (VWHR_extra h1 h2 _).
    eapply VPatternCheckOK_map; [| exact h3].
    intros a b [T HT]. exists T. exact (VIsDefEq_defeqDFC Hcl W HT).
Qed.

Theorem VWHRed_weak' env U Pat rho G G' e1 e2 :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VWHRed env U Pat G e1 e2 ->
  VWHRed env U Pat G' (vlift' rho e1) (vlift' rho e2).
Proof.
  intros Hwf W H.
  induction H as [f f' a _ IH | f a a' h1 _ IH | A e a | p r e m1 m2 h1 h2 h3]; simpl.
  - exact (VWHR_app (vlift' rho a) IH).
  - exact (VWHR_major (proj2 (VIsMajorPremise_lift' Pat rho f) h1) IH).
  - rewrite vlift'_vinst_hi. apply VWHR_beta.
  - rewrite vrhs_apply_vlift'.
    eapply VWHR_extra.
    + exact h1.
    + apply VPatternMatches_vlift'. exists m2; split; [exact h2 | reflexivity].
    + exact (VPatternCheckOK_weak' Hwf W h3).
Qed.

Theorem VWHRed_weakN env U Pat n k G G' e1 e2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VWHRed env U Pat G e1 e2 ->
  VWHRed env U Pat G' (vliftN n k e1) (vliftN n k e2).
Proof.
  intros Hwf W H.
  rewrite <- !vlift'_consN_skipN.
  exact (VWHRed_weak' Hwf (proj1 (VCtxLiftN_iff_VCtxLift' n k G G') W) H).
Qed.

Theorem VWHRed_weakU_inv env U Pat rho G G' e1 e2' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' rho G G' ->
  VWHRed env U Pat G' (vlift' rho e1) e2' ->
  exists e2, e2' = vlift' rho e2 /\ VWHRed env U Pat G e1 e2.
Proof.
  intros Hwf Hinj HG' W H.
  remember (vlift' rho e1) as e1' eqn:Heq.
  revert e1 Heq.
  induction H as [f f' a h1 IH | f a a' h1 h2 IH | A e a | p r e m1 m2 h1 h2 h3];
    intros e1 Heq.
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IH _ eq_refl) as [f2 [-> a1]].
    exists (VApp f2 e1_2); split; [reflexivity | exact (VWHR_app e1_2 a1)].
  - destruct e1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IH _ eq_refl) as [a2 [-> a1]].
    exists (VApp e1_1 a2); split;
      [reflexivity | exact (VWHR_major (proj1 (VIsMajorPremise_lift' Pat rho e1_1) h1) a1)].
  - destruct e1; simpl in Heq; try discriminate.
    destruct e1_1; simpl in Heq; try discriminate.
    inversion Heq; subst.
    exists (vinst0 e1_1_2 e1_2); split;
      [symmetry; apply vlift'_vinst_hi | apply VWHR_beta].
  - subst e.
    destruct (proj1 (@VPatternMatches_vlift' p rho e1 m1 m2) h2) as [m2_0 [h4 ->]].
    exists (@vrhs_apply p m1 m2_0 (fst r)); split.
    + symmetry. apply vrhs_apply_vlift'.
    + refine (VWHR_extra h1 h4 _).
      eapply VPatternCheckOK_map; [| exact h3].
      intros a b Hab.
      rewrite <- !vrhs_apply_vlift' in Hab.
      exact (proj1 (@VIsDefEqU_weak'_iff env U rho G G' _ _ Hwf Hinj HG' W) Hab).
Qed.

Theorem VWHRed_parRed env U Pat G e1 e2 :
  VWHRed env U Pat G e1 e2 ->
  VParRedT env U Pat G e1 e2.
Proof.
  induction 1 as [f f' a _ IH | f a a' _ _ IH | A e a | p r e m1 m2 h1 h2 h3].
  - exact (VPRT_app IH (VParRedT_refl env U Pat G a)).
  - exact (VPRT_app (VParRedT_refl env U Pat G f) IH).
  - exact (VPRT_beta (VParRedT_refl env U Pat (A :: G) e) (VParRedT_refl env U Pat G a)).
  - exact (VPRT_extra h1 h2 h3 (fun x => VParRedT_refl env U Pat G (vpath_get m2 x))).
Qed.

Theorem VWHRed_defeq env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VWHRed env U Pat G e1 e2 ->
  VHasType env U G e1 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hpp HG H He.
  exact (VParRedT_defeq Hpp HG (VWHRed_parRed H) He).
Qed.

Theorem VWHRed_hasType env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VWHRed env U Pat G e1 e2 ->
  VHasType env U G e1 A ->
  VHasType env U G e2 A.
Proof.
  intros Hpp HG H He.
  exact (VIsDefEq_refl_r (VWHRed_defeq Hpp HG H He)).
Qed.

Theorem VWHRed_instN env U Pat G0 a A0 k G1 G e1 e2 :
  VEnvWF env ->
  VHasType env U G0 a A0 ->
  VCtxInstN G0 a A0 k G1 G ->
  VWHRed env U Pat G1 e1 e2 ->
  VWHRed env U Pat G (vinst e1 a k) (vinst e2 a k).
Proof.
  intros Hwf H0 W H.
  induction H as [f f' arg _ IH | f arg arg' h1 _ IH | A e arg | p r e m1 m2 h1 h2 h3]; simpl.
  - exact (VWHR_app (vinst arg a k) IH).
  - exact (VWHR_major (VIsMajorPremise_instN a k h1) IH).
  - rewrite vinst0_vinst_hi. apply VWHR_beta.
  - rewrite vrhs_apply_vinst.
    exact (VWHR_extra h1 (VPatternMatches_vinst a k h2) (VPatternCheckOK_instN Hwf W H0 h3)).
Qed.

(* Weak Head Normal Forms and Determinism of Weak Head Reduction *)

Definition VWHNF (env : VEnv) (U : nat) (Pat : VPatRel) (G : list VExpr) (e : VExpr) : Prop :=
  forall e', ~ VWHRed env U Pat G e e'.

Theorem VWHNF_bvar env U Pat G i :
  VWHNF env U Pat G (VBVar i).
Proof.
  intros e' H. inversion H as [| | | p r e0 m1 m2 _ hm _]; subst.
  exact (VPatternMatches_not_bvar p i m1 m2 hm).
Qed.

Theorem VWHNF_lam env U Pat G A e :
  VWHNF env U Pat G (VLam A e).
Proof.
  intros e' H. inversion H as [| | | p r e0 m1 m2 _ hm _]; subst.
  exact (VPatternMatches_not_lam p A e m1 m2 hm).
Qed.

Theorem VWHNF_sort env U Pat G u :
  VWHNF env U Pat G (VSort u).
Proof.
  intros e' H. inversion H as [| | | p r e0 m1 m2 _ hm _]; subst.
  exact (VPatternMatches_not_sort p u m1 m2 hm).
Qed.

Theorem VWHNF_forallE env U Pat G A B :
  VWHNF env U Pat G (VForallE A B).
Proof.
  intros e' H. inversion H as [| | | p r e0 m1 m2 _ hm _]; subst.
  exact (VPatternMatches_not_forallE p A B m1 m2 hm).
Qed.

Theorem VWHNF_subpattern env U Pat G p r p1 e m1 m2 :
  PatternParamsFor env Pat ->
  Pat p r ->
  VSubpattern p1 p ->
  p1 <> p ->
  VPatternMatches p1 e m1 m2 ->
  VWHNF env U Pat G e.
Proof.
  intros Hpp h1 h2 h3 h4.
  assert (Hex : exists c n, p1 = vpattern_varN (VPConst c) n).
  { destruct (pp_simple Hpp h1) as [[rec k0 c0 n0 | hd] Hp]; subst p; simpl in h2.
    - inversion h2 as [| f0 a0 Hsub | f0 a0 Hsub |]; subst.
      + exfalso; exact (h3 eq_refl).
      + destruct (VSubpattern_varN_const Hsub) as [n Hn]; exists rec, n; exact Hn.
      + destruct (VSubpattern_varN_const Hsub) as [n Hn]; exists c0, n; exact Hn.
    - inversion h2; subst; exfalso; exact (h3 eq_refl). }
  destruct Hex as [c [n ->]].
  assert (Hno_const : forall r0, ~ Pat (VPConst c) r0).
  { intros r0 h0.
    destruct (pp_uniq Hpp h1 h0
                (VSubpattern_trans (VSubpattern_varN n (VSub_refl (VPConst c))) h2)
                (vpattern_inter_self (VPConst c)))
      as [Heq1 _].
    subst p. apply h3. symmetry.
    exact (VSubpattern_antisymm h2 (VSubpattern_varN n (VSub_refl (VPConst c)))). }
  clear h3.
  intros e' H2.
  revert n m1 m2 h2 h4.
  induction H2 as [f f' a r1 IH | f a a' r1 r2 IH | A0 bd0 a0 | p' r' e0 m1' m2' r1 r2 r3];
    intros n m1 m2 h2 h4.
  - destruct n as [|n]; simpl in h4; [exact h4 |].
    destruct h4 as [_ h4f].
    exact (IH n m1 (snd m2)
             (VSubpattern_trans (VSub_varL (VSub_refl _)) h2) h4f).
  - destruct n as [|n]; simpl in h4; [exact h4 |].
    destruct h4 as [_ h4f].
    destruct r1 as [p' [[r' h1'] [p1' [p2' [h2' [mf1 [mf2 h3']]]]]]].
    pose proof (Params_simple_app Hpp h1' h2') as Heq_p'; subst p'.
    destruct (pp_simple Hpp h1) as [[rec k0 c0 n0 | hd] Hp]; subst p; simpl in h2.
    + destruct (proj1 (VPatternMatches_inter p1' (vpattern_varN (VPConst c) n) f)
                  (conj (ex_intro _ mf1 (ex_intro _ mf2 h3'))
                        (ex_intro _ m1 (ex_intro _ (snd m2) h4f))))
        as [p_int [_ [_ [a1 _]]]].
      inversion h2 as [| f0 a0 h2_sub | f0 a0 h2_sub |]; subst.
      * pose proof (pp_app_l_uniq Hpp h1 h1' (VSub_refl _) (VSub_refl _) h2_sub) as Hnone.
        rewrite Hnone in a1; discriminate.
      * pose proof (pp_app_uniq Hpp h1' h1 (VSub_refl _) (VSub_refl _) (VSub_refl _)
                      (VSubpattern_trans (VSub_varL (VSub_refl _)) h2_sub)) as Hnone.
        rewrite Hnone in a1; discriminate.
    + inversion h2.
  - exact (VPatternMatches_not_app_lam _ _ _ _ _ _ h4).
  - destruct (proj1 (VPatternMatches_inter p' (vpattern_varN (VPConst c) n) e0)
                (conj (ex_intro _ m1' (ex_intro _ m2' r2))
                      (ex_intro _ m1 (ex_intro _ m2 h4))))
      as [p_int [_ [_ [a1 _]]]].
    destruct (pp_uniq Hpp h1 r1 h2 a1) as [Heq1 Heq2]; subst p p'.
    destruct n as [|n]; simpl in r1.
    + exact (Hno_const r' r1).
    + exact (Params_pat_not_var Hpp r1).
Qed.

Theorem VIsMajorPremise_whnf env U Pat G e :
  PatternParamsFor env Pat ->
  VIsMajorPremise Pat e ->
  VWHNF env U Pat G e.
Proof.
  intros Hpp [p [[r h1] [p1 [p2 [h2 [m1 [m2 h3]]]]]]].
  eapply (VWHNF_subpattern Hpp h1
            (VSubpattern_trans (@VSub_appL p1 p1 p2 (VSub_refl p1)) h2));
    [| exact h3].
  intros Heq; subst p1.
  pose proof (VSubpattern_antisymm h2 (@VSub_appL p p p2 (VSub_refl p))) as Habs.
  pose proof (f_equal vpattern_size Habs) as Hsz; simpl in Hsz; lia.
Qed.

Theorem VWHRed_determ env U Pat G e e1 e2 :
  PatternParamsFor env Pat ->
  VWHRed env U Pat G e e1 ->
  VWHRed env U Pat G e e2 ->
  e1 = e2.
Proof.
  intros Hpp H1.
  revert e2.
  induction H1 as [f f' a l1 IH | f a a' l1 l2 IH | A e0 a | p r e m1 m2 l1 l2 l3];
    intros e2 H2.
  - inversion H2 as [g g' b r1 | g b b' r1 r2 | A0 bd0 b | p' r' e0 m1' m2' r1 r2 _]; subst.
    + f_equal; exact (IH _ r1).
    + exfalso; exact (VIsMajorPremise_whnf Hpp r1 l1).
    + exfalso; exact (VWHNF_lam l1).
    + exfalso.
      destruct p' as [c' | pf' pa' | pf']; simpl in r2.
      * exact r2.
      * destruct r2 as [r3 _].
        refine (VIsMajorPremise_whnf Hpp _ l1).
        exists (VPApp pf' pa'); split; [exists r'; exact r1 |].
        exists pf', pa'; split; [apply VSub_refl | exists m1', (fst m2'); exact r3].
      * exact (Params_pat_not_var Hpp r1).
  - inversion H2 as [g g' b r1 | g b b' r1 r2 | A0 bd0 b | p' r' e0 m1' m2' r1 r2 _]; subst.
    + exfalso; exact (VIsMajorPremise_whnf Hpp l1 r1).
    + f_equal; exact (IH _ r2).
    + exfalso; exact (VIsMajorPremise_lam l1).
    + exfalso.
      destruct p' as [c' | pf' pa' | pf']; simpl in r2.
      * exact r2.
      * destruct r2 as [_ [ls2' r4]].
        refine (VWHNF_subpattern Hpp r1 (@VSub_appR pa' pf' pa' (VSub_refl pa')) _ r4 l2).
        intros Heq; pose proof (f_equal vpattern_size Heq); simpl in *; lia.
      * exact (Params_pat_not_var Hpp r1).
  - inversion H2 as [g g' b r1 | g b b' r1 _ | | p' r' e_ex m1' m2' _ r2 _]; subst.
    + exfalso; exact (VWHNF_lam r1).
    + exfalso; exact (VIsMajorPremise_lam r1).
    + reflexivity.
    + exfalso; exact (VPatternMatches_not_app_lam _ _ _ _ _ _ r2).
  - inversion H2 as [g g' b r1 | g b b' r1 r2 | A0 bd0 b | p' r' e0 m1' m2' r1 r2 _]; subst.
    + exfalso.
      destruct p as [c | pf pa | pf]; simpl in l2.
      * exact l2.
      * destruct l2 as [l_f _].
        refine (VIsMajorPremise_whnf Hpp _ r1).
        exists (VPApp pf pa); split; [exists r; exact l1 |].
        exists pf, pa; split; [apply VSub_refl | exists m1, (fst m2); exact l_f].
      * exact (Params_pat_not_var Hpp l1).
    + exfalso.
      destruct p as [c | pf pa | pf]; simpl in l2.
      * exact l2.
      * destruct l2 as [_ [ls2 l4]].
        refine (VWHNF_subpattern Hpp l1 (@VSub_appR pa pf pa (VSub_refl pa)) _ l4 r2).
        intros Heq; pose proof (f_equal vpattern_size Heq); simpl in *; lia.
      * exact (Params_pat_not_var Hpp l1).
    + exfalso; exact (VPatternMatches_not_app_lam _ _ _ _ _ _ l2).
    + destruct (proj1 (VPatternMatches_inter p' p e)
                  (conj (ex_intro _ m1' (ex_intro _ m2' r2))
                        (ex_intro _ m1 (ex_intro _ m2 l2))))
        as [p_int [_ [_ [a1 _]]]].
      destruct (pp_uniq Hpp l1 r1 (VSub_refl p) a1) as [Heq_p _]; subst p'.
      pose proof (pp_rhs_uniq Hpp l1 r1) as Heq_r; subst r'.
      destruct (VPatternMatches_determ l2 r2) as [-> ->].
      reflexivity.
Qed.

(* Multi-step Weak Head Reduction *)

Definition VWHRedS (env : VEnv) (U : nat) (Pat : VPatRel) (G : list VExpr) :
    VExpr -> VExpr -> Prop :=
  VRTClosure (VWHRed env U Pat G).

Theorem VWHRedS_defeqDFC env U Pat G0 G1 G2 e1 e2 :
  VEnvWF env ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VWHRedS env U Pat G1 e1 e2 ->
  VWHRedS env U Pat G2 e1 e2.
Proof.
  intros Hwf W H.
  induction H as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_defeqDFC Hwf W h2)).
Qed.

Theorem VWHRedS_parRedS env U Pat G e1 e2 :
  VWHRedS env U Pat G e1 e2 ->
  VParRedTS env U Pat G e1 e2.
Proof.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_parRed h2)).
Qed.

Theorem VWHRedS_app env U Pat G f f' a :
  VWHRedS env U Pat G f f' ->
  VWHRedS env U Pat G (VApp f a) (VApp f' a).
Proof.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHR_app a h2)).
Qed.

Theorem VWHRedS_major env U Pat G f a a' :
  VIsMajorPremise Pat f ->
  VWHRedS env U Pat G a a' ->
  VWHRedS env U Pat G (VApp f a) (VApp f a').
Proof.
  intros Hmaj.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHR_major Hmaj h2)).
Qed.

Theorem VWHRedS_defeq env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VWHRedS env U Pat G e1 e2 ->
  VHasType env U G e1 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hpp HG H He.
  exact (VParRedTS_defeq Hpp HG (VWHRedS_parRedS H) He).
Qed.

Theorem VWHRedS_hasType env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VWHRedS env U Pat G e1 e2 ->
  VHasType env U G e1 A ->
  VHasType env U G e2 A.
Proof.
  intros Hpp HG H He.
  exact (VIsDefEq_refl_r (VWHRedS_defeq Hpp HG H He)).
Qed.

Theorem VWHRedS_weak' env U Pat rho G G' e1 e2 :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VWHRedS env U Pat G e1 e2 ->
  VWHRedS env U Pat G' (vlift' rho e1) (vlift' rho e2).
Proof.
  intros Hwf W.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_weak' Hwf W h2)).
Qed.

Theorem VWHRedS_weakN env U Pat n k G G' e1 e2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VWHRedS env U Pat G e1 e2 ->
  VWHRedS env U Pat G' (vliftN n k e1) (vliftN n k e2).
Proof.
  intros Hwf W H.
  rewrite <- !vlift'_consN_skipN.
  exact (VWHRedS_weak' Hwf (proj1 (VCtxLiftN_iff_VCtxLift' n k G G') W) H).
Qed.

Theorem VWHRedS_instN env U Pat G0 a A0 k G1 G e1 e2 :
  VEnvWF env ->
  VHasType env U G0 a A0 ->
  VCtxInstN G0 a A0 k G1 G ->
  VWHRedS env U Pat G1 e1 e2 ->
  VWHRedS env U Pat G (vinst e1 a k) (vinst e2 a k).
Proof.
  intros Hwf H0 W.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_instN Hwf H0 W h2)).
Qed.

Theorem VWHNF_whRedS env U Pat G e e' :
  VWHNF env U Pat G e ->
  VWHRedS env U Pat G e e' ->
  e = e'.
Proof.
  intros Hnf Hred.
  apply (@VRTC_head_ind VExpr (VWHRed env U Pat G)
           (fun x z => VWHNF env U Pat G x -> x = z)
           (fun x _ => eq_refl)
           (fun x y z h1 _ _ Hnfx => False_ind _ (Hnfx y h1))
           e e' Hred Hnf).
Qed.

Theorem VWHRedS_determ env U Pat G e e1 e2 :
  PatternParamsFor env Pat ->
  VWHRedS env U Pat G e e1 ->
  VWHNF env U Pat G e1 ->
  VWHRedS env U Pat G e e2 ->
  VWHNF env U Pat G e2 ->
  e1 = e2.
Proof.
  intros Hpp H1 W1 H2 W2.
  revert e2 H2 W2.
  refine (@VRTC_head_ind VExpr (VWHRed env U Pat G)
            (fun x z => VWHNF env U Pat G z ->
               forall e2, VWHRedS env U Pat G x e2 -> VWHNF env U Pat G e2 -> z = e2)
            _ _ e e1 H1 W1).
  - intros x Wx e2 H2 W2.
    exact (VWHNF_whRedS Wx H2).
  - intros x y z l1 _ IH Wz e2 H2 W2.
    destruct (VRTC_to_hd H2) as [| x0 y' z' r1 r2].
    + exfalso; exact (W2 y l1).
    + pose proof (VWHRed_determ Hpp l1 r1) as Heq; subst y'.
      exact (IH Wz z' (VRTC_of_hd r2) W2).
Qed.

Theorem VWHRedS_weakU_inv env U Pat rho G G' e1 e2' :
  VEnvWF env ->
  DefEqInjectivity env ->
  VCtxWF env U G' ->
  VCtxLift' rho G G' ->
  VWHRedS env U Pat G' (vlift' rho e1) e2' ->
  exists e2, e2' = vlift' rho e2 /\ VWHRedS env U Pat G e1 e2.
Proof.
  intros Hwf Hinj HG' W H.
  induction H as [| y z _ IH h2].
  - exists e1; split; [reflexivity | exact VRTC_rfl].
  - destruct IH as [y0 [-> a1]].
    destruct (VWHRed_weakU_inv Hwf Hinj HG' W h2) as [z0 [-> a2]].
    exists z0; split; [reflexivity | exact (VRTC_tail a1 a2)].
Qed.

(* Kashima Standard Reduction (StRed) and Standardization *)

Inductive VStRed (env : VEnv) (U : nat) (Pat : VPatRel) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VStR_bvar : forall G e i,
    VWHRedS env U Pat G e (VBVar i) ->
    VStRed env U Pat G e (VBVar i)
| VStR_sort : forall G e u,
    VWHRedS env U Pat G e (VSort u) ->
    VStRed env U Pat G e (VSort u)
| VStR_const : forall G e c ls,
    VWHRedS env U Pat G e (VConst c ls) ->
    VStRed env U Pat G e (VConst c ls)
| VStR_app : forall G e f f' a a',
    VWHRedS env U Pat G e (VApp f a) ->
    VStRed env U Pat G f f' ->
    VStRed env U Pat G a a' ->
    VStRed env U Pat G e (VApp f' a')
| VStR_lam : forall G e A A' body body',
    VWHRedS env U Pat G e (VLam A body) ->
    VStRed env U Pat G A A' ->
    VStRed env U Pat (A :: G) body body' ->
    VStRed env U Pat G e (VLam A' body')
| VStR_forallE : forall G e A A' B B',
    VWHRedS env U Pat G e (VForallE A B) ->
    VStRed env U Pat G A A' ->
    VStRed env U Pat (A :: G) B B' ->
    VStRed env U Pat G e (VForallE A' B').

Theorem VStRed_refl env U Pat G e :
  VStRed env U Pat G e e.
Proof.
  revert G.
  induction e as [i | u | c ls | f IHf a IHa | A IHA b IHb | A IHA B IHB]; intros G.
  - exact (VStR_bvar (@VRTC_rfl _ _ (VBVar i))).
  - exact (VStR_sort (@VRTC_rfl _ _ (VSort u))).
  - exact (VStR_const (@VRTC_rfl _ _ (VConst c ls))).
  - exact (VStR_app VRTC_rfl (IHf G) (IHa G)).
  - exact (VStR_lam VRTC_rfl (IHA G) (IHb (A :: G))).
  - exact (VStR_forallE VRTC_rfl (IHA G) (IHB (A :: G))).
Qed.

Theorem VStRed_bvar_l env U Pat G i e :
  VStRed env U Pat G (VBVar i) e ->
  e = VBVar i.
Proof.
  intros H.
  inversion H as [G0 e0 j h1 | G0 e0 u h1 | G0 e0 c ls h1
                 | G0 e0 f f' a a' h1 _ _ | G0 e0 A A' b b' h1 _ _
                 | G0 e0 A A' B B' h1 _ _]; subst;
    pose proof (VWHNF_whRedS (@VWHNF_bvar env U Pat G i) h1) as Heq;
    inversion Heq; reflexivity.
Qed.

Theorem VStRed_sort_l env U Pat G u e :
  VStRed env U Pat G (VSort u) e ->
  e = VSort u.
Proof.
  intros H.
  inversion H as [G0 e0 j h1 | G0 e0 v h1 | G0 e0 c ls h1
                 | G0 e0 f f' a a' h1 _ _ | G0 e0 A A' b b' h1 _ _
                 | G0 e0 A A' B B' h1 _ _]; subst;
    pose proof (VWHNF_whRedS (@VWHNF_sort env U Pat G u) h1) as Heq;
    inversion Heq; reflexivity.
Qed.

Theorem VStRed_lam_l env U Pat G A B e :
  VStRed env U Pat G (VLam A B) e ->
  exists A' B',
    e = VLam A' B' /\
    VStRed env U Pat G A A' /\
    VStRed env U Pat (A :: G) B B'.
Proof.
  intros H.
  inversion H as [G0 e0 j h1 | G0 e0 v h1 | G0 e0 c ls h1
                 | G0 e0 f f' a a' h1 _ _ | G0 e0 A0 A' b B' h1 h2 h3
                 | G0 e0 A0 A' B0 B' h1 _ _]; subst;
    pose proof (VWHNF_whRedS (@VWHNF_lam env U Pat G A B) h1) as Heq;
    try discriminate.
  inversion Heq; subst.
  exists A', B'; auto.
Qed.

Theorem VStRed_forallE_l env U Pat G A B e :
  VStRed env U Pat G (VForallE A B) e ->
  exists A' B',
    e = VForallE A' B' /\
    VStRed env U Pat G A A' /\
    VStRed env U Pat (A :: G) B B'.
Proof.
  intros H.
  inversion H as [G0 e0 j h1 | G0 e0 v h1 | G0 e0 c ls h1
                 | G0 e0 f f' a a' h1 _ _ | G0 e0 A0 A' b B' h1 _ _
                 | G0 e0 A0 A' B0 B' h1 h2 h3]; subst;
    pose proof (VWHNF_whRedS (@VWHNF_forallE env U Pat G A B) h1) as Heq;
    try discriminate.
  inversion Heq; subst.
  exists A', B'; auto.
Qed.

Theorem VStRed_defeqDFC env U Pat G0 G1 G2 e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VHasType env U G1 e1 A ->
  VStRed env U Pat G1 e1 e2 ->
  VStRed env U Pat G2 e1 e2.
Proof.
  intros Hpp HG0 W Hty H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert G2 A W Hty.
  induction H as
    [ G1 e i h1
    | G1 e u h1
    | G1 e c ls h1
    | G1 e f f' a a' h1 _ IH1 _ IH2
    | G1 e A0 A0' body body' h1 _ IH1 _ IH2
    | G1 e A0 A0' B0 B0' h1 _ IH1 _ IH2 ];
    intros G2 A W Hty.
  - exact (VStR_bvar (VWHRedS_defeqDFC Hwf W h1)).
  - exact (VStR_sort (VWHRedS_defeqDFC Hwf W h1)).
  - exact (VStR_const (VWHRedS_defeqDFC Hwf W h1)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_app_inv Hwf HG1 (VWHRedS_hasType Hpp HG1 h1 Hty))
      as [A_f [B_f [hf ha]]].
    exact (VStR_app (VWHRedS_defeqDFC Hwf W h1) (IH1 _ _ W hf) (IH2 _ _ W ha)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_lam_inv Hwf HG1 (VWHRedS_hasType Hpp HG1 h1 Hty))
      as [[u hA] [B_b he]].
    exact (VStR_lam (VWHRedS_defeqDFC Hwf W h1) (IH1 _ _ W hA)
                    (IH2 _ _ (VIsDefEqCtx_succ W hA) he)).
  - pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_forallE_inv Hwf (VWHRedS_hasType Hpp HG1 h1 Hty))
      as [[u hA] [v hB]].
    exact (VStR_forallE (VWHRedS_defeqDFC Hwf W h1) (IH1 _ _ W hA)
                        (IH2 _ _ (VIsDefEqCtx_succ W hA) hB)).
Qed.

Theorem VStRed_parRedS env U Pat G e e' :
  VStRed env U Pat G e e' ->
  VParRedTS env U Pat G e e'.
Proof.
  induction 1 as
    [ G e i h1
    | G e u h1
    | G e c ls h1
    | G e f f' a a' h1 _ IH1 _ IH2
    | G e A A' body body' h1 _ IH1 _ IH2
    | G e A A' B B' h1 _ IH1 _ IH2 ].
  - exact (VWHRedS_parRedS h1).
  - exact (VWHRedS_parRedS h1).
  - exact (VWHRedS_parRedS h1).
  - exact (VRTC_trans (VWHRedS_parRedS h1) (VParRedTS_app IH1 IH2)).
  - exact (VRTC_trans (VWHRedS_parRedS h1) (VParRedTS_lam IH1 IH2)).
  - exact (VRTC_trans (VWHRedS_parRedS h1) (VParRedTS_forallE IH1 IH2)).
Qed.

Theorem VStRed_whRed env U Pat G e1 e2 e' :
  VWHRedS env U Pat G e1 e2 ->
  VStRed env U Pat G e2 e' ->
  VStRed env U Pat G e1 e'.
Proof.
  intros H1 H2.
  inversion H2 as
    [ G0 e0 i h1
    | G0 e0 u h1
    | G0 e0 c ls h1
    | G0 e0 f f' a a' h1 h2 h3
    | G0 e0 A A' body body' h1 h2 h3
    | G0 e0 A A' B B' h1 h2 h3 ]; subst.
  - exact (VStR_bvar (VRTC_trans H1 h1)).
  - exact (VStR_sort (VRTC_trans H1 h1)).
  - exact (VStR_const (VRTC_trans H1 h1)).
  - exact (VStR_app (VRTC_trans H1 h1) h2 h3).
  - exact (VStR_lam (VRTC_trans H1 h1) h2 h3).
  - exact (VStR_forallE (VRTC_trans H1 h1) h2 h3).
Qed.

Theorem VStRed_defeq env U Pat G e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VStRed env U Pat G e1 e2 ->
  VHasType env U G e1 A ->
  VIsDefEq env U G e1 e2 A.
Proof.
  intros Hpp HG H He.
  exact (VParRedTS_defeq Hpp HG (VStRed_parRedS H) He).
Qed.

Theorem VStRed_weak' env U Pat rho G G' e1 e2 :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VStRed env U Pat G e1 e2 ->
  VStRed env U Pat G' (vlift' rho e1) (vlift' rho e2).
Proof.
  intros Hwf W H.
  revert rho G' W.
  induction H as
    [ G e i h1
    | G e u h1
    | G e c ls h1
    | G e f f' a a' h1 _ IH1 _ IH2
    | G e A A' body body' h1 _ IH1 _ IH2
    | G e A A' B B' h1 _ IH1 _ IH2 ];
    intros rho G' W; simpl.
  - exact (VStR_bvar (VWHRedS_weak' Hwf W h1)).
  - exact (VStR_sort (VWHRedS_weak' Hwf W h1)).
  - exact (VStR_const (VWHRedS_weak' Hwf W h1)).
  - exact (VStR_app (VWHRedS_weak' Hwf W h1) (IH1 _ _ W) (IH2 _ _ W)).
  - exact (VStR_lam (VWHRedS_weak' Hwf W h1) (IH1 _ _ W) (IH2 _ _ (VCtxLift'_cons A W))).
  - exact (VStR_forallE (VWHRedS_weak' Hwf W h1) (IH1 _ _ W) (IH2 _ _ (VCtxLift'_cons A W))).
Qed.

Theorem VStRed_weakN env U Pat n k G G' e1 e2 :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VStRed env U Pat G e1 e2 ->
  VStRed env U Pat G' (vliftN n k e1) (vliftN n k e2).
Proof.
  intros Hwf W H.
  rewrite <- !vlift'_consN_skipN.
  exact (VStRed_weak' Hwf (proj1 (VCtxLiftN_iff_VCtxLift' n k G G') W) H).
Qed.

Theorem VStRed_instN env U Pat G0 a1 a2 A0 k G1 G e1 e2 :
  VEnvWF env ->
  VStRed env U Pat G0 a1 a2 ->
  VHasType env U G0 a1 A0 ->
  VCtxInstN G0 a1 A0 k G1 G ->
  VStRed env U Pat G1 e1 e2 ->
  VStRed env U Pat G (vinst e1 a1 k) (vinst e2 a2 k).
Proof.
  intros Hwf H0 H0' W H.
  revert k G W.
  induction H as
    [ G1 e i h1
    | G1 e u h1
    | G1 e c ls h1
    | G1 e f f' a a' h1 _ IH1 _ IH2
    | G1 e A A' body body' h1 _ IH1 _ IH2
    | G1 e A A' B B' h1 _ IH1 _ IH2 ];
    intros k G W; simpl.
  - apply (VStRed_whRed (VWHRedS_instN Hwf H0' W h1)).
    clear e h1.
    revert i.
    induction W as [| k G1 G C W IHW]; intros i; simpl.
    + destruct i as [|i]; unfold vinstVar; simpl.
      * rewrite !vliftN_zero; exact H0.
      * exact (VStR_bvar (@VRTC_rfl _ _ (VBVar i))).
    + destruct i as [|i]; simpl.
      * unfold vinstVar; simpl; exact (VStR_bvar (@VRTC_rfl _ _ (VBVar 0))).
      * rewrite !vinstVar_succ.
        exact (VStRed_weakN Hwf (VCtxLiftN_one _ _) (IHW i)).
  - exact (VStR_sort (VWHRedS_instN Hwf H0' W h1)).
  - exact (VStR_const (VWHRedS_instN Hwf H0' W h1)).
  - exact (VStR_app (VWHRedS_instN Hwf H0' W h1) (IH1 _ _ W) (IH2 _ _ W)).
  - exact (VStR_lam (VWHRedS_instN Hwf H0' W h1) (IH1 _ _ W)
                    (IH2 _ _ (VCtxInstN_succ A W))).
  - exact (VStR_forallE (VWHRedS_instN Hwf H0' W h1) (IH1 _ _ W)
                        (IH2 _ _ (VCtxInstN_succ A W))).
Qed.

Theorem VStRed_apply_pat env U Pat G p (r : VPatternRHS p) m1 (m2 m3 : VMatchEnv p) :
  (forall a, VStRed env U Pat G (vpath_get m2 a) (vpath_get m3 a)) ->
  VStRed env U Pat G (@vrhs_apply p m1 m2 r) (@vrhs_apply p m1 m3 r).
Proof.
  intros H.
  induction r as [c Hcl | f IHf a IHa | path]; simpl.
  - apply VStRed_refl.
  - exact (VStR_app VRTC_rfl IHf IHa).
  - exact (H path).
Qed.

(* Kashima's Triangle Lemma for Standard Reduction *)

Theorem VStRed_triangle env U Pat G0 G1 G2 e e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VHasType env U G1 e A ->
  VStRed env U Pat G1 e e1 ->
  VParRedT env U Pat G2 e1 e2 ->
  VStRed env U Pat G1 e e2.
Proof.
  intros Hpp HG0 W Hty H1 H2.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert G1 e A W Hty H1.
  induction H2 as
    [ G2 i
    | G2 u
    | G2 c ls
    | G2 f1 f2 a1 a2 _ IH1 _ IH2
    | G2 A1 A2 body1 body2 _ IH1 _ IH2
    | G2 A1 A2 B1 B2 _ IH1 _ IH2
    | G2 dom bd1 bd2 arg1 arg2 _ IH1 _ IH2
    | G2 p r e1 m1 m2 m2' h1 h2 h3 _ IH ];
    intros G1 e A W Hty H1.
  - exact H1.
  - exact H1.
  - exact H1.
  - inversion H1 as [| | | G_x e_x f0 f1' a0 a1' a_1 a_2 a_3 | |]; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_app_inv Hwf HG1 (VWHRedS_hasType Hpp HG1 a_1 Hty))
      as [A_f [B_f [hf ha]]].
    exact (VStR_app a_1 (IH1 _ _ _ W hf a_2) (IH2 _ _ _ W ha a_3)).
  - inversion H1 as [| | | | G_x e_x A0 A1' bd0 bd1' a_1 a_2 a_3 |]; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_lam_inv Hwf HG1 (VWHRedS_hasType Hpp HG1 a_1 Hty))
      as [[u hA] [B_b he]].
    exact (VStR_lam a_1 (IH1 _ _ _ W hA a_2)
                    (IH2 _ _ _ (VIsDefEqCtx_succ W (VStRed_defeq Hpp HG1 a_2 hA))
                         he a_3)).
  - inversion H1 as [| | | | | G_x e_x A0 A1' B0 B1' a_1 a_2 a_3]; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_forallE_inv Hwf (VWHRedS_hasType Hpp HG1 a_1 Hty))
      as [[u hA] [v he]].
    exact (VStR_forallE a_1 (IH1 _ _ _ W hA a_2)
                        (IH2 _ _ _ (VIsDefEqCtx_succ W (VStRed_defeq Hpp HG1 a_2 hA))
                             he a_3)).
  - (* beta *)
    inversion H1 as [| | | G_x e_x f0 lam_t a0 arg1' a_1 a_2 a_3 | |]; subst.
    inversion a_2 as [| | | | G_y f_y A0 dom' bd0 bd1' a_4 a_5 a_6 |]; subst.
    pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    destruct (VHasType_app_inv Hwf HG1 (VWHRedS_hasType Hpp HG1 a_1 Hty))
      as [A_f [B_f [hf ha]]].
    pose proof (VWHRedS_hasType Hpp HG1 a_4 hf) as c1.
    destruct (VHasType_lam_inv Hwf HG1 c1) as [[u_a hA] [B_b he]].
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG1
                (VIsDefEq_uniqU Hwf Hinj HG1 c1 (VHasType_lam hA he)))
      as [[w1 u1] _].
    apply (VStRed_whRed
             (VRTC_tail (VRTC_trans a_1 (VWHRedS_app a0 a_4))
                        (VWHR_beta G1 A0 bd0 a0))).
    exact (VStRed_instN Hwf
             (IH2 _ _ _ W ha a_3)
             (VDF_defeqDF u1 ha)
             (VCtxInstN_zero G1 a0 A0)
             (IH1 _ _ _ (VIsDefEqCtx_succ W (VStRed_defeq Hpp HG1 a_5 hA)) he a_6)).
  - (* extra *)
    pose proof (VIsDefEqCtx_wf Hcl HG0 W) as HG1.
    assert (Hsuff : forall p' e1_p m1_p (m2_p : VMatchEnv p'),
      VSubpattern p' p ->
      VPatternMatches p' e1_p m1_p m2_p ->
      forall e_p, VStRed env U Pat G1 e_p e1_p ->
      exists e0_p (m3_p : VMatchEnv p'),
        VWHRedS env U Pat G1 e_p e0_p /\
        VPatternMatches p' e0_p m1_p m3_p /\
        (forall x : VPatternPath p',
           VStRed env U Pat G1 (vpath_get m3_p x) (vpath_get m2_p x))).
    { clear h2 h3 IH Hty H1 e1 m1 m2 m2' e A.
      induction p' as [c | pf IHf pa IHa | pf IHf];
        intros e1_p m1_p m2_p hp h2_p e_p Hst.
      - destruct e1_p; simpl in h2_p; try contradiction.
        destruct h2_p as [<- [<- ->]].
        inversion Hst as [| | G_x e_x c_x ls_x r1 | | |]; subst.
        exists (VConst c m1_p), tt; split; [exact r1 |].
        split; [exact (VPM_const c m1_p) | intros []].
      - destruct e1_p as [| | | f1 a1 | |]; simpl in h2_p; try contradiction.
        destruct m2_p as [mf2 ma2]; simpl in h2_p.
        destruct h2_p as [hmf [ls2 hma]].
        inversion Hst as [| | | G_x e_x f0 f1' a0 a1' r1 r2 r3 | |]; subst.
        destruct (IHf f1 m1_p mf2
                    (VSubpattern_trans (@VSub_appL pf pf pa (VSub_refl pf)) hp)
                    hmf f0 r2)
          as [f0' [mf3 [a_1 [a_2 a_3]]]].
        destruct (IHa a1 ls2 ma2
                    (VSubpattern_trans (@VSub_appR pa pf pa (VSub_refl pa)) hp)
                    hma a0 r3)
          as [a0' [ma3 [b_1 [b_2 b_3]]]].
        assert (Hmaj : VIsMajorPremise Pat f0').
        { exists p; split; [exists r; exact h1 |].
          exists pf, pa; split; [exact hp | exists m1_p, mf3; exact a_2]. }
        exists (VApp f0' a0'), (mf3, ma3); split.
        + exact (VRTC_trans r1 (VRTC_trans (VWHRedS_app a0 a_1)
                                           (VWHRedS_major Hmaj b_1))).
        + split; [exact (VPM_app a_2 b_2) |].
          intros [xf | xa]; simpl; [exact (a_3 xf) | exact (b_3 xa)].
      - destruct e1_p as [| | | f1 a1 | |]; simpl in h2_p; try contradiction.
        destruct m2_p as [ea2 mf2]; simpl in h2_p.
        destruct h2_p as [-> hmf].
        inversion Hst as [| | | G_x e_x f0 f1' a0 a1' r1 r2 r3 | |]; subst.
        destruct (IHf f1 m1_p mf2
                    (VSubpattern_trans (@VSub_varL pf pf (VSub_refl pf)) hp)
                    hmf f0 r2)
          as [f0' [mf3 [a_1 [a_2 a_3]]]].
        exists (VApp f0' a0), (a0, mf3); split.
        + exact (VRTC_trans r1 (VWHRedS_app a0 a_1)).
        + split; [simpl; split; [reflexivity | exact a_2] |].
          intros [xf |]; simpl; [exact (a_3 xf) | exact r3]. }
    destruct (Hsuff p e1 m1 m2 (VSub_refl p) h2 e H1)
      as [e0 [m3 [a_1 [a_2 a_3]]]].
    pose proof (VWHRedS_hasType Hpp HG1 a_1 Hty) as He0_ty.
    assert (Hpath_ty : forall x, exists T, VHasType env U G1 (vpath_get m3 x) T).
    { intros x. exact (VPatternMatches_hasType x Hwf HG1 a_2 He0_ty). }
    assert (Hck_m3 : VPatternCheckOK (VIsDefEqU env U G1) m1 m3 (snd r)).
    { eapply VPatternCheckOK_map; [| exact h3].
      intros ra rb [T HT].
      pose proof (VIsDefEq_defeqDFC Hcl (VIsDefEqCtx_symm Hcl W) HT) as HT_G1.
      assert (Hih_eq : forall x B,
        VHasType env U G1 (vpath_get m2 x) B ->
        VIsDefEqU env U G1 (vpath_get m2 x) (vpath_get m3 x)).
      { intros x B _.
        destruct (Hpath_ty x) as [Tx HTx].
        exists Tx. exact (VDF_symm (VStRed_defeq Hpp HG1 (a_3 x) HTx)). }
      pose proof (VIsDefEq_apply_pat Hwf Hinj HG1 Hih_eq (VIsDefEq_refl_l HT_G1)) as Hra.
      pose proof (VIsDefEq_apply_pat Hwf Hinj HG1 Hih_eq (VIsDefEq_refl_r HT_G1)) as Hrb.
      exists T.
      exact (VDF_trans (VDF_symm Hra) (VDF_trans HT_G1 Hrb)). }
    apply (VStRed_whRed (VRTC_tail a_1 (VWHR_extra h1 a_2 Hck_m3))).
    apply VStRed_apply_pat.
    intros x.
    destruct (Hpath_ty x) as [Tx HTx].
    exact (IH x _ _ _ W HTx (a_3 x)).
Qed.

Theorem VStRed_triangleS env U Pat G0 G1 G2 e e1 e2 A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VIsDefEqCtx env U G0 G1 G2 ->
  VHasType env U G1 e A ->
  VStRed env U Pat G1 e e1 ->
  VParRedTS env U Pat G2 e1 e2 ->
  VStRed env U Pat G1 e e2.
Proof.
  intros Hpp HG0 W Hty H1 H2.
  induction H2 as [| y z _ IH h2].
  - exact H1.
  - exact (VStRed_triangle Hpp HG0 W Hty IH h2).
Qed.

Theorem VParRedTS_standard env U Pat G e e' A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G e A ->
  VParRedTS env U Pat G e e' ->
  VStRed env U Pat G e e'.
Proof.
  intros Hpp HG Hty H.
  exact (VStRed_triangleS Hpp HG (VIsDefEqCtx_zero env U G) Hty
           (VStRed_refl env U Pat G e) H).
Qed.

(* Head Reduction to Sorts and Pi Types *)

Theorem VIsDefEq_reduce_sort env U Pat G e u A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VIsDefEq env U G e (VSort u) A ->
  exists u', VWHRedS env U Pat G e (VSort u') /\ vlevel_equiv u' u.
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  destruct (VIsDefEq_church_rosser Hpp HG H)
    as [_ [_ [e' [s' [h1 [h2 h3]]]]]].
  pose proof (VStRed_sort_l (VParRedTS_standard Hpp HG (VIsDefEq_refl_r H) h2))
    as Hs'; subst s'.
  pose proof (VIsDefEq_sort_inv_r H) as hu.
  assert (Hex : exists v, e' = VSort v /\ vlevel_equiv v u).
  { inversion h3 as
      [ G0 x T _
      | G0 l1 l2 _ _ h_eq
      | | | |
      | G0 s0 A0 B0 bd h_eta _
      |
      | G0 p x1 x2 hp1 _ hp3 ]; subst.
    - exists u; split; [reflexivity | apply vlevel_equiv_refl].
    - exists l1; split; [reflexivity | exact h_eq].
    - exfalso.
      exact (VIsDefEqU_sort_forallE_inv Hinj HG
               (VIsDefEq_uniqU Hwf Hinj HG (VHasType_sort env U G u hu) h_eta)).
    - exfalso.
      pose proof (VHasType_defeqU_l Hwf Hinj HG
                    (VIsDefEqU_symm (VIsDefEq_uniqU Hwf Hinj HG
                       (VHasType_sort env U G u hu) hp3))
                    hp1)
        as Hsort_zero.
      pose proof (VIsDefEqU_sort_inv Hinj HG
                    (VIsDefEq_uniqU Hwf Hinj HG
                       (VHasType_sort env U G (VLSucc u) hu) Hsort_zero))
        as Hlev.
      specialize (Hlev []); simpl in Hlev; discriminate. }
  destruct Hex as [v [-> a1]].
  pose proof (VParRedTS_standard Hpp HG (VIsDefEq_refl_l H) h1) as Hst1.
  inversion Hst1 as [| G0 e0 v0 r1 | | | |]; subst.
  exists v; split; [exact r1 | exact a1].
Qed.

Theorem VIsDefEq_reduce_forallE env U Pat G e A B V :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VIsDefEq env U G e (VForallE A B) V ->
  exists A' B', VWHRedS env U Pat G e (VForallE A' B').
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  destruct (VIsDefEq_church_rosser Hpp HG H)
    as [_ [_ [e' [pi' [h1 [h2 h3]]]]]].
  destruct (VStRed_forallE_l (VParRedTS_standard Hpp HG (VIsDefEq_refl_r H) h2))
    as [A1 [B1 [-> [eA eB]]]].
  destruct (VHasType_forallE_inv Hwf (VIsDefEq_refl_r H)) as [[u hA] [v hB]].
  pose proof (VParRedTS_defeq Hpp HG (VStRed_parRedS eA) hA) as hA1.
  pose proof (VIsDefEq_defeqDF_l' (D := []) Hcl hA1
                (VParRedTS_hasType Hpp (vctx_cons HG hA) (VStRed_parRedS eB) hB))
    as hB1.
  assert (Hex : exists A' B', e' = VForallE A' B').
  { inversion h3 as
      [ G0 x T _
      | | | |
      | G0 dom A' A1' B' B1' u0 v0 _ _ _ _
      | G0 s0 A0 B0 bd h_eta _
      |
      | G0 p x1 x2 hp1 _ hp3 ]; subst.
    - exists A1, B1; reflexivity.
    - exists A', B'; reflexivity.
    - exfalso.
      pose proof (VHasType_forallE (VIsDefEq_refl_r hA1) hB1) as hpi1.
      exact (VIsDefEqU_sort_forallE_inv Hinj HG
               (VIsDefEq_uniqU Hwf Hinj HG hpi1 h_eta)).
    - exfalso.
      pose proof (VHasType_forallE (VIsDefEq_refl_r hA1) hB1) as hpi1.
      pose proof (VHasType_defeqU_l Hwf Hinj HG
                    (VIsDefEqU_symm (VIsDefEq_uniqU Hwf Hinj HG hpi1 hp3))
                    hp1)
        as Hsort_zero.
      pose proof (VIsDefEq_sort_inv_l Hsort_zero) as hw_imax.
      pose proof (VIsDefEqU_sort_inv Hinj HG
                    (VIsDefEq_uniqU Hwf Hinj HG
                       (VHasType_sort env U G _ hw_imax) Hsort_zero))
        as Hlev.
      specialize (Hlev []); simpl in Hlev; discriminate. }
  destruct Hex as [A' [B' ->]].
  pose proof (VParRedTS_standard Hpp HG (VIsDefEq_refl_l H) h1) as Hst1.
  inversion Hst1 as [| | | | | G0 e0 A0 A0' B0 B0' r1 _ _]; subst.
  exists A0, B0; exact r1.
Qed.

(* Syntax-Directed Type Inference (InferType and InferTypeS) *)

Inductive VInferType (env : VEnv) (U : nat) (Pat : VPatRel) :
    list VExpr -> VExpr -> VExpr -> Prop :=
| VIT_bvar : forall G i A,
    VLookup G i A ->
    VInferType env U Pat G (VBVar i) A
| VIT_sort : forall G u,
    vlevel_wf U u ->
    VInferType env U Pat G (VSort u) (VSort (VLSucc u))
| VIT_const : forall G c ci ls,
    venv_constants env c = Some ci ->
    Forall (vlevel_wf U) ls ->
    List.length ls = vc_uvars ci ->
    VInferType env U Pat G (VConst c ls) (vinstL ls (vc_type ci))
| VIT_app : forall G f F A B a,
    VInferType env U Pat G f F ->
    VWHRedS env U Pat G F (VForallE A B) ->
    VHasType env U G a A ->
    VInferType env U Pat G (VApp f a) (vinst0 B a)
| VIT_lam : forall G A u body B,
    VHasType env U G A (VSort u) ->
    VInferType env U Pat (A :: G) body B ->
    VInferType env U Pat G (VLam A body) (VForallE A B)
| VIT_forallE : forall G A U_ty u B V_ty v,
    VInferType env U Pat G A U_ty ->
    VWHRedS env U Pat G U_ty (VSort u) ->
    VInferType env U Pat (A :: G) B V_ty ->
    VWHRedS env U Pat (A :: G) V_ty (VSort v) ->
    VInferType env U Pat G (VForallE A B) (VSort (VLIMax u v)).

Arguments VIT_bvar {env U Pat G i A} _.
Arguments VIT_sort {env U Pat} G {u} _.
Arguments VIT_const {env U Pat} G {c ci ls} _ _ _.

Theorem VInferType_hasType env U Pat G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VInferType env U Pat G e A ->
  VHasType env U G e A.
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  revert HG.
  induction H as
    [ G i A h1
    | G u h1
    | G c ci ls h1 h2 h3
    | G f F A B a _ IHf h2 h3
    | G A u body B h1 _ IHb
    | G A U_ty u B V_ty v _ IHA h2 _ IHB h4 ];
    intros HG.
  - exact (VDF_bvar h1).
  - exact (VHasType_sort env U G u h1).
  - exact (VHasType_const G h1 h2 h3).
  - pose proof (IHf HG) as hf.
    destruct (VIsDefEq_isType Hwf HG hf) as [w hF].
    exact (VHasType_app (VDF_defeqDF (VWHRedS_defeq Hpp HG h2 hF) hf) h3).
  - exact (VHasType_lam h1 (IHb (vctx_cons HG h1))).
  - pose proof (IHA HG) as hA0.
    destruct (VIsDefEq_isType Hwf HG hA0) as [wU hU].
    pose proof (VDF_defeqDF (VWHRedS_defeq Hpp HG h2 hU) hA0) as hA.
    pose proof (vctx_cons HG hA) as HG'.
    pose proof (IHB HG') as hB0.
    destruct (VIsDefEq_isType Hwf HG' hB0) as [wV hV].
    pose proof (VDF_defeqDF (VWHRedS_defeq Hpp HG' h4 hV) hB0) as hB.
    exact (VHasType_forallE hA hB).
Qed.

Theorem VInferType_determ env U Pat G e A A' :
  PatternParamsFor env Pat ->
  VInferType env U Pat G e A ->
  VInferType env U Pat G e A' ->
  A = A'.
Proof.
  intros Hpp H1.
  revert A'.
  induction H1 as
    [ G i A l1
    | G u l1
    | G c ci ls l1 _ _
    | G f F A B a _ IHf l2 _
    | G A u body B _ _ IHb
    | G A U_ty u B V_ty v _ IHA l2 _ IHB l4 ];
    intros A' H2.
  - inversion H2 as [G0 j B0 r1 | | | | |]; subst.
    exact (VLookup_deterministic l1 r1).
  - inversion H2; reflexivity.
  - inversion H2 as [| | G0 c0 ci' ls0 r1 _ _ | | |]; subst.
    rewrite l1 in r1; inversion r1; reflexivity.
  - inversion H2 as [| | | G0 f0 F' A2 B2 a0 r1 r2 _ | |]; subst.
    pose proof (IHf _ r1) as HeqF; subst F'.
    pose proof (VWHRedS_determ Hpp l2 (@VWHNF_forallE env U Pat G A B)
                               r2 (@VWHNF_forallE env U Pat G A2 B2)) as HeqPi.
    inversion HeqPi; reflexivity.
  - inversion H2 as [| | | | G0 A0 u0 bd0 B' _ r2 |]; subst.
    f_equal; exact (IHb _ r2).
  - inversion H2 as [| | | | | G0 A0 U_ty' u' B0 V_ty' v' r1 r2 r3 r4]; subst.
    pose proof (IHA _ r1) as HeqU; subst U_ty'.
    pose proof (VWHRedS_determ Hpp l2 (@VWHNF_sort env U Pat G u)
                               r2 (@VWHNF_sort env U Pat G u')) as Hequ.
    inversion Hequ; subst u'.
    pose proof (IHB _ r3) as HeqV; subst V_ty'.
    pose proof (VWHRedS_determ Hpp l4 (@VWHNF_sort env U Pat (A :: G) v)
                               r4 (@VWHNF_sort env U Pat (A :: G) v')) as Heqv.
    inversion Heqv; subst v'.
    reflexivity.
Qed.

Theorem VInferType_weak' env U Pat rho G G' e A :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VInferType env U Pat G e A ->
  VInferType env U Pat G' (vlift' rho e) (vlift' rho A).
Proof.
  intros Hwf W H.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  revert rho G' W.
  induction H as
    [ G i A h1
    | G u h1
    | G c ci ls h1 h2 h3
    | G f F A B a _ IHf h2 h3
    | G A u body B h1 _ IHb
    | G A U_ty u B V_ty v _ IHA h2 _ IHB h4 ];
    intros rho G' W; simpl.
  - exact (VIT_bvar (VLookup_weak' W h1)).
  - exact (VIT_sort G' h1).
  - rewrite (@vclosedN_vlift'_eq 0 rho _ (closed_inst_const ls 0 Hcl h1) (vlift_fixes_zero rho)).
    exact (VIT_const G' h1 h2 h3).
  - rewrite vlift'_vinst_hi.
    exact (VIT_app (IHf _ _ W) (VWHRedS_weak' Hwf W h2) (VIsDefEq_weak' Hcl W h3)).
  - exact (VIT_lam (VIsDefEq_weak' Hcl W h1) (IHb _ _ (VCtxLift'_cons A W))).
  - exact (VIT_forallE (IHA _ _ W) (VWHRedS_weak' Hwf W h2)
                       (IHB _ _ (VCtxLift'_cons A W))
                       (VWHRedS_weak' Hwf (VCtxLift'_cons A W) h4)).
Qed.

Theorem VInferType_weakN env U Pat n k G G' e A :
  VEnvWF env ->
  VCtxLiftN n k G G' ->
  VInferType env U Pat G e A ->
  VInferType env U Pat G' (vliftN n k e) (vliftN n k A).
Proof.
  intros Hwf W H.
  rewrite <- !vlift'_consN_skipN.
  exact (VInferType_weak' Hwf (proj1 (VCtxLiftN_iff_VCtxLift' n k G G') W) H).
Qed.

Theorem VInferType_weakU_inv env U Pat rho G G' e A' :
  PatternParamsFor env Pat ->
  VCtxWF env U G' ->
  VCtxLift' rho G G' ->
  VInferType env U Pat G' (vlift' rho e) A' ->
  exists A, A' = vlift' rho A /\ VInferType env U Pat G e A.
Proof.
  intros Hpp HG' W H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  remember (vlift' rho e) as e' eqn:Heq.
  revert rho G e HG' W Heq.
  induction H as
    [ G' i A' h1
    | G' u h1
    | G' c ci ls h1 h2 h3
    | G' f' F' A' B' a' _ IHf h2 h3
    | G' A' u body' B' h1 _ IHb
    | G' A' U_ty' u B' V_ty' v _ IHA h2 _ IHB h4 ];
    intros rho G e HG' W Heq.
  - destruct e; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (VLookup_weakU_inv W h1) as [A0 [-> h2]].
    exists A0; split; [reflexivity | exact (VIT_bvar h2)].
  - destruct e as [| u0 | | | |]; simpl in Heq; try discriminate.
    inversion Heq; subst u0.
    exists (VSort (VLSucc u)); split; [reflexivity | exact (VIT_sort G h1)].
  - destruct e as [| | c0 ls0 | | |]; simpl in Heq; try discriminate.
    inversion Heq; subst c0 ls0.
    exists (vinstL ls (vc_type ci)); split.
    + symmetry.
      exact (@vclosedN_vlift'_eq 0 rho _ (closed_inst_const ls 0 Hcl h1) (vlift_fixes_zero rho)).
    + exact (VIT_const G h1 h2 h3).
  - destruct e; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHf _ _ _ HG' W eq_refl) as [F [-> a1]].
    destruct (VWHRedS_weakU_inv Hwf Hinj HG' W h2) as [Pi0 [HeqPi a3]].
    destruct Pi0 as [| | | | | A0 B0]; simpl in HeqPi; try discriminate.
    inversion HeqPi; subst A' B'.
    exists (vinst0 B0 e2); split.
    + symmetry. apply vlift'_vinst_hi.
    + exact (VIT_app a1 a3
               (proj1 (@VHasType_weak'_iff env U rho G G' e2 A0 Hwf Hinj HG' W) h3)).
  - destruct e; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHb _ _ _ (vctx_cons HG' h1) (VCtxLift'_cons e1 W) eq_refl)
      as [B0 [-> a2]].
    exists (VForallE e1 B0); split; [reflexivity |].
    exact (VIT_lam
             (proj1 (@VHasType_weak'_iff env U rho G G' e1 (VSort u) Hwf Hinj HG' W) h1)
             a2).
  - destruct e; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHA _ _ _ HG' W eq_refl) as [U0 [-> a1]].
    destruct (VWHRedS_weakU_inv Hwf Hinj HG' W h2) as [S0 [HeqS a3]].
    destruct S0 as [| u0 | | | |]; simpl in HeqS; try discriminate.
    inversion HeqS; subst u0.
    pose proof (VCtxWF_weak'_inv Hwf Hinj W HG') as HG.
    pose proof (VInferType_hasType Hpp HG a1) as hA_U0.
    destruct (VIsDefEq_isType Hwf HG hA_U0) as [wU hU0].
    pose proof (VDF_defeqDF (VWHRedS_defeq Hpp HG a3 hU0) hA_U0) as hA.
    pose proof (vctx_cons HG' (VIsDefEq_weak' Hcl W hA)) as HG'_ext.
    destruct (IHB _ _ _ HG'_ext (VCtxLift'_cons e1 W) eq_refl) as [V0 [-> b1]].
    destruct (VWHRedS_weakU_inv Hwf Hinj HG'_ext (VCtxLift'_cons e1 W) h4)
      as [S1 [HeqS1 b3]].
    destruct S1 as [| v0 | | | |]; simpl in HeqS1; try discriminate.
    inversion HeqS1; subst v0.
    exists (VSort (VLIMax u v)); split; [reflexivity | exact (VIT_forallE a1 a3 b1 b3)].
Qed.

Theorem VInferType_weak'_inv env U Pat rho G G' e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G' ->
  VCtxLift' rho G G' ->
  VInferType env U Pat G' (vlift' rho e) (vlift' rho A) ->
  VInferType env U Pat G e A.
Proof.
  intros Hpp HG' W H.
  destruct (VInferType_weakU_inv Hpp HG' W H) as [A0 [Heq h2]].
  apply vlift'_inj in Heq; subst A0.
  exact h2.
Qed.

Theorem VInferType_instN env U Pat G0 e0 A0 k G1 G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G0 ->
  VCtxWF env U G1 ->
  VInferType env U Pat G0 e0 A0 ->
  VCtxInstN G0 e0 A0 k G1 G ->
  VInferType env U Pat G1 e A ->
  VInferType env U Pat G (vinst e e0 k) (vinst A e0 k).
Proof.
  intros Hpp HG0 HG1 He0 W H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (VEnvWF_closed Hwf) as Hcl.
  pose proof (VInferType_hasType Hpp HG0 He0) as He0_ty.
  revert k G HG1 W.
  induction H as
    [ G1 i ty h
    | G1 u h1
    | G1 c ci ls h1 h2 h3
    | G1 f F A B a _ IHf h2 h3
    | G1 A u body B h1 _ IHb
    | G1 A U_ty u B V_ty v h1 IHA h2 _ IHB h4 ];
    intros k G HG1 W; simpl.
  - revert i ty h HG1.
    induction W as [| k G1 G C W IHW]; intros i ty h HG1.
    + inversion h as [A' G' Heq1 Heq2 | A' G' j B' Hj Heq1 Heq2]; subst.
      * change (vinstVar 0 e0 0) with (vliftN 0 0 e0).
        rewrite vliftN_zero.
        change (vinst (vlift A0) e0 0) with (vinst0 (vlift A0) e0).
        rewrite vinst0_vlift.
        exact He0.
      * change (vinstVar (S j) e0 0) with (VBVar j).
        change (vinst (vlift B') e0 0) with (vinst0 (vlift B') e0).
        rewrite vinst0_vlift.
        exact (VIT_bvar Hj).
    + inversion h as [A' G' Heq1 Heq2 | A' G' j B' Hj Heq1 Heq2]; subst.
      * change (vinstVar 0 e0 (S k)) with (VBVar 0).
        rewrite vinst_vlift_succ.
        exact (VIT_bvar (VLookupZero _ _)).
      * rewrite vinstVar_succ, vinst_vlift_succ.
        pose proof (IHW j B' Hj (proj1 HG1)) as Hsub.
        exact (VInferType_weakN Hwf (VCtxLiftN_one _ _) Hsub).
  - exact (VIT_sort G h1).
  - rewrite (vclosedN_vinst_eq e0 (closed_inst_const ls k Hcl h1)).
    exact (VIT_const G h1 h2 h3).
  - rewrite vinst0_vinst_hi.
    exact (VIT_app (IHf _ _ HG1 W)
                   (VWHRedS_instN Hwf He0_ty W h2)
                   (VHasType_instN Hcl W h3 He0_ty)).
  - exact (VIT_lam (VHasType_instN Hcl W h1 He0_ty)
                   (IHb _ _ (vctx_cons HG1 h1) (VCtxInstN_succ A W))).
  - pose proof (VInferType_hasType Hpp HG1 h1) as hA_U.
    destruct (VIsDefEq_isType Hwf HG1 hA_U) as [wU hU].
    pose proof (VDF_defeqDF (VWHRedS_defeq Hpp HG1 h2 hU) hA_U) as hA.
    exact (VIT_forallE (IHA _ _ HG1 W)
                       (VWHRedS_instN Hwf He0_ty W h2)
                       (IHB _ _ (vctx_cons HG1 hA) (VCtxInstN_succ A W))
                       (VWHRedS_instN Hwf He0_ty (VCtxInstN_succ A W) h4)).
Qed.

Theorem VInferType_inst env U Pat G a A0 e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VInferType env U Pat G a A0 ->
  VInferType env U Pat (A0 :: G) e A ->
  VInferType env U Pat G (vinst0 e a) (vinst0 A a).
Proof.
  intros Hpp HG H0 H.
  destruct (VIsDefEq_isType (pp_wf Hpp) HG (VInferType_hasType Hpp HG H0)) as [u hA].
  exact (VInferType_instN Hpp HG (vctx_cons HG hA) H0 (VCtxInstN_zero G a A0) H).
Qed.

Theorem VInferType_exists env U Pat G a A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VHasType env U G a A ->
  exists A', VInferType env U Pat G a A'.
Proof.
  intros Hpp HG H.
  pose proof (pp_wf Hpp) as Hwf.
  pose proof (pp_inj Hpp) as Hinj.
  pose proof (proj1 (VIsDefEqStrong_hasType' (VIsDefEq_strong Hwf HG H))) as Hst.
  clear H.
  revert HG.
  induction Hst as
    [ G i A u h1 _ _ _
    | G l l' h1 _ _
    | G c ci ls u h1 h2 h3 _ _ _ _ _
    | G A B f a u v _ _ _ _ _ _ _ _ hf IHf ha _ _ _
    | G A B body u v _ _ hA _ _ _ _ IHb _ _
    | G A body u v _ _ hA IHA hB IHB
    | G e A _ IH
    | G e A B u _ _ _ _ _ _ _ IH ];
    intros HG.
  - exists A; exact (VIT_bvar h1).
  - exists (VSort (VLSucc l)); exact (VIT_sort G h1).
  - exists (vinstL ls (vc_type ci)); exact (VIT_const G h1 h2 h3).
  - destruct (IHf HG) as [F hF].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG
                (VInferType_hasType Hpp HG hF)
                (VHasTypeStrong_hasType hf))
      as [w h].
    destruct (VIsDefEq_reduce_forallE Hpp HG h) as [A' [B' rF]].
    destruct (VIsDefEqU_forallE_inv Hwf Hinj HG
                (ex_intro _ _
                   (VDF_trans (VDF_symm (VWHRedS_defeq Hpp HG rF (VIsDefEq_refl_l h)))
                              h)))
      as [[w1 hA_eq] _].
    exists (vinst0 B' a).
    exact (VIT_app hF rF (VDF_defeqDF (VDF_symm hA_eq) (VHasTypeStrong_hasType ha))).
  - pose proof (VHasTypeStrong_hasType hA) as hA_ty.
    destruct (IHb (vctx_cons HG hA_ty)) as [B' hB'].
    exists (VForallE A B').
    exact (VIT_lam hA_ty hB').
  - destruct (IHA HG) as [U_ty hU].
    pose proof (VHasTypeStrong_hasType hA) as hA_ty.
    destruct (VIsDefEq_uniq_same Hwf Hinj HG (VInferType_hasType Hpp HG hU) hA_ty)
      as [wU hU_eq].
    destruct (VIsDefEq_reduce_sort Hpp HG hU_eq) as [u' [rU _]].
    pose proof (vctx_cons HG hA_ty) as HG'.
    destruct (IHB HG') as [V_ty hV].
    destruct (VIsDefEq_uniq_same Hwf Hinj HG'
                (VInferType_hasType Hpp HG' hV)
                (VHasTypeStrong_hasType hB))
      as [wV hV_eq].
    destruct (VIsDefEq_reduce_sort Hpp HG' hV_eq) as [v' [rV _]].
    exists (VSort (VLIMax u' v')).
    exact (VIT_forallE hU rU hV rV).
  - exact (IH HG).
  - exact (IH HG).
Qed.

(* InferTypeS: Type inference followed by weak head reduction *)

Definition VInferTypeS (env : VEnv) (U : nat) (Pat : VPatRel)
    (G : list VExpr) (e A : VExpr) : Prop :=
  exists A', VInferType env U Pat G e A' /\ VWHRedS env U Pat G A' A.

Theorem VInferTypeS_hasType env U Pat G e A :
  PatternParamsFor env Pat ->
  VCtxWF env U G ->
  VInferTypeS env U Pat G e A ->
  VHasType env U G e A.
Proof.
  intros Hpp HG [A' [h1 h2]].
  pose proof (VInferType_hasType Hpp HG h1) as he.
  destruct (VIsDefEq_isType (pp_wf Hpp) HG he) as [u h3].
  exact (VDF_defeqDF (VWHRedS_defeq Hpp HG h2 h3) he).
Qed.

Theorem VWHRedS_inferType env U Pat G e e1 e2 :
  PatternParamsFor env Pat ->
  VWHRedS env U Pat G e e1 ->
  VWHNF env U Pat G e1 ->
  VWHRedS env U Pat G e e2 ->
  VWHNF env U Pat G e2 ->
  e1 = e2.
Proof.
  exact (@VWHRedS_determ env U Pat G e e1 e2).
Qed.

Theorem VInferTypeS_determ env U Pat G e A A' :
  PatternParamsFor env Pat ->
  VInferTypeS env U Pat G e A ->
  VWHNF env U Pat G A ->
  VInferTypeS env U Pat G e A' ->
  VWHNF env U Pat G A' ->
  A = A'.
Proof.
  intros Hpp [T1 [h1 h2]] W1 [T2 [h3 h4]] W2.
  pose proof (VInferType_determ Hpp h1 h3) as Heq; subst T2.
  exact (VWHRedS_determ Hpp h2 W1 h4 W2).
Qed.

Theorem VInferTypeS_weak' env U Pat rho G G' e A :
  VEnvWF env ->
  VCtxLift' rho G G' ->
  VInferTypeS env U Pat G e A ->
  VInferTypeS env U Pat G' (vlift' rho e) (vlift' rho A).
Proof.
  intros Hwf W [A' [h1 h2]].
  exists (vlift' rho A'); split;
    [exact (VInferType_weak' Hwf W h1) | exact (VWHRedS_weak' Hwf W h2)].
Qed.

Theorem VInferTypeS_weakU_inv env U Pat rho G G' e A' :
  PatternParamsFor env Pat ->
  VCtxWF env U G' ->
  VCtxLift' rho G G' ->
  VInferTypeS env U Pat G' (vlift' rho e) A' ->
  exists A, A' = vlift' rho A /\ VInferTypeS env U Pat G e A.
Proof.
  intros Hpp HG' W [T' [h1 h2]].
  destruct (VInferType_weakU_inv Hpp HG' W h1) as [T [-> a1]].
  destruct (VWHRedS_weakU_inv (pp_wf Hpp) (pp_inj Hpp) HG' W h2) as [A [-> a2]].
  exists A; split; [reflexivity | exists T; split; [exact a1 | exact a2]].
Qed.

(* ========================================================================= *)
(* 5. Unconditional Non-Vacuity on Empty / Extra-Free Environments           *)
(*    & Complete Axiom-Freedom Audit                                         *)
(* ========================================================================= *)

Definition vpat_empty : VPatRel := fun _ _ => False.

(* 5a. Instantiation of PatternParamsFor / PatternParams on extra-free envs
       and venv_empty *)

Theorem PatternParamsFor_of_no_defeqs env :
  VEnvWF env ->
  (forall df, ~ venv_defeqs env df) ->
  DefEqInjectivity env ->
  PatternParamsFor env vpat_empty.
Proof.
  intros Hwf Hnodef Hinj.
  constructor.
  - exact Hwf.
  - exact Hinj.
  - intros p r H; contradiction.
  - intros p1 p2 p3 p4 r r' H; contradiction.
  - intros p r r' H; contradiction.
  - intros U G p r e m1 m2 A H; contradiction.
  - intros p r p1 p2 p3 p4 H; contradiction.
  - intros p p' r r' p1 p2 p1' p2' p3 H; contradiction.
  - intros p p' r r' p1 p2 p1' p2' p3 p3' H; contradiction.
  - intros U G df ls Hdf; exfalso; exact (Hnodef df Hdf).
  - intros U G e A _ _.
    right; intros [p [r [_ [_ [H _]]]]]; exact H.
  - intros U G f1 f2 a1 a2 A B p r m1 m2 m2' _ _ _ _ _ _ _ H; contradiction.
Qed.

Theorem PatternParams_of_no_defeqs env :
  VEnvWF env ->
  (forall df, ~ venv_defeqs env df) ->
  DefEqInjectivity env ->
  PatternParams env.
Proof.
  intros Hwf Hnodef Hinj.
  exists vpat_empty.
  exact (PatternParamsFor_of_no_defeqs Hwf Hnodef Hinj).
Qed.

Theorem PatternParamsFor_empty :
  DefEqInjectivity venv_empty ->
  PatternParamsFor venv_empty vpat_empty.
Proof.
  intros Hinj.
  exact (PatternParamsFor_of_no_defeqs VEnvWF_empty (fun _ H => H) Hinj).
Qed.

Theorem PatternParams_empty :
  DefEqInjectivity venv_empty ->
  PatternParams venv_empty.
Proof.
  intros Hinj.
  exists vpat_empty.
  exact (PatternParamsFor_empty Hinj).
Qed.

(* 5b. Unconditional Equivalence with Pure-Beta Parallel Reduction (VParRed),
       Unconditional Confluence, Determinism of Weak Head Reduction, and
       Unconditional Kashima Standardization on Pure Beta / venv_empty *)

Theorem VParRedT_vpat_empty_iff env U G e1 e2 :
  VParRedT env U vpat_empty G e1 e2 <-> VParRed e1 e2.
Proof.
  split.
  - induction 1 as
      [ G0 i
      | G0 u
      | G0 c ls
      | G0 f f' a a' _ IHf _ IHa
      | G0 A A' b b' _ IHA _ IHb
      | G0 A A' B B' _ IHA _ IHB
      | G0 A e1 e1' e2 e2' _ IH1 _ IH2
      | G0 p r e m1 m2 m2' Hpat ];
      try (constructor; assumption).
    contradiction.
  - intros H; revert G.
    induction H as
      [ i
      | u
      | c ls
      | f f' a a' _ IHf _ IHa
      | A A' b b' _ IHA _ IHb
      | A A' B B' _ IHA _ IHB
      | A b b' a a' _ IHb _ IHa ];
      intros G.
    + apply VPRT_bvar.
    + apply VPRT_sort.
    + apply VPRT_const.
    + exact (VPRT_app (IHf G) (IHa G)).
    + exact (VPRT_lam (IHA G) (IHb (A :: G))).
    + exact (VPRT_forallE (IHA G) (IHB (A :: G))).
    + exact (VPRT_beta (IHb (A :: G)) (IHa G)).
Qed.

Theorem VParRedTS_vpat_empty_iff env U G e1 e2 :
  VParRedTS env U vpat_empty G e1 e2 <-> VParRedStar e1 e2.
Proof.
  split.
  - induction 1 as [| y z _ IH h2].
    + apply VPRS_refl.
    + exact (VParRedStar_trans IH
               (VParRed_to_Star (proj1 (VParRedT_vpat_empty_iff env U G y z) h2))).
  - induction 1 as [e | e1 e2 e3 h1 _ IH].
    + exact VRTC_rfl.
    + exact (VRTC_head (proj2 (VParRedT_vpat_empty_iff env U G e1 e2) h1) IH).
Qed.

Theorem VParRedT_vpat_empty_diamond env U G e e1 e2 :
  VParRedT env U vpat_empty G e e1 ->
  VParRedT env U vpat_empty G e e2 ->
  exists e3,
    VParRedT env U vpat_empty G e1 e3 /\
    VParRedT env U vpat_empty G e2 e3.
Proof.
  intros H1 H2.
  apply VParRedT_vpat_empty_iff in H1.
  apply VParRedT_vpat_empty_iff in H2.
  destruct (VParRed_diamond H1 H2) as [e3 [R1 R2]].
  exists e3; split; apply VParRedT_vpat_empty_iff; assumption.
Qed.

Theorem VParRedTS_vpat_empty_church_rosser env U G e e1 e2 :
  VParRedTS env U vpat_empty G e e1 ->
  VParRedTS env U vpat_empty G e e2 ->
  exists e3,
    VParRedTS env U vpat_empty G e1 e3 /\
    VParRedTS env U vpat_empty G e2 e3.
Proof.
  intros H1 H2.
  apply VParRedTS_vpat_empty_iff in H1.
  apply VParRedTS_vpat_empty_iff in H2.
  destruct (VParRedStar_ChurchRosser H1 H2) as [e3 [R1 R2]].
  exists e3; split; apply VParRedTS_vpat_empty_iff; assumption.
Qed.

Corollary VParRedTS_empty_uncond_church_rosser U G e e1 e2 :
  VParRedTS venv_empty U vpat_empty G e e1 ->
  VParRedTS venv_empty U vpat_empty G e e2 ->
  exists e3,
    VParRedTS venv_empty U vpat_empty G e1 e3 /\
    VParRedTS venv_empty U vpat_empty G e2 e3.
Proof.
  exact (@VParRedTS_vpat_empty_church_rosser venv_empty U G e e1 e2).
Qed.

Lemma VIsMajorPremise_vpat_empty e :
  ~ VIsMajorPremise vpat_empty e.
Proof.
  intros [p [[r H] _]]; exact H.
Qed.

Theorem VWHRed_vpat_empty_determ env U G e e1 e2 :
  VWHRed env U vpat_empty G e e1 ->
  VWHRed env U vpat_empty G e e2 ->
  e1 = e2.
Proof.
  intros H1. revert e2.
  induction H1 as [f f' a l1 IH | f a a' l1 _ _ | A bd a | p r e0 m1 m2 l1 _ _];
    intros e2 H2.
  - inversion H2 as [g g' b r1 | g b b' r1 _ | A0 bd0 b | p' r' e0 m1' m2' r1 _ _]; subst.
    + f_equal; exact (IH _ r1).
    + exfalso; exact (VIsMajorPremise_vpat_empty r1).
    + exfalso; exact (VWHNF_lam l1).
    + contradiction.
  - exfalso; exact (VIsMajorPremise_vpat_empty l1).
  - inversion H2 as [g g' b r1 | g b b' r1 _ | | p' r' e0 m1' m2' r1 _ _]; subst.
    + exfalso; exact (VWHNF_lam r1).
    + exfalso; exact (VIsMajorPremise_vpat_empty r1).
    + reflexivity.
    + contradiction.
  - contradiction.
Qed.

Theorem VWHRedS_vpat_empty_determ env U G e e1 e2 :
  VWHRedS env U vpat_empty G e e1 ->
  VWHNF env U vpat_empty G e1 ->
  VWHRedS env U vpat_empty G e e2 ->
  VWHNF env U vpat_empty G e2 ->
  e1 = e2.
Proof.
  intros H1 W1 H2 W2.
  revert e2 H2 W2.
  refine (@VRTC_head_ind VExpr (VWHRed env U vpat_empty G)
            (fun x z => VWHNF env U vpat_empty G z ->
               forall e2, VWHRedS env U vpat_empty G x e2 ->
                          VWHNF env U vpat_empty G e2 -> z = e2)
            _ _ e e1 H1 W1).
  - intros x Wx e2 H2 W2.
    exact (VWHNF_whRedS Wx H2).
  - intros x y z l1 _ IH Wz e2 H2 W2.
    destruct (VRTC_to_hd H2) as [| x0 y' z' r1 r2].
    + exfalso; exact (W2 y l1).
    + pose proof (VWHRed_vpat_empty_determ l1 r1) as Heq; subst y'.
      exact (IH Wz z' (VRTC_of_hd r2) W2).
Qed.

Corollary VWHRed_empty_determ U G e e1 e2 :
  VWHRed venv_empty U vpat_empty G e e1 ->
  VWHRed venv_empty U vpat_empty G e e2 ->
  e1 = e2.
Proof.
  exact (@VWHRed_vpat_empty_determ venv_empty U G e e1 e2).
Qed.

Corollary VWHRedS_empty_determ U G e e1 e2 :
  VWHRedS venv_empty U vpat_empty G e e1 ->
  VWHNF venv_empty U vpat_empty G e1 ->
  VWHRedS venv_empty U vpat_empty G e e2 ->
  VWHNF venv_empty U vpat_empty G e2 ->
  e1 = e2.
Proof.
  exact (@VWHRedS_vpat_empty_determ venv_empty U G e e1 e2).
Qed.

(* Concrete inhabited evaluation witness on venv_empty:
   ((\x : Type 0. x) Prop) weak-head reduces in venv_empty to Prop in WHNF *)
Theorem VWHRedS_empty_id_sort_witness :
  VWHRedS venv_empty 0 vpat_empty []
    (VApp (VLam (VSort (VLSucc VLZero)) (VBVar 0)) (VSort VLZero))
    (VSort VLZero) /\
  VWHNF venv_empty 0 vpat_empty [] (VSort VLZero).
Proof.
  split.
  - pose proof (VWHR_beta (env := venv_empty) (U := 0) (Pat := vpat_empty)
                  [] (VSort (VLSucc VLZero)) (VBVar 0) (VSort VLZero)) as Hstep.
    simpl in Hstep.
    exact (VRTC_single Hstep).
  - apply VWHNF_sort.
Qed.

(* Unconditional Kashima Standardization on Pure Beta / vpat_empty *)

Lemma VWHRed_vpat_empty_ctx_irrel env U G1 env' U' G2 e1 e2 :
  VWHRed env U vpat_empty G1 e1 e2 ->
  VWHRed env' U' vpat_empty G2 e1 e2.
Proof.
  induction 1 as [f f' a _ IH | f a a' l1 _ _ | A bd a | p r e0 m1 m2 l1 _ _].
  - exact (VWHR_app a IH).
  - exfalso; exact (VIsMajorPremise_vpat_empty l1).
  - apply VWHR_beta.
  - contradiction.
Qed.

Lemma VWHRedS_vpat_empty_ctx_irrel env U G1 env' U' G2 e1 e2 :
  VWHRedS env U vpat_empty G1 e1 e2 ->
  VWHRedS env' U' vpat_empty G2 e1 e2.
Proof.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_vpat_empty_ctx_irrel env' U' G2 h2)).
Qed.

Lemma VStRed_vpat_empty_ctx_irrel env U G1 env' U' G2 e1 e2 :
  VStRed env U vpat_empty G1 e1 e2 ->
  VStRed env' U' vpat_empty G2 e1 e2.
Proof.
  intros H; revert G2.
  induction H as
    [ G1 e i h1
    | G1 e u h1
    | G1 e c ls h1
    | G1 e f f' a a' h1 _ IH1 _ IH2
    | G1 e A A' b b' h1 _ IH1 _ IH2
    | G1 e A A' B B' h1 _ IH1 _ IH2 ];
    intros G2.
  - exact (VStR_bvar (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1)).
  - exact (VStR_sort (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1)).
  - exact (VStR_const (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1)).
  - exact (VStR_app (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1) (IH1 G2) (IH2 G2)).
  - exact (VStR_lam (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1) (IH1 G2) (IH2 (A :: G2))).
  - exact (VStR_forallE (VWHRedS_vpat_empty_ctx_irrel env' U' G2 h1) (IH1 G2) (IH2 (A :: G2))).
Qed.

Lemma VWHRed_vpat_empty_weakN env U G n k e1 e2 :
  VWHRed env U vpat_empty G e1 e2 ->
  VWHRed env U vpat_empty G (vliftN n k e1) (vliftN n k e2).
Proof.
  induction 1 as [f f' a _ IH | f a a' l1 _ _ | A bd a | p r e0 m1 m2 l1 _ _]; simpl.
  - exact (VWHR_app (vliftN n k a) IH).
  - exfalso; exact (VIsMajorPremise_vpat_empty l1).
  - rewrite vliftN_vinst0; apply VWHR_beta.
  - contradiction.
Qed.

Lemma VWHRedS_vpat_empty_weakN env U G n k e1 e2 :
  VWHRedS env U vpat_empty G e1 e2 ->
  VWHRedS env U vpat_empty G (vliftN n k e1) (vliftN n k e2).
Proof.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_vpat_empty_weakN n k h2)).
Qed.

Lemma VStRed_vpat_empty_weakN env U G n k e1 e2 :
  VStRed env U vpat_empty G e1 e2 ->
  VStRed env U vpat_empty G (vliftN n k e1) (vliftN n k e2).
Proof.
  intros H.
  assert (Hgen : forall G' k, VStRed env U vpat_empty G' (vliftN n k e1) (vliftN n k e2)).
  { induction H as
      [ G0 e i h1
      | G0 e u h1
      | G0 e c ls h1
      | G0 e f f' a a' h1 _ IH1 _ IH2
      | G0 e A A' b b' h1 _ IH1 _ IH2
      | G0 e A A' B B' h1 _ IH1 _ IH2 ];
      intros G' k0; simpl.
    - exact (VStR_bvar (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
    - exact (VStR_sort (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
    - exact (VStR_const (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
    - exact (VStR_app (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                      (IH1 G' k0) (IH2 G' k0)).
    - exact (VStR_lam (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                      (IH1 G' k0) (IH2 (vliftN n k0 A :: G') (S k0))).
    - exact (VStR_forallE (VWHRedS_vpat_empty_weakN n k0 (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                          (IH1 G' k0) (IH2 (vliftN n k0 A :: G') (S k0))). }
  exact (Hgen G k).
Qed.

Lemma VWHRed_vpat_empty_inst env U G a k e1 e2 :
  VWHRed env U vpat_empty G e1 e2 ->
  VWHRed env U vpat_empty G (vinst e1 a k) (vinst e2 a k).
Proof.
  induction 1 as [f f' arg _ IH | f arg arg' l1 _ _ | A bd arg | p r e0 m1 m2 l1 _ _]; simpl.
  - exact (VWHR_app (vinst arg a k) IH).
  - exfalso; exact (VIsMajorPremise_vpat_empty l1).
  - rewrite vinst0_vinst_hi; apply VWHR_beta.
  - contradiction.
Qed.

Lemma VWHRedS_vpat_empty_inst env U G a k e1 e2 :
  VWHRedS env U vpat_empty G e1 e2 ->
  VWHRedS env U vpat_empty G (vinst e1 a k) (vinst e2 a k).
Proof.
  induction 1 as [| y z _ IH h2].
  - exact VRTC_rfl.
  - exact (VRTC_tail IH (VWHRed_vpat_empty_inst a k h2)).
Qed.

Lemma VStRed_vpat_empty_inst env U G a1 a2 e1 e2 k :
  VStRed env U vpat_empty G a1 a2 ->
  VStRed env U vpat_empty G e1 e2 ->
  VStRed env U vpat_empty G (vinst e1 a1 k) (vinst e2 a2 k).
Proof.
  intros Ha He.
  assert (Hgen : forall G' k0,
    VStRed env U vpat_empty G' a1 a2 ->
    VStRed env U vpat_empty G' (vinst e1 a1 k0) (vinst e2 a2 k0)).
  { clear k Ha.
    induction He as
      [ G0 e i h1
      | G0 e u h1
      | G0 e c ls h1
      | G0 e f f' a a' h1 _ IH1 _ IH2
      | G0 e A A' b b' h1 _ IH1 _ IH2
      | G0 e A A' B B' h1 _ IH1 _ IH2 ];
      intros G' k0 Ha; simpl.
    - apply (VStRed_whRed
               (VWHRedS_vpat_empty_inst a1 k0
                  (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
      simpl; unfold vinstVar.
      destruct (i <? k0).
      + apply VStRed_refl.
      + destruct (Nat.eqb i k0).
        * exact (VStRed_vpat_empty_weakN k0 0 Ha).
        * apply VStRed_refl.
    - exact (VStR_sort (VWHRedS_vpat_empty_inst a1 k0
                          (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
    - exact (VStR_const (VWHRedS_vpat_empty_inst a1 k0
                           (VWHRedS_vpat_empty_ctx_irrel env U G' h1))).
    - exact (VStR_app (VWHRedS_vpat_empty_inst a1 k0
                         (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                      (IH1 G' k0 Ha) (IH2 G' k0 Ha)).
    - exact (VStR_lam (VWHRedS_vpat_empty_inst a1 k0
                         (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                      (IH1 G' k0 Ha)
                      (IH2 (vinst A a1 k0 :: G') (S k0)
                           (VStRed_vpat_empty_ctx_irrel _ _ _ Ha))).
    - exact (VStR_forallE (VWHRedS_vpat_empty_inst a1 k0
                             (VWHRedS_vpat_empty_ctx_irrel env U G' h1))
                          (IH1 G' k0 Ha)
                          (IH2 (vinst A a1 k0 :: G') (S k0)
                               (VStRed_vpat_empty_ctx_irrel _ _ _ Ha))). }
  exact (Hgen G k Ha).
Qed.

Theorem VStRed_vpat_empty_triangle env U G e e1 e2 :
  VStRed env U vpat_empty G e e1 ->
  VParRed e1 e2 ->
  VStRed env U vpat_empty G e e2.
Proof.
  intros H1 H2.
  revert G e H1.
  induction H2 as
    [ i
    | u
    | c ls
    | f1 f2 a1 a2 _ IH1 _ IH2
    | A1 A2 b1 b2 _ IH1 _ IH2
    | A1 A2 B1 B2 _ IH1 _ IH2
    | dom bd1 bd2 arg1 arg2 _ IH1 _ IH2 ];
    intros G e H1.
  - exact H1.
  - exact H1.
  - exact H1.
  - inversion H1 as [| | | G0 e0 f0 f1' a0 a1' a_1 a_2 a_3 | |]; subst.
    exact (VStR_app a_1 (IH1 _ _ a_2) (IH2 _ _ a_3)).
  - inversion H1 as [| | | | G0 e0 A0 A1' bd0 b1' a_1 a_2 a_3 |]; subst.
    exact (VStR_lam a_1 (IH1 _ _ a_2) (IH2 _ _ a_3)).
  - inversion H1 as [| | | | | G0 e0 A0 A1' B0 B1' a_1 a_2 a_3]; subst.
    exact (VStR_forallE a_1 (IH1 _ _ a_2) (IH2 _ _ a_3)).
  - inversion H1 as [| | | G0 e0 f0 lam_t a0 arg1' a_1 a_2 a_3 | |]; subst.
    inversion a_2 as [| | | | G1 f_y A0 dom' bd0 bd1' a_4 a_5 a_6 |]; subst.
    apply (VStRed_whRed
             (VRTC_tail (VRTC_trans a_1 (VWHRedS_app a0 a_4))
                        (VWHR_beta G A0 bd0 a0))).
    exact (VStRed_vpat_empty_inst 0
             (IH2 G a0 a_3)
             (IH1 G bd0 (VStRed_vpat_empty_ctx_irrel _ _ _ a_6))).
Qed.

Theorem VParRedTS_vpat_empty_standard env U G e e' :
  VParRedTS env U vpat_empty G e e' ->
  VStRed env U vpat_empty G e e'.
Proof.
  intros H.
  assert (Hstar : forall x y, VParRedStar x y ->
            forall z, VStRed env U vpat_empty G z x -> VStRed env U vpat_empty G z y).
  { intros x y Hxy.
    induction Hxy as [x | x w y Hstep _ IH]; intros z Hz.
    - exact Hz.
    - exact (IH z (VStRed_vpat_empty_triangle Hz Hstep)). }
  exact (Hstar e e' (proj1 (VParRedTS_vpat_empty_iff env U G e e') H)
               e (VStRed_refl env U vpat_empty G e)).
Qed.

Corollary VParRedStar_standard_empty e e' :
  VParRedStar e e' ->
  VStRed venv_empty 0 vpat_empty [] e e'.
Proof.
  intros H.
  apply VParRedTS_vpat_empty_standard.
  apply VParRedTS_vpat_empty_iff.
  exact H.
Qed.

Corollary VParRedStar_whRedS_sort_empty e u :
  VParRedStar e (VSort u) ->
  VWHRedS venv_empty 0 vpat_empty [] e (VSort u).
Proof.
  intros H.
  pose proof (VParRedStar_standard_empty H) as Hst.
  inversion Hst as [| G0 e0 v r1 | | | |]; subst.
  exact r1.
Qed.

Corollary VParRedStar_whRedS_forallE_empty e A B :
  VParRedStar e (VForallE A B) ->
  exists A0 B0,
    VWHRedS venv_empty 0 vpat_empty [] e (VForallE A0 B0) /\
    VParRedStar A0 A /\
    VParRedStar B0 B.
Proof.
  intros H.
  pose proof (VParRedStar_standard_empty H) as Hst.
  inversion Hst as [| | | | | G0 e0 A0 A' B0 B' r1 r2 r3]; subst.
  exists A0, B0; split; [exact r1 | split].
  - apply (VParRedTS_vpat_empty_iff venv_empty 0 []).
    exact (VStRed_parRedS r2).
  - apply (VParRedTS_vpat_empty_iff venv_empty 0 [A0]).
    exact (VStRed_parRedS r3).
Qed.

(* ========================================================================= *)
(* Axiom Audit: Verify Closed under the global context for all milestones    *)
(* ========================================================================= *)

(* Section 1: Pattern.lean *)
Print Assumptions VPatternMatches_uniq.
Print Assumptions VPatternMatches_determ.
Print Assumptions VPatternMatches_vlift'.
Print Assumptions VPatternMatches_vliftN.
Print Assumptions VPatternMatches_vinst.
Print Assumptions vrhs_apply_vlift'.
Print Assumptions vrhs_apply_vliftN.
Print Assumptions vrhs_apply_vinst.

(* Section 2: Injectivity.lean & UniqueTyping.lean *)
Print Assumptions VIsDefEq_uniq.
Print Assumptions VIsDefEq_uniqU.
Print Assumptions VIsDefEq_iff.
Print Assumptions VIsDefEq_trans_l.
Print Assumptions VIsDefEq_trans_r.
Print Assumptions VIsDefEqU_defeqDF.
Print Assumptions VIsDefEqU_of_l.
Print Assumptions VIsDefEqU_of_r.
Print Assumptions VIsDefEqU_trans.
Print Assumptions VHasType_defeqU_l.
Print Assumptions VHasType_defeqU_r.
Print Assumptions VIsType_defeqU_l.
Print Assumptions VIsDefEq_skips.
Print Assumptions VIsDefEq_weakN_iff.
Print Assumptions VHasType_weakN_iff.
Print Assumptions VIsType_weakN_iff.

(* Section 3: ChurchRosser.lean *)
Print Assumptions VCParRedT_to_VParRedT.
Print Assumptions VCParRedT_exists.
Print Assumptions VParRedT_triangle.
Print Assumptions VParRedT_church_rosser.
Print Assumptions VNormalEq_parRed.
Print Assumptions VNormalEq_parRedS.
Print Assumptions VParRedTS_church_rosser.
Print Assumptions VCRDefEq_refl.
Print Assumptions VCRDefEq_symm.
Print Assumptions VCRDefEq_trans.
Print Assumptions VIsDefEq_church_rosser.

(* Section 4: HeadReduction.lean *)
Print Assumptions VWHRed_determ.
Print Assumptions VWHRedS_determ.
Print Assumptions VStRed_triangle.
Print Assumptions VParRedTS_standard.
Print Assumptions VIsDefEq_reduce_sort.
Print Assumptions VIsDefEq_reduce_forallE.
Print Assumptions VInferType_hasType.
Print Assumptions VInferType_determ.
Print Assumptions VInferType_exists.

(* Section 5: Non-Vacuity & Unconditional Pure-Beta Theorems *)
Print Assumptions PatternParams_of_no_defeqs.
Print Assumptions PatternParams_empty.
Print Assumptions VParRedTS_empty_uncond_church_rosser.
Print Assumptions VWHRed_empty_determ.
Print Assumptions VWHRedS_empty_determ.
Print Assumptions VWHRedS_empty_id_sort_witness.
Print Assumptions VParRedStar_standard_empty.
Print Assumptions VParRedStar_whRedS_sort_empty.
Print Assumptions VParRedStar_whRedS_forallE_empty.
