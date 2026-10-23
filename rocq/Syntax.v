(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Changed Gallina reimplementation of Lean4Lean syntax/context operations.
   Upstream pin and attribution: NOTICE. *)
From Coq Require Import List String Bool Arith PeanoNat NArith Lia.
Import ListNotations.
Set Implicit Arguments.

Inductive name : Type :=
| NameAnon : name
| NameStr : name -> string -> name
| NameNum : name -> N -> name.

Fixpoint name_eqb (a b : name) : bool :=
  match a, b with
  | NameAnon, NameAnon => true
  | NameStr a s, NameStr b t => name_eqb a b && String.eqb s t
  | NameNum a n, NameNum b m => name_eqb a b && N.eqb n m
  | _, _ => false
  end.

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
  | _, _ => false
  end.

Definition name_mem (n : name) (ns : list name) : bool :=
  existsb (name_eqb n) ns.

Fixpoint names_unique (ns : list name) : bool :=
  match ns with
  | [] => true
  | n :: ns => negb (name_mem n ns) && names_unique ns
  end.

Inductive level : Type :=
| LZero : level
| LSucc : level -> level
| LMax : level -> level -> level
| LIMax : level -> level -> level
| LParam : name -> level
| LMVar : name -> level.

Fixpoint level_eqb (u v : level) : bool :=
  match u, v with
  | LZero, LZero => true
  | LSucc u, LSucc v => level_eqb u v
  | LMax a b, LMax c d | LIMax a b, LIMax c d =>
      level_eqb a c && level_eqb b d
  | LParam a, LParam b | LMVar a, LMVar b => name_eqb a b
  | _, _ => false
  end.

Fixpoint level_wf (ps : list name) (u : level) : bool :=
  match u with
  | LZero => true
  | LSucc v => level_wf ps v
  | LMax a b | LIMax a b => level_wf ps a && level_wf ps b
  | LParam n => name_mem n ps
  | LMVar _ => false
  end.

Fixpoint level_has_meta (u : level) : bool :=
  match u with
  | LMVar _ => true
  | LSucc v => level_has_meta v
  | LMax a b | LIMax a b => level_has_meta a || level_has_meta b
  | _ => false
  end.

Fixpoint lookup_level (ps : list name) (us : list level) (n : name) : level :=
  match ps, us with
  | p :: ps, u :: us => if name_eqb p n then u else lookup_level ps us n
  | _, _ => LParam n
  end.

Fixpoint subst_level (ps : list name) (us : list level) (u : level) : level :=
  match u with
  | LZero => LZero
  | LSucc v => LSucc (subst_level ps us v)
  | LMax a b => LMax (subst_level ps us a) (subst_level ps us b)
  | LIMax a b => LIMax (subst_level ps us a) (subst_level ps us b)
  | LParam n => lookup_level ps us n
  | LMVar n => LMVar n
  end.

Inductive binder_info := BDefault | BImplicit | BStrictImplicit | BInstImplicit.
Inductive literal := LitNat : N -> literal | LitString : string -> literal.
Inductive expr : Type :=
| EBVar : nat -> expr
| EFVar : name -> expr
| EMVar : name -> expr
| ESort : level -> expr
| EConst : name -> list level -> expr
| EApp : expr -> expr -> expr
| ELam : name -> binder_info -> expr -> expr -> expr
| EPi : name -> binder_info -> expr -> expr -> expr
| ELet : name -> expr -> expr -> expr -> bool -> expr
| ELit : literal -> expr
| EProj : name -> nat -> expr -> expr
| EMData : expr -> expr.

Definition literal_eqb (a b : literal) : bool :=
  match a, b with
  | LitNat n, LitNat m => N.eqb n m
  | LitString s, LitString t => String.eqb s t
  | _, _ => false
  end.

(* Binder names, hints and binder-info are not part of kernel alpha equality. *)
Fixpoint expr_eqb (a b : expr) : bool :=
  match a, b with
  | EBVar n, EBVar m => Nat.eqb n m
  | EFVar n, EFVar m | EMVar n, EMVar m => name_eqb n m
  | ESort u, ESort v => level_eqb u v
  | EConst n us, EConst m vs => name_eqb n m && list_eqb level_eqb us vs
  | EApp f x, EApp g y => expr_eqb f g && expr_eqb x y
  | ELam _ _ a b, ELam _ _ c d | EPi _ _ a b, EPi _ _ c d =>
      expr_eqb a c && expr_eqb b d
  | ELet _ a v b _, ELet _ c w d _ =>
      expr_eqb a c && expr_eqb v w && expr_eqb b d
  | ELit l, ELit k => literal_eqb l k
  | EProj n i a, EProj m j b => name_eqb n m && Nat.eqb i j && expr_eqb a b
  | EMData a, EMData b => expr_eqb a b
  | _, _ => false
  end.

Fixpoint lift (amount cutoff : nat) (e : expr) : expr :=
  match e with
  | EBVar i => EBVar (if cutoff <=? i then amount + i else i)
  | EApp f a => EApp (lift amount cutoff f) (lift amount cutoff a)
  | ELam n bi a b => ELam n bi (lift amount cutoff a) (lift amount (S cutoff) b)
  | EPi n bi a b => EPi n bi (lift amount cutoff a) (lift amount (S cutoff) b)
  | ELet n a v b nd => ELet n (lift amount cutoff a) (lift amount cutoff v)
      (lift amount (S cutoff) b) nd
  | EProj n i a => EProj n i (lift amount cutoff a)
  | EMData a => EMData (lift amount cutoff a)
  | _ => e
  end.

(* Removing a binder lowers variables above it and lifts the substituted value
   beneath intervening binders. *)
Fixpoint subst (index : nat) (value e : expr) : expr :=
  match e with
  | EBVar i =>
      if Nat.eqb i index then
        match index with 0 => value | S _ => lift index 0 value end
      else EBVar (if index <? i then pred i else i)
  | EApp f a => EApp (subst index value f) (subst index value a)
  | ELam n bi a b => ELam n bi (subst index value a) (subst (S index) value b)
  | EPi n bi a b => EPi n bi (subst index value a) (subst (S index) value b)
  | ELet n a v b nd => ELet n (subst index value a) (subst index value v)
      (subst (S index) value b) nd
  | EProj n i a => EProj n i (subst index value a)
  | EMData a => EMData (subst index value a)
  | _ => e
  end.

Definition instantiate (body value : expr) : expr := subst 0 value body.

(* Values are ordered innermost binder first and live outside the removed block. *)
Fixpoint subst_many (index : nat) (values : list expr) (e : expr) : expr :=
  match e with
  | EBVar i =>
      if i <? index then e else
      match nth_error values (i - index) with
      | Some value => match index with 0 => value | S _ => lift index 0 value end
      | None => EBVar (i - List.length values)
      end
  | EApp f a => EApp (subst_many index values f) (subst_many index values a)
  | ELam n bi a b => ELam n bi (subst_many index values a) (subst_many (S index) values b)
  | EPi n bi a b => EPi n bi (subst_many index values a) (subst_many (S index) values b)
  | ELet n a v b nd => ELet n (subst_many index values a) (subst_many index values v)
      (subst_many (S index) values b) nd
  | EProj n i a => EProj n i (subst_many index values a)
  | EMData a => EMData (subst_many index values a)
  | _ => e
  end.

Definition instantiate_many (body : expr) (values : list expr) : expr :=
  match values with [] => body | _ => subst_many 0 values body end.

Fixpoint subst_levels (ps : list name) (us : list level) (e : expr) : expr :=
  match e with
  | ESort u => ESort (subst_level ps us u)
  | EConst n vs => EConst n (map (subst_level ps us) vs)
  | EApp f a => EApp (subst_levels ps us f) (subst_levels ps us a)
  | ELam n bi a b => ELam n bi (subst_levels ps us a) (subst_levels ps us b)
  | EPi n bi a b => EPi n bi (subst_levels ps us a) (subst_levels ps us b)
  | ELet n a v b nd => ELet n (subst_levels ps us a) (subst_levels ps us v)
      (subst_levels ps us b) nd
  | EProj n i a => EProj n i (subst_levels ps us a)
  | EMData a => EMData (subst_levels ps us a)
  | _ => e
  end.

Fixpoint supported_expr (e : expr) : bool :=
  match e with
  | ELit _ | EProj _ _ _ => false
  | EApp a b | ELam _ _ a b | EPi _ _ a b => supported_expr a && supported_expr b
  | ELet _ a v b _ => supported_expr a && supported_expr v && supported_expr b
  | EMData a => supported_expr a
  | _ => true
  end.

Fixpoint scoped (depth : nat) (e : expr) : bool :=
  match e with
  | EBVar i => i <? depth
  | EApp a b => scoped depth a && scoped depth b
  | ELam _ _ a b | EPi _ _ a b => scoped depth a && scoped (S depth) b
  | ELet _ a v b _ => scoped depth a && scoped depth v && scoped (S depth) b
  | EProj _ _ a | EMData a => scoped depth a
  | _ => true
  end.

Record binding := { binding_type : expr; binding_value : option expr }.
Record context := {
  bound_context : list binding;
  free_context : list (name * binding)
}.
Definition empty_context : context := {| bound_context := []; free_context := [] |}.
Definition push_binding (g : context) (ty : expr) (value : option expr) : context :=
  {| bound_context := {| binding_type := ty; binding_value := value |} :: bound_context g;
     free_context := free_context g |}.
Fixpoint find_free (n : name) (xs : list (name * binding)) : option binding :=
  match xs with
  | [] => None
  | (m, b) :: xs => if name_eqb n m then Some b else find_free n xs
  end.

Record inductive_data := {
  ind_num_params : nat;
  ind_num_indices : nat;
  ind_all : list name;
  ind_ctors : list name;
  ind_num_nested : nat;
  ind_is_rec : bool;
  ind_is_reflexive : bool;
  ind_is_unsafe : bool
}.
Record constructor_data := {
  ctor_induct : name;
  ctor_index : nat;
  ctor_num_params : nat;
  ctor_num_fields : nat;
  ctor_is_unsafe : bool
}.
Record recursor_rule := {
  rule_ctor : name;
  rule_nfields : nat;
  rule_rhs : expr
}.
Record recursor_data := {
  rec_all : list name;
  rec_num_params : nat;
  rec_num_indices : nat;
  rec_num_motives : nat;
  rec_num_minors : nat;
  rec_rules : list recursor_rule;
  rec_k : bool;
  rec_is_unsafe : bool
}.
Inductive primitive_kind :=
| PNatAdd | PNatPred | PNatSub | PNatMul | PNatPow | PNatGcd
| PNatMod | PNatDiv | PNatBEq | PNatBLE
| PNatLAnd | PNatLOr | PNatXor | PNatBitwise | PNatShiftLeft | PNatShiftRight
| PCharOfNat | PStringOfList.

Definition primitive_kind_eqb (a b : primitive_kind) : bool :=
  match a, b with
  | PNatAdd, PNatAdd | PNatPred, PNatPred | PNatSub, PNatSub
  | PNatMul, PNatMul | PNatPow, PNatPow | PNatGcd, PNatGcd
  | PNatMod, PNatMod | PNatDiv, PNatDiv | PNatBEq, PNatBEq | PNatBLE, PNatBLE
  | PNatLAnd, PNatLAnd | PNatLOr, PNatLOr | PNatXor, PNatXor
  | PNatBitwise, PNatBitwise | PNatShiftLeft, PNatShiftLeft
  | PNatShiftRight, PNatShiftRight | PCharOfNat, PCharOfNat
  | PStringOfList, PStringOfList => true
  | _, _ => false
  end.

Lemma primitive_kind_eqb_spec a b : primitive_kind_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; congruence. Qed.
Inductive quotient_kind := QType | QCtor | QLift | QInd.
Inductive decl_kind :=
| DAssumption | DDefinition | DTheorem | DOpaque | DUnsupported
| DInductive : inductive_data -> decl_kind
| DConstructor : constructor_data -> decl_kind
| DRecursor : recursor_data -> decl_kind
| DPrimitive : primitive_kind -> decl_kind
| DQuotient : quotient_kind -> decl_kind
| DUnsafe : decl_kind -> decl_kind
| DPartial : decl_kind.
(* Lean4Lean/Declaration.lean ReducibilityHints.lt'. Heights are unbounded
   naturals: transport must not truncate hostile exported heights to UInt32. *)
Inductive reducibility_hints := HintOpaque | HintAbbrev | HintRegular : N -> reducibility_hints.
Definition hints_lt (a b : reducibility_hints) : bool :=
  match a, b with
  | _, HintOpaque => false
  | HintAbbrev, _ => false
  | HintOpaque, _ => true
  | _, HintAbbrev => true
  | HintRegular n, HintRegular m => N.ltb n m
  end.
Record declaration := {
  decl_name : name;
  decl_params : list name;
  decl_type : expr;
  decl_value : option expr;
  decl_kind_of : decl_kind;
  decl_hints : reducibility_hints
}.
Definition effective_hints (d : declaration) : reducibility_hints :=
  match decl_kind_of d with
  | DDefinition | DPrimitive _ => decl_hints d
  | _ => HintOpaque
  end.
Definition environment := list declaration.
Fixpoint find_decl (n : name) (env : environment) : option declaration :=
  match env with
  | [] => None
  | d :: env => if name_eqb n (decl_name d) then Some d else find_decl n env
  end.

Inductive reject_reason :=
| UnknownConstant | UnknownFreeVariable | LooseBoundVariable
| UnknownUniverse | UniverseArity | ExpectedSort | ExpectedPi
| TypeMismatch | NotDefinitionallyEqual | DuplicateDeclaration
| DuplicateUniverse | MalformedDeclaration | MetaVariable.
Inductive decline_reason := OutOfFuel | UnsupportedExpression | UnsupportedDeclaration.
Inductive result (A : Type) :=
| Accept : A -> result A
| Reject : reject_reason -> result A
| Decline : decline_reason -> result A.
Arguments Accept {A} _.
Arguments Reject {A} _.
Arguments Decline {A} _.

Definition bind {A B} (r : result A) (f : A -> result B) : result B :=
  match r with Accept a => f a | Reject e => Reject e | Decline e => Decline e end.
Notation "x <- r ;; f" := (bind r (fun x => f))
  (at level 100, r at next level, right associativity).
Definition require (b : bool) (err : reject_reason) : result unit :=
  if b then Accept tt else Reject err.

Lemma name_eqb_refl n : name_eqb n n = true.
Proof.
  induction n; simpl; rewrite ?IHn, ?String.eqb_refl, ?N.eqb_refl; reflexivity.
Qed.

Lemma name_eqb_eq a b : name_eqb a b = true -> a = b.
Proof.
  revert b; induction a; destruct b; simpl; try discriminate; auto.
  - intros H. apply andb_true_iff in H as [H1 H2].
    apply IHa in H1. apply String.eqb_eq in H2. subst. reflexivity.
  - intros H. apply andb_true_iff in H as [H1 H2].
    apply IHa in H1. apply N.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lift_zero e : forall cutoff, lift 0 cutoff e = e.
Proof.
  induction e; intros; simpl; try (f_equal; auto).
  destruct (cutoff <=? n); reflexivity.
Qed.

Lemma instantiate_var value : instantiate (EBVar 0) value = value.
Proof. reflexivity. Qed.

Lemma subst_many_nil e : forall index, subst_many index [] e = e.
Proof.
  induction e; intros; simpl; try (f_equal; auto).
  destruct (n <? index); simpl; auto.
  destruct (n - index); simpl; rewrite ?Nat.sub_0_r; reflexivity.
Qed.

Lemma subst_many_single e : forall index value,
  subst_many index [value] e = subst index value e.
Proof.
  induction e; intros; simpl; try (f_equal; auto).
  destruct (Nat.lt_trichotomy n index) as [Hlt | [Heq | Hgt]].
  - assert ((n <? index) = true) as A by (apply Nat.ltb_lt; lia).
    assert ((n =? index) = false) as B by (apply Nat.eqb_neq; lia).
    assert ((index <? n) = false) as C by (apply Nat.ltb_ge; lia).
    rewrite A, B, C. reflexivity.
  - subst n. rewrite Nat.ltb_irrefl, Nat.eqb_refl, Nat.sub_diag. reflexivity.
  - assert ((n <? index) = false) as A by (apply Nat.ltb_ge; lia).
    assert ((n =? index) = false) as B by (apply Nat.eqb_neq; lia).
    assert ((index <? n) = true) as C by (apply Nat.ltb_lt; lia).
    rewrite A, B, C. destruct (n - index) eqn:D; [lia |].
    destruct n0; simpl; f_equal; lia.
Qed.

Lemma instantiate_many_single body value :
  instantiate_many body [value] = instantiate body value.
Proof. apply subst_many_single. Qed.

Lemma lift_scoped e : forall amount cutoff depth,
  scoped depth e = true -> scoped (amount + depth) (lift amount cutoff e) = true.
Proof.
  induction e; intros amount cutoff depth H; simpl in *; try reflexivity.
  - apply Nat.ltb_lt in H. destruct (cutoff <=? n); apply Nat.ltb_lt; lia.
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. auto.
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. split; auto.
    replace (S (amount + depth)) with (amount + S depth) by lia. auto.
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. split; auto.
    replace (S (amount + depth)) with (amount + S depth) by lia. auto.
  - apply andb_true_iff in H as [Hav Hb]. apply andb_true_iff in Hav as [Ha Hv].
    apply andb_true_iff. split; [apply andb_true_iff; auto |].
    replace (S (amount + depth)) with (amount + S depth) by lia. auto.
  - auto.
  - auto.
Qed.

Lemma subst_many_scoped e : forall index values depth,
  scoped (index + List.length values + depth) e = true ->
  Forall (fun value => scoped depth value = true) values ->
  scoped (index + depth) (subst_many index values e) = true.
Proof.
  induction e; intros index values depth H Hvalues; simpl in *; try reflexivity.
  - apply Nat.ltb_lt in H. destruct (n <? index) eqn:Hsmall.
    + simpl. apply Nat.ltb_lt. apply Nat.ltb_lt in Hsmall. lia.
    + apply Nat.ltb_ge in Hsmall. destruct (nth_error values (n - index)) eqn:Hnth.
      * assert (Hv : scoped depth e = true).
        { rewrite Forall_forall in Hvalues. apply Hvalues.
          eapply nth_error_In. exact Hnth. }
        destruct index; simpl; auto. exact (@lift_scoped e (S index) 0 depth Hv).
      * apply nth_error_None in Hnth. simpl. apply Nat.ltb_lt. lia.
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. eauto.
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. split; eauto.
    exact (IHe2 (S index) values depth Hb Hvalues).
  - apply andb_true_iff in H as [Ha Hb]. apply andb_true_iff. split; eauto.
    exact (IHe2 (S index) values depth Hb Hvalues).
  - apply andb_true_iff in H as [Hav Hb]. apply andb_true_iff in Hav as [Ha Hv].
    apply andb_true_iff. split; [apply andb_true_iff; eauto |].
    exact (IHe3 (S index) values depth Hb Hvalues).
  - eauto.
  - eauto.
Qed.

Lemma subst_level_nil us u : subst_level [] us u = u.
Proof. induction u; simpl; f_equal; auto. Qed.

Lemma subst_levels_nil us e : subst_levels [] us e = e.
Proof.
  induction e; simpl; try (f_equal; auto).
  - rewrite subst_level_nil. reflexivity.
  - f_equal. induction l; simpl; rewrite ?subst_level_nil, ?IHl; reflexivity.
Qed.

Definition instantiate_levels (ps : list name) (us : list level) (e : expr) : expr :=
  match ps with [] => e | _ => subst_levels ps us e end.

Lemma instantiate_levels_correct ps us e :
  instantiate_levels ps us e = subst_levels ps us e.
Proof. destruct ps; simpl; auto. symmetry. apply subst_levels_nil. Qed.

Lemma bind_decline {A B} (d : decline_reason) (f : A -> result B) :
  bind (Decline d) f = Decline d.
Proof. reflexivity. Qed.
