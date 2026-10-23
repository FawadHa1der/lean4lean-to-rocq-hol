(* SPDX-License-Identifier: Apache-2.0
   Free-variable telescopes for the port of Lean4Lean/Inductive/Add.lean.
   They are internal syntax operations, never a bypass around type checking. *)
From Stdlib Require Import List String Bool Arith NArith.
From LeanPort Require Import Syntax Universes Checker.
Import ListNotations.
Open Scope string_scope.

Record ind_local := {
  il_id : name;
  il_user : name;
  il_binder : binder_info;
  il_type : expr
}.
Record ind_state := { ist_next : nat; ist_context : context }.
Definition initial_ind_state :=
  {| ist_next := 0; ist_context := empty_context |}.
Definition local_expr (x : ind_local) := EFVar (il_id x).
Definition local_exprs (xs : list ind_local) := map local_expr xs.

Definition ind_fresh (s : ind_state) (user : name) (bi : binder_info) (ty : expr)
    : ind_local * ind_state :=
  let id := NameNum (NameStr NameAnon "_rocq_ind") (N.of_nat (ist_next s)) in
  let x := {| il_id := id; il_user := user; il_binder := bi; il_type := ty |} in
  let g := ist_context s in
  (x, {| ist_next := S (ist_next s);
         ist_context := {| bound_context := bound_context g;
           free_context := (id, {| binding_type := ty; binding_value := None |})
                             :: free_context g |} |}).

Fixpoint abstract_local (id : name) (depth : nat) (e : expr) : expr :=
  match e with
  | EFVar n => if name_eqb id n then EBVar depth else e
  | EApp f a => EApp (abstract_local id depth f) (abstract_local id depth a)
  | ELam n bi a b => ELam n bi (abstract_local id depth a) (abstract_local id (S depth) b)
  | EPi n bi a b => EPi n bi (abstract_local id depth a) (abstract_local id (S depth) b)
  | ELet n a v b nd => ELet n (abstract_local id depth a) (abstract_local id depth v)
      (abstract_local id (S depth) b) nd
  | EProj n i a => EProj n i (abstract_local id depth a)
  | EMData a => EMData (abstract_local id depth a)
  | _ => e
  end.

Definition close_pi (xs : list ind_local) (body : expr) : expr :=
  fold_right (fun x b => EPi (il_user x) (il_binder x) (il_type x)
                             (abstract_local (il_id x) 0 b)) body xs.
Definition close_lam (xs : list ind_local) (body : expr) : expr :=
  fold_right (fun x b => ELam (il_user x) (il_binder x) (il_type x)
                              (abstract_local (il_id x) 0 b)) body xs.
Definition apply_exprs (fn : expr) (args : list expr) := fold_left EApp args fn.
Definition apply_locals (fn : expr) (args : list ind_local) :=
  apply_exprs fn (local_exprs args).
Fixpoint split_app_aux (e : expr) (args : list expr) : expr * list expr :=
  match e with
  | EApp f a => split_app_aux f (a :: args)
  | _ => (e,args)
  end.
Definition split_app (e : expr) := split_app_aux e [].

Fixpoint has_inductive (names : list name) (e : expr) : bool :=
  match e with
  | EConst n _ => name_mem n names
  | EApp a b | ELam _ _ a b | EPi _ _ a b => has_inductive names a || has_inductive names b
  | ELet _ a v b _ => has_inductive names a || has_inductive names v || has_inductive names b
  | EProj n _ a => name_mem n names || has_inductive names a
  | EMData a => has_inductive names a
  | _ => false
  end.
Fixpoint raw_arity (e : expr) : nat :=
  match e with EPi _ _ _ body => S (raw_arity body) | _ => 0 end.
Fixpoint recursive_constructor (names : list name) (e : expr) : bool :=
  match e with
  | EPi _ _ a b => has_inductive names a || recursive_constructor names b
  | _ => false
  end.
Fixpoint reflexive_constructor (names : list name) (e : expr) : bool :=
  match e with
  | EPi _ _ a b =>
    (match a with EPi _ _ _ _ => has_inductive names a | _ => false end)
    || reflexive_constructor names b
  | _ => false
  end.
Fixpoint level_never_zero (u : level) : bool :=
  match u with
  | LSucc _ => true
  | LMax a b => level_never_zero a || level_never_zero b
  | LIMax _ b => level_never_zero b
  | _ => false
  end.

Definition ind_sort (fuel : nat) (env : environment) (ps : list name)
    (s : ind_state) (e : expr) : result level :=
  ty <- infer fuel env ps (ist_context s) e ;;
  ty <- whnf fuel env ps (ist_context s) ty ;;
  match ty with ESort u => Accept u | _ => Reject ExpectedSort end.

Fixpoint consume_type_annotations (e : expr) : expr :=
  match e with
  | EApp (EApp (EConst n _) a) _ =>
    if name_eqb n (NameStr NameAnon "optParam") ||
       name_eqb n (NameStr NameAnon "autoParam")
    then consume_type_annotations a else e
  | EApp (EConst n _) a =>
    if name_eqb n (NameStr NameAnon "outParam") ||
       name_eqb n (NameStr NameAnon "semiOutParam")
    then consume_type_annotations a else e
  | _ => e
  end.
Definition checked_domain (fuel : nat) (env : environment) (ps : list name)
    (s : ind_state) (a : expr) : result expr :=
  let cleaned := consume_type_annotations a in
  if expr_eqb a cleaned then Accept a else
  ok <- defeq fuel env ps (ist_context s) a cleaned ;;
  _ <- require ok TypeMismatch ;; Accept cleaned.

Fixpoint open_telescope (depth fuel : nat) (env : environment) (ps : list name)
    (s : ind_state) (ty : expr) : result (list ind_local * expr * ind_state) :=
  match depth with
  | 0 => Decline OutOfFuel
  | S depth =>
    ty <- whnf fuel env ps (ist_context s) ty ;;
    match ty with
    | EPi n bi a b =>
      a <- checked_domain fuel env ps s a ;;
      let '(x,s) := ind_fresh s n bi a in
      rest <- open_telescope depth fuel env ps s (instantiate b (local_expr x)) ;;
      let '(xs,body,s) := rest in Accept (x::xs,body,s)
    | _ => Accept ([],ty,s)
    end
  end.

Fixpoint open_parameters (count fuel : nat) (env : environment) (ps : list name)
    (s : ind_state) (ty : expr) : result (list ind_local * expr * ind_state) :=
  match count with
  | 0 => Accept ([],ty,s)
  | S count =>
    ty <- whnf fuel env ps (ist_context s) ty ;;
    match ty with
    | EPi n bi a b =>
      a <- checked_domain fuel env ps s a ;;
      let '(x,s) := ind_fresh s n bi a in
      rest <- open_parameters count fuel env ps s (instantiate b (local_expr x)) ;;
      let '(xs,body,s) := rest in Accept (x::xs,body,s)
    | _ => Reject MalformedDeclaration
    end
  end.

Fixpoint apply_parameters (params : list ind_local) (fuel : nat)
    (env : environment) (ps : list name) (s : ind_state) (ty : expr) : result expr :=
  match params with
  | [] => Accept ty
  | x :: xs =>
    ty <- whnf fuel env ps (ist_context s) ty ;;
    match ty with
    | EPi _ _ a b =>
      ok <- defeq fuel env ps (ist_context s) a (il_type x) ;;
      _ <- require ok TypeMismatch ;;
      apply_parameters xs fuel env ps s (instantiate b (local_expr x))
    | _ => Reject MalformedDeclaration
    end
  end.

Lemma abstract_local_self n depth : abstract_local n depth (EFVar n) = EBVar depth.
Proof. simpl. rewrite name_eqb_refl. reflexivity. Qed.
Lemma close_pi_empty e : close_pi [] e = e.
Proof. reflexivity. Qed.
Lemma apply_exprs_empty e : apply_exprs e [] = e.
Proof. reflexivity. Qed.
