(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Verified pure-Gallina runtime kernel combining:
   - All 6 Lean4Lean FuelConfig axes (whnf, whnfEager, lazyDelta, etaExpand,
     recDepth, inductiveFuel);
   - Annotated runtime expressions (cexpr) carrying exact O(1) looseBVarRange,
     hasFVar, alpha-invariant 20-bit structural hash, support flag, and optional
     DAG arena identity (eliminating O(|term|) lift/subst/hash walks on closed
     subterms and O(2^n) alpha comparisons on shared DAGs, all in pure Gallina
     with zero pointer equality or extraction overrides);
   - O(1) interned context IDs (cc_id : positive) for collision-free,
     full-context WHNF, InferType, DefEq, delta-congruence failure, and
     union-find EquivManager caches (closing open-term-cache-context without
     re-hashing or re-walking binder telescopes);
   - Canonical path-trie DAG inference (O(N log N) on exponential-tree DAGs
     such as app-lam, beta-ladder, and fueled-chain);
   - Two-level tail-recursive Nat.add accumulator loop inside WHNF (O(1) stack
     and O(1) recursion depth on deeply nested Nat.add chains such as g 19 0);
   - Hint-priority congruence-before-literal, opposite-projection before Nat
     probes, lazyDeltaProjReduction on bare and applied projections, and
     cheap-atomic-args-first refutation. *)
From Stdlib Require Import List Bool String Arith PeanoNat NArith PArith.BinPos Lia
  FSets.FMapAVL FSets.FMapPositive FSets.FMapFacts.
From LeanPort Require Import Syntax Universes WhnfPolicy EagerPolicy NatProbeDispatch
  Checker LookupCore LookupIntegration LookupRefinement Primitives Declarations
  InductiveUtils Inductive NestedTransform NestedAdmission Quotient Safety
  InductiveSafety DagScope DagArena DagMemo IndexedDagAdmission PersistentIndex
  AdmissionDelta CombinedAdmissionRefinement PersistentAdmission FuelConfig DefEqCache.
Import ListNotations.
Open Scope nat_scope.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Annotated Runtime Expressions (cexpr) with O(1) Metadata               *)
(* ========================================================================= *)

Definition chash_mix (a b : positive) : positive :=
  pos_xor_trunc 14 (xO a) b.

Definition pos_of_nat_fast (n : nat) : positive := hash_nat_small n.
Definition pos_of_N_fast (n : N) : positive := hash_N_fast n.
Definition hash_name (n : name) : positive := hash_name_bounded 6 n.
Definition hash_level (u : level) : positive := hash_level_bounded 4 u.
Definition hash_levels (us : list level) : positive := hash_levels_bounded 3 us 1%positive.
Definition hash_string (s : string) : positive := hash_string_bounded 12 s 1%positive.

Record cmeta : Type := {
  cm_lbr  : nat;
  cm_hfv  : bool;
  cm_supp : bool;
  cm_dag  : option positive
}.

Definition cmeta_closed_supp : cmeta :=
  {| cm_lbr := 0; cm_hfv := false; cm_supp := true; cm_dag := None |}.

Definition cmeta_closed_unsupp : cmeta :=
  {| cm_lbr := 0; cm_hfv := false; cm_supp := false; cm_dag := None |}.

Definition cmeta_fvar : cmeta :=
  {| cm_lbr := 0; cm_hfv := true; cm_supp := true; cm_dag := None |}.

Inductive cexpr : Type :=
| CBVar  : cmeta -> nat -> cexpr
| CFVar  : cmeta -> name -> cexpr
| CMVar  : cmeta -> name -> cexpr
| CSort  : cmeta -> level -> cexpr
| CConst : cmeta -> name -> list level -> cexpr
| CApp   : cmeta -> cexpr -> cexpr -> cexpr
| CLam   : cmeta -> name -> binder_info -> cexpr -> cexpr -> cexpr
| CPi    : cmeta -> name -> binder_info -> cexpr -> cexpr -> cexpr
| CLet   : cmeta -> name -> cexpr -> cexpr -> cexpr -> bool -> cexpr
| CProj  : cmeta -> name -> nat -> cexpr -> cexpr
| CMData : cmeta -> cexpr -> cexpr
| CLit   : cmeta -> literal -> cexpr.

Definition c_meta (e : cexpr) : cmeta :=
  match e with
  | CBVar m _ | CFVar m _ | CMVar m _ | CSort m _ | CConst m _ _
  | CApp m _ _ | CLam m _ _ _ _ | CPi m _ _ _ _ | CLet m _ _ _ _ _
  | CProj m _ _ _ | CMData m _ | CLit m _ => m
  end.

Definition ce_lbr  (e : cexpr) : nat      := cm_lbr  (c_meta e).
Definition ce_hfv  (e : cexpr) : bool     := cm_hfv  (c_meta e).
Definition ce_supp (e : cexpr) : bool     := cm_supp (c_meta e).
Definition ce_dag  (e : cexpr) : option positive := cm_dag (c_meta e).

Fixpoint c_hash_expr_bounded (depth : nat) (e : cexpr) : positive :=
  match depth with
  | 0 =>
      match e with
      | CBVar _ i => chash_mix 3%positive (pos_of_nat_fast i)
      | CFVar _ n => chash_mix 5%positive (hash_name n)
      | CMVar _ n => chash_mix 7%positive (hash_name n)
      | CSort _ _ => 11%positive
      | CConst _ n _ => chash_mix 13%positive (hash_name n)
      | CApp _ _ _ => 17%positive
      | CLam _ _ _ _ _ => 19%positive
      | CPi _ _ _ _ _ => 23%positive
      | CLet _ _ _ _ _ _ => 29%positive
      | CProj _ n i _ => chash_mix 31%positive (chash_mix (hash_name n) (pos_of_nat_fast i))
      | CMData _ _ => 37%positive
      | CLit _ (LitNat n) => chash_mix 41%positive (pos_of_N_fast n)
      | CLit _ (LitString s) => chash_mix 43%positive (hash_string s)
      end
  | S d =>
      match e with
      | CBVar _ i => chash_mix 3%positive (pos_of_nat_fast i)
      | CFVar _ n => chash_mix 5%positive (hash_name n)
      | CMVar _ n => chash_mix 7%positive (hash_name n)
      | CSort _ u => chash_mix 11%positive (hash_level u)
      | CConst _ n us => chash_mix 13%positive (chash_mix (hash_name n) (hash_levels us))
      | CApp _ f a => chash_mix 17%positive (chash_mix (c_hash_expr_bounded d f) (c_hash_expr_bounded d a))
      | CLam _ _ _ dom b => chash_mix 19%positive (chash_mix (c_hash_expr_bounded d dom) (c_hash_expr_bounded d b))
      | CPi _ _ _ dom b => chash_mix 23%positive (chash_mix (c_hash_expr_bounded d dom) (c_hash_expr_bounded d b))
      | CLet _ _ t v b _ =>
          chash_mix 29%positive
            (chash_mix (c_hash_expr_bounded d t) (chash_mix (c_hash_expr_bounded d v) (c_hash_expr_bounded d b)))
      | CProj _ n i a =>
          chash_mix 31%positive (chash_mix (hash_name n) (chash_mix (pos_of_nat_fast i) (c_hash_expr_bounded d a)))
      | CMData _ a => chash_mix 37%positive (c_hash_expr_bounded d a)
      | CLit _ (LitNat n) => chash_mix 41%positive (pos_of_N_fast n)
      | CLit _ (LitString s) => chash_mix 43%positive (hash_string s)
      end
  end.

Definition ce_hash (e : cexpr) : positive := c_hash_expr_bounded 3 e.

Definition c_tag_dag (id : positive) (e : cexpr) : cexpr :=
  let m := c_meta e in
  let m' := {| cm_lbr := cm_lbr m; cm_hfv := cm_hfv m;
               cm_supp := cm_supp m; cm_dag := Some id |} in
  match e with
  | CBVar _ i => CBVar m' i
  | CFVar _ n => CFVar m' n
  | CMVar _ n => CMVar m' n
  | CSort _ u => CSort m' u
  | CConst _ n us => CConst m' n us
  | CApp _ f a => CApp m' f a
  | CLam _ n bi d b => CLam m' n bi d b
  | CPi _ n bi d b => CPi m' n bi d b
  | CLet _ n t v b nd => CLet m' n t v b nd
  | CProj _ n i a => CProj m' n i a
  | CMData _ a => CMData m' a
  | CLit _ l => CLit m' l
  end.

Definition mk_cmeta (lbr : nat) (hfv supp : bool) : cmeta :=
  match lbr, hfv, supp with
  | 0, false, true => cmeta_closed_supp
  | 0, false, false => cmeta_closed_unsupp
  | 0, true, true => cmeta_fvar
  | _, _, _ => {| cm_lbr := lbr; cm_hfv := hfv; cm_supp := supp; cm_dag := None |}
  end.

Definition mk_cbvar (i : nat) : cexpr :=
  CBVar {| cm_lbr := S i; cm_hfv := false; cm_supp := true; cm_dag := None |} i.

Definition mk_cfvar (n : name) : cexpr := CFVar cmeta_fvar n.
Definition mk_cmvar (n : name) : cexpr := CMVar cmeta_closed_supp n.
Definition mk_csort (u : level) : cexpr := CSort cmeta_closed_supp u.
Definition mk_cconst (n : name) (us : list level) : cexpr := CConst cmeta_closed_supp n us.

Definition mk_capp (f a : cexpr) : cexpr :=
  let mf := c_meta f in let ma := c_meta a in
  CApp (mk_cmeta (Nat.max (cm_lbr mf) (cm_lbr ma))
                 (cm_hfv mf || cm_hfv ma)
                 (cm_supp mf && cm_supp ma)) f a.

Definition mk_clam (n : name) (bi : binder_info) (d b : cexpr) : cexpr :=
  let md := c_meta d in let mb := c_meta b in
  CLam (mk_cmeta (Nat.max (cm_lbr md) (Nat.pred (cm_lbr mb)))
                 (cm_hfv md || cm_hfv mb)
                 (cm_supp md && cm_supp mb)) n bi d b.

Definition mk_cpi (n : name) (bi : binder_info) (d b : cexpr) : cexpr :=
  let md := c_meta d in let mb := c_meta b in
  CPi (mk_cmeta (Nat.max (cm_lbr md) (Nat.pred (cm_lbr mb)))
                (cm_hfv md || cm_hfv mb)
                (cm_supp md && cm_supp mb)) n bi d b.

Definition mk_clet (n : name) (t v b : cexpr) (nd : bool) : cexpr :=
  let mt := c_meta t in let mv := c_meta v in let mb := c_meta b in
  CLet (mk_cmeta (Nat.max (Nat.max (cm_lbr mt) (cm_lbr mv)) (Nat.pred (cm_lbr mb)))
                 (cm_hfv mt || cm_hfv mv || cm_hfv mb)
                 (cm_supp mt && cm_supp mv && cm_supp mb)) n t v b nd.

Definition mk_cproj (n : name) (i : nat) (a : cexpr) : cexpr :=
  let ma := c_meta a in
  CProj (mk_cmeta (cm_lbr ma) (cm_hfv ma) (cm_supp ma)) n i a.

Definition mk_cmdata (a : cexpr) : cexpr :=
  let ma := c_meta a in
  CMData (mk_cmeta (cm_lbr ma) (cm_hfv ma) (cm_supp ma)) a.

Definition mk_clit (nat_ready str_ready : bool) (l : literal) : cexpr :=
  let supp := match l with
              | LitNat _ => nat_ready
              | LitString s => str_ready && match core_utf8 s with Some _ => true | None => false end
              end in
  CLit (if supp then cmeta_closed_supp else cmeta_closed_unsupp) l.

Definition mk_cnat (n : N) : cexpr := CLit cmeta_closed_supp (LitNat n).

Fixpoint c_erase (e : cexpr) : expr :=
  match e with
  | CBVar _ i => EBVar i
  | CFVar _ n => EFVar n
  | CMVar _ n => EMVar n
  | CSort _ u => ESort u
  | CConst _ n us => EConst n us
  | CApp _ f a => EApp (c_erase f) (c_erase a)
  | CLam _ n bi d b => ELam n bi (c_erase d) (c_erase b)
  | CPi _ n bi d b => EPi n bi (c_erase d) (c_erase b)
  | CLet _ n t v b nd => ELet n (c_erase t) (c_erase v) (c_erase b) nd
  | CProj _ n i a => EProj n i (c_erase a)
  | CMData _ a => EMData (c_erase a)
  | CLit _ l => ELit l
  end.

Fixpoint c_of_expr (nat_ready str_ready : bool) (e : expr) : cexpr :=
  match e with
  | EBVar i => mk_cbvar i
  | EFVar n => mk_cfvar n
  | EMVar n => mk_cmvar n
  | ESort u => mk_csort u
  | EConst n us => mk_cconst n us
  | EApp f a => mk_capp (c_of_expr nat_ready str_ready f) (c_of_expr nat_ready str_ready a)
  | ELam n bi d b => mk_clam n bi (c_of_expr nat_ready str_ready d) (c_of_expr nat_ready str_ready b)
  | EPi n bi d b => mk_cpi n bi (c_of_expr nat_ready str_ready d) (c_of_expr nat_ready str_ready b)
  | ELet n t v b nd =>
      mk_clet n (c_of_expr nat_ready str_ready t) (c_of_expr nat_ready str_ready v)
        (c_of_expr nat_ready str_ready b) nd
  | EProj n i a => mk_cproj n i (c_of_expr nat_ready str_ready a)
  | EMData a => mk_cmdata (c_of_expr nat_ready str_ready a)
  | ELit l => mk_clit nat_ready str_ready l
  end.

Definition c_lbr_ok (e : cexpr) : Prop :=
  ce_lbr e = required_depth (c_erase e).

(* O(1) short-circuiting lift / subst / subst_many / subst_levels *)
Fixpoint c_lift_go (amount cutoff : nat) (e : cexpr) : cexpr :=
  if ce_lbr e <=? cutoff then e
  else
    match e with
    | CBVar _ i => if cutoff <=? i then mk_cbvar (amount + i) else e
    | CApp _ f a => mk_capp (c_lift_go amount cutoff f) (c_lift_go amount cutoff a)
    | CLam _ n bi d b => mk_clam n bi (c_lift_go amount cutoff d) (c_lift_go amount (S cutoff) b)
    | CPi _ n bi d b => mk_cpi n bi (c_lift_go amount cutoff d) (c_lift_go amount (S cutoff) b)
    | CLet _ n t v b nd =>
        mk_clet n (c_lift_go amount cutoff t) (c_lift_go amount cutoff v)
          (c_lift_go amount (S cutoff) b) nd
    | CProj _ n i a => mk_cproj n i (c_lift_go amount cutoff a)
    | CMData _ a => mk_cmdata (c_lift_go amount cutoff a)
    | _ => e
    end.

Definition c_lift (amount cutoff : nat) (e : cexpr) : cexpr :=
  match amount with
  | 0 => e
  | S _ => c_lift_go amount cutoff e
  end.

Fixpoint c_subst (index : nat) (value e : cexpr) : cexpr :=
  if ce_lbr e <=? index then e
  else
    match e with
    | CBVar _ i =>
        if Nat.eqb i index then
          match index with 0 => value | S _ => c_lift index 0 value end
        else if index <? i then mk_cbvar (Nat.pred i)
        else e
    | CApp _ f a => mk_capp (c_subst index value f) (c_subst index value a)
    | CLam _ n bi d b => mk_clam n bi (c_subst index value d) (c_subst (S index) value b)
    | CPi _ n bi d b => mk_cpi n bi (c_subst index value d) (c_subst (S index) value b)
    | CLet _ n t v b nd =>
        mk_clet n (c_subst index value t) (c_subst index value v) (c_subst (S index) value b) nd
    | CProj _ n i a => mk_cproj n i (c_subst index value a)
    | CMData _ a => mk_cmdata (c_subst index value a)
    | _ => e
    end.

Definition c_instantiate (body value : cexpr) : cexpr :=
  c_subst 0 value body.

Fixpoint c_subst_many_go (index nvals : nat) (values : list cexpr) (e : cexpr) : cexpr :=
  if ce_lbr e <=? index then e
  else
    match e with
    | CBVar _ i =>
        if i <? index then e
        else
          match nth_error values (i - index) with
          | Some value =>
              match index with 0 => value | S _ => c_lift index 0 value end
          | None => mk_cbvar (i - nvals)
          end
    | CApp _ f a =>
        mk_capp (c_subst_many_go index nvals values f) (c_subst_many_go index nvals values a)
    | CLam _ n bi d b =>
        mk_clam n bi (c_subst_many_go index nvals values d)
          (c_subst_many_go (S index) nvals values b)
    | CPi _ n bi d b =>
        mk_cpi n bi (c_subst_many_go index nvals values d)
          (c_subst_many_go (S index) nvals values b)
    | CLet _ n t v b nd =>
        mk_clet n (c_subst_many_go index nvals values t)
          (c_subst_many_go index nvals values v)
          (c_subst_many_go (S index) nvals values b) nd
    | CProj _ n i a => mk_cproj n i (c_subst_many_go index nvals values a)
    | CMData _ a => mk_cmdata (c_subst_many_go index nvals values a)
    | _ => e
    end.

Definition c_subst_many (index : nat) (values : list cexpr) (e : cexpr) : cexpr :=
  match values with
  | [] => e
  | _ => c_subst_many_go index (List.length values) values e
  end.

Definition c_instantiate_many (body : cexpr) (values : list cexpr) : cexpr :=
  c_subst_many 0 values body.

Fixpoint c_subst_levels_go (ps : list name) (us : list level) (e : cexpr) : cexpr :=
  match e with
  | CSort _ u => mk_csort (subst_level ps us u)
  | CConst _ n ls => mk_cconst n (map (subst_level ps us) ls)
  | CApp _ f a => mk_capp (c_subst_levels_go ps us f) (c_subst_levels_go ps us a)
  | CLam _ n bi d b => mk_clam n bi (c_subst_levels_go ps us d) (c_subst_levels_go ps us b)
  | CPi _ n bi d b => mk_cpi n bi (c_subst_levels_go ps us d) (c_subst_levels_go ps us b)
  | CLet _ n t v b nd =>
      mk_clet n (c_subst_levels_go ps us t) (c_subst_levels_go ps us v)
        (c_subst_levels_go ps us b) nd
  | CProj _ n i a => mk_cproj n i (c_subst_levels_go ps us a)
  | CMData _ a => mk_cmdata (c_subst_levels_go ps us a)
  | _ => e
  end.

Definition c_subst_levels (ps : list name) (us : list level) (e : cexpr) : cexpr :=
  match ps with
  | [] => e
  | _ => c_subst_levels_go ps us e
  end.

Fixpoint c_spine (e : cexpr) (acc : list cexpr) : cexpr * list cexpr :=
  match e with
  | CApp _ f a => c_spine f (a :: acc)
  | _ => (e, acc)
  end.

Fixpoint c_apps (f : cexpr) (args : list cexpr) : cexpr :=
  match args with
  | [] => f
  | a :: rest => c_apps (mk_capp f a) rest
  end.

Fixpoint c_beta_collect (head : cexpr) (args values : list cexpr) : cexpr :=
  match args with
  | [] => c_instantiate_many head values
  | a :: rest =>
      match head with
      | CLam _ _ _ _ body => c_beta_collect body rest (a :: values)
      | _ => c_apps (c_instantiate_many head values) (a :: rest)
      end
  end.

Definition c_beta (head : cexpr) (args : list cexpr) : cexpr :=
  c_beta_collect head args [].

Definition c_dag_same (t s : cexpr) : bool :=
  match ce_dag t, ce_dag s with
  | Some id1, Some id2 => Pos.eqb id1 id2
  | _, _ => false
  end.

(* Fast alpha-equality with O(1) DAG identity hit & O(1) hash miss *)
Fixpoint c_alpha (budget : nat) (t s : cexpr) {struct t} : bool * nat :=
  if c_dag_same t s then (true, budget)
  else
    match budget with
    | 0 => (false, 0)
    | S budget =>
        match t, s with
        | CApp _ f a, CApp _ h b
        | CLam _ _ _ f a, CLam _ _ _ h b
        | CPi _ _ _ f a, CPi _ _ _ h b =>
            let '(ok, rem) := c_alpha budget f h in
            if ok then c_alpha rem a b else (false, rem)
        | CLet _ _ a v b _, CLet _ _ c w d _ =>
            let '(ok, rem) := c_alpha budget a c in
            if ok then
              let '(ok, rem) := c_alpha rem v w in
              if ok then c_alpha rem b d else (false, rem)
            else (false, rem)
        | CProj _ n i a, CProj _ m j b =>
            if name_eqb n m && Nat.eqb i j then c_alpha budget a b else (false, budget)
        | CMData _ a, CMData _ b => c_alpha budget a b
        | CBVar _ i, CBVar _ j => (Nat.eqb i j, budget)
        | CFVar _ n, CFVar _ m | CMVar _ n, CMVar _ m => (name_eqb n m, budget)
        | CConst _ n us, CConst _ m vs => (name_eqb n m && list_eqb level_eqb us vs, budget)
        | CSort _ u, CSort _ v => (level_eqb u v, budget)
        | CLit _ a, CLit _ b => (literal_eqb a b, budget)
        | _, _ => (false, budget)
        end
    end.

Definition c_alpha_eq (t s : cexpr) : bool := fst (c_alpha 512 t s).

Fixpoint c_expr_eqb (t s : cexpr) : bool :=
  if c_dag_same t s then true
  else
    match t, s with
    | CApp _ f a, CApp _ h b
    | CLam _ _ _ f a, CLam _ _ _ h b
    | CPi _ _ _ f a, CPi _ _ _ h b => c_expr_eqb f h && c_expr_eqb a b
    | CLet _ _ a v b _, CLet _ _ c w d _ =>
        c_expr_eqb a c && c_expr_eqb v w && c_expr_eqb b d
    | CProj _ n i a, CProj _ m j b => name_eqb n m && Nat.eqb i j && c_expr_eqb a b
    | CMData _ a, CMData _ b => c_expr_eqb a b
    | CBVar _ i, CBVar _ j => Nat.eqb i j
    | CFVar _ n, CFVar _ m | CMVar _ n, CMVar _ m => name_eqb n m
    | CConst _ n us, CConst _ m vs => name_eqb n m && list_eqb level_eqb us vs
    | CSort _ u, CSort _ v => level_eqb u v
    | CLit _ a, CLit _ b => literal_eqb a b
    | _, _ => false
    end.

Definition c_nat_value (e : cexpr) : option N :=
  match e with
  | CLit _ (LitNat n) => Some n
  | CConst _ n [] => if name_eqb n core_zero_name then Some 0%N else None
  | _ => None
  end.

Definition c_nat_constructor (n : N) : cexpr :=
  if N.eqb n 0%N then mk_cconst core_zero_name []
  else mk_capp (mk_cconst core_succ_name []) (mk_cnat (N.pred n)).

Definition c_is_true (e : cexpr) : bool :=
  match e with CConst _ n [] => name_eqb n core_true_name | _ => false end.

Definition c_is_eager_reduce_argument (e : cexpr) : bool :=
  match fst (c_spine e []) with
  | CConst _ n _ => name_eqb n eager_reduce_name
  | _ => false
  end.

Definition c_same_head (fuel : nat) (t s : cexpr) : result bool :=
  match t, s with
  | CConst _ n us, CConst _ m vs =>
      if name_eqb n m then levels_equiv fuel us vs else Accept false
  | CBVar _ n, CBVar _ m => Accept (Nat.eqb n m)
  | CFVar _ n, CFVar _ m => Accept (name_eqb n m)
  | CProj _ _ i a, CProj _ _ j b => Accept (Nat.eqb i j && c_expr_eqb a b)
  | _, _ => Accept false
  end.

Definition c_reduce_native (e : cexpr) : result (option cexpr) :=
  match fst (c_spine e []) with
  | CConst _ n _ =>
      if name_eqb n core_reduce_bool_name || name_eqb n core_reduce_nat_name
      then Decline UnsupportedExpression
      else Accept None
  | _ => Accept None
  end.

Definition c_char_expr (code : N) : cexpr :=
  mk_capp (mk_cconst core_char_of_nat []) (mk_cnat code).

Fixpoint c_char_list (codes : list N) : cexpr :=
  let char_ty := mk_cconst core_char_name [] in
  match codes with
  | [] => mk_capp (mk_cconst (NameStr core_list_name "nil"%string) [LZero]) char_ty
  | code :: rest =>
      c_apps (mk_cconst (NameStr core_list_name "cons"%string) [LZero])
        [char_ty; c_char_expr code; c_char_list rest]
  end.

Definition c_expand_string (s : string) : result cexpr :=
  match core_utf8 s with
  | Some codes => Accept (mk_capp (mk_cconst core_string_of_list []) (c_char_list codes))
  | None => Reject MalformedDeclaration
  end.

Definition c_core_nat : cexpr := mk_cconst core_nat_name [].
Definition c_core_string : cexpr := mk_cconst core_string_name [].

(* Compile DAG rows once into a PositiveMap of cexprs tagged with Some id *)
Definition c_arena_table := PositiveMap.t cexpr.

Definition c_arena_ref (tbl : c_arena_table) (id : positive) : result cexpr :=
  match PositiveMap.find id tbl with
  | Some e => Accept e
  | None => Reject MalformedDeclaration
  end.

Definition c_arena_compile_node (nat_ready str_ready : bool)
    (tbl : c_arena_table) (id : positive) (node : dag_node) : result cexpr :=
  match node with
  | DBVar i => Accept (c_tag_dag id (mk_cbvar i))
  | DFVar n => Accept (c_tag_dag id (mk_cfvar n))
  | DMVar n => Accept (c_tag_dag id (mk_cmvar n))
  | DSort u => Accept (c_tag_dag id (mk_csort u))
  | DConst n us => Accept (c_tag_dag id (mk_cconst n us))
  | DApp f a =>
      fe <- c_arena_ref tbl f ;; ae <- c_arena_ref tbl a ;;
      Accept (c_tag_dag id (mk_capp fe ae))
  | DLam n bi d b =>
      de <- c_arena_ref tbl d ;; be <- c_arena_ref tbl b ;;
      Accept (c_tag_dag id (mk_clam n bi de be))
  | DPi n bi d b =>
      de <- c_arena_ref tbl d ;; be <- c_arena_ref tbl b ;;
      Accept (c_tag_dag id (mk_cpi n bi de be))
  | DLet n t v b nd =>
      te <- c_arena_ref tbl t ;; ve <- c_arena_ref tbl v ;; be <- c_arena_ref tbl b ;;
      Accept (c_tag_dag id (mk_clet n te ve be nd))
  | DLit l => Accept (c_tag_dag id (mk_clit nat_ready str_ready l))
  | DProj n i a =>
      ae <- c_arena_ref tbl a ;;
      Accept (c_tag_dag id (mk_cproj n i ae))
  | DMData a =>
      ae <- c_arena_ref tbl a ;;
      Accept (c_tag_dag id (mk_cmdata ae))
  end.

Fixpoint c_arena_build (nat_ready str_ready : bool)
    (tbl : c_arena_table) (rows : list (positive * dag_node)) : result c_arena_table :=
  match rows with
  | [] => Accept tbl
  | (id, node) :: rest =>
      ce <- c_arena_compile_node nat_ready str_ready tbl id node ;;
      c_arena_build nat_ready str_ready (PositiveMap.add id ce tbl) rest
  end.

(* ========================================================================= *)
(* 2. O(1) Interned Contexts, Caches, & Union-Find EquivManager              *)
(* ========================================================================= *)

Record c_binding : Type := {
  cb_type  : cexpr;
  cb_value : option cexpr
}.

Record c_context : Type := {
  cc_id    : positive;
  cc_bound : list c_binding;
  cc_free  : list (name * c_binding)
}.

Definition empty_c_context : c_context := {|
  cc_id    := 1%positive;
  cc_bound := [];
  cc_free  := []
|}.

Fixpoint c_find_free (n : name) (xs : list (name * c_binding)) : option c_binding :=
  match xs with
  | [] => None
  | (m, b) :: rest => if name_eqb n m then Some b else c_find_free n rest
  end.

Definition c_is_non_let_local (g : c_context) (e : cexpr) : bool :=
  match e with
  | CBVar _ i =>
      match nth_error (cc_bound g) i with
      | Some b => match cb_value b with None => true | Some _ => false end
      | None => false
      end
  | CFVar _ n =>
      match c_find_free n (cc_free g) with
      | Some b => match cb_value b with None => true | Some _ => false end
      | None => false
      end
  | _ => false
  end.

(* Pure-Gallina Union-Find EquivManager keyed by O(1) (cc_id, cexpr) *)
Record c_equiv_manager : Type := {
  cem_next   : positive;
  cem_nodes  : CacheMap.t (list (positive * cexpr * positive));
  cem_parent : PositiveMap.t positive
}.

Definition cem_empty : c_equiv_manager := {|
  cem_next   := 1%positive;
  cem_nodes  := CacheMap.empty _;
  cem_parent := PositiveMap.empty _
|}.

Fixpoint cem_find_root_fuel (fuel : nat) (parents : PositiveMap.t positive)
    (id : positive) : positive :=
  match fuel with
  | 0 => id
  | S fuel =>
      match PositiveMap.find id parents with
      | Some p => if Pos.eqb p id then id else cem_find_root_fuel fuel parents p
      | None => id
      end
  end.

Definition cem_find_root (em : c_equiv_manager) (id : positive) : positive :=
  cem_find_root_fuel 64 (cem_parent em) id.

Fixpoint cem_bucket_lookup (cid : positive) (e : cexpr)
    (xs : list (positive * cexpr * positive)) : option positive :=
  match xs with
  | [] => None
  | (cid', e', nid) :: rest =>
      if Pos.eqb cid cid' && fst (c_alpha 1024 e e') then Some nid
      else cem_bucket_lookup cid e rest
  end.

Definition cem_is_equiv_ro (em : c_equiv_manager) (h1 h2 cid : positive)
    (t s : cexpr) : bool :=
  match cache_find h1 (cem_nodes em), cache_find h2 (cem_nodes em) with
  | Some b1, Some b2 =>
      match cem_bucket_lookup cid t b1, cem_bucket_lookup cid s b2 with
      | Some id1, Some id2 => Pos.eqb (cem_find_root em id1) (cem_find_root em id2)
      | _, _ => false
      end
  | _, _ => false
  end.

Definition cem_intern (em : c_equiv_manager) (h cid : positive) (e : cexpr)
    : positive * c_equiv_manager :=
  let bucket := match cache_find h (cem_nodes em) with Some b => b | None => [] end in
  match cem_bucket_lookup cid e bucket with
  | Some id => (id, em)
  | None =>
      let id := cem_next em in
      let bucket' := (cid, e, id) :: firstn 3 bucket in
      (id, {| cem_next   := Pos.succ id;
              cem_nodes  := PositiveMap.add h bucket' (cem_nodes em);
              cem_parent := cem_parent em |})
  end.

Definition cem_add_equiv (em : c_equiv_manager) (h1 h2 cid : positive)
    (t s : cexpr) : c_equiv_manager :=
  let '(id1, em1) := cem_intern em h1 cid t in
  let '(id2, em2) := cem_intern em1 h2 cid s in
  let r1 := cem_find_root em2 id1 in
  let r2 := cem_find_root em2 id2 in
  if Pos.eqb r1 r2 then em2
  else {| cem_next   := cem_next em2;
          cem_nodes  := cem_nodes em2;
          cem_parent := PositiveMap.add r1 r2 (cem_parent em2) |}.

(* Compiled declaration & recursor rule cache *)
Record compiled_decl : Type := {
  cd_decl  : declaration;
  cd_type  : cexpr;
  cd_value : option cexpr;
  cd_rules : list (name * nat * cexpr)
}.

Record checker_state : Type := {
  cs_whnf_cache  : CacheMap.t (list (positive * cexpr * cexpr));
  cs_infer_cache : CacheMap.t (list (bool * positive * cexpr * cexpr));
  cs_defeq_cache : CacheMap.t (list (positive * cexpr * cexpr * bool));
  cs_fail_cache  : CacheMap.t (list (positive * cexpr * cexpr));
  cs_equiv       : c_equiv_manager;
  cs_decl_cache  : CacheMap.t (list (name * compiled_decl));
  cs_ctx_trie    : PositiveMap.t (list (cexpr * option cexpr * positive));
  cs_next_ctx    : positive
}.

Definition empty_checker_state : checker_state := {|
  cs_whnf_cache  := CacheMap.empty _;
  cs_infer_cache := CacheMap.empty _;
  cs_defeq_cache := CacheMap.empty _;
  cs_fail_cache  := CacheMap.empty _;
  cs_equiv       := cem_empty;
  cs_decl_cache  := CacheMap.empty _;
  cs_ctx_trie    := PositiveMap.empty _;
  cs_next_ctx    := 2%positive
|}.

Definition cache_bucket_cap : nat := 4.

Definition c_push_capped {A : Type} (x : A) (xs : list A) : list A :=
  x :: firstn (pred cache_bucket_cap) xs.

Definition c_should_cache_whnf (g : c_context) (e : cexpr) : bool :=
  match e with
  | CBVar _ _ | CSort _ _ | CMVar _ _ | CPi _ _ _ _ _ | CLit _ _ | CLam _ _ _ _ _ => false
  | CFVar _ n =>
      match c_find_free n (cc_free g) with
      | Some b => match cb_value b with Some _ => true | None => false end
      | None => false
      end
  | _ => true
  end.

Definition c_should_cache_infer (e : cexpr) : bool :=
  match e with
  | CApp _ _ _ | CLam _ _ _ _ _ | CPi _ _ _ _ _ | CLet _ _ _ _ _ _ | CProj _ _ _ _ => true
  | _ => false
  end.

Definition c_is_trivial_defeq_expr (e : cexpr) : bool :=
  match e with
  | CBVar _ _ | CFVar _ _ | CSort _ _ | CLit _ _ => true
  | _ => false
  end.

Fixpoint c_whnf_bucket_find (cid : positive) (e : cexpr)
    (xs : list (positive * cexpr * cexpr)) : option cexpr :=
  match xs with
  | [] => None
  | (cid', e', v) :: rest =>
      if Pos.eqb cid cid' && fst (c_alpha 1024 e e') then Some v
      else c_whnf_bucket_find cid e rest
  end.

Definition c_whnf_find_h (h cid : positive) (e : cexpr) (st : checker_state)
    : option cexpr :=
  match cache_find h (cs_whnf_cache st) with
  | None => None
  | Some xs => c_whnf_bucket_find cid e xs
  end.

Definition c_whnf_put_h (h cid : positive) (e v : cexpr) (st : checker_state)
    : checker_state :=
  let xs := match cache_find h (cs_whnf_cache st) with Some b => b | None => [] end in
  {| cs_whnf_cache  := PositiveMap.add h (c_push_capped (cid, e, v) xs) (cs_whnf_cache st);
     cs_infer_cache := cs_infer_cache st;
     cs_defeq_cache := cs_defeq_cache st;
     cs_fail_cache  := cs_fail_cache st;
     cs_equiv       := cs_equiv st;
     cs_decl_cache  := cs_decl_cache st;
     cs_ctx_trie    := cs_ctx_trie st;
     cs_next_ctx    := cs_next_ctx st |}.

Fixpoint c_infer_bucket_find (flag : bool) (cid : positive) (e : cexpr)
    (xs : list (bool * positive * cexpr * cexpr)) : option cexpr :=
  match xs with
  | [] => None
  | (f', cid', e', v) :: rest =>
      if Bool.eqb flag f' && Pos.eqb cid cid' && fst (c_alpha 1024 e e')
      then Some v else c_infer_bucket_find flag cid e rest
  end.

Definition c_infer_find_h (h : positive) (checking : bool) (cid : positive) (e : cexpr)
    (st : checker_state) : option cexpr :=
  match cache_find h (cs_infer_cache st) with
  | None => None
  | Some xs => c_infer_bucket_find checking cid e xs
  end.

Definition c_infer_put_h (h : positive) (checking : bool) (cid : positive) (e v : cexpr)
    (st : checker_state) : checker_state :=
  let xs := match cache_find h (cs_infer_cache st) with Some b => b | None => [] end in
  {| cs_whnf_cache  := cs_whnf_cache st;
     cs_infer_cache := PositiveMap.add h (c_push_capped (checking, cid, e, v) xs) (cs_infer_cache st);
     cs_defeq_cache := cs_defeq_cache st;
     cs_fail_cache  := cs_fail_cache st;
     cs_equiv       := cs_equiv st;
     cs_decl_cache  := cs_decl_cache st;
     cs_ctx_trie    := cs_ctx_trie st;
     cs_next_ctx    := cs_next_ctx st |}.

Fixpoint c_defeq_bucket_find (cid : positive) (t s : cexpr)
    (xs : list (positive * cexpr * cexpr * bool)) : option bool :=
  match xs with
  | [] => None
  | (cid', t', s', v) :: rest =>
      if Pos.eqb cid cid' &&
         ((fst (c_alpha 1024 t t') && fst (c_alpha 1024 s s')) ||
          (fst (c_alpha 1024 t s') && fst (c_alpha 1024 s t')))
      then Some v
      else c_defeq_bucket_find cid t s rest
  end.

Fixpoint c_fail_bucket_mem (cid : positive) (t s : cexpr)
    (xs : list (positive * cexpr * cexpr)) : bool :=
  match xs with
  | [] => false
  | (cid', t', s') :: rest =>
      if Pos.eqb cid cid' &&
         ((fst (c_alpha 1024 t t') && fst (c_alpha 1024 s s')) ||
          (fst (c_alpha 1024 t s') && fst (c_alpha 1024 s t')))
      then true
      else c_fail_bucket_mem cid t s rest
  end.

Definition c_defeq_hashes (cid : positive) (t s : cexpr) : positive * positive * positive :=
  let ht := ce_hash t in
  let hs := ce_hash s in
  let h1 := chash_mix cid ht in
  let h2 := chash_mix cid hs in
  let '(lo, hi) := if Pos.leb ht hs then (ht, hs) else (hs, ht) in
  (h1, h2, chash_mix cid (chash_mix lo hi)).

Definition c_defeq_find_h (h1 h2 hpair cid : positive) (t s : cexpr)
    (st : checker_state) : option bool :=
  if cem_is_equiv_ro (cs_equiv st) h1 h2 cid t s then Some true
  else
    match cache_find hpair (cs_defeq_cache st) with
    | None => None
    | Some xs => c_defeq_bucket_find cid t s xs
    end.

Definition c_defeq_put_h (h1 h2 hpair cid : positive) (t s : cexpr)
    (v : bool) (st : checker_state) : checker_state :=
  let xs := match cache_find hpair (cs_defeq_cache st) with Some b => b | None => [] end in
  let eqv' := if v then cem_add_equiv (cs_equiv st) h1 h2 cid t s else cs_equiv st in
  {| cs_whnf_cache  := cs_whnf_cache st;
     cs_infer_cache := cs_infer_cache st;
     cs_defeq_cache := PositiveMap.add hpair (c_push_capped (cid, t, s, v) xs) (cs_defeq_cache st);
     cs_fail_cache  := cs_fail_cache st;
     cs_equiv       := eqv';
     cs_decl_cache  := cs_decl_cache st;
     cs_ctx_trie    := cs_ctx_trie st;
     cs_next_ctx    := cs_next_ctx st |}.

Definition c_fail_mem_h (hpair cid : positive) (t s : cexpr) (st : checker_state) : bool :=
  match cache_find hpair (cs_fail_cache st) with
  | None => false
  | Some xs => c_fail_bucket_mem cid t s xs
  end.

Definition c_fail_put_h (hpair cid : positive) (t s : cexpr) (st : checker_state)
    : checker_state :=
  let xs := match cache_find hpair (cs_fail_cache st) with Some b => b | None => [] end in
  {| cs_whnf_cache  := cs_whnf_cache st;
     cs_infer_cache := cs_infer_cache st;
     cs_defeq_cache := cs_defeq_cache st;
     cs_fail_cache  := PositiveMap.add hpair (c_push_capped (cid, t, s) xs) (cs_fail_cache st);
     cs_equiv       := cs_equiv st;
     cs_decl_cache  := cs_decl_cache st;
     cs_ctx_trie    := cs_ctx_trie st;
     cs_next_ctx    := cs_next_ctx st |}.

Fixpoint c_decl_bucket_find (n : name) (xs : list (name * compiled_decl))
    : option compiled_decl :=
  match xs with
  | [] => None
  | (m, cd) :: rest => if name_eqb n m then Some cd else c_decl_bucket_find n rest
  end.

Fixpoint c_find_compiled_rule (cn : name) (rules : list (name * nat * cexpr))
    : option (nat * cexpr) :=
  match rules with
  | [] => None
  | (rn, nf, rhs) :: rest =>
      if name_eqb rn cn then Some (nf, rhs) else c_find_compiled_rule cn rest
  end.

(* ========================================================================= *)
(* 3. Stateful Monad & Methods Record                                        *)
(* ========================================================================= *)

Definition c_act (A : Type) := checker_state -> result A * checker_state.
Definition c_ret {A} (x : A) : c_act A := fun st => (Accept x, st).
Definition c_pure {A} (r : result A) : c_act A := fun st => (r, st).
Definition c_bind {A B} (m : c_act A) (f : A -> c_act B) : c_act B :=
  fun st =>
    let '(r, st') := m st in
    match r with
    | Accept x => f x st'
    | Reject err => (Reject err, st')
    | Decline why => (Decline why, st')
    end.

Notation "x <-- a ;; b" := (c_bind a (fun x => b))
  (at level 100, a at next level, right associativity).

Definition c_opt_alpha (budget : nat) (a b : option cexpr) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => fst (c_alpha budget x y)
  | _, _ => false
  end.

Fixpoint c_ctx_trie_find (ty : cexpr) (val : option cexpr)
    (xs : list (cexpr * option cexpr * positive)) : option positive :=
  match xs with
  | [] => None
  | (ty', val', nid) :: rest =>
      if fst (c_alpha 512 ty ty') && c_opt_alpha 512 val val' then Some nid
      else c_ctx_trie_find ty val rest
  end.

Definition c_push_binding (g : c_context) (ty : cexpr) (val : option cexpr)
    : c_act c_context :=
  fun st =>
    let pid := cc_id g in
    let edges := match cache_find pid (cs_ctx_trie st) with Some xs => xs | None => [] end in
    match c_ctx_trie_find ty val edges with
    | Some nid =>
        (Accept {| cc_id    := nid;
                   cc_bound := {| cb_type := ty; cb_value := val |} :: cc_bound g;
                   cc_free  := cc_free g |}, st)
    | None =>
        let nid := cs_next_ctx st in
        let edges' := (ty, val, nid) :: firstn 7 edges in
        (Accept {| cc_id    := nid;
                   cc_bound := {| cb_type := ty; cb_value := val |} :: cc_bound g;
                   cc_free  := cc_free g |},
         {| cs_whnf_cache  := cs_whnf_cache st;
            cs_infer_cache := cs_infer_cache st;
            cs_defeq_cache := cs_defeq_cache st;
            cs_fail_cache  := cs_fail_cache st;
            cs_equiv       := cs_equiv st;
            cs_decl_cache  := cs_decl_cache st;
            cs_ctx_trie    := PositiveMap.add pid edges' (cs_ctx_trie st);
            cs_next_ctx    := Pos.succ nid |})
    end.

Record c_methods : Type := {
  cm_infer       : c_context -> cexpr -> c_act cexpr;
  cm_infer_type  : c_context -> cexpr -> c_act cexpr;
  cm_whnf        : c_context -> cexpr -> c_act cexpr;
  cm_whnf_core   : bool -> c_context -> cexpr -> c_act cexpr;
  cm_defeq       : c_context -> cexpr -> cexpr -> c_act bool;
  cm_mode        : reduction_mode;
  cm_eager_defeq : c_context -> cexpr -> cexpr -> c_act bool
}.

Definition cm_inference_only (m : c_methods) : c_methods := {|
  cm_infer       := cm_infer_type m;
  cm_infer_type  := cm_infer_type m;
  cm_whnf        := cm_whnf m;
  cm_whnf_core   := cm_whnf_core m;
  cm_defeq       := cm_defeq m;
  cm_mode        := cm_mode m;
  cm_eager_defeq := cm_eager_defeq m
|}.

Definition cm_app_type_defeq (m : c_methods) (g : c_context)
    (argument domain arg_type : cexpr) : c_act bool :=
  if c_is_eager_reduce_argument argument then cm_eager_defeq m g domain arg_type
  else cm_defeq m g domain arg_type.

Definition cm_sort_of (m : c_methods) (g : c_context) (e : cexpr) : c_act level :=
  ty <-- cm_infer m g e ;;
  ty <-- cm_whnf m g ty ;;
  match ty with
  | CSort _ u => c_ret u
  | _ => c_pure (Reject ExpectedSort)
  end.

(* ========================================================================= *)
(* 4. Cached Checker Core Parameterized by Lookup & Six-Axis FuelConfig      *)
(* ========================================================================= *)

Section CachedKernel.
Variable lookup : declaration_lookup.
Variable cfg : fuel_config.
Variable env : environment.

Variable nat_ready : bool.
Variable str_ready : bool.
Variable bool_ready : bool.

Let resolve (n : name) (_ : environment) : option declaration := lookup n.

Definition c_compile_decl (d : declaration) : compiled_decl :=
  let rules :=
    match decl_kind_of d with
    | DRecursor info =>
        map (fun r => (rule_ctor r, rule_nfields r, c_of_expr nat_ready str_ready (rule_rhs r)))
            (rec_rules info)
    | _ => []
    end in
  {| cd_decl  := d;
     cd_type  := c_of_expr nat_ready str_ready (decl_type d);
     cd_value := option_map (c_of_expr nat_ready str_ready) (decl_value d);
     cd_rules := rules |}.

Definition c_get_compiled (n : name) : c_act (option compiled_decl) :=
  fun st =>
    let h := hash_name n in
    match cache_find h (cs_decl_cache st) with
    | Some bucket =>
        match c_decl_bucket_find n bucket with
        | Some cd => (Accept (Some cd), st)
        | None =>
            match lookup n with
            | None => (Accept None, st)
            | Some d =>
                let cd := c_compile_decl d in
                let st' :=
                  {| cs_whnf_cache  := cs_whnf_cache st;
                     cs_infer_cache := cs_infer_cache st;
                     cs_defeq_cache := cs_defeq_cache st;
                     cs_fail_cache  := cs_fail_cache st;
                     cs_equiv       := cs_equiv st;
                     cs_decl_cache  := PositiveMap.add h ((n, cd) :: bucket) (cs_decl_cache st);
                     cs_ctx_trie    := cs_ctx_trie st;
                     cs_next_ctx    := cs_next_ctx st |} in
                (Accept (Some cd), st')
            end
        end
    | None =>
        match lookup n with
        | None => (Accept None, st)
        | Some d =>
            let cd := c_compile_decl d in
            let st' :=
              {| cs_whnf_cache  := cs_whnf_cache st;
                 cs_infer_cache := cs_infer_cache st;
                 cs_defeq_cache := cs_defeq_cache st;
                 cs_fail_cache  := cs_fail_cache st;
                 cs_equiv       := cs_equiv st;
                 cs_decl_cache  := PositiveMap.add h [(n, cd)] (cs_decl_cache st);
                 cs_ctx_trie    := cs_ctx_trie st;
                 cs_next_ctx    := cs_next_ctx st |} in
            (Accept (Some cd), st')
        end
    end.

Definition c_get_constant (ps : list name) (n : name) (us : list level)
    : c_act compiled_decl :=
  cd_opt <-- c_get_compiled n ;;
  match cd_opt with
  | None => c_pure (Reject UnknownConstant)
  | Some cd =>
      let d := cd_decl cd in
      match decl_kind_of d with
      | DUnsupported => c_pure (Decline UnsupportedDeclaration)
      | DPartial | DUnsafe _ => c_pure (Reject MalformedDeclaration)
      | _ =>
          _ <-- c_pure (require (Nat.eqb (List.length (decl_params d)) (List.length us))
                          UniverseArity) ;;
          _ <-- c_pure (check_levels ps us) ;;
          c_ret cd
      end
  end.

Definition c_unfold (ps : list name) (e : cexpr) : c_act (option cexpr) :=
  let '(head, args) := c_spine e [] in
  match head with
  | CConst _ n us =>
      cd <-- c_get_constant ps n us ;;
      let d := cd_decl cd in
      match decl_kind_of d with
      | DDefinition | DTheorem | DPrimitive _ =>
          match cd_value cd with
          | Some value =>
              c_ret (Some (c_beta (c_subst_levels (decl_params d) us value) args))
          | None => c_pure (Reject MalformedDeclaration)
          end
      | _ => c_ret None
      end
  | _ => c_ret None
  end.

Definition c_delta_info (e : cexpr) : option declaration :=
  match fst (c_spine e []) with
  | CConst _ n us =>
      match lookup n with
      | Some d =>
          match decl_kind_of d, decl_value d with
          | DDefinition, Some _ | DTheorem, Some _ | DPrimitive _, Some _ =>
              if Nat.eqb (List.length (decl_params d)) (List.length us)
              then Some d else None
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition c_delta_sides (t s : cexpr) : bool * bool :=
  match c_delta_info t, c_delta_info s with
  | Some dt, Some ds =>
      if hints_lt (effective_hints dt) (effective_hints ds) then (false, true)
      else if hints_lt (effective_hints ds) (effective_hints dt) then (true, false)
      else (true, true)
  | _, _ => (true, true)
  end.

Definition c_erasing_delta (e : cexpr) : bool :=
  let '(head, args) := c_spine e [] in
  match head, args with
  | CConst _ n _, _ :: _ =>
      match lookup n with
      | Some d =>
          match decl_value d with
          | Some (ELam _ _ _ body) => negb (core_occurs 0 body)
          | _ => false
          end
      | None => false
      end
  | _, _ => false
  end.

Definition c_is_cheap_arg (e : cexpr) : bool :=
  match e with
  | CBVar _ _ | CFVar _ _ | CSort _ _ | CLit _ _ => true
  | CConst _ n _ =>
      match lookup n with
      | Some d =>
          match decl_kind_of d with
          | DConstructor _ | DInductive _ | DAssumption => true
          | _ => false
          end
      | None => false
      end
  | _ => false
  end.

Definition c_nat_probe_head (e : cexpr) : bool :=
  let '(head, args) := c_spine e [] in
  match head, args with
  | CConst _ n [], [_] =>
      if name_eqb n core_succ_name then true
      else match lookup n with
           | Some d => match decl_kind_of d with DPrimitive PNatPred => true | _ => false end
           | None => false
           end
  | CConst _ n [], [_; _] =>
      match lookup n with
      | Some d => match decl_kind_of d with
                  | DPrimitive PNatBitwise => false
                  | DPrimitive _ => true
                  | _ => false
                  end
      | None => false
      end
  | _, _ => false
  end.

Definition c_make_structure (owner : name) (us : list level)
    (params : list cexpr) (value : cexpr) : option cexpr :=
  match Accessor.core_inductive resolve env owner with
  | Some info =>
      match ind_ctors info with
      | [ctor] =>
          match Accessor.core_constructor resolve env ctor with
          | Some c =>
              let fix fields (index count : nat) : list cexpr :=
                match count with
                | 0 => []
                | S count => mk_cproj owner index value :: fields (S index) count
                end in
              Some (c_apps (mk_cconst ctor us)
                (List.app (firstn (ctor_num_params c) params) (fields 0 (ctor_num_fields c))))
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Definition c_reduce_proj_core (index : nat) (e : cexpr) : option cexpr :=
  let '(head, args) := c_spine e [] in
  match head with
  | CConst _ n _ =>
      match Accessor.core_constructor resolve env n with
      | Some ci =>
          if (index <? ctor_num_fields ci) &&
             Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci)
          then nth_error args (ctor_num_params ci + index)
          else None
      | None => None
      end
  | _ => None
  end.

Definition c_apply_type (rec : c_methods) (g : c_context) : cexpr -> list cexpr -> c_act cexpr :=
  fix go ty args :=
    match args with
    | [] => c_ret ty
    | arg :: args =>
        ty <-- cm_whnf rec g ty ;;
        match ty with
        | CPi _ _ _ _ body => go (c_instantiate body arg) args
        | _ => c_pure (Reject ExpectedPi)
        end
    end.

Fixpoint c_occurs (target : nat) (e : cexpr) : bool :=
  if ce_lbr e <=? target then false
  else
    match e with
    | CBVar _ i => Nat.eqb i target
    | CApp _ f a => c_occurs target f || c_occurs target a
    | CLam _ _ _ d b | CPi _ _ _ d b => c_occurs target d || c_occurs (S target) b
    | CLet _ _ t v b _ => c_occurs target t || c_occurs target v || c_occurs (S target) b
    | CProj _ _ _ a | CMData _ a => c_occurs target a
    | _ => false
    end.

Fixpoint c_projection_field (rec : c_methods) (fuel : nat) (g : c_context)
    (owner : name) (value : cexpr) (prop : bool) (skip index : nat) (ty : cexpr)
    : c_act cexpr :=
  ty <-- cm_whnf rec g ty ;;
  match ty with
  | CPi _ _ _ domain body =>
      let verify_prop := fun (_ : unit) =>
        sort <-- cm_sort_of rec g domain ;;
        is_prop <-- c_pure (level_equiv fuel sort LZero) ;;
        c_pure (require is_prop TypeMismatch) in
      match skip with
      | 0 =>
          _ <-- (if prop then verify_prop tt else c_ret tt) ;;
          c_ret domain
      | S skip =>
          _ <-- (if prop && c_occurs 0 body then verify_prop tt else c_ret tt) ;;
          c_projection_field rec fuel g owner value prop skip (S index)
            (c_instantiate body (mk_cproj owner index value))
      end
  | _ => c_pure (Reject ExpectedPi)
  end.

Definition c_infer_projection (rec : c_methods) (fuel : nat) (g : c_context)
    (owner : name) (index : nat) (value : cexpr) : c_act cexpr :=
  st <-- cm_infer rec g value ;;
  st <-- cm_whnf rec g st ;;
  let '(head, args) := c_spine st [] in
  match head, Accessor.core_inductive resolve env owner with
  | CConst _ n us, Some info =>
      _ <-- c_pure (require (name_eqb n owner &&
        Nat.eqb (List.length args) (ind_num_params info + ind_num_indices info) &&
        Nat.eqb (ind_num_indices info) 0 &&
        negb (ind_is_rec info)) TypeMismatch) ;;
      match ind_ctors info with
      | [ctor] =>
          cd_opt <-- c_get_compiled ctor ;;
          match cd_opt with
          | Some cd =>
              let d := cd_decl cd in
              match decl_kind_of d with
              | DConstructor c =>
                  _ <-- c_pure (require (index <? ctor_num_fields c) TypeMismatch) ;;
                  ty <-- c_apply_type rec g (c_subst_levels (decl_params d) us (cd_type cd))
                           (firstn (ind_num_params info) args) ;;
                  u <-- cm_sort_of rec g st ;;
                  c_projection_field rec fuel g owner value (negb (core_level_positive u))
                    index 0 ty
              | _ => c_pure (Reject MalformedDeclaration)
              end
          | None => c_pure (Reject UnknownConstant)
          end
      | _ => c_pure (Reject TypeMismatch)
      end
  | _, _ => c_pure (Reject TypeMismatch)
  end.

Definition c_binary_nat (fuel : nat) (op : primitive_kind) (a b : N) : result (option cexpr) :=
  let numeric := fun n => Accept (Some (mk_cnat n)) in
  let bounded := fun (operation : N -> N -> N) =>
    if N.leb b core_pow_max_exp then numeric (operation a b) else Accept None in
  let boolean := fun (v : bool) =>
    if bool_ready then Accept (Some (mk_cconst (if v then core_true_name else core_false_name) []))
    else Decline UnsupportedExpression in
  match op with
  | PNatAdd => numeric (N.add a b)
  | PNatSub => numeric (N.sub a b)
  | PNatMul => numeric (N.mul a b)
  | PNatPow => bounded N.pow
  | PNatGcd => numeric (N.gcd a b)
  | PNatMod => numeric (N.modulo a b)
  | PNatDiv => numeric (N.div a b)
  | PNatBEq => boolean (N.eqb a b)
  | PNatBLE => boolean (N.leb a b)
  | PNatLAnd => numeric (N.land a b)
  | PNatLOr => numeric (N.lor a b)
  | PNatXor => numeric (N.lxor a b)
  | PNatBitwise => Accept None
  | PNatShiftLeft => bounded N.shiftl
  | PNatShiftRight =>
      match core_shiftr a b with
      | Some value => numeric value
      | None => Accept None
      end
  | _ => Accept None
  end.

Definition c_reduce_nat (rec : c_methods) (fuel : nat) (g : c_context) (e : cexpr)
    : c_act (option cexpr) :=
  let '(head, args) := c_spine e [] in
  match head, args with
  | CConst _ n [], [a] =>
      let op :=
        if name_eqb n core_succ_name then Some true else
        match lookup n with
        | Some d => match decl_kind_of d with DPrimitive PNatPred => Some false | _ => None end
        | None => None
        end in
      match op with
      | Some successor =>
          if negb nat_ready then c_ret None else
          if c_is_non_let_local g a then c_ret None else
          a <-- cm_whnf rec g a ;;
          match c_nat_value a with
          | Some av => c_ret (Some (mk_cnat (if successor then N.succ av else N.pred av)))
          | None => c_ret None
          end
      | None => c_ret None
      end
  | CConst _ n [], [a; b] =>
      match lookup n with
      | Some d =>
          match decl_kind_of d with
          | DPrimitive PNatBitwise => c_ret None
          | DPrimitive op =>
              if negb nat_ready then c_ret None else
              if c_is_non_let_local g a || c_is_non_let_local g b then c_ret None else
              a <-- cm_whnf rec g a ;;
              match c_nat_value a with
              | Some av =>
                  b <-- cm_whnf rec g b ;;
                  match c_nat_value b with
                  | Some bv => c_pure (c_binary_nat fuel op av bv)
                  | None => c_ret None
                  end
              | None => c_ret None
              end
          | _ => c_ret None
          end
      | None => c_ret None
      end
  | _, _ => c_ret None
  end.

Definition c_to_constructor (rec : c_methods) (fuel : nat) (g : c_context)
    (owner : name) (k_rule : bool) (value : cexpr) : c_act cexpr :=
  reduced <-- cm_whnf rec g value ;;
  match reduced with
  | CLit _ (LitNat n) =>
      if name_eqb owner core_nat_name && nat_ready
      then c_ret (c_nat_constructor n) else c_ret reduced
  | CLit _ (LitString s) =>
      expanded <-- c_pure (c_expand_string s) ;; cm_whnf rec g expanded
  | _ =>
      let try_eta := fun _ =>
        if negb (k_rule || Accessor.core_structure resolve env owner) then c_ret reduced else
        ty <-- cm_infer rec g reduced ;;
        ty <-- cm_whnf rec g ty ;;
        let '(head, args) := c_spine ty [] in
        match head with
        | CConst _ n us =>
            if negb (name_eqb n owner) then c_ret reduced else
            match c_make_structure owner us args reduced with
            | Some candidate =>
                if k_rule then
                  sort <-- cm_sort_of rec g ty ;;
                  prop <-- c_pure (level_equiv fuel sort LZero) ;;
                  if prop then
                    ct <-- cm_infer rec g candidate ;;
                    ok <-- cm_defeq rec g ty ct ;;
                    if ok then c_ret candidate else c_ret reduced
                  else c_ret reduced
                else
                  sort <-- cm_sort_of rec g ty ;;
                  if core_level_positive sort then c_ret candidate else c_ret reduced
            | None => c_ret reduced
            end
        | _ => c_ret reduced
        end in
      match fst (c_spine reduced []) with
      | CConst _ n _ =>
          match Accessor.core_constructor resolve env n with
          | Some _ => c_ret reduced
          | None => try_eta tt
          end
      | _ => try_eta tt
      end
  end.

Definition c_reduce_recursor_compiled (rec : c_methods) (fuel : nat) (g : c_context)
    (cd : compiled_decl) (us : list level) (args : list cexpr) : c_act (option cexpr) :=
  let d := cd_decl cd in
  match decl_kind_of d with
  | DRecursor info =>
      let first_index := rec_num_params info + rec_num_motives info + rec_num_minors info in
      let major_index := first_index + rec_num_indices info in
      match nth_error args major_index with
      | None => c_ret None
      | Some major =>
          match core_major_induct major_index (decl_type d) with
          | None => c_pure (Reject MalformedDeclaration)
          | Some owner =>
              major <-- c_to_constructor rec fuel g owner (rec_k info) major ;;
              let '(ctor, fields) := c_spine major [] in
              match ctor with
              | CConst _ cn _ =>
                  match c_find_compiled_rule cn (cd_rules cd),
                        Accessor.core_constructor resolve env cn with
                  | Some (nfields, rhs_c), Some ci =>
                      if negb (name_eqb (ctor_induct ci) owner &&
                        Nat.eqb (List.length fields) (ctor_num_params ci + ctor_num_fields ci) &&
                        Nat.eqb nfields (ctor_num_fields ci) &&
                        Nat.eqb (List.length us) (List.length (decl_params d)))
                      then c_ret None else
                      let rhs_inst := c_subst_levels (decl_params d) us rhs_c in
                      let new_args :=
                        List.app (firstn first_index args)
                          (List.app (skipn (ctor_num_params ci) fields)
                            (skipn (S major_index) args)) in
                      c_ret (Some (c_beta rhs_inst new_args))
                  | _, _ => c_ret None
                  end
              | _ => c_ret None
              end
          end
      end
  | _ => c_ret None
  end.

Definition c_reduce_recursor (rec : c_methods) (fuel : nat) (g : c_context) (e : cexpr)
    : c_act (option cexpr) :=
  let '(head, args) := c_spine e [] in
  match head with
  | CConst _ n us =>
      cd_opt <-- c_get_compiled n ;;
      match cd_opt with
      | Some cd => c_reduce_recursor_compiled rec fuel g cd us args
      | None => c_ret None
      end
  | _ => c_ret None
  end.

Definition c_reduce_projection_with (rec : c_methods)
    (reduce : c_context -> cexpr -> c_act cexpr) (g : c_context)
    (owner : name) (index : nat) (value : cexpr) : c_act (option cexpr) :=
  reduced <-- reduce g value ;;
  reduced <-- match reduced with
              | CLit _ (LitString s) => expanded <-- c_pure (c_expand_string s) ;; cm_whnf rec g expanded
              | _ => c_ret reduced
              end ;;
  let '(head, args) := c_spine reduced [] in
  match head with
  | CConst _ n _ =>
      match Accessor.core_constructor resolve env n with
      | Some ci =>
          if name_eqb (ctor_induct ci) owner && (index <? ctor_num_fields ci) &&
             Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci)
          then c_ret (nth_error args (ctor_num_params ci + index))
          else c_ret None
      | None => c_ret None
      end
  | _ => c_ret None
  end.

Definition c_reduce_quotient_parts (rec : c_methods) (g : c_context)
    (qk : quotient_kind) (args : list cexpr) : c_act (option cexpr) :=
  let major_pos := match qk with QLift => Some 5 | QInd => Some 4 | _ => None end in
  match major_pos with
  | Some index =>
      match nth_error args index, nth_error args 3 with
      | Some major, Some fn =>
          major <-- cm_whnf rec g major ;;
          let '(ctor, cargs) := c_spine major [] in
          match ctor, cargs with
          | CConst _ cn _, [_; _; representative] =>
              match lookup cn with
              | Some cd =>
                  match decl_kind_of cd with
                  | DQuotient QCtor =>
                      c_ret (Some (c_apps (mk_capp fn representative) (skipn (S index) args)))
                  | _ => c_ret None
                  end
              | None => c_ret None
              end
          | _, _ => c_ret None
          end
      | _, _ => c_ret None
      end
  | None => c_ret None
  end.

Definition c_reduce_quotient (rec : c_methods) (g : c_context) (e : cexpr)
    : c_act (option cexpr) :=
  let '(head, args) := c_spine e [] in
  match head with
  | CConst _ n _ =>
      match lookup n with
      | Some d =>
          match decl_kind_of d with
          | DQuotient qk => c_reduce_quotient_parts rec g qk args
          | _ => c_ret None
          end
      | None => c_ret None
      end
  | _ => c_ret None
  end.

Fixpoint c_infer_step (rec : c_methods) (fuel : nat) (ps : list name)
    (checking : bool) (g : c_context) (e : cexpr) {struct e} : c_act cexpr :=
  let compute : c_act cexpr :=
    match e with
    | CBVar _ i =>
        match nth_error (cc_bound g) i with
        | Some b => c_ret (c_lift (S i) 0 (cb_type b))
        | None => c_pure (Reject LooseBoundVariable)
        end
    | CFVar _ n =>
        match c_find_free n (cc_free g) with
        | Some b => c_ret (cb_type b)
        | None => c_pure (Reject UnknownFreeVariable)
        end
    | CMVar _ _ => c_pure (Reject MetaVariable)
    | CSort _ u => _ <-- c_pure (check_level ps u) ;; c_ret (mk_csort (LSucc u))
    | CConst _ n us =>
        cd <-- c_get_constant ps n us ;;
        c_ret (c_subst_levels (decl_params (cd_decl cd)) us (cd_type cd))
    | CApp _ f a =>
        ft <-- c_infer_step rec fuel ps checking g f ;;
        ft <-- cm_whnf rec g ft ;;
        match ft with
        | CPi _ _ _ domain body =>
            _ <-- (if checking then
              arg_type <-- c_infer_step rec fuel ps true g a ;;
              ok <-- cm_app_type_defeq rec g a domain arg_type ;;
              c_pure (require ok TypeMismatch)
              else c_ret tt) ;;
            c_ret (c_instantiate body a)
        | _ => c_pure (Reject ExpectedPi)
        end
    | CLam _ n bi domain body =>
        _ <-- (if checking then
          dt <-- c_infer_step rec fuel ps true g domain ;;
          dt <-- cm_whnf rec g dt ;;
          match dt with CSort _ _ => c_ret tt | _ => c_pure (Reject ExpectedSort) end
          else c_ret tt) ;;
        gb <-- c_push_binding g domain None ;;
        bt <-- c_infer_step rec fuel ps checking gb body ;;
        c_ret (mk_cpi n bi domain bt)
    | CPi _ _ _ domain body =>
        dt <-- c_infer_step rec fuel ps checking g domain ;;
        dt <-- cm_whnf rec g dt ;;
        u <-- match dt with CSort _ u => c_ret u | _ => c_pure (Reject ExpectedSort) end ;;
        gb <-- c_push_binding g domain None ;;
        bt <-- c_infer_step rec fuel ps checking gb body ;;
        bt <-- cm_whnf rec gb bt ;;
        v <-- match bt with CSort _ v => c_ret v | _ => c_pure (Reject ExpectedSort) end ;;
        c_ret (mk_csort (LIMax u v))
    | CLet _ _ ty value body _ =>
        _ <-- (if checking then
          sort_type <-- c_infer_step rec fuel ps true g ty ;;
          sort_type <-- cm_whnf rec g sort_type ;;
          _ <-- match sort_type with CSort _ _ => c_ret tt | _ => c_pure (Reject ExpectedSort) end ;;
          vt <-- c_infer_step rec fuel ps true g value ;;
          ok <-- cm_defeq rec g vt ty ;;
          c_pure (require ok TypeMismatch)
          else c_ret tt) ;;
        gb <-- c_push_binding g ty (Some value) ;;
        bt <-- c_infer_step rec fuel ps checking gb body ;;
        c_ret (c_instantiate bt value)
    | CMData _ body => c_infer_step rec fuel ps checking g body
    | CLit _ (LitNat _) =>
        if nat_ready then c_ret c_core_nat
        else c_pure (Decline UnsupportedExpression)
    | CLit _ (LitString s) =>
        if str_ready then
          _ <-- c_pure (c_expand_string s) ;; c_ret c_core_string
        else c_pure (Decline UnsupportedExpression)
    | CProj _ owner index value =>
        match Accessor.core_inductive resolve env owner with
        | None => c_pure (Reject TypeMismatch)
        | Some _ => c_infer_projection
            (if checking then rec else cm_inference_only rec) fuel g owner index value
        end
    end in
  fun st =>
    if negb (c_should_cache_infer e) then compute st
    else
      let cid := cc_id g in
      let h := chash_mix (if checking then 149%positive else 151%positive)
                 (chash_mix cid (ce_hash e)) in
      match c_infer_find_h h checking cid e st with
      | Some ty => (Accept ty, st)
      | None =>
          let '(res, st') := compute st in
          match res with
          | Accept ty => (Accept ty, c_infer_put_h h checking cid e ty st')
          | other => (other, st')
          end
      end.

(* O(1) exact external-local check using precomputed cm_hfv and cm_lbr *)
Definition c_is_closed_no_fvar (e : cexpr) : bool :=
  negb (ce_hfv e) && Nat.eqb (ce_lbr e) 0.

Definition c_nat_probe_allowed (mode : reduction_mode) (t s : cexpr) : bool :=
  match mode with
  | EagerReduction => true
  | NormalReduction => c_is_closed_no_fvar t && c_is_closed_no_fvar s
  end.

Definition c_true_probe_allowed (mode : reduction_mode) (t : cexpr) : bool :=
  match mode with
  | EagerReduction => true
  | NormalReduction => c_is_closed_no_fvar t
  end.

Definition c_whnf_core_step (rec : c_methods) (fuel : nat) (ps : list name)
    (cheap : bool) (g : c_context) (e : cexpr) : c_act cexpr :=
  match e with
  | CApp _ _ _ =>
      let '(head, args) := c_spine e [] in
      match head with
      | CLam _ _ _ _ _ => cm_whnf_core rec cheap g (c_beta head args)
      | CConst _ n us =>
          cd <-- c_get_constant ps n us ;;
          match decl_kind_of (cd_decl cd) with
          | DQuotient qk =>
              quot <-- c_reduce_quotient_parts rec g qk args ;;
              match quot with
              | Some value => cm_whnf_core rec cheap g value
              | None => c_ret e
              end
          | DRecursor _ =>
              step <-- c_reduce_recursor_compiled rec fuel g cd us args ;;
              match step with
              | Some value => cm_whnf_core rec cheap g value
              | None => c_ret e
              end
          | _ => c_ret e
          end
      | _ =>
          fn <-- cm_whnf_core rec cheap g head ;;
          match fn with
          | CLam _ _ _ _ _ => cm_whnf_core rec cheap g (c_beta fn args)
          | _ =>
              let rebuilt := c_apps fn args in
              quot <-- c_reduce_quotient rec g rebuilt ;;
              step <-- match quot with Some value => c_ret (Some value)
                       | None => c_reduce_recursor rec fuel g rebuilt end ;;
              match step with
              | Some value => cm_whnf_core rec cheap g value
              | None => c_ret rebuilt
              end
          end
      end
  | CLet _ _ _ value body _ => cm_whnf_core rec cheap g (c_instantiate body value)
  | CMData _ body => cm_whnf_core rec cheap g body
  | CBVar _ i =>
      match nth_error (cc_bound g) i with
      | None => c_pure (Reject LooseBoundVariable)
      | Some b =>
          match cb_value b with
          | None => c_ret e
          | Some v => cm_whnf_core rec cheap g (c_lift (S i) 0 v)
          end
      end
  | CFVar _ n =>
      match c_find_free n (cc_free g) with
      | None => c_pure (Reject UnknownFreeVariable)
      | Some b =>
          match cb_value b with
          | None => c_ret e
          | Some v => cm_whnf_core rec cheap g v
          end
      end
  | CConst _ n us =>
      _ <-- c_get_constant ps n us ;; c_ret e
  | CSort _ u =>
      _ <-- c_pure (check_level ps u) ;; c_ret e
  | CMVar _ _ => c_pure (Reject MetaVariable)
  | CProj _ owner index value =>
      step <-- c_reduce_projection_with rec
        (if cheap then cm_whnf_core rec true else cm_whnf rec)
        g owner index value ;;
      match step with
      | Some value => cm_whnf_core rec cheap g value
      | None => c_ret e
      end
  | CLit _ (LitString s) =>
      _ <-- c_pure (c_expand_string s) ;; c_ret e
  | _ => c_ret e
  end.

(* Two-level tail-recursive Nat.add accumulator loop (8000 * 1000 = 8M steps) *)
Definition c_nat_add_outer_limit : nat := 8000.
Definition c_nat_add_inner_limit : nat := 1000.

Definition c_is_nat_add (e : cexpr) : option (cexpr * cexpr) :=
  let '(head, args) := c_spine e [] in
  match head, args with
  | CConst _ n [], [a; b] =>
      match lookup n with
      | Some d =>
          match decl_kind_of d with
          | DPrimitive PNatAdd => Some (a, b)
          | _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

Inductive c_add_step_res :=
| CAddDone : N -> c_add_step_res
| CAddFallback : c_add_step_res
| CAddNext : cexpr -> N -> c_add_step_res.

Definition c_nat_add_one_step (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (cur : cexpr) (acc : N) : c_act c_add_step_res :=
  fun st =>
    let cached_opt :=
      match cur with
      | CConst _ _ _ =>
          let cid := cc_id g in
          c_whnf_find_h (chash_mix cid (ce_hash cur)) cid cur st
      | _ => None
      end in
    match cached_opt with
    | Some cached =>
        match c_nat_value cached with
        | Some na => (Accept (CAddDone (N.add na acc)), st)
        | None => (Accept CAddFallback, st)
        end
    | None =>
        (cur' <-- c_whnf_core_step rec fuel ps false g cur ;;
         match c_nat_value cur' with
         | Some na => c_ret (CAddDone (N.add na acc))
         | None =>
             match c_is_nat_add cur' with
             | Some (a', b') =>
                 if c_is_non_let_local g b' then c_ret CAddFallback else
                 bv' <-- cm_whnf rec g b' ;;
                 match c_nat_value bv' with
                 | Some nb' => c_ret (CAddNext a' (N.add acc nb'))
                 | None => c_ret CAddFallback
                 end
             | None =>
                 match cur' with
                 | CApp _ (CConst _ m []) a' =>
                     if name_eqb m core_succ_name
                     then c_ret (CAddNext a' (N.succ acc))
                     else
                       unfolded <-- c_unfold ps cur' ;;
                       match unfolded with
                       | Some next => c_ret (CAddNext next acc)
                       | None => c_ret CAddFallback
                       end
                 | _ =>
                     unfolded <-- c_unfold ps cur' ;;
                     match unfolded with
                     | Some next => c_ret (CAddNext next acc)
                     | None => c_ret CAddFallback
                     end
                 end
             end
         end) st
    end.

Fixpoint c_nat_add_inner (inner : nat) (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (cur : cexpr) (acc : N) : c_act c_add_step_res :=
  match inner with
  | 0 => c_ret (CAddNext cur acc)
  | S inner =>
      step <-- c_nat_add_one_step rec fuel ps g cur acc ;;
      match step with
      | CAddNext cur' acc' => c_nat_add_inner inner rec fuel ps g cur' acc'
      | other => c_ret other
      end
  end.

Fixpoint c_nat_add_outer (outer : nat) (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (cur : cexpr) (acc : N) : c_act (option cexpr) :=
  match outer with
  | 0 => c_pure (Decline OutOfFuel)
  | S outer =>
      step <-- c_nat_add_inner c_nat_add_inner_limit rec fuel ps g cur acc ;;
      match step with
      | CAddDone total => c_ret (Some (mk_cnat total))
      | CAddFallback => c_ret None
      | CAddNext cur' acc' => c_nat_add_outer outer rec fuel ps g cur' acc'
      end
  end.

Inductive c_whnf_round :=
| CWhnfDone : cexpr -> c_whnf_round
| CWhnfContinue : cexpr -> c_whnf_round.

Definition c_whnf_round_step (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (e : cexpr) : c_act c_whnf_round :=
  reduced <-- c_whnf_core_step rec fuel ps false g e ;;
  match reduced with
  | CConst _ n _ =>
      if name_eqb n core_zero_name && nat_ready
      then c_ret (CWhnfDone (mk_cnat 0%N))
      else
        unfolded <-- c_unfold ps reduced ;;
        c_ret (match unfolded with Some v => CWhnfContinue v | None => CWhnfDone reduced end)
  | _ =>
      nat_hook <-- c_pure (c_reduce_native reduced) ;;
      match nat_hook with
      | Some value => c_ret (CWhnfDone value)
      | None =>
          add_fast <--
            (match c_is_nat_add reduced with
             | Some (a, b) =>
                 if c_is_closed_no_fvar a && negb (c_is_non_let_local g b) && nat_ready then
                   bv <-- cm_whnf rec g b ;;
                   match c_nat_value bv with
                   | Some nb => c_nat_add_outer c_nat_add_outer_limit rec fuel ps g a nb
                   | None => c_ret None
                   end
                 else c_ret None
             | None => c_ret None
             end) ;;
          match add_fast with
          | Some value => c_ret (CWhnfDone value)
          | None =>
              native <-- c_reduce_nat rec fuel g reduced ;;
              match native with
              | Some value => c_ret (CWhnfDone value)
              | None =>
                  unfolded <-- c_unfold ps reduced ;;
                  c_ret (match unfolded with Some v => CWhnfContinue v | None => CWhnfDone reduced end)
              end
          end
      end
  end.

Fixpoint c_whnf_loop_aux (rounds : nat) (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (e : cexpr) : c_act cexpr :=
  match rounds with
  | 0 => c_pure (Decline OutOfFuel)
  | S rounds =>
      step <-- c_whnf_round_step rec fuel ps g e ;;
      match step with
      | CWhnfDone value => c_ret value
      | CWhnfContinue next => c_whnf_loop_aux rounds rec fuel ps g next
      end
  end.

Definition c_whnf_loop (rounds : nat) (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (e : cexpr) : c_act cexpr :=
  fun st =>
    if negb (c_should_cache_whnf g e) then
      c_whnf_loop_aux rounds rec fuel ps g e st
    else
      let cid := cc_id g in
      let h := chash_mix cid (ce_hash e) in
      match c_whnf_find_h h cid e st with
      | Some r => (Accept r, st)
      | None =>
          let '(res, st') := c_whnf_loop_aux rounds rec fuel ps g e st in
          match res with
          | Accept r => (Accept r, c_whnf_put_h h cid e r st')
          | other => (other, st')
          end
      end.

Definition c_eta_compare (rec : c_methods) (g : c_context)
    (domain body other : cexpr) : c_act bool :=
  ty <-- cm_infer rec g other ;;
  ty <-- cm_whnf rec g ty ;;
  match ty with
  | CPi _ _ _ domain' _ =>
      ok <-- cm_defeq rec g domain domain' ;;
      if ok then
        gb <-- c_push_binding g domain None ;;
        cm_defeq rec gb body (mk_capp (c_lift 1 0 other) (mk_cbvar 0))
      else c_ret false
  | _ => c_ret false
  end.

Fixpoint c_compare_args_filtered (want_cheap : bool) (rec : c_methods)
    (g : c_context) (xs ys : list cexpr) : c_act bool :=
  match xs, ys with
  | [], [] => c_ret true
  | x :: xs, y :: ys =>
      let is_cheap := c_is_cheap_arg x && c_is_cheap_arg y in
      if Bool.eqb is_cheap want_cheap then
        ok <-- cm_defeq rec g x y ;;
        if ok then c_compare_args_filtered want_cheap rec g xs ys else c_ret false
      else c_compare_args_filtered want_cheap rec g xs ys
  | _, _ => c_ret false
  end.

Definition c_compare_args_cheap_first (rec : c_methods) (g : c_context)
    (xs ys : list cexpr) : c_act bool :=
  ok <-- c_compare_args_filtered true rec g xs ys ;;
  if ok then c_compare_args_filtered false rec g xs ys else c_ret false.

Definition c_congruent_apps (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act bool :=
  match t, s with
  | CApp _ _ _, CApp _ _ _ =>
      let '(tf, ta) := c_spine t [] in
      let '(sf, sa) := c_spine s [] in
      same <-- c_pure (c_same_head fuel tf sf) ;;
      if same && Nat.eqb (List.length ta) (List.length sa) then
        c_compare_args_cheap_first rec g ta sa
      else c_ret false
  | _, _ => c_ret false
  end.

Definition c_delta_congruent (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act bool :=
  fun st =>
    match c_delta_info t, c_delta_info s with
    | Some dt, Some ds =>
        match effective_hints dt, effective_hints ds with
        | HintRegular ht, HintRegular hs =>
            if N.eqb ht hs && negb (c_erasing_delta t || c_erasing_delta s) then
              let cid := cc_id g in
              let '(h1, h2, hpair) := c_defeq_hashes cid t s in
              if c_fail_mem_h hpair cid t s st then (Accept false, st)
              else
                match c_defeq_find_h h1 h2 hpair cid t s st with
                | Some true => (Accept true, st)
                | _ =>
                    let '(res, st') := c_congruent_apps rec fuel g t s st in
                    match res with
                    | Accept true => (Accept true, c_defeq_put_h h1 h2 hpair cid t s true st')
                    | Accept false => (Accept false, c_fail_put_h hpair cid t s st')
                    | other => (other, st')
                    end
                end
            else (Accept false, st)
        | _, _ => (Accept false, st)
        end
    | _, _ => (Accept false, st)
    end.

Definition c_compare_heads (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act bool :=
  match t, s with
  | CConst _ n us, CConst _ m vs =>
      if name_eqb n m then c_pure (levels_equiv fuel us vs) else c_ret false
  | CBVar _ n, CBVar _ m => c_ret (Nat.eqb n m)
  | CFVar _ n, CFVar _ m => c_ret (name_eqb n m)
  | CProj _ _ i a, CProj _ _ j b =>
      if Nat.eqb i j then cm_defeq rec g a b else c_ret false
  | CApp _ _ _, CApp _ _ _ =>
      let '(tf, ta) := c_spine t [] in
      let '(sf, sa) := c_spine s [] in
      if Nat.eqb (List.length ta) (List.length sa) then
        ok <-- cm_defeq rec g tf sf ;;
        if ok then c_compare_args_cheap_first rec g ta sa else c_ret false
      else c_ret false
  | CLam _ _ _ domain body, other => c_eta_compare rec g domain body other
  | other, CLam _ _ _ domain body => c_eta_compare rec g domain body other
  | _, _ => c_ret false
  end.

Fixpoint c_compare_fields (rec : c_methods) (g : c_context) (owner : name)
    (value : cexpr) (index : nat) (fields : list cexpr) : c_act bool :=
  match fields with
  | [] => c_ret true
  | field :: fields =>
      ok <-- cm_defeq rec g (mk_cproj owner index value) field ;;
      if ok then c_compare_fields rec g owner value (S index) fields else c_ret false
  end.

Definition c_structure_eta (rec : c_methods) (g : c_context)
    (value constructed : cexpr) : c_act bool :=
  let '(head, args) := c_spine constructed [] in
  match head with
  | CConst _ ctor _ =>
      let '(vhead, vargs) := c_spine value [] in
      let same_ctor :=
        match vhead with
        | CConst _ vctor _ => name_eqb vctor ctor && Nat.eqb (List.length vargs) (List.length args)
        | _ => false
        end in
      if same_ctor then c_ret false else
      match Accessor.core_constructor resolve env ctor with
      | Some c =>
          if Accessor.core_structure resolve env (ctor_induct c) &&
             Nat.eqb (List.length args) (ctor_num_params c + ctor_num_fields c) then
            vt <-- cm_infer rec g value ;;
            ct <-- cm_infer rec g constructed ;;
            ok <-- cm_defeq rec g vt ct ;;
            if ok then c_compare_fields rec g (ctor_induct c) value 0
              (skipn (ctor_num_params c) args) else c_ret false
          else c_ret false
      | None => c_ret false
      end
  | _ => c_ret false
  end.

Definition c_unit_like (rec : c_methods) (g : c_context) (t s : cexpr) : c_act bool :=
  ty <-- cm_infer rec g t ;;
  ty <-- cm_whnf rec g ty ;;
  match fst (c_spine ty []) with
  | CConst _ owner _ =>
      if Accessor.core_structure resolve env owner then
        match Accessor.core_inductive resolve env owner with
        | Some i =>
            match ind_ctors i with
            | [ctor] =>
                match Accessor.core_constructor resolve env ctor with
                | Some c =>
                    if Nat.eqb (ctor_num_fields c) 0 then
                      sty <-- cm_infer rec g s ;; cm_defeq rec g ty sty
                    else c_ret false
                | None => c_ret false
                end
            | _ => c_ret false
            end
        | None => c_ret false
        end
      else c_ret false
  | _ => c_ret false
  end.

Definition c_try_string_expansion (rec : c_methods) (g : c_context)
    (t s : cexpr) : c_act (option bool) :=
  let expand := fun text other =>
    expanded <-- c_pure (c_expand_string text) ;;
    ok <-- cm_defeq rec g expanded other ;; c_ret (Some ok) in
  match t, s with
  | CLit _ (LitString text), CApp _ (CConst _ n []) _ =>
      if name_eqb n core_string_of_list then expand text s else c_ret None
  | CApp _ (CConst _ n []) _, CLit _ (LitString text) =>
      if name_eqb n core_string_of_list then expand text t else c_ret None
  | _, _ => c_ret None
  end.

Definition c_compare_fallback (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act bool :=
  ok <-- c_compare_heads rec fuel g t s ;;
  if ok then c_ret true else
  ok <-- c_structure_eta rec g t s ;;
  if ok then c_ret true else
  ok <-- c_structure_eta rec g s t ;;
  if ok then c_ret true else
  expanded <-- c_try_string_expansion rec g t s ;;
  match expanded with
  | Some ok => c_ret ok
  | None => c_unit_like rec g t s
  end.

Definition c_compare_after_whnf (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act bool :=
  if c_alpha_eq t s then c_ret true else
  match t, s with
  | CSort _ u, CSort _ v => c_pure (level_equiv fuel u v)
  | CLit _ (LitNat n), CLit _ (LitNat m) => c_ret (N.eqb n m)
  | CLit _ (LitString a), CLit _ (LitString b) => c_ret (String.eqb a b)
  | CLam _ _ _ a b, CLam _ _ _ c d | CPi _ _ _ a b, CPi _ _ _ c d =>
      ok <-- cm_defeq rec g a c ;;
      if ok then
        gb <-- c_push_binding g a None ;;
        cm_defeq rec gb b d
      else c_ret false
  | _, _ =>
      tt <-- cm_infer rec g t ;;
      sort <-- cm_sort_of rec g tt ;;
      is_prop <-- c_pure (level_equiv fuel sort LZero) ;;
      if is_prop then
        st <-- cm_infer rec g s ;; cm_defeq rec g tt st
      else c_compare_fallback rec fuel g t s
  end.

Definition c_quick (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act (option bool) :=
  fun st =>
    if c_alpha_eq t s then (Accept (Some true), st)
    else
      match t, s with
      | CSort _ u, CSort _ v =>
          (ok <-- c_pure (level_equiv fuel u v) ;; c_ret (Some ok)) st
      | CLit _ a, CLit _ b => (Accept (Some (literal_eqb a b)), st)
      | CLam _ _ _ a b, CLam _ _ _ c d | CPi _ _ _ a b, CPi _ _ _ c d =>
          (ok <-- cm_defeq rec g a c ;;
           if ok then
             gb <-- c_push_binding g a None ;;
             ok <-- cm_defeq rec gb b d ;; c_ret (Some ok)
           else c_ret (Some false)) st
      | CMData _ a, CMData _ b =>
          (ok <-- cm_defeq rec g a b ;; c_ret (Some ok)) st
      | _, _ => (Accept None, st)
      end.

Definition c_proof_irrel (rec : c_methods) (fuel : nat) (g : c_context)
    (t s : cexpr) : c_act (option bool) :=
  ty <-- cm_infer rec g t ;;
  sort <-- cm_sort_of rec g ty ;;
  is_prop <-- c_pure (level_equiv fuel sort LZero) ;;
  if is_prop then
    sty <-- cm_infer rec g s ;;
    ok <-- cm_defeq rec g ty sty ;; c_ret (Some ok)
  else c_ret None.

Definition c_offset (rec : c_methods) (g : c_context) (t s : cexpr) : c_act (option bool) :=
  if nat_ready then
    let pred_of := fun e => match e with
      | CLit _ (LitNat n) => if N.eqb n 0 then None else Some (mk_cnat (N.pred n))
      | CApp _ (CConst _ n []) a => if name_eqb n core_succ_name then Some a else None
      | _ => None end in
    let zero := fun e => match e with
      | CLit _ (LitNat n) => N.eqb n 0
      | CConst _ n [] => name_eqb n core_zero_name
      | _ => false end in
    if zero t && zero s then c_ret (Some true) else
      match pred_of t, pred_of s with
      | Some a, Some b => ok <-- cm_defeq rec g a b ;; c_ret (Some ok)
      | _, _ => c_ret None
      end
  else c_ret None.

Definition c_try_unfold_proj_app (rec : c_methods) (g : c_context) (e : cexpr)
    : c_act (option cexpr) :=
  match fst (c_spine e []) with
  | CProj _ _ _ _ =>
      reduced <-- cm_whnf_core rec false g e ;;
      c_ret (if c_expr_eqb reduced e then None else Some reduced)
  | _ => c_ret None
  end.

Definition c_opposite_projection (rec : c_methods) (g : c_context)
    (t s : cexpr) : c_act (option (cexpr * cexpr)) :=
  match c_delta_info t, c_delta_info s with
  | Some _, None =>
      reduced <-- c_try_unfold_proj_app rec g s ;;
      c_ret (match reduced with Some s' => Some (t, s') | None => None end)
  | None, Some _ =>
      reduced <-- c_try_unfold_proj_app rec g t ;;
      c_ret (match reduced with Some t' => Some (t', s) | None => None end)
  | _, _ => c_ret None
  end.

Inductive c_conversion_progress :=
| CConversionDone : bool -> c_conversion_progress
| CConversionStuck : cexpr -> cexpr -> c_conversion_progress.

Definition c_nat_congr_worth_trying (t s : cexpr) : bool :=
  match snd (c_spine t []), snd (c_spine s []) with
  | [a1], [a2] => c_alpha_eq a1 a2
  | [a1; b1], [a2; b2] =>
      c_alpha_eq a1 a2 || (c_alpha_eq b1 b2 && negb (c_is_cheap_arg b1))
  | _, _ => false
  end.

Fixpoint c_lazy_delta (rounds : nat) (rec : c_methods) (fuel : nat)
    (ps : list name) (g : c_context) (t s : cexpr) : c_act c_conversion_progress :=
  match rounds with
  | 0 => c_pure (Decline OutOfFuel)
  | S rounds =>
      quick <-- c_quick rec fuel g t s ;;
      match quick with
      | Some ok => c_ret (CConversionDone ok)
      | None =>
        offset <-- c_offset rec g t s ;;
        match offset with
        | Some ok => c_ret (CConversionDone ok)
        | None =>
          let left_nat := c_nat_probe_head t in
          let right_nat := c_nat_probe_head s in
          let try_congr :=
            if left_nat && right_nat && c_is_closed_no_fvar t && c_is_closed_no_fvar s
            then c_nat_congr_worth_trying t s
            else true in
          same <-- (if try_congr then c_delta_congruent rec fuel g t s else c_ret false) ;;
          if same then c_ret (CConversionDone true) else
          projected <-- c_opposite_projection rec g t s ;;
          match projected with
          | Some (tn, sn) => c_lazy_delta rounds rec fuel ps g tn sn
          | None =>
            let '(unfold_left, unfold_right) := c_delta_sides t s in
            let both_delta :=
              match c_delta_info t, c_delta_info s with
              | Some _, Some _ => true
              | _, _ => false
              end in
            if both_delta && unfold_left && unfold_right && (negb left_nat && right_nat) then
              td <-- c_unfold ps t ;;
              match td with
              | Some e =>
                  tn <-- cm_whnf_core rec true g e ;;
                  c_lazy_delta rounds rec fuel ps g tn s
              | None => c_ret (CConversionStuck t s)
              end
            else if both_delta && unfold_left && unfold_right && (left_nat && negb right_nat) then
              sd <-- c_unfold ps s ;;
              match sd with
              | Some e =>
                  sn <-- cm_whnf_core rec true g e ;;
                  c_lazy_delta rounds rec fuel ps g t sn
              | None => c_ret (CConversionStuck t s)
              end
            else
            let eligible := pair_probe_guard left_nat right_nat
              (fun _ => c_nat_probe_allowed (cm_mode rec) t s) in
            tn <-- (if unfold_left && eligible then c_reduce_nat rec fuel g t else c_ret None) ;;
            match tn with
            | Some tn => ok <-- cm_defeq rec g tn s ;; c_ret (CConversionDone ok)
            | None =>
              sn <-- (if unfold_right && eligible then c_reduce_nat rec fuel g s else c_ret None) ;;
              match sn with
              | Some sn => ok <-- cm_defeq rec g t sn ;; c_ret (CConversionDone ok)
              | None =>
              nat_t <-- c_pure (c_reduce_native t) ;;
              match nat_t with
              | Some tn => ok <-- cm_defeq rec g tn s ;; c_ret (CConversionDone ok)
              | None =>
              nat_s <-- c_pure (c_reduce_native s) ;;
              match nat_s with
              | Some sn => ok <-- cm_defeq rec g t sn ;; c_ret (CConversionDone ok)
              | None =>
                td <-- (if unfold_left then c_unfold ps t else c_ret None) ;;
                sd <-- (if unfold_right then c_unfold ps s else c_ret None) ;;
                match td, sd with
                | None, None => c_ret (CConversionStuck t s)
                | _, _ =>
                  tn <-- match td with Some e => cm_whnf_core rec true g e | None => c_ret t end ;;
                  sn <-- match sd with Some e => cm_whnf_core rec true g e | None => c_ret s end ;;
                  c_lazy_delta rounds rec fuel ps g tn sn
                end
              end
              end
              end
            end
          end
        end
      end
  end.

Fixpoint c_lazy_delta_proj (rounds : nat) (rec : c_methods) (fuel : nat)
    (ps : list name) (g : c_context) (idx : nat) (t s : cexpr) : c_act bool :=
  match rounds with
  | 0 => c_pure (Decline OutOfFuel)
  | S rounds =>
      quick <-- c_quick rec fuel g t s ;;
      match quick with
      | Some ok => c_ret ok
      | None =>
        same <-- c_delta_congruent rec fuel g t s ;;
        if same then c_ret true else
        projected <-- c_opposite_projection rec g t s ;;
        match projected with
        | Some (tn, sn) => c_lazy_delta_proj rounds rec fuel ps g idx tn sn
        | None =>
          let '(unfold_left, unfold_right) := c_delta_sides t s in
          td <-- (if unfold_left then c_unfold ps t else c_ret None) ;;
          sd <-- (if unfold_right then c_unfold ps s else c_ret None) ;;
          match td, sd with
          | None, None =>
              match c_reduce_proj_core idx t, c_reduce_proj_core idx s with
              | Some tf, Some sf => cm_defeq rec g tf sf
              | _, _ => cm_defeq rec g t s
              end
          | _, _ =>
              tn <-- match td with Some e => cm_whnf_core rec true g e | None => c_ret t end ;;
              sn <-- match sd with Some e => cm_whnf_core rec true g e | None => c_ret s end ;;
              c_lazy_delta_proj rounds rec fuel ps g idx tn sn
          end
        end
      end
  end.

Definition c_finish_conversion (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (t s : cexpr) : c_act bool :=
  let '(th, ta) := c_spine t [] in
  let '(sh, sa) := c_spine s [] in
  lazy_proj_ok <--
    match th, sh with
    | CProj _ _ ti te, CProj _ _ si se =>
        if Nat.eqb ti si && Nat.eqb (List.length ta) (List.length sa) then
          ok <-- c_lazy_delta_proj (fc_lazy_delta cfg) rec fuel ps g ti te se ;;
          if ok then
            match ta with
            | [] => c_ret true
            | _ => c_compare_args_cheap_first rec g ta sa
            end
          else c_ret false
        else c_ret false
    | _, _ => c_ret false
    end ;;
  if lazy_proj_ok then c_ret true else
  let project := fun e => let '(head, args) := c_spine e [] in match head with
    | CProj _ owner index value =>
        field <-- c_reduce_projection_with rec (cm_whnf rec) g owner index value ;;
        c_ret (option_map (fun f => c_apps f args) field)
    | _ => c_ret None end in
  tp <-- project t ;; sp <-- project s ;;
  match tp, sp with
  | Some t, Some s => cm_defeq rec g t s
  | Some t, None => cm_defeq rec g t s
  | None, Some s => cm_defeq rec g t s
  | None, None => c_compare_after_whnf rec fuel g t s
  end.

Definition c_true_shortcut (rec : c_methods) (g : c_context) (t s : cexpr) : c_act bool :=
  if c_is_true s && c_true_probe_allowed (cm_mode rec) t && bool_ready
  then tn <-- cm_whnf rec g t ;; c_ret (c_is_true tn)
  else c_ret false.

Definition c_defeq_step (rec : c_methods) (fuel : nat) (ps : list name)
    (g : c_context) (t s : cexpr) : c_act bool :=
  fun st =>
    if fst (c_alpha 2048 t s) then (Accept true, st)
    else
      let rec := cm_inference_only rec in
      let work : c_act bool :=
        quick <-- c_quick rec fuel g t s ;;
        match quick with
        | Some ok => c_ret ok
        | None =>
          shortcut <-- c_true_shortcut rec g t s ;;
          if shortcut then c_ret true else
          irrelevant <-- c_proof_irrel rec fuel g t s ;;
          match irrelevant with
          | Some ok => c_ret ok
          | None =>
            tn <-- cm_whnf_core rec true g t ;;
            sn <-- cm_whnf_core rec true g s ;;
            progress <-- c_lazy_delta (fc_lazy_delta cfg) rec fuel ps g tn sn ;;
            match progress with
            | CConversionDone ok => c_ret ok
            | CConversionStuck tn sn => c_finish_conversion rec fuel ps g tn sn
            end
          end
        end in
      if c_is_trivial_defeq_expr t && c_is_trivial_defeq_expr s then work st
      else
        let cid := cc_id g in
        let '(h1, h2, hpair) := c_defeq_hashes cid t s in
        match c_defeq_find_h h1 h2 hpair cid t s st with
        | Some v => (Accept v, st)
        | None =>
            let '(res, st') := work st in
            match res with
            | Accept v => (Accept v, c_defeq_put_h h1 h2 hpair cid t s v st')
            | other => (other, st')
            end
        end.

Fixpoint c_checker_mode (mode : reduction_mode) (fuel : nat) (ps : list name)
    {struct fuel} : c_methods :=
  match fuel with
  | 0 => {| cm_infer       := fun _ _ => c_pure (Decline OutOfFuel);
            cm_infer_type  := fun _ _ => c_pure (Decline OutOfFuel);
            cm_whnf        := fun _ _ => c_pure (Decline OutOfFuel);
            cm_whnf_core   := fun _ _ _ => c_pure (Decline OutOfFuel);
            cm_defeq       := fun _ _ _ => c_pure (Decline OutOfFuel);
            cm_mode        := mode;
            cm_eager_defeq := fun _ _ _ => c_pure (Decline OutOfFuel) |}
  | S n =>
      let whnf_rounds :=
        match mode with NormalReduction => fc_whnf cfg | EagerReduction => fc_whnf_eager cfg end in
      {| cm_infer := fun g e =>
           let rec := c_checker_mode mode n ps in c_infer_step rec n ps true g e;
         cm_infer_type := fun g e =>
           let rec := c_checker_mode mode n ps in c_infer_step rec n ps false g e;
         cm_whnf := fun g e =>
           let rec := c_checker_mode mode n ps in c_whnf_loop whnf_rounds rec n ps g e;
         cm_whnf_core := fun cheap g e =>
           let rec := c_checker_mode mode n ps in c_whnf_core_step rec n ps cheap g e;
         cm_defeq := fun g t s =>
           let rec := c_checker_mode mode n ps in c_defeq_step rec n ps g t s;
         cm_mode := mode;
         cm_eager_defeq := fun g t s =>
           let rec := c_checker_mode EagerReduction n ps in c_defeq_step rec n ps g t s |}
  end.

Definition c_checker (ps : list name) : c_methods :=
  c_checker_mode NormalReduction (fc_rec_depth cfg) ps.

(* ========================================================================= *)
(* 5. Canonical Path-Trie DAG Inference (O(N log N) on Huge DAGs)            *)
(* ========================================================================= *)

Record path_trie : Type := {
  pt_edges : PositiveMap.t (list (positive * option positive * c_context))
}.

Definition empty_path_trie : path_trie := {|
  pt_edges := PositiveMap.empty _
|}.

Fixpoint pt_find_edge (ty_id : positive) (val_id : option positive)
    (xs : list (positive * option positive * c_context)) : option c_context :=
  match xs with
  | [] => None
  | (t', v', gb) :: rest =>
      if Pos.eqb ty_id t' && value_key_eqb val_id v' then Some gb
      else pt_find_edge ty_id val_id rest
  end.

Record dag_infer_state : Type := {
  dis_trie      : path_trie;
  dis_checked   : PositiveMap.t (PositiveMap.t cexpr);
  dis_unchecked : PositiveMap.t (PositiveMap.t cexpr);
  dis_cs        : checker_state
}.

Definition empty_dag_infer_state (cs : checker_state) : dag_infer_state := {|
  dis_trie      := empty_path_trie;
  dis_checked   := PositiveMap.empty _;
  dis_unchecked := PositiveMap.empty _;
  dis_cs        := cs
|}.

Definition dis_find (checking : bool) (id cid : positive) (ds : dag_infer_state)
    : option cexpr :=
  let tbl := if checking then dis_checked ds else dis_unchecked ds in
  match PositiveMap.find id tbl with
  | Some m => PositiveMap.find cid m
  | None => None
  end.

Definition dis_put (checking : bool) (id cid : positive) (ty : cexpr) (ds : dag_infer_state)
    : dag_infer_state :=
  let tbl := if checking then dis_checked ds else dis_unchecked ds in
  let inner := match PositiveMap.find id tbl with Some m => m | None => PositiveMap.empty _ end in
  let tbl' := PositiveMap.add id (PositiveMap.add cid ty inner) tbl in
  if checking then
    {| dis_trie := dis_trie ds; dis_checked := tbl';
       dis_unchecked := dis_unchecked ds; dis_cs := dis_cs ds |}
  else
    {| dis_trie := dis_trie ds; dis_checked := dis_checked ds;
       dis_unchecked := tbl'; dis_cs := dis_cs ds |}.

Definition d_act (A : Type) := dag_infer_state -> result A * dag_infer_state.
Definition d_ret {A} (x : A) : d_act A := fun ds => (Accept x, ds).
Definition d_pure {A} (r : result A) : d_act A := fun ds => (r, ds).
Definition d_lift {A} (m : c_act A) : d_act A :=
  fun ds =>
    let '(r, cs') := m (dis_cs ds) in
    (r, {| dis_trie := dis_trie ds; dis_checked := dis_checked ds;
           dis_unchecked := dis_unchecked ds; dis_cs := cs' |}).
Definition d_bind {A B} (m : d_act A) (f : A -> d_act B) : d_act B :=
  fun ds =>
    let '(r, ds') := m ds in
    match r with
    | Accept x => f x ds'
    | Reject err => (Reject err, ds')
    | Decline why => (Decline why, ds')
    end.

Notation "x <~ a ;; b" := (d_bind a (fun x => b))
  (at level 100, a at next level, right associativity).

Definition d_push_binding (g : c_context) (ty_id : positive) (ty : cexpr)
    (val_id : option positive) (val : option cexpr) : d_act c_context :=
  fun ds =>
    let pid := cc_id g in
    let edges := match PositiveMap.find pid (pt_edges (dis_trie ds)) with Some xs => xs | None => [] end in
    match pt_find_edge ty_id val_id edges with
    | Some gb => (Accept gb, ds)
    | None =>
        let '(res, cs') := c_push_binding g ty val (dis_cs ds) in
        match res with
        | Accept gb =>
            let pt' := {| pt_edges := PositiveMap.add pid ((ty_id, val_id, gb) :: edges)
                                        (pt_edges (dis_trie ds)) |} in
            (Accept gb,
             {| dis_trie := pt'; dis_checked := dis_checked ds;
                dis_unchecked := dis_unchecked ds; dis_cs := cs' |})
        | Reject err =>
            (Reject err,
             {| dis_trie := dis_trie ds; dis_checked := dis_checked ds;
                dis_unchecked := dis_unchecked ds; dis_cs := cs' |})
        | Decline why =>
            (Decline why,
             {| dis_trie := dis_trie ds; dis_checked := dis_checked ds;
                dis_unchecked := dis_unchecked ds; dis_cs := cs' |})
        end
    end.

Fixpoint c_dag_infer (budget : nat) (rec : c_methods) (fuel : nat) (ps : list name)
    (arena : dag_arena) (carena : c_arena_table) (checking : bool)
    (id : positive) (g : c_context) : d_act cexpr :=
  fun ds =>
    let cid := cc_id g in
    match dis_find checking id cid ds with
    | Some ty => (Accept ty, ds)
    | None =>
        let work : d_act cexpr :=
          match budget with
          | 0 =>
              ce <~ d_pure (c_arena_ref carena id) ;;
              d_lift (c_infer_step rec fuel ps checking g ce)
          | S budget =>
              ce <~ d_pure (c_arena_ref carena id) ;;
              match PositiveMap.find id (arena_nodes arena) with
              | Some (DApp f a) =>
                  ae <~ d_pure (c_arena_ref carena a) ;;
                  ft <~ c_dag_infer budget rec fuel ps arena carena checking f g ;;
                  ft <~ d_lift (cm_whnf rec g ft) ;;
                  match ft with
                  | CPi _ _ _ domain body =>
                      _ <~ (if checking then
                        at_ <~ c_dag_infer budget rec fuel ps arena carena true a g ;;
                        ok <~ d_lift (cm_app_type_defeq rec g ae domain at_) ;;
                        d_pure (require ok TypeMismatch)
                        else d_ret tt) ;;
                      d_ret (c_instantiate body ae)
                  | _ => d_pure (Reject ExpectedPi)
                  end
              | Some (DLam n bi a b) =>
                  ae <~ d_pure (c_arena_ref carena a) ;;
                  _ <~ (if checking then
                    dt <~ c_dag_infer budget rec fuel ps arena carena true a g ;;
                    dt <~ d_lift (cm_whnf rec g dt) ;;
                    match dt with CSort _ _ => d_ret tt | _ => d_pure (Reject ExpectedSort) end
                    else d_ret tt) ;;
                  gb <~ d_push_binding g a ae None None ;;
                  bt <~ c_dag_infer budget rec fuel ps arena carena checking b gb ;;
                  d_ret (mk_cpi n bi ae bt)
              | Some (DPi n bi a b) =>
                  ae <~ d_pure (c_arena_ref carena a) ;;
                  dt <~ c_dag_infer budget rec fuel ps arena carena checking a g ;;
                  dt <~ d_lift (cm_whnf rec g dt) ;;
                  u <~ match dt with CSort _ u => d_ret u | _ => d_pure (Reject ExpectedSort) end ;;
                  gb <~ d_push_binding g a ae None None ;;
                  bt <~ c_dag_infer budget rec fuel ps arena carena checking b gb ;;
                  bt <~ d_lift (cm_whnf rec gb bt) ;;
                  v <~ match bt with CSort _ v => d_ret v | _ => d_pure (Reject ExpectedSort) end ;;
                  d_ret (mk_csort (LIMax u v))
              | Some (DLet n a v b nd) =>
                  ae <~ d_pure (c_arena_ref carena a) ;;
                  ve <~ d_pure (c_arena_ref carena v) ;;
                  _ <~ (if checking then
                    dt <~ c_dag_infer budget rec fuel ps arena carena true a g ;;
                    dt <~ d_lift (cm_whnf rec g dt) ;;
                    _ <~ match dt with CSort _ _ => d_ret tt | _ => d_pure (Reject ExpectedSort) end ;;
                    vt <~ c_dag_infer budget rec fuel ps arena carena true v g ;;
                    ok <~ d_lift (cm_defeq rec g vt ae) ;;
                    d_pure (require ok TypeMismatch)
                    else d_ret tt) ;;
                  gb <~ d_push_binding g a ae (Some v) (Some ve) ;;
                  bt <~ c_dag_infer budget rec fuel ps arena carena checking b gb ;;
                  d_ret (c_instantiate bt ve)
              | Some (DMData a) =>
                  c_dag_infer budget rec fuel ps arena carena checking a g
              | _ =>
                  d_lift (c_infer_step rec fuel ps checking g ce)
              end
          end in
        let '(res, ds') := work ds in
        match res with
        | Accept ty => (Accept ty, dis_put checking id cid ty ds')
        | other => (other, ds')
        end
    end.

Definition c_run_dag_infer (budget : nat) (ps : list name)
    (arena : dag_arena) (carena : c_arena_table) (root : positive) : c_act cexpr :=
  fun cs =>
    match fc_rec_depth cfg with
    | 0 => (Decline OutOfFuel, cs)
    | S n =>
        let rec := c_checker_mode NormalReduction n ps in
        let '(res, ds') :=
          c_dag_infer budget rec n ps arena carena true root empty_c_context
            (empty_dag_infer_state cs) in
        (res, dis_cs ds')
    end.

Definition c_whnf_top (ps : list name) (g : c_context) (e : cexpr) : c_act cexpr :=
  match fc_rec_depth cfg with
  | 0 => c_pure (Decline OutOfFuel)
  | S _ =>
      if ce_supp e then cm_whnf (c_checker ps) g e
      else c_pure (Decline UnsupportedExpression)
  end.

Definition c_defeq_top (ps : list name) (g : c_context) (t s : cexpr) : c_act bool :=
  match fc_rec_depth cfg with
  | 0 => c_pure (Decline OutOfFuel)
  | S _ =>
      if ce_supp t && ce_supp s then cm_defeq (c_checker ps) g t s
      else c_pure (Decline UnsupportedExpression)
  end.

(* ========================================================================= *)
(* 6. Cached DAG & Batch Admission                                           *)
(* ========================================================================= *)

Definition c_input_header (budget : nat) (n : name) (ps : list name)
    (arena : dag_arena) (carena : c_arena_table) (root : positive)
    (entry : scope_entry) : c_act unit :=
  match lookup n with
  | Some _ => c_pure (Reject DuplicateDeclaration)
  | None =>
      if negb (names_unique ps) then c_pure (Reject DuplicateUniverse) else
      if negb (N.leb (scope_need entry) 0%N) then c_pure (Reject MalformedDeclaration) else
      inferred <-- c_run_dag_infer budget ps arena carena root ;;
      reduced <-- c_whnf_top ps empty_c_context inferred ;;
      match reduced with CSort _ _ => c_ret tt | _ => c_pure (Reject ExpectedSort) end
  end.

Definition c_input_check (budget : nat) (ps : list name)
    (arena : dag_arena) (carena : c_arena_table) (tr br : positive) (ty_c : cexpr)
    : c_act unit :=
  type_type <-- c_run_dag_infer budget ps arena carena tr ;;
  type_type <-- cm_whnf (c_checker ps) empty_c_context type_type ;;
  _ <-- match type_type with CSort _ u => c_ret u | _ => c_pure (Reject ExpectedSort) end ;;
  body_type <-- c_run_dag_infer budget ps arena carena br ;;
  ok <-- c_defeq_top ps empty_c_context body_type ty_c ;;
  c_pure (require ok TypeMismatch).

Definition c_input_proposition (budget : nat) (ps : list name)
    (arena : dag_arena) (carena : c_arena_table) (root : positive) : c_act unit :=
  inferred <-- c_run_dag_infer budget ps arena carena root ;;
  reduced <-- c_whnf_top ps empty_c_context inferred ;;
  match reduced with
  | CSort _ u =>
      is_zero <-- c_pure (level_equiv (fc_rec_depth cfg) u LZero) ;;
      if is_zero then c_ret tt else c_pure (Reject MalformedDeclaration)
  | _ => c_pure (Reject ExpectedSort)
  end.

Definition c_admit_dag_delta (kind : dag_admission_kind) (budget : nat)
    (n : name) (ps : list name) (rows : list (positive * dag_node))
    (tr br : positive) : result environment :=
  match fc_rec_depth cfg with
  | 0 => Decline OutOfFuel
  | S _ =>
      arena <- arena_build empty_arena rows ;;
      carena <- c_arena_build nat_ready str_ready (PositiveMap.empty _) rows ;;
      ty <- scope_ref (arena_scope arena) tr ;;
      body <- scope_ref (arena_scope arena) br ;;
      ty_c <- c_arena_ref carena tr ;;
      let act : c_act declaration :=
        match kind with
        | DagDefinition hints =>
            _ <-- c_input_header budget n ps arena carena tr ty ;;
            _ <-- c_pure (require (N.leb (scope_need body) 0%N) MalformedDeclaration) ;;
            _ <-- c_input_check budget ps arena carena tr br ty_c ;;
            primitive <-- c_pure (classify_primitive (fc_rec_depth cfg) env n ps
                                    (scope_expr ty) (scope_expr body)) ;;
            let dk := match primitive with Some p => DPrimitive p | None => DDefinition end in
            c_ret {| decl_hints := hints; decl_name := n; decl_params := ps;
                     decl_type := scope_expr ty; decl_value := Some (scope_expr body);
                     decl_kind_of := dk |}
        | DagTheorem =>
            if name_mem n reserved_names then c_pure (Reject MalformedDeclaration) else
            _ <-- c_input_header budget n ps arena carena tr ty ;;
            _ <-- c_input_proposition budget ps arena carena tr ;;
            _ <-- (if N.leb (scope_need body) 0%N
                   then c_input_check budget ps arena carena tr br ty_c
                   else c_pure (Reject MalformedDeclaration)) ;;
            c_ret {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
                     decl_type := scope_expr ty; decl_value := Some (scope_expr body);
                     decl_kind_of := DTheorem |}
        | DagOpaque =>
            if name_mem n reserved_names then c_pure (Reject MalformedDeclaration) else
            _ <-- c_input_header budget n ps arena carena tr ty ;;
            _ <-- (if N.leb (scope_need body) 0%N
                   then c_input_check budget ps arena carena tr br ty_c
                   else c_pure (Reject MalformedDeclaration)) ;;
            c_ret {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
                     decl_type := scope_expr ty; decl_value := Some (scope_expr body);
                     decl_kind_of := DOpaque |}
        end in
      d <- fst (act empty_checker_state) ;;
      Accept [d]
  end.

End CachedKernel.

(* ========================================================================= *)
(* 7. Public Runtime Entry Points & Machine-Verified Soundness Properties    *)
(* ========================================================================= *)

Definition cached_batch_delta (cfg : fuel_config) (s : runtime_state)
    (request : admission_batch) : result environment :=
  if fuel_config_nonzero cfg then
    let env := state_environment s in
    match request with
    | BatchDag kind budget n ps rows tr br =>
        let lk := state_lookup s in
        let res := fun nm (_ : environment) => lk nm in
        let nat_r := Accessor.core_nat_ready res env in
        let str_r := Accessor.core_string_ready res env in
        let bool_r := Accessor.core_bool_ready res env in
        c_admit_dag_delta lk cfg env nat_r str_r bool_r kind budget n ps rows tr br
    | BatchOrdinary input =>
        single_delta (admit_extended (fc_rec_depth cfg) env input)
    | BatchQuotient n ps ty kind =>
        single_delta (admit_quotient (fc_rec_depth cfg) env n ps ty kind)
    | BatchInductive types ctors recs =>
        inductive_delta (fc_rec_depth cfg) env types ctors recs
    | BatchMutual inputs =>
        mutual_delta (fc_rec_depth cfg) env inputs
    end
  else Decline OutOfFuel.

Definition admit_batch_cached (cfg : fuel_config) (s : runtime_state)
    (request : admission_batch) : result runtime_state :=
  added <- cached_batch_delta cfg s request ;;
  Accept (extend_state s added).

Definition cached_transaction (cfg : fuel_config) (s : runtime_state)
    (request : admission_batch) : runtime_state * result unit :=
  match admit_batch_cached cfg s request with
  | Accept next => (next, Accept tt)
  | Reject reason => (s, Reject reason)
  | Decline reason => (s, Decline reason)
  end.

(* Soundness of O(1) looseBVarRange short-circuiting *)
Lemma lift_noop_when_scoped e : forall amount cutoff,
  required_depth e <= cutoff -> lift amount cutoff e = e.
Proof.
  induction e; intros amount cutoff H; simpl in *; try reflexivity.
  - destruct (cutoff <=? n) eqn:Hle; [apply Nat.leb_le in Hle; lia | reflexivity].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2, IHe3; [reflexivity | lia | lia | lia].
  - rewrite IHe; [reflexivity | exact H].
  - rewrite IHe; [reflexivity | exact H].
Qed.

Lemma subst_noop_when_scoped e : forall index value,
  required_depth e <= index -> subst index value e = e.
Proof.
  induction e; intros index value H; simpl in *; try reflexivity.
  - destruct (Nat.eqb n index) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|].
    destruct (index <? n) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia | reflexivity].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2, IHe3; [reflexivity | lia | lia | lia].
  - rewrite IHe; [reflexivity | exact H].
  - rewrite IHe; [reflexivity | exact H].
Qed.

Lemma subst_many_noop_when_scoped e : forall index values,
  required_depth e <= index -> subst_many index values e = e.
Proof.
  induction e; intros index values H; simpl in *; try reflexivity.
  - destruct (n <? index) eqn:Hlt; [reflexivity | apply Nat.ltb_ge in Hlt; lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2; [reflexivity | lia | lia].
  - rewrite IHe1, IHe2, IHe3; [reflexivity | lia | lia | lia].
  - rewrite IHe; [reflexivity | exact H].
  - rewrite IHe; [reflexivity | exact H].
Qed.

Fixpoint c_lbr_wf (e : cexpr) : Prop :=
  ce_lbr e = required_depth (c_erase e) /\
  match e with
  | CApp _ f a | CLam _ _ _ f a | CPi _ _ _ f a => c_lbr_wf f /\ c_lbr_wf a
  | CLet _ _ t v b _ => c_lbr_wf t /\ c_lbr_wf v /\ c_lbr_wf b
  | CProj _ _ _ a | CMData _ a => c_lbr_wf a
  | _ => True
  end.

Lemma c_lbr_wf_eq {e} : c_lbr_wf e -> cm_lbr (c_meta e) = required_depth (c_erase e).
Proof. destruct e; simpl; intros [H _]; exact H. Qed.

Lemma cm_lbr_mk_cmeta lbr hfv supp : cm_lbr (mk_cmeta lbr hfv supp) = lbr.
Proof. destruct lbr, hfv, supp; reflexivity. Qed.

Lemma c_erase_of_expr nat_r str_r e :
  c_erase (c_of_expr nat_r str_r e) = e /\ c_lbr_wf (c_of_expr nat_r str_r e).
Proof.
  induction e; simpl;
    try (split; [reflexivity | split; [reflexivity | exact I]]).
  - destruct IHe1 as [E1 W1], IHe2 as [E2 W2].
    split; [simpl; now rewrite E1, E2|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1), (c_lbr_wf_eq W2); reflexivity | split; assumption].
  - destruct IHe1 as [E1 W1], IHe2 as [E2 W2].
    split; [simpl; now rewrite E1, E2|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1), (c_lbr_wf_eq W2); reflexivity | split; assumption].
  - destruct IHe1 as [E1 W1], IHe2 as [E2 W2].
    split; [simpl; now rewrite E1, E2|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1), (c_lbr_wf_eq W2); reflexivity | split; assumption].
  - destruct IHe1 as [E1 W1], IHe2 as [E2 W2], IHe3 as [E3 W3].
    split; [simpl; now rewrite E1, E2, E3|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1), (c_lbr_wf_eq W2), (c_lbr_wf_eq W3); reflexivity | repeat split; assumption].
  - split; [reflexivity | split; [unfold ce_lbr, mk_clit; destruct l; [destruct nat_r | destruct str_r; try destruct (core_utf8 _)]; reflexivity | exact I]].
  - destruct IHe as [E1 W1].
    split; [simpl; now rewrite E1|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1); reflexivity | assumption].
  - destruct IHe as [E1 W1].
    split; [simpl; now rewrite E1|].
    split; [unfold ce_lbr; simpl; rewrite cm_lbr_mk_cmeta, (c_lbr_wf_eq W1); reflexivity | assumption].
Qed.

Lemma c_erase_lift_go e : forall amount cutoff,
  c_lbr_wf e -> c_erase (c_lift_go amount cutoff e) = lift amount cutoff (c_erase e).
Proof.
  induction e; intros amount cutoff [Hlbr Hsub]; cbn [c_lift_go];
    destruct (ce_lbr _ <=? cutoff) eqn:Hle;
    try (apply Nat.leb_le in Hle; rewrite Hlbr in Hle;
         symmetry; apply lift_noop_when_scoped; exact Hle).
  - simpl. destruct (cutoff <=? n); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct Hsub as [Hf Ha]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Hd Hb]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Hd Hb]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Ht [Hv Hb]]. simpl. rewrite IHe1, IHe2, IHe3; auto.
  - simpl. rewrite IHe; auto.
  - simpl. rewrite IHe; auto.
  - reflexivity.
Qed.

Lemma c_erase_lift e amount cutoff :
  c_lbr_wf e -> c_erase (c_lift amount cutoff e) = lift amount cutoff (c_erase e).
Proof.
  intro Hw. destruct amount as [|amount].
  - simpl. set (x := c_erase e). clearbody x. revert cutoff.
    induction x; intro c; simpl;
      try reflexivity;
      try (destruct (c <=? n); reflexivity);
      try (rewrite <- IHx1, <- IHx2; reflexivity);
      try (rewrite <- IHx1, <- IHx2, <- IHx3; reflexivity);
      try (rewrite <- IHx; reflexivity).
  - apply c_erase_lift_go; exact Hw.
Qed.

Lemma c_erase_subst e : forall index value,
  c_lbr_wf e -> c_lbr_wf value ->
  c_erase (c_subst index value e) = subst index (c_erase value) (c_erase e).
Proof.
  induction e; intros index value [Hlbr Hsub] Hval; cbn [c_subst];
    destruct (ce_lbr _ <=? index) eqn:Hle;
    try (apply Nat.leb_le in Hle; rewrite Hlbr in Hle;
         symmetry; apply subst_noop_when_scoped; exact Hle).
  - simpl. destruct (Nat.eqb n index).
    + destruct index; [reflexivity | apply c_erase_lift; exact Hval].
    + destruct (index <? n); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct Hsub as [Hf Ha]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Hd Hb]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Hd Hb]. simpl. rewrite IHe1, IHe2; auto.
  - destruct Hsub as [Ht [Hv Hb]]. simpl. rewrite IHe1, IHe2, IHe3; auto.
  - simpl. rewrite IHe; auto.
  - simpl. rewrite IHe; auto.
  - reflexivity.
Qed.

(* Soundness of DAG-identity + hash-guarded c_alpha *)
Fixpoint c_dag_wf (amap : positive -> option expr) (e : cexpr) : Prop :=
  (forall id, ce_dag e = Some id -> amap id = Some (c_erase e)) /\
  match e with
  | CApp _ f a | CLam _ _ _ f a | CPi _ _ _ f a => c_dag_wf amap f /\ c_dag_wf amap a
  | CLet _ _ t v b _ => c_dag_wf amap t /\ c_dag_wf amap v /\ c_dag_wf amap b
  | CProj _ _ _ a | CMData _ a => c_dag_wf amap a
  | _ => True
  end.

Lemma level_eqb_refl_local u : level_eqb u u = true.
Proof.
  induction u; simpl; rewrite ?name_eqb_refl, ?IHu, ?IHu1, ?IHu2; reflexivity.
Qed.

Lemma expr_eqb_refl_local e : expr_eqb e e = true.
Proof.
  induction e; simpl;
    rewrite ?Nat.eqb_refl, ?name_eqb_refl, ?level_eqb_refl_local, ?IHe, ?IHe1, ?IHe2, ?IHe3;
    try reflexivity.
  - induction l; simpl; [reflexivity | rewrite level_eqb_refl_local, IHl; reflexivity].
  - destruct l; simpl; [apply N.eqb_refl | apply String.eqb_refl].
Qed.

Lemma c_dag_wf_eq {amap e} :
  c_dag_wf amap e -> forall id, ce_dag e = Some id -> amap id = Some (c_erase e).
Proof. destruct e; simpl; intros [H _]; exact H. Qed.

Lemma c_dag_same_sound amap t s :
  c_dag_wf amap t -> c_dag_wf amap s ->
  c_dag_same t s = true ->
  expr_eqb (c_erase t) (c_erase s) = true.
Proof.
  intros Hdt Hds H. unfold c_dag_same in H.
  destruct (ce_dag t) as [id1|] eqn:E1; [|discriminate].
  destruct (ce_dag s) as [id2|] eqn:E2; [|discriminate].
  apply Pos.eqb_eq in H. subst id2.
  pose proof (c_dag_wf_eq Hdt E1) as H1.
  pose proof (c_dag_wf_eq Hds E2) as H2.
  rewrite H1 in H2. inversion H2 as [Eeq]. rewrite Eeq.
  apply expr_eqb_refl_local.
Qed.

Lemma c_alpha_sound amap t : forall budget s rem,
  c_dag_wf amap t -> c_dag_wf amap s ->
  c_alpha budget t s = (true, rem) ->
  expr_eqb (c_erase t) (c_erase s) = true.
Proof.
  induction t; intros budget s rem Hdt Hds H;
    cbn [c_alpha] in H;
    (destruct (c_dag_same _ s) eqn:Edag;
     [eapply c_dag_same_sound; eauto |]);
    destruct budget as [|budget]; try discriminate;
    destruct s; try discriminate;
    destruct Hdt as [_ Hsubt]; destruct Hds as [_ Hsubs];
    simpl in *;
    repeat match type of H with
    | c_alpha _ _ _ = _ => fail 1
    | context [if (name_eqb ?n ?m && Nat.eqb ?i ?j) then _ else _] =>
        let E := fresh "Ec" in destruct (name_eqb n m && Nat.eqb i j) eqn:E; try discriminate
    | context [c_alpha ?b ?x ?y] =>
        let E := fresh "Ea" in let ok := fresh "ok" in let r := fresh "r" in
        destruct (c_alpha b x y) as [ok r] eqn:E;
        destruct ok; simpl in H; try discriminate
    end;
    repeat match goal with
    | H1 : (_ && _)%bool = true |- _ => apply andb_true_iff in H1; destruct H1
    | H1 : _ /\ _ |- _ => destruct H1
    end;
    try (injection H as H1 _; exact H1);
    try (injection H as H1 _; apply andb_true_iff in H1; destruct H1; rewrite !andb_true_iff; auto);
    try (eapply IHt; eauto);
    try (rewrite !andb_true_iff; repeat split; try assumption; eauto).
Qed.

Theorem admit_batch_cached_zero_min_declines cfg s request :
  min_fuel_of_config cfg = 0 ->
  admit_batch_cached cfg s request = Decline OutOfFuel.
Proof.
  intros H0.
  apply (proj2 (fuel_config_nonzero_false_iff cfg)) in H0.
  unfold admit_batch_cached, cached_batch_delta. rewrite H0. reflexivity.
Qed.

Theorem cached_transaction_reject_rolls_back cfg s request reason :
  admit_batch_cached cfg s request = Reject reason ->
  cached_transaction cfg s request = (s, Reject reason).
Proof. intro H. unfold cached_transaction. now rewrite H. Qed.

Theorem cached_transaction_decline_rolls_back cfg s request reason :
  admit_batch_cached cfg s request = Decline reason ->
  cached_transaction cfg s request = (s, Decline reason).
Proof. intro H. unfold cached_transaction. now rewrite H. Qed.

Print Assumptions c_erase_of_expr.
Print Assumptions c_erase_lift.
Print Assumptions c_erase_subst.
Print Assumptions c_alpha_sound.
Print Assumptions admit_batch_cached_zero_min_declines.
Print Assumptions cached_transaction_reject_rolls_back.
Print Assumptions cached_transaction_decline_rolls_back.
