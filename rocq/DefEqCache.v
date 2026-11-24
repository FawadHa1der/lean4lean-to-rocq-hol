(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Full-context hash-bucketed positive/negative definitional-equality cache and
   pure-Gallina union-find EquivManager (Lean4Lean/EquivManager.lean).
   Every cache key compares the ENTIRE bound context (binder types and let
   values) and ENTIRE free context (names, types, and let values), so
   same-depth inequivalent contexts can never alias. *)
From Stdlib Require Import List Bool Arith PeanoNat NArith PArith.BinPos String Ascii
  FSets.FMapAVL FSets.FMapPositive FSets.FMapFacts Structures.OrderedTypeEx.
From LeanPort Require Import Syntax Checker SemanticModel DeclarativeTyping.
Import ListNotations.
Set Implicit Arguments.

Module CacheMap := PositiveMap.
Module CacheMapFacts := FMapFacts.WFacts(CacheMap).
Module PosMapFacts := FMapFacts.WFacts(PositiveMap).

(* ========================================================================= *)
(* 1. Exact & Bounded Full-Context Equality                                  *)
(* ========================================================================= *)

Definition option_expr_eqb (a b : option expr) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => expr_eqb x y
  | _, _ => false
  end.

Definition binding_eqb (b1 b2 : binding) : bool :=
  expr_eqb (binding_type b1) (binding_type b2) &&
  option_expr_eqb (binding_value b1) (binding_value b2).

Definition free_entry_eqb (p1 p2 : name * binding) : bool :=
  name_eqb (fst p1) (fst p2) && binding_eqb (snd p1) (snd p2).

Definition context_eqb (g1 g2 : context) : bool :=
  list_eqb binding_eqb (bound_context g1) (bound_context g2) &&
  list_eqb free_entry_eqb (free_context g1) (free_context g2).

(* Bounded-budget alpha equality for contexts: O(1) worst case on huge DAGs,
   and whenever it returns true it implies exact context_eqb = true. *)
Definition core_alpha_opt (budget : nat) (a b : option expr) : bool * nat :=
  match a, b with
  | None, None => (true, budget)
  | Some x, Some y => core_alpha budget x y
  | _, _ => (false, budget)
  end.

Definition core_alpha_binding (budget : nat) (b1 b2 : binding) : bool * nat :=
  let '(ok, rem) := core_alpha budget (binding_type b1) (binding_type b2) in
  if ok then core_alpha_opt rem (binding_value b1) (binding_value b2)
  else (false, rem).

Fixpoint core_alpha_bindings (budget : nat) (xs ys : list binding) : bool * nat :=
  match xs, ys with
  | [], [] => (true, budget)
  | x :: xs, y :: ys =>
      let '(ok, rem) := core_alpha_binding budget x y in
      if ok then core_alpha_bindings rem xs ys else (false, rem)
  | _, _ => (false, budget)
  end.

Fixpoint core_alpha_free (budget : nat) (xs ys : list (name * binding)) : bool * nat :=
  match xs, ys with
  | [], [] => (true, budget)
  | (n1, b1) :: xs, (n2, b2) :: ys =>
      if name_eqb n1 n2 then
        let '(ok, rem) := core_alpha_binding budget b1 b2 in
        if ok then core_alpha_free rem xs ys else (false, rem)
      else (false, budget)
  | _, _ => (false, budget)
  end.

Definition core_alpha_context (budget : nat) (g1 g2 : context) : bool :=
  let '(ok, rem) := core_alpha_bindings budget (bound_context g1) (bound_context g2) in
  if ok then fst (core_alpha_free rem (free_context g1) (free_context g2))
  else false.

Lemma core_alpha_opt_sound budget a b rem :
  core_alpha_opt budget a b = (true, rem) -> option_expr_eqb a b = true.
Proof.
  destruct a, b; simpl; try discriminate; intro H; [|reflexivity].
  eapply core_alpha_sound. exact H.
Qed.

Lemma core_alpha_binding_sound budget b1 b2 rem :
  core_alpha_binding budget b1 b2 = (true, rem) -> binding_eqb b1 b2 = true.
Proof.
  unfold core_alpha_binding, binding_eqb.
  destruct (core_alpha budget (binding_type b1) (binding_type b2)) as [ok r1] eqn:H1.
  destruct ok; [|discriminate]. intro H2.
  apply andb_true_iff; split; [eapply core_alpha_sound; eauto | eapply core_alpha_opt_sound; eauto].
Qed.

Lemma core_alpha_bindings_sound xs : forall budget ys rem,
  core_alpha_bindings budget xs ys = (true, rem) -> list_eqb binding_eqb xs ys = true.
Proof.
  induction xs as [|x xs IH]; intros budget [|y ys] rem H; simpl in *; try discriminate; [reflexivity|].
  destruct (core_alpha_binding budget x y) as [ok r1] eqn:Hb.
  destruct ok; [|discriminate].
  apply andb_true_iff; split; [eapply core_alpha_binding_sound; eauto | eapply IH; eauto].
Qed.

Lemma core_alpha_free_sound xs : forall budget ys rem,
  core_alpha_free budget xs ys = (true, rem) -> list_eqb free_entry_eqb xs ys = true.
Proof.
  induction xs as [|[n1 b1] xs IH]; intros budget [|[n2 b2] ys] rem H; simpl in *;
    try discriminate; [reflexivity|].
  destruct (name_eqb n1 n2) eqn:Hn; [|discriminate].
  destruct (core_alpha_binding budget b1 b2) as [ok r1] eqn:Hb.
  destruct ok; [|discriminate].
  apply andb_true_iff; split.
  - unfold free_entry_eqb; simpl. rewrite Hn. eapply core_alpha_binding_sound; eauto.
  - eapply IH; eauto.
Qed.

Theorem core_alpha_context_sound budget g1 g2 :
  core_alpha_context budget g1 g2 = true -> context_eqb g1 g2 = true.
Proof.
  unfold core_alpha_context, context_eqb.
  destruct (core_alpha_bindings budget (bound_context g1) (bound_context g2)) as [ok rem] eqn:Hb.
  destruct ok; [|discriminate].
  destruct (core_alpha_free rem (free_context g1) (free_context g2)) as [okf remf] eqn:Hf.
  simpl. intro H; subst okf.
  apply andb_true_iff; split; [eapply core_alpha_bindings_sound; eauto | eapply core_alpha_free_sound; eauto].
Qed.

(* ========================================================================= *)
(* 2. Fast O(1) 16-bit Positive Hashing (Zero Multiplication / Zero Peano)   *)
(* ========================================================================= *)

Fixpoint pos_trunc (k : nat) (p : positive) : positive :=
  match k, p with
  | 0, _ => xH
  | S k, xI q => xI (pos_trunc k q)
  | S k, xO q => xO (pos_trunc k q)
  | S _, xH => xH
  end.

Fixpoint pos_xor_trunc (k : nat) (a b : positive) : positive :=
  match k with
  | 0 => xH
  | S k =>
      match a, b with
      | xI a', xI b' => xO (pos_xor_trunc k a' b')
      | xO a', xO b' => xO (pos_xor_trunc k a' b')
      | xI a', xO b' => xI (pos_xor_trunc k a' b')
      | xO a', xI b' => xI (pos_xor_trunc k a' b')
      | xH, _ => pos_trunc (S k) b
      | _, xH => pos_trunc (S k) a
      end
  end.

(* Shift-left by 1 bit and XOR, capped at 16 bits: <= 16 constructor ops! *)
Definition hash_mix (a b : positive) : positive :=
  pos_xor_trunc 16 (xO a) b.

Definition hash_ascii (c : ascii) : positive :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      let f (b : bool) (p : positive) := if b then xI p else xO p in
      f b0 (f b1 (f b2 (f b3 (f b4 (f b5 (f b6 (f b7 xH)))))))
  end.

Fixpoint hash_string_bounded (fuel : nat) (s : string) (acc : positive) : positive :=
  match fuel, s with
  | 0, _ | _, EmptyString => acc
  | S fuel, String c rest =>
      hash_string_bounded fuel rest (hash_mix acc (hash_ascii c))
  end.

Definition hash_nat_small (n : nat) : positive :=
  match n with
  | 0 => 1%positive
  | 1 => 2%positive
  | 2 => 3%positive
  | 3 => 4%positive
  | 4 => 5%positive
  | 5 => 6%positive
  | 6 => 7%positive
  | 7 => 8%positive
  | _ => pos_trunc 16 (Pos.of_succ_nat n)
  end.

Definition hash_N_fast (n : N) : positive :=
  match n with
  | N0 => 1%positive
  | Npos p => pos_trunc 16 p
  end.

Fixpoint hash_name_bounded (fuel : nat) (n : name) : positive :=
  match fuel, n with
  | 0, _ => 1%positive
  | _, NameAnon => 3%positive
  | S fuel, NameStr p s =>
      hash_mix (hash_name_bounded fuel p) (hash_string_bounded 6 s 7%positive)
  | S fuel, NameNum p k =>
      hash_mix (hash_name_bounded fuel p) (hash_mix 11%positive (hash_N_fast k))
  end.

Fixpoint hash_level_bounded (fuel : nat) (u : level) : positive :=
  match fuel with
  | 0 => 5%positive
  | S fuel =>
      match u with
      | LZero => 13%positive
      | LSucc v => hash_mix 17%positive (hash_level_bounded fuel v)
      | LMax a b => hash_mix 19%positive (hash_mix (hash_level_bounded fuel a) (hash_level_bounded fuel b))
      | LIMax a b => hash_mix 23%positive (hash_mix (hash_level_bounded fuel a) (hash_level_bounded fuel b))
      | LParam n => hash_mix 29%positive (hash_name_bounded 2 n)
      | LMVar n => hash_mix 37%positive (hash_name_bounded 2 n)
      end
  end.

Fixpoint hash_levels_bounded (fuel : nat) (us : list level) (acc : positive) : positive :=
  match fuel, us with
  | 0, _ | _, [] => acc
  | S fuel, u :: us => hash_levels_bounded fuel us (hash_mix acc (hash_level_bounded 2 u))
  end.

Fixpoint hash_expr_bounded (depth : nat) (e : expr) : positive :=
  match depth with
  | 0 => 41%positive
  | S d =>
      match e with
      | EBVar i => hash_mix 43%positive (hash_nat_small i)
      | EFVar n => hash_mix 47%positive (hash_name_bounded 2 n)
      | EMVar n => hash_mix 53%positive (hash_name_bounded 2 n)
      | ESort u => hash_mix 59%positive (hash_level_bounded 2 u)
      | EConst n us =>
          hash_mix 61%positive (hash_mix (hash_name_bounded 2 n) (hash_levels_bounded 2 us 67%positive))
      | EApp f a =>
          hash_mix 71%positive (hash_mix (hash_expr_bounded d f) (hash_expr_bounded d a))
      | ELam _ _ a b =>
          hash_mix 73%positive (hash_mix (hash_expr_bounded d a) (hash_expr_bounded d b))
      | EPi _ _ a b =>
          hash_mix 79%positive (hash_mix (hash_expr_bounded d a) (hash_expr_bounded d b))
      | ELet _ a v b _ =>
          hash_mix 83%positive (hash_mix (hash_expr_bounded d a)
            (hash_mix (hash_expr_bounded d v) (hash_expr_bounded d b)))
      | ELit (LitNat n) => hash_mix 89%positive (hash_N_fast n)
      | ELit (LitString s) => hash_mix 97%positive (hash_string_bounded 6 s 101%positive)
      | EProj _ i a =>
          hash_mix 103%positive (hash_mix (hash_nat_small i) (hash_expr_bounded d a))
      | EMData a => hash_mix 107%positive (hash_expr_bounded d a)
      end
  end.

Definition hash_expr (e : expr) : positive := hash_expr_bounded 3 e.

Definition hash_binding (b : binding) : positive :=
  let vh := match binding_value b with Some v => hash_mix 109%positive (hash_expr_bounded 2 v) | None => 113%positive end in
  hash_mix (hash_expr_bounded 2 (binding_type b)) vh.

Fixpoint hash_bound_prefix (fuel : nat) (bs : list binding) (acc : positive) : positive :=
  match fuel, bs with
  | 0, _ | _, [] => acc
  | S fuel, b :: bs => hash_bound_prefix fuel bs (hash_mix acc (hash_binding b))
  end.

Fixpoint hash_free_prefix (fuel : nat) (fs : list (name * binding)) (acc : positive) : positive :=
  match fuel, fs with
  | 0, _ | _, [] => acc
  | S fuel, (n, b) :: fs =>
      hash_free_prefix fuel fs (hash_mix acc (hash_mix (hash_name_bounded 2 n) (hash_binding b)))
  end.

Definition hash_context (g : context) : positive :=
  match bound_context g, free_context g with
  | [], [] => 127%positive
  | bs, fs =>
      hash_mix
        (hash_bound_prefix 2 bs 127%positive)
        (hash_free_prefix 2 fs 131%positive)
  end.

(* ========================================================================= *)
(* 3. Full-Context Hash-Bucketed Positive & Negative DefEq Cache             *)
(* ========================================================================= *)

Record defeq_cache_key : Type := {
  dck_context : context;
  dck_lhs     : expr;
  dck_rhs     : expr
}.

Definition defeq_cache_key_eqb (k1 k2 : defeq_cache_key) : bool :=
  context_eqb (dck_context k1) (dck_context k2) &&
  expr_eqb (dck_lhs k1) (dck_lhs k2) &&
  expr_eqb (dck_rhs k1) (dck_rhs k2).

Definition defeq_cache_key_hash (k : defeq_cache_key) : positive :=
  hash_mix (hash_context (dck_context k))
    (hash_mix (hash_expr (dck_lhs k)) (hash_expr (dck_rhs k))).

Record defeq_cache_entry : Type := {
  dce_key     : defeq_cache_key;
  dce_verdict : bool (* true = positive DefEq hit; false = negative failure hit *)
}.

Definition defeq_cache := CacheMap.t (list defeq_cache_entry).

Definition empty_defeq_cache : defeq_cache := CacheMap.empty _.

Fixpoint bucket_lookup (k : defeq_cache_key) (entries : list defeq_cache_entry) : option bool :=
  match entries with
  | [] => None
  | entry :: rest =>
      if defeq_cache_key_eqb k (dce_key entry)
      then Some (dce_verdict entry)
      else bucket_lookup k rest
  end.

Definition cache_find {A : Type} (h : positive) (m : CacheMap.t A) : option A :=
  match m with
  | PositiveMap.Leaf _ => None
  | _ => PositiveMap.find h m
  end.

Definition cache_lookup (k : defeq_cache_key) (cache : defeq_cache) : option bool :=
  match cache_find (defeq_cache_key_hash k) cache with
  | None => None
  | Some entries => bucket_lookup k entries
  end.

Definition cache_insert (k : defeq_cache_key) (verdict : bool)
    (cache : defeq_cache) : defeq_cache :=
  let h := defeq_cache_key_hash k in
  let entries := match cache_find h cache with Some xs => xs | None => [] end in
  CacheMap.add h ({| dce_key := k; dce_verdict := verdict |} :: entries) cache.

Definition key_of_query (g : context) (t s : expr) : defeq_cache_key := {|
  dck_context := g;
  dck_lhs := t;
  dck_rhs := s
|}.

(* Cached definitional-equality wrapper returning updated cache + result *)
Definition cached_defeq (fuel : nat) (env : environment) (ps : list name)
    (g : context) (cache : defeq_cache) (t s : expr)
    : defeq_cache * result bool :=
  let key := key_of_query g t s in
  match cache_lookup key cache with
  | Some verdict => (cache, Accept verdict)
  | None =>
      let res := defeq fuel env ps g t s in
      match res with
      | Accept verdict => (cache_insert key verdict cache, Accept verdict)
      | Reject err => (cache, Reject err)
      | Decline why => (cache, Decline why)
      end
  end.

(* ========================================================================= *)
(* 4. Cache Soundness Invariant & Exact Refinement Theorems                  *)
(* ========================================================================= *)

Definition cache_sound_for (fuel : nat) (env : environment) (ps : list name)
    (cache : defeq_cache) : Prop :=
  forall g t s verdict,
    cache_lookup (key_of_query g t s) cache = Some verdict ->
    defeq fuel env ps g t s = Accept verdict.

Lemma empty_cache_sound fuel env ps :
  cache_sound_for fuel env ps empty_defeq_cache.
Proof.
  intros g t s verdict H. unfold cache_lookup, empty_defeq_cache, cache_find in H.
  discriminate H.
Qed.

Theorem cached_defeq_refines_uncached fuel env ps g cache t s :
  cache_sound_for fuel env ps cache ->
  snd (cached_defeq fuel env ps g cache t s) = defeq fuel env ps g t s.
Proof.
  intros Hsound. unfold cached_defeq.
  destruct (cache_lookup (key_of_query g t s) cache) as [verdict|] eqn:Hlk.
  - simpl. symmetry. apply Hsound. exact Hlk.
  - destruct (defeq fuel env ps g t s); reflexivity.
Qed.

Theorem cached_defeq_preserves_positive_and_negative fuel env ps g cache t s verdict :
  cache_sound_for fuel env ps cache ->
  snd (cached_defeq fuel env ps g cache t s) = Accept verdict <->
  defeq fuel env ps g t s = Accept verdict.
Proof.
  intros Hsound.
  rewrite (@cached_defeq_refines_uncached fuel env ps g cache t s Hsound).
  tauto.
Qed.

(* Same-depth distinct contexts never alias (closes bugs/open-term-cache-context). *)
Example same_depth_distinct_types_never_alias :
  let g1 := push_binding empty_context (ESort LZero) None in
  let g2 := push_binding empty_context (ESort (LSucc LZero)) None in
  List.length (bound_context g1) = List.length (bound_context g2) /\
  defeq_cache_key_eqb (key_of_query g1 (EBVar 0) (EBVar 0))
                      (key_of_query g2 (EBVar 0) (EBVar 0)) = false.
Proof. split; reflexivity. Qed.

Example same_depth_distinct_let_values_never_alias :
  let g1 := push_binding empty_context (ESort LZero) (Some (ELit (LitNat 0))) in
  let g2 := push_binding empty_context (ESort LZero) (Some (ELit (LitNat 1))) in
  List.length (bound_context g1) = List.length (bound_context g2) /\
  defeq_cache_key_eqb (key_of_query g1 (EBVar 0) (EBVar 0))
                      (key_of_query g2 (EBVar 0) (EBVar 0)) = false.
Proof. split; reflexivity. Qed.

(* Semantic soundness of positive cache hits with respect to VIsDefEqU *)
Definition positive_cache_semantically_sound (venv : VEnv) (uvars : nat)
    (interp : context -> expr -> VExpr -> Prop) (cache : defeq_cache) : Prop :=
  forall g t s t' s' G,
    List.length G = List.length (bound_context g) ->
    cache_lookup (key_of_query g t s) cache = Some true ->
    interp g t t' ->
    interp g s s' ->
    VIsDefEqU venv uvars G t' s'.

Theorem positive_cache_hit_sound venv uvars interp cache g t s t' s' G :
  positive_cache_semantically_sound venv uvars interp cache ->
  List.length G = List.length (bound_context g) ->
  cache_lookup (key_of_query g t s) cache = Some true ->
  interp g t t' ->
  interp g s s' ->
  VIsDefEqU venv uvars G t' s'.
Proof.
  intros Hsem Hlen Hlk Ht Hs.
  eapply Hsem; eassumption.
Qed.

(* ========================================================================= *)
(* 5. Pure-Gallina Union-Find EquivManager (Lean4Lean/EquivManager.lean)     *)
(* ========================================================================= *)

Record equiv_manager : Type := {
  em_parent : PositiveMap.t positive;
  em_next   : positive;
  em_nodes  : CacheMap.t (list (context * expr * positive))
}.

Definition em_empty : equiv_manager := {|
  em_parent := PositiveMap.empty _;
  em_next   := 1%positive;
  em_nodes  := CacheMap.empty _
|}.

Fixpoint em_find_aux (fuel : nat) (parent : PositiveMap.t positive)
    (n : positive) : positive * PositiveMap.t positive :=
  match fuel with
  | 0 => (n, parent)
  | S fuel =>
      match PositiveMap.find n parent with
      | None => (n, parent)
      | Some p =>
          if Pos.eqb p n then (n, parent)
          else
            let '(root, parent') := em_find_aux fuel parent p in
            (root, PositiveMap.add n root parent')
      end
  end.

Definition em_find (m : equiv_manager) (n : positive) : positive * equiv_manager :=
  let '(r, parent') := em_find_aux 64 (em_parent m) n in
  (r, {| em_parent := parent'; em_next := em_next m; em_nodes := em_nodes m |}).

Definition em_merge (m : equiv_manager) (n1 n2 : positive) : equiv_manager :=
  let '(r1, m1) := em_find m n1 in
  let '(r2, m2) := em_find m1 n2 in
  if Pos.eqb r1 r2 then m2
  else {| em_parent := PositiveMap.add r1 r2 (em_parent m2);
          em_next := em_next m2;
          em_nodes := em_nodes m2 |}.

Fixpoint em_bucket_find (g : context) (e : expr)
    (xs : list (context * expr * positive)) : option positive :=
  match xs with
  | [] => None
  | (g', e', id) :: rest =>
      if core_alpha_context 256 g g' && fst (core_alpha 256 e e')
      then Some id
      else em_bucket_find g e rest
  end.

Definition em_to_node_hashed (m : equiv_manager) (h : positive) (g : context) (e : expr)
    : positive * equiv_manager :=
  let bucket := match cache_find h (em_nodes m) with Some xs => xs | None => [] end in
  match em_bucket_find g e bucket with
  | Some id => (id, m)
  | None =>
      let id := em_next m in
      let nodes' := CacheMap.add h ((g, e, id) :: firstn 3 bucket) (em_nodes m) in
      (id, {| em_parent := em_parent m; em_next := Pos.succ id; em_nodes := nodes' |})
  end.

Definition em_to_node (m : equiv_manager) (g : context) (e : expr)
    : positive * equiv_manager :=
  em_to_node_hashed m (hash_mix (hash_context g) (hash_expr e)) g e.

Definition em_add_equiv_hashed (m : equiv_manager) (h1 h2 : positive)
    (g : context) (e1 e2 : expr) : equiv_manager :=
  let '(r1, m1) := em_to_node_hashed m h1 g e1 in
  let '(r2, m2) := em_to_node_hashed m1 h2 g e2 in
  em_merge m2 r1 r2.

Definition em_add_equiv (m : equiv_manager) (g : context) (e1 e2 : expr)
    : equiv_manager :=
  let hg := hash_context g in
  em_add_equiv_hashed m (hash_mix hg (hash_expr e1)) (hash_mix hg (hash_expr e2)) g e1 e2.

Definition em_check_equiv (m : equiv_manager) (g : context) (e1 e2 : expr)
    : bool * equiv_manager :=
  if core_alpha_eq e1 e2 then (true, m)
  else
    let hg := hash_context g in
    let h1 := hash_mix hg (hash_expr e1) in
    let h2 := hash_mix hg (hash_expr e2) in
    match CacheMap.find h1 (em_nodes m), CacheMap.find h2 (em_nodes m) with
    | Some b1, Some b2 =>
        match em_bucket_find g e1 b1, em_bucket_find g e2 b2 with
        | Some n1, Some n2 =>
            let '(r1, m1) := em_find m n1 in
            let '(r2, m2) := em_find m1 n2 in
            (Pos.eqb r1 r2, m2)
        | _, _ => (false, m)
        end
    | _, _ => (false, m)
    end.

(* Read-only root lookup for fast, trivially invariant-preserving checks. *)
Fixpoint em_root_aux (fuel : nat) (parent : PositiveMap.t positive)
    (n : positive) : positive :=
  match fuel with
  | 0 => n
  | S fuel =>
      match PositiveMap.find n parent with
      | None => n
      | Some p => if Pos.eqb p n then n else em_root_aux fuel parent p
      end
  end.

Definition em_root (m : equiv_manager) (n : positive) : positive :=
  em_root_aux 64 (em_parent m) n.

Definition em_is_equiv_ro_hashed (m : equiv_manager) (h1 h2 : positive)
    (g : context) (e1 e2 : expr) : bool :=
  match em_next m with
  | xH => false
  | _ =>
      match CacheMap.find h1 (em_nodes m), CacheMap.find h2 (em_nodes m) with
      | Some b1, Some b2 =>
          match em_bucket_find g e1 b1, em_bucket_find g e2 b2 with
          | Some n1, Some n2 => Pos.eqb (em_root m n1) (em_root m n2)
          | _, _ => false
          end
      | _, _ => false
      end
  end.

Definition em_is_equiv_ro (m : equiv_manager) (g : context) (e1 e2 : expr) : bool :=
  if core_alpha_eq e1 e2 then true
  else
    let hg := hash_context g in
    em_is_equiv_ro_hashed m (hash_mix hg (hash_expr e1)) (hash_mix hg (hash_expr e2)) g e1 e2.

Definition em_sound_for (R : context -> expr -> expr -> Prop) (m : equiv_manager) : Prop :=
  exists (interp : positive -> context -> expr -> Prop),
    (forall g e id,
       (exists h b, CacheMap.find h (em_nodes m) = Some b /\ em_bucket_find g e b = Some id) ->
       interp id g e) /\
    (forall id1 id2 g e1 e2,
       interp id1 g e1 -> interp id2 g e2 ->
       em_root m id1 = em_root m id2 ->
       R g e1 e2).

Lemma em_empty_sound R : em_sound_for R em_empty.
Proof.
  exists (fun _ _ _ => False). split.
  - intros g e id [h [b [Hfind _]]]. simpl in Hfind.
    rewrite PositiveMap.gempty in Hfind. discriminate.
  - intros id1 id2 g e1 e2 H _. destruct H.
Qed.

Theorem em_is_equiv_ro_hashed_sound R m h1 h2 g e1 e2 :
  em_sound_for R m ->
  em_is_equiv_ro_hashed m h1 h2 g e1 e2 = true ->
  R g e1 e2.
Proof.
  intros [interp [Hnode Heq]] Hchk.
  unfold em_is_equiv_ro_hashed in Hchk.
  destruct (em_next m); [| |discriminate];
    (destruct (CacheMap.find h1 (em_nodes m)) as [b1|] eqn:Hf1; [|discriminate];
     destruct (CacheMap.find h2 (em_nodes m)) as [b2|] eqn:Hf2; [|discriminate];
     destruct (em_bucket_find g e1 b1) as [n1|] eqn:Hb1; [|discriminate];
     destruct (em_bucket_find g e2 b2) as [n2|] eqn:Hb2; [|discriminate];
     apply Pos.eqb_eq in Hchk;
     eapply Heq; [eapply Hnode; eauto | eapply Hnode; eauto | exact Hchk]).
Qed.

Theorem em_is_equiv_ro_sound R m g e1 e2 :
  (forall g a b, expr_eqb a b = true -> R g a b) ->
  em_sound_for R m ->
  em_is_equiv_ro m g e1 e2 = true ->
  R g e1 e2.
Proof.
  intros Halpha Hm Hchk.
  unfold em_is_equiv_ro in Hchk.
  destruct (core_alpha_eq e1 e2) eqn:Ha.
  - apply Halpha. unfold core_alpha_eq in Ha.
    destruct (core_alpha 256 e1 e2) as [ok rem] eqn:Hca. simpl in Ha; subst ok.
    eapply core_alpha_sound. exact Hca.
  - eapply em_is_equiv_ro_hashed_sound; eauto.
Qed.

Print Assumptions core_alpha_context_sound.
Print Assumptions cached_defeq_refines_uncached.
Print Assumptions cached_defeq_preserves_positive_and_negative.
Print Assumptions positive_cache_hit_sound.
Print Assumptions em_empty_sound.
Print Assumptions em_is_equiv_ro_hashed_sound.
Print Assumptions em_is_equiv_ro_sound.
