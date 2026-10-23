(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Collision-safe immutable indexing, independent of the chosen name hash. *)
From Stdlib Require Import List NArith Bool FSets.FMapAVL FSets.FMapFacts
  Structures.OrderedTypeEx.
From LeanPort Require Import Syntax.
Import ListNotations.

Module DeclarationBuckets := FMapAVL.Make(N_as_OT).
Module DeclarationBucketFacts := FMapFacts.WFacts(DeclarationBuckets).

Definition declaration_index := DeclarationBuckets.t (list declaration).

Definition declaration_bucket (key : N) (index : declaration_index) : environment :=
  match DeclarationBuckets.find key index with
  | Some bucket => bucket
  | None => []
  end.

Definition empty_declaration_index : declaration_index := DeclarationBuckets.empty _.

Definition index_declaration (hash : name -> N) (d : declaration)
    (index : declaration_index) : declaration_index :=
  let key := hash (decl_name d) in
  DeclarationBuckets.add key (d :: declaration_bucket key index) index.

Fixpoint index_environment (hash : name -> N) (env : environment) : declaration_index :=
  match env with
  | [] => empty_declaration_index
  | d :: rest => index_declaration hash d (index_environment hash rest)
  end.

Definition indexed_find_decl (hash : name -> N) (n : name)
    (index : declaration_index) : option declaration :=
  find_decl n (declaration_bucket (hash n) index).

Definition declaration_index_matches (hash : name -> N) (env : environment)
    (index : declaration_index) : Prop :=
  forall key, declaration_bucket key index =
    filter (fun d => N.eqb key (hash (decl_name d))) env.

Lemma empty_declaration_index_matches hash :
  declaration_index_matches hash [] empty_declaration_index.
Proof.
  intros key. unfold declaration_bucket, empty_declaration_index.
  rewrite DeclarationBucketFacts.empty_o. reflexivity.
Qed.

Lemma index_declaration_matches hash env index d :
  declaration_index_matches hash env index ->
  declaration_index_matches hash (d :: env) (index_declaration hash d index).
Proof.
  intros H key. unfold index_declaration, declaration_bucket at 1.
  destruct (N.eq_dec (hash (decl_name d)) key) as [Heq | Hneq].
  - subst key. rewrite DeclarationBucketFacts.add_eq_o by reflexivity.
    simpl. rewrite N.eqb_refl. rewrite H. reflexivity.
  - rewrite DeclarationBucketFacts.add_neq_o by exact Hneq.
    change (declaration_bucket key index =
      filter (fun e => N.eqb key (hash (decl_name e))) (d :: env)).
    simpl. assert (N.eqb key (hash (decl_name d)) = false) as E.
    { apply N.eqb_neq. congruence. }
    rewrite E. apply H.
Qed.

Theorem index_environment_matches hash env :
  declaration_index_matches hash env (index_environment hash env).
Proof.
  induction env as [|d env IH]; simpl.
  - apply empty_declaration_index_matches.
  - now apply index_declaration_matches.
Qed.

Lemma find_decl_hash_filter hash n env :
  find_decl n (filter (fun d => N.eqb (hash n) (hash (decl_name d))) env) =
  find_decl n env.
Proof.
  induction env as [|d env IH]; simpl; auto.
  destruct (N.eqb (hash n) (hash (decl_name d))) eqn:E; simpl.
  - destruct (name_eqb n (decl_name d)); auto.
  - destruct (name_eqb n (decl_name d)) eqn:H; auto.
    apply name_eqb_eq in H. subst n. rewrite N.eqb_refl in E. discriminate.
Qed.

Theorem indexed_find_decl_refines hash env index n :
  declaration_index_matches hash env index ->
  indexed_find_decl hash n index = find_decl n env.
Proof.
  intros H. unfold indexed_find_decl. rewrite H. apply find_decl_hash_filter.
Qed.

Corollary indexed_environment_lookup hash env n :
  indexed_find_decl hash n (index_environment hash env) = find_decl n env.
Proof.
  apply indexed_find_decl_refines. apply index_environment_matches.
Qed.

Corollary indexed_lookup_shadowing hash env d :
  indexed_find_decl hash (decl_name d) (index_environment hash (d :: env)) = Some d.
Proof.
  rewrite indexed_environment_lookup. simpl. now rewrite name_eqb_refl.
Qed.

(* A constant hash deliberately puts every declaration in the same bucket.
   Refinement still holds: no injectivity or collision-resistance assumption. *)
Example constant_hash_refinement env n :
  indexed_find_decl (fun _ => 0%N) n (index_environment (fun _ => 0%N) env) =
  find_decl n env.
Proof. apply indexed_environment_lookup. Qed.

Definition index_test_decl (n : name) (ty : expr) : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := ty;
     decl_value := None; decl_kind_of := DAssumption |}.
Definition index_test_a := NameNum NameAnon 1.
Definition index_test_b := NameNum NameAnon 2.
Definition index_test_old := index_test_decl index_test_a (ESort LZero).
Definition index_test_new := index_test_decl index_test_a (ESort (LSucc LZero)).
Definition index_test_other := index_test_decl index_test_b (ESort LZero).

Example colliding_keys_remain_distinct :
  indexed_find_decl (fun _ => 0%N) index_test_b
    (index_environment (fun _ => 0%N) [index_test_new;index_test_other;index_test_old]) =
  Some index_test_other.
Proof. vm_compute. reflexivity. Qed.

Example colliding_duplicate_preserves_newest :
  indexed_find_decl (fun _ => 0%N) index_test_a
    (index_environment (fun _ => 0%N) [index_test_new;index_test_other;index_test_old]) =
  Some index_test_new.
Proof. vm_compute. reflexivity. Qed.

Example missing_colliding_key_is_missing :
  indexed_find_decl (fun _ => 0%N) NameAnon
    (index_environment (fun _ => 0%N) [index_test_new;index_test_other;index_test_old]) = None.
Proof. vm_compute. reflexivity. Qed.
