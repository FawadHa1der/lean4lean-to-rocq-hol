(* SPDX-License-Identifier: Apache-2.0
   Isolated benchmark candidates; not imported by the production checker. *)
From Stdlib Require Import List String Ascii NArith Extraction.
From LeanPort Require Import Syntax EnvironmentIndex.
Import ListNotations.

Definition benchmark_hash_step (mask h byte : N) : N :=
  N.land (N.shiftl h 5 + h + byte) mask.

Fixpoint benchmark_hash_string (mask h : N) (s : string) : N :=
  match s with
  | EmptyString => h
  | String c rest =>
      benchmark_hash_string mask (benchmark_hash_step mask h (N_of_ascii c)) rest
  end.

Fixpoint benchmark_hash_positive (mask h : N) (p : positive) : N :=
  match p with
  | xH => benchmark_hash_step mask h 1
  | xO rest => benchmark_hash_step mask (benchmark_hash_positive mask h rest) 0
  | xI rest => benchmark_hash_step mask (benchmark_hash_positive mask h rest) 1
  end.

Definition benchmark_hash_number (mask h n : N) : N :=
  match n with
  | N0 => benchmark_hash_step mask h 0
  | Npos p => benchmark_hash_positive mask (benchmark_hash_step mask h 1) p
  end.

Fixpoint benchmark_hash_name (mask : N) (n : name) : N :=
  match n with
  | NameAnon => N.land 5381 mask
  | NameStr parent s =>
      benchmark_hash_string mask
        (benchmark_hash_step mask (benchmark_hash_name mask parent) 2) s
  | NameNum parent value =>
      benchmark_hash_number mask
        (benchmark_hash_step mask (benchmark_hash_name mask parent) 3) value
  end.

Definition benchmark_hash16 := benchmark_hash_name 65535.
Definition benchmark_hash32 := benchmark_hash_name 4294967295.
Definition benchmark_hash_leaf16 (n : name) : N :=
  match n with
  | NameAnon => N.land 5381 65535
  | NameStr _ s =>
      benchmark_hash_string 65535 (benchmark_hash_step 65535 5381 2) s
  | NameNum _ value =>
      benchmark_hash_number 65535 (benchmark_hash_step 65535 5381 3) value
  end.
Definition benchmark_hash_constant (_ : name) : N := 0.

Lemma benchmark_hash_step_bound mask h byte :
  (benchmark_hash_step mask h byte <= mask)%N.
Proof. apply N.land_le_r. Qed.

Lemma benchmark_hash_string_bound mask s h :
  (h <= mask)%N -> (benchmark_hash_string mask h s <= mask)%N.
Proof.
  revert h. induction s; intros h H; simpl; auto.
  apply IHs. apply benchmark_hash_step_bound.
Qed.

Lemma benchmark_hash_positive_bound mask p h :
  (benchmark_hash_positive mask h p <= mask)%N.
Proof. destruct p; simpl; apply benchmark_hash_step_bound. Qed.

Lemma benchmark_hash_number_bound mask h n :
  (benchmark_hash_number mask h n <= mask)%N.
Proof.
  destruct n; simpl.
  - apply benchmark_hash_step_bound.
  - apply benchmark_hash_positive_bound.
Qed.

Lemma benchmark_hash_name_bound mask n :
  (benchmark_hash_name mask n <= mask)%N.
Proof.
  destruct n.
  - exact (N.land_le_r 5381 mask).
  - apply benchmark_hash_string_bound. apply benchmark_hash_step_bound.
  - apply benchmark_hash_number_bound.
Qed.

Example benchmark_hash16_bound n : (benchmark_hash16 n <= 65535)%N.
Proof. apply benchmark_hash_name_bound. Qed.
Example benchmark_hash32_bound n : (benchmark_hash32 n <= 4294967295)%N.
Proof. apply benchmark_hash_name_bound. Qed.
Example benchmark_hash_leaf16_bound n : (benchmark_hash_leaf16 n <= 65535)%N.
Proof.
  destruct n.
  - exact (N.land_le_r 5381 65535).
  - apply benchmark_hash_string_bound. apply benchmark_hash_step_bound.
  - apply benchmark_hash_number_bound.
Qed.

Example benchmark_hash16_lookup env n :
  indexed_find_decl benchmark_hash16 n (index_environment benchmark_hash16 env) = find_decl n env.
Proof. apply indexed_environment_lookup. Qed.
Example benchmark_hash32_lookup env n :
  indexed_find_decl benchmark_hash32 n (index_environment benchmark_hash32 env) = find_decl n env.
Proof. apply indexed_environment_lookup. Qed.
Example benchmark_hash_leaf16_lookup env n :
  indexed_find_decl benchmark_hash_leaf16 n (index_environment benchmark_hash_leaf16 env) = find_decl n env.
Proof. apply indexed_environment_lookup. Qed.

Definition benchmark_dummy_declaration (n : name) (serial : N) : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := [NameNum NameAnon serial];
     decl_type := ESort LZero; decl_value := None; decl_kind_of := DAssumption |}.

Definition benchmark_bucket_lengths (index : declaration_index) : list nat :=
  List.map (fun entry => List.length (snd entry)) (DeclarationBuckets.elements index).

(* Ordinary structural extraction only. Compile from the dedicated build cwd so
   these generated artifacts never appear among handwritten rocq sources. *)
Extraction Language OCaml.
Extraction "environment_index_extracted.ml"
  benchmark_hash16 benchmark_hash32 benchmark_hash_leaf16 benchmark_hash_constant
  benchmark_dummy_declaration benchmark_bucket_lengths
  empty_declaration_index index_declaration index_environment indexed_find_decl find_decl.
