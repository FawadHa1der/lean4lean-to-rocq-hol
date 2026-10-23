(* SPDX-License-Identifier: Apache-2.0
   Private benchmark candidates only; no production extraction overrides. *)
From Stdlib Require Import List String Ascii NArith Extraction.
From LeanPort Require Import Syntax EnvironmentIndex EnvironmentIndexBenchmark.
Import ListNotations.

Definition suffix_zero := Ascii false false false false false false false false.
Definition suffix_bit (b : bool) (p : positive) := if b then xI p else xO p.

(* A leading sentinel bit avoids normalization/arithmetic while packing bytes. *)
Definition suffix_byte (c : ascii) (p : positive) : positive :=
  let '(Ascii b0 b1 b2 b3 b4 b5 b6 b7) := c in
  suffix_bit b0 (suffix_bit b1 (suffix_bit b2 (suffix_bit b3
    (suffix_bit b4 (suffix_bit b5 (suffix_bit b6 (suffix_bit b7 p))))))).

Fixpoint suffix_scan2 (a b : ascii) (s : string) : positive :=
  match s with
  | EmptyString => suffix_byte b (suffix_byte a xH)
  | String c rest => suffix_scan2 b c rest
  end.
Fixpoint suffix_scan3 (a b c : ascii) (s : string) : positive :=
  match s with
  | EmptyString => suffix_byte c (suffix_byte b (suffix_byte a xH))
  | String d rest => suffix_scan3 b c d rest
  end.
Fixpoint suffix_scan4 (a b c d : ascii) (s : string) : positive :=
  match s with
  | EmptyString => suffix_byte d (suffix_byte c (suffix_byte b (suffix_byte a xH)))
  | String e rest => suffix_scan4 b c d e rest
  end.

Definition suffix_xor_rotate (a c : ascii) : ascii :=
  let '(Ascii a0 a1 a2 a3 a4 a5 a6 a7) := a in
  let '(Ascii c0 c1 c2 c3 c4 c5 c6 c7) := c in
  Ascii (xorb a7 c0) (xorb a0 c1) (xorb a1 c2) (xorb a2 c3)
        (xorb a3 c4) (xorb a4 c5) (xorb a5 c6) (xorb a6 c7).

Fixpoint suffix_fold8 (a : ascii) (s : string) : positive :=
  match s with
  | EmptyString => suffix_byte a xH
  | String c rest => suffix_fold8 (suffix_xor_rotate a c) rest
  end.
Fixpoint suffix_fold16 (a b : ascii) (s : string) : positive :=
  match s with
  | EmptyString => suffix_byte b (suffix_byte a xH)
  | String c rest => suffix_fold16 b (suffix_xor_rotate a c) rest
  end.

Definition suffix_lift (f : string -> positive) (n : name) : N :=
  match n with
  | NameAnon => 0
  | NameStr _ s => Npos (f s)
  | NameNum _ value => N.land value 65535
  end.
Definition suffix_last2 := suffix_lift (suffix_scan2 suffix_zero suffix_zero).
Definition suffix_last3 := suffix_lift (suffix_scan3 suffix_zero suffix_zero suffix_zero).
Definition suffix_last4 := suffix_lift (suffix_scan4 suffix_zero suffix_zero suffix_zero suffix_zero).
Definition suffix_bitfold8 := suffix_lift (suffix_fold8 suffix_zero).
Definition suffix_bitfold16 := suffix_lift (suffix_fold16 suffix_zero suffix_zero).

Fixpoint suffix_pair (a b : ascii) (s : string) : ascii * ascii :=
  match s with
  | EmptyString => (a,b)
  | String c rest => suffix_pair b c rest
  end.
Definition suffix_component_pair (n : name) : ascii * ascii :=
  match n with
  | NameStr _ s => suffix_pair suffix_zero suffix_zero s
  | _ => (suffix_zero,suffix_zero)
  end.
Definition suffix_parent2 (n : name) : N :=
  match n with
  | NameAnon => 0
  | NameNum _ value => N.land value 65535
  | NameStr parent s =>
      let '(a,b) := suffix_component_pair parent in
      let '(c,d) := suffix_pair suffix_zero suffix_zero s in
      Npos (suffix_byte d (suffix_byte c (suffix_byte b (suffix_byte a xH))))
  end.

Lemma suffix_bit_width b p : Pos.size_nat (suffix_bit b p) = S (Pos.size_nat p).
Proof. destruct b; reflexivity. Qed.
Lemma suffix_byte_width c p : Pos.size_nat (suffix_byte c p) = 8 + Pos.size_nat p.
Proof. destruct c. unfold suffix_byte. repeat rewrite suffix_bit_width. reflexivity. Qed.
Lemma suffix_scan2_width s a b : Pos.size_nat (suffix_scan2 a b s) = 17.
Proof. revert a b. induction s; intros; simpl; [repeat rewrite suffix_byte_width; reflexivity | apply IHs]. Qed.
Lemma suffix_scan3_width s a b c : Pos.size_nat (suffix_scan3 a b c s) = 25.
Proof. revert a b c. induction s; intros; simpl; [repeat rewrite suffix_byte_width; reflexivity | apply IHs]. Qed.
Lemma suffix_scan4_width s a b c d : Pos.size_nat (suffix_scan4 a b c d s) = 33.
Proof. revert a b c d. induction s; intros; simpl; [repeat rewrite suffix_byte_width; reflexivity | apply IHs]. Qed.
Lemma suffix_fold8_width s a : Pos.size_nat (suffix_fold8 a s) = 9.
Proof. revert a. induction s; intros; simpl; [rewrite suffix_byte_width; reflexivity | apply IHs]. Qed.
Lemma suffix_fold16_width s a b : Pos.size_nat (suffix_fold16 a b s) = 17.
Proof. revert a b. induction s; intros; simpl; [repeat rewrite suffix_byte_width; reflexivity | apply IHs]. Qed.
Lemma suffix_parent2_width parent s :
  match suffix_parent2 (NameStr parent s) with N0 => False | Npos p => Pos.size_nat p = 33 end.
Proof.
  unfold suffix_parent2. destruct (suffix_component_pair parent) as [a b].
  destruct (suffix_pair suffix_zero suffix_zero s) as [c d].
  repeat rewrite suffix_byte_width. reflexivity.
Qed.
Lemma suffix_numeric_bound value : (N.land value 65535 <= 65535)%N.
Proof. apply N.land_le_r. Qed.

Definition suffix_candidates : list (name -> N) :=
  [suffix_last2; suffix_last3; suffix_last4; suffix_bitfold8; suffix_bitfold16; suffix_parent2].
Theorem suffix_candidates_refine :
  Forall (fun hash => forall env n,
    indexed_find_decl hash n (index_environment hash env) = find_decl n env) suffix_candidates.
Proof. apply Forall_forall. intros hash _ env n. apply indexed_environment_lookup. Qed.

Example suffix_last2_collision :
  suffix_last2 (NameStr NameAnon "leftXY") = suffix_last2 (NameStr NameAnon "rightXY").
Proof. vm_compute. reflexivity. Qed.
Example suffix_collision_not_equality :
  indexed_find_decl suffix_last2 (NameStr NameAnon "rightXY")
    (index_environment suffix_last2
      [benchmark_dummy_declaration (NameStr NameAnon "leftXY") 1;
       benchmark_dummy_declaration (NameStr NameAnon "rightXY") 2]) =
    Some (benchmark_dummy_declaration (NameStr NameAnon "rightXY") 2).
Proof. vm_compute. reflexivity. Qed.

Extraction Language OCaml.
Extraction "environment_index_suffix_extracted.ml"
  suffix_last2 suffix_last3 suffix_last4 suffix_bitfold8 suffix_bitfold16 suffix_parent2
  benchmark_hash_leaf16 benchmark_hash32 benchmark_hash_constant
  benchmark_dummy_declaration benchmark_bucket_lengths
  empty_declaration_index index_declaration index_environment indexed_find_decl find_decl.
