(* SPDX-License-Identifier: Apache-2.0
   Atomic quotient-initialization candidate. NOT COMPILED OR INTEGRATED.
   Adapted from pinned Lean4Lean/Quot.lean addQuot; see HANDOFF761.txt.
   The initialized bit is kernel-owned state, never a caller certificate. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Quotient.
Import ListNotations.

Definition quotient_transaction_state := (environment * bool)%type.
Definition quotient_initial_state : quotient_transaction_state := ([], false).
Definition quotient_transaction_names := [q_name; q_mk_name; q_lift_name; q_ind_name].

Fixpoint quotient_names_fresh (env : environment) (names : list name) : bool :=
  match names with
  | [] => true
  | n :: rest =>
      match find_decl n env with
      | None => quotient_names_fresh env rest
      | Some _ => false
      end
  end.

(* Environment.add prepends each generated declaration in upstream order. *)
Definition canonical_quotient_block : environment :=
  [canonical_quotient QInd; canonical_quotient QLift;
   canonical_quotient QCtor; canonical_quotient QType].

Definition initialize_quotient (state : quotient_transaction_state)
    : result quotient_transaction_state :=
  if snd state then Accept state else
  _ <- quotient_check_eq (fst state) ;;
  if quotient_names_fresh (fst state) quotient_transaction_names then
    Accept (canonical_quotient_block ++ fst state, true)
  else Reject DuplicateDeclaration.

Lemma quotient_initialized_noop env :
  initialize_quotient (env, true) = Accept (env, true).
Proof. reflexivity. Qed.

Lemma quotient_eq_error_precedes_names env reason :
  quotient_check_eq env = Reject reason ->
  initialize_quotient (env, false) = Reject reason.
Proof. intro H. unfold initialize_quotient. cbn [fst snd]. rewrite H. reflexivity. Qed.

Lemma quotient_collision_transaction env :
  quotient_check_eq env = Accept tt ->
  quotient_names_fresh env quotient_transaction_names = false ->
  initialize_quotient (env, false) = Reject DuplicateDeclaration.
Proof.
  intros Heq Hnames. unfold initialize_quotient. cbn [fst snd].
  rewrite Heq. cbn [bind]. rewrite Hnames. reflexivity.
Qed.

Lemma quotient_success_transaction env :
  quotient_check_eq env = Accept tt ->
  quotient_names_fresh env quotient_transaction_names = true ->
  initialize_quotient (env, false) =
    Accept (canonical_quotient_block ++ env, true).
Proof.
  intros Heq Hnames. unfold initialize_quotient. cbn [fst snd].
  rewrite Heq. cbn [bind]. rewrite Hnames. reflexivity.
Qed.

Lemma quotient_transaction_sets_flag state next :
  initialize_quotient state = Accept next -> snd next = true.
Proof.
  destruct state as [env initialized]. destruct initialized.
  - cbn [initialize_quotient]. intro H. inversion H. reflexivity.
  - unfold initialize_quotient. cbn [fst snd].
    destruct (quotient_check_eq env) as [u|reason|reason]; cbn [bind];
      try (intro H; discriminate H).
    destruct (quotient_names_fresh env quotient_transaction_names);
      intro H; inversion H; reflexivity.
Qed.

Lemma quotient_transaction_idempotent state next :
  initialize_quotient state = Accept next ->
  initialize_quotient next = Accept next.
Proof.
  intro H. pose proof (@quotient_transaction_sets_flag state next H) as flag.
  unfold initialize_quotient. rewrite flag. reflexivity.
Qed.

Lemma quotient_transaction_no_partial_commit env next :
  initialize_quotient (env, false) = Accept next ->
  next = (canonical_quotient_block ++ env, true).
Proof.
  unfold initialize_quotient. cbn [fst snd].
  destruct (quotient_check_eq env) as [u|reason|reason]; cbn [bind];
    try (intro H; discriminate H).
  destruct (quotient_names_fresh env quotient_transaction_names);
    intro H; inversion H; reflexivity.
Qed.

Lemma canonical_quotient_block_length : List.length canonical_quotient_block = 4.
Proof. reflexivity. Qed.

Print Assumptions quotient_transaction_no_partial_commit.
Print Assumptions quotient_transaction_idempotent.
