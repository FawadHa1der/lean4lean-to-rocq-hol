(* SPDX-License-Identifier: Apache-2.0
   SOURCE-ONLY interface candidate, not compiled or integrated.
   Refines preserved QuotientTransaction761 with a prefix/next-flag payload.
   Environment projection uses AdmissionDelta's existing prefix API.
   The initialized bit is kernel-owned, not an exported-row certificate.
   This API does not replace or bypass admit_quotient's header validation. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Declarations Quotient AdmissionDelta
  QuotientTransaction.
Import ListNotations.

Definition quotient_delta_prefix (state : quotient_transaction_state) : environment :=
  if snd state then [] else canonical_quotient_block.

(* Payload is (new prefix, next initialized bit), not a complete environment. *)
Definition quotient_transaction_delta := (environment * bool)%type.

(* Select a payload only after the complete retained transaction succeeds. *)
Definition initialize_quotient_delta (state : quotient_transaction_state)
    : result quotient_transaction_delta :=
  next <- initialize_quotient state ;;
  Accept (quotient_delta_prefix state, snd next).

Definition apply_quotient_delta (state : quotient_transaction_state)
    (payload : quotient_transaction_delta) : quotient_transaction_state :=
  (fst payload ++ fst state, snd payload).

Definition attach_quotient_delta (state : quotient_transaction_state)
    (delta : result quotient_transaction_delta) : result quotient_transaction_state :=
  result_map (apply_quotient_delta state) delta.

Definition quotient_delta_step (state : quotient_transaction_state)
    : result quotient_transaction_state :=
  attach_quotient_delta state (initialize_quotient_delta state).

(* Match PersistentAdmission.transaction's failure behavior without an index
   adapter or default-driver integration. No failure carries a new state. *)
Definition quotient_delta_transaction (state : quotient_transaction_state)
    : quotient_transaction_state * result unit :=
  match quotient_delta_step state with
  | Accept next => (next, Accept tt)
  | Reject reason => (state, Reject reason)
  | Decline reason => (state, Decline reason)
  end.

Lemma quotient_delta_refines state :
  attach_quotient_delta state (initialize_quotient_delta state) =
  initialize_quotient state.
Proof.
  destruct state as [env initialized]. destruct initialized.
  - reflexivity.
  - unfold attach_quotient_delta, initialize_quotient_delta.
    destruct (initialize_quotient (env, false)) as [next|err|reason] eqn:Run;
      try reflexivity.
    pose proof (@quotient_transaction_no_partial_commit env next Run) as Shape.
    subst next. reflexivity.
Qed.

Lemma quotient_delta_environment_refines state :
  attach_prefix (fst state) (result_map fst (initialize_quotient_delta state)) =
  result_map fst (initialize_quotient state).
Proof.
  destruct state as [env initialized]. destruct initialized.
  - reflexivity.
  - unfold attach_prefix, initialize_quotient_delta.
    destruct (initialize_quotient (env, false)) as [next|err|reason] eqn:Run;
      try reflexivity.
    pose proof (@quotient_transaction_no_partial_commit env next Run) as Shape.
    subst next. reflexivity.
Qed.

Lemma quotient_delta_step_refines state :
  quotient_delta_step state = initialize_quotient state.
Proof. apply quotient_delta_refines. Qed.

Lemma quotient_delta_success_from_transaction state next :
  initialize_quotient state = Accept next ->
  initialize_quotient_delta state = Accept (quotient_delta_prefix state, snd next).
Proof. intro H. unfold initialize_quotient_delta. rewrite H. reflexivity. Qed.

Lemma quotient_delta_accepted_payload state payload :
  initialize_quotient_delta state = Accept payload ->
  payload = (quotient_delta_prefix state, true).
Proof.
  unfold initialize_quotient_delta.
  destruct (initialize_quotient state) as [next|err|reason] eqn:Run;
    cbn [bind]; intro H; try discriminate.
  pose proof (@quotient_transaction_sets_flag state next Run) as Flag.
  inversion H. rewrite Flag. reflexivity.
Qed.

Lemma quotient_delta_first_success env :
  quotient_check_eq env = Accept tt ->
  quotient_names_fresh env quotient_transaction_names = true ->
  initialize_quotient_delta (env, false) = Accept (canonical_quotient_block, true).
Proof.
  intros Eq Fresh. unfold initialize_quotient_delta.
  rewrite (@quotient_success_transaction env Eq Fresh). reflexivity.
Qed.

Lemma quotient_delta_first_exact env payload :
  initialize_quotient_delta (env, false) = Accept payload ->
  payload = (canonical_quotient_block, true).
Proof. apply quotient_delta_accepted_payload. Qed.

Lemma quotient_delta_initialized_empty env :
  initialize_quotient_delta (env, true) = Accept ([], true).
Proof. reflexivity. Qed.

Lemma quotient_delta_length state payload :
  initialize_quotient_delta state = Accept payload ->
  List.length (fst payload) = if snd state then 0 else 4.
Proof.
  intro H. rewrite (@quotient_delta_accepted_payload state payload H).
  unfold quotient_delta_prefix. destruct (snd state); reflexivity.
Qed.

Lemma quotient_delta_reject_exact state reason :
  initialize_quotient_delta state = Reject reason <->
  initialize_quotient state = Reject reason.
Proof.
  unfold initialize_quotient_delta.
  destruct (initialize_quotient state); cbn [bind]; split; intro H;
    inversion H; reflexivity.
Qed.

Lemma quotient_delta_decline_exact state reason :
  initialize_quotient_delta state = Decline reason <->
  initialize_quotient state = Decline reason.
Proof.
  unfold initialize_quotient_delta.
  destruct (initialize_quotient state); cbn [bind]; split; intro H;
    inversion H; reflexivity.
Qed.

Lemma quotient_delta_eq_error_first env reason :
  quotient_check_eq env = Reject reason ->
  initialize_quotient_delta (env, false) = Reject reason.
Proof.
  intro H. apply (proj2 (quotient_delta_reject_exact (env, false) reason)).
  apply quotient_eq_error_precedes_names. exact H.
Qed.

Lemma quotient_delta_collision env :
  quotient_check_eq env = Accept tt ->
  quotient_names_fresh env quotient_transaction_names = false ->
  initialize_quotient_delta (env, false) = Reject DuplicateDeclaration.
Proof.
  intros Eq Names.
  apply (proj2 (quotient_delta_reject_exact (env, false) DuplicateDeclaration)).
  apply quotient_collision_transaction; assumption.
Qed.

Lemma quotient_delta_transaction_refines state :
  quotient_delta_transaction state =
  match initialize_quotient state with
  | Accept next => (next, Accept tt)
  | Reject reason => (state, Reject reason)
  | Decline reason => (state, Decline reason)
  end.
Proof.
  unfold quotient_delta_transaction. rewrite quotient_delta_step_refines.
  reflexivity.
Qed.

Lemma quotient_delta_reject_rolls_back state reason :
  initialize_quotient_delta state = Reject reason ->
  quotient_delta_transaction state = (state, Reject reason).
Proof.
  intro H. unfold quotient_delta_transaction, quotient_delta_step,
    attach_quotient_delta. rewrite H. reflexivity.
Qed.

Lemma quotient_delta_decline_rolls_back state reason :
  initialize_quotient_delta state = Decline reason ->
  quotient_delta_transaction state = (state, Decline reason).
Proof.
  intro H. unfold quotient_delta_transaction, quotient_delta_step,
    attach_quotient_delta. rewrite H. reflexivity.
Qed.

Lemma quotient_delta_success_commits_whole state payload :
  initialize_quotient_delta state = Accept payload ->
  quotient_delta_transaction state =
    ((fst payload ++ fst state, snd payload), Accept tt).
Proof.
  intro H. unfold quotient_delta_transaction, quotient_delta_step,
    attach_quotient_delta. rewrite H. reflexivity.
Qed.

Lemma quotient_delta_repeat_empty state next :
  quotient_delta_step state = Accept next ->
  initialize_quotient_delta next = Accept ([], true).
Proof.
  rewrite quotient_delta_step_refines. intro H.
  pose proof (@quotient_transaction_sets_flag state next H) as Flag.
  pose proof (@quotient_transaction_idempotent state next H) as Again.
  unfold initialize_quotient_delta. rewrite Again. cbn [bind].
  unfold quotient_delta_prefix. rewrite Flag. reflexivity.
Qed.

(* A separate theorem about the UNCHANGED exported-row API, not an adapter from
   unchecked row data to initialization. Replay/header composition remains open. *)
Lemma existing_export_admission_requires_header fuel env n ps ty kind next :
  admit_quotient fuel env n ps ty kind = Accept next ->
  check_header fuel env n ps ty = Accept tt.
Proof.
  unfold admit_quotient.
  destruct (quotient_check_eq env) as [u_eq| |]; cbn [bind]; try (intro H; discriminate H).
  destruct (check_header fuel env n ps ty) as [u_hdr|err|reason] eqn:Header;
    cbn [bind]; try (intro H; discriminate H).
  intro H. destruct u_hdr. reflexivity.
Qed.

(* These requests are source for a later guarded proof/assumption audit. *)
Print Assumptions quotient_delta_refines.
Print Assumptions quotient_delta_environment_refines.
Print Assumptions quotient_delta_length.
Print Assumptions quotient_delta_reject_rolls_back.
Print Assumptions quotient_delta_decline_rolls_back.
Print Assumptions quotient_delta_repeat_empty.
Print Assumptions existing_export_admission_requires_header.
