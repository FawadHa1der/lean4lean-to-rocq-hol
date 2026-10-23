(* SPDX-License-Identifier: Apache-2.0
   SOURCE-ONLY persistent-index adapter for preserved quotient delta794/761.
   Not compiled, extracted, or connected to the default admission driver.
   Index correctness is carried by indexed_state. This record does NOT prove
   kernel reachability or provenance of its initialized bit. *)
From Stdlib Require Import List NArith Bool.
From LeanPort Require Import Syntax EnvironmentIndex RuntimeChecker PersistentIndex AdmissionDelta
  QuotientTransaction QuotientTransactionDelta.
Import ListNotations.
Set Implicit Arguments.

Record quotient_indexed_state (hash : name -> N) : Type := {
  quotient_indexed_base : indexed_state hash;
  quotient_indexed_initialized : bool
}.

Definition quotient_indexed_project hash (s : quotient_indexed_state hash)
    : quotient_transaction_state :=
  (state_environment (quotient_indexed_base s), quotient_indexed_initialized s).

Definition quotient_indexed_empty (hash : name -> N) : quotient_indexed_state hash :=
  {| quotient_indexed_base := seed_state hash [];
     quotient_indexed_initialized := false |}.

(* No separate delta, environment, lookup, or next flag is an input. *)
Definition quotient_indexed_step hash (s : quotient_indexed_state hash)
    : result (quotient_indexed_state hash) :=
  payload <- initialize_quotient_delta (quotient_indexed_project s) ;;
  Accept {| quotient_indexed_base := extend_state (quotient_indexed_base s) (fst payload);
            quotient_indexed_initialized := snd payload |}.

Definition quotient_indexed_project_result hash
    (r : result (quotient_indexed_state hash)) : result quotient_transaction_state :=
  result_map (@quotient_indexed_project hash) r.

Definition quotient_indexed_transaction hash (s : quotient_indexed_state hash)
    : quotient_indexed_state hash * result unit :=
  match quotient_indexed_step s with
  | Accept next => (next, Accept tt)
  | Reject reason => (s, Reject reason)
  | Decline reason => (s, Decline reason)
  end.

(* Fixed-hash candidate boundary. State is kernel-owned, NOT a deserialized
   transport record. No transport decoder or driver integration is supplied. *)
Definition quotient_runtime_state := quotient_indexed_state suffix_bitfold8.
Definition quotient_runtime_initial : quotient_runtime_state :=
  quotient_indexed_empty suffix_bitfold8.
Definition quotient_runtime_initialize (s : quotient_runtime_state) :=
  quotient_indexed_transaction s.

Lemma quotient_indexed_empty_projects hash :
  quotient_indexed_project (quotient_indexed_empty hash) = quotient_initial_state.
Proof. reflexivity. Qed.

Lemma quotient_indexed_step_refines hash (s : quotient_indexed_state hash) :
  quotient_indexed_project_result (quotient_indexed_step s) =
  initialize_quotient (quotient_indexed_project s).
Proof.
  rewrite <- (quotient_delta_refines (quotient_indexed_project s)).
  unfold quotient_indexed_project_result, quotient_indexed_step, attach_quotient_delta.
  destruct (initialize_quotient_delta (quotient_indexed_project s)); reflexivity.
Qed.

Lemma quotient_indexed_accepted_projection hash (s next : quotient_indexed_state hash) :
  quotient_indexed_step s = Accept next ->
  initialize_quotient (quotient_indexed_project s) =
    Accept (quotient_indexed_project next).
Proof.
  intro Run. pose proof (quotient_indexed_step_refines s) as Refines.
  unfold quotient_indexed_project_result in Refines. rewrite Run in Refines.
  cbn [result_map bind] in Refines. symmetry. exact Refines.
Qed.

Lemma quotient_indexed_success_shape hash (s next : quotient_indexed_state hash) :
  quotient_indexed_step s = Accept next ->
  next = {| quotient_indexed_base := extend_state (quotient_indexed_base s)
              (quotient_delta_prefix (quotient_indexed_project s));
            quotient_indexed_initialized := true |}.
Proof.
  unfold quotient_indexed_step.
  destruct (initialize_quotient_delta (quotient_indexed_project s))
    as [payload|err|reason] eqn:Delta; cbn [bind]; intro Run; try discriminate.
  pose proof (@quotient_delta_accepted_payload (quotient_indexed_project s)
    payload Delta) as Whole.
  rewrite Whole in Run. inversion Run. reflexivity.
Qed.

Lemma quotient_indexed_success_flag hash (s next : quotient_indexed_state hash) :
  quotient_indexed_step s = Accept next -> quotient_indexed_initialized next = true.
Proof.
  intro Run. rewrite (@quotient_indexed_success_shape hash s next Run). reflexivity.
Qed.

Lemma quotient_indexed_first_state_shape hash (s next : quotient_indexed_state hash) :
  quotient_indexed_initialized s = false ->
  quotient_indexed_step s = Accept next ->
  next = {| quotient_indexed_base := extend_state (quotient_indexed_base s)
              canonical_quotient_block;
            quotient_indexed_initialized := true |}.
Proof.
  intros Flag Run. pose proof (@quotient_indexed_success_shape hash s next Run) as Shape.
  unfold quotient_delta_prefix, quotient_indexed_project in Shape.
  cbn [fst snd] in Shape. rewrite Flag in Shape. exact Shape.
Qed.

Lemma quotient_indexed_first_length hash (s next : quotient_indexed_state hash) :
  quotient_indexed_initialized s = false ->
  quotient_indexed_step s = Accept next ->
  List.length (state_environment (quotient_indexed_base next)) =
    4 + List.length (state_environment (quotient_indexed_base s)).
Proof.
  intros Flag Run.
  rewrite (@quotient_indexed_first_state_shape hash s next Flag Run). reflexivity.
Qed.

Lemma quotient_indexed_lookup_correct hash (s : quotient_indexed_state hash) key :
  state_lookup (quotient_indexed_base s) key =
  find_decl key (fst (quotient_indexed_project s)).
Proof. apply state_lookup_correct. Qed.

Lemma quotient_indexed_lookup_after_success hash
    (s next : quotient_indexed_state hash) key :
  quotient_indexed_step s = Accept next ->
  state_lookup (quotient_indexed_base next) key =
    find_decl key (quotient_delta_prefix (quotient_indexed_project s) ++
      state_environment (quotient_indexed_base s)).
Proof.
  intro Run. rewrite quotient_indexed_lookup_correct.
  rewrite (@quotient_indexed_success_shape hash s next Run). reflexivity.
Qed.

(* Equality is of the actual stored environment/index data, not of proof fields.
   No proof-irrelevance axiom is needed to state this no-op property. *)
Lemma quotient_indexed_zero_prefix_data hash
    (s next : quotient_indexed_state hash) next_flag :
  initialize_quotient_delta (quotient_indexed_project s) = Accept ([], next_flag) ->
  quotient_indexed_step s = Accept next ->
  state_environment (quotient_indexed_base next) = state_environment (quotient_indexed_base s) /\
  state_index (quotient_indexed_base next) = state_index (quotient_indexed_base s) /\
  quotient_indexed_initialized next = next_flag.
Proof.
  intros Delta Run. unfold quotient_indexed_step in Run. rewrite Delta in Run.
  cbn [bind] in Run. inversion Run; subst. repeat split; reflexivity.
Qed.

Lemma quotient_indexed_initialized_data hash (s next : quotient_indexed_state hash) :
  quotient_indexed_initialized s = true ->
  quotient_indexed_step s = Accept next ->
  state_environment (quotient_indexed_base next) = state_environment (quotient_indexed_base s) /\
  state_index (quotient_indexed_base next) = state_index (quotient_indexed_base s) /\
  quotient_indexed_initialized next = true.
Proof.
  intros Flag Run. apply (@quotient_indexed_zero_prefix_data hash s next true).
  - unfold quotient_indexed_project. rewrite Flag. apply quotient_delta_initialized_empty.
  - exact Run.
Qed.

Lemma quotient_indexed_repeat_preserves_data hash
    (s next again : quotient_indexed_state hash) :
  quotient_indexed_step s = Accept next ->
  quotient_indexed_step next = Accept again ->
  state_environment (quotient_indexed_base again) = state_environment (quotient_indexed_base next) /\
  state_index (quotient_indexed_base again) = state_index (quotient_indexed_base next) /\
  quotient_indexed_initialized again = true.
Proof.
  intros First Again. apply quotient_indexed_initialized_data.
  - exact (@quotient_indexed_success_flag hash s next First).
  - exact Again.
Qed.

Lemma quotient_indexed_delta_reject hash (s : quotient_indexed_state hash) reason :
  initialize_quotient_delta (quotient_indexed_project s) = Reject reason ->
  quotient_indexed_step s = Reject reason.
Proof. intro H. unfold quotient_indexed_step. rewrite H. reflexivity. Qed.

Lemma quotient_indexed_delta_decline hash (s : quotient_indexed_state hash) reason :
  initialize_quotient_delta (quotient_indexed_project s) = Decline reason ->
  quotient_indexed_step s = Decline reason.
Proof. intro H. unfold quotient_indexed_step. rewrite H. reflexivity. Qed.

Lemma quotient_indexed_reject_rolls_back hash (s : quotient_indexed_state hash) reason :
  quotient_indexed_step s = Reject reason ->
  quotient_indexed_transaction s = (s, Reject reason).
Proof. intro H. unfold quotient_indexed_transaction. rewrite H. reflexivity. Qed.

Lemma quotient_indexed_decline_rolls_back hash (s : quotient_indexed_state hash) reason :
  quotient_indexed_step s = Decline reason ->
  quotient_indexed_transaction s = (s, Decline reason).
Proof. intro H. unfold quotient_indexed_transaction. rewrite H. reflexivity. Qed.

Lemma quotient_indexed_transaction_refines hash (s : quotient_indexed_state hash) :
  (let '(next, status) := quotient_indexed_transaction s in
    (quotient_indexed_project next, status)) =
  quotient_delta_transaction (quotient_indexed_project s).
Proof.
  unfold quotient_indexed_transaction. rewrite quotient_delta_transaction_refines.
  pose proof (quotient_indexed_step_refines s) as Refines.
  unfold quotient_indexed_project_result in Refines.
  destruct (quotient_indexed_step s); cbn [result_map bind] in Refines;
    rewrite <- Refines; reflexivity.
Qed.

(* Unexecuted assumption-audit requests, not proof receipts. *)
Print Assumptions quotient_indexed_step_refines.
Print Assumptions quotient_indexed_transaction_refines.
Print Assumptions quotient_indexed_first_length.
Print Assumptions quotient_indexed_lookup_after_success.
Print Assumptions quotient_indexed_zero_prefix_data.
Print Assumptions quotient_indexed_reject_rolls_back.
Print Assumptions quotient_indexed_decline_rolls_back.
