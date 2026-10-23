(* SPDX-License-Identifier: Apache-2.0
   Incremental checked admission. The transport never constructs an index,
   supplies a lookup, or commits caller-selected declarations. *)
From Stdlib Require Import List NArith.
From LeanPort Require Import Syntax Checker Declarations DagScope DagArena
  DagAdmission DagTheoremOpaque IndexedDagAdmission CombinedAdmissionRefinement
  LookupIntegration LookupRefinement RuntimeChecker PersistentIndex AdmissionDelta
  Safety InductiveSafety Quotient.
Import ListNotations.
Set Implicit Arguments.

Lemma preparation_refines prepare kind budget fuel env n ps rows tr br :
  (forall key, prepare tt key = find_decl key env) ->
  admit_with_preparation prepare kind budget fuel env n ps rows tr br =
    linear_env_admit kind budget fuel env n ps rows tr br.
Proof.
  intro Lookup. unfold admit_with_preparation, linear_env_admit.
  destruct kind; unfold DagAdmission.admit_dag_definition,
    DagTheoremOpaque.admit_dag_theorem, DagTheoremOpaque.admit_dag_opaque;
    destruct (arena_build empty_arena rows) eqn:Build; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) tr) eqn:Htype; cbn [bind]; try reflexivity;
    destruct (scope_ref (arena_scope d) br) eqn:Hbody; cbn [bind]; try reflexivity.
  all: apply early_in_arena_refines; auto;
    eapply arena_build_ok; [apply empty_arena_ok|exact Build].
Qed.

Definition cached_dag_admit hash (s : indexed_state hash) kind budget fuel n ps rows tr br :=
  let env := state_environment s in
  if RuntimeChecker.use_index fuel env then
    admit_with_preparation (fun _ => state_lookup s) kind budget fuel env n ps rows tr br
  else linear_env_admit kind budget fuel env n ps rows tr br.

Theorem cached_dag_refines hash (s : indexed_state hash) kind budget fuel n ps rows tr br :
  cached_dag_admit s kind budget fuel n ps rows tr br =
    indexed_dag_admit kind budget fuel (state_environment s) n ps rows tr br.
Proof.
  unfold cached_dag_admit, indexed_dag_admit.
  destruct (RuntimeChecker.use_index fuel (state_environment s)); [|reflexivity].
  rewrite indexed_admit_refines. apply preparation_refines, state_lookup_correct.
Qed.

Lemma cached_dag_single hash (s : indexed_state hash) kind budget fuel n ps rows tr br :
  single_extension (state_environment s)
    (cached_dag_admit s kind budget fuel n ps rows tr br).
Proof.
  rewrite cached_dag_refines, combined_guarded_refines_new_ordinary.
  unfold new_ordinary_decode_admit.
  repeat (apply single_bind; intro). apply admit_single.
Qed.

Inductive admission_batch : Type :=
| BatchDag : dag_admission_kind -> nat -> name -> list name ->
    list (positive * dag_node) -> positive -> positive -> admission_batch
| BatchOrdinary : input_decl -> admission_batch
| BatchQuotient : name -> list name -> expr -> quotient_kind -> admission_batch
| BatchInductive : list declaration -> list declaration -> list declaration -> admission_batch
| BatchMutual : list input_decl -> admission_batch.

Definition reference_batch fuel env request : result environment :=
  match request with
  | BatchDag kind budget n ps rows tr br => indexed_dag_admit kind budget fuel env n ps rows tr br
  | BatchOrdinary input => admit_extended fuel env input
  | BatchQuotient n ps ty kind => admit_quotient fuel env n ps ty kind
  | BatchInductive types ctors recs => admit_inductive_extended fuel env types ctors recs
  | BatchMutual inputs => admit_mutual fuel env inputs
  end.

Definition batch_delta hash fuel (s : indexed_state hash) request : result environment :=
  let env := state_environment s in
  match request with
  | BatchDag kind budget n ps rows tr br => single_delta (cached_dag_admit s kind budget fuel n ps rows tr br)
  | BatchOrdinary input => single_delta (admit_extended fuel env input)
  | BatchQuotient n ps ty kind => single_delta (admit_quotient fuel env n ps ty kind)
  | BatchInductive types ctors recs => inductive_delta fuel env types ctors recs
  | BatchMutual inputs => mutual_delta fuel env inputs
  end.

Theorem batch_delta_refines hash fuel (s : indexed_state hash) request :
  attach_prefix (state_environment s) (batch_delta fuel s request) =
    reference_batch fuel (state_environment s) request.
Proof.
  destruct request; cbn [batch_delta reference_batch].
  - rewrite single_delta_exact by apply cached_dag_single. apply cached_dag_refines.
  - apply single_delta_exact, extended_single.
  - apply single_delta_exact, quotient_single.
  - apply inductive_delta_exact.
  - apply mutual_delta_exact.
Qed.

Definition state_step hash fuel (s : indexed_state hash) request : result (indexed_state hash) :=
  added <- batch_delta fuel s request ;; Accept (extend_state s added).
Definition project_result hash (r : result (indexed_state hash)) := result_map (@state_environment hash) r.

Theorem state_step_refines hash fuel (s : indexed_state hash) request :
  project_result (state_step fuel s request) = reference_batch fuel (state_environment s) request.
Proof.
  pose proof (batch_delta_refines fuel s request) as H.
  unfold state_step, project_result. destruct (batch_delta fuel s request);
    cbn [result_map bind state_environment extend_state attach_prefix] in *; exact H.
Qed.

Corollary persistent_dag_refines_linear_cache_new hash fuel (s : indexed_state hash)
    kind budget n ps rows tr br :
  project_result (state_step fuel s (BatchDag kind budget n ps rows tr br)) =
    linear_cache_new_admit kind budget fuel (state_environment s) n ps rows tr br.
Proof. rewrite state_step_refines. apply combined_guarded_refines_linear_cache_new. Qed.

Corollary persistent_dag_refines_new_ordinary hash fuel (s : indexed_state hash)
    kind budget n ps rows tr br :
  project_result (state_step fuel s (BatchDag kind budget n ps rows tr br)) =
    new_ordinary_decode_admit kind fuel (state_environment s) n ps rows tr br.
Proof. rewrite state_step_refines. apply combined_guarded_refines_new_ordinary. Qed.

Definition transaction hash fuel (s : indexed_state hash) request : indexed_state hash * result unit :=
  match state_step fuel s request with
  | Accept next => (next,Accept tt)
  | Reject reason => (s,Reject reason)
  | Decline reason => (s,Decline reason)
  end.

Theorem reject_rolls_back hash fuel (s : indexed_state hash) request reason :
  state_step fuel s request = Reject reason -> transaction fuel s request = (s,Reject reason).
Proof. intro H. unfold transaction. now rewrite H. Qed.
Theorem decline_rolls_back hash fuel (s : indexed_state hash) request reason :
  state_step fuel s request = Decline reason -> transaction fuel s request = (s,Decline reason).
Proof. intro H. unfold transaction. now rewrite H. Qed.

Fixpoint state_stream hash fuel (s : indexed_state hash) requests : result (indexed_state hash) :=
  match requests with
  | [] => Accept s
  | request :: rest => next <- state_step fuel s request ;; state_stream fuel next rest
  end.
Fixpoint reference_stream fuel env requests : result environment :=
  match requests with
  | [] => Accept env
  | request :: rest => next <- reference_batch fuel env request ;; reference_stream fuel next rest
  end.

Theorem state_stream_refines hash fuel requests : forall s : indexed_state hash,
  project_result (state_stream fuel s requests) = reference_stream fuel (state_environment s) requests.
Proof.
  induction requests as [|request rest IH]; intro s; cbn [state_stream reference_stream].
  - reflexivity.
  - rewrite <- (state_step_refines fuel s request).
    unfold project_result at 1 2. destruct (state_step fuel s request);
      cbn [bind result_map]; try reflexivity. apply IH.
Qed.

Corollary initialized_stream_refines hash fuel env requests :
  project_result (state_stream fuel (seed_state hash env) requests) =
    reference_stream fuel env requests.
Proof. apply state_stream_refines. Qed.

(* Fixed-hash public frontend boundary: no hash, lookup, index, environment,
   invariant proof, or addition list is supplied separately by the frontend. *)
Definition runtime_state := indexed_state suffix_bitfold8.
Definition initial_state : runtime_state := seed_state suffix_bitfold8 [].
Definition admit_batch fuel (s : runtime_state) request := state_step fuel s request.
Definition runtime_transaction fuel (s : runtime_state) request := transaction fuel s request.

Print Assumptions cached_dag_refines.
Print Assumptions batch_delta_refines.
Print Assumptions state_step_refines.
Print Assumptions persistent_dag_refines_linear_cache_new.
Print Assumptions persistent_dag_refines_new_ordinary.
Print Assumptions state_stream_refines.
Print Assumptions initialized_stream_refines.
Print Assumptions reject_rolls_back.
Print Assumptions decline_rolls_back.
