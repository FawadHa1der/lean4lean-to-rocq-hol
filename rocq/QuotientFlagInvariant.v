(* SPDX-License-Identifier: Apache-2.0
   SOURCE ONLY: proposed invariant proofs, not compiled or integrated.
   A true internal initialization flag implies visible canonical declarations.
   This is not typing soundness or equivalence of quotient reduction rules. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Declarations Safety Quotient QuotientTransaction
  QuotientTransactionDelta.
Import ListNotations.

Definition quotient_flag_sound (state : quotient_transaction_state) : Prop :=
  snd state = true -> forall kind,
    find_decl (decl_name (canonical_quotient kind)) (fst state) =
      Some (canonical_quotient kind).

(* This condition is a proof obligation on checked admission, not permission
   for transport to choose an extension or supply an erased proof. *)
Definition quotient_prefix_fresh (prefix env : environment) : Prop :=
  forall d, In d prefix -> find_decl (decl_name d) env = None.

Definition quotient_flag_extend prefix (state : quotient_transaction_state) :=
  (prefix ++ fst state, snd state).

Lemma quotient_canonical_block_visible env kind :
  find_decl (decl_name (canonical_quotient kind))
    (canonical_quotient_block ++ env) = Some (canonical_quotient kind).
Proof. destruct kind; reflexivity. Qed.

Lemma quotient_initial_flag_sound : quotient_flag_sound quotient_initial_state.
Proof. unfold quotient_flag_sound, quotient_initial_state. discriminate. Qed.

Lemma quotient_installed_flag_sound env :
  quotient_flag_sound (canonical_quotient_block ++ env, true).
Proof. intros _ kind. apply quotient_canonical_block_visible. Qed.

Lemma quotient_initialize_preserves_flag_sound state next :
  quotient_flag_sound state -> initialize_quotient state = Accept next ->
  quotient_flag_sound next.
Proof.
  destruct state as [env initialized]. destruct initialized; intros Valid Run.
  - rewrite quotient_initialized_noop in Run. inversion Run; subst. exact Valid.
  - apply quotient_transaction_no_partial_commit in Run. subst next.
    apply quotient_installed_flag_sound.
Qed.

Lemma quotient_delta_preserves_flag_sound state next :
  quotient_flag_sound state -> quotient_delta_step state = Accept next ->
  quotient_flag_sound next.
Proof.
  intros Valid Run. rewrite quotient_delta_step_refines in Run.
  exact (quotient_initialize_preserves_flag_sound state next Valid Run).
Qed.

Lemma quotient_transaction_preserves_flag_sound state :
  quotient_flag_sound state ->
  quotient_flag_sound (fst (quotient_delta_transaction state)).
Proof.
  intro Valid. unfold quotient_delta_transaction.
  destruct (quotient_delta_step state) as [next|reason|reason] eqn:Run;
    cbn [fst].
  - exact (quotient_delta_preserves_flag_sound state next Valid Run).
  - exact Valid.
  - exact Valid.
Qed.

Lemma quotient_fresh_prefix_preserves_lookup prefix env n d :
  quotient_prefix_fresh prefix env -> find_decl n env = Some d ->
  find_decl n (prefix ++ env) = Some d.
Proof.
  induction prefix as [|head rest IH]; intros Fresh Found; cbn [app find_decl].
  - exact Found.
  - destruct (name_eqb n (decl_name head)) eqn:Same.
    + apply name_eqb_eq in Same. subst n.
      pose proof (Fresh head (or_introl eq_refl)) as Missing.
      rewrite Found in Missing. discriminate.
    + apply IH.
      * intros entry InRest. apply Fresh. right. exact InRest.
      * exact Found.
Qed.

Lemma quotient_fresh_extension_preserves_flag_sound prefix state :
  quotient_flag_sound state -> quotient_prefix_fresh prefix (fst state) ->
  quotient_flag_sound (quotient_flag_extend prefix state).
Proof.
  intros Valid Fresh Initialized kind.
  apply quotient_fresh_prefix_preserves_lookup.
  - exact Fresh.
  - apply Valid. exact Initialized.
Qed.

Lemma quotient_header_requires_fresh_name fuel env n ps ty :
  check_header fuel env n ps ty = Accept tt -> find_decl n env = None.
Proof.
  unfold check_header. destruct (find_decl n env) eqn:Found;
    intro Run; [discriminate|reflexivity].
Qed.

Lemma quotient_safety_view_absence mode env n :
  find_decl n (safety_environment mode env) = None <-> find_decl n env = None.
Proof.
  induction env as [|d rest IH]; cbn [safety_environment map find_decl checking_view decl_name].
  - reflexivity.
  - destruct (name_eqb n (decl_name d)).
    + split; discriminate.
    + exact IH.
Qed.

Lemma quotient_view_header_requires_fresh_name fuel mode env n ps ty :
  check_header fuel (safety_environment mode env) n ps ty = Accept tt ->
  find_decl n env = None.
Proof.
  intro Header. apply (proj1 (quotient_safety_view_absence mode env n)).
  eapply quotient_header_requires_fresh_name. exact Header.
Qed.

Lemma quotient_header_checked_extension_preserves_flag fuel state d :
  quotient_flag_sound state ->
  check_header fuel (fst state) (decl_name d) (decl_params d) (decl_type d) = Accept tt ->
  quotient_flag_sound (quotient_flag_extend [d] state).
Proof.
  intros Valid Header. apply quotient_fresh_extension_preserves_flag_sound.
  - exact Valid.
  - intros entry [Equal|Impossible].
    + subst entry. eapply quotient_header_requires_fresh_name. exact Header.
    + contradiction.
Qed.

(* An overapproximate history for this ONE invariant. Fresh extensions need
   not be well typed. No claim says actual batch admission satisfies Fresh. *)
Inductive quotient_flag_history : quotient_transaction_state -> Prop :=
| quotient_history_initial : quotient_flag_history quotient_initial_state
| quotient_history_initialize state next :
    quotient_flag_history state -> initialize_quotient state = Accept next ->
    quotient_flag_history next
| quotient_history_extend prefix state :
    quotient_flag_history state -> quotient_prefix_fresh prefix (fst state) ->
    quotient_flag_history (quotient_flag_extend prefix state).

Theorem quotient_history_flag_sound state :
  quotient_flag_history state -> quotient_flag_sound state.
Proof.
  intro History. induction History.
  - apply quotient_initial_flag_sound.
  - eapply quotient_initialize_preserves_flag_sound; eassumption.
  - eapply quotient_fresh_extension_preserves_flag_sound; eassumption.
Qed.

(* The function's no-op law alone cannot authenticate an initialized state. *)
Example quotient_forged_true_is_not_sound :
  ~ quotient_flag_sound ([], true).
Proof.
  intro Valid. pose proof (Valid eq_refl QType) as Impossible.
  discriminate Impossible.
Qed.

Example quotient_forged_true_still_noops :
  initialize_quotient ([], true) = Accept ([], true).
Proof. reflexivity. Qed.

Print Assumptions quotient_initialize_preserves_flag_sound.
Print Assumptions quotient_transaction_preserves_flag_sound.
Print Assumptions quotient_fresh_prefix_preserves_lookup.
Print Assumptions quotient_view_header_requires_fresh_name.
Print Assumptions quotient_header_checked_extension_preserves_flag.
Print Assumptions quotient_history_flag_sound.
