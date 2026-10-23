(* SPDX-License-Identifier: Apache-2.0
   Unsafe inductives use the same generation and metadata checks, with positivity
   disabled as upstream permits. Only the checking-local environment is opened;
   persistent declarations retain the marker rejected by safe inference. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker Declarations Safety NestedAdmission.
Import ListNotations.

Definition mark_unsafe_inductive (d : declaration) : declaration :=
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
     decl_type := decl_type d; decl_value := decl_value d;
     decl_kind_of := DUnsafe (decl_kind_of d) |}.

Definition inductive_input_unsafe (types : list declaration) : bool :=
  match types with
  | d::_ => match decl_kind_of d with DInductive i => ind_is_unsafe i | _ => false end
  | [] => false end.

Definition admit_inductive_extended (fuel : nat) (env : environment)
    (types ctors recs : list declaration) : result environment :=
  if inductive_input_unsafe types then
    let view := safety_environment InputUnsafe env in
    next <- admit_inductive_nested fuel view types ctors recs ;;
    let generated := filter (fun d =>
      match find_decl (decl_name d) env with None => true | _ => false end) next in
    Accept (List.app (map mark_unsafe_inductive generated) env)
  else admit_inductive_nested fuel env types ctors recs.

Lemma marked_inductive_retains_name d :
  decl_name (mark_unsafe_inductive d) = decl_name d.
Proof. reflexivity. Qed.

Lemma marked_inductive_stays_restricted d :
  decl_kind_of (checking_view InputSafe (mark_unsafe_inductive d)) =
    DUnsafe (decl_kind_of d).
Proof. reflexivity. Qed.

Lemma marked_inductive_unsafe_view d :
  decl_kind_of (checking_view InputUnsafe (mark_unsafe_inductive d)) = decl_kind_of d.
Proof. reflexivity. Qed.

Theorem unsafe_inductive_admission_preserves_restrictions fuel env types ctors recs next :
  inductive_input_unsafe types = true ->
  admit_inductive_extended fuel env types ctors recs = Accept next ->
  exists additions,
    next = List.app additions env /\
    Forall (fun d => exists kind, decl_kind_of d = DUnsafe kind) additions.
Proof.
  intros Hmode Haccepted.
  unfold admit_inductive_extended in Haccepted. rewrite Hmode in Haccepted.
  destruct (admit_inductive_nested fuel (safety_environment InputUnsafe env)
    types ctors recs) as [checked|err|reason] eqn:Hchecked;
    simpl in Haccepted; try discriminate.
  inversion Haccepted; subst next.
  eexists. split; [reflexivity |].
  apply Forall_forall. intros d Hin. apply in_map_iff in Hin.
  destruct Hin as [source [Heq Hin]]. subst d.
  exists (decl_kind_of source). reflexivity.
Qed.

Print Assumptions unsafe_inductive_admission_preserves_restrictions.
