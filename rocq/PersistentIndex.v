(* SPDX-License-Identifier: Apache-2.0
   Immutable environment/index pairs. The invariant is constructed in Gallina,
   never supplied by the transport frontend or assumed about an environment. *)
From Stdlib Require Import List NArith.
From LeanPort Require Import Syntax EnvironmentIndex.
Import ListNotations.
Set Implicit Arguments.

Record indexed_state (hash : name -> N) : Type := {
  state_environment : environment;
  state_index : declaration_index;
  state_matches : declaration_index_matches hash state_environment state_index
}.

Definition seed_state hash env : indexed_state hash :=
  {| state_environment := env; state_index := index_environment hash env;
     state_matches := index_environment_matches hash env |}.

Fixpoint prepend_index hash (added : list declaration) index :=
  match added with
  | [] => index
  | d :: rest => index_declaration hash d (prepend_index hash rest index)
  end.

Lemma prepend_index_matches hash added env index :
  declaration_index_matches hash env index ->
  declaration_index_matches hash (added ++ env) (prepend_index hash added index).
Proof.
  intro H. induction added as [|d rest IH]; cbn [app prepend_index].
  - exact H.
  - apply index_declaration_matches. exact IH.
Qed.

Definition extend_state hash (s : indexed_state hash) added : indexed_state hash :=
  {| state_environment := added ++ state_environment s;
     state_index := prepend_index hash added (state_index s);
     state_matches := prepend_index_matches added (state_matches s) |}.

Definition state_lookup hash (s : indexed_state hash) n :=
  indexed_find_decl hash n (state_index s).

Theorem state_lookup_correct hash (s : indexed_state hash) n :
  state_lookup s n = find_decl n (state_environment s).
Proof. apply indexed_find_decl_refines, state_matches. Qed.

Lemma extend_state_environment hash (s : indexed_state hash) added :
  state_environment (extend_state s added) = added ++ state_environment s.
Proof. reflexivity. Qed.

Print Assumptions state_lookup_correct.
Print Assumptions prepend_index_matches.
