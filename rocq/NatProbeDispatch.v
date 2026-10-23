(* SPDX-License-Identifier: Apache-2.0
   Exact negative dispatch adapted from the parent NatProbeHead.v sidecar.
   Parent source SHA: e05aeb7241708b4b36eb6393821028bbdd4230fa46fca8351d6c902d5223aa51. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax.
Import ListNotations.

Definition nat_probe_head
    (resolve : name -> environment -> option declaration) (succ_name : name)
    (env : environment) (view : expr * list expr) : bool :=
  let '(head, args) := view in
  match head, args with
  | EConst n [], [_] =>
      if name_eqb n succ_name then true else
      match resolve n env with
      | Some d => match decl_kind_of d with
                  | DPrimitive PNatPred => true | _ => false end
      | None => false
      end
  | EConst n [], [_; _] =>
      match resolve n env with
      | Some d => match decl_kind_of d with
                  | DPrimitive PNatBitwise => false
                  | DPrimitive _ => true
                  | _ => false end
      | None => false
      end
  | _, _ => false
  end.

Definition pair_probe_guard (left right : bool) (eligible : unit -> bool) : bool :=
  if left || right then eligible tt else false.

Lemma pair_probe_left_exact {A} left right eligible (probe : result (option A)) :
  (left = false -> probe = Accept None) ->
  (if pair_probe_guard left right eligible then probe else Accept None) =
    (if eligible tt then probe else Accept None).
Proof.
  intro H. unfold pair_probe_guard. destruct left, right; simpl; try reflexivity.
  rewrite (H eq_refl). destruct (eligible tt); reflexivity.
Qed.

Lemma pair_probe_right_exact {A} left right eligible (probe : result (option A)) :
  (right = false -> probe = Accept None) ->
  (if pair_probe_guard left right eligible then probe else Accept None) =
    (if eligible tt then probe else Accept None).
Proof.
  intro H. unfold pair_probe_guard. destruct left, right; simpl; try reflexivity.
  rewrite (H eq_refl). destruct (eligible tt); reflexivity.
Qed.

Print Assumptions pair_probe_left_exact.
Print Assumptions pair_probe_right_exact.
