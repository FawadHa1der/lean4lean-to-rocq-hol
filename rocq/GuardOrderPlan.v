(* SPDX-License-Identifier: Apache-2.0
   Complete results, proved before changing the candidate's guard sites. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax EagerPolicy NatProbeDispatch Checker LookupCore.
Import ListNotations.

Theorem ordinary_inactive_nat_probe rec fuel env g e :
  nat_probe_head find_decl Checker.core_succ_name env (Checker.core_spine e []) = false ->
  Checker.core_reduce_nat rec fuel env g e = Accept None.
Proof.
  unfold nat_probe_head, Checker.core_reduce_nat.
  destruct (Checker.core_spine e []) as [head args].
  destruct head; try (intros; reflexivity).
  destruct l; try (intros; reflexivity).
  destruct args as [|a [|b [|c args]]]; try (intros; reflexivity).
  all: repeat match goal with
  | |- context [name_eqb ?n ?m] => destruct (name_eqb n m)
  | |- context [find_decl ?n ?env] => destruct (find_decl n env)
  | |- context [decl_kind_of ?d] => destruct (decl_kind_of d)
  | op : primitive_kind |- _ => destruct op
  end; intros H; try discriminate; reflexivity.
Qed.

Theorem accessor_inactive_nat_probe resolve rec fuel env g e :
  nat_probe_head resolve Accessor.core_succ_name env (Accessor.core_spine e []) = false ->
  Accessor.core_reduce_nat resolve rec fuel env g e = Accept None.
Proof.
  unfold nat_probe_head, Accessor.core_reduce_nat.
  destruct (Accessor.core_spine e []) as [head args].
  destruct head; try (intros; reflexivity).
  destruct l; try (intros; reflexivity).
  destruct args as [|a [|b [|c args]]]; try (intros; reflexivity).
  all: repeat match goal with
  | |- context [name_eqb ?n ?m] => destruct (name_eqb n m)
  | |- context [match ?entry with Some _ => _ | None => _ end] =>
      let T := type of entry in unify T (option declaration); destruct entry
  | |- context [decl_kind_of ?d] => destruct (decl_kind_of d)
  | op : primitive_kind |- _ => destruct op
  end; intros H; try discriminate; reflexivity.
Qed.

Theorem ordinary_true_guard_reorder rec env g t s :
  (if Checker.core_is_true s && true_probe_allowed (method_mode rec) t && Checker.core_bool_ready env
   then bind (whnf_method rec g t) (fun tn => Accept (Checker.core_is_true tn))
   else Accept false) =
  (if true_probe_allowed (method_mode rec) t && Checker.core_is_true s && Checker.core_bool_ready env
   then bind (whnf_method rec g t) (fun tn => Accept (Checker.core_is_true tn))
   else Accept false).
Proof. rewrite (Bool.andb_comm (Checker.core_is_true s)). reflexivity. Qed.

Theorem accessor_true_guard_reorder resolve rec env g t s :
  (if Checker.core_is_true s && true_probe_allowed (method_mode rec) t && Accessor.core_bool_ready resolve env
   then bind (whnf_method rec g t) (fun tn => Accept (Checker.core_is_true tn))
   else Accept false) =
  (if true_probe_allowed (method_mode rec) t && Checker.core_is_true s && Accessor.core_bool_ready resolve env
   then bind (whnf_method rec g t) (fun tn => Accept (Checker.core_is_true tn))
   else Accept false).
Proof. rewrite (Bool.andb_comm (Checker.core_is_true s)). reflexivity. Qed.

Print Assumptions ordinary_inactive_nat_probe.
Print Assumptions accessor_inactive_nat_probe.
Print Assumptions ordinary_true_guard_reorder.
Print Assumptions accessor_true_guard_reorder.
