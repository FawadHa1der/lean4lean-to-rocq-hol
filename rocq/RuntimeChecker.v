(* SPDX-License-Identifier: Apache-2.0
   Private performance candidate only; no production API has changed. *)
From LeanPort Require Export Checker IndexedChecker EnvironmentIndexSuffixBenchmark.

Fixpoint at_least (count : nat) (env : Syntax.environment) : bool :=
  match count, env with
  | O, _ => true
  | S _, nil => false
  | S count, cons _ rest => at_least count rest
  end.
Definition use_index fuel env :=
  match fuel with O => false | S _ => at_least 64 env end.
Definition checker fuel env ps :=
  if use_index fuel env then Indexed.checker suffix_bitfold8 fuel env ps
  else Checker.checker fuel env ps.
Definition infer fuel env ps g e :=
  if use_index fuel env then Indexed.infer suffix_bitfold8 fuel env ps g e
  else Checker.infer fuel env ps g e.
Definition whnf fuel env ps g e :=
  if use_index fuel env then Indexed.whnf suffix_bitfold8 fuel env ps g e
  else Checker.whnf fuel env ps g e.
Definition defeq fuel env ps g a b :=
  if use_index fuel env then Indexed.defeq suffix_bitfold8 fuel env ps g a b
  else Checker.defeq fuel env ps g a b.
Definition check fuel env ps g e ty :=
  if use_index fuel env then Indexed.check suffix_bitfold8 fuel env ps g e ty
  else Checker.check fuel env ps g e ty.
Definition check_defeq fuel env ps g a b :=
  if use_index fuel env then Indexed.check_defeq suffix_bitfold8 fuel env ps g a b
  else Checker.check_defeq fuel env ps g a b.

Theorem runtime_infer_refines fuel env ps g e :
  infer fuel env ps g e = Checker.infer fuel env ps g e.
Proof. unfold infer. destruct (use_index fuel env); auto using indexed_infer_refines. Qed.
Theorem runtime_check_refines fuel env ps g e ty :
  check fuel env ps g e ty = Checker.check fuel env ps g e ty.
Proof. unfold check. destruct (use_index fuel env); auto using indexed_check_refines. Qed.
Theorem runtime_checker_refines fuel env ps :
  LookupRefinement.methods_equivalent (checker fuel env ps) (Checker.checker fuel env ps).
Proof. unfold checker. destruct (use_index fuel env);
  auto using indexed_checker_refines, LookupRefinement.methods_equivalent_refl. Qed.
Theorem runtime_whnf_refines fuel env ps g e :
  whnf fuel env ps g e = Checker.whnf fuel env ps g e.
Proof. unfold whnf. destruct (use_index fuel env); auto using indexed_whnf_refines. Qed.
Theorem runtime_defeq_refines fuel env ps g a b :
  defeq fuel env ps g a b = Checker.defeq fuel env ps g a b.
Proof. unfold defeq. destruct (use_index fuel env); auto using indexed_defeq_refines. Qed.
Theorem runtime_check_defeq_refines fuel env ps g a b :
  check_defeq fuel env ps g a b = Checker.check_defeq fuel env ps g a b.
Proof. unfold check_defeq. destruct (use_index fuel env); auto using indexed_check_defeq_refines. Qed.
Print Assumptions runtime_infer_refines.
Print Assumptions runtime_check_refines.
