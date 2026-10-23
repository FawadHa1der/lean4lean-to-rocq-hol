(* SPDX-License-Identifier: Apache-2.0
   Upstream application orientation and NEW ordinary full-result refinements.
   No old/new same-fuel equality is asserted. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax EagerPolicy Checker LookupCore LookupRefinement
  IndexedChecker DagArena DagQuery ReferenceDagQuery DagInfer ReferenceDagInfer
  IndexedDagInfer EagerPolicyRegression.

Theorem application_upstream_order rec g argument domain argument_type :
  application_type_defeq rec g argument domain argument_type =
  (if is_eager_reduce_argument argument then eager_defeq_method rec else defeq_method rec)
    g domain argument_type.
Proof. unfold application_type_defeq. destruct (is_eager_reduce_argument argument); reflexivity. Qed.

Theorem unmarked_application_full_result rec g argument domain argument_type answer :
  is_eager_reduce_argument argument = false ->
  defeq_method rec g domain argument_type = answer ->
  application_type_defeq rec g argument domain argument_type = answer.
Proof. intros H R. rewrite unmarked_application_order by exact H. exact R. Qed.

Theorem marked_application_full_result rec g argument domain argument_type answer :
  is_eager_reduce_argument argument = true ->
  eager_defeq_method rec g domain argument_type = answer ->
  application_type_defeq rec g argument domain argument_type = answer.
Proof. intros H R. rewrite marked_application_order by exact H. exact R. Qed.

Theorem application_inference_only_order rec g argument domain argument_type :
  application_type_defeq (inference_only rec) g argument domain argument_type =
  application_type_defeq rec g argument domain argument_type.
Proof. unfold application_type_defeq, inference_only. destruct (is_eager_reduce_argument argument); reflexivity. Qed.

Theorem new_order_accessor_inference_full_result resolve env
    (lookup_correct : forall n, resolve n env = find_decl n env)
    a b fuel ps checking g e : methods_equivalent a b ->
  Accessor.infer_step resolve a fuel env ps checking g e =
    Checker.infer_step b fuel env ps checking g e.
Proof. apply infer_step_refines. exact lookup_correct. Qed.

Theorem new_order_prepared_methods mode fuel env lookup ps :
  (forall n, lookup n = find_decl n env) ->
  methods_equivalent (checker_with_lookup_mode mode fuel env lookup ps)
    (Checker.checker_mode mode fuel env ps).
Proof. apply checker_with_lookup_mode_refines. Qed.

Theorem new_order_ordinary_dag_full_result rec fuel env ps base arena budget checking q :
  arena_ok arena ->
  DagInfer.run_memo_infer rec fuel env ps base arena budget checking q =
    DagQuery.step_eval rec fuel env ps base arena checking q.
Proof. apply DagInfer.run_memo_infer_refines. Qed.

Theorem new_order_reference_dag_full_result rec fuel env ps base arena budget checking q :
  arena_ok arena ->
  ReferenceDagInfer.run_memo_infer rec fuel env ps base arena budget checking q =
    ReferenceDagQuery.step_eval rec fuel env ps base arena checking q.
Proof. apply ReferenceDagInfer.run_memo_infer_refines. Qed.

Theorem new_order_indexed_dag_full_result lookup rec fuel env ps base arena budget checking q :
  (forall n, lookup n = find_decl n env) -> arena_ok arena ->
  IndexedDagInfer.run_memo_infer lookup rec fuel env ps base arena budget checking q =
    DagQuery.step_eval rec fuel env ps base arena checking q.
Proof. intros Hlookup Harena. apply IndexedDagInfer.run_memo_infer_refines; assumption. Qed.

Print Assumptions application_upstream_order.
Print Assumptions unmarked_application_full_result.
Print Assumptions marked_application_full_result.
Print Assumptions application_inference_only_order.
Print Assumptions new_order_accessor_inference_full_result.
Print Assumptions new_order_prepared_methods.
Print Assumptions new_order_ordinary_dag_full_result.
Print Assumptions new_order_reference_dag_full_result.
Print Assumptions new_order_indexed_dag_full_result.
