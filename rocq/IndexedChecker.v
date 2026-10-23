(* SPDX-License-Identifier: Apache-2.0
   Private list-API wrapper. The hash is a computational parameter until chosen.
   No accessor, index, or readiness assertion is supplied by the frontend. *)
From Stdlib Require Import List Bool NArith.
From LeanPort Require Import Syntax Universes EagerPolicy Checker EnvironmentIndex
  LookupIntegration LookupCore LookupRefinement.
Import ListNotations.

(* env is carried to preserve the exact reference factorization. The prepared
   accessor closes over this same env, and never constructs another index. *)
Definition checker_with_lookup_mode (mode : reduction_mode) (fuel : nat) (env : environment)
    (lookup : declaration_lookup) (ps : list name) : methods :=
  Accessor.checker_mode (fun n _ => lookup n) mode fuel env ps.

Definition checker_with_lookup := checker_with_lookup_mode NormalReduction.

Theorem checker_with_lookup_mode_refines mode fuel env lookup ps :
  (forall n, lookup n = find_decl n env) ->
  methods_equivalent (checker_with_lookup_mode mode fuel env lookup ps)
    (Checker.checker_mode mode fuel env ps).
Proof. intro H. apply checker_mode_lookup_refines. exact H. Qed.

Theorem checker_with_lookup_refines fuel env lookup ps :
  (forall n, lookup n = find_decl n env) ->
  methods_equivalent (checker_with_lookup fuel env lookup ps) (Checker.checker fuel env ps).
Proof. intro H. apply checker_lookup_refines. exact H. Qed.

Definition supported_with_lookup (lookup : declaration_lookup) env e :=
  Accessor.core_supported (fun n _ => lookup n) env e.

Definition defeq_with_methods lookup env (m : methods) g t s : result bool :=
  if supported_with_lookup lookup env t && supported_with_lookup lookup env s
  then defeq_method m g t s else Decline UnsupportedExpression.

(* Zero fuel declines before index construction. A positive entry prepares once,
   including the multiple inference/conversion calls made by check/check_defeq. *)
Definition with_prepared {A} (hash : name -> N) fuel env ps
    (run : declaration_lookup -> methods -> result A) : result A :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S _ =>
      let lookup := prepare_lookup hash env in
      run lookup (checker_with_lookup fuel env lookup ps)
  end.

Module Indexed.
Definition checker_mode mode hash fuel env ps : methods :=
  match fuel with
  | 0 => Checker.checker_mode mode 0 env ps
  | S _ => let lookup := prepare_lookup hash env in checker_with_lookup_mode mode fuel env lookup ps
  end.
Definition checker := checker_mode NormalReduction.
Definition infer hash fuel env ps g e : result expr :=
  with_prepared hash fuel env ps (fun _ m => infer_method m g e).
Definition whnf hash fuel env ps g e : result expr :=
  with_prepared hash fuel env ps (fun lookup m =>
    if supported_with_lookup lookup env e then whnf_method m g e
    else Decline UnsupportedExpression).
Definition defeq hash fuel env ps g t s : result bool :=
  with_prepared hash fuel env ps (fun lookup m => defeq_with_methods lookup env m g t s).
Definition check hash fuel env ps g e ty : result unit :=
  with_prepared hash fuel env ps (fun lookup m =>
    ignored <- Checker.sort_of m g ty ;;
    et <- infer_method m g e ;;
    ok <- defeq_with_methods lookup env m g et ty ;;
    require ok TypeMismatch).
Definition check_defeq hash fuel env ps g t s : result unit :=
  with_prepared hash fuel env ps (fun lookup m =>
    tt <- infer_method m g t ;;
    st <- infer_method m g s ;;
    same_type <- defeq_with_methods lookup env m g tt st ;;
    ignored <- require same_type TypeMismatch ;;
    same_term <- defeq_with_methods lookup env m g t s ;;
    require same_term NotDefinitionallyEqual).
End Indexed.

Lemma prepared_methods_mode_refine mode hash fuel env ps :
  methods_equivalent (checker_with_lookup_mode mode fuel env (prepare_lookup hash env) ps)
    (Checker.checker_mode mode fuel env ps).
Proof. apply checker_with_lookup_mode_refines. apply prepare_lookup_correct. Qed.

Lemma prepared_methods_refine hash fuel env ps :
  methods_equivalent (checker_with_lookup fuel env (prepare_lookup hash env) ps)
    (Checker.checker fuel env ps).
Proof. apply checker_with_lookup_refines. apply prepare_lookup_correct. Qed.

Lemma prepared_supported_refines hash env e :
  supported_with_lookup (prepare_lookup hash env) env e = Checker.core_supported env e.
Proof. apply core_supported_refines. apply prepare_lookup_correct. Qed.

#[local] Hint Resolve same_infer same_infer_type same_whnf same_whnf_core same_defeq
  prepared_methods_refine prepared_supported_refines sort_of_refines : lookup_refinement.

Lemma prepared_defeq_refines hash fuel env ps g t s :
  defeq_with_methods (prepare_lookup hash env) env
    (checker_with_lookup (S fuel) env (prepare_lookup hash env) ps) g t s =
    Checker.defeq (S fuel) env ps g t s.
Proof.
  unfold defeq_with_methods, Checker.defeq. cbn beta iota zeta.
  repeat rewrite prepared_supported_refines.
  destruct (Checker.core_supported env t && Checker.core_supported env s);
    [apply same_defeq, prepared_methods_refine|reflexivity].
Qed.
#[local] Hint Resolve prepared_defeq_refines : lookup_refinement.

Theorem indexed_checker_mode_refines mode hash fuel env ps :
  methods_equivalent (Indexed.checker_mode mode hash fuel env ps)
    (Checker.checker_mode mode fuel env ps).
Proof.
  destruct fuel; cbn [Indexed.checker_mode];
    auto using methods_equivalent_refl, prepared_methods_mode_refine.
Qed.

Theorem indexed_checker_refines hash fuel env ps :
  methods_equivalent (Indexed.checker hash fuel env ps) (Checker.checker fuel env ps).
Proof. apply indexed_checker_mode_refines. Qed.

Theorem indexed_infer_refines hash fuel env ps g e :
  Indexed.infer hash fuel env ps g e = Checker.infer fuel env ps g e.
Proof.
  destruct fuel; [reflexivity|].
  unfold Indexed.infer, with_prepared, Checker.infer. cbn beta iota zeta.
  apply same_infer, prepared_methods_refine.
Qed.

Theorem indexed_whnf_refines hash fuel env ps g e :
  Indexed.whnf hash fuel env ps g e = Checker.whnf fuel env ps g e.
Proof.
  destruct fuel; [reflexivity|].
  unfold Indexed.whnf, with_prepared, Checker.whnf. cbn beta iota zeta.
  rewrite prepared_supported_refines.
  destruct (Checker.core_supported env e);
    [apply same_whnf, prepared_methods_refine|reflexivity].
Qed.

Theorem indexed_defeq_refines hash fuel env ps g t s :
  Indexed.defeq hash fuel env ps g t s = Checker.defeq fuel env ps g t s.
Proof.
  destruct fuel; [reflexivity|].
  unfold Indexed.defeq, with_prepared. cbn beta iota zeta. apply prepared_defeq_refines.
Qed.

Theorem indexed_check_refines hash fuel env ps g e ty :
  Indexed.check hash fuel env ps g e ty = Checker.check fuel env ps g e ty.
Proof.
  destruct fuel; [reflexivity|].
  unfold Indexed.check, with_prepared, Checker.check, Checker.infer.
  cbn beta iota zeta.
  apply bind_pointwise; [apply sort_of_refines, prepared_methods_refine|intro ignored].
  apply bind_pointwise; [apply same_infer, prepared_methods_refine|intro et].
  apply bind_pointwise; [apply prepared_defeq_refines|reflexivity].
Qed.

Theorem indexed_check_defeq_refines hash fuel env ps g t s :
  Indexed.check_defeq hash fuel env ps g t s = Checker.check_defeq fuel env ps g t s.
Proof.
  destruct fuel; [reflexivity|].
  unfold Indexed.check_defeq, with_prepared, Checker.check_defeq, Checker.infer.
  cbn beta iota zeta.
  apply bind_pointwise; [apply same_infer, prepared_methods_refine|intro tt].
  apply bind_pointwise; [apply same_infer, prepared_methods_refine|intro st].
  apply bind_pointwise; [apply prepared_defeq_refines|intro same_type].
  apply bind_pointwise; [reflexivity|intro ignored].
  apply bind_pointwise; [apply prepared_defeq_refines|reflexivity].
Qed.

Print Assumptions checker_with_lookup_refines.
Print Assumptions checker_with_lookup_mode_refines.
Print Assumptions indexed_checker_mode_refines.
Print Assumptions indexed_infer_refines.
Print Assumptions indexed_whnf_refines.
Print Assumptions indexed_defeq_refines.
Print Assumptions indexed_check_refines.
Print Assumptions indexed_check_defeq_refines.
