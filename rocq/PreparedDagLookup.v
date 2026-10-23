(* SPDX-License-Identifier: Apache-2.0
   Public checker operations over one already prepared, internal lookup. *)
From Stdlib Require Import List Bool.
From LeanPort Require Import Syntax Checker LookupIntegration LookupCore
  LookupRefinement IndexedChecker.

Definition prepared_whnf lookup fuel env ps g e : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S _ => if supported_with_lookup lookup env e
      then whnf_method (checker_with_lookup fuel env lookup ps) g e
      else Decline UnsupportedExpression
  end.

Definition prepared_defeq lookup fuel env ps g t s : result bool :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S _ => defeq_with_methods lookup env
      (checker_with_lookup fuel env lookup ps) g t s
  end.

Section Refinement.
Context (lookup : declaration_lookup) (env : environment).
Hypothesis Lookup : forall n, lookup n = find_decl n env.

Lemma lookup_methods_refine fuel ps :
  methods_equivalent (checker_with_lookup fuel env lookup ps) (Checker.checker fuel env ps).
Proof. apply checker_with_lookup_refines. exact Lookup. Qed.

Lemma lookup_supported_refines e :
  supported_with_lookup lookup env e = Checker.core_supported env e.
Proof. apply core_supported_refines. exact Lookup. Qed.

Lemma prepared_whnf_refines fuel ps g e :
  prepared_whnf lookup fuel env ps g e = Checker.whnf fuel env ps g e.
Proof.
  destruct fuel; [reflexivity|]. unfold prepared_whnf, Checker.whnf.
  rewrite lookup_supported_refines.
  destruct (Checker.core_supported env e); [|reflexivity].
  apply same_whnf, lookup_methods_refine.
Qed.

Lemma prepared_defeq_refines fuel ps g t s :
  prepared_defeq lookup fuel env ps g t s = Checker.defeq fuel env ps g t s.
Proof.
  destruct fuel; [reflexivity|].
  unfold prepared_defeq, defeq_with_methods, Checker.defeq.
  repeat rewrite lookup_supported_refines.
  destruct (Checker.core_supported env t && Checker.core_supported env s);
    [apply same_defeq, lookup_methods_refine|reflexivity].
Qed.
End Refinement.

Lemma original_infer_step_methods a b fuel env ps checking g e :
  methods_equivalent a b ->
  Checker.infer_step a fuel env ps checking g e =
  Checker.infer_step b fuel env ps checking g e.
Proof.
  intro H. change (Accessor.infer_step find_decl a fuel env ps checking g e =
    Checker.infer_step b fuel env ps checking g e).
  apply infer_step_refines; [reflexivity|exact H].
Qed.
