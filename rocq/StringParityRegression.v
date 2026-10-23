(* SPDX-License-Identifier: Apache-2.0
   Pinned upstream late-hook behavior on fully admitted custom interfaces. *)
From Stdlib Require Import List String Bool.
From LeanPort Require Import Syntax Checker StringParityFixtures.
Import ListNotations.
Open Scope string_scope.
Example sp_candidate_behavior : sp_observations tt =
  List.app (repeat (Reject NotDefinitionallyEqual) 6)
    (List.app (repeat (Accept tt) 8)
      (List.app (repeat (Reject NotDefinitionallyEqual) 4)
        [Reject TypeMismatch;Accept tt;Reject TypeMismatch;Reject TypeMismatch])).
Proof. vm_compute. reflexivity. Qed.
Example sp_candidate_all_gates : sp_gate_results tt = repeat true 14.
Proof. vm_compute. reflexivity. Qed.
Example sp_ordinary_whnf_remains_neutral :
  (env <- sp_text_env false true false ;;
   whnf 256 env [] empty_context (sp_literal "A")) = Accept (sp_literal "A").
Proof. vm_compute. reflexivity. Qed.
Example sp_same_literal_still_converts :
  (env <- sp_text_env false true false ;;
   check_defeq 256 env [] empty_context (sp_literal "A") (sp_literal "A")) = Accept tt.
Proof. vm_compute. reflexivity. Qed.

(* These are local control-flow tests of the late hook, not typing certificates
   in an artificial environment. The checked-environment cases are above. *)
Definition sp_hook_methods (answer : bool) : methods :=
  {| infer_method := fun _ _ => Decline OutOfFuel;
     infer_type_method := fun _ _ => Decline OutOfFuel;
     whnf_method := fun _ _ => Decline OutOfFuel;
     whnf_core_method := fun _ _ _ => Decline OutOfFuel;
     defeq_method := fun _ _ _ => Accept answer;
     method_mode := EagerPolicy.NormalReduction;
     eager_defeq_method := fun _ _ _ => Accept answer |}.
Definition sp_exact_app := EApp (EConst core_string_of_list []) sp_nil.
Example sp_hook_accepts_only_exact_monomorphic_head :
  (core_try_string_expansion (sp_hook_methods true) empty_context (sp_literal "A") sp_exact_app,
   core_try_string_expansion (sp_hook_methods true) empty_context sp_exact_app (sp_literal "A")) =
    (Accept (Some true),Accept (Some true)).
Proof. reflexivity. Qed.
Example sp_hook_shape_controls :
  map (fun e => core_try_string_expansion (sp_hook_methods true) empty_context (sp_literal "A") e)
    [EApp (EConst core_string_of_list [LZero]) sp_nil;
     EApp (EConst (core_name "String.ofList") []) sp_nil;
     EApp (EConst (NameStr (core_name "Other") "ofList") []) sp_nil;
     EConst core_string_of_list [];
     EApp sp_exact_app sp_nil;
     sp_nil;sp_literal "A"] = repeat (Accept None) 7.
Proof. reflexivity. Qed.
Example sp_hook_false_is_not_fallthrough :
  core_compare_fallback (sp_hook_methods false) 8 [] empty_context
    (sp_literal "A") sp_exact_app = Accept false.
Proof. reflexivity. Qed.
Example sp_hook_true_precedes_unit_fallback :
  core_compare_fallback (sp_hook_methods true) 8 [] empty_context
    sp_exact_app (sp_literal "A") = Accept true.
Proof. reflexivity. Qed.
Example sp_hook_inapplicable_reaches_unit_fallback :
  core_compare_fallback (sp_hook_methods false) 8 [] empty_context
    (sp_literal "A") sp_nil = Decline OutOfFuel.
Proof. reflexivity. Qed.
Print Assumptions sp_candidate_behavior.
Print Assumptions sp_candidate_all_gates.
Print Assumptions sp_hook_false_is_not_fallthrough.
