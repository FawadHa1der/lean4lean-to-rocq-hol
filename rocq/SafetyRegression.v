(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List String.
From LeanPort Require Import Syntax Checker Declarations Safety.
Import ListNotations.
Open Scope string_scope.

Definition safety_p := NameStr NameAnon "P".
Definition safety_f := NameStr NameAnon "f".
Definition safety_g := NameStr NameAnon "g".
Definition safety_h := NameStr NameAnon "h".
Definition safety_prop := EConst safety_p [].
Definition safety_env := [restricted_constant safety_p [] (ESort LZero) None DAssumption].
Definition safety_loop mode := InputDefinition HintOpaque safety_f [] safety_prop (EConst safety_f []) mode.
Definition safety_good {A} (r : result A) := match r with Accept _ => true | _ => false end.
Definition safety_bad {A} (r : result A) := match r with Reject _ => true | _ => false end.
Definition safety_after mode :=
  [restricted_constant safety_f [] safety_prop (Some (EConst safety_f [])) (safety_kind mode);
   restricted_constant safety_p [] (ESort LZero) None DAssumption].

Example unsafe_loop_checked : safety_good (admit_extended 100 safety_env (safety_loop InputUnsafe)) = true.
Proof. reflexivity. Qed.
Example partial_mutual_loop_checked :
  safety_good (admit_mutual 100 safety_env [safety_loop InputPartial]) = true.
Proof. reflexivity. Qed.
Example safe_recursive_definition_rejected :
  safety_bad (admit_extended 100 safety_env (safety_loop InputSafe)) = true.
Proof. reflexivity. Qed.
Example unsafe_not_usable_in_theorem :
  safety_bad (admit_extended 100 (safety_after InputUnsafe)
    (InputTheorem safety_h [] safety_prop (EConst safety_f []))) = true.
Proof. reflexivity. Qed.
Example partial_not_usable_in_theorem :
  safety_bad (admit_extended 100 (safety_after InputPartial)
    (InputTheorem safety_h [] safety_prop (EConst safety_f []))) = true.
Proof. reflexivity. Qed.
Example partial_not_usable_in_safe_definition :
  safety_bad (admit_extended 100 (safety_after InputPartial)
    (InputDefinition HintOpaque safety_h [] safety_prop (EConst safety_f []) InputSafe)) = true.
Proof. reflexivity. Qed.
Example unsafe_may_reference_unsafe :
  safety_good (admit_extended 100 (safety_after InputUnsafe)
    (InputDefinition HintOpaque safety_h [] safety_prop (EConst safety_f []) InputUnsafe)) = true.
Proof. reflexivity. Qed.
Example unsafe_may_reference_partial :
  safety_good (admit_extended 100 (safety_after InputPartial)
    (InputDefinition HintOpaque safety_h [] safety_prop (EConst safety_f []) InputUnsafe)) = true.
Proof. reflexivity. Qed.
Example safe_mutual_definition_rejected :
  safety_bad (admit_mutual 100 safety_env [safety_loop InputSafe]) = true.
Proof. reflexivity. Qed.
Example duplicate_mutual_names_rejected :
  safety_bad (admit_mutual 100 safety_env [safety_loop InputUnsafe;safety_loop InputUnsafe]) = true.
Proof. reflexivity. Qed.
Example mutual_mixed_safety_rejected :
  safety_bad (admit_mutual 100 safety_env
    [safety_loop InputUnsafe;InputDefinition HintOpaque safety_g [] safety_prop (EConst safety_f []) InputPartial]) = true.
Proof. reflexivity. Qed.
Example mutual_mixed_universes_rejected :
  safety_bad (admit_mutual 100 safety_env
    [safety_loop InputUnsafe;InputDefinition HintOpaque safety_g [safety_h] safety_prop (EConst safety_f []) InputUnsafe]) = true.
Proof. reflexivity. Qed.
Example empty_mutual_rejected : safety_bad (admit_mutual 100 safety_env []) = true.
Proof. reflexivity. Qed.
Example unsafe_axiom_checked :
  safety_good (admit_extended 100 safety_env (InputAxiom safety_f [] safety_prop true)) = true.
Proof. reflexivity. Qed.
Print Assumptions unsafe_not_usable_in_theorem.
Print Assumptions partial_mutual_loop_checked.
