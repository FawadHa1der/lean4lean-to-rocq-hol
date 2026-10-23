From Coq Require Import List String.
From LeanPort Require Import Syntax Universes Checker Declarations.
Import ListNotations.
Open Scope string_scope.

Definition test_fuel : nat := 200.
Definition p_name := NameStr NameAnon "P".
Definition id_name := NameStr NameAnon "identity".
Definition u_name := NameStr NameAnon "u".
Definition prop_sort := ESort LZero.
Definition identity_type :=
  EPi p_name BDefault prop_sort
    (EPi NameAnon BDefault (EBVar 0) (EBVar 1)).
Definition identity_proof :=
  ELam p_name BDefault prop_sort
    (ELam NameAnon BDefault (EBVar 0) (EBVar 0)).
Definition accepted {A} (r : result A) : bool :=
  match r with Accept _ => true | _ => false end.
Definition rejected {A} (r : result A) : bool :=
  match r with Reject _ => true | _ => false end.

Example accepts_proposition_assumption :
  accepted (admit test_fuel [] (InputAxiom p_name [] prop_sort false)) = true.
Proof. reflexivity. Qed.

Example accepts_identity_theorem :
  accepted (admit test_fuel []
    (InputTheorem id_name [] identity_type identity_proof)) = true.
Proof. reflexivity. Qed.

Example rejects_nonpropositional_theorem :
  rejected (admit test_fuel [] (InputTheorem id_name []
    (ESort (LSucc LZero)) prop_sort)) = true.
Proof. reflexivity. Qed.

Example rejects_type_in_type_definition :
  rejected (admit test_fuel []
    (InputDefinition HintOpaque id_name [] prop_sort prop_sort InputSafe)) = true.
Proof. reflexivity. Qed.

Example rejects_duplicate_names :
  check_declarations test_fuel []
    [InputAxiom p_name [] prop_sort false; InputAxiom p_name [] prop_sort false] =
    Reject DuplicateDeclaration.
Proof. reflexivity. Qed.

Example rejects_duplicate_level_parameters :
  admit test_fuel [] (InputAxiom p_name [u_name; u_name] prop_sort false) =
    Reject DuplicateUniverse.
Proof. reflexivity. Qed.

Example rejects_undefined_universe :
  rejected (admit test_fuel []
    (InputAxiom p_name [] (ESort (LParam u_name)) false)) = true.
Proof. reflexivity. Qed.

Example rejects_open_body :
  rejected (admit test_fuel []
    (InputDefinition HintOpaque id_name [] prop_sort (EBVar 0) InputSafe)) = true.
Proof. reflexivity. Qed.

Example rejects_reserved_axiom :
  admit test_fuel [] (InputAxiom nat_name [] prop_sort false) =
    Reject MalformedDeclaration.
Proof. reflexivity. Qed.

Example wrong_primitive_signature_is_rejected :
  rejected (admit test_fuel [] (InputDefinition HintOpaque (NameStr nat_name "add") []
    identity_type identity_proof InputSafe)) = true.
Proof. reflexivity. Qed.

Example no_fuel_is_not_invalidity :
  admit 0 [] (InputAxiom p_name [] prop_sort false) = Decline OutOfFuel.
Proof. reflexivity. Qed.

Example unsupported_midstream_does_not_return_prefix_acceptance :
  check_declarations test_fuel []
    [InputAxiom p_name [] prop_sort false; InputUnsupported] =
    Decline UnsupportedDeclaration.
Proof. reflexivity. Qed.

Print Assumptions accepts_identity_theorem.
Print Assumptions rejects_type_in_type_definition.
