(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Executable regressions for the supported core, negative cases and declines. *)
From Coq Require Import List String NArith Bool.
From LeanPort Require Import Syntax Universes Checker.
Import ListNotations.
Open Scope string_scope.

Definition nm (s : string) := NameStr NameAnon s.
Definition u := LParam (nm "u").
Definition v := LParam (nm "v").
Definition w := LParam (nm "w").
Definition one := LSucc LZero.
Definition two := LSucc one.
Definition prop := ESort LZero.
Definition type0 := ESort one.
Definition type1 := ESort two.
Definition id_type := EPi (nm "A") BDefault type0
  (EPi (nm "x") BDefault (EBVar 0) (EBVar 1)).
Definition id_term := ELam (nm "A") BDefault type0
  (ELam (nm "x") BDefault (EBVar 0) (EBVar 0)).
Definition prop_id_type := EPi (nm "P") BDefault prop
  (EPi (nm "h") BDefault (EBVar 0) (EBVar 1)).
Definition prop_id := ELam (nm "P") BDefault prop
  (ELam (nm "h") BDefault (EBVar 0) (EBVar 0)).

Definition proof_context : context :=
  {| bound_context := [];
     free_context :=
       [(nm "p", {| binding_type := EFVar (nm "P"); binding_value := None |});
        (nm "q", {| binding_type := EFVar (nm "P"); binding_value := None |});
        (nm "r", {| binding_type := EFVar (nm "Q"); binding_value := None |});
        (nm "P", {| binding_type := prop; binding_value := None |});
        (nm "Q", {| binding_type := prop; binding_value := None |})] |}.
Definition function_context : context :=
  {| bound_context := [];
     free_context := [(nm "f", {| binding_type :=
       EPi (nm "x") BDefault type0 type0; binding_value := None |})] |}.
Definition eta_f := ELam (nm "x") BDefault type0 (EApp (EFVar (nm "f")) (EBVar 0)).
Definition id_decl (kind : decl_kind) : declaration :=
  {| decl_hints := HintOpaque; decl_name := nm "proof_id"; decl_params := []; decl_type := prop_id_type;
     decl_value := Some prop_id; decl_kind_of := kind |}.
Definition level_decl : declaration :=
  {| decl_hints := HintOpaque; decl_name := nm "sort"; decl_params := [nm "u"];
     decl_type := ESort (LSucc u); decl_value := Some (ESort u);
     decl_kind_of := DDefinition |}.
Definition cyclic_decl : declaration :=
  {| decl_hints := HintOpaque; decl_name := nm "cycle"; decl_params := []; decl_type := prop;
     decl_value := Some (EConst (nm "cycle") []); decl_kind_of := DDefinition |}.

Example structured_name_no_flattening :
  name_eqb (nm "A.B") (NameStr (nm "A") "B") = false.
Proof. reflexivity. Qed.

Example binary_name_beyond_machine_int :
  name_eqb (NameNum NameAnon 184467440737095516160000000000000000000%N)
           (NameNum NameAnon 184467440737095516160000000000000000001%N) = false.
Proof. vm_compute. reflexivity. Qed.

Example capture_avoiding_substitution :
  instantiate (ELam NameAnon BDefault prop (EBVar 1)) (EBVar 0) =
  ELam NameAnon BDefault prop (EBVar 1).
Proof. reflexivity. Qed.

Example remove_binder_shifts_above : instantiate (EBVar 3) prop = EBVar 2.
Proof. reflexivity. Qed.

Example imax_zero : level_equiv 32 (LIMax u LZero) LZero = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_succ : level_equiv 32 (LIMax u (LSucc v)) (LMax u (LSucc v)) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_self : level_equiv 32 (LIMax u u) u = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_one_parameter : level_equiv 32 (LIMax one u) u = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_max_right :
  level_equiv 32 (LIMax u (LMax v w)) (LMax (LIMax u v) (LIMax u w)) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_imax_right :
  level_equiv 32 (LIMax u (LIMax v w)) (LMax (LIMax u w) (LIMax v w)) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_guard_order :
  level_equiv 32 (LIMax (LIMax two u) v)
    (LIMax (LIMax (LIMax two v) u) v) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example imax_not_max : level_equiv 32 (LIMax two u) (LMax two u) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example imax_constant_var_dominators : level_le 32 (LIMax two u) (LMax two u) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example max_not_below_imax : level_le 32 (LMax two u) (LIMax two u) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example max_commutes : level_equiv 32 (LMax u v) (LMax v u) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example succ_max : level_equiv 32 (LSucc (LMax u v)) (LMax (LSucc u) (LSucc v)) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example unknown_levels_not_equal : level_equiv 32 u v = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example level_fuel_declines : level_equiv 0 u u = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example level_meta_rejected_even_in_dead_imax :
  level_equiv 32 (LIMax (LMVar NameAnon) LZero) LZero = Reject MetaVariable.
Proof. reflexivity. Qed.

Example infer_sort : infer 8 [] [] empty_context prop = Accept type0.
Proof. reflexivity. Qed.
Example infer_polymorphic_identity :
  infer 32 [] [] empty_context id_term = Accept id_type.
Proof. vm_compute. reflexivity. Qed.
Example check_polymorphic_identity :
  check 64 [] [] empty_context id_term id_type = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example check_propositional_identity :
  check 64 [] [] empty_context prop_id prop_id_type = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example noncumulative_sort_rejects :
  check 32 [] [] empty_context prop type1 = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example applying_nonfunction_rejects :
  infer 32 [] [] empty_context (EApp prop prop) = Reject ExpectedPi.
Proof. vm_compute. reflexivity. Qed.
Example application_domain_rejects :
  infer 32 [] [] empty_context (EApp id_term type0) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example unknown_constant_rejects :
  infer 32 [] [] empty_context (EConst (nm "missing") []) = Reject UnknownConstant.
Proof. reflexivity. Qed.
Example unknown_universe_rejects :
  infer 32 [] [] empty_context (ESort u) = Reject UnknownUniverse.
Proof. reflexivity. Qed.
Example local_lookup_lifts :
  infer 8 [] [] (push_binding (push_binding empty_context type0 None) (EBVar 0) None)
    (EBVar 0) = Accept (EBVar 1).
Proof. reflexivity. Qed.
Example loose_variable_rejects :
  infer 8 [] [] empty_context (EBVar 0) = Reject LooseBoundVariable.
Proof. reflexivity. Qed.

Example beta_whnf :
  whnf 32 [] [] empty_context
    (EApp (ELam NameAnon BDefault type0 (EBVar 0)) prop) = Accept prop.
Proof. reflexivity. Qed.
Example zeta_whnf :
  whnf 32 [] [] empty_context (ELet NameAnon type0 prop (EBVar 0) false) = Accept prop.
Proof. reflexivity. Qed.
Example let_inference :
  infer 32 [] [] empty_context (ELet NameAnon type0 prop (EBVar 0) false) = Accept type0.
Proof. vm_compute. reflexivity. Qed.
Example invalid_let_rejects :
  infer 32 [] [] empty_context (ELet NameAnon type0 type0 (EBVar 0) false) = Reject TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example local_let_whnf :
  whnf 8 [] [] (push_binding empty_context type0 (Some prop)) (EBVar 0) = Accept prop.
Proof. reflexivity. Qed.
Example definition_delta :
  whnf 32 [id_decl DDefinition] [] empty_context (EConst (nm "proof_id") []) = Accept prop_id.
Proof. reflexivity. Qed.
Example pinned_theorem_delta :
  whnf 32 [id_decl DTheorem] [] empty_context (EConst (nm "proof_id") []) = Accept prop_id.
Proof. reflexivity. Qed.
Example opaque_does_not_delta :
  whnf 32 [id_decl DOpaque] [] empty_context (EConst (nm "proof_id") []) =
    Accept (EConst (nm "proof_id") []).
Proof. reflexivity. Qed.
Example delta_instantiates_universes :
  whnf 32 [level_decl] [] empty_context (EConst (nm "sort") [LZero]) = Accept prop.
Proof. reflexivity. Qed.
Example universe_arity_rejects :
  infer 32 [level_decl] [] empty_context (EConst (nm "sort") []) = Reject UniverseArity.
Proof. reflexivity. Qed.
(* An intentionally unvalidated environment exercises only the fuel contract. *)
Example delta_cycle_declines :
  whnf 32 [cyclic_decl] [] empty_context (EConst (nm "cycle") []) = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example checked_proof_irrelevance :
  check_defeq 64 [] [] proof_context (EFVar (nm "p")) (EFVar (nm "q")) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example distinct_propositions_not_irrelevant :
  defeq 64 [] [] proof_context (EFVar (nm "p")) (EFVar (nm "r")) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example checked_function_eta :
  check_defeq 64 [] [] function_context eta_f (EFVar (nm "f")) = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example checked_function_eta_symmetric :
  check_defeq 64 [] [] function_context (EFVar (nm "f")) eta_f = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example alpha_ignores_binder_names_and_info :
  defeq 32 [] [] empty_context
    (ELam (nm "a") BImplicit type0 (EBVar 0))
    (ELam (nm "b") BDefault type0 (EBVar 0)) = Accept true.
Proof. reflexivity. Qed.
Example metadata_erased :
  check_defeq 32 [] [] empty_context (EMData prop) prop = Accept tt.
Proof. vm_compute. reflexivity. Qed.
Example projection_declines :
  infer 32 [] [] empty_context (EProj (nm "S") 0 prop) = Decline UnsupportedExpression.
Proof. reflexivity. Qed.
Example literal_declines_without_nat_admission :
  infer 32 [] [] empty_context (ELit (LitNat 184467440737095516160000000000000000000%N)) =
    Decline UnsupportedExpression.
Proof. reflexivity. Qed.
Example discarded_unsupported_expression_declines :
  whnf 32 [] [] empty_context
    (ELet NameAnon prop (ELit (LitNat 0)) prop false) = Decline UnsupportedExpression.
Proof. reflexivity. Qed.
Example unsupported_declaration_declines :
  check_defeq 32 [id_decl DUnsupported] [] empty_context
    (EConst (nm "proof_id") []) (EConst (nm "proof_id") []) = Decline UnsupportedDeclaration.
Proof. reflexivity. Qed.
Example checked_equality_does_not_accept_illtyped_reflexivity :
  check_defeq 32 [] [] empty_context (EApp prop prop) (EApp prop prop) = Reject ExpectedPi.
Proof. reflexivity. Qed.
Example even_reflexivity_needs_fuel :
  defeq 0 [] [] empty_context prop prop = Decline OutOfFuel.
Proof. reflexivity. Qed.

Definition accepted {A} (r : result A) : bool :=
  match r with Accept _ => true | _ => false end.
Definition rejected {A} (r : result A) : bool :=
  match r with Reject _ => true | _ => false end.
Definition declined {A} (r : result A) : bool :=
  match r with Decline _ => true | _ => false end.
Definition decided_true (r : result bool) : bool :=
  match r with Accept true => true | _ => false end.

(* Evaluated again by the separately compiled extracted OCaml executable. *)
Definition regression_checks (_ : unit) : list bool :=
  [decided_true (level_equiv 32 (LIMax u (LMax v w)) (LMax (LIMax u v) (LIMax u w)));
   decided_true (level_le 32 (LIMax two u) (LMax two u));
   negb (decided_true (level_equiv 32 (LIMax two u) (LMax two u)));
   accepted (check 64 [] [] empty_context id_term id_type);
   accepted (check 64 [] [] empty_context prop_id prop_id_type);
   rejected (check 32 [] [] empty_context prop type1);
   rejected (infer 32 [] [] empty_context (EApp prop prop));
   rejected (infer 32 [] [] empty_context (EApp id_term type0));
   accepted (check_defeq 64 [] [] proof_context (EFVar (nm "p")) (EFVar (nm "q")));
   negb (decided_true (defeq 64 [] [] proof_context (EFVar (nm "p")) (EFVar (nm "r"))));
   accepted (check_defeq 64 [] [] function_context eta_f (EFVar (nm "f")));
   accepted (check_defeq 64 [] [] function_context (EFVar (nm "f")) eta_f);
   declined (whnf 32 [cyclic_decl] [] empty_context (EConst (nm "cycle") []));
   declined (infer 32 [] [] empty_context (ELit (LitNat 184467440737095516160000000000000000000%N)));
   match whnf 32 [id_decl DTheorem] [] empty_context (EConst (nm "proof_id") []) with
   | Accept e => expr_eqb e prop_id | _ => false end;
   match whnf 32 [id_decl DOpaque] [] empty_context (EConst (nm "proof_id") []) with
   | Accept e => expr_eqb e (EConst (nm "proof_id") []) | _ => false end;
   match whnf 32 [level_decl] [] empty_context (EConst (nm "sort") [LZero]) with
   | Accept e => expr_eqb e prop | _ => false end].

Example regression_checks_all_true : forallb (fun b => b) (regression_checks tt) = true.
Proof. vm_compute. reflexivity. Qed.
