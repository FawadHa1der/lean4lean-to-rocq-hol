(* SPDX-License-Identifier: Apache-2.0
   Checked custom text interfaces; no imported raw environment fixture. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Universes Checker Primitives Declarations Inductive.
Import ListNotations.
Open Scope string_scope.

Definition sp_pi a b := EPi NameAnon BDefault a b.
Definition sp_lam a b := ELam NameAnon BDefault a b.
Definition sp_type := ESort (LSucc LZero).
Definition sp_u := core_name "u".
Definition sp_decl n ps ty k : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := ty;
     decl_kind_of := k; decl_value := None |}.
Definition sp_ind n ps np ty cs := sp_decl n ps ty
  (DInductive {| ind_num_params := np; ind_num_indices := 0; ind_all := [n];
    ind_ctors := cs; ind_num_nested := 0; ind_is_rec := false;
    ind_is_reflexive := false; ind_is_unsafe := false |}).
Definition sp_ctor n owner ps np i nf ty := sp_decl n ps ty
  (DConstructor {| ctor_induct := owner; ctor_index := i; ctor_num_params := np;
    ctor_num_fields := nf; ctor_is_unsafe := false |}).
Definition sp_is_ind d := match decl_kind_of d with DInductive _ => true | _ => false end.
Definition sp_is_ctor d := match decl_kind_of d with DConstructor _ => true | _ => false end.
Definition sp_is_rec d := match decl_kind_of d with DRecursor _ => true | _ => false end.
Definition sp_install_ind env ps np spec :=
  generated <- derive_inductive 256 env ps np [spec] ;;
  admit_inductive 256 env (filter sp_is_ind generated)
    (filter sp_is_ctor generated) (filter sp_is_rec generated).
Definition sp_define env n ps ty body := admit 256 env (InputDefinition HintOpaque n ps ty body InputSafe).
Definition sp_success {A} (r : result A) := match r with Accept _ => true | _ => false end.

Definition sp_nat := sp_install_ind [] [] 0
  {| spec_decl := sp_ind core_nat_name [] 0 sp_type [core_zero_name;core_succ_name];
     spec_ctors := [sp_ctor core_zero_name core_nat_name [] 0 0 0 core_nat;
       sp_ctor core_succ_name core_nat_name [] 0 1 1 (sp_pi core_nat core_nat)] |}.
Definition sp_list a := EApp (EConst core_list_name [LParam sp_u]) a.
Definition sp_list_spec :=
  {| spec_decl := sp_ind core_list_name [sp_u] 1
       (sp_pi (ESort (LSucc (LParam sp_u))) (ESort (LSucc (LParam sp_u))))
       [NameStr core_list_name "nil";NameStr core_list_name "cons"];
     spec_ctors :=
       [sp_ctor (NameStr core_list_name "nil") core_list_name [sp_u] 1 0 0
         (sp_pi (ESort (LSucc (LParam sp_u))) (sp_list (EBVar 0)));
        sp_ctor (NameStr core_list_name "cons") core_list_name [sp_u] 1 1 2
         (sp_pi (ESort (LSucc (LParam sp_u)))
           (sp_pi (EBVar 0) (sp_pi (sp_list (EBVar 1)) (sp_list (EBVar 2)))))] |}.
Definition sp_base :=
  env <- sp_nat ;;
  env <- sp_install_ind env [sp_u] 1 sp_list_spec ;;
  sp_define env core_char_name [] sp_type core_nat.
Definition sp_nil := EApp (EConst (NameStr core_list_name "nil") [LZero]) primitive_char.
Definition sp_mk := NameStr core_string_name "mk".
Definition sp_string_spec :=
  {| spec_decl := sp_ind core_string_name [] 0 sp_type [sp_mk];
     spec_ctors := [sp_ctor sp_mk core_string_name [] 0 0 1
       (sp_pi primitive_list_char primitive_string)] |}.
Definition sp_text_env (structure collapsed_char collapsed_string : bool) :=
  env <- sp_base ;;
  env <- if structure then sp_install_ind env [] 0 sp_string_spec
         else sp_define env core_string_name [] sp_type primitive_list_char ;;
  env <- sp_define env core_char_of_nat [] (primitive_signature PCharOfNat)
    (sp_lam core_nat (if collapsed_char then ELit (LitNat 0) else EBVar 0)) ;;
  sp_define env core_string_of_list [] (primitive_signature PStringOfList)
    (sp_lam primitive_list_char
      (let value := if collapsed_string then sp_nil else EBVar 0 in
       if structure then EApp (EConst sp_mk []) value else value)).
Definition sp_literal s := ELit (LitString s).
Definition sp_checked_pair env a b :=
  _ <- check 256 env [] empty_context a primitive_string ;;
  _ <- check 256 env [] empty_context b primitive_string ;; Accept tt.
Definition sp_pair_gate structure cc cs s :=
  env <- sp_text_env structure cc cs ;;
  expanded <- core_expand_string s ;; sp_checked_pair env (sp_literal s) expanded.
Definition sp_compare structure cc cs (reverse : bool) s :=
  env <- sp_text_env structure cc cs ;;
  expanded <- core_expand_string s ;;
  _ <- sp_checked_pair env (sp_literal s) expanded ;;
  if reverse then check_defeq 256 env [] empty_context expanded (sp_literal s)
  else check_defeq 256 env [] empty_context (sp_literal s) expanded.
Definition sp_compare_normal structure cc cs s :=
  env <- sp_text_env structure cc cs ;;
  expanded <- core_expand_string s ;;
  expanded <- whnf 256 env [] empty_context expanded ;;
  _ <- sp_checked_pair env (sp_literal s) expanded ;;
  check_defeq 256 env [] empty_context (sp_literal s) expanded.
Definition sp_distinct structure cc cs :=
  env <- sp_text_env structure cc cs ;;
  _ <- sp_checked_pair env (sp_literal "A") (sp_literal "B") ;;
  check_defeq 256 env [] empty_context (sp_literal "A") (sp_literal "B").
Definition sp_projection s :=
  env <- sp_text_env true false false ;;
  let p := EProj core_string_name 0 (sp_literal s) in
  _ <- check 256 env [] empty_context p primitive_list_char ;;
  check_defeq 256 env [] empty_context p (core_char_list
    (match core_utf8 s with Some cs => cs | None => [] end)).
Definition sp_recursor s :=
  env <- sp_text_env true false false ;;
  let fold := core_apps (EConst (rec_name core_string_name) [LSucc LZero])
    [sp_lam primitive_string primitive_list_char;
     sp_lam primitive_list_char (EBVar 0);sp_literal s] in
  _ <- check 256 env [] empty_context fold primitive_list_char ;;
  check_defeq 256 env [] empty_context fold (core_char_list
    (match core_utf8 s with Some cs => cs | None => [] end)).

Definition sp_eq_name := core_name "Eq".
Definition sp_eq_at u a x y := core_apps (EConst sp_eq_name [u]) [a;x;y].
Definition sp_eq_spec :=
  {| spec_decl := sp_ind sp_eq_name [sp_u] 2
       (sp_pi (ESort (LParam sp_u)) (sp_pi (EBVar 0) (sp_pi (EBVar 1) (ESort LZero))))
       [NameStr sp_eq_name "refl"];
     spec_ctors := [sp_ctor (NameStr sp_eq_name "refl") sp_eq_name [sp_u] 2 0 0
       (sp_pi (ESort (LParam sp_u)) (sp_pi (EBVar 0)
         (sp_eq_at (LParam sp_u) (EBVar 1) (EBVar 0) (EBVar 0))))] |}.
Definition sp_eq_env structure :=
  env <- sp_text_env structure true false ;;
  sp_install_ind env [sp_u] 2 sp_eq_spec.
Definition sp_refl e := core_apps (EConst (NameStr sp_eq_name "refl") [LSucc LZero])
  [primitive_string;e].
Definition sp_literal_equality := sp_eq_at (LSucc LZero) primitive_string
  (sp_literal "A") (sp_literal "B").
Definition sp_expanded_proof_gate structure :=
  env <- sp_eq_env structure ;; expanded <- core_expand_string "A" ;;
  check 256 env [] empty_context (sp_refl expanded)
    (sp_eq_at (LSucc LZero) primitive_string expanded expanded).
Definition sp_expanded_theorem structure :=
  env <- sp_eq_env structure ;; expanded <- core_expand_string "A" ;;
  _ <- sp_expanded_proof_gate structure ;;
  _ <- admit 256 env (InputTheorem (core_name "ExpandedTextEquality") []
    sp_literal_equality (sp_refl expanded)) ;; Accept tt.
Definition sp_literal_theorem structure :=
  env <- sp_eq_env structure ;;
  _ <- admit 256 env (InputTheorem (core_name "LiteralTextEquality") []
    sp_literal_equality (sp_refl (sp_literal "A"))) ;; Accept tt.

Example sp_nat_admission_gate : sp_success sp_nat = true.
Proof. vm_compute. reflexivity. Qed.

Example sp_eq_and_expanded_proof_gates :
  (sp_success (sp_eq_env false), sp_success (sp_eq_env true),
   sp_expanded_proof_gate false, sp_expanded_proof_gate true) =
    (true,true,Accept tt,Accept tt).
Proof. vm_compute. reflexivity. Qed.

Definition sp_gate_results (_ : unit) : list bool :=
  [sp_success sp_nat;sp_success sp_base;
   sp_success (sp_text_env false false false);sp_success (sp_text_env false true false);
   sp_success (sp_text_env false false true);sp_success (sp_text_env true false false);
   sp_success (sp_text_env true true false);sp_success (sp_text_env true false true);
   sp_success (sp_pair_gate false false false "A");sp_success (sp_pair_gate true false false "A");
   sp_success (sp_eq_env false);sp_success (sp_eq_env true);
   sp_success (sp_expanded_proof_gate false);sp_success (sp_expanded_proof_gate true)].
Example sp_base_admission_gate : sp_success sp_base = true.
Proof. vm_compute. reflexivity. Qed.
Example sp_all_text_admission_gates :
  map (fun '(s,c,d) => sp_success (sp_text_env s c d))
    [(false,false,false);(false,true,false);(false,false,true);
     (true,false,false);(true,true,false);(true,false,true)] = repeat true 6.
Proof. vm_compute. reflexivity. Qed.
Example sp_all_literal_expansion_typing_gates :
  map (fun '(s,c,d) => sp_pair_gate s c d "A")
    [(false,false,false);(false,true,false);(false,false,true);
     (true,false,false);(true,true,false);(true,false,true)] = repeat (Accept tt) 6.
Proof. vm_compute. reflexivity. Qed.

Definition sp_observations (_ : unit) : list (result unit) :=
  [sp_compare false false false false "A";
   sp_compare false false false true "A";
   sp_compare false true false false "A";
   sp_compare false false true false "A";
   sp_compare false false false false "";
   sp_compare_normal false false false "A";
   sp_compare true false false false "A";
   sp_compare true false false true "A";
   sp_compare true true false false "A";
   sp_compare true false true false "A";
   sp_projection "A";sp_projection "";sp_recursor "A";sp_recursor "";
   sp_distinct false true false;sp_distinct false false true;
   sp_distinct true true false;sp_distinct true false true;
   sp_expanded_theorem false;sp_expanded_theorem true;
   sp_literal_theorem false;sp_literal_theorem true].
