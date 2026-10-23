(* SPDX-License-Identifier: Apache-2.0
   Computational tests of nested transformation and checked admission.
   Expected declarations below are handwritten, not obtained from derivation. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax InductiveUtils Inductive NestedTransform NestedAdmission.
Import ListNotations.
Open Scope string_scope.

Module NestedRegression.

Definition nm (s : string) := NameStr NameAnon s.
Definition ty := ESort (LSucc LZero).
Definition pi := EPi NameAnon BDefault.
Definition lam := ELam NameAnon BDefault.
Definition v := nm "v".
Definition accepts {A} (r : result A) := match r with Accept _ => true | _ => false end.
Definition loc (n : string) (t : expr) : ind_local :=
  {| il_id := nm n; il_user := NameAnon; il_binder := BDefault; il_type := t |}.
Definition p := loc "p" ty.
Definition q := loc "q" ty.

Example substitute_lambda_avoids_capture :
  instantiate_locals [p] [EBVar 0] 0
    (lam (local_expr p) (EApp (local_expr p) (EBVar 0))) =
    lam (EBVar 0) (EApp (EBVar 1) (EBVar 0)).
Proof. vm_compute. reflexivity. Qed.
Example substitute_pi_avoids_capture :
  instantiate_locals [p] [EBVar 0] 0
    (pi (local_expr p) (EApp (local_expr p) (EBVar 0))) =
    pi (EBVar 0) (EApp (EBVar 1) (EBVar 0)).
Proof. vm_compute. reflexivity. Qed.
Example substitute_let_avoids_capture :
  instantiate_locals [p] [EBVar 0] 0
    (ELet NameAnon (local_expr p) (local_expr p)
      (EApp (local_expr p) (EBVar 0)) true) =
    ELet NameAnon (EBVar 0) (EBVar 0) (EApp (EBVar 1) (EBVar 0)) true.
Proof. vm_compute. reflexivity. Qed.
Example substitute_nested_binders_accumulate_depth :
  instantiate_locals [p] [EBVar 0] 0
    (lam ty (pi (local_expr p)
      (ELet NameAnon (local_expr p) (EBVar 0)
        (EApp (local_expr p) (EBVar 0)) false))) =
    lam ty (pi (EBVar 1)
      (ELet NameAnon (EBVar 2) (EBVar 0) (EApp (EBVar 3) (EBVar 0)) false)).
Proof. vm_compute. reflexivity. Qed.
Example substitute_preserves_unmapped_free_local :
  instantiate_locals [p] [EBVar 0] 2 (local_expr q) = local_expr q.
Proof. vm_compute. reflexivity. Qed.
Example substitute_is_simultaneous_not_recursive :
  instantiate_locals [p;q] [local_expr q;EBVar 0] 0
    (EApp (local_expr p) (local_expr q)) = EApp (local_expr q) (EBVar 0).
Proof. vm_compute. reflexivity. Qed.

Definition old := nm "Old".
Definition aux := nested_aux_name 1.
Definition aux_ctor := NameNum (NameStr aux "mk") 2%N.
Definition old_ctor := NameNum (NameStr old "mk") 2%N.
Definition symbolic_result : nested_elimination :=
  {| nested_params := [p]; nested_context := empty_context; nested_specs := [];
     nested_mapping := [(EApp (EConst old [LParam v]) (local_expr p),aux)];
     nested_aux_names := [aux]; nested_aux_count := 1 |}.
Definition symbolic_ctor : declaration :=
  {| decl_hints := HintOpaque; decl_name := aux_ctor; decl_params := [v]; decl_type := ty; decl_value := None;
     decl_kind_of := DConstructor {| ctor_induct := aux; ctor_index := 0;
       ctor_num_params := 1; ctor_num_fields := 1; ctor_is_unsafe := false |} |}.
Definition rec_map := auxiliary_rec_names (nm "Tree") [aux] 1.

(* Symbolic fixtures exercise restoration only, not environment admission. *)
Example restore_auxiliary_head_and_indices :
  restore_nested_expr 30 [symbolic_ctor] symbolic_result []
    (apply_exprs (EConst aux [LParam v]) [ty;EBVar 0]) =
    Accept (apply_exprs (EConst old [LParam v]) [ty;EBVar 0]).
Proof. vm_compute. reflexivity. Qed.
Example restore_auxiliary_short_arity_rejected :
  restore_nested_expr 30 [symbolic_ctor] symbolic_result [] (EConst aux [LParam v]) =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example restore_constructor_name_preserves_numeric_suffix :
  restore_ctor_name 30 [symbolic_ctor] symbolic_result aux_ctor = Accept old_ctor.
Proof. vm_compute. reflexivity. Qed.
Example restore_constructor_head_parameters_and_fields :
  restore_nested_expr 30 [symbolic_ctor] symbolic_result []
    (apply_exprs (EConst aux_ctor [LParam v]) [ty;EBVar 0]) =
    Accept (apply_exprs (EConst old_ctor [LParam v]) [ty;EBVar 0]).
Proof. vm_compute. reflexivity. Qed.
Example restore_constructor_short_arity_rejected :
  restore_nested_expr 30 [symbolic_ctor] symbolic_result [] (EConst aux_ctor [LParam v]) =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example restore_recursor_name_keeps_universe_arguments :
  restore_nested_expr 30 [] symbolic_result rec_map
    (EApp (EConst (rec_name aux) [LZero;LParam v]) ty) =
    Accept (EApp (EConst (NameStr (nm "Tree") "rec_1") [LZero;LParam v]) ty).
Proof. vm_compute. reflexivity. Qed.
Example auxiliary_recursor_decimal_names :
  auxiliary_rec_names (nm "Tree") [aux;nested_aux_name 2] 9 =
    [(rec_name aux,NameStr (nm "Tree") "rec_9");
     (rec_name (nested_aux_name 2),NameStr (nm "Tree") "rec_10")].
Proof. vm_compute. reflexivity. Qed.
Example restore_pi_opens_rebases_and_closes :
  restore_nested_type 30 [] symbolic_result []
    (pi ty (EApp (EConst aux [LParam v]) (EBVar 0))) =
    Accept (pi ty (EApp (EConst old [LParam v]) (EBVar 0))).
Proof. vm_compute. reflexivity. Qed.
Example restore_lambda_opens_rebases_and_closes :
  restore_nested_type 30 [] symbolic_result []
    (lam ty (EApp (EConst aux [LParam v]) (EBVar 0))) =
    Accept (lam ty (EApp (EConst old [LParam v]) (EBVar 0))).
Proof. vm_compute. reflexivity. Qed.
Example restore_telescope_short_arity_rejected :
  restore_nested_type 30 [] symbolic_result [] ty = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example restore_arguments_before_outer_auxiliary :
  restore_nested_expr 30 [] symbolic_result []
    (EApp (EConst aux [LParam v]) (EApp (EConst aux [LParam v]) ty)) =
    Accept (EApp (EConst old [LParam v]) (EApp (EConst old [LParam v]) ty)).
Proof. vm_compute. reflexivity. Qed.
Example restoration_fuel_declines :
  restore_nested_expr 0 [] symbolic_result [] ty = Decline OutOfFuel.
Proof. reflexivity. Qed.

Definition reserved := NameStr (nm "_nested") "T".
Example reserved_constant_detected_under_binders :
  uses_reserved_nested (lam ty (EMData (EConst reserved []))) = true.
Proof. vm_compute. reflexivity. Qed.
Example reserved_projection_owner_detected :
  uses_reserved_nested (EProj reserved 0 (EBVar 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Example similar_namespace_is_not_reserved :
  uses_reserved_nested (EConst (NameStr (nm "_nestedOther") "T") []) = false.
Proof. vm_compute. reflexivity. Qed.

Definition ind_decl (n : name) (np nested : nat) (cs : list name) (recursive : bool) (t : expr) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := t; decl_value := None;
     decl_kind_of := DInductive {| ind_num_params := np; ind_num_indices := 0;
       ind_all := [n]; ind_ctors := cs; ind_num_nested := nested;
       ind_is_rec := recursive; ind_is_reflexive := false; ind_is_unsafe := false |} |}.
Definition ctor_decl (n owner : name) (index np fields : nat) (t : expr) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := t; decl_value := None;
     decl_kind_of := DConstructor {| ctor_induct := owner; ctor_index := index;
       ctor_num_params := np; ctor_num_fields := fields; ctor_is_unsafe := false |} |}.
Definition rec_decl (n owner : name) (np motives minors : nat) (t : expr)
    (rules : list recursor_rule) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := [v]; decl_type := t; decl_value := None;
     decl_kind_of := DRecursor {| rec_all := [owner]; rec_num_params := np;
       rec_num_indices := 0; rec_num_motives := motives; rec_num_minors := minors;
       rec_rules := rules; rec_k := false; rec_is_unsafe := false |} |}.
Definition with_kind (d : declaration) (k : decl_kind) :=
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d; decl_type := decl_type d;
     decl_value := decl_value d; decl_kind_of := k |}.
Definition with_type (d : declaration) (t : expr) :=
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d; decl_type := t;
     decl_value := decl_value d; decl_kind_of := decl_kind_of d |}.
Definition with_rec_k (d : declaration) (k : bool) :=
  match decl_kind_of d with
  | DRecursor r => with_kind d (DRecursor {| rec_all := rec_all r;
      rec_num_params := rec_num_params r; rec_num_indices := rec_num_indices r;
      rec_num_motives := rec_num_motives r; rec_num_minors := rec_num_minors r;
      rec_rules := rec_rules r; rec_k := k; rec_is_unsafe := rec_is_unsafe r |})
  | _ => d
  end.
Definition with_rules (d : declaration) (rules : list recursor_rule) :=
  match decl_kind_of d with
  | DRecursor r => with_kind d (DRecursor {| rec_all := rec_all r;
      rec_num_params := rec_num_params r; rec_num_indices := rec_num_indices r;
      rec_num_motives := rec_num_motives r; rec_num_minors := rec_num_minors r;
      rec_rules := rules; rec_k := rec_k r; rec_is_unsafe := rec_is_unsafe r |})
  | _ => d
  end.

Definition empty_name := nm "RegressionEmpty".
Definition empty_type := EConst empty_name [].
Definition empty_decl := ind_decl empty_name 0 0 [] false ty.
Definition empty_rec := rec_decl (rec_name empty_name) empty_name 0 1 0
  (pi (pi empty_type (ESort (LParam v)))
    (pi empty_type (EApp (EBVar 1) (EBVar 0)))) [].
Example empty_baseline_accepted :
  accepts (admit_inductive_nested 120 [] [empty_decl] [] [empty_rec]) = true.
Proof. vm_compute. reflexivity. Qed.
Example empty_forged_k_rejected :
  admit_inductive_nested 120 [] [empty_decl] [] [with_rec_k empty_rec true] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example empty_forged_nested_count_rejected :
  admit_inductive_nested 120 [] [ind_decl empty_name 0 1 [] false ty] [] [empty_rec] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example empty_missing_recursor_rejected :
  admit_inductive_nested 120 [] [empty_decl] [] [] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example empty_forged_rule_rejected :
  admit_inductive_nested 120 [] [empty_decl] []
    [with_rules empty_rec [{| rule_ctor := NameStr empty_name "impossible";
       rule_nfields := 0; rule_rhs := ty |}]] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

(* A fully checked Box, with independent literal signature and iota rule. *)
Definition box := nm "RegressionBox".
Definition box_mk := NameStr box "mk".
Definition box_at (a : expr) := EApp (EConst box []) a.
Definition box_val (a x : expr) := apply_exprs (EConst box_mk []) [a;x].
Definition A := loc "A" ty.
Definition x := loc "x" (local_expr A).
Definition box_motive := loc "box_motive" (pi (box_at (local_expr A)) (ESort (LParam v))).
Definition box_minor := loc "box_minor"
  (close_pi [x] (EApp (local_expr box_motive) (box_val (local_expr A) (local_expr x)))).
Definition box_major := loc "box_major" (box_at (local_expr A)).
Definition box_decl := ind_decl box 1 0 [box_mk] false (pi ty ty).
Definition box_ctor := ctor_decl box_mk box 0 1 1
  (close_pi [A;x] (box_at (local_expr A))).
Definition box_rule := {| rule_ctor := box_mk; rule_nfields := 1;
  rule_rhs := close_lam [A;box_motive;box_minor;x]
    (EApp (local_expr box_minor) (local_expr x)) |}.
Definition box_rec := rec_decl (rec_name box) box 1 1 1
  (close_pi [A;box_motive;box_minor;box_major]
    (EApp (local_expr box_motive) (local_expr box_major))) [box_rule].
Definition box_admission := admit_inductive_nested 180 [] [box_decl] [box_ctor] [box_rec].
Example container_baseline_accepted : accepts box_admission = true.
Proof. vm_compute. reflexivity. Qed.

(* Tree has a leaf and a nested Box Tree field. Both recursors and all rules
   are specified independently, using named locals only to write binders. *)
Definition tree := nm "RegressionTree".
Definition tree_ty := EConst tree [].
Definition leaf := NameStr tree "leaf".
Definition node := NameStr tree "node".
Definition nested_rec := NameStr tree "rec_1".
Definition mt := loc "mt" (pi tree_ty (ESort (LParam v))).
Definition mb := loc "mb" (pi (box_at tree_ty) (ESort (LParam v))).
Definition leaf_minor := loc "leaf_minor" (EApp (local_expr mt) (EConst leaf [])).
Definition bt := loc "bt" (box_at tree_ty).
Definition bt_ih := loc "bt_ih" (EApp (local_expr mb) (local_expr bt)).
Definition node_minor := loc "node_minor" (close_pi [bt;bt_ih]
  (EApp (local_expr mt) (EApp (EConst node []) (local_expr bt)))).
Definition tt := loc "tt" tree_ty.
Definition tt_ih := loc "tt_ih" (EApp (local_expr mt) (local_expr tt)).
Definition box_tree_minor := loc "box_tree_minor" (close_pi [tt;tt_ih]
  (EApp (local_expr mb) (box_val tree_ty (local_expr tt)))).
Definition handlers := [mt;mb;leaf_minor;node_minor;box_tree_minor].
Definition tree_decl (nested : nat) := ind_decl tree 0 nested [leaf;node] true ty.
Definition leaf_ctor := ctor_decl leaf tree 0 0 0 tree_ty.
Definition node_ctor := ctor_decl node tree 1 0 1 (pi (box_at tree_ty) tree_ty).
Definition leaf_rule := {| rule_ctor := leaf; rule_nfields := 0;
  rule_rhs := close_lam handlers (local_expr leaf_minor) |}.
Definition node_rule := {| rule_ctor := node; rule_nfields := 1;
  rule_rhs := close_lam (List.app handlers [bt])
    (apply_exprs (local_expr node_minor) [local_expr bt;
      apply_locals (EConst nested_rec [LParam v]) (List.app handlers [bt])]) |}.
Definition box_tree_rule := {| rule_ctor := box_mk; rule_nfields := 1;
  rule_rhs := close_lam (List.app handlers [tt])
    (apply_exprs (local_expr box_tree_minor) [local_expr tt;
      apply_locals (EConst (rec_name tree) [LParam v]) (List.app handlers [tt])]) |}.
Definition tree_rec := rec_decl (rec_name tree) tree 0 2 3
  (close_pi (List.app handlers [tt]) (EApp (local_expr mt) (local_expr tt)))
  [leaf_rule;node_rule].
Definition tree_aux_rec := rec_decl nested_rec tree 0 2 3
  (close_pi (List.app handlers [bt]) (EApp (local_expr mb) (local_expr bt))) [box_tree_rule].
Definition admit_tree (d : declaration) (cs rs : list declaration) :=
  env <- box_admission ;; admit_inductive_nested 240 env [d] cs rs.
Definition tree_admission := admit_tree (tree_decl 1) [leaf_ctor;node_ctor] [tree_rec;tree_aux_rec].

Example genuine_nested_baseline_accepted : accepts tree_admission = true.
Proof. vm_compute. reflexivity. Qed.
Example genuine_nested_elimination_produces_one_auxiliary :
  match box_admission with
  | Accept env =>
    match eliminate_nested 120 env [] 0
      [{| spec_decl := tree_decl 1; spec_ctors := [leaf_ctor;node_ctor] |}] with
    | Accept r => Nat.eqb (nested_aux_count r) 1 &&
        list_eqb expr_eqb (map fst (nested_mapping r)) [box_at tree_ty]
    | _ => false end
  | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example nested_admission_hides_auxiliary_types_but_keeps_restored_recursor :
  match tree_admission with
  | Accept env => Nat.eqb (List.length env) 8 &&
      match find_decl aux env,find_decl (rec_name aux) env,find_decl nested_rec env with
      | None,None,Some d => name_eqb (decl_name d) nested_rec
      | _,_,_ => false end
  | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example nested_forged_count_rejected :
  admit_tree (tree_decl 0) [leaf_ctor;node_ctor] [tree_rec;tree_aux_rec] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_forged_constructor_field_count_rejected :
  admit_tree (tree_decl 1)
    [leaf_ctor;ctor_decl node tree 1 0 0 (decl_type node_ctor)] [tree_rec;tree_aux_rec] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_forged_recursor_k_rejected :
  admit_tree (tree_decl 1) [leaf_ctor;node_ctor] [with_rec_k tree_rec true;tree_aux_rec] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_missing_auxiliary_recursor_rejected :
  admit_tree (tree_decl 1) [leaf_ctor;node_ctor] [tree_rec] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_forged_auxiliary_rule_body_rejected :
  admit_tree (tree_decl 1) [leaf_ctor;node_ctor]
    [tree_rec;with_rules tree_aux_rec [{| rule_ctor := box_mk; rule_nfields := 1;
      rule_rhs := close_lam (List.app handlers [tt]) (EConst leaf []) |}]] =
    Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example nested_forged_restored_constructor_name_rejected :
  admit_tree (tree_decl 1) [leaf_ctor;node_ctor]
    [tree_rec;with_rules tree_aux_rec [{| rule_ctor := NameStr aux "mk"; rule_nfields := 1;
      rule_rhs := rule_rhs box_tree_rule |}]] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example reserved_namespace_mutation_rejected :
  admit_tree (tree_decl 1)
    [leaf_ctor;with_type node_ctor (pi (EApp (EConst reserved []) tree_ty) tree_ty)]
    [tree_rec;tree_aux_rec] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Module DependentParameters.

Definition a_type := loc "a_type" ty.
Definition a_value := loc "a_value" (local_expr a_type).
Definition parameters := [a_type;a_value].
Definition tname := nm "DependentNestedTree".
Definition t := apply_locals (EConst tname []) parameters.
Definition cleaf := NameStr tname "leaf".
Definition cnode := NameStr tname "node".
Definition raux := NameStr tname "rec_1".
Definition motive_t := loc "motive_t" (pi t (ESort (LParam v))).
Definition motive_b := loc "motive_b" (pi (box_at t) (ESort (LParam v))).
Definition minor_leaf := loc "minor_leaf"
  (EApp (local_expr motive_t) (apply_locals (EConst cleaf []) parameters)).
Definition field_b := loc "field_b" (box_at t).
Definition ih_b := loc "ih_b" (EApp (local_expr motive_b) (local_expr field_b)).
Definition minor_node := loc "minor_node" (close_pi [field_b;ih_b]
  (EApp (local_expr motive_t)
    (apply_locals (EConst cnode []) (List.app parameters [field_b])))).
Definition field_t := loc "field_t" t.
Definition ih_t := loc "ih_t" (EApp (local_expr motive_t) (local_expr field_t)).
Definition minor_box := loc "minor_box" (close_pi [field_t;ih_t]
  (EApp (local_expr motive_b) (box_val t (local_expr field_t)))).
Definition prefix := List.app parameters [motive_t;motive_b;minor_leaf;minor_node;minor_box].
Definition idecl := ind_decl tname 2 1 [cleaf;cnode] true (close_pi parameters ty).
Definition leaf_decl := ctor_decl cleaf tname 0 2 0 (close_pi parameters t).
Definition node_decl := ctor_decl cnode tname 1 2 1 (close_pi parameters (pi (box_at t) t)).
Definition leaf_iota := {| rule_ctor := cleaf; rule_nfields := 0;
  rule_rhs := close_lam prefix (local_expr minor_leaf) |}.
Definition node_iota := {| rule_ctor := cnode; rule_nfields := 1;
  rule_rhs := close_lam (List.app prefix [field_b])
    (apply_exprs (local_expr minor_node) [local_expr field_b;
      apply_locals (EConst raux [LParam v]) (List.app prefix [field_b])]) |}.
Definition box_iota := {| rule_ctor := box_mk; rule_nfields := 1;
  rule_rhs := close_lam (List.app prefix [field_t])
    (apply_exprs (local_expr minor_box) [local_expr field_t;
      apply_locals (EConst (rec_name tname) [LParam v]) (List.app prefix [field_t])]) |}.
Definition main_rec := rec_decl (rec_name tname) tname 2 2 3
  (close_pi (List.app prefix [field_t]) (EApp (local_expr motive_t) (local_expr field_t)))
  [leaf_iota;node_iota].
Definition aux_rec := rec_decl raux tname 2 2 3
  (close_pi (List.app prefix [field_b]) (EApp (local_expr motive_b) (local_expr field_b)))
  [box_iota].
Definition admission (recs : list declaration) :=
  env <- box_admission ;; admit_inductive_nested 300 env [idecl] [leaf_decl;node_decl] recs.

Example dependent_nested_baseline_accepted : accepts (admission [main_rec;aux_rec]) = true.
Proof. vm_compute. reflexivity. Qed.
Example dependent_constructor_round_trip :
  match box_admission with
  | Accept env =>
    match eliminate_nested 180 env [] 2
      [{| spec_decl := idecl; spec_ctors := [leaf_decl;node_decl] |}] with
    | Accept r =>
      match map_result (fun d => restore_nested_type 180 [] r [] (decl_type d))
        (flat_map spec_ctors (firstn 1 (nested_specs r))) with
      | Accept ts => list_eqb expr_eqb ts [decl_type leaf_decl;decl_type node_decl] &&
          Nat.eqb (List.length (free_context (nested_context r))) 2 &&
          Nat.eqb (nested_aux_count r) 1
      | _ => false end
    | _ => false end
  | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example dependent_forged_auxiliary_rule_rejected :
  admission [main_rec;with_rules aux_rec
    [{| rule_ctor := box_mk; rule_nfields := 1;
        rule_rhs := close_lam (List.app prefix [field_t])
          (apply_locals (EConst cleaf []) parameters) |}]] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

End DependentParameters.

Print Assumptions genuine_nested_baseline_accepted.
Print Assumptions nested_forged_auxiliary_rule_body_rejected.
Print Assumptions DependentParameters.dependent_nested_baseline_accepted.

End NestedRegression.
