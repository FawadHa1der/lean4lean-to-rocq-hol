(* SPDX-License-Identifier: Apache-2.0
   Test-only fixtures. Every positive environment is built through checked
   declaration admission. Seed tags describe inputs; none is installed directly. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Checker Primitives Declarations InductiveUtils
  Inductive Quotient DagScope DagArena IndexedDagAdmission CombinedAdmissionRefinement
  PreparedDagLookup LookupIntegration RuntimeChecker.
Import ListNotations.
Open Scope string_scope.

Module Metadata.
Definition fuel := 256.
Definition label s := NameStr (NameStr NameAnon "MetadataTest") s.
Definition pi a b := EPi NameAnon BDefault a b.
Definition lam a b := ELam NameAnon BDefault a b.
Definition type0 := ESort (LSucc LZero).
Definition type1 := ESort (LSucc (LSucc LZero)).
Definition decl n ps ty kind := {| decl_hints := HintOpaque; decl_name := n; decl_params := ps;
  decl_type := ty; decl_value := None; decl_kind_of := kind |}.
Definition seed_ind n ps ty np ctors := decl n ps ty (DInductive
  {| ind_num_params := np; ind_num_indices := 0; ind_all := [n]; ind_ctors := ctors;
     ind_num_nested := 0; ind_is_rec := false; ind_is_reflexive := false;
     ind_is_unsafe := false |}).
Definition seed_ctor n owner ps ty np i fields := decl n ps ty (DConstructor
  {| ctor_induct := owner; ctor_index := i; ctor_num_params := np;
     ctor_num_fields := fields; ctor_is_unsafe := false |}).
Definition is_ind d := match decl_kind_of d with DInductive _ => true | _ => false end.
Definition is_ctor d := match decl_kind_of d with DConstructor _ => true | _ => false end.
Definition is_rec d := match decl_kind_of d with DRecursor _ => true | _ => false end.
Definition admit_generated env ds := admit_inductive fuel env
  (filter is_ind ds) (filter is_ctor ds) (filter is_rec ds).
Definition checked_block env ps np specs :=
  generated <- derive_inductive fuel env ps np specs ;;
  admit_generated env generated.

Fixpoint padding count : result environment :=
  match count with
  | 0 => Accept []
  | S n => env <- padding n ;;
    Declarations.admit fuel env (InputAxiom (NameNum (label "pad") (N.of_nat n))
      [] (ESort LZero) false)
  end.
Definition nat_spec := {| spec_decl := seed_ind core_nat_name [] type0 0
  [core_zero_name;core_succ_name]; spec_ctors :=
  [seed_ctor core_zero_name core_nat_name [] core_nat 0 0 0;
   seed_ctor core_succ_name core_nat_name [] (pi core_nat core_nat) 0 1 1] |}.
Definition u_name := NameStr NameAnon "u".
Definition u := LParam u_name.
Definition refl_name := NameStr q_eq_name "refl".
Definition eq_spec := {| spec_decl := seed_ind q_eq_name [u_name]
  (quotient_eq_type u) 2 [refl_name]; spec_ctors :=
  [seed_ctor refl_name q_eq_name [u_name] (quotient_eq_refl_type u) 2 0 0] |}.
Definition box_name := label "Box".
Definition box_mk := NameStr box_name "mk".
Definition box := EConst box_name [].
Definition box_spec := {| spec_decl := seed_ind box_name [] type0 0 [box_mk];
  spec_ctors := [seed_ctor box_mk box_name [] (pi core_nat box) 0 0 1] |}.
Definition dep_name := label "Dependent".
Definition dep_mk := NameStr dep_name "mk".
Definition dep := EConst dep_name [].
Definition dep_spec := {| spec_decl := seed_ind dep_name [] type1 0 [dep_mk];
  spec_ctors := [seed_ctor dep_mk dep_name [] (pi type0 (pi (EBVar 0) dep)) 0 0 2] |}.
Definition padded_env := padding 64.
Definition nat_env := env <- padded_env ;; checked_block env [] 0 [nat_spec].
Definition eq_env := env <- nat_env ;; checked_block env [u_name] 2 [eq_spec].
Definition structure_env :=
  env <- eq_env ;; env <- checked_block env [] 0 [box_spec] ;;
  checked_block env [] 0 [dep_spec].
Definition add_quot env k := let d := canonical_quotient k in
  admit_quotient fuel env (decl_name d) (decl_params d) (decl_type d) k.
Definition base_env := env <- structure_env ;;
  env <- add_quot env QType ;; env <- add_quot env QCtor ;;
  env <- add_quot env QLift ;; add_quot env QInd.

Definition fold ty z step n := core_apps (EConst (rec_name core_nat_name) [LSucc LZero])
  [lam core_nat ty;z;step;n].
Definition add_body := lam core_nat (lam core_nat
  (fold core_nat (EBVar 1) (lam core_nat (lam core_nat (primitive_succ (EBVar 0))))
    (EBVar 0))).
Definition false_add := lam core_nat (lam core_nat (EBVar 1)).
Definition rec_value := fold core_nat primitive_one
  (lam core_nat (lam core_nat (EBVar 0))) primitive_two.
Definition eq_nat a b := core_apps (EConst q_eq_name [LSucc LZero]) [core_nat;a;b].
Definition refl_nat a := core_apps (EConst refl_name [LSucc LZero]) [core_nat;a].
Definition indexed_rec_value := core_apps (EConst (rec_name q_eq_name) [LSucc LZero;LSucc LZero])
  [core_nat;primitive_one;
   lam core_nat (lam (eq_nat primitive_one (EBVar 0)) core_nat);
   primitive_one;primitive_one;refl_nat primitive_one].
Definition box_value := EApp (EConst box_mk []) primitive_one.
Definition dep_value := core_apps (EConst dep_mk []) [core_nat;primitive_one].
Definition project_box := EProj box_name 0 box_value.
Definition project_dep := EProj dep_name 1 dep_value.
Definition project_dep_fn := lam dep (EProj dep_name 1 (EBVar 0)).
Definition project_dep_type := pi dep (EProj dep_name 0 (EBVar 0)).
Definition relation := lam core_nat (lam core_nat (eq_nat (EBVar 1) (EBVar 0))).
Definition identity := lam core_nat (EBVar 0).
Definition respect := lam core_nat (lam core_nat
  (lam (eq_nat (EBVar 1) (EBVar 0)) (EBVar 0))).
Definition quot := core_apps (EConst q_name [LSucc LZero]) [core_nat;relation].
Definition quot_value := core_apps (EConst q_mk_name [LSucc LZero])
  [core_nat;relation;primitive_one].
Definition lift_value := core_apps (EConst q_lift_name [LSucc LZero;LSucc LZero])
  [core_nat;relation;core_nat;identity;respect;quot_value].
Definition ind_value := core_apps (EConst q_ind_name [LSucc LZero])
  [core_nat;relation;lam quot (eq_nat primitive_one primitive_one);
   lam core_nat (refl_nat primitive_one);quot_value].
Definition add_value := primitive_call PNatAdd [primitive_one;primitive_one].
Definition with_add := env <- base_env ;;
  Declarations.admit fuel env (InputDefinition HintOpaque (primitive_name PNatAdd) []
    (primitive_signature PNatAdd) add_body InputSafe).

Definition fixture_shape_checks := env <- base_env ;;
  Accept (core_nat_ready env &&
    match find_decl (rec_name q_eq_name) env, find_decl dep_mk env with
    | Some r,Some c => match decl_kind_of r,decl_kind_of c with
      | DRecursor r,DConstructor c => Nat.eqb (rec_num_indices r) 1 &&
          Nat.eqb (rec_num_params r) 2 && Nat.eqb (ctor_num_fields c) 2
      | _,_ => false end
    | _,_ => false end).

(* Negative-only corruptions never initialize a positive environment. *)
Definition without n env := filter (fun d => negb (name_eqb n (decl_name d))) env.
Definition unsafe_shadow n env := match find_decl n env with
  | None => env
  | Some d => {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
    decl_type := decl_type d; decl_value := decl_value d;
    decl_kind_of := DUnsafe (decl_kind_of d) |} :: env end.
Definition corrupt_fields d := match decl_kind_of d with
  | DConstructor c => {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
    decl_type := decl_type d; decl_value := decl_value d;
    decl_kind_of := DConstructor {| ctor_induct := ctor_induct c;
      ctor_index := ctor_index c; ctor_num_params := ctor_num_params c;
      ctor_num_fields := S (ctor_num_fields c); ctor_is_unsafe := ctor_is_unsafe c |} |}
  | _ => d end.
Definition corrupt_rule d := match decl_kind_of d with
  | DRecursor r => {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
    decl_type := decl_type d; decl_value := decl_value d;
    decl_kind_of := DRecursor {| rec_all := rec_all r; rec_num_params := rec_num_params r;
      rec_num_indices := rec_num_indices r; rec_num_motives := rec_num_motives r;
      rec_num_minors := rec_num_minors r; rec_rules := [];
      rec_k := rec_k r; rec_is_unsafe := rec_is_unsafe r |} |}
  | _ => d end.
Definition rejected_ctor_metadata := env <- padded_env ;;
  ds <- derive_inductive fuel env [] 0 [nat_spec] ;;
  admit_generated env (map corrupt_fields ds).
Definition rejected_rec_metadata := env <- padded_env ;;
  ds <- derive_inductive fuel env [] 0 [nat_spec] ;;
  admit_generated env (map corrupt_rule ds).
Definition rejected_quot_signature := env <- structure_env ;;
  admit_quotient fuel env q_name [u_name] type0 QType.
Definition missing_eq_quot := env <- nat_env ;; add_quot env QType.

Definition accepted {A} (x : result A) := match x with Accept _ => true | _ => false end.
Definition reject_reason_of {A} (x : result A) :=
  match x with Reject r => Some r | _ => None end.
End Metadata.
