(* SPDX-License-Identifier: Apache-2.0
   Private accessor-integration pilot. No production checker change. *)
From Stdlib Require Import List Bool NArith.
From LeanPort Require Import Syntax Checker EnvironmentIndex.
Import ListNotations.

Definition declaration_lookup := name -> option declaration.
Definition linear_lookup (env : environment) : declaration_lookup :=
  fun n => find_decl n env.
Definition prepare_lookup (hash : name -> N) (env : environment) : declaration_lookup :=
  let index := index_environment hash env in
  fun n => indexed_find_decl hash n index.

Theorem prepare_lookup_correct hash env n :
  prepare_lookup hash env n = find_decl n env.
Proof. apply indexed_environment_lookup. Qed.

Definition lookup_get_constant (lookup : declaration_lookup) (ps : list name)
    (n : name) (us : list level) : result declaration :=
  match lookup n with
  | None => Reject UnknownConstant
  | Some d =>
      match decl_kind_of d with
      | DUnsupported => Decline UnsupportedDeclaration
      | DUnsafe _ | DPartial => Reject MalformedDeclaration
      | _ =>
          ignored <- require (Nat.eqb (List.length (decl_params d)) (List.length us))
                             UniverseArity ;;
          ignored <- check_levels ps us ;; Accept d
      end
  end.

Lemma lookup_get_constant_refines lookup env ps n us :
  (forall key, lookup key = find_decl key env) ->
  lookup_get_constant lookup ps n us = get_constant env ps n us.
Proof. intro H. unfold lookup_get_constant, get_constant. now rewrite H. Qed.

Corollary prepared_get_constant_refines hash env ps n us :
  lookup_get_constant (prepare_lookup hash env) ps n us = get_constant env ps n us.
Proof. apply lookup_get_constant_refines. apply prepare_lookup_correct. Qed.

Definition lookup_ctor_shape (lookup : declaration_lookup) (n parent : name)
    (index fields : nat) (ty : expr) : bool :=
  match lookup n with
  | Some d =>
      match decl_kind_of d with
      | DConstructor c => name_eqb (ctor_induct c) parent &&
          Nat.eqb (ctor_index c) index && Nat.eqb (ctor_num_params c) 0 &&
          Nat.eqb (ctor_num_fields c) fields && negb (ctor_is_unsafe c) &&
          Nat.eqb (List.length (decl_params d)) 0 && expr_eqb (decl_type d) ty
      | _ => false
      end
  | None => false
  end.

Definition lookup_nat_ready (lookup : declaration_lookup) : bool :=
  match lookup core_nat_name with
  | Some d =>
      match decl_kind_of d with
      | DInductive i =>
          Nat.eqb (List.length (decl_params d)) 0 &&
          expr_eqb (decl_type d) (ESort (LSucc LZero)) &&
          Nat.eqb (ind_num_params i) 0 && Nat.eqb (ind_num_indices i) 0 &&
          negb (ind_is_unsafe i) &&
          list_eqb name_eqb (ind_ctors i) [core_zero_name; core_succ_name] &&
          lookup_ctor_shape lookup core_zero_name core_nat_name 0 0 core_nat &&
          lookup_ctor_shape lookup core_succ_name core_nat_name 1 1
            (EPi NameAnon BDefault core_nat core_nat)
      | _ => false
      end
  | None => false
  end.

Lemma lookup_ctor_shape_refines lookup env n parent index fields ty :
  (forall key, lookup key = find_decl key env) ->
  lookup_ctor_shape lookup n parent index fields ty =
    core_ctor_shape env n parent index fields ty.
Proof. intro H. unfold lookup_ctor_shape, core_ctor_shape. now rewrite H. Qed.

Lemma lookup_nat_ready_refines lookup env :
  (forall key, lookup key = find_decl key env) ->
  lookup_nat_ready lookup = core_nat_ready env.
Proof.
  intro H. unfold lookup_nat_ready, core_nat_ready. rewrite H.
  destruct (find_decl core_nat_name env) as [d|]; auto.
  destruct (decl_kind_of d); auto.
  repeat rewrite (lookup_ctor_shape_refines lookup env) by exact H.
  reflexivity.
Qed.

Corollary prepared_nat_ready_refines hash env :
  lookup_nat_ready (prepare_lookup hash env) = core_nat_ready env.
Proof. apply lookup_nat_ready_refines. apply prepare_lookup_correct. Qed.

Definition fixture (n : name) (kind : decl_kind) : declaration :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := ESort LZero;
     decl_value := None; decl_kind_of := kind |}.
Definition all_collide (_ : name) := 0%N.

Example prepared_missing_constant_rejects :
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon DAssumption])
    [] (NameNum NameAnon 0) [] = Reject UnknownConstant.
Proof. vm_compute. reflexivity. Qed.
Example prepared_unsafe_shadow_rejects :
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon (DUnsafe DOpaque);
      fixture NameAnon DAssumption]) [] NameAnon [] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example prepared_partial_rejects :
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon DPartial])
    [] NameAnon [] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example prepared_unsupported_declines :
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon DUnsupported])
    [] NameAnon [] = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example prepared_contexts_do_not_share_views :
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon (DUnsafe DOpaque)])
      [] NameAnon [] = Reject MalformedDeclaration /\
  lookup_get_constant (prepare_lookup all_collide [fixture NameAnon DOpaque])
      [] NameAnon [] = Accept (fixture NameAnon DOpaque).
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions prepared_get_constant_refines.
Print Assumptions prepared_nat_ready_refines.
