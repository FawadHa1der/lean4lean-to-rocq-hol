(* SPDX-License-Identifier: Apache-2.0
   Restoration and checked admission from Lean4Lean/Inductive/Add.lean. *)
From Stdlib Require Import List String Bool Arith DecimalString DecimalNat.
From LeanPort Require Import Syntax Universes Checker Declarations InductiveUtils Inductive NestedTransform.
Import ListNotations.
Open Scope string_scope.

Fixpoint restore_lookup (n : name) (mapping : list (expr * name)) : option expr :=
  match mapping with
  | [] => None
  | (e,m)::mapping => if name_eqb n m then Some e else restore_lookup n mapping
  end.
Fixpoint restore_name (n : name) (mapping : list (name * name)) : name :=
  match mapping with
  | [] => n
  | (old,new)::mapping => if name_eqb old n then new else restore_name n mapping
  end.
Fixpoint local_replacement (n : name) (ps : list ind_local) (values : list expr) : option expr :=
  match ps,values with
  | p::ps,v::vs => if name_eqb n (il_id p) then Some v else local_replacement n ps vs
  | _,_ => None
  end.
Fixpoint instantiate_locals (ps : list ind_local) (values : list expr) (depth : nat) (e : expr) : expr :=
  match e with
  | EFVar n => match local_replacement n ps values with
    | Some v => lift depth 0 v | None => e end
  | EApp f a => EApp (instantiate_locals ps values depth f) (instantiate_locals ps values depth a)
  | ELam n bi a b => ELam n bi (instantiate_locals ps values depth a)
      (instantiate_locals ps values (S depth) b)
  | EPi n bi a b => EPi n bi (instantiate_locals ps values depth a)
      (instantiate_locals ps values (S depth) b)
  | ELet n a v b nd => ELet n (instantiate_locals ps values depth a)
      (instantiate_locals ps values depth v) (instantiate_locals ps values (S depth) b) nd
  | EProj n i a => EProj n i (instantiate_locals ps values depth a)
  | EMData a => EMData (instantiate_locals ps values depth a)
  | _ => e
  end.

Definition nested_ctor_pattern (generated : environment) (res : nested_elimination) (n : name)
    : option (expr * name) :=
  match find_decl n generated with
  | Some d => match decl_kind_of d with
    | DConstructor c => match restore_lookup (ctor_induct c) (nested_mapping res) with
      | Some pattern => Some (pattern,ctor_induct c)
      | None => None
      end
    | _ => None
    end
  | None => None
  end.
Definition restore_ctor_name (fuel : nat) (generated : environment)
    (res : nested_elimination) (n : name) : result name :=
  match nested_ctor_pattern generated res n with
  | None => Accept n
  | Some (pattern,aux) =>
    match fst (split_app pattern) with
    | EConst original _ => nested_replace_prefix fuel aux original n
    | _ => Reject MalformedDeclaration
    end
  end.

Definition rewrite_nested_head (fuel : nat) (generated : environment)
    (res : nested_elimination) (rec_map : list (name * name))
    (n : name) (us : list level) (args : list expr) : result expr :=
  let np := List.length (nested_params res) in
  match restore_lookup n (nested_mapping res) with
  | Some pattern =>
    _ <- require (np <=? List.length args)%nat MalformedDeclaration ;;
    Accept (apply_exprs
      (instantiate_locals (nested_params res) (firstn np args) 0 pattern) (skipn np args))
  | None =>
    match nested_ctor_pattern generated res n with
    | Some (pattern,aux) =>
      _ <- require (np <=? List.length args)%nat MalformedDeclaration ;;
      let pattern := instantiate_locals (nested_params res) (firstn np args) 0 pattern in
      let '(head,parameters) := split_app pattern in
      match head with
      | EConst original levels =>
        ctor <- nested_replace_prefix fuel aux original n ;;
        Accept (apply_exprs (EConst ctor levels) (List.app parameters (skipn np args)))
      | _ => Reject MalformedDeclaration
      end
    | None => Accept (apply_exprs (EConst (restore_name n rec_map) us) args)
    end
  end.

Fixpoint restore_nested_expr (fuel : nat) (generated : environment)
    (res : nested_elimination) (rec_map : list (name * name)) (e : expr) : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match e with
    | EApp _ _ =>
      let '(head,args) := split_app e in
      args <- map_result (restore_nested_expr fuel generated res rec_map) args ;;
      match head with
      | EConst n us => rewrite_nested_head fuel generated res rec_map n us args
      | _ => head <- restore_nested_expr fuel generated res rec_map head ;;
             Accept (apply_exprs head args)
      end
    | EConst n us => rewrite_nested_head fuel generated res rec_map n us []
    | ELam n bi a b =>
      a <- restore_nested_expr fuel generated res rec_map a ;;
      b <- restore_nested_expr fuel generated res rec_map b ;;
      Accept (ELam n bi a b)
    | EPi n bi a b =>
      a <- restore_nested_expr fuel generated res rec_map a ;;
      b <- restore_nested_expr fuel generated res rec_map b ;;
      Accept (EPi n bi a b)
    | ELet n a v b nd =>
      a <- restore_nested_expr fuel generated res rec_map a ;;
      v <- restore_nested_expr fuel generated res rec_map v ;;
      b <- restore_nested_expr fuel generated res rec_map b ;;
      Accept (ELet n a v b nd)
    | EProj n i a =>
      a <- restore_nested_expr fuel generated res rec_map a ;; Accept (EProj n i a)
    | EMData a => a <- restore_nested_expr fuel generated res rec_map a ;; Accept (EMData a)
    | _ => Accept e
    end
  end.

Fixpoint restore_open (count : nat) (s : ind_state) (e : expr)
    : result (list ind_local * expr) :=
  match count with
  | 0 => Accept ([],e)
  | S count =>
    match e with
    | EPi n bi a b | ELam n bi a b =>
      let '(x,s) := ind_fresh s n bi a in
      rest <- restore_open count s (instantiate b (local_expr x)) ;;
      let '(xs,body) := rest in Accept (x::xs,body)
    | _ => Reject MalformedDeclaration
    end
  end.
Definition restore_nested_type (fuel : nat) (generated : environment)
    (res : nested_elimination) (rec_map : list (name * name)) (e : expr) : result expr :=
  opened <- restore_open (List.length (nested_params res)) initial_ind_state e ;;
  let '(params,body) := opened in
  (* Maps in the elimination result use the common parameter locals. Rebase
     them to the newly opened telescope before restoring its body. *)
  let mapping := map (fun entry =>
    let '(pattern,n) := entry in
    (instantiate_locals (nested_params res) (local_exprs params) 0 pattern,n)) (nested_mapping res) in
  let rebased := {| nested_params := params; nested_context := nested_context res;
    nested_specs := nested_specs res; nested_mapping := mapping;
    nested_aux_names := nested_aux_names res; nested_aux_count := nested_aux_count res |} in
  body <- restore_nested_expr fuel generated rebased rec_map body ;;
  match e with EPi _ _ _ _ => Accept (close_pi params body)
  | _ => Accept (close_lam params body) end.

Definition indexed_rec_name (main : name) (i : nat) :=
  NameStr main ("rec_" ++ NilZero.string_of_uint (Nat.to_uint i)).
Fixpoint auxiliary_rec_names (main : name) (names : list name) (i : nat)
    : list (name * name) :=
  match names with
  | [] => []
  | n::names => (rec_name n,indexed_rec_name main i)::auxiliary_rec_names main names (S i)
  end.

Definition restore_rule (fuel : nat) (generated : environment) (res : nested_elimination)
    (rec_map : list (name * name)) (r : recursor_rule) : result recursor_rule :=
  ctor <- restore_ctor_name fuel generated res (rule_ctor r) ;;
  rhs <- restore_nested_type fuel generated res rec_map (rule_rhs r) ;;
  Accept {| rule_ctor := ctor; rule_nfields := rule_nfields r; rule_rhs := rhs |}.

Definition restore_recursor (fuel : nat) (generated : environment) (res : nested_elimination)
    (rec_map : list (name * name)) (all : list name) (old : name) : result declaration :=
  match find_decl old generated with
  | Some d => match decl_kind_of d with
    | DRecursor info =>
      ty <- restore_nested_type fuel generated res rec_map (decl_type d) ;;
      rules <- map_result (restore_rule fuel generated res rec_map) (rec_rules info) ;;
      Accept {| decl_hints := HintOpaque; decl_name := restore_name old rec_map; decl_params := decl_params d;
        decl_type := ty; decl_value := None;
        decl_kind_of := DRecursor {| rec_all := all; rec_num_params := rec_num_params info;
          rec_num_indices := rec_num_indices info; rec_num_motives := rec_num_motives info;
          rec_num_minors := rec_num_minors info; rec_rules := rules;
          rec_k := rec_k info; rec_is_unsafe := rec_is_unsafe info |} |}
    | _ => Reject MalformedDeclaration
    end
  | None => Reject UnknownConstant
  end.

Definition restore_constructor (fuel : nat) (generated : environment) (res : nested_elimination)
    (n : name) : result declaration :=
  match find_decl n generated with
  | Some d => match decl_kind_of d with
    | DConstructor info =>
      ty <- restore_nested_type fuel generated res [] (decl_type d) ;;
      Accept {| decl_hints := HintOpaque; decl_name := n; decl_params := decl_params d; decl_type := ty;
        decl_value := None; decl_kind_of := DConstructor info |}
    | _ => Reject MalformedDeclaration
    end
  | None => Reject UnknownConstant
  end.

Definition restore_inductive (generated : environment) (res : nested_elimination)
    (all : list name) (n : name) : result declaration :=
  match find_decl n generated with
  | Some d => match decl_kind_of d with
    | DInductive info =>
      Accept {| decl_hints := HintOpaque; decl_name := n; decl_params := decl_params d; decl_type := decl_type d;
        decl_value := None;
        decl_kind_of := DInductive {| ind_num_params := ind_num_params info;
          ind_num_indices := ind_num_indices info; ind_all := all; ind_ctors := ind_ctors info;
          ind_num_nested := nested_aux_count res; ind_is_rec := ind_is_rec info;
          ind_is_reflexive := ind_is_reflexive info; ind_is_unsafe := ind_is_unsafe info |} |}
    | _ => Reject MalformedDeclaration
    end
  | None => Reject UnknownConstant
  end.

Fixpoint name_prefix (prefix n : name) : bool :=
  if name_eqb prefix n then true else
  match n with NameStr p _ | NameNum p _ => name_prefix prefix p | NameAnon => false end.
Fixpoint uses_reserved_nested (e : expr) : bool :=
  match e with
  | EConst n _ => name_prefix (NameStr NameAnon "_nested") n
  | EProj n _ a => name_prefix (NameStr NameAnon "_nested") n || uses_reserved_nested a
  | EApp a b | EPi _ _ a b | ELam _ _ a b => uses_reserved_nested a || uses_reserved_nested b
  | ELet _ a v b _ => uses_reserved_nested a || uses_reserved_nested v || uses_reserved_nested b
  | EMData a => uses_reserved_nested a
  | _ => false
  end.

Definition admit_inductive_nested (fuel : nat) (env : environment)
    (types ctors recs : list declaration) : result environment :=
  prepared <- prepare_inductive env types ctors recs ;;
  let '(ps,np,specs) := prepared in
  _ <- require (negb (existsb (fun d => uses_reserved_nested (decl_type d)) ctors))
                MalformedDeclaration ;;
  transformed <- eliminate_nested fuel env ps np specs ;;
  generated <- derive_inductive fuel env ps np (nested_specs transformed) ;;
  if Nat.eqb (nested_aux_count transformed) 0 then
    _ <- verify_members (List.app types (List.app ctors recs)) generated ;;
    Accept (List.app generated env)
  else
    match types with
    | [] => Reject MalformedDeclaration
    | main::_ =>
      let all := ind_names types in
      let auxiliary := skipn (List.length types)
        (map (fun s => decl_name (spec_decl s)) (nested_specs transformed)) in
      let rec_map := auxiliary_rec_names (decl_name main) auxiliary 1 in
      restored_inds <- map_result (restore_inductive generated transformed all) all ;;
      restored_ctors <- map_result (restore_constructor fuel generated transformed) (ind_names ctors) ;;
      restored_recs <- map_result (restore_recursor fuel generated transformed rec_map all)
        (map rec_name (List.app all auxiliary)) ;;
      let restored := List.app restored_recs (List.app restored_ctors restored_inds) in
      _ <- verify_members (List.app types (List.app ctors recs)) restored ;;
      let final_env := List.app restored env in
      _ <- map_result (fun entry =>
        inferred <- infer fuel final_env ps (nested_context transformed) (fst entry) ;; Accept tt)
        (nested_mapping transformed) ;;
      Accept final_env
    end.
