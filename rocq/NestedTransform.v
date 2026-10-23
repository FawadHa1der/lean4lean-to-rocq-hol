(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Changed Gallina port of ElimNestedInductive in Lean4Lean/Inductive/Add.lean,
   upstream 8223d223ed98661882e95d9d6a7126df7097cd76. See NOTICE.
   This transforms syntax only. The caller must check the extended mutual
   declaration, restore auxiliary names, and compare all exported metadata. *)
From Stdlib Require Import List String Bool Arith NArith.
From LeanPort Require Import Syntax Universes Checker Declarations InductiveUtils Inductive.
Import ListNotations.
Open Scope string_scope.

Record nested_elimination := {
  nested_params : list ind_local;
  nested_context : context;
  nested_specs : list ind_spec;
  nested_mapping : list (expr * name);
  nested_aux_names : list name;
  nested_aux_count : nat
}.

Record nested_work := {
  nw_specs : list ind_spec;
  nw_mapping : list (expr * name);
  nw_next_aux : nat;
  nw_next_local : nat
}.

Definition nested_set_specs (w : nested_work) (specs : list ind_spec) :=
  {| nw_specs := specs; nw_mapping := nw_mapping w;
     nw_next_aux := nw_next_aux w; nw_next_local := nw_next_local w |}.

Definition nested_set_local (w : nested_work) (next : nat) :=
  {| nw_specs := nw_specs w; nw_mapping := nw_mapping w;
     nw_next_aux := nw_next_aux w; nw_next_local := next |}.

(* Unlike admission telescopes, the upstream transformation opens raw Pis,
   without normalization or checking domains containing the new constants. *)
Fixpoint nested_open_params (fuel count : nat) (s : ind_state) (ty : expr)
    : result (list ind_local * expr * ind_state) :=
  match count with
  | 0 => Accept ([],ty,s)
  | S count =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      match ty with
      | EPi n bi a b =>
        let '(x,s) := ind_fresh s n bi a in
        rest <- nested_open_params fuel count s (instantiate b (local_expr x)) ;;
        let '(xs,body,s) := rest in Accept (x::xs,body,s)
      | _ => Reject MalformedDeclaration
      end
    end
  end.

Fixpoint nested_instantiate_params (fuel : nat) (args : list expr) (ty : expr)
    : result expr :=
  match args with
  | [] => Accept ty
  | a::args =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      match ty with
      | EPi _ _ _ body => nested_instantiate_params fuel args (instantiate body a)
      | _ => Decline UnsupportedDeclaration
      end
    end
  end.

Fixpoint nested_lookup_local (fuel : nat) (n : name) (xs ys : list ind_local)
    : result expr :=
  match xs,ys with
  | [],[] => Accept (EFVar n)
  | x::xs,y::ys =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      if name_eqb n (il_id x) then Accept (local_expr y)
      else nested_lookup_local fuel n xs ys
    end
  | _,_ => Decline UnsupportedDeclaration
  end.

(* Simultaneous renaming is abstract/instantiate on these closed local
   variables. It leaves binders and every unrelated free variable untouched. *)
Fixpoint nested_rebase (fuel : nat) (from to : list ind_local) (e : expr)
    : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match e with
    | EFVar n => nested_lookup_local fuel n from to
    | EApp a b => a <- nested_rebase fuel from to a ;;
        b <- nested_rebase fuel from to b ;; Accept (EApp a b)
    | ELam n bi a b => a <- nested_rebase fuel from to a ;;
        b <- nested_rebase fuel from to b ;; Accept (ELam n bi a b)
    | EPi n bi a b => a <- nested_rebase fuel from to a ;;
        b <- nested_rebase fuel from to b ;; Accept (EPi n bi a b)
    | ELet n a v b nd => a <- nested_rebase fuel from to a ;;
        v <- nested_rebase fuel from to v ;;
        b <- nested_rebase fuel from to b ;; Accept (ELet n a v b nd)
    | EProj n i a => a <- nested_rebase fuel from to a ;; Accept (EProj n i a)
    | EMData a => a <- nested_rebase fuel from to a ;; Accept (EMData a)
    | _ => Accept e
    end
  end.

Fixpoint nested_has_new (fuel : nat) (names : list name) (e : expr) : result bool :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match e with
    | EConst n _ => Accept (name_mem n names)
    | EApp a b | ELam _ _ a b | EPi _ _ a b =>
      a <- nested_has_new fuel names a ;;
      if a then Accept true else nested_has_new fuel names b
    | ELet _ a v b _ =>
      a <- nested_has_new fuel names a ;;
      if a then Accept true else
      v <- nested_has_new fuel names v ;;
      if v then Accept true else nested_has_new fuel names b
    | EProj _ _ a | EMData a => nested_has_new fuel names a
    | _ => Accept false
    end
  end.

Fixpoint nested_any_new (fuel : nat) (names : list name) (args : list expr)
    : result bool :=
  match args with
  | [] => Accept false
  | a::args =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      found <- nested_has_new fuel names a ;;
      if found then Accept true else nested_any_new fuel names args
    end
  end.

Definition nested_candidate (fuel : nat) (env : environment) (w : nested_work)
    (e : expr) : result (option (declaration * inductive_data * list level * list expr)) :=
  let '(head,args) := split_app e in
  match args,head with
  | _::_, EConst n us =>
    match find_decl n env with
    | Some d =>
      match decl_kind_of d with
      | DInductive data =>
        if Nat.leb (ind_num_params data) (List.length args) then
          let params := firstn (ind_num_params data) args in
          found <- nested_any_new fuel (map (fun s => decl_name (spec_decl s)) (nw_specs w)) params ;;
          if found then
            if forallb (scoped 0) params then Accept (Some (d,data,us,args))
            else Reject MalformedDeclaration
          else Accept None
        else Accept None
      | _ => Accept None
      end
    | None => Accept None
    end
  | _,_ => Accept None
  end.

(* Lean's Expr.eqv ignores binder annotations but compares the let nonDep
   flag. Syntax.expr_eqb deliberately ignores that optimization flag. *)
Fixpoint nested_same_flags (fuel : nat) (a b : expr) : result bool :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match a,b with
    | EApp a b,EApp c d | ELam _ _ a b,ELam _ _ c d | EPi _ _ a b,EPi _ _ c d =>
      same <- nested_same_flags fuel a c ;;
      if same then nested_same_flags fuel b d else Accept false
    | ELet _ a v b nd,ELet _ c w d md =>
      if Bool.eqb nd md then
        same <- nested_same_flags fuel a c ;;
        if same then
          same <- nested_same_flags fuel v w ;;
          if same then nested_same_flags fuel b d else Accept false
        else Accept false
      else Accept false
    | EProj _ _ a,EProj _ _ b | EMData a,EMData b => nested_same_flags fuel a b
    | _,_ => Accept true
    end
  end.

Definition nested_key_eq (fuel : nat) (a b : expr) : result bool :=
  if expr_eqb a b then nested_same_flags fuel a b else Accept false.

Fixpoint nested_find_mapping (fuel : nat) (e : expr) (mapping : list (expr * name))
    : result (option name) :=
  match mapping with
  | [] => Accept None
  | (key,n)::mapping =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      same <- nested_key_eq fuel key e ;;
      if same then Accept (Some n) else nested_find_mapping fuel e mapping
    end
  end.

Fixpoint nested_replace_prefix (fuel : nat) (old new n : name) : result name :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    if name_eqb n old then Accept new else
    match n with
    | NameStr p s => p <- nested_replace_prefix fuel old new p ;; Accept (NameStr p s)
    | NameNum p i => p <- nested_replace_prefix fuel old new p ;; Accept (NameNum p i)
    | NameAnon => Decline UnsupportedDeclaration
    end
  end.

Definition nested_aux_name (i : nat) := NameNum (NameStr NameAnon "_rocq_nested") (N.of_nat i).

Fixpoint nested_unique_aux (fuel : nat) (used : list name) (old : name)
    (ctors : list name) (index : nat) : result (name * list name * nat) :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    let aux := nested_aux_name index in
    renamed <- map_result (nested_replace_prefix fuel old aux) ctors ;;
    let reserved := aux :: rec_name aux :: renamed in
    if existsb (fun n => name_mem n used) reserved || negb (names_unique reserved)
    then nested_unique_aux fuel used old ctors (S index)
    else Accept (aux,renamed,S index)
  end.

Definition nested_used_names (env : environment) (w : nested_work) :=
  List.app (map decl_name env)
    (List.app (map (fun s => decl_name (spec_decl s)) (nw_specs w))
      (List.app (map (fun s => rec_name (decl_name (spec_decl s))) (nw_specs w))
        (all_ctor_names (nw_specs w)))).

Fixpoint nested_make_ctors (fuel : nat) (env : environment) (ps : list name)
    (As : list ind_local) (us : list level) (params : list expr) (owner : name)
    (old_names new_names : list name) (index : nat) : result (list declaration) :=
  match old_names,new_names with
  | [],[] => Accept []
  | old::olds,new::news =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      match find_decl old env with
      | Some d =>
        match decl_kind_of d with
        | DConstructor _ =>
          _ <- require (Nat.eqb (List.length (decl_params d)) (List.length us)) UniverseArity ;;
          ty <- nested_instantiate_params fuel params
            (subst_levels (decl_params d) us (decl_type d)) ;;
          rest <- nested_make_ctors fuel env ps As us params owner olds news (S index) ;;
          Accept ({| decl_hints := HintOpaque; decl_name := new; decl_params := ps; decl_type := close_pi As ty;
            decl_value := None; decl_kind_of := DConstructor
              {| ctor_induct := owner; ctor_index := index;
                 ctor_num_params := List.length As; ctor_num_fields := 0;
                 ctor_is_unsafe := false |} |} :: rest)
        | _ => Decline UnsupportedDeclaration
        end
      | None => Decline UnsupportedDeclaration
      end
    end
  | _,_ => Decline UnsupportedDeclaration
  end.

Fixpoint nested_expand_family (fuel : nat) (env : environment) (ps : list name)
    (params As : list ind_local) (us : list level) (old_params : list expr)
    (family : list name) (w : nested_work) : result nested_work :=
  match family with
  | [] => Accept w
  | old::family =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      match find_decl old env with
      | Some d =>
        match decl_kind_of d with
        | DInductive data =>
          _ <- require (Nat.eqb (List.length (decl_params d)) (List.length us)) UniverseArity ;;
          if negb (Nat.eqb (ind_num_params data) (List.length old_params))
          then Decline UnsupportedDeclaration else
          fresh <- nested_unique_aux fuel (nested_used_names env w) old (ind_ctors data) (nw_next_aux w) ;;
          let '(aux,ctor_names,next) := fresh in
          ty <- nested_instantiate_params fuel old_params
            (subst_levels (decl_params d) us (decl_type d)) ;;
          key <- nested_rebase fuel As params (apply_exprs (EConst old us) old_params) ;;
          ctors <- nested_make_ctors fuel env ps As us old_params aux (ind_ctors data) ctor_names 0 ;;
          let spec := {| spec_decl :=
            {| decl_hints := HintOpaque; decl_name := aux; decl_params := ps; decl_type := close_pi As ty;
               decl_value := None; decl_kind_of := DInductive
                 {| ind_num_params := List.length As; ind_num_indices := 0;
                    ind_all := []; ind_ctors := ctor_names; ind_num_nested := 0;
                    ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |} |};
            spec_ctors := ctors |} in
          nested_expand_family fuel env ps params As us old_params family
            {| nw_specs := List.app (nw_specs w) [spec];
               nw_mapping := List.app (nw_mapping w) [(key,aux)];
               nw_next_aux := next; nw_next_local := nw_next_local w |}
        | _ => Decline UnsupportedDeclaration
        end
      | None => Decline UnsupportedDeclaration
      end
    end
  end.

Definition nested_replace_root (fuel : nat) (env : environment) (ps : list name)
    (params As : list ind_local) (e : expr) (w : nested_work)
    : result (option expr * nested_work) :=
  candidate <- nested_candidate fuel env w e ;;
  match candidate with
  | None => Accept (None,w)
  | Some (d,data,us,args) =>
    let old_params := firstn (ind_num_params data) args in
    key <- nested_rebase fuel As params (apply_exprs (EConst (decl_name d) us) old_params) ;;
    found <- nested_find_mapping fuel key (nw_mapping w) ;;
    w <- match found with
      | Some _ => Accept w
      | None => nested_expand_family fuel env ps params As us old_params (ind_all data) w
      end ;;
    found <- nested_find_mapping fuel key (nw_mapping w) ;;
    match found with
    | Some aux => Accept (Some (apply_exprs (apply_locals (EConst aux (map LParam ps)) As)
                                  (skipn (ind_num_params data) args)),w)
    | None => Decline UnsupportedDeclaration
    end
  end.

(* Preorder replacement stops below a replaced node. Aux constructors retain
   the old references until the growing worklist visits their new specs. *)
Fixpoint nested_rewrite (fuel : nat) (env : environment) (ps : list name)
    (params As : list ind_local) (e : expr) (w : nested_work) : result (expr * nested_work) :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    replaced <- nested_replace_root fuel env ps params As e w ;;
    let '(replacement,w) := replaced in
    match replacement with
    | Some e => Accept (e,w)
    | None =>
      match e with
      | EApp a b =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        second <- nested_rewrite fuel env ps params As b w ;; let '(b,w) := second in
        Accept (EApp a b,w)
      | ELam n bi a b =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        second <- nested_rewrite fuel env ps params As b w ;; let '(b,w) := second in
        Accept (ELam n bi a b,w)
      | EPi n bi a b =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        second <- nested_rewrite fuel env ps params As b w ;; let '(b,w) := second in
        Accept (EPi n bi a b,w)
      | ELet n a v b nd =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        second <- nested_rewrite fuel env ps params As v w ;; let '(v,w) := second in
        third <- nested_rewrite fuel env ps params As b w ;; let '(b,w) := third in
        Accept (ELet n a v b nd,w)
      | EProj n i a =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        Accept (EProj n i a,w)
      | EMData a =>
        first <- nested_rewrite fuel env ps params As a w ;; let '(a,w) := first in
        Accept (EMData a,w)
      | _ => Accept (e,w)
      end
    end
  end.

Fixpoint nested_rewrite_ctors (fuel : nat) (env : environment) (ps : list name)
    (nparams : nat) (params : list ind_local) (ctors : list declaration) (w : nested_work)
    : result (list declaration * nested_work) :=
  match ctors with
  | [] => Accept ([],w)
  | d::ctors =>
    match fuel with
    | 0 => Decline OutOfFuel
    | S fuel =>
      opened <- nested_open_params fuel nparams
        {| ist_next := nw_next_local w; ist_context := empty_context |} (decl_type d) ;;
      let '(As,body,s) := opened in
      rewritten <- nested_rewrite fuel env ps params As body (nested_set_local w (ist_next s)) ;;
      let '(body,w) := rewritten in
      tail <- nested_rewrite_ctors fuel env ps nparams params ctors w ;;
      let '(rest,w) := tail in
      Accept ({| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d;
        decl_type := close_pi As body; decl_value := decl_value d;
        decl_kind_of := decl_kind_of d |} :: rest,w)
    end
  end.

Fixpoint nested_replace_spec (fuel index : nat) (spec : ind_spec) (specs : list ind_spec)
    : result (list ind_spec) :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match index,specs with
    | 0,_::rest => Accept (spec::rest)
    | S index,head::rest =>
      rest <- nested_replace_spec fuel index spec rest ;; Accept (head::rest)
    | _,[] => Decline UnsupportedDeclaration
    end
  end.

Fixpoint nested_worklist (fuel index : nat) (env : environment) (ps : list name)
    (nparams : nat) (params : list ind_local) (w : nested_work) : result nested_work :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match nth_error (nw_specs w) index with
    | None => Accept w
    | Some spec =>
      rewritten <- nested_rewrite_ctors fuel env ps nparams params (spec_ctors spec) w ;;
      let '(ctors,w) := rewritten in
      specs <- nested_replace_spec fuel index
        {| spec_decl := spec_decl spec; spec_ctors := ctors |} (nw_specs w) ;;
      nested_worklist fuel (S index) env ps nparams params (nested_set_specs w specs)
    end
  end.

Definition eliminate_nested (fuel : nat) (env : environment) (ps : list name)
    (nparams : nat) (specs : list ind_spec) : result nested_elimination :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S remaining =>
    match specs with
    | [] => Reject MalformedDeclaration
    | first::_ =>
      opened <- nested_open_params remaining nparams initial_ind_state (decl_type (spec_decl first)) ;;
      let '(params,_,s) := opened in
      w <- nested_worklist remaining 0 env ps nparams params
        {| nw_specs := specs; nw_mapping := []; nw_next_aux := 1; nw_next_local := ist_next s |} ;;
      let aux_names := map snd (nw_mapping w) in
      Accept {| nested_params := params; nested_context := ist_context s;
        nested_specs := nw_specs w; nested_mapping := nw_mapping w;
        nested_aux_names := aux_names; nested_aux_count := List.length aux_names |}
    end
  end.

(* Closed computational regressions for this syntax transformation, not
   assumptions about admission or proofs of the checker's soundness. *)
Module NestedTransformRegression.

Definition u := NameStr NameAnon "u".
Definition list_name := NameStr NameAnon "NestedList".
Definition tree_name := NameStr NameAnon "NestedTree".
Definition type0 := ESort (LSucc LZero).
Definition pi := EPi NameAnon BDefault.
Definition list_at (e : expr) := EApp (EConst list_name [LZero]) e.
Definition tree := EConst tree_name [].
Definition aux1 := nested_aux_name 1.
Definition aux2 := nested_aux_name 2.

Definition ind (n : name) (ps : list name) (np ni : nat) (all ctors : list name) (ty : expr) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := ty; decl_value := None;
     decl_kind_of := DInductive {| ind_num_params := np; ind_num_indices := ni;
       ind_all := all; ind_ctors := ctors; ind_num_nested := 0;
       ind_is_rec := false; ind_is_reflexive := false; ind_is_unsafe := false |} |}.
Definition ctor (n owner : name) (ps : list name) (np : nat) (ty : expr) :=
  {| decl_hints := HintOpaque; decl_name := n; decl_params := ps; decl_type := ty; decl_value := None;
     decl_kind_of := DConstructor {| ctor_induct := owner; ctor_index := 0;
       ctor_num_params := np; ctor_num_fields := 0; ctor_is_unsafe := false |} |}.
Definition list_nil := NameStr list_name "nil".
Definition list_cons := NameStr list_name "cons".
Definition list_poly := EConst list_name [LParam u].
Definition list_env := [
  ind list_name [u] 1 0 [list_name] [list_nil;list_cons]
    (pi (ESort (LSucc (LParam u))) (ESort (LSucc (LParam u))));
  ctor list_nil list_name [u] 1
    (pi (ESort (LSucc (LParam u))) (EApp list_poly (EBVar 0)));
  ctor list_cons list_name [u] 1
    (pi (ESort (LSucc (LParam u)))
      (pi (EBVar 0) (pi (EApp list_poly (EBVar 1)) (EApp list_poly (EBVar 2)))))].

Definition tree_spec (field : expr) :=
  {| spec_decl := ind tree_name [] 0 0 [tree_name] [NameStr tree_name "mk"] type0;
     spec_ctors := [ctor (NameStr tree_name "mk") tree_name [] 0 (pi field tree)] |}.
Definition satisfies (r : result nested_elimination) (p : nested_elimination -> bool) :=
  match r with Accept x => p x | _ => false end.
Definition result_count (r : result nested_elimination) :=
  match r with Accept x => Some (nested_aux_count x) | _ => None end.

Example zero_fuel_declines : eliminate_nested 0 [] [] 0 [] = Decline OutOfFuel.
Proof. reflexivity. Qed.
Example empty_group_rejected : eliminate_nested 30 [] [] 0 [] = Reject MalformedDeclaration.
Proof. reflexivity. Qed.
Example insufficient_parameter_telescope_rejected :
  eliminate_nested 30 [] [] 1 [tree_spec tree] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example unnested_preserved :
  satisfies (eliminate_nested 50 list_env [] 0 [tree_spec tree])
    (fun r => Nat.eqb (nested_aux_count r) 0 &&
      list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r))) [pi tree tree]) = true.
Proof. vm_compute. reflexivity. Qed.

Example one_nested_list :
  satisfies (eliminate_nested 60 list_env [] 0 [tree_spec (list_at tree)]) (fun r =>
    Nat.eqb (nested_aux_count r) 1 && Nat.eqb (List.length (nested_specs r)) 2 &&
    list_eqb name_eqb (nested_aux_names r) [aux1] &&
    list_eqb expr_eqb (map fst (nested_mapping r)) [list_at tree] &&
    list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
      [pi (EConst aux1 []) tree;
       EConst aux1 [];
       pi tree (pi (EConst aux1 []) (EConst aux1 []))]) = true.
Proof. vm_compute. reflexivity. Qed.

Example nested_list_of_lists_grows_worklist :
  satisfies (eliminate_nested 80 list_env [] 0 [tree_spec (list_at (list_at tree))]) (fun r =>
    Nat.eqb (nested_aux_count r) 2 &&
    list_eqb expr_eqb (map fst (nested_mapping r)) [list_at (list_at tree);list_at tree] &&
    list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
      [pi (EConst aux1 []) tree;
       EConst aux1 []; pi (EConst aux2 []) (pi (EConst aux1 []) (EConst aux1 []));
       EConst aux2 []; pi tree (pi (EConst aux2 []) (EConst aux2 []))]) = true.
Proof. vm_compute. reflexivity. Qed.

Definition param_ctor_type := pi type0
  (pi (list_at (EApp tree (EBVar 0))) (EApp tree (EBVar 1))).
Definition param_spec :=
  {| spec_decl := ind tree_name [] 1 0 [tree_name]
       [NameStr tree_name "mk";NameStr tree_name "other"] (pi type0 type0);
     spec_ctors := [ctor (NameStr tree_name "mk") tree_name [] 1 param_ctor_type;
                   ctor (NameStr tree_name "other") tree_name [] 1 param_ctor_type] |}.

Example common_parameters_rebased_and_memoized :
  satisfies (eliminate_nested 90 list_env [] 1 [param_spec]) (fun r =>
    match nested_params r with
    | [p] =>
      Nat.eqb (nested_aux_count r) 1 &&
      Nat.eqb (List.length (free_context (nested_context r))) 1 &&
      list_eqb expr_eqb (map fst (nested_mapping r)) [list_at (EApp tree (local_expr p))] &&
      list_eqb expr_eqb (map decl_type (firstn 2 (flat_map spec_ctors (nested_specs r))))
        [pi type0 (pi (EApp (EConst aux1 []) (EBVar 0)) (EApp tree (EBVar 1)));
         pi type0 (pi (EApp (EConst aux1 []) (EBVar 0)) (EApp tree (EBVar 1)))]
    | _ => false
    end) = true.
Proof. vm_compute. reflexivity. Qed.

Definition dependent_sort := ESort (LSucc (LParam u)).
Definition dependent_tree := EConst tree_name [LParam u].
Definition dependent_aux := EConst aux1 [LParam u].
Definition dependent_spec :=
  {| spec_decl := ind tree_name [u] 2 0 [tree_name] [NameStr tree_name "mk"]
       (pi dependent_sort (pi (EBVar 0) dependent_sort));
     spec_ctors := [ctor (NameStr tree_name "mk") tree_name [u] 2
       (pi dependent_sort (pi (EBVar 0)
         (pi (EApp list_poly (apply_exprs dependent_tree [EBVar 1;EBVar 0]))
             (apply_exprs dependent_tree [EBVar 2;EBVar 1]))))] |}.
Example dependent_parameters_and_universes_preserved :
  satisfies (eliminate_nested 120 list_env [u] 2 [dependent_spec]) (fun r =>
    match nested_params r with
    | [a;x] =>
      Nat.eqb (nested_aux_count r) 1 &&
      expr_eqb (il_type x) (local_expr a) &&
      list_eqb expr_eqb (map fst (nested_mapping r))
        [EApp list_poly (apply_exprs dependent_tree [local_expr a;local_expr x])] &&
      list_eqb expr_eqb (map (fun s => decl_type (spec_decl s)) (nested_specs r))
        [pi dependent_sort (pi (EBVar 0) dependent_sort);
         pi dependent_sort (pi (EBVar 0) dependent_sort)] &&
      list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
        [pi dependent_sort (pi (EBVar 0)
           (pi (apply_exprs dependent_aux [EBVar 1;EBVar 0])
               (apply_exprs dependent_tree [EBVar 2;EBVar 1])));
         pi dependent_sort (pi (EBVar 0) (apply_exprs dependent_aux [EBVar 1;EBVar 0]));
         pi dependent_sort (pi (EBVar 0)
           (pi (apply_exprs dependent_tree [EBVar 1;EBVar 0])
             (pi (apply_exprs dependent_aux [EBVar 2;EBVar 1])
                 (apply_exprs dependent_aux [EBVar 3;EBVar 2]))))]
    | _ => false
    end) = true.
Proof. vm_compute. reflexivity. Qed.

Example free_field_parameter_rejected :
  eliminate_nested 70 list_env [] 0
    [tree_spec (pi type0 (list_at (EApp tree (EBVar 0))))] = Reject MalformedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Definition work_for_tree := {| nw_specs := [tree_spec tree]; nw_mapping := [];
  nw_next_aux := 1; nw_next_local := 0 |}.
Example closed_inner_binder_is_not_loose :
  match nested_candidate 40 list_env work_for_tree
      (list_at (ELam NameAnon BDefault type0 (EApp tree (EBVar 0)))) with
  | Accept (Some _) => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example loose_nonnested_parameter_does_not_trigger_elimination :
  nested_candidate 40 list_env work_for_tree (list_at (EBVar 0)) = Accept None.
Proof. vm_compute. reflexivity. Qed.

Definition box_name := NameStr NameAnon "NestedBox".
Definition box_ctor := NameStr box_name "mk".
Definition box_env := [
  ind box_name [] 1 1 [box_name] [box_ctor] (pi type0 (pi type0 type0));
  ctor box_ctor box_name [] 1
    (pi type0 (pi type0 (EApp (EApp (EConst box_name []) (EBVar 1)) (EBVar 0))))].
Example indices_are_retained_not_in_mapping_key :
  satisfies (eliminate_nested 80 box_env [] 0
    [tree_spec (EApp (EApp (EConst box_name []) tree) type0)]) (fun r =>
    list_eqb expr_eqb (map fst (nested_mapping r)) [EApp (EConst box_name []) tree] &&
    list_eqb expr_eqb (map (fun s => decl_type (spec_decl s)) (nested_specs r))
      [type0; pi type0 type0] &&
    list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
      [pi (EApp (EConst aux1 []) type0) tree; pi type0 (EApp (EConst aux1 []) (EBVar 0))]) = true.
Proof. vm_compute. reflexivity. Qed.

Definition ma := NameStr NameAnon "MutualA".
Definition mb := NameStr NameAnon "MutualB".
Definition ca := NameStr ma "mk".
Definition cb := NameStr mb "mk".
Definition mutual_env := [
  ind ma [] 1 0 [ma;mb] [ca] (pi type0 type0);
  ind mb [] 1 0 [ma;mb] [cb] (pi type0 type0);
  ctor ca ma [] 1 (pi type0 (pi (EApp (EConst mb []) (EBVar 0))
    (EApp (EConst ma []) (EBVar 1))));
  ctor cb mb [] 1 (pi type0 (EApp (EConst mb []) (EBVar 0)))].
Example entire_existing_mutual_family_expanded :
  satisfies (eliminate_nested 90 mutual_env [] 0 [tree_spec (EApp (EConst ma []) tree)]) (fun r =>
    Nat.eqb (nested_aux_count r) 2 &&
    list_eqb expr_eqb (map fst (nested_mapping r))
      [EApp (EConst ma []) tree;EApp (EConst mb []) tree] &&
    list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
      [pi (EConst aux1 []) tree;pi (EConst aux2 []) (EConst aux1 []);EConst aux2 []] &&
    list_eqb name_eqb (all_ctor_names (skipn 1 (nested_specs r)))
      [NameStr aux1 "mk";NameStr aux2 "mk"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example second_mutual_member_selects_second_auxiliary :
  satisfies (eliminate_nested 90 mutual_env [] 0 [tree_spec (EApp (EConst mb []) tree)]) (fun r =>
    Nat.eqb (nested_aux_count r) 2 &&
    list_eqb expr_eqb (map fst (nested_mapping r))
      [EApp (EConst ma []) tree;EApp (EConst mb []) tree] &&
    list_eqb expr_eqb (map decl_type (flat_map spec_ctors (nested_specs r)))
      [pi (EConst aux2 []) tree;pi (EConst aux2 []) (EConst aux1 []);EConst aux2 []]) = true.
Proof. vm_compute. reflexivity. Qed.

Example constructor_prefix_preserves_numeric_segments :
  nested_replace_prefix 10 ma aux1 (NameNum (NameStr ma "nested") 4%N) =
    Accept (NameNum (NameStr aux1 "nested") 4%N).
Proof. vm_compute. reflexivity. Qed.
Example nonprefix_constructor_declines :
  nested_replace_prefix 10 ma aux1 (NameStr NameAnon "unrelated") = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.

Definition blocker (n : name) := {| decl_hints := HintOpaque; decl_name := n; decl_params := []; decl_type := type0;
  decl_value := None; decl_kind_of := DAssumption |}.
Example existing_auxiliary_name_avoided :
  satisfies (eliminate_nested 70 (blocker aux1 :: list_env) [] 0 [tree_spec (list_at tree)])
    (fun r => list_eqb name_eqb (nested_aux_names r) [aux2]) = true.
Proof. vm_compute. reflexivity. Qed.
Example existing_auxiliary_constructor_name_avoided :
  satisfies (eliminate_nested 70 (blocker (NameStr aux1 "cons") :: list_env) [] 0
    [tree_spec (list_at tree)])
    (fun r => list_eqb name_eqb (nested_aux_names r) [aux2]) = true.
Proof. vm_compute. reflexivity. Qed.
Example existing_auxiliary_recursor_name_avoided :
  satisfies (eliminate_nested 70 (blocker (rec_name aux1) :: list_env) [] 0
    [tree_spec (list_at tree)])
    (fun r => list_eqb name_eqb (nested_aux_names r) [aux2]) = true.
Proof. vm_compute. reflexivity. Qed.
Example fresh_search_exhaustion_declines :
  nested_unique_aux 1 [aux1] list_name [] 1 = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.
Example wrong_universe_arity_rejected :
  eliminate_nested 80 list_env [] 0 [tree_spec (EApp (EConst list_name []) tree)] = Reject UniverseArity.
Proof. vm_compute. reflexivity. Qed.
Example mapping_preserves_let_flag_distinction :
  nested_key_eq 20 (ELet NameAnon type0 tree tree false)
    (ELet NameAnon type0 tree tree true) = Accept false.
Proof. vm_compute. reflexivity. Qed.
Example mapping_ignores_binder_names_and_annotations :
  nested_key_eq 20 (pi type0 (EBVar 0))
    (EPi tree_name BImplicit type0 (EBVar 0)) = Accept true.
Proof. vm_compute. reflexivity. Qed.
Example bounded_growing_worklist_declines :
  eliminate_nested 3 list_env [] 0 [tree_spec (list_at (list_at tree))] = Decline OutOfFuel.
Proof. vm_compute. reflexivity. Qed.

End NestedTransformRegression.
