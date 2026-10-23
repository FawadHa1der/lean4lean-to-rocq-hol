(* SPDX-License-Identifier: Apache-2.0
   Checked inductive admission, adapted from Lean4Lean/Inductive/Add.lean.
   Exported metadata is a claim to compare, not trusted checker state. *)
From Stdlib Require Import List String Bool Arith NArith.
From LeanPort Require Import Syntax Universes Checker Declarations InductiveUtils.
Import ListNotations.
Open Scope string_scope.

Record ind_spec := { spec_decl : declaration; spec_ctors : list declaration }.
Record ind_checked := {
  checked_spec : ind_spec;
  checked_indices : list ind_local;
  checked_level : level
}.
Record ind_stats := {
  stats_params : list ind_local;
  stats_types : list ind_checked;
  stats_names : list name;
  stats_levels : list level;
  stats_result : level;
  stats_unsafe : bool;
  stats_state : ind_state
}.
Record ind_motive := {
  motive_type_info : ind_checked;
  motive_local : ind_local;
  motive_major : ind_local
}.
Record ind_recursive_arg := {
  ra_field : ind_local;
  ra_arguments : list ind_local;
  ra_inductive : nat;
  ra_indices : list expr
}.
Record ind_minor := {
  minor_ctor : declaration;
  minor_owner : nat;
  minor_local : ind_local;
  minor_fields : list ind_local;
  minor_recursive : list ind_recursive_arg
}.

Definition same_names := list_eqb name_eqb.
Definition same_levels := list_eqb level_eqb.
Definition ind_names (types : list declaration) := map decl_name types.
Definition all_ctor_names (specs : list ind_spec) :=
  flat_map (fun s => map decl_name (spec_ctors s)) specs.
Definition rec_name n := NameStr n "rec".

Fixpoint gather_ctors (ns : list name) (ctors : list declaration)
    : result (list declaration) :=
  match ns with
  | [] => Accept []
  | n::ns =>
    match find_decl n ctors with
    | None => Reject MalformedDeclaration
    | Some d =>
      match decl_kind_of d with
      | DConstructor _ => ds <- gather_ctors ns ctors ;; Accept (d::ds)
      | _ => Reject MalformedDeclaration
      end
    end
  end.

Fixpoint gather_specs (types ctors : list declaration) : result (list ind_spec) :=
  match types with
  | [] => Accept []
  | d::ds =>
    match decl_kind_of d with
    | DInductive data =>
      cs <- gather_ctors (ind_ctors data) ctors ;;
      rest <- gather_specs ds ctors ;;
      Accept ({| spec_decl := d; spec_ctors := cs |} :: rest)
    | _ => Reject MalformedDeclaration
    end
  end.

Definition check_primitive_inductive (ps : list name) (nparams : nat)
    (specs : list ind_spec) : bool :=
  match ps,nparams,specs with
  | [],0,[s] =>
    let d := spec_decl s in
    if expr_eqb (decl_type d) (ESort (LSucc LZero)) then
      match spec_ctors s with
      | [a;b] =>
        let head := EConst (decl_name d) [] in
        if name_eqb (decl_name d) nat_name then
          name_eqb (decl_name a) (NameStr nat_name "zero") &&
          name_eqb (decl_name b) (NameStr nat_name "succ") &&
          expr_eqb (decl_type a) head &&
          expr_eqb (decl_type b) (EPi NameAnon BDefault head head)
        else if name_eqb (decl_name d) bool_name then
          name_eqb (decl_name a) (NameStr bool_name "false") &&
          name_eqb (decl_name b) (NameStr bool_name "true") &&
          expr_eqb (decl_type a) head && expr_eqb (decl_type b) head
        else false
      | _ => false
      end
    else false
  | _,_,_ => false
  end.

Fixpoint check_inductive_types (specs : list ind_spec) (fuel : nat)
    (env : environment) (ps : list name) (params : list ind_local)
    (result_level : option level) (s : ind_state)
    : result (list ind_checked * ind_state) :=
  match specs with
  | [] => Accept ([],s)
  | spec::specs =>
    let d := spec_decl spec in
    _ <- require (same_names (decl_params d) ps) MalformedDeclaration ;;
    _ <- check_header fuel env (decl_name d) ps (decl_type d) ;;
    ty <- apply_parameters params fuel env ps s (decl_type d) ;;
    opened <- open_telescope fuel fuel env ps s ty ;;
    let '(indices,body,s) := opened in
    match body with
    | ESort u =>
      _ <- match result_level with
        | None => Accept tt
        | Some v => ok <- level_equiv fuel u v ;; require ok MalformedDeclaration
        end ;;
      tail <- check_inductive_types specs fuel env ps params (Some u) s ;;
      let '(rest,s) := tail in
      Accept ({| checked_spec := spec; checked_indices := indices; checked_level := u |}::rest,s)
    | _ => Reject ExpectedSort
    end
  end.

Fixpoint valid_ind_app_at (types : list ind_checked) (stats : ind_stats)
    (head : expr) (args : list expr) (i : nat) : option nat :=
  match types with
  | [] => None
  | t::ts =>
    let d := spec_decl (checked_spec t) in
    if expr_eqb head (EConst (decl_name d) (stats_levels stats)) &&
       Nat.eqb (List.length args)
         (List.length (stats_params stats) + List.length (checked_indices t)) &&
       list_eqb expr_eqb (firstn (List.length (stats_params stats)) args)
         (local_exprs (stats_params stats)) &&
       negb (existsb (has_inductive (stats_names stats))
         (skipn (List.length (stats_params stats)) args))
    then Some i else valid_ind_app_at ts stats head args (S i)
  end.
Definition valid_ind_app (stats : ind_stats) (e : expr) : option nat :=
  let '(h,args) := split_app e in valid_ind_app_at (stats_types stats) stats h args 0.
Definition ind_app_indices (stats : ind_stats) (e : expr) : list expr :=
  skipn (List.length (stats_params stats)) (snd (split_app e)).

Fixpoint check_positive (depth fuel : nat) (env : environment) (ps : list name)
    (stats : ind_stats) (s : ind_state) (e : expr) : result unit :=
  match depth with
  | 0 => Decline OutOfFuel
  | S depth =>
    e <- whnf fuel env ps (ist_context s) e ;;
    if negb (has_inductive (stats_names stats) e) then Accept tt else
    match e with
    | EPi n bi a b =>
      _ <- require (negb (has_inductive (stats_names stats) a)) MalformedDeclaration ;;
      let '(x,s) := ind_fresh s n bi a in
      check_positive depth fuel env ps stats s (instantiate b (local_expr x))
    | _ =>
      match valid_ind_app stats e with
      | Some _ => Accept tt
      (* Nested occurrences have already been eliminated. A remaining
         occurrence under a stuck external type former is not strictly positive. *)
      | None => Reject MalformedDeclaration
      end
    end
  end.

Definition derived_inductive (stats : ind_stats) (t : ind_checked) : declaration :=
  let specs := map checked_spec (stats_types stats) in
  let ctors := flat_map spec_ctors specs in
  let d := spec_decl (checked_spec t) in
  {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := decl_params d; decl_type := decl_type d;
     decl_value := None;
     decl_kind_of := DInductive
       {| ind_num_params := List.length (stats_params stats);
          ind_num_indices := List.length (checked_indices t);
          ind_all := stats_names stats;
          ind_ctors := map decl_name (spec_ctors (checked_spec t));
          ind_num_nested := 0;
          ind_is_rec := existsb (fun c => recursive_constructor (stats_names stats) (decl_type c)) ctors;
          ind_is_reflexive := existsb (fun c => reflexive_constructor (stats_names stats) (decl_type c)) ctors;
          ind_is_unsafe := stats_unsafe stats |} |}.

Definition inductive_data_eqb (a b : inductive_data) :=
  Nat.eqb (ind_num_params a) (ind_num_params b) &&
  Nat.eqb (ind_num_indices a) (ind_num_indices b) && same_names (ind_all a) (ind_all b) &&
  same_names (ind_ctors a) (ind_ctors b) && Nat.eqb (ind_num_nested a) (ind_num_nested b) &&
  Bool.eqb (ind_is_rec a) (ind_is_rec b) && Bool.eqb (ind_is_reflexive a) (ind_is_reflexive b) &&
  Bool.eqb (ind_is_unsafe a) (ind_is_unsafe b).
Definition constructor_data_eqb (a b : constructor_data) :=
  name_eqb (ctor_induct a) (ctor_induct b) && Nat.eqb (ctor_index a) (ctor_index b) &&
  Nat.eqb (ctor_num_params a) (ctor_num_params b) && Nat.eqb (ctor_num_fields a) (ctor_num_fields b) &&
  Bool.eqb (ctor_is_unsafe a) (ctor_is_unsafe b).

Definition verify_ind_metadata (stats : ind_stats) (t : ind_checked) : result declaration :=
  let generated := derived_inductive stats t in
  match decl_kind_of (spec_decl (checked_spec t)),decl_kind_of generated with
  | DInductive supplied,DInductive actual =>
    if negb (Nat.eqb (ind_num_nested supplied) 0) || ind_is_unsafe supplied
    then Decline UnsupportedDeclaration else
    _ <- require (inductive_data_eqb supplied actual) MalformedDeclaration ;;
    Accept generated
  | _,_ => Reject MalformedDeclaration
  end.

Fixpoint map_result {A B : Type} (f : A -> result B) (xs : list A) : result (list B) :=
  match xs with
  | [] => Accept []
  | x::xs => y <- f x ;; ys <- map_result f xs ;; Accept (y::ys)
  end.

Definition check_field (fuel : nat) (env : environment) (ps : list name)
    (stats : ind_stats) (s : ind_state) (field : ind_local) : result unit :=
  u <- ind_sort fuel env ps s (il_type field) ;;
  prop <- level_equiv fuel (stats_result stats) LZero ;;
  _ <- if prop then Accept tt else
    ok <- level_le fuel u (stats_result stats) ;; require ok MalformedDeclaration ;;
  if stats_unsafe stats then Accept tt
  else check_positive fuel fuel env ps stats s (il_type field).

Fixpoint check_ctors (ctors : list declaration) (owner : name) (index fuel : nat)
    (env : environment) (ps : list name) (stats : ind_stats) (s : ind_state)
    : result (list declaration * ind_state) :=
  match ctors with
  | [] => Accept ([],s)
  | d::ctors =>
    _ <- require (same_names (decl_params d) ps) MalformedDeclaration ;;
    _ <- check_header fuel env (decl_name d) ps (decl_type d) ;;
    ty <- apply_parameters (stats_params stats) fuel env ps s (decl_type d) ;;
    opened <- open_telescope fuel fuel env ps s ty ;;
    let '(fields,body,s) := opened in
    _ <- map_result (check_field fuel env ps stats s) fields ;;
    _ <- match valid_ind_app stats body with
      | None => Reject MalformedDeclaration
      | Some i => match nth_error (stats_names stats) i with
        | None => Reject MalformedDeclaration
        | Some n => require (name_eqb n owner) MalformedDeclaration
        end
      end ;;
    let actual := {| ctor_induct := owner; ctor_index := index;
      ctor_num_params := List.length (stats_params stats);
      ctor_num_fields := List.length fields; ctor_is_unsafe := stats_unsafe stats |} in
    _ <- require (Nat.eqb (raw_arity (decl_type d))
          (List.length (stats_params stats) + List.length fields)) MalformedDeclaration ;;
    let generated := {| decl_hints := decl_hints d; decl_name := decl_name d; decl_params := ps; decl_type := decl_type d;
      decl_value := None; decl_kind_of := DConstructor actual |} in
    tail <- check_ctors ctors owner (S index) fuel env ps stats s ;;
    let '(rest,s) := tail in Accept (generated::rest,s)
  end.

Fixpoint check_all_ctors (types : list ind_checked) (fuel : nat)
    (env : environment) (ps : list name) (stats : ind_stats) (s : ind_state)
    : result (list declaration * ind_state) :=
  match types with
  | [] => Accept ([],s)
  | t::types =>
    let spec := checked_spec t in
    first <- check_ctors (spec_ctors spec) (decl_name (spec_decl spec)) 0 fuel env ps stats s ;;
    let '(ctors,s) := first in
    tail <- check_all_ctors types fuel env ps stats s ;;
    let '(rest,s) := tail in Accept (List.app ctors rest,s)
  end.

Definition large_elimination (fuel : nat) (env : environment) (ps : list name)
    (stats : ind_stats) (s : ind_state) : result bool :=
  if level_never_zero (stats_result stats) then Accept true else
  match stats_types stats with
  | [t] =>
    match spec_ctors (checked_spec t) with
    | [] => Accept true
    | [c] =>
      ty <- apply_parameters (stats_params stats) fuel env ps s (decl_type c) ;;
      opened <- open_telescope fuel fuel env ps s ty ;;
      let '(fields,body,s) := opened in
      let args := snd (split_app body) in
      checks <- map_result (fun x =>
        u <- ind_sort fuel env ps s (il_type x) ;;
        prop <- level_equiv fuel u LZero ;;
        Accept (prop || existsb (expr_eqb (local_expr x)) args)) fields ;;
      Accept (forallb (fun x => x) checks)
    | _ => Accept false
    end
  | _ => Accept false
  end.

Definition k_target (fuel : nat) (stats : ind_stats) : result bool :=
  prop <- level_equiv fuel (stats_result stats) LZero ;;
  if prop then match stats_types stats with
  | [t] => match spec_ctors (checked_spec t) with
    | [c] => Accept (raw_arity (decl_type c) <=? List.length (stats_params stats))%nat
    | _ => Accept false
    end
  | _ => Accept false
  end else Accept false.

Fixpoint fresh_elim_name (fuel index : nat) (ps : list name) : result name :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    let n := NameNum (NameStr NameAnon "_rocq_elim") (N.of_nat index) in
    if name_mem n ps then fresh_elim_name fuel (S index) ps else Accept n
  end.

Fixpoint build_motives (types : list ind_checked) (stats : ind_stats)
    (elim : level) (s : ind_state) : list ind_motive * ind_state :=
  match types with
  | [] => ([],s)
  | t::types =>
    let head := EConst (decl_name (spec_decl (checked_spec t))) (stats_levels stats) in
    let major_ty := apply_locals (apply_locals head (stats_params stats)) (checked_indices t) in
    let '(major,s) := ind_fresh s (NameStr NameAnon "t") BDefault major_ty in
    let motive_ty := close_pi (checked_indices t) (close_pi [major] (ESort elim)) in
    let '(motive,s) := ind_fresh s (NameStr NameAnon "motive") BDefault motive_ty in
    let '(rest,s) := build_motives types stats elim s in
    ({| motive_type_info := t; motive_local := motive; motive_major := major |}::rest,s)
  end.

Fixpoint build_recursive_args (fields : list ind_local) (fuel : nat)
    (env : environment) (ps : list name) (stats : ind_stats) (s : ind_state)
    : result (list ind_recursive_arg * ind_state) :=
  match fields with
  | [] => Accept ([],s)
  | x::fields =>
    opened <- open_telescope fuel fuel env ps s (il_type x) ;;
    let '(args,body,s) := opened in
    tail <- build_recursive_args fields fuel env ps stats s ;;
    let '(rest,s) := tail in
    match valid_ind_app stats body with
    | None => Accept (rest,s)
    | Some i => Accept ({| ra_field := x; ra_arguments := args;
         ra_inductive := i; ra_indices := ind_app_indices stats body |}::rest,s)
    end
  end.

Fixpoint build_ihs (args : list ind_recursive_arg) (motives : list ind_motive)
    (s : ind_state) : result (list ind_local * ind_state) :=
  match args with
  | [] => Accept ([],s)
  | a::args =>
    match nth_error motives (ra_inductive a) with
    | None => Reject MalformedDeclaration
    | Some m =>
      let ih_ty := close_pi (ra_arguments a)
        (EApp (apply_exprs (local_expr (motive_local m)) (ra_indices a))
          (apply_locals (local_expr (ra_field a)) (ra_arguments a))) in
      let '(ih,s) := ind_fresh s (NameStr NameAnon "ih") BDefault ih_ty in
      tail <- build_ihs args motives s ;;
      let '(rest,s) := tail in Accept (ih::rest,s)
    end
  end.

Fixpoint build_minors (ctors : list declaration) (owner fuel : nat)
    (env : environment) (ps : list name) (stats : ind_stats) (motives : list ind_motive)
    (s : ind_state) : result (list ind_minor * ind_state) :=
  match ctors with
  | [] => Accept ([],s)
  | c::ctors =>
    ty <- apply_parameters (stats_params stats) fuel env ps s (decl_type c) ;;
    opened <- open_telescope fuel fuel env ps s ty ;;
    let '(fields,body,s) := opened in
    recursive <- build_recursive_args fields fuel env ps stats s ;;
    let '(recursive,s) := recursive in
    ihs <- build_ihs recursive motives s ;;
    let '(ihs,s) := ihs in
    match nth_error motives owner with
    | None => Reject MalformedDeclaration
    | Some m =>
      let ctor_app := apply_locals
        (apply_locals (EConst (decl_name c) (stats_levels stats)) (stats_params stats)) fields in
      let minor_ty := close_pi fields (close_pi ihs
        (EApp (apply_exprs (local_expr (motive_local m)) (ind_app_indices stats body)) ctor_app)) in
      let '(minor,s) := ind_fresh s (decl_name c) BDefault minor_ty in
      tail <- build_minors ctors owner fuel env ps stats motives s ;;
      let '(rest,s) := tail in
      Accept ({| minor_ctor := c; minor_owner := owner; minor_local := minor;
        minor_fields := fields; minor_recursive := recursive |}::rest,s)
    end
  end.

Fixpoint build_all_minors (types : list ind_checked) (owner fuel : nat)
    (env : environment) (ps : list name) (stats : ind_stats) (motives : list ind_motive)
    (s : ind_state) : result (list ind_minor * ind_state) :=
  match types with
  | [] => Accept ([],s)
  | t::types =>
    first <- build_minors (spec_ctors (checked_spec t)) owner fuel env ps stats motives s ;;
    let '(minors,s) := first in
    tail <- build_all_minors types (S owner) fuel env ps stats motives s ;;
    let '(rest,s) := tail in Accept (List.app minors rest,s)
  end.

Definition recursive_value (stats : ind_stats) (rec_levels : list level)
    (motives : list ind_motive) (minors : list ind_minor) (a : ind_recursive_arg)
    : result expr :=
  match nth_error (stats_names stats) (ra_inductive a) with
  | None => Reject MalformedDeclaration
  | Some n =>
    let f := apply_locals (EConst (rec_name n) rec_levels) (stats_params stats) in
    let f := apply_locals f (map motive_local motives) in
    let f := apply_locals f (map minor_local minors) in
    let f := apply_exprs f (ra_indices a) in
    Accept (close_lam (ra_arguments a)
      (EApp f (apply_locals (local_expr (ra_field a)) (ra_arguments a))))
  end.

Definition build_rule (stats : ind_stats) (rec_levels : list level)
    (motives : list ind_motive) (minors : list ind_minor) (m : ind_minor)
    : result recursor_rule :=
  rec_values <- map_result (recursive_value stats rec_levels motives minors) (minor_recursive m) ;;
  let body := apply_exprs (apply_locals (local_expr (minor_local m)) (minor_fields m)) rec_values in
  Accept {| rule_ctor := decl_name (minor_ctor m);
    rule_nfields := List.length (minor_fields m);
    rule_rhs := close_lam (stats_params stats) (close_lam (map motive_local motives)
      (close_lam (map minor_local minors) (close_lam (minor_fields m) body))) |}.

Definition build_recursor (stats : ind_stats) (rec_ps : list name)
    (motives : list ind_motive) (minors : list ind_minor) (k : bool) (index : nat)
    (m : ind_motive) : result declaration :=
  let t := motive_type_info m in
  let major := motive_major m in
  let ty := close_pi (stats_params stats) (close_pi (map motive_local motives)
    (close_pi (map minor_local minors) (close_pi (checked_indices t) (close_pi [major]
      (EApp (apply_locals (local_expr (motive_local m)) (checked_indices t)) (local_expr major)))))) in
  rules <- map_result (build_rule stats (map LParam rec_ps) motives minors)
    (filter (fun x => Nat.eqb (minor_owner x) index) minors) ;;
  Accept {| decl_hints := HintOpaque; decl_name := rec_name (decl_name (spec_decl (checked_spec t)));
    decl_params := rec_ps; decl_type := ty; decl_value := None;
    decl_kind_of := DRecursor {| rec_all := stats_names stats;
      rec_num_params := List.length (stats_params stats);
      rec_num_indices := List.length (checked_indices t);
      rec_num_motives := List.length motives; rec_num_minors := List.length minors;
      rec_rules := rules; rec_k := k; rec_is_unsafe := stats_unsafe stats |} |}.

Fixpoint build_recursors (remaining : list ind_motive) (index : nat)
    (stats : ind_stats) (rec_ps : list name) (motives : list ind_motive)
    (minors : list ind_minor) (k : bool) : result (list declaration) :=
  match remaining with
  | [] => Accept []
  | m::remaining =>
    d <- build_recursor stats rec_ps motives minors k index m ;;
    ds <- build_recursors remaining (S index) stats rec_ps motives minors k ;;
    Accept (d::ds)
  end.

Definition rule_eqb (source_ps target_ps : list name) (a b : recursor_rule) :=
  name_eqb (rule_ctor a) (rule_ctor b) && Nat.eqb (rule_nfields a) (rule_nfields b) &&
  expr_eqb (subst_levels source_ps (map LParam target_ps) (rule_rhs a)) (rule_rhs b).
Definition recursor_data_eqb (source_ps target_ps : list name) (a b : recursor_data) :=
  same_names (rec_all a) (rec_all b) && Nat.eqb (rec_num_params a) (rec_num_params b) &&
  Nat.eqb (rec_num_indices a) (rec_num_indices b) && Nat.eqb (rec_num_motives a) (rec_num_motives b) &&
  Nat.eqb (rec_num_minors a) (rec_num_minors b) && Bool.eqb (rec_k a) (rec_k b) &&
  Bool.eqb (rec_is_unsafe a) (rec_is_unsafe b) &&
  list_eqb (rule_eqb source_ps target_ps) (rec_rules a) (rec_rules b).

Definition verify_rec_metadata (source generated : declaration) : result unit :=
  let sps := decl_params source in
  let gps := decl_params generated in
  _ <- require (names_unique sps && Nat.eqb (List.length sps) (List.length gps)) MalformedDeclaration ;;
  _ <- require (name_eqb (decl_name source) (decl_name generated)) MalformedDeclaration ;;
  _ <- require (expr_eqb (subst_levels sps (map LParam gps) (decl_type source))
                         (decl_type generated)) MalformedDeclaration ;;
  match decl_kind_of source,decl_kind_of generated with
  | DRecursor a,DRecursor b => require (recursor_data_eqb sps gps a b) MalformedDeclaration
  | _,_ => Reject MalformedDeclaration
  end.

Fixpoint verify_recursors (sources generated : list declaration) : result unit :=
  match generated with
  | [] => require (Nat.eqb (List.length sources) 0) MalformedDeclaration
  | d::ds =>
    match find_decl (decl_name d) sources with
    | None => Reject MalformedDeclaration
    | Some source =>
      _ <- verify_rec_metadata source d ;;
      verify_recursors (filter (fun x => negb (name_eqb (decl_name x) (decl_name d))) sources) ds
    end
  end.

(* Derivation checks all logical premises and constructs its own metadata.
   Wire metadata comparison is a separate mandatory admission step. This split
   also permits nested-inductive elimination to use an internal mutual block. *)
Definition derive_inductive (fuel : nat) (env : environment) (ps : list name)
    (np : nat) (specs : list ind_spec) : result (list declaration) :=
  match specs with
  | [] => Reject MalformedDeclaration
  | first_spec::_ =>
      let first := spec_decl first_spec in
      let unsafe := match decl_kind_of first with
        | DInductive i => ind_is_unsafe i | _ => false end in
      let types := map spec_decl specs in
      let ns := ind_names types in
      let derived_names := List.app ns (List.app (all_ctor_names specs) (map rec_name ns)) in
      _ <- require (names_unique derived_names) DuplicateDeclaration ;;
      _ <- require (forallb (fun n => match find_decl n env with None => true | _ => false end)
                    derived_names) DuplicateDeclaration ;;
      _ <- require (names_unique ps) DuplicateUniverse ;;
      _ <- require ((negb unsafe && check_primitive_inductive ps np specs) ||
        negb (existsb (fun n => name_mem n reserved_names) derived_names)) MalformedDeclaration ;;
      params <- open_parameters np fuel env ps initial_ind_state (decl_type first) ;;
      let '(params,_,s) := params in
      checked <- check_inductive_types specs fuel env ps params None s ;;
      let '(checked,s) := checked in
      match checked with
      | [] => Reject MalformedDeclaration
      | head::_ =>
        let stats := {| stats_params := params; stats_types := checked;
          stats_names := ind_names types; stats_levels := map LParam ps;
          stats_result := checked_level head; stats_unsafe := unsafe; stats_state := s |} in
        let inds := map (derived_inductive stats) checked in
        let ind_env := List.app inds env in
        constructors <- check_all_ctors checked fuel ind_env ps stats s ;;
        let '(constructors,s) := constructors in
        let ctor_env := List.app constructors ind_env in
        large <- large_elimination fuel ctor_env ps stats s ;;
        k <- k_target fuel stats ;;
        fresh <- fresh_elim_name (S (List.length ps)) 0 ps ;;
        let elim := if large then LParam fresh else LZero in
        let rec_ps := if large then fresh::ps else ps in
        let '(motives,s) := build_motives checked stats elim s in
        minors <- build_all_minors checked 0 fuel ctor_env rec_ps stats motives s ;;
        let '(minors,_) := minors in
        generated <- build_recursors motives 0 stats rec_ps motives minors k ;;
        Accept (List.app generated (List.app constructors inds))
      end
  end.

Definition verify_member_metadata (source actual : declaration) : result unit :=
  match decl_kind_of source,decl_kind_of actual with
  | DRecursor _,DRecursor _ => verify_rec_metadata source actual
  | sk,ak =>
    _ <- require (name_eqb (decl_name source) (decl_name actual) &&
      same_names (decl_params source) (decl_params actual) &&
      expr_eqb (decl_type source) (decl_type actual)) MalformedDeclaration ;;
    match sk,ak with
    | DInductive a,DInductive b => require (inductive_data_eqb a b) MalformedDeclaration
    | DConstructor a,DConstructor b => require (constructor_data_eqb a b) MalformedDeclaration
    | _,_ => Reject MalformedDeclaration
    end
  end.

Fixpoint verify_members (sources actual : list declaration) : result unit :=
  match sources with
  | [] => require (Nat.eqb (List.length actual) 0) MalformedDeclaration
  | source::sources =>
    match find_decl (decl_name source) actual with
    | None => Reject MalformedDeclaration
    | Some derived =>
      _ <- verify_member_metadata source derived ;;
      verify_members sources
        (filter (fun d => negb (name_eqb (decl_name d) (decl_name source))) actual)
    end
  end.

Definition prepare_inductive (env : environment) (types ctors recs : list declaration)
    : result (list name * nat * list ind_spec) :=
  match types with
  | [] => Reject MalformedDeclaration
  | first::_ =>
    match decl_kind_of first with
    | DInductive info =>
      let sources := List.app types (List.app ctors recs) in
      let ns := ind_names sources in
      _ <- require (names_unique ns) DuplicateDeclaration ;;
      _ <- require (forallb (fun n => match find_decl n env with None => true | _ => false end) ns)
                   DuplicateDeclaration ;;
      _ <- require (forallb (fun d => match decl_kind_of d with
        | DInductive i => Bool.eqb (ind_is_unsafe i) (ind_is_unsafe info)
        | DConstructor c => Bool.eqb (ctor_is_unsafe c) (ind_is_unsafe info)
        | DRecursor r => Bool.eqb (rec_is_unsafe r) (ind_is_unsafe info)
        | _ => false end) sources) MalformedDeclaration ;;
      specs <- gather_specs types ctors ;;
      _ <- require (Nat.eqb (List.length (all_ctor_names specs)) (List.length ctors) &&
        names_unique (all_ctor_names specs)) MalformedDeclaration ;;
      Accept (decl_params first,ind_num_params info,specs)
    | _ => Reject MalformedDeclaration
    end
  end.

Definition admit_inductive (fuel : nat) (env : environment)
    (types ctors recs : list declaration) : result environment :=
  prepared <- prepare_inductive env types ctors recs ;;
  let '(ps,np,specs) := prepared in
  _ <- if existsb (fun d => match decl_kind_of d with
    | DInductive i => negb (Nat.eqb (ind_num_nested i) 0)
    | _ => false end) types then Decline UnsupportedDeclaration else Accept tt ;;
  generated <- derive_inductive fuel env ps np specs ;;
  _ <- verify_members (List.app types (List.app ctors recs)) generated ;;
  Accept (List.app generated env).
