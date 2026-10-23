(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Mechanical private factorization of dispatch-enabled Checker.v.
   Lean4Lean pin/provenance remains that of Checker.v and its NOTICE.
   Only find_decl is abstracted; the expression and environment data are unchanged. *)
From Stdlib Require Import List Bool Arith PeanoNat NArith String Ascii.
From LeanPort Require Import Syntax Universes EagerPolicy NatProbeDispatch WhnfPolicy Checker.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Module Accessor.
Section WithLookup.
Variable resolve : name -> environment -> option declaration.

Definition core_name (s : string) := NameStr NameAnon s.

Definition core_nat_name := core_name "Nat".

Definition core_zero_name := NameStr core_nat_name "zero".

Definition core_succ_name := NameStr core_nat_name "succ".

Definition core_bitwise_name := NameStr core_nat_name "bitwise".

Definition core_bool_name := core_name "Bool".

Definition core_false_name := NameStr core_bool_name "false".

Definition core_true_name := NameStr core_bool_name "true".

Definition core_char_name := core_name "Char".

Definition core_char_of_nat := NameStr core_char_name "ofNat".

Definition core_string_name := core_name "String".

Definition core_string_of_list := NameStr core_string_name "ofList".

Definition core_list_name := core_name "List".

Definition core_nat := EConst core_nat_name [].

Fixpoint core_spine (e : expr) (args : list expr) : expr * list expr :=
  match e with EApp f a => core_spine f (a :: args) | _ => (e, args) end.

Definition core_apps (e : expr) (args : list expr) : expr := fold_left EApp args e.

Fixpoint core_occurs (index : nat) (e : expr) : bool :=
  match e with
  | EBVar i => Nat.eqb i index
  | EApp a b => core_occurs index a || core_occurs index b
  | ELam _ _ a b | EPi _ _ a b => core_occurs index a || core_occurs (S index) b
  | ELet _ a v b _ => core_occurs index a || core_occurs index v || core_occurs (S index) b
  | EProj _ _ a | EMData a => core_occurs index a
  | _ => false
  end.

Fixpoint core_level_positive (u : level) : bool :=
  match u with
  | LSucc _ => true
  | LMax a b => core_level_positive a || core_level_positive b
  | LIMax _ b => core_level_positive b
  | _ => false
  end.

Definition core_inductive (env : environment) (n : name) : option inductive_data :=
  match resolve n env with
  | Some d => match decl_kind_of d with DInductive i => Some i | _ => None end
  | None => None
  end.

Definition core_constructor (env : environment) (n : name) : option constructor_data :=
  match resolve n env with
  | Some d => match decl_kind_of d with DConstructor i => Some i | _ => None end
  | None => None
  end.

Definition core_structure (env : environment) (n : name) : bool :=
  match core_inductive env n with
  | Some i => negb (ind_is_rec i) && Nat.eqb (ind_num_indices i) 0 &&
              Nat.eqb (List.length (ind_ctors i)) 1
  | None => false
  end.

Definition core_ctor_shape (env : environment) (n parent : name) (index fields : nat)
    (ty : expr) : bool :=
  match resolve n env with
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

Definition core_nat_ready (env : environment) : bool :=
  match resolve core_nat_name env with
  | Some d =>
      match decl_kind_of d with
      | DInductive i =>
          Nat.eqb (List.length (decl_params d)) 0 &&
          expr_eqb (decl_type d) (ESort (LSucc LZero)) &&
          Nat.eqb (ind_num_params i) 0 && Nat.eqb (ind_num_indices i) 0 &&
          negb (ind_is_unsafe i) &&
          list_eqb name_eqb (ind_ctors i) [core_zero_name; core_succ_name] &&
          core_ctor_shape env core_zero_name core_nat_name 0 0 core_nat &&
          core_ctor_shape env core_succ_name core_nat_name 1 1
            (EPi NameAnon BDefault core_nat core_nat)
      | _ => false
      end
  | None => false
  end.

Definition core_bool_ready (env : environment) : bool :=
  match resolve core_bool_name env with
  | Some d =>
      match decl_kind_of d with
      | DInductive i =>
          Nat.eqb (List.length (decl_params d)) 0 &&
          expr_eqb (decl_type d) (ESort (LSucc LZero)) &&
          Nat.eqb (ind_num_params i) 0 && Nat.eqb (ind_num_indices i) 0 &&
          negb (ind_is_unsafe i) &&
          list_eqb name_eqb (ind_ctors i) [core_false_name; core_true_name] &&
          core_ctor_shape env core_false_name core_bool_name 0 0 (EConst core_bool_name []) &&
          core_ctor_shape env core_true_name core_bool_name 1 0 (EConst core_bool_name [])
      | _ => false
      end
  | None => false
  end.

Definition core_string_ready (env : environment) : bool :=
  match resolve core_char_of_nat env, resolve core_string_of_list env with
  | Some c, Some s =>
      match decl_kind_of c, decl_kind_of s with
      | DPrimitive PCharOfNat, DPrimitive PStringOfList => core_nat_ready env
      | _, _ => false
      end
  | _, _ => false
  end.

Fixpoint core_supported (env : environment) (e : expr) : bool :=
  match e with
  | ELit (LitNat _) => core_nat_ready env
  | ELit (LitString _) => core_string_ready env
  | EProj n _ a =>
      match core_inductive env n with Some _ => core_supported env a | None => false end
  | EApp a b | ELam _ _ a b | EPi _ _ a b => core_supported env a && core_supported env b
  | ELet _ a v b _ => core_supported env a && core_supported env v && core_supported env b
  | EMData a => core_supported env a
  | _ => true
  end.

Definition check_level (ps : list name) (u : level) : result unit :=
  if level_has_meta u then Reject MetaVariable
  else require (level_wf ps u) UnknownUniverse.

Fixpoint check_levels (ps : list name) (us : list level) : result unit :=
  match us with
  | [] => Accept tt
  | u :: us => ignored <- check_level ps u ;; check_levels ps us
  end.

Definition get_constant (env : environment) (ps : list name) (n : name)
    (us : list level) : result declaration :=
  match resolve n env with
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

Definition inference_only (rec : methods) : methods :=
  {| infer_method := infer_type_method rec;
     infer_type_method := infer_type_method rec;
     whnf_method := whnf_method rec;
     whnf_core_method := whnf_core_method rec;
     defeq_method := defeq_method rec;
     method_mode := method_mode rec;
     eager_defeq_method := eager_defeq_method rec |}.

Definition sort_of (rec : methods) (g : context) (e : expr) : result level :=
  t <- infer_method rec g e ;;
  t <- whnf_method rec g t ;;
  match t with ESort u => Accept u | _ => Reject ExpectedSort end.

Fixpoint core_apply_type (rec : methods) (g : context) (ty : expr) (args : list expr)
    : result expr :=
  match args with
  | [] => Accept ty
  | a :: args =>
      ty <- whnf_method rec g ty ;;
      match ty with
      | EPi _ _ _ body => core_apply_type rec g (instantiate body a) args
      | _ => Reject ExpectedPi
      end
  end.

Fixpoint core_projection_field (rec : methods) (fuel : nat) (g : context)
    (owner : name) (value : expr) (maybe_prop : bool) (skip index : nat) (ty : expr)
    : result expr :=
  reduced <- whnf_method rec g ty ;;
  match reduced with
  | EPi _ _ domain body =>
      let verify_prop := fun (_ : unit) =>
        u <- sort_of rec g domain ;;
        ok <- level_equiv fuel u LZero ;; require ok TypeMismatch in
      match skip with
      | 0 =>
          ignored <- if maybe_prop then verify_prop tt else Accept tt ;;
          Accept domain
      | S skip =>
          ignored <- if maybe_prop && core_occurs 0 body then verify_prop tt else Accept tt ;;
          core_projection_field rec fuel g owner value maybe_prop skip (S index)
            (instantiate body (EProj owner index value))
      end
  | _ => Reject ExpectedPi
  end.

Definition core_infer_projection (rec : methods) (fuel : nat) (env : environment)
    (g : context) (owner : name) (index : nat) (value : expr) : result expr :=
  st <- infer_method rec g value ;;
  st <- whnf_method rec g st ;;
  let '(head, args) := core_spine st [] in
  match head, core_inductive env owner with
  | EConst n us, Some info =>
      ignored <- require (name_eqb n owner &&
        Nat.eqb (List.length args) (ind_num_params info + ind_num_indices info)) TypeMismatch ;;
      match ind_ctors info with
      | [ctor] =>
          match resolve ctor env with
          | Some d =>
              match decl_kind_of d with
              | DConstructor c =>
                  ignored <- require (index <? ctor_num_fields c) TypeMismatch ;;
                  ty <- core_apply_type rec g (subst_levels (decl_params d) us (decl_type d))
                          (firstn (ind_num_params info) args) ;;
                  u <- sort_of rec g st ;;
                  core_projection_field rec fuel g owner value (negb (core_level_positive u))
                    index 0 ty
              | _ => Reject MalformedDeclaration
              end
          | None => Reject UnknownConstant
          end
      | _ => Reject TypeMismatch
      end
  | _, _ => Reject TypeMismatch
  end.

Definition core_nat_value (e : expr) : option N :=
  match e with
  | ELit (LitNat n) => Some n
  | EConst n [] => if name_eqb n core_zero_name then Some 0%N else None
  | _ => None
  end.

Definition core_nat_constructor (n : N) : expr :=
  match n with
  | N0 => EConst core_zero_name []
  | Npos _ => EApp (EConst core_succ_name []) (ELit (LitNat (N.pred n)))
  end.

Definition core_shiftr (fuel : nat) (a b : N) : result N :=
  if N.ltb (N.log2 a) b then Accept 0%N
  else if N.leb b (N.of_nat fuel) then Accept (N.shiftr a b)
  else Decline OutOfFuel.

Definition core_binary_nat (fuel : nat) (env : environment) (op : primitive_kind)
    (a b : N) : result (option expr) :=
  let numeric := fun n => Accept (Some (ELit (LitNat n))) in
  let bounded := fun (operation : N -> N -> N) =>
    if N.leb b (N.of_nat fuel) then numeric (operation a b) else Decline OutOfFuel in
  let boolean := fun (b : bool) =>
    if core_bool_ready env then
      Accept (Some (EConst (if b then core_true_name else core_false_name) []))
    else Decline UnsupportedExpression in
  match op with
  | PNatAdd => numeric (N.add a b)
  | PNatSub => numeric (N.sub a b)
  | PNatMul => numeric (N.mul a b)
  | PNatPow => bounded N.pow
  | PNatGcd => numeric (N.gcd a b)
  | PNatMod => numeric (N.modulo a b)
  | PNatDiv => numeric (N.div a b)
  | PNatBEq => boolean (N.eqb a b)
  | PNatBLE => boolean (N.leb a b)
  | PNatLAnd => numeric (N.land a b)
  | PNatLOr => numeric (N.lor a b)
  | PNatXor => numeric (N.lxor a b)
  | PNatBitwise => Accept None
  | PNatShiftLeft => bounded N.shiftl
  | PNatShiftRight => value <- core_shiftr fuel a b ;; numeric value
  | _ => Accept None
  end.

Definition core_reduce_nat_reference (rec : methods) (fuel : nat) (env : environment)
    (g : context) (e : expr) : result (option expr) :=
  if negb (core_nat_ready env) then Accept None else
  let '(head, args) := core_spine e [] in
  match head, args with
  | EConst n [], [a] =>
      let op :=
        if name_eqb n core_succ_name then Some true else
        match resolve n env with
        | Some d => match decl_kind_of d with DPrimitive PNatPred => Some false | _ => None end
        | None => None
        end in
      match op with
      | Some successor =>
          a <- whnf_method rec g a ;;
          match core_nat_value a with
          | Some a => Accept (Some (ELit (LitNat (if successor then N.succ a else N.pred a))))
          | None => Accept None
          end
      | None => Accept None
      end
  | EConst n [], [a; b] =>
      match resolve n env with
      | Some d =>
          match decl_kind_of d with
          | DPrimitive PNatBitwise => Accept None
          | DPrimitive op =>
              a <- whnf_method rec g a ;; b <- whnf_method rec g b ;;
              match core_nat_value a, core_nat_value b with
              | Some a, Some b => core_binary_nat fuel env op a b
              | _, _ => Accept None
              end
          | _ => Accept None
          end
      | None => Accept None
      end
  | _, _ => Accept None
  end.

Definition core_reduce_nat (rec : methods) (fuel : nat) (env : environment)
    (g : context) (e : expr) : result (option expr) :=
  let '(head, args) := core_spine e [] in
  match head, args with
  | EConst n [], [a] =>
      let op :=
        if name_eqb n core_succ_name then Some true else
        match resolve n env with
        | Some d => match decl_kind_of d with DPrimitive PNatPred => Some false | _ => None end
        | None => None
        end in
      match op with
      | Some successor =>
          if negb (core_nat_ready env) then Accept None else
          a <- whnf_method rec g a ;;
          match core_nat_value a with
          | Some a => Accept (Some (ELit (LitNat (if successor then N.succ a else N.pred a))))
          | None => Accept None
          end
      | None => Accept None
      end
  | EConst n [], [a; b] =>
      match resolve n env with
      | Some d =>
          match decl_kind_of d with
          | DPrimitive PNatBitwise => Accept None
          | DPrimitive op =>
              if negb (core_nat_ready env) then Accept None else
              a <- whnf_method rec g a ;; b <- whnf_method rec g b ;;
              match core_nat_value a, core_nat_value b with
              | Some a, Some b => core_binary_nat fuel env op a b
              | _, _ => Accept None
              end
          | _ => Accept None
          end
      | None => Accept None
      end
  | _, _ => Accept None
  end.

Definition core_cont (b : ascii) : bool :=
  (128 <=? nat_of_ascii b) && (nat_of_ascii b <? 192).

Definition core_digit (b : ascii) : N := N.modulo (N.of_nat (nat_of_ascii b)) 64.

Definition core_append_digit (n : N) (b : ascii) : N := (n * 64 + core_digit b)%N.

(* Wire strings are UTF-8 bytes; Lean string-literal expansion uses Unicode
   scalar values. Decode in Gallina, rejecting overlongs and surrogates. *)

Fixpoint core_utf8 (s : string) : option (list N) :=
  match s with
  | EmptyString => Some []
  | String a rest =>
      let n := nat_of_ascii a in
      if n <? 128 then option_map (cons (N.of_nat n)) (core_utf8 rest)
      else if n <? 194 then None
      else if n <? 224 then
        match rest with
        | String b tail =>
            if core_cont b then
              option_map (cons (core_append_digit (N.of_nat (n - 192)) b)) (core_utf8 tail)
            else None
        | _ => None
        end
      else if n <? 240 then
        match rest with
        | String b (String c tail) =>
            if core_cont b && core_cont c &&
               (negb (Nat.eqb n 224) || (160 <=? nat_of_ascii b)) &&
               (negb (Nat.eqb n 237) || (nat_of_ascii b <? 160)) then
              option_map (cons (core_append_digit
                (core_append_digit (N.of_nat (n - 224)) b) c)) (core_utf8 tail)
            else None
        | _ => None
        end
      else if n <? 245 then
        match rest with
        | String b (String c (String d tail)) =>
            if core_cont b && core_cont c && core_cont d &&
               (negb (Nat.eqb n 240) || (144 <=? nat_of_ascii b)) &&
               (negb (Nat.eqb n 244) || (nat_of_ascii b <? 144)) then
              option_map (cons (core_append_digit (core_append_digit
                (core_append_digit (N.of_nat (n - 240)) b) c) d)) (core_utf8 tail)
            else None
        | _ => None
        end
      else None
  end.

Fixpoint core_char_list (cs : list N) : expr :=
  let char := EConst core_char_name [] in
  match cs with
  | [] => EApp (EConst (NameStr core_list_name "nil") [LZero]) char
  | c :: cs => core_apps (EConst (NameStr core_list_name "cons") [LZero])
      [char; EApp (EConst core_char_of_nat []) (ELit (LitNat c)); core_char_list cs]
  end.

Definition core_expand_string (s : string) : result expr :=
  match core_utf8 s with
  | Some cs => Accept (EApp (EConst core_string_of_list []) (core_char_list cs))
  | None => Reject MalformedDeclaration
  end.

Fixpoint core_major_induct (index : nat) (ty : expr) : option name :=
  match ty with
  | EPi _ _ domain body =>
      match index with
      | 0 => match fst (core_spine domain []) with EConst n _ => Some n | _ => None end
      | S index => core_major_induct index body
      end
  | _ => None
  end.

Definition core_make_structure (env : environment) (owner : name)
    (us : list level) (args : list expr) (value : expr) : option expr :=
  match core_inductive env owner with
  | Some info =>
      match ind_ctors info with
      | [ctor] =>
          match core_constructor env ctor with
          | Some c => Some (core_apps (EConst ctor us)
              (List.app (firstn (ctor_num_params c) args)
                (map (fun i => EProj owner i value) (seq 0 (ctor_num_fields c)))))
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Definition core_to_constructor (rec : methods) (fuel : nat) (env : environment)
    (g : context) (owner : name) (k_rule : bool) (value : expr) : result expr :=
  reduced <- whnf_method rec g value ;;
  match reduced with
  | ELit (LitNat n) =>
      if name_eqb owner core_nat_name && core_nat_ready env then
        Accept (core_nat_constructor n) else Accept reduced
  | ELit (LitString s) =>
      expanded <- core_expand_string s ;; whnf_method rec g expanded
  | _ =>
      match fst (core_spine reduced []) with
      | EConst n _ =>
          match core_constructor env n with
          | Some _ => Accept reduced
          | None =>
              if negb (k_rule || core_structure env owner) then Accept reduced else
              ty <- infer_method rec g reduced ;;
              ty <- whnf_method rec g ty ;;
              let '(head, args) := core_spine ty [] in
              match head with
              | EConst n us =>
                  if negb (name_eqb n owner) then Accept reduced else
                  match core_make_structure env owner us args reduced with
                  | Some candidate =>
                      if k_rule then
                        sort <- sort_of rec g ty ;;
                        prop <- level_equiv fuel sort LZero ;;
                        if prop then
                          ct <- infer_method rec g candidate ;;
                          ok <- defeq_method rec g ty ct ;;
                          if ok then Accept candidate else Accept reduced
                        else Accept reduced
                      else
                        sort <- sort_of rec g ty ;;
                        if core_level_positive sort then Accept candidate else Accept reduced
                  | None => Accept reduced
                  end
              | _ => Accept reduced
              end
          end
      | _ =>
          if negb (k_rule || core_structure env owner) then Accept reduced else
          ty <- infer_method rec g reduced ;;
          ty <- whnf_method rec g ty ;;
          let '(head, args) := core_spine ty [] in
          match head with
          | EConst n us =>
              if negb (name_eqb n owner) then Accept reduced else
              match core_make_structure env owner us args reduced with
              | Some candidate =>
                  if k_rule then
                    sort <- sort_of rec g ty ;;
                    prop <- level_equiv fuel sort LZero ;;
                    if prop then
                      ct <- infer_method rec g candidate ;;
                      ok <- defeq_method rec g ty ct ;;
                      if ok then Accept candidate else Accept reduced
                    else Accept reduced
                  else
                    sort <- sort_of rec g ty ;;
                    if core_level_positive sort then Accept candidate else Accept reduced
              | None => Accept reduced
              end
          | _ => Accept reduced
          end
      end
  end.

Fixpoint core_find_rule (n : name) (rules : list recursor_rule) : option recursor_rule :=
  match rules with
  | [] => None
  | r :: rules => if name_eqb n (rule_ctor r) then Some r else core_find_rule n rules
  end.

Definition core_reduce_recursor (rec : methods) (fuel : nat) (env : environment)
    (g : context) (e : expr) : result (option expr) :=
  let '(head, args) := core_spine e [] in
  match head with
  | EConst n us =>
      match resolve n env with
      | Some d =>
          match decl_kind_of d with
          | DRecursor info =>
              let first_index := rec_num_params info + rec_num_motives info + rec_num_minors info in
              let major_index := first_index + rec_num_indices info in
              match nth_error args major_index with
              | None => Accept None
              | Some major =>
                  match core_major_induct major_index (decl_type d) with
                  | None => Reject MalformedDeclaration
                  | Some owner =>
                      major <- core_to_constructor rec fuel env g owner (rec_k info) major ;;
                      let '(ctor, fields) := core_spine major [] in
                      match ctor with
                      | EConst cn _ =>
                          match core_find_rule cn (rec_rules info), core_constructor env cn with
                          | Some rule, Some ci =>
                              if negb (name_eqb (ctor_induct ci) owner &&
                                Nat.eqb (List.length fields) (ctor_num_params ci + ctor_num_fields ci) &&
                                Nat.eqb (rule_nfields rule) (ctor_num_fields ci) &&
                                Nat.eqb (List.length us) (List.length (decl_params d)))
                              then Accept None else
                              Accept (Some (core_apps (subst_levels (decl_params d) us (rule_rhs rule))
                                (List.app (firstn first_index args)
                                  (List.app (skipn (ctor_num_params ci) fields)
                                    (skipn (S major_index) args)))))
                          | _, _ => Accept None
                          end
                      | _ => Accept None
                      end
                  end
              end
          | _ => Accept None
          end
      | None => Accept None
      end
  | _ => Accept None
  end.

Definition core_reduce_projection_with (rec : methods)
    (reduce : context -> expr -> result expr) (env : environment) (g : context)
    (owner : name) (index : nat) (value : expr) : result (option expr) :=
  reduced <- reduce g value ;;
  reduced <- match reduced with
             | ELit (LitString s) => expanded <- core_expand_string s ;; whnf_method rec g expanded
             | _ => Accept reduced
             end ;;
  let '(head, args) := core_spine reduced [] in
  match head with
  | EConst n _ =>
      match core_constructor env n with
      | Some ci =>
          if name_eqb (ctor_induct ci) owner && (index <? ctor_num_fields ci) &&
             Nat.eqb (List.length args) (ctor_num_params ci + ctor_num_fields ci)
          then Accept (nth_error args (ctor_num_params ci + index))
          else Accept None
      | None => Accept None
      end
  | _ => Accept None
  end.

Definition core_reduce_projection (rec : methods) :=
  core_reduce_projection_with rec (whnf_method rec).

Definition core_reduce_quotient (rec : methods) (env : environment) (g : context)
    (e : expr) : result (option expr) :=
  let '(head, args) := core_spine e [] in
  match head with
  | EConst n _ =>
      match resolve n env with
      | Some d =>
          let major_pos := match decl_kind_of d with
                           | DQuotient QLift => Some 5
                           | DQuotient QInd => Some 4
                           | _ => None
                           end in
          match major_pos with
          | Some index =>
              match nth_error args index, nth_error args 3 with
              | Some major, Some fn =>
                  major <- whnf_method rec g major ;;
                  let '(ctor, cargs) := core_spine major [] in
                  match ctor, cargs with
                  | EConst cn _, [_; _; representative] =>
                      match resolve cn env with
                      | Some cd =>
                          match decl_kind_of cd with
                          | DQuotient QCtor =>
                              Accept (Some (core_apps (EApp fn representative) (skipn (S index) args)))
                          | _ => Accept None
                          end
                      | None => Accept None
                      end
                  | _, _ => Accept None
                  end
              | _, _ => Accept None
              end
          | None => Accept None
          end
      | None => Accept None
      end
  | _ => Accept None
  end.

Definition core_reduce_head (rec : methods) (fuel : nat) (env : environment)
    (g : context) (e : expr) : result (option expr) :=
  native <- core_reduce_nat rec fuel env g e ;;
  match native with
  | Some _ => Accept native
  | None =>
      quotient <- core_reduce_quotient rec env g e ;;
      match quotient with
      | Some _ => Accept quotient
      | None => core_reduce_recursor rec fuel env g e
      end
  end.

Fixpoint infer_step (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (checking : bool) (g : context) (e : expr) {struct e} : result expr :=
  match e with
  | EBVar i =>
      match nth_error (bound_context g) i with
      | Some b => Accept (lift (S i) 0 (binding_type b))
      | None => Reject LooseBoundVariable
      end
  | EFVar n =>
      match find_free n (free_context g) with
      | Some b => Accept (binding_type b)
      | None => Reject UnknownFreeVariable
      end
  | EMVar _ => Reject MetaVariable
  | ESort u => ignored <- check_level ps u ;; Accept (ESort (LSucc u))
  | EConst n us =>
      d <- get_constant env ps n us ;;
      Accept (instantiate_levels (decl_params d) us (decl_type d))
  | EApp f a =>
      ft <- infer_step rec fuel env ps checking g f ;;
      ft <- whnf_method rec g ft ;;
      match ft with
      | EPi _ _ domain body =>
          ignored <- if checking then
            arg_type <- infer_step rec fuel env ps true g a ;;
            ok <- application_type_defeq rec g a domain arg_type ;; require ok TypeMismatch
            else Accept tt ;;
          Accept (instantiate body a)
      | _ => Reject ExpectedPi
      end
  | ELam n bi domain body =>
      ignored <- if checking then
        dt <- infer_step rec fuel env ps true g domain ;;
        dt <- whnf_method rec g dt ;;
        match dt with ESort _ => Accept tt | _ => Reject ExpectedSort end
        else Accept tt ;;
      bt <- infer_step rec fuel env ps checking (push_binding g domain None) body ;;
      Accept (EPi n bi domain bt)
  | EPi _ _ domain body =>
      dt <- infer_step rec fuel env ps checking g domain ;;
      dt <- whnf_method rec g dt ;;
      u <- match dt with ESort u => Accept u | _ => Reject ExpectedSort end ;;
      let gb := push_binding g domain None in
      bt <- infer_step rec fuel env ps checking gb body ;;
      bt <- whnf_method rec gb bt ;;
      v <- match bt with ESort v => Accept v | _ => Reject ExpectedSort end ;;
      Accept (ESort (LIMax u v))
  | ELet _ ty value body _ =>
      ignored <- if checking then
        sort_type <- infer_step rec fuel env ps true g ty ;;
        sort_type <- whnf_method rec g sort_type ;;
        ignored <- match sort_type with ESort _ => Accept tt | _ => Reject ExpectedSort end ;;
        vt <- infer_step rec fuel env ps true g value ;;
        ok <- defeq_method rec g vt ty ;; require ok TypeMismatch
        else Accept tt ;;
      bt <- infer_step rec fuel env ps checking (push_binding g ty (Some value)) body ;;
      Accept (instantiate bt value)
  | EMData body => infer_step rec fuel env ps checking g body
  | ELit (LitNat _) =>
      if core_nat_ready env then Accept core_nat else Decline UnsupportedExpression
  | ELit (LitString s) =>
      if core_string_ready env then
        ignored <- core_expand_string s ;; Accept (EConst core_string_name [])
      else Decline UnsupportedExpression
  | EProj owner index value =>
      match core_inductive env owner with
      | None => Decline UnsupportedExpression
      | Some _ => core_infer_projection
          (if checking then rec else inference_only rec) fuel env g owner index value
      end
  end.

(* TypeChecker.whnfCore' batches the visible lambda prefix before substitution.
   Lambdas exposed by substitution are handled on the next WHNF iteration. *)

Fixpoint core_beta_collect (head : expr) (args values : list expr) : expr :=
  match args with
  | [] => instantiate_many head values
  | a :: args =>
      match head with
      | ELam _ _ _ body => core_beta_collect body args (a :: values)
      | _ => core_apps (instantiate_many head values) (a :: args)
      end
  end.

Definition core_beta (head : expr) (args : list expr) : expr :=
  core_beta_collect head args [].

Definition core_unfold (env : environment) (ps : list name) (e : expr)
    : result (option expr) :=
  let '(head, args) := core_spine e [] in
  match head with
  | EConst n us =>
      d <- get_constant env ps n us ;;
      match decl_kind_of d with
      | DDefinition | DTheorem | DPrimitive _ =>
          match decl_value d with
          | Some value => Accept (Some (core_apps
              (instantiate_levels (decl_params d) us value) args))
          | None => Reject MalformedDeclaration
          end
      | _ => Accept None
      end
  | _ => Accept None
  end.

Definition whnf_core_step (rec : methods) (fuel : nat) (env : environment)
    (ps : list name) (cheap : bool) (g : context) (e : expr) : result expr :=
  match e with
  | EApp _ _ =>
      let '(head, args) := core_spine e [] in
      fn <- whnf_core_method rec cheap g head ;;
      match fn with
      | ELam _ _ _ _ => whnf_core_method rec cheap g (core_beta fn args)
      | _ =>
          let rebuilt := core_apps fn args in
          quot <- core_reduce_quotient rec env g rebuilt ;;
          step <- match quot with Some value => Accept (Some value)
                  | None => core_reduce_recursor rec fuel env g rebuilt end ;;
          match step with Some value => whnf_core_method rec cheap g value
                        | None => Accept rebuilt end
      end
  | ELet _ _ value body _ => whnf_core_method rec cheap g (instantiate body value)
  | EMData body => whnf_core_method rec cheap g body
  | EBVar i =>
      match nth_error (bound_context g) i with
      | None => Reject LooseBoundVariable
      | Some b =>
          match binding_value b with
          | None => Accept e
          | Some v => whnf_core_method rec cheap g (lift (S i) 0 v)
          end
      end
  | EFVar n =>
      match find_free n (free_context g) with
      | None => Reject UnknownFreeVariable
      | Some b =>
          match binding_value b with
          | None => Accept e
          | Some v => whnf_core_method rec cheap g v
          end
      end
  | EConst n us =>
      ignored <- get_constant env ps n us ;; Accept e
  | ESort u => ignored <- check_level ps u ;; Accept e
  | EMVar _ => Reject MetaVariable
  | EProj owner index value =>
      step <- core_reduce_projection_with rec
        (if cheap then whnf_core_method rec true else whnf_method rec)
        env g owner index value ;;
      match step with Some value => whnf_core_method rec cheap g value | None => Accept e end
  | ELit (LitString s) => ignored <- core_expand_string s ;; Accept e
  | _ => Accept e
  end.

Definition whnf_step (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (g : context) (e : expr) : result expr :=
  reduced <- whnf_core_step rec fuel env ps false g e ;;
  match reduced with
  | EConst n _ =>
      if name_eqb n core_zero_name && core_nat_ready env then Accept (ELit (LitNat 0))
      else unfolded <- core_unfold env ps reduced ;;
        match unfolded with Some value => whnf_method rec g value | None => Accept reduced end
  | _ =>
      native <- core_reduce_nat rec fuel env g reduced ;;
      match native with
      | Some value => Accept value
      | None =>
          unfolded <- core_unfold env ps reduced ;;
          match unfolded with Some value => whnf_method rec g value | None => Accept reduced end
      end
  end.

Definition finish_whnf_unfold (env : environment) (ps : list name) (e : expr)
    : result whnf_round :=
  unfolded <- core_unfold env ps e ;;
  Accept (match unfolded with Some value => WhnfContinue value
          | None => WhnfDone e end).

Definition whnf_round_step (rec : methods) (fuel : nat) (env : environment)
    (ps : list name) (g : context) (e : expr) : result whnf_round :=
  reduced <- whnf_core_step rec fuel env ps false g e ;;
  match reduced with
  | EConst n _ =>
      if name_eqb n core_zero_name && core_nat_ready env
      then Accept (WhnfDone (ELit (LitNat 0%N)))
      else finish_whnf_unfold env ps reduced
  | _ =>
      native <- core_reduce_nat rec fuel env g reduced ;;
      match native with
      | Some value => Accept (WhnfDone value)
      | None => finish_whnf_unfold env ps reduced
      end
  end.

Definition whnf_loop rounds rec fuel env ps g e :=
  run_whnf_rounds rounds (whnf_round_step rec fuel env ps g) e.

Definition eta_compare (rec : methods) (g : context) (domain body other : expr)
    : result bool :=
  ty <- infer_method rec g other ;;
  ty <- whnf_method rec g ty ;;
  match ty with
  | EPi _ _ domain' _ =>
      ok <- defeq_method rec g domain domain' ;;
      if ok then
        defeq_method rec (push_binding g domain None) body
          (EApp (lift 1 0 other) (EBVar 0))
      else Accept false
  | _ => Accept false
  end.

(* A failed bounded alpha comparison is only an inconclusive fast path. The
   node budget is shared by both branches, so a shared input cannot make this
   preliminary traversal exponential. No pointer equality or cache is assumed. *)

Fixpoint core_alpha (budget : nat) (t s : expr) {struct t} : bool * nat :=
  match budget with
  | 0 => (false, 0)
  | S budget =>
    match t, s with
    | EApp f a, EApp h b | ELam _ _ f a, ELam _ _ h b | EPi _ _ f a, EPi _ _ h b =>
        let '(ok, remaining) := core_alpha budget f h in
        if ok then core_alpha remaining a b else (false, remaining)
    | ELet _ a v b _, ELet _ c w d _ =>
        let '(ok, remaining) := core_alpha budget a c in
        if ok then
          let '(ok, remaining) := core_alpha remaining v w in
          if ok then core_alpha remaining b d else (false, remaining)
        else (false, remaining)
    | EProj n i a, EProj m j b =>
        if name_eqb n m && Nat.eqb i j then core_alpha budget a b else (false, budget)
    | EMData a, EMData b => core_alpha budget a b
    | EBVar i, EBVar j => (Nat.eqb i j, budget)
    | EFVar n, EFVar m | EMVar n, EMVar m => (name_eqb n m, budget)
    | EConst n us, EConst m vs => (name_eqb n m && list_eqb level_eqb us vs, budget)
    | ESort u, ESort v => (level_eqb u v, budget)
    | ELit a, ELit b => (literal_eqb a b, budget)
    | _, _ => (false, budget)
    end
  end.

Definition core_alpha_eq (t s : expr) : bool := fst (core_alpha 256 t s).

Fixpoint core_compare_args (rec : methods) (g : context) (xs ys : list expr)
    : result bool :=
  match xs, ys with
  | [], [] => Accept true
  | x :: xs, y :: ys =>
      ok <- defeq_method rec g x y ;;
      if ok then core_compare_args rec g xs ys else Accept false
  | _, _ => Accept false
  end.

Definition core_same_head (fuel : nat) (t s : expr) : result bool :=
  match t, s with
  | EConst n us, EConst m vs =>
      if name_eqb n m then levels_equiv fuel us vs else Accept false
  | EFVar n, EFVar m => Accept (name_eqb n m)
  | EBVar i, EBVar j => Accept (Nat.eqb i j)
  | _, _ => Accept false
  end.

Definition core_congruent_apps (rec : methods) (fuel : nat) (g : context)
    (t s : expr) : result bool :=
  match t, s with
  | EApp _ _, EApp _ _ =>
      let '(tf, ta) := core_spine t [] in
      let '(sf, sa) := core_spine s [] in
      same <- core_same_head fuel tf sf ;;
      if same && Nat.eqb (List.length ta) (List.length sa) then
        core_compare_args rec g (rev ta) (rev sa)
      else Accept false
  | _, _ => Accept false
  end.

Definition core_delta_info (env : environment) (e : expr) : option declaration :=
  match fst (core_spine e []) with
  | EConst n us =>
      match resolve n env with
      | Some d =>
          match decl_kind_of d, decl_value d with
          | DDefinition, Some _ | DTheorem, Some _ | DPrimitive _, Some _ =>
              if Nat.eqb (List.length (decl_params d)) (List.length us)
              then Some d else None
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition core_delta_head (env : environment) (e : expr) : bool :=
  match core_delta_info env e with Some _ => true | None => false end.

(* Pinned lazyDeltaReductionStep priority, not an opacity gate. In the
   single/absent-head cases retain core_unfold's ordinary validation errors. *)
Definition core_delta_sides (env : environment) (t s : expr) : bool * bool :=
  match core_delta_info env t, core_delta_info env s with
  | Some dt, Some ds =>
    if hints_lt (effective_hints dt) (effective_hints ds) then (false,true)
    else if hints_lt (effective_hints ds) (effective_hints dt) then (true,false)
    else (true,true)
  | _, _ => (true,true)
  end.

Definition core_erasing_delta (env : environment) (e : expr) : bool :=
  let '(head, args) := core_spine e [] in
  match head, args with
  | EConst n _, _ :: _ =>
      match resolve n env with
      | Some d =>
          match decl_value d with
          | Some (ELam _ _ _ body) => negb (core_occurs 0 body)
          | _ => false
          end
      | None => false
      end
  | _, _ => false
  end.

(* Upstream tries argument congruence here only for matching delta heads.
   Rigid applications are compared once, after lazy reduction has stalled. *)

Definition core_delta_congruent (rec : methods) (fuel : nat) (env : environment)
    (g : context) (t s : expr) : result bool :=
  (* A syntactically unused binder makes unfolding cheaper than speculation.
     This only selects ordinary delta/beta reduction, never an equality verdict. *)
  match core_delta_info env t, core_delta_info env s with
  | Some dt, Some ds =>
    match effective_hints dt, effective_hints ds with
    | HintRegular ht, HintRegular hs =>
      if N.eqb ht hs && negb (core_erasing_delta env t || core_erasing_delta env s)
      then core_congruent_apps rec fuel g t s else Accept false
    | _, _ => Accept false
    end
  | _, _ => Accept false
  end.

Definition compare_heads (rec : methods) (fuel : nat) (g : context)
    (t s : expr) : result bool :=
  match t, s with
  | EConst n us, EConst m vs =>
      if name_eqb n m then levels_equiv fuel us vs else Accept false
  | EBVar n, EBVar m => Accept (Nat.eqb n m)
  | EFVar n, EFVar m => Accept (name_eqb n m)
  | EProj n i a, EProj m j b =>
      if name_eqb n m && Nat.eqb i j then defeq_method rec g a b else Accept false
  | EApp f a, EApp h b =>
      let '(tf, ta) := core_spine t [] in
      let '(sf, sa) := core_spine s [] in
      if Nat.eqb (List.length ta) (List.length sa) then
        ok <- defeq_method rec g tf sf ;;
        if ok then core_compare_args rec g ta sa else Accept false
      else Accept false
  | ELam _ _ domain body, other => eta_compare rec g domain body other
  | other, ELam _ _ domain body => eta_compare rec g domain body other
  | _, _ => Accept false
  end.

Fixpoint core_compare_fields (rec : methods) (g : context) (owner : name)
    (value : expr) (index : nat) (fields : list expr) : result bool :=
  match fields with
  | [] => Accept true
  | field :: fields =>
      ok <- defeq_method rec g (EProj owner index value) field ;;
      if ok then core_compare_fields rec g owner value (S index) fields else Accept false
  end.

Definition core_structure_eta (rec : methods) (env : environment) (g : context)
    (value constructed : expr) : result bool :=
  let '(head, args) := core_spine constructed [] in
  match head with
  | EConst ctor _ =>
      match core_constructor env ctor with
      | Some c =>
          if core_structure env (ctor_induct c) &&
             Nat.eqb (List.length args) (ctor_num_params c + ctor_num_fields c) then
            vt <- infer_method rec g value ;;
            ct <- infer_method rec g constructed ;;
            ok <- defeq_method rec g vt ct ;;
            if ok then core_compare_fields rec g (ctor_induct c) value 0
              (skipn (ctor_num_params c) args) else Accept false
          else Accept false
      | None => Accept false
      end
  | _ => Accept false
  end.

Definition core_unit_like (rec : methods) (env : environment) (g : context)
    (t s : expr) : result bool :=
  ty <- infer_method rec g t ;;
  ty <- whnf_method rec g ty ;;
  match fst (core_spine ty []) with
  | EConst owner _ =>
      if core_structure env owner then
        match core_inductive env owner with
        | Some i =>
            match ind_ctors i with
            | [ctor] =>
                match core_constructor env ctor with
                | Some c =>
                    if Nat.eqb (ctor_num_fields c) 0 then
                      sty <- infer_method rec g s ;; defeq_method rec g ty sty
                    else Accept false
                | None => Accept false
                end
            | _ => Accept false
            end
        | None => Accept false
        end
      else Accept false
  | _ => Accept false
  end.

(* Same late exact hook as Checker; lookup abstraction does not change dispatch. *)
Definition core_try_string_expansion (rec : methods) (g : context)
    (t s : expr) : result (option bool) :=
  let expand := fun text other =>
    expanded <- core_expand_string text ;;
    ok <- defeq_method rec g expanded other ;; Accept (Some ok) in
  match t, s with
  | ELit (LitString text), EApp (EConst n []) _ =>
      if name_eqb n core_string_of_list then expand text s else Accept None
  | EApp (EConst n []) _, ELit (LitString text) =>
      if name_eqb n core_string_of_list then expand text t else Accept None
  | _, _ => Accept None
  end.

Definition core_compare_fallback (rec : methods) (fuel : nat) (env : environment)
    (g : context) (t s : expr) : result bool :=
  ok <- compare_heads rec fuel g t s ;;
  if ok then Accept true else
  ok <- core_structure_eta rec env g t s ;;
  if ok then Accept true else
  ok <- core_structure_eta rec env g s t ;;
  if ok then Accept true else
  expanded <- core_try_string_expansion rec g t s ;;
  match expanded with
  | Some ok => Accept ok
  | None => core_unit_like rec env g t s
  end.

Definition compare_after_whnf (rec : methods) (fuel : nat) (env : environment) (g : context)
    (t s : expr) : result bool :=
  if core_alpha_eq t s then Accept true else
  match t, s with
  | ESort u, ESort v => level_equiv fuel u v
  | ELit (LitNat n), ELit (LitNat m) => Accept (N.eqb n m)
  | ELit (LitString a), ELit (LitString b) => Accept (String.eqb a b)
  | ELam _ _ a b, ELam _ _ c d | EPi _ _ a b, EPi _ _ c d =>
      ok <- defeq_method rec g a c ;;
      if ok then defeq_method rec (push_binding g a None) b d else Accept false
  | _, _ =>
      (* Lean proof irrelevance requires that the common type is a proposition,
         not merely that the two terms happen to have types of the same sort. *)
      tt <- infer_method rec g t ;;
      sort <- sort_of rec g tt ;;
      is_prop <- level_equiv fuel sort LZero ;;
      if is_prop then
        st <- infer_method rec g s ;; defeq_method rec g tt st
      else core_compare_fallback rec fuel env g t s
  end.

Definition core_quick (rec : methods) (fuel : nat) (g : context)
    (t s : expr) : result (option bool) :=
  if core_alpha_eq t s then Accept (Some true) else
  match t, s with
  | ESort u, ESort v => ok <- level_equiv fuel u v ;; Accept (Some ok)
  | ELit a, ELit b => Accept (Some (literal_eqb a b))
  | ELam _ _ a b, ELam _ _ c d | EPi _ _ a b, EPi _ _ c d =>
      ok <- defeq_method rec g a c ;;
      if ok then ok <- defeq_method rec (push_binding g a None) b d ;; Accept (Some ok)
      else Accept (Some false)
  | EMData a, EMData b => ok <- defeq_method rec g a b ;; Accept (Some ok)
  | _, _ => Accept None
  end.

Definition core_proof_irrel (rec : methods) (fuel : nat) (g : context)
    (t s : expr) : result (option bool) :=
  ty <- infer_method rec g t ;;
  sort <- sort_of rec g ty ;;
  is_prop <- level_equiv fuel sort LZero ;;
  if is_prop then
    sty <- infer_method rec g s ;;
    ok <- defeq_method rec g ty sty ;; Accept (Some ok)
  else Accept None.

Definition core_offset (rec : methods) (env : environment) (g : context)
    (t s : expr) : result (option bool) :=
  if core_nat_ready env then
    let pred_of := fun e => match e with
      | ELit (LitNat n) => if N.eqb n 0 then None else Some (ELit (LitNat (N.pred n)))
      | EApp (EConst n []) a => if name_eqb n core_succ_name then Some a else None
      | _ => None end in
    let zero := fun e => match e with
      | ELit (LitNat n) => N.eqb n 0
      | EConst n [] => name_eqb n core_zero_name
      | _ => false end in
    if zero t && zero s then Accept (Some true) else
      match pred_of t, pred_of s with
      | Some a, Some b => ok <- defeq_method rec g a b ;; Accept (Some ok)
      | _, _ => Accept None
      end
  else Accept None.

(* TypeChecker.tryUnfoldProjApp retries only a projection-headed application.
   Its full whnfCore callback may expose a constructor hidden by cheap mode. *)
Definition core_try_unfold_proj_app (rec : methods) (g : context) (e : expr)
    : result (option expr) :=
  match fst (core_spine e []) with
  | EProj _ _ _ =>
      reduced <- whnf_core_method rec false g e ;;
      Accept (if expr_eqb reduced e then None else Some reduced)
  | _ => Accept None
  end.

Definition core_opposite_projection (rec : methods) (env : environment)
    (g : context) (t s : expr) : result (option (expr * expr)) :=
  match core_delta_info env t, core_delta_info env s with
  | Some _, None =>
      reduced <- core_try_unfold_proj_app rec g s ;;
      Accept (match reduced with Some s' => Some (t, s') | None => None end)
  | None, Some _ =>
      reduced <- core_try_unfold_proj_app rec g t ;;
      Accept (match reduced with Some t' => Some (t', s) | None => None end)
  | _, _ => Accept None
  end.

(* This local loop, like Lean's lazyDelta loop, has its own decreasing fuel.
   Probe Nat before speculative congruence and stop probing after left success,
   as in pinned Lean4Lean TypeChecker.lazyDeltaReduction (lines 777-793).
   Congruence failure is not non-convertibility: definitions can erase arguments.
   Hint priority chooses a head before unfolding or normalizing its value. *)

Fixpoint core_lazy_delta (rounds : nat) (rec : methods) (fuel : nat)
    (env : environment) (ps : list name) (g : context) (t s : expr)
    : result conversion_progress :=
  match rounds with
  | 0 => Decline OutOfFuel
  | S rounds =>
      quick <- core_quick rec fuel g t s ;;
      match quick with
      | Some ok => Accept (ConversionDone ok)
      | None =>
        offset <- core_offset rec env g t s ;;
        match offset with
        | Some ok => Accept (ConversionDone ok)
        | None =>
          let eligible := pair_probe_guard
            (nat_probe_head resolve core_succ_name env (core_spine t []))
            (nat_probe_head resolve core_succ_name env (core_spine s []))
            (fun _ => nat_probe_allowed (method_mode rec) t s) in
          tn <- if eligible then core_reduce_nat rec fuel env g t else Accept None ;;
          match tn with
          | Some tn => ok <- defeq_method rec g tn s ;; Accept (ConversionDone ok)
          | None =>
            sn <- if eligible then core_reduce_nat rec fuel env g s else Accept None ;;
            match sn with
            | Some sn => ok <- defeq_method rec g t sn ;; Accept (ConversionDone ok)
            | None =>
            same <- core_delta_congruent rec fuel env g t s ;;
            if same then Accept (ConversionDone true) else
            projected <- core_opposite_projection rec env g t s ;;
            match projected with
            | Some (tn, sn) => core_lazy_delta rounds rec fuel env ps g tn sn
            | None =>
            let '(unfold_left, unfold_right) := core_delta_sides env t s in
            td <- if unfold_left then core_unfold env ps t else Accept None ;;
            sd <- if unfold_right then core_unfold env ps s else Accept None ;;
            match td, sd with
            | None, None => Accept (ConversionStuck t s)
            | _, _ =>
              tn <- match td with Some e => whnf_core_method rec true g e | None => Accept t end ;;
              sn <- match sd with Some e => whnf_core_method rec true g e | None => Accept s end ;;
              core_lazy_delta rounds rec fuel env ps g tn sn
            end
            end
            end
          end
        end
      end
  end.

Definition core_finish_conversion (rec : methods) (fuel : nat) (env : environment)
    (g : context) (t s : expr) : result bool :=
  (* Cheap projections can hide a constructor. Only re-enter conversion when
     full projection reduction actually produced a field. *)
  let project := fun e => let '(head, args) := core_spine e [] in match head with
    | EProj owner index value =>
        field <- core_reduce_projection rec env g owner index value ;;
        Accept (option_map (fun f => core_apps f args) field)
    | _ => Accept None end in
  tp <- project t ;; sp <- project s ;;
  match tp, sp with
  | Some t, Some s => defeq_method rec g t s
  | Some t, None => defeq_method rec g t s
  | None, Some s => defeq_method rec g t s
  | None, None => compare_after_whnf rec fuel env g t s
  end.

Definition core_true_shortcut (rec : methods) (env : environment)
    (g : context) (t s : expr) : result bool :=
  if core_is_true s && true_probe_allowed (method_mode rec) t && core_bool_ready env
  then tn <- whnf_method rec g t ;; Accept (core_is_true tn)
  else Accept false.

Definition defeq_step (rec : methods) (fuel : nat) (env : environment) (ps : list name)
    (g : context) (t s : expr) : result bool :=
  let rec := inference_only rec in
  quick <- core_quick rec fuel g t s ;;
  match quick with
  | Some ok => Accept ok
  | None =>
    shortcut <- core_true_shortcut rec env g t s ;;
    if shortcut then Accept true else
    irrelevant <- core_proof_irrel rec fuel g t s ;;
    match irrelevant with
    | Some ok => Accept ok
    | None =>
      tn <- whnf_core_method rec true g t ;;
      sn <- whnf_core_method rec true g s ;;
      progress <- core_lazy_delta (S fuel) rec fuel env ps g tn sn ;;
      match progress with
      | ConversionDone ok => Accept ok
      | ConversionStuck tn sn => core_finish_conversion rec fuel env g tn sn
      end
    end
  end.

(* Eager record construction, not the upstream eagerReduce policy. *)

Fixpoint checker_eager_mode (mode : reduction_mode) (fuel : nat)
    (env : environment) (ps : list name) {struct fuel} : methods :=
  match fuel with
  | 0 => {| infer_method := fun _ _ => Decline OutOfFuel;
            infer_type_method := fun _ _ => Decline OutOfFuel;
            whnf_method := fun _ _ => Decline OutOfFuel;
            whnf_core_method := fun _ _ _ => Decline OutOfFuel;
            defeq_method := fun _ _ _ => Decline OutOfFuel;
            method_mode := mode;
            eager_defeq_method := fun _ _ _ => Decline OutOfFuel |}
  | S n =>
      let rec := checker_eager_mode mode n env ps in
      {| infer_method := infer_step rec n env ps true;
         infer_type_method := infer_step rec n env ps false;
         whnf_method := whnf_loop (whnf_round_limit mode) rec n env ps;
         whnf_core_method := whnf_core_step rec n env ps;
         defeq_method := defeq_step rec n env ps;
         method_mode := mode;
         eager_defeq_method := fun g t s =>
           let rec := checker_eager_mode EagerReduction n env ps in
           defeq_step rec n env ps g t s |}
  end.

(* Build the predecessor only when a method is called. Ordinary extraction
   preserves these lambdas; there is no memoization or context-insensitive cache. *)

Fixpoint checker_mode (mode : reduction_mode) (fuel : nat)
    (env : environment) (ps : list name) {struct fuel} : methods :=
  match fuel with
  | 0 => {| infer_method := fun _ _ => Decline OutOfFuel;
            infer_type_method := fun _ _ => Decline OutOfFuel;
            whnf_method := fun _ _ => Decline OutOfFuel;
            whnf_core_method := fun _ _ _ => Decline OutOfFuel;
            defeq_method := fun _ _ _ => Decline OutOfFuel;
            method_mode := mode;
            eager_defeq_method := fun _ _ _ => Decline OutOfFuel |}
  | S n =>
      {| infer_method := fun g e =>
           let rec := checker_mode mode n env ps in infer_step rec n env ps true g e;
         infer_type_method := fun g e =>
           let rec := checker_mode mode n env ps in infer_step rec n env ps false g e;
         whnf_method := fun g e =>
           let rec := checker_mode mode n env ps in
           whnf_loop (whnf_round_limit mode) rec n env ps g e;
         whnf_core_method := fun cheap g e =>
           let rec := checker_mode mode n env ps in whnf_core_step rec n env ps cheap g e;
         defeq_method := fun g t s =>
           let rec := checker_mode mode n env ps in defeq_step rec n env ps g t s;
         method_mode := mode;
         eager_defeq_method := fun g t s =>
           let rec := checker_mode EagerReduction n env ps in defeq_step rec n env ps g t s |}
  end.

Definition checker := checker_mode NormalReduction.
Definition checker_eager := checker_eager_mode NormalReduction.

Definition infer (fuel : nat) (env : environment) (ps : list name)
    (g : context) (e : expr) : result expr := infer_method (checker fuel env ps) g e.

Definition whnf (fuel : nat) (env : environment) (ps : list name)
    (g : context) (e : expr) : result expr :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S _ => if core_supported env e then whnf_method (checker fuel env ps) g e
           else Decline UnsupportedExpression
  end.

Definition defeq (fuel : nat) (env : environment) (ps : list name)
    (g : context) (t s : expr) : result bool :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S _ => if core_supported env t && core_supported env s
           then defeq_method (checker fuel env ps) g t s
           else Decline UnsupportedExpression
  end.

Definition check (fuel : nat) (env : environment) (ps : list name)
    (g : context) (e ty : expr) : result unit :=
  ignored <- sort_of (checker fuel env ps) g ty ;;
  et <- infer fuel env ps g e ;;
  ok <- defeq fuel env ps g et ty ;;
  require ok TypeMismatch.

Definition check_defeq (fuel : nat) (env : environment) (ps : list name)
    (g : context) (t s : expr) : result unit :=
  tt <- infer fuel env ps g t ;;
  st <- infer fuel env ps g s ;;
  same_type <- defeq fuel env ps g tt st ;;
  ignored <- require same_type TypeMismatch ;;
  same_term <- defeq fuel env ps g t s ;;
  require same_term NotDefinitionallyEqual.

End WithLookup.
End Accessor.

(* This is definitional equality, not functional extensionality. *)
Lemma linear_checker_definitional fuel env ps :
  Accessor.checker find_decl fuel env ps = Checker.checker fuel env ps.
Proof. reflexivity. Qed.
Lemma linear_check_definitional fuel env ps g e ty :
  Accessor.check find_decl fuel env ps g e ty = Checker.check fuel env ps g e ty.
Proof. reflexivity. Qed.
Print Assumptions linear_checker_definitional.
