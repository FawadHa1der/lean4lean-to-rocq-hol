(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Changed Gallina adaptation of Lean4Lean/Primitive.lean, by Mario Carneiro
   and Lean4Lean contributors, Apache-2.0, commit
   8223d223ed98661882e95d9d6a7126df7097cd76.
   Coverage, stronger guards, and deliberate declines: docs/PRIMITIVES.md. *)
From Stdlib Require Import List String Bool Arith.
From LeanPort Require Import Syntax Universes Checker InductiveUtils.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Definition primitive_name (op : primitive_kind) : name :=
  match op with
  | PNatAdd => NameStr core_nat_name "add"
  | PNatPred => NameStr core_nat_name "pred"
  | PNatSub => NameStr core_nat_name "sub"
  | PNatMul => NameStr core_nat_name "mul"
  | PNatPow => NameStr core_nat_name "pow"
  | PNatGcd => NameStr core_nat_name "gcd"
  | PNatMod => NameStr core_nat_name "mod"
  | PNatDiv => NameStr core_nat_name "div"
  | PNatBEq => NameStr core_nat_name "beq"
  | PNatBLE => NameStr core_nat_name "ble"
  | PNatBitwise => NameStr core_nat_name "bitwise"
  | PNatLAnd => NameStr core_nat_name "land"
  | PNatLOr => NameStr core_nat_name "lor"
  | PNatXor => NameStr core_nat_name "xor"
  | PNatShiftLeft => NameStr core_nat_name "shiftLeft"
  | PNatShiftRight => NameStr core_nat_name "shiftRight"
  | PCharOfNat => core_char_of_nat
  | PStringOfList => core_string_of_list
  end.

Definition primitive_kinds :=
  [PNatAdd; PNatPred; PNatSub; PNatMul; PNatPow; PNatGcd; PNatMod; PNatDiv;
   PNatBEq; PNatBLE; PNatBitwise; PNatLAnd; PNatLOr; PNatXor; PNatShiftLeft; PNatShiftRight;
   PCharOfNat; PStringOfList].
Definition primitive_lookup (n : name) : option primitive_kind :=
  find (fun op => name_eqb n (primitive_name op)) primitive_kinds.
Definition primitive_bitwise_name := NameStr core_nat_name "bitwise".
Definition primitive_bool := EConst core_bool_name [].
Definition primitive_char := EConst core_char_name [].
Definition primitive_string := EConst core_string_name [].
Definition primitive_list_char := EApp (EConst core_list_name [LZero]) primitive_char.
Definition primitive_arrow (a b : expr) := EPi NameAnon BDefault a b.
Definition primitive_signature (op : primitive_kind) : expr :=
  match op with
  | PNatPred => primitive_arrow core_nat core_nat
  | PNatBEq | PNatBLE =>
      primitive_arrow core_nat (primitive_arrow core_nat primitive_bool)
  | PNatBitwise =>
      primitive_arrow
        (primitive_arrow primitive_bool (primitive_arrow primitive_bool primitive_bool))
        (primitive_arrow core_nat (primitive_arrow core_nat core_nat))
  | PCharOfNat => primitive_arrow core_nat primitive_char
  | PStringOfList => primitive_arrow primitive_list_char primitive_string
  | _ => primitive_arrow core_nat (primitive_arrow core_nat core_nat)
  end.
Definition primitive_zero := EConst core_zero_name [].
Definition primitive_succ (e : expr) := EApp (EConst core_succ_name []) e.
Definition primitive_one := primitive_succ primitive_zero.
Definition primitive_two := primitive_succ primitive_one.
Definition primitive_true := EConst core_true_name [].
Definition primitive_false := EConst core_false_name [].
Definition primitive_call (op : primitive_kind) (args : list expr) :=
  core_apps (EConst (primitive_name op) []) args.

(* Upstream's @& domains carry metadata. The wire syntax retains only an
   EMData wrapper, which is transparent to the kernel; aliases are not erased. *)
Fixpoint primitive_check_signature (fuel : nat) (actual expected : expr) : result unit :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match actual, expected with
    | EMData a, _ => primitive_check_signature fuel a expected
    | EPi _ _ a b, EPi _ _ c d | EApp a b, EApp c d =>
        _ <- primitive_check_signature fuel a c ;; primitive_check_signature fuel b d
    | _, _ => require (expr_eqb actual expected) TypeMismatch
    end
  end.

(* Dependencies must already have passed classification, not merely exist. *)
Definition primitive_authenticated (fuel : nat) (env : environment)
    (op : primitive_kind) : result unit :=
  match find_decl (primitive_name op) env with
  | Some d =>
    match decl_kind_of d, decl_value d with
    | DPrimitive actual, Some _ =>
      _ <- require (primitive_kind_eqb actual op &&
        Nat.eqb (List.length (decl_params d)) 0) MalformedDeclaration ;;
      primitive_check_signature fuel (decl_type d) (primitive_signature op)
    | _, _ => Reject MalformedDeclaration
    end
  | None => Reject MalformedDeclaration
  end.

Definition primitive_dependencies (fuel : nat) (env : environment)
    (op : primitive_kind) : result unit :=
  _ <- require (core_nat_ready env) MalformedDeclaration ;;
  match op with
  | PNatSub => primitive_authenticated fuel env PNatPred
  | PNatMul => primitive_authenticated fuel env PNatAdd
  | PNatPow | PNatShiftLeft => primitive_authenticated fuel env PNatMul
  | PNatShiftRight => primitive_authenticated fuel env PNatDiv
  | PNatBEq | PNatBLE => require (core_bool_ready env) MalformedDeclaration
  | _ => Accept tt
  end.

(* The caller checks typing in the empty context. Also check closedness here
   so probe binders cannot accidentally close a malformed candidate. *)
Fixpoint primitive_closed (fuel depth : nat) (e : expr) : result unit :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match e with
    | EBVar i => require (i <? depth) LooseBoundVariable
    | EFVar _ => Reject UnknownFreeVariable
    | EMVar _ => Reject MetaVariable
    | EApp a b =>
        _ <- primitive_closed fuel depth a ;; primitive_closed fuel depth b
    | ELam _ _ a b | EPi _ _ a b =>
        _ <- primitive_closed fuel depth a ;; primitive_closed fuel (S depth) b
    | ELet _ a v b _ =>
        _ <- primitive_closed fuel depth a ;;
        _ <- primitive_closed fuel depth v ;; primitive_closed fuel (S depth) b
    | EProj _ _ a | EMData a => primitive_closed fuel depth a
    | _ => Accept tt
    end
  end.

Record primitive_equation := {
  primitive_context : context;
  primitive_lhs : expr;
  primitive_rhs : expr
}.
Definition primitive_equation_at (g : context) (a b : expr) : primitive_equation :=
  {| primitive_context := g; primitive_lhs := a; primitive_rhs := b |}.
Definition primitive_x_context := push_binding empty_context core_nat None.
Definition primitive_xy_context := push_binding primitive_x_context core_nat None.

(* The variables are arbitrary, not a finite collection of numeric samples.
   Recursive occurrences always use the candidate body, never its reserved name. *)
Definition primitive_equations (op : primitive_kind) (body : expr)
    : option (list primitive_equation) :=
  let eq0 := primitive_equation_at empty_context in
  let eqx := primitive_equation_at primitive_x_context in
  let eqxy := primitive_equation_at primitive_xy_context in
  let f := fun x y => core_apps body [x; y] in
  let x := EBVar 0 in
  let xx := EBVar 1 in
  let y := EBVar 0 in
  let base := fun z => eqx (f x primitive_zero) z in
  let step := fun z => eqxy (f xx (primitive_succ y)) z in
  match op with
  | PNatAdd => Some [base x; step (primitive_succ (f xx y))]
  | PNatPred => Some
      [eq0 (EApp body primitive_zero) primitive_zero;
       eqx (EApp body (primitive_succ x)) x]
  | PNatSub => Some [base x; step (primitive_call PNatPred [f xx y])]
  | PNatMul => Some
      [base primitive_zero; step (primitive_call PNatAdd [f xx y; xx])]
  | PNatPow => Some
      [base primitive_one; step (primitive_call PNatMul [f xx y; xx])]
  | PNatShiftLeft => Some
      [base x; step (f (primitive_call PNatMul [primitive_two; xx]) y)]
  | PNatShiftRight => Some
      [base x; step (primitive_call PNatDiv [f xx y; primitive_two])]
  | PNatBEq | PNatBLE => Some
      [eq0 (f primitive_zero primitive_zero) primitive_true;
       eqx (f primitive_zero (primitive_succ x))
         (match op with PNatBEq => primitive_false | _ => primitive_true end);
       eqx (f (primitive_succ x) primitive_zero) primitive_false;
       eqxy (f (primitive_succ xx) (primitive_succ y)) (f xx y)]
  | _ => None
  end.

Fixpoint primitive_check_equations (steps fuel : nat) (env : environment)
    (equations : list primitive_equation) : result unit :=
  match equations with
  | [] => Accept tt
  | e :: es =>
    match steps with
    | 0 => Decline OutOfFuel
    | S steps =>
      _ <- check_defeq fuel env [] (primitive_context e) (primitive_lhs e) (primitive_rhs e) ;;
      primitive_check_equations steps fuel env es
    end
  end.

Definition primitive_path (parts : list string) : name := fold_left NameStr parts NameAnon.
Definition primitive_const (parts : list string) (us : list level) : expr :=
  EConst (primitive_path parts) us.

(* A construction-only, level-indexed quotation language. Bound variables are
   generated by the binders; embedding an open term weakens it capture-free. *)
Module PrimitiveQuote.
Definition term := nat -> expr.
Definition embed (e : expr) : term := fun depth => lift depth 0 e.
Definition app (f a : term) : term := fun depth => EApp (f depth) (a depth).
Definition apps (f : term) (args : list term) : term :=
  fun depth => core_apps (f depth) (map (fun a => a depth) args).
Definition lam (a : term) (b : term -> term) : term := fun depth =>
  ELam NameAnon BDefault (a depth) (b (fun d => EBVar (d - S depth)) (S depth)).
Definition pi (a : term) (b : term -> term) : term := fun depth =>
  EPi NameAnon BDefault (a depth) (b (fun d => EBVar (d - S depth)) (S depth)).
Definition arrow (a b : term) := pi a (fun _ => b).
Definition run (e : term) := e 0.
Definition const parts us := embed (primitive_const parts us).
Definition prop := embed (ESort LZero).
Definition type0 := embed (ESort (LSucc LZero)).
Definition nat := embed core_nat.
Definition bool := embed primitive_bool.
Definition tru := embed primitive_true.
Definition fal := embed primitive_false.
Definition zero := embed primitive_zero.
Definition one := embed primitive_one.
Definition two := embed primitive_two.
Definition succ n := app (embed (EConst core_succ_name [])) n.
Definition call op args := apps (embed (EConst (primitive_name op) [])) args.
Definition eq (a x y : term) := apps (const ["Eq"] [LSucc LZero]) [a; x; y].
Definition refl (a x : term) := apps (const ["Eq"; "refl"] [LSucc LZero]) [a; x].
Definition not (p : term) := app (const ["Not"] []) p.
Definition dec (p : term) := app (const ["Decidable"] []) p.
Definition is_true p h := apps (const ["Decidable"; "isTrue"] []) [p; h].
Definition is_false p h := apps (const ["Decidable"; "isFalse"] []) [p; h].
Definition ite ty p d t e := apps (const ["ite"] [LSucc LZero]) [ty; p; d; t; e].
Definition dite ty p d t e := apps (const ["dite"] [LSucc LZero])
  [ty; p; d; lam p t; lam (not p) e].
Definition bool_dec b := apps (const ["Bool"; "decEq"] []) [b; tru].
End PrimitiveQuote.
Module PQ := PrimitiveQuote.

Record primitive_reflection := {
  reflection_type : expr;
  reflection_true : expr;
  reflection_false : expr;
  reflection_dec : expr
}.

Definition primitive_reflection_type (false_eq : bool) : expr :=
  PQ.run (PQ.lam PQ.prop (fun p => PQ.lam PQ.bool (fun b =>
    PQ.pi PQ.prop (fun q => PQ.arrow
      (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p)
        (PQ.arrow (PQ.arrow
          (if false_eq then PQ.eq PQ.bool b PQ.fal else PQ.not (PQ.eq PQ.bool b PQ.tru))
          (PQ.not p)) q)) q)))).

Definition primitive_reflection_make (false_eq : bool) : primitive_reflection :=
  let rt := primitive_reflection_type false_eq in
  let relation p b := PQ.apps (PQ.embed rt) [p; b] in
  {| reflection_type := rt;
     reflection_true := PQ.run (PQ.lam PQ.prop (fun p =>
       PQ.lam (relation p PQ.tru) (fun h => PQ.apps h [p;
         PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.tru PQ.tru) p) (fun hp =>
           PQ.lam (PQ.arrow
             (if false_eq then PQ.eq PQ.bool PQ.tru PQ.fal
              else PQ.not (PQ.eq PQ.bool PQ.tru PQ.tru)) (PQ.not p))
             (fun _ => PQ.app hp (PQ.refl PQ.bool PQ.tru)))])));
     reflection_false := PQ.run (PQ.lam PQ.prop (fun p =>
       PQ.lam (relation p PQ.fal) (fun h => PQ.apps h [PQ.not p;
         PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.fal PQ.tru) p) (fun _ =>
           PQ.lam (PQ.arrow
             (if false_eq then PQ.eq PQ.bool PQ.fal PQ.fal
              else PQ.not (PQ.eq PQ.bool PQ.fal PQ.tru)) (PQ.not p))
             (fun hn => PQ.app hn (if false_eq then PQ.refl PQ.bool PQ.fal else
               PQ.lam (PQ.eq PQ.bool PQ.fal PQ.tru) (fun bad =>
                 PQ.apps (PQ.const ["Bool"; "noConfusion"] [LZero])
                   [PQ.const ["False"] []; PQ.fal; PQ.tru; bad]))))])));
     reflection_dec := PQ.run (PQ.lam PQ.prop (fun p => PQ.lam PQ.bool (fun b =>
       PQ.lam (relation p b) (fun h =>
         let pos hp := PQ.is_true p (PQ.apps h [p;
           PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p) (fun yes =>
             PQ.lam (PQ.arrow
               (if false_eq then PQ.eq PQ.bool b PQ.fal else PQ.not (PQ.eq PQ.bool b PQ.tru))
               (PQ.not p)) (fun _ => PQ.app yes hp))]) in
         let neg hn := PQ.is_false p (PQ.apps h [PQ.not p;
           PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p) (fun _ =>
             PQ.lam (PQ.arrow
               (if false_eq then PQ.eq PQ.bool b PQ.fal else PQ.not (PQ.eq PQ.bool b PQ.tru))
               (PQ.not p)) (fun no => PQ.app no hn))]) in
         if false_eq then
           PQ.app (PQ.apps (PQ.const ["Bool"; "rec"] [LSucc LZero])
             [PQ.lam PQ.bool (fun b' => PQ.arrow (PQ.eq PQ.bool b b') (PQ.dec p));
              PQ.lam (PQ.eq PQ.bool b PQ.fal) neg;
              PQ.lam (PQ.eq PQ.bool b PQ.tru) pos; b]) (PQ.refl PQ.bool b)
         else PQ.dite (PQ.dec p) (PQ.eq PQ.bool b PQ.tru) (PQ.bool_dec b) pos neg)))) |}.

Definition primitive_reflection_ite (r : primitive_reflection) : expr :=
  PQ.run (PQ.lam PQ.prop (fun p => PQ.lam PQ.bool (fun b =>
    PQ.lam (PQ.apps (PQ.embed (reflection_type r)) [p; b]) (fun h =>
      PQ.lam PQ.type0 (fun a => PQ.apps (PQ.const ["ite"] [LSucc LZero])
        [a; p; PQ.apps (PQ.embed (reflection_dec r)) [p; b; h]]))))).
Definition primitive_reflection_dite (r : primitive_reflection) : expr :=
  PQ.run (PQ.lam PQ.prop (fun p => PQ.lam PQ.bool (fun b =>
    PQ.lam (PQ.apps (PQ.embed (reflection_type r)) [p; b]) (fun h =>
      PQ.apps (PQ.const ["dite"] [LSucc LZero])
        [PQ.nat; p; PQ.apps (PQ.embed (reflection_dec r)) [p; b; h]])))).

Definition primitive_eq_closed fuel env a b :=
  check_defeq fuel env [] empty_context (PQ.run a) (PQ.run b).
Definition primitive_check_closed fuel env a ty :=
  check fuel env [] empty_context (PQ.run a) (PQ.run ty).

Definition primitive_check_reflection (fuel : nat) (env : environment)
    (r : primitive_reflection) (with_ite with_dite : bool) : result unit :=
  let relation p b := PQ.apps (PQ.embed (reflection_type r)) [p; b] in
  _ <- primitive_check_closed fuel env (PQ.embed (reflection_type r))
    (PQ.arrow PQ.prop (PQ.arrow PQ.bool PQ.prop)) ;;
  _ <- if with_ite then
    let it := PQ.embed (primitive_reflection_ite r) in
    _ <- primitive_check_closed fuel env it
      (PQ.pi PQ.prop (fun p => PQ.pi PQ.bool (fun b => PQ.arrow (relation p b)
        (PQ.pi PQ.type0 (fun a => PQ.arrow a (PQ.arrow a a)))))) ;;
    _ <- primitive_eq_closed fuel env
      (PQ.lam PQ.prop (fun p => PQ.lam (relation p PQ.tru) (fun h => PQ.apps it [p; PQ.tru; h])))
      (PQ.lam PQ.prop (fun p => PQ.lam (relation p PQ.tru) (fun _ =>
        PQ.lam PQ.type0 (fun a => PQ.lam a (fun x => PQ.lam a (fun _ => x)))))) ;;
    primitive_eq_closed fuel env
      (PQ.lam PQ.prop (fun p => PQ.lam (relation p PQ.fal) (fun h => PQ.apps it [p; PQ.fal; h])))
      (PQ.lam PQ.prop (fun p => PQ.lam (relation p PQ.fal) (fun _ =>
        PQ.lam PQ.type0 (fun a => PQ.lam a (fun _ => PQ.lam a (fun x => x))))))
    else Accept tt ;;
  if with_dite then
    let di := PQ.embed (primitive_reflection_dite r) in
    _ <- primitive_check_closed fuel env (PQ.const ["Not"] []) (PQ.arrow PQ.prop PQ.prop) ;;
    _ <- primitive_check_closed fuel env di
      (PQ.pi PQ.prop (fun p => PQ.pi PQ.bool (fun b => PQ.arrow (relation p b)
        (PQ.arrow (PQ.arrow p PQ.nat) (PQ.arrow (PQ.arrow (PQ.not p) PQ.nat) PQ.nat))))) ;;
    _ <- primitive_check_closed fuel env (PQ.embed (reflection_true r))
      (PQ.pi PQ.prop (fun p => PQ.arrow (relation p PQ.tru) p)) ;;
    _ <- primitive_check_closed fuel env (PQ.embed (reflection_false r))
      (PQ.pi PQ.prop (fun p => PQ.arrow (relation p PQ.fal) (PQ.not p))) ;;
    let lhs b := PQ.lam PQ.prop (fun p => PQ.lam (PQ.arrow p PQ.nat) (fun yes =>
      PQ.lam (PQ.arrow (PQ.not p) PQ.nat) (fun no => PQ.lam (relation p b) (fun h =>
        PQ.apps di [p; b; h; yes; no])))) in
    let rhs b (positive : bool) := PQ.lam PQ.prop (fun p => PQ.lam (PQ.arrow p PQ.nat) (fun yes =>
      PQ.lam (PQ.arrow (PQ.not p) PQ.nat) (fun no => PQ.lam (relation p b) (fun h =>
        PQ.app (if positive then yes else no)
          (PQ.apps (PQ.embed (if positive then reflection_true r else reflection_false r)) [p; h]))))) in
    _ <- primitive_eq_closed fuel env (lhs PQ.tru) (rhs PQ.tru true) ;;
    primitive_eq_closed fuel env (lhs PQ.fal) (rhs PQ.fal false)
  else Accept tt.

Inductive primitive_condition := PCBool | PCNatLE | PCNatEq.
Definition primitive_condition_prop (c : primitive_condition) : expr :=
  match c with
  | PCBool => PQ.run (PQ.lam PQ.bool (fun b => PQ.eq PQ.bool b PQ.tru))
  | PCNatLE => primitive_const ["Nat"; "le"] []
  | PCNatEq => EApp (primitive_const ["Eq"] [LSucc LZero]) core_nat
  end.
Definition primitive_condition_dec (c : primitive_condition) : expr :=
  match c with
  | PCBool => PQ.run (PQ.lam PQ.bool PQ.bool_dec)
  | PCNatLE => primitive_const ["Nat"; "decLe"] []
  | PCNatEq => primitive_const ["Nat"; "decEq"] []
  end.
Definition primitive_condition_ite c a args t e :=
  PQ.ite a (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t e.
Definition primitive_condition_dite c args t e :=
  PQ.dite PQ.nat (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t e.
Definition primitive_condition_decide c args :=
  primitive_condition_ite c PQ.bool args PQ.tru PQ.fal.

Definition primitive_condition_proof (c : primitive_condition) : expr :=
  let is_eq := match c with PCNatEq => true | _ => false end in
  PQ.run (PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
    let p := PQ.apps (PQ.embed (primitive_condition_prop c)) [x; y] in
    let b := PQ.call (if is_eq then PNatBEq else PNatBLE) [x; y] in
    PQ.lam PQ.prop (fun q =>
      PQ.lam (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p)
        (PQ.arrow (PQ.arrow
          (if is_eq then PQ.eq PQ.bool b PQ.fal else PQ.not (PQ.eq PQ.bool b PQ.tru))
          (PQ.not p)) q)) (fun h =>
          PQ.apps h
            [PQ.apps (PQ.const ["Nat"; if is_eq then "eq_of_beq_eq_true" else "le_of_ble_eq_true"] []) [x; y];
             PQ.apps (PQ.const ["Nat"; if is_eq then "ne_of_beq_eq_false" else "not_le_of_not_ble_eq_true"] []) [x; y]]))))).

Definition primitive_check_condition (fuel : nat) (env : environment)
    (c : primitive_condition) (with_ite with_dite : bool) : result unit :=
  _ <- require (core_bool_ready env) MalformedDeclaration ;;
  _ <- infer fuel env [] empty_context (primitive_condition_dec c) ;;
  match c with
  | PCBool =>
    _ <- primitive_check_closed fuel env (PQ.embed (primitive_condition_prop c))
      (PQ.arrow PQ.bool PQ.prop) ;;
    _ <- if with_ite then
      let it := PQ.lam PQ.bool (fun b => PQ.apps (PQ.const ["ite"] [LSucc LZero])
        [PQ.nat; PQ.apps (PQ.embed (primitive_condition_prop c)) [b];
         PQ.apps (PQ.embed (primitive_condition_dec c)) [b]]) in
      _ <- primitive_check_closed fuel env it
        (PQ.arrow PQ.bool (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.nat))) ;;
      _ <- primitive_eq_closed fuel env (PQ.app it PQ.tru)
        (PQ.lam PQ.nat (fun a => PQ.lam PQ.nat (fun _ => a))) ;;
      primitive_eq_closed fuel env (PQ.app it PQ.fal)
        (PQ.lam PQ.nat (fun _ => PQ.lam PQ.nat (fun a => a)))
      else Accept tt ;;
    if with_dite then Decline UnsupportedDeclaration else Accept tt
  | PCNatLE | PCNatEq =>
    let is_eq := match c with PCNatEq => true | _ => false end in
    let op := if is_eq then PNatBEq else PNatBLE in
    _ <- primitive_authenticated fuel env op ;;
    let r := primitive_reflection_make is_eq in
    _ <- primitive_check_reflection fuel env r with_ite with_dite ;;
    let gadget := PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
      PQ.apps
        (PQ.lam PQ.prop (fun p => PQ.lam PQ.bool (fun b =>
          PQ.lam (PQ.apps (PQ.embed (reflection_type r)) [p; b]) (fun h =>
            PQ.apps (PQ.embed (reflection_dec r)) [p; b; h]))))
        [PQ.apps (PQ.embed (primitive_condition_prop c)) [x; y];
         PQ.call op [x; y]; PQ.apps (PQ.embed (primitive_condition_proof c)) [x; y]])) in
    primitive_eq_closed fuel env gadget (PQ.embed (primitive_condition_dec c))
  end.

Definition primitive_go_name (modulo : bool) : name :=
  if modulo then primitive_path ["Nat"; "modCore"; "go"]
  else primitive_path ["Nat"; "div"; "go"].
Definition primitive_le x y := PQ.apps (PQ.embed (primitive_condition_prop PCNatLE)) [x; y].
Definition primitive_go_type : expr := PQ.run
  (PQ.pi PQ.nat (fun y => PQ.arrow (primitive_le PQ.one y)
    (PQ.pi PQ.nat (fun fuel => PQ.pi PQ.nat (fun x =>
      PQ.arrow (primitive_le (PQ.succ x) fuel) PQ.nat))))).

Definition primitive_fuel_top (modulo : bool) : expr :=
  let go := PQ.embed (EConst (primitive_go_name modulo) []) in
  PQ.run (PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
    let n := if modulo then PQ.succ x else x in
    let inner := primitive_condition_dite PCNatLE [PQ.one; y]
      (fun hy => PQ.apps go [y; hy; PQ.succ n; n;
        PQ.app (PQ.const ["Nat"; "lt_succ_self"] []) n])
      (fun _ => if modulo then n else PQ.zero) in
    if modulo then primitive_condition_ite PCNatLE PQ.nat [y; n] inner n else inner))).

Definition primitive_fuel_step (modulo : bool) (rhs : bool) : expr :=
  let go := PQ.embed (EConst (primitive_go_name modulo) []) in
  PQ.run (PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
    PQ.lam (primitive_le PQ.one y) (fun hy => PQ.lam PQ.nat (fun t =>
      PQ.lam (primitive_le (PQ.succ x) (PQ.succ t)) (fun h =>
        if rhs then primitive_condition_dite PCNatLE [y; x]
          (fun hle =>
            let rec := PQ.apps go [y; hy; t; PQ.call PNatSub [x; y];
              PQ.apps (PQ.const ["Nat"; "div_rec_fuel_lemma"] []) [x; y; t; hy; hle; h]] in
            if modulo then rec else PQ.succ rec)
          (fun _ => if modulo then x else PQ.zero)
        else PQ.apps go [y; hy; PQ.succ t; x; h])))))).

Definition primitive_check_fuel_rec (fuel : nat) (env : environment)
    (modulo : bool) (body : expr) : result unit :=
  _ <- require (core_nat_ready env && core_bool_ready env) MalformedDeclaration ;;
  _ <- primitive_authenticated fuel env PNatSub ;;
  _ <- primitive_check_closed fuel env (PQ.embed (primitive_condition_prop PCNatLE))
    (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.prop)) ;;
  _ <- check fuel env [] empty_context (EConst (primitive_go_name modulo) []) primitive_go_type ;;
  _ <- primitive_check_condition fuel env PCNatLE modulo true ;;
  _ <- if modulo then primitive_eq_closed fuel env
    (PQ.lam PQ.nat (fun x => PQ.apps (PQ.embed body) [PQ.zero; x]))
    (PQ.lam PQ.nat (fun _ => PQ.zero)) else Accept tt ;;
  _ <- primitive_eq_closed fuel env
    (PQ.lam PQ.nat (fun x => PQ.lam PQ.nat (fun y =>
      PQ.apps (PQ.embed body) [if modulo then PQ.succ x else x; y])))
    (PQ.embed (primitive_fuel_top modulo)) ;;
  check_defeq fuel env [] empty_context (primitive_fuel_step modulo false)
    (primitive_fuel_step modulo true).

(* whnfCore performs computational reductions but leaves delta steps explicit.
   This is essential when recognizing the fix/go wrapper boundary. *)
Definition primitive_whnf_core fuel env g e :=
  whnf_core_method (checker fuel env []) false g e.

Definition primitive_unfold (env : environment) (e : expr) : result expr :=
  let '(head,args) := core_spine e [] in
  match head with
  | EConst n us =>
    d <- get_constant env [] n us ;;
    match decl_kind_of d, decl_value d with
    | DDefinition, Some v | DPrimitive _, Some v =>
        Accept (core_apps (subst_levels (decl_params d) us v) args)
    | _, _ => Decline UnsupportedDeclaration
    end
  | _ => Decline UnsupportedDeclaration
  end.

Fixpoint primitive_lambda_telescope (depth fuel : nat) (env : environment)
    (s : ind_state) (e : expr) : result (list ind_local * expr * ind_state) :=
  match depth with
  | 0 => Decline OutOfFuel
  | S depth =>
    match e with
    | EMData e => primitive_lambda_telescope depth fuel env s e
    | ELam n bi ty b =>
      _ <- sort_of (checker fuel env []) (ist_context s) ty ;;
      let '(x,s) := ind_fresh s n bi ty in
      rest <- primitive_lambda_telescope depth fuel env s (instantiate b (local_expr x)) ;;
      let '(xs,b,s) := rest in Accept (x::xs,b,s)
    | _ => Accept ([],e,s)
    end
  end.

Fixpoint primitive_no_free (fuel : nat) (n : name) (e : expr) : result unit :=
  match fuel with
  | 0 => Decline OutOfFuel
  | S fuel =>
    match e with
    | EFVar m => require (negb (name_eqb n m)) MalformedDeclaration
    | EApp a b | ELam _ _ a b | EPi _ _ a b =>
      _ <- primitive_no_free fuel n a ;; primitive_no_free fuel n b
    | ELet _ a v b _ => _ <- primitive_no_free fuel n a ;;
      _ <- primitive_no_free fuel n v ;; primitive_no_free fuel n b
    | EProj _ _ a | EMData a => primitive_no_free fuel n a
    | _ => Accept tt
    end
  end.

Definition primitive_proof (fuel : nat) (env : environment) (g : context) (e : expr) : result unit :=
  ty <- infer fuel env [] g e ;;
  u <- sort_of (checker fuel env []) g ty ;;
  is_prop <- level_equiv fuel u LZero ;; require is_prop TypeMismatch.

Record primitive_probe := {
  probe_pack : expr;
  probe_dom : expr;
  probe_functional : expr
}.

Definition primitive_check_go (fuel : nat) (env : environment)
    (s : ind_state) (go : expr) : result unit :=
  value <- primitive_unfold env go ;;
  opened <- primitive_lambda_telescope fuel fuel env s value ;;
  let '(xs,b,st) := opened in
  match xs,b with
  | [_;_;_;f;t], EApp nat_rec t' =>
    _ <- require (expr_eqb t' (local_expr t)) NotDefinitionallyEqual ;;
    _ <- primitive_no_free fuel (il_id t) nat_rec ;;
    _ <- infer fuel env [] (ist_context st) (primitive_succ (local_expr t)) ;;
    let next := EApp nat_rec (primitive_succ (local_expr t)) in
    _ <- infer fuel env [] (ist_context st) next ;;
    next <- primitive_whnf_core fuel env (ist_context st) next ;;
    opened <- primitive_lambda_telescope fuel fuel env st next ;;
    let '(ys,b,st) := opened in
    match ys,b with
    | [x;_], EApp fx ih =>
      _ <- require (expr_eqb fx (EApp (local_expr f) (local_expr x))) NotDefinitionallyEqual ;;
      opened <- primitive_lambda_telescope fuel fuel env st ih ;;
      let '(zs,b,st) := opened in
      match zs,b with
      | [y;_], EApp recursive_call pf =>
        _ <- primitive_proof fuel env (ist_context st) pf ;;
        require (expr_eqb recursive_call (core_apps nat_rec [local_expr t; local_expr y]))
          NotDefinitionallyEqual
      | _,_ => Decline UnsupportedDeclaration
      end
    | _,_ => Decline UnsupportedDeclaration
    end
  | _,_ => Decline UnsupportedDeclaration
  end.

Definition primitive_unfold_nat_well_founded (fuel : nat) (env : environment)
    (s : ind_state) (e measure : expr) : result primitive_probe :=
  opened <- primitive_lambda_telescope fuel fuel env s measure ;;
  let '(locals,measure_body,st) := opened in
  let applied := apply_locals e locals in
  _ <- infer fuel env [] (ist_context st) applied ;;
  top <- primitive_whnf_core fuel env (ist_context st) applied ;;
  top <- primitive_unfold env top ;;
  top <- primitive_whnf_core fuel env (ist_context st) top ;;
  let '(fix_head,args) := core_spine top [] in
  match fix_head,args with
  | EConst fix_name [u;v], [alpha;motive;meas;functional;packed] =>
    _ <- require (name_eqb fix_name (primitive_path ["WellFounded";"Nat";"fix"]))
      MalformedDeclaration ;;
    ty <- infer fuel env [] (ist_context st) packed ;;
    let '(a,sa) := ind_fresh st NameAnon BDefault ty in
    let av := local_expr a in
    _ <- check fuel env [] (ist_context sa) (EApp meas av) core_nat ;;
    _ <- check_defeq fuel env [] (ist_context sa) (EApp meas packed) measure_body ;;
    unfolded <- primitive_unfold env (core_apps fix_head [alpha;motive;meas;functional;av]) ;;
    unfolded <- primitive_whnf_core fuel env (ist_context sa) unfolded ;;
    let '(go,args) := core_spine unfolded [] in
    match args with
    | [alpha';motive';meas';functional';fuel_expr;av';pf] =>
      _ <- require (list_eqb expr_eqb [alpha;motive;meas;functional;av]
        [alpha';motive';meas';functional';av']) NotDefinitionallyEqual ;;
      _ <- primitive_proof fuel env (ist_context sa) pf ;;
      match fuel_expr with
      | EApp eager n =>
        _ <- check_defeq fuel env [] (ist_context sa) n (primitive_succ (EApp meas av)) ;;
        _ <- primitive_authenticated fuel env PNatBEq ;;
        let '(x,sx) := ind_fresh sa NameAnon BDefault core_nat in
        let xv := PQ.embed (local_expr x) in
        _ <- check_defeq fuel env [] (ist_context sx) (EApp eager (local_expr x))
          (PQ.run (primitive_condition_ite PCBool PQ.nat [PQ.call PNatBEq [xv;xv]] xv xv)) ;;
        _ <- primitive_check_go fuel env s go ;;
        (* Re-infer F in the outer scope, without the unpacked recursion
           arguments. This enforces upstream's F-closedness obligation. *)
        fty <- infer fuel env [] (ist_context s) functional ;;
        fty <- whnf fuel env [] (ist_context s) fty ;;
        match fty with
        | EPi _ _ domain cod =>
          _ <- check_defeq fuel env [] (ist_context st) ty domain ;;
          let '(z,sz) := ind_fresh s NameAnon BDefault domain in
          cod <- whnf fuel env [] (ist_context sz) (instantiate cod (local_expr z)) ;;
          match cod with
          | EPi _ _ ih_domain _ =>
            let dom := close_lam [z] ih_domain in
            let pack := close_lam locals packed in
            _ <- infer fuel env [] (ist_context s) pack ;;
            _ <- infer fuel env [] (ist_context s) dom ;;
            Accept {| probe_pack := pack; probe_dom := dom; probe_functional := functional |}
          | _ => Reject ExpectedPi
          end
        | _ => Reject ExpectedPi
        end
      | _ => Decline UnsupportedDeclaration
      end
    | _ => Decline UnsupportedDeclaration
    end
  | _,_ => Decline UnsupportedDeclaration
  end.

Definition primitive_run_probe (fuel : nat) (env : environment) (s : ind_state)
    (p : primitive_probe) (args : list expr) (rhs : expr -> expr) : result unit :=
  let a := core_apps (probe_pack p) args in
  let '(ih,si) := ind_fresh s NameAnon BDefault (EApp (probe_dom p) a) in
  check_defeq fuel env [] (ist_context si)
    (core_apps (probe_functional p) [a;local_expr ih]) (rhs (local_expr ih)).

Definition primitive_first_measure := PQ.run (PQ.lam PQ.nat (fun m => PQ.lam PQ.nat (fun _ => m))).

Definition primitive_check_gcd (fuel : nat) (env : environment) (body : expr) : result unit :=
  _ <- require (core_nat_ready env && core_bool_ready env) MalformedDeclaration ;;
  _ <- primitive_authenticated fuel env PNatMod ;;
  _ <- primitive_check_condition fuel env PCBool true false ;;
  p <- primitive_unfold_nat_well_founded fuel env initial_ind_state body primitive_first_measure ;;
  let '(n,sn) := ind_fresh initial_ind_state NameAnon BDefault core_nat in
  _ <- primitive_run_probe fuel env sn p [primitive_zero; local_expr n] (fun _ => local_expr n) ;;
  let '(m,sm) := ind_fresh sn NameAnon BDefault core_nat in
  primitive_run_probe fuel env sm p [primitive_succ (local_expr m); local_expr n] (fun ih =>
    let mm := PQ.embed (local_expr m) in
    let nn := PQ.embed (local_expr n) in
    PQ.run (PQ.apps (PQ.embed ih)
      [PQ.apps (PQ.embed (probe_pack p)) [PQ.call PNatMod [nn;PQ.succ mm]; PQ.succ mm];
       PQ.apps (PQ.const ["Nat"; "mod_lt"] [])
         [nn; PQ.succ mm; PQ.app (PQ.const ["Nat";"zero_lt_succ"] []) mm]])).

Definition primitive_bool_operator_type :=
  primitive_arrow primitive_bool (primitive_arrow primitive_bool primitive_bool).

Definition primitive_check_bitwise (fuel : nat) (env : environment) (body : expr) : result unit :=
  _ <- require (core_nat_ready env && core_bool_ready env) MalformedDeclaration ;;
  _ <- primitive_authenticated fuel env PNatAdd ;;
  _ <- primitive_authenticated fuel env PNatDiv ;;
  _ <- primitive_authenticated fuel env PNatMod ;;
  _ <- primitive_check_condition fuel env PCNatEq true true ;;
  _ <- primitive_check_condition fuel env PCBool true false ;;
  let '(f,sf) := ind_fresh initial_ind_state NameAnon BDefault primitive_bool_operator_type in
  p <- primitive_unfold_nat_well_founded fuel env sf (EApp body (local_expr f)) primitive_first_measure ;;
  let '(n,sn) := ind_fresh sf NameAnon BDefault core_nat in
  let '(m,sm) := ind_fresh sn NameAnon BDefault core_nat in
  primitive_run_probe fuel env sm p [local_expr n;local_expr m] (fun ih =>
    let f := PQ.embed (local_expr f) in
    let n := PQ.embed (local_expr n) in
    let m := PQ.embed (local_expr m) in
    let bool_ite b := primitive_condition_ite PCBool PQ.nat [b] in
    PQ.run (primitive_condition_dite PCNatEq [n;PQ.zero]
      (fun _ => bool_ite (PQ.apps f [PQ.fal;PQ.tru]) m PQ.zero)
      (fun hn => primitive_condition_ite PCNatEq PQ.nat [m;PQ.zero]
        (bool_ite (PQ.apps f [PQ.tru;PQ.fal]) n PQ.zero)
        (let n' := PQ.call PNatDiv [n;PQ.two] in
         let m' := PQ.call PNatDiv [m;PQ.two] in
         let b1 := primitive_condition_decide PCNatEq [PQ.call PNatMod [n;PQ.two];PQ.one] in
         let b2 := primitive_condition_decide PCNatEq [PQ.call PNatMod [m;PQ.two];PQ.one] in
         let r := PQ.apps (PQ.embed ih)
           [PQ.apps (PQ.embed (probe_pack p)) [n';m'];
            PQ.apps (PQ.const ["Nat";"bitwise_rec_lemma"] []) [n;hn]] in
         let rr := PQ.call PNatAdd [r;r] in
         bool_ite (PQ.apps f [b1;b2]) (PQ.call PNatAdd [rr;PQ.one]) rr)))).

Definition primitive_check_boolean_operator (fuel : nat) (env : environment)
    (op : primitive_kind) (operator : expr) : result unit :=
  _ <- check fuel env [] empty_context operator primitive_bool_operator_type ;;
  let f := PQ.embed operator in
  let fx b := PQ.lam PQ.bool (fun x => PQ.apps f [b;x]) in
  match op with
  | PNatLAnd =>
    _ <- primitive_eq_closed fuel env (fx PQ.fal) (PQ.lam PQ.bool (fun _ => PQ.fal)) ;;
    primitive_eq_closed fuel env (fx PQ.tru) (PQ.lam PQ.bool (fun x => x))
  | PNatLOr =>
    _ <- primitive_eq_closed fuel env (fx PQ.fal) (PQ.lam PQ.bool (fun x => x)) ;;
    primitive_eq_closed fuel env (fx PQ.tru) (PQ.lam PQ.bool (fun _ => PQ.tru))
  | PNatXor =>
    _ <- primitive_eq_closed fuel env (PQ.apps f [PQ.fal;PQ.fal]) PQ.fal ;;
    _ <- primitive_eq_closed fuel env (PQ.apps f [PQ.tru;PQ.fal]) PQ.tru ;;
    _ <- primitive_eq_closed fuel env (PQ.apps f [PQ.fal;PQ.tru]) PQ.tru ;;
    primitive_eq_closed fuel env (PQ.apps f [PQ.tru;PQ.tru]) PQ.fal
  | _ => Decline UnsupportedDeclaration
  end.

(* The higher-order operation has its own equation certificate. An ordinary
   definition or a binary-operation certificate cannot authorize an instance. *)
Definition primitive_check_bitwise_instance (fuel : nat) (env : environment)
    (op : primitive_kind) (body : expr) : result unit :=
  _ <- primitive_authenticated fuel env PNatBitwise ;;
  match body with
  | EApp (EConst n []) operator =>
      _ <- require (name_eqb n primitive_bitwise_name) MalformedDeclaration ;;
      primitive_check_boolean_operator fuel env op operator
  | _ => Decline UnsupportedDeclaration
  end.

Definition primitive_is_text (op : primitive_kind) : bool :=
  match op with PCharOfNat | PStringOfList => true | _ => false end.

Definition primitive_ensure_type (fuel : nat) (env : environment) (e : expr) : result unit :=
  _ <- sort_of (checker fuel env []) empty_context e ;; Accept tt.

(* Text literals denote these applications. Unlike Nat arithmetic, no host
   computation of these functions is authorized by their metadata. *)
Definition primitive_check_text_interface (fuel : nat) (env : environment)
    (op : primitive_kind) : result unit :=
  match op with
  | PCharOfNat =>
      _ <- require (core_nat_ready env) MalformedDeclaration ;;
      primitive_ensure_type fuel env primitive_char
  | PStringOfList =>
      _ <- primitive_ensure_type fuel env primitive_list_char ;;
      _ <- primitive_ensure_type fuel env primitive_char ;;
      _ <- check fuel env [] empty_context
        (EApp (EConst (NameStr core_list_name "nil") [LZero]) primitive_char)
        primitive_list_char ;;
      check fuel env [] empty_context
        (EApp (EConst (NameStr core_list_name "cons") [LZero]) primitive_char)
        (primitive_arrow primitive_char (primitive_arrow primitive_list_char primitive_list_char))
  | _ => Accept tt
  end.

Definition primitive_check_nat_equations (fuel : nat) (env : environment)
    (op : primitive_kind) (body : expr) : result unit :=
  match primitive_equations op body with
  | Some equations =>
      _ <- primitive_dependencies fuel env op ;;
      primitive_check_equations fuel fuel env equations
  | None =>
      match op with
      | PNatMod => primitive_check_fuel_rec fuel env true body
      | PNatDiv => primitive_check_fuel_rec fuel env false body
      | PNatGcd => primitive_check_gcd fuel env body
      | PNatBitwise => primitive_check_bitwise fuel env body
      | PNatLAnd | PNatLOr | PNatXor => primitive_check_bitwise_instance fuel env op body
      | _ => Decline UnsupportedDeclaration
      end
  end.

Definition classify_primitive (fuel : nat) (env : environment) (n : name)
    (params : list name) (ty body : expr) : result (option primitive_kind) :=
  match primitive_lookup n with
  | None =>
      if name_mem n [core_nat_name; core_zero_name; core_succ_name;
                     core_bool_name; core_false_name; core_true_name]
      then Reject MalformedDeclaration else Accept None
  | Some op =>
    _ <- match find_decl n env with
         | None => Accept tt | Some _ => Reject DuplicateDeclaration end ;;
    _ <- require (Nat.eqb (List.length params) 0) UniverseArity ;;
    _ <- primitive_check_signature fuel ty (primitive_signature op) ;;
    _ <- primitive_closed fuel 0 body ;;
    _ <- if primitive_is_text op then primitive_check_text_interface fuel env op
         else primitive_check_nat_equations fuel env op body ;;
    Accept (Some op)
  end.

Lemma primitive_equations_no_steps fuel env e es :
  primitive_check_equations 0 fuel env (e :: es) = Decline OutOfFuel.
Proof. reflexivity. Qed.

Lemma primitive_closed_no_fuel depth e :
  primitive_closed 0 depth e = Decline OutOfFuel.
Proof. reflexivity. Qed.

Theorem primitive_check_equations_accepts steps fuel env equations :
  primitive_check_equations steps fuel env equations = Accept tt ->
  Forall (fun e => check_defeq fuel env [] (primitive_context e)
    (primitive_lhs e) (primitive_rhs e) = Accept tt) equations.
Proof.
  revert steps. induction equations as [|e es IH]; intros steps H.
  - constructor.
  - destruct steps; simpl in H; try discriminate.
    destruct (check_defeq fuel env [] (primitive_context e)
      (primitive_lhs e) (primitive_rhs e)) as [u|r|d] eqn:He;
      simpl in H; try discriminate.
    destruct u. constructor; [exact He | exact (IH _ H)].
Qed.

Theorem classify_primitive_metadata_requires_certificate fuel env n params ty body op :
  classify_primitive fuel env n params ty body = Accept (Some op) ->
  primitive_lookup n = Some op /\
  ((primitive_is_text op = false /\
    primitive_check_nat_equations fuel env op body = Accept tt) \/
   (primitive_is_text op = true /\
    primitive_check_text_interface fuel env op = Accept tt)).
Proof.
  unfold classify_primitive.
  destruct (primitive_lookup n) as [selected|] eqn:Hselected;
    try (destruct (name_mem n _); discriminate).
  all: destruct (find_decl n env); simpl; try discriminate.
  all: destruct (require (Nat.eqb (List.length params) 0) UniverseArity);
    simpl; try discriminate.
  all: destruct (primitive_check_signature fuel ty _); simpl; try discriminate.
  all: destruct (primitive_closed fuel 0 body); simpl; try discriminate.
  all: destruct (primitive_is_text selected) eqn:Htext.
  all: try (destruct (primitive_check_text_interface fuel env selected) as [checked|r|d] eqn:Hcheck;
    simpl; try discriminate; destruct checked; intros H; inversion H; subst;
    split; [reflexivity | right; split; assumption]).
  all: destruct (primitive_check_nat_equations fuel env selected body) as [checked|r|d] eqn:Hcheck;
    simpl; try discriminate; destruct checked; intros H; inversion H; subst;
    split; [reflexivity | left; split; assumption].
Qed.

Theorem primitive_lookup_complete op :
  primitive_lookup (primitive_name op) = Some op.
Proof. destruct op; reflexivity. Qed.

Theorem primitive_bitwise_instances_require_certificate fuel env op body :
  primitive_check_bitwise_instance fuel env op body = Accept tt ->
  primitive_authenticated fuel env PNatBitwise = Accept tt.
Proof.
  unfold primitive_check_bitwise_instance.
  destruct (primitive_authenticated fuel env PNatBitwise) as [u|r|d] eqn:H;
    cbn; try discriminate.
  destruct u. intros _. reflexivity.
Qed.

Theorem classify_bitwise_requires_full_equations fuel env n params ty body :
  classify_primitive fuel env n params ty body = Accept (Some PNatBitwise) ->
  primitive_check_bitwise fuel env body = Accept tt.
Proof.
  intros H. apply classify_primitive_metadata_requires_certificate in H.
  destruct H as [_ [[_ H]|[H _]]]; [exact H | discriminate].
Qed.
