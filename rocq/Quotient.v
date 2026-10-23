(* SPDX-License-Identifier: Apache-2.0
   Canonical quotient signatures from Lean4Lean/Quot.lean. *)
From Stdlib Require Import List String Bool.
From LeanPort Require Import Syntax Universes Checker Declarations InductiveUtils.
Import ListNotations.
Open Scope string_scope.

Definition q_name := NameStr NameAnon "Quot".
Definition q_mk_name := NameStr q_name "mk".
Definition q_lift_name := NameStr q_name "lift".
Definition q_ind_name := NameStr q_name "ind".
Definition q_eq_name := NameStr NameAnon "Eq".
Definition q_arrow a b := EPi NameAnon BDefault a (lift 1 0 b).
Definition q_local s label bi ty := ind_fresh s (NameStr NameAnon label) bi ty.

Definition quotient_eq_type (u : level) : expr :=
  let '(a,s) := q_local initial_ind_state "alpha" BImplicit (ESort u) in
  close_pi [a] (q_arrow (local_expr a) (q_arrow (local_expr a) (ESort LZero))).
Definition quotient_eq_refl_type (u : level) : expr :=
  let '(alpha,s) := q_local initial_ind_state "alpha" BImplicit (ESort u) in
  let '(a,_) := q_local s "a" BDefault (local_expr alpha) in
  close_pi [alpha;a] (apply_exprs (EConst q_eq_name [u])
    [local_expr alpha;local_expr a;local_expr a]).

Definition quotient_check_eq (env : environment) : result unit :=
  match find_decl q_eq_name env with
  | Some d =>
    match decl_kind_of d,decl_params d with
    | DInductive info,[u] =>
      _ <- require (expr_eqb (decl_type d) (quotient_eq_type (LParam u))) MalformedDeclaration ;;
      match ind_ctors info with
      | [ctor] =>
        match find_decl ctor env with
        | Some c => match decl_kind_of c,decl_params c with
          | DConstructor ci,[v] =>
            require (name_eqb (ctor_induct ci) q_eq_name &&
              expr_eqb (decl_type c) (quotient_eq_refl_type (LParam v))) MalformedDeclaration
          | _,_ => Reject MalformedDeclaration
          end
        | None => Reject UnknownConstant
        end
      | _ => Reject MalformedDeclaration
      end
    | _,_ => Reject MalformedDeclaration
    end
  | None => Reject UnknownConstant
  end.

Definition canonical_quotient (kind : quotient_kind) : declaration :=
  let un := NameStr NameAnon "u" in
  let vn := NameStr NameAnon "v" in
  let u := LParam un in
  let v := LParam vn in
  let '(alpha,s) := q_local initial_ind_state "alpha" BImplicit (ESort u) in
  let av := local_expr alpha in
  let '(relation,s) := q_local s "r"
    (match kind with QType | QCtor => BDefault | _ => BImplicit end)
    (q_arrow av (q_arrow av (ESort LZero))) in
  let rv := local_expr relation in
  let quot := apply_exprs (EConst q_name [u]) [av;rv] in
  let '(a,s) := q_local s "a" BDefault av in
  let aa := local_expr a in
  let '(name,params,ty) :=
    match kind with
    | QType => (q_name,[un],close_pi [alpha;relation] (ESort u))
    | QCtor => (q_mk_name,[un],close_pi [alpha;relation;a] quot)
    | QLift =>
      let '(beta,s) := q_local s "beta" BImplicit (ESort v) in
      let bv := local_expr beta in
      let '(f,s) := q_local s "f" BDefault (q_arrow av bv) in
      let fv := local_expr f in
      let '(b,_) := q_local s "b" BDefault av in
      let bb := local_expr b in
      let equality := apply_exprs (EConst q_eq_name [v]) [bv;EApp fv aa;EApp fv bb] in
      let sanity := close_pi [a;b] (q_arrow (apply_exprs rv [aa;bb]) equality) in
      (q_lift_name,[un;vn],close_pi [alpha;relation;beta;f] (q_arrow sanity (q_arrow quot bv)))
    | QInd =>
      let '(beta,s) := q_local s "beta" BImplicit (q_arrow quot (ESort LZero)) in
      let bv := local_expr beta in
      let all_quot := close_pi [a] (EApp bv (apply_exprs (EConst q_mk_name [u]) [av;rv;aa])) in
      let '(q,_) := q_local s "q" BImplicit quot in
      (q_ind_name,[un],close_pi [alpha;relation]
        (close_pi [beta] (q_arrow all_quot (close_pi [q] (EApp bv (local_expr q))))))
    end in
  {| decl_hints := HintOpaque; decl_name := name; decl_params := params; decl_type := ty; decl_value := None;
     decl_kind_of := DQuotient kind |}.

(* A well-typed ordinary constant is not a built-in quotient dependency.
   Inspect the first visible declaration, as the checker does. *)
Definition quotient_header_matches (kind : quotient_kind) (d : declaration) : bool :=
  let generated := canonical_quotient kind in
  let same_kind := match kind, decl_kind_of d with
    | QType, DQuotient QType | QCtor, DQuotient QCtor
    | QLift, DQuotient QLift | QInd, DQuotient QInd => true
    | _, _ => false
    end in
  same_kind && name_eqb (decl_name d) (decl_name generated) &&
  names_unique (decl_params d) &&
  Nat.eqb (List.length (decl_params d)) (List.length (decl_params generated)) &&
  (match decl_value d with None => true | Some _ => false end) &&
  expr_eqb (decl_type d)
    (subst_levels (decl_params generated) (map LParam (decl_params d))
      (decl_type generated)).

Definition quotient_dependency (env : environment) (kind : quotient_kind) : bool :=
  match find_decl (decl_name (canonical_quotient kind)) env with
  | Some d => quotient_header_matches kind d
  | None => false
  end.

Definition quotient_dependencies (env : environment) (kind : quotient_kind) : bool :=
  match kind with
  | QType => true
  | QCtor | QLift => quotient_dependency env QType
  | QInd => quotient_dependency env QType && quotient_dependency env QCtor
  end.

Definition admit_quotient (fuel : nat) (env : environment) (n : name)
    (ps : list name) (ty : expr) (kind : quotient_kind) : result environment :=
  _ <- quotient_check_eq env ;;
  _ <- check_header fuel env n ps ty ;;
  let generated := canonical_quotient kind in
  _ <- require (name_eqb n (decl_name generated) &&
    Nat.eqb (List.length ps) (List.length (decl_params generated))) MalformedDeclaration ;;
  _ <- require (expr_eqb (subst_levels ps (map LParam (decl_params generated)) ty)
    (decl_type generated)) MalformedDeclaration ;;
  _ <- require (quotient_dependencies env kind) MalformedDeclaration ;;
  Accept (generated::env).
