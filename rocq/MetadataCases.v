(* SPDX-License-Identifier: Apache-2.0
   Small test-only syntax encoder and full-result entry probes. *)
From Stdlib Require Import List String Bool NArith.
From LeanPort Require Import Syntax Checker Primitives Declarations DagScope DagArena
  IndexedDagAdmission CombinedAdmissionRefinement MetadataFixtures Inductive Quotient.
Import ListNotations.
Open Scope string_scope.

Module MetadataCases.
Module M := Metadata.
Definition rows := list (positive * dag_node).
Definition emit (next : positive) (prior : rows) (node : dag_node) :=
  (next,Pos.succ next,List.app prior [(next,node)]).
Fixpoint quote (e : expr) (next : positive) : positive * positive * rows :=
  match e with
  | EBVar n => emit next [] (DBVar n)
  | EFVar n => emit next [] (DFVar n)
  | EMVar n => emit next [] (DMVar n)
  | ESort u => emit next [] (DSort u)
  | EConst n us => emit next [] (DConst n us)
  | ELit l => emit next [] (DLit l)
  | EApp f a => let '(fi,next,fs) := quote f next in
    let '(ai,next,ars) := quote a next in emit next (List.app fs ars) (DApp fi ai)
  | ELam n bi a b => let '(ai,next,ars) := quote a next in
    let '(bi0,next,bs) := quote b next in emit next (List.app ars bs) (DLam n bi ai bi0)
  | EPi n bi a b => let '(ai,next,ars) := quote a next in
    let '(bi0,next,bs) := quote b next in emit next (List.app ars bs) (DPi n bi ai bi0)
  | ELet n a v b nd => let '(ai,next,ars) := quote a next in
    let '(vi,next,vs) := quote v next in let '(bi,next,bs) := quote b next in
    emit next (List.app ars (List.app vs bs)) (DLet n ai vi bi nd)
  | EProj n i a => let '(ai,next,ars) := quote a next in emit next ars (DProj n i ai)
  | EMData a => let '(ai,next,ars) := quote a next in emit next ars (DMData ai)
  end.
Definition quote_pair ty body :=
  let '(tr,next,ts) := quote ty 1%positive in
  let '(br,_,bs) := quote body next in (tr,br,List.app ts bs).

Record test_case := {
  case_label : string;
  case_kind : dag_admission_kind;
  case_env : result environment;
  case_name : name;
  case_type : expr;
  case_body : expr;
  case_positive : bool
}.
Definition positive s k env n ty body :=
  {| case_label := s; case_kind := k; case_env := env; case_name := n;
     case_type := ty; case_body := body; case_positive := true |}.
Definition equality_case s value := positive s DagTheorem M.base_env (M.label s)
  (M.eq_nat value primitive_one) (M.refl_nat primitive_one).
Definition positives :=
  [positive "authenticated-add" (DagDefinition HintOpaque) M.base_env (primitive_name PNatAdd)
      (primitive_signature PNatAdd) M.add_body;
   equality_case "nat-recursor" M.rec_value;
   equality_case "indexed-equality-recursor" M.indexed_rec_value;
   equality_case "quot-lift" M.lift_value;
   equality_case "ordinary-projection" M.project_box;
   equality_case "dependent-projection" M.project_dep;
   positive "dependent-function" (DagDefinition HintOpaque) M.base_env (M.label "dependent-function")
     M.project_dep_type M.project_dep_fn;
   positive "quot-ind" DagTheorem M.base_env (M.label "quot-ind")
     (M.eq_nat primitive_one primitive_one) M.ind_value;
   positive "authenticated-add-reduction" DagTheorem M.with_add (M.label "add-reduction")
     (M.eq_nat M.add_value primitive_two) (M.refl_nat primitive_two)].
Definition change s env ty body (c : test_case) :=
  {| case_label := s; case_kind := case_kind c; case_env := env;
     case_name := case_name c; case_type := ty; case_body := body; case_positive := false |}.
Definition alter_env (f : environment -> environment) := env <- M.base_env ;; Accept (f env).
Definition negative_cases :=
  let add := positive "add" (DagDefinition HintOpaque) M.base_env (primitive_name PNatAdd)
    (primitive_signature PNatAdd) M.add_body in
  let rec := equality_case "rec" M.rec_value in
  let q := equality_case "quot" M.lift_value in
  let proj := equality_case "proj" M.project_box in
  [change "false-add-equations" M.base_env (case_type add) M.false_add add;
   change "missing-rec" (alter_env (M.without (rec_name core_nat_name)))
     (case_type add) (case_body add) add;
   change "unsafe-rec-shadow" (alter_env (M.unsafe_shadow (rec_name core_nat_name)))
     (case_type rec) (case_body rec) rec;
   change "missing-quot-mk" (alter_env (M.without q_mk_name)) (case_type q) (case_body q) q;
   change "unsafe-quot-shadow" (alter_env (M.unsafe_shadow q_lift_name))
     (case_type q) (case_body q) q;
   change "missing-projection-owner" (alter_env (M.without M.box_name))
     (case_type proj) (case_body proj) proj;
   change "unsafe-constructor-shadow" (alter_env (M.unsafe_shadow M.box_mk))
     (case_type proj) (case_body proj) proj;
   change "projection-out-of-range" M.base_env
     (M.eq_nat (EProj M.box_name 1 M.box_value) primitive_one) (case_body proj) proj;
   change "wrong-recursor-result" M.base_env
     (M.eq_nat M.rec_value primitive_zero) (M.refl_nat primitive_zero) rec;
   change "wrong-dependent-result" M.base_env
     (M.eq_nat M.project_dep primitive_zero) (M.refl_nat primitive_zero) proj;
   change "forged-nat-fields" (alter_env (map (fun d =>
     if name_eqb (decl_name d) core_succ_name then M.corrupt_fields d else d)))
     (primitive_signature PNatAdd) M.add_body add].
Definition cases := List.app positives negative_cases.
Definition ordinary env c := Declarations.admit M.fuel env
  (match case_kind c with
   | DagDefinition hints => InputDefinition hints (case_name c) [] (case_type c) (case_body c) InputSafe
   | DagTheorem => InputTheorem (case_name c) [] (case_type c) (case_body c)
   | DagOpaque => InputOpaque (case_name c) [] (case_type c) (case_body c) false end).
Definition guarded budget env c := let '(tr,br,rs) := quote_pair (case_type c) (case_body c) in
  indexed_dag_admit (case_kind c) budget M.fuel env (case_name c) [] rs tr br.
Definition forced budget env c := let '(tr,br,rs) := quote_pair (case_type c) (case_body c) in
  indexed_admit (fun _ => 0%N) (case_kind c) budget M.fuel env (case_name c) [] rs tr br.
Definition linear_cache_new budget env c := let '(tr,br,rs) := quote_pair (case_type c) (case_body c) in
  linear_cache_new_admit (case_kind c) budget M.fuel env (case_name c) [] rs tr br.
Definition expected env c :=
  Accept ({| decl_hints := match case_kind c with DagDefinition h => h | _ => HintOpaque end;
    decl_name := case_name c; decl_params := []; decl_type := case_type c;
    decl_value := Some (case_body c); decl_kind_of :=
    if name_eqb (case_name c) (primitive_name PNatAdd) then DPrimitive PNatAdd else
    match case_kind c with DagDefinition _ => DDefinition | DagTheorem => DTheorem
      | DagOpaque => DOpaque end |} :: env).
Definition check_decoded c := let '(tr,br,rs) := quote_pair (case_type c) (case_body c) in
  arena <- arena_build empty_arena rs ;;
  ty <- scope_ref (arena_scope arena) tr ;;
  body <- scope_ref (arena_scope arena) br ;;
  require (expr_eqb (scope_expr ty) (case_type c) &&
    expr_eqb (scope_expr body) (case_body c)) MalformedDeclaration.
Definition checked_case c := env <- case_env c ;; guarded 128 env c.
Definition reductions :=
  [("nat-recursor",M.rec_value,ELit (LitNat 1));
   ("indexed-equality-recursor",M.indexed_rec_value,ELit (LitNat 1));
   ("quot-lift",M.lift_value,ELit (LitNat 1));
   ("quot-ind",M.ind_value,M.refl_nat primitive_one);
   ("ordinary-projection",M.project_box,ELit (LitNat 1));
   ("dependent-projection",M.project_dep,ELit (LitNat 1))].
End MetadataCases.
