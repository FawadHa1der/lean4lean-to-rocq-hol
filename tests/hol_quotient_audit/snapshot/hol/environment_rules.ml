(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/inductive_syntax.ml";;
needs "hol/primitive_names.ml";;
needs "hol/nested_names.ml";;
needs "hol/family_syntax.ml";;
needs "hol/indexed_syntax.ml";;
needs "hol/projection_syntax.ml";;
needs "hol/primitive_contracts.ml";;
needs "hol/quotient_syntax.ml";;

let l4_entry_kind_INDUCT,l4_entry_kind_RECURSION = define_type
 "l4_entry_kind = L4DefKind | L4ThmKind | L4OpaqueKind | L4AxiomKind | L4Generated l4_role | L4QuotientKind l4_quot_kind";;
let l4_entry_INDUCT,l4_entry_RECURSION = define_type
 "l4_entry = L4Entry l4_entry_kind l4_name (l4_name list) l4_expr l4_expr";;
let l4_entry_tag = new_recursive_definition l4_entry_RECURSION
 `l4_entry_tag (L4Entry k n ps a v) = k`;;
let l4_entry_name = new_recursive_definition l4_entry_RECURSION
 `l4_entry_name (L4Entry k n ps a v) = n`;;
let l4_entry_params = new_recursive_definition l4_entry_RECURSION
 `l4_entry_params (L4Entry k n ps a v) = ps`;;
let l4_entry_type = new_recursive_definition l4_entry_RECURSION
 `l4_entry_type (L4Entry k n ps a v) = a`;;
let l4_entry_body = new_recursive_definition l4_entry_RECURSION
 `l4_entry_body (L4Entry k n ps a v) = v`;;
let l4_entry_transparent = new_definition
 `l4_entry_transparent d <=>
    l4_entry_tag d = L4DefKind \/ l4_entry_tag d = L4ThmKind`;;

needs "hol/inductive_entries.ml";;
needs "hol/family_entries.ml";;
needs "hol/indexed_entries.ml";;
needs "hol/projection_entries.ml";;
needs "hol/quotient_entries.ml";;

(* The first thirteen clauses deliberately match the pure engine's rule order. *)
let l4_edef_RULES,l4_edef_INDUCT,l4_edef_CASES = new_inductive_definition
 `(!env g i. i < LENGTH g ==>
     l4_edef env g (L4BVar i) (L4BVar i) (l4_lift (EL i g) (SUC i) 0)) /\
  (!env g u v. l4_level_equiv u v ==>
     l4_edef env g (L4Sort u) (L4Sort v) (L4Sort (L4Succ u))) /\
  (!env g f f' a a' n d b.
     l4_edef env g f f' (L4Pi n d b) /\ l4_edef env g a a' d ==>
     l4_edef env g (L4App f a) (L4App f' a') (l4_inst a b)) /\
  (!env g n n' a a' b b' t u.
     l4_edef env g a a' (L4Sort u) /\ l4_edef env (CONS a g) b b' t ==>
     l4_edef env g (L4Lam n a b) (L4Lam n' a' b') (L4Pi n a t)) /\
  (!env g n n' a a' b b' u v.
     l4_edef env g a a' (L4Sort u) /\ l4_edef env (CONS a g) b b' (L4Sort v) ==>
     l4_edef env g (L4Pi n a b) (L4Pi n' a' b') (L4Sort (L4IMax u v))) /\
  (!env g a b e e' u.
     l4_edef env g a b (L4Sort u) /\ l4_edef env g e e' a ==>
     l4_edef env g e e' b) /\
  (!env g e e' a. l4_edef env g e e' a ==> l4_edef env g e' e a) /\
  (!env g e e' e'' a.
     l4_edef env g e e' a /\ l4_edef env g e' e'' a ==> l4_edef env g e e'' a) /\
  (!env g n a b t v.
     l4_edef env (CONS a g) b b t /\ l4_edef env g v v a ==>
     l4_edef env g (L4App (L4Lam n a b) v) (l4_inst v b) (l4_inst v t)) /\
  (!env g n a b e.
     l4_edef env g e e (L4Pi n a b) ==>
     l4_edef env g (L4Lam n a (L4App (l4_lift e 1 0) (L4BVar 0))) e
       (L4Pi n a b)) /\
  (!env g p h h'.
     l4_edef env g p p (L4Sort L4Zero) /\ l4_edef env g h h p /\ l4_edef env g h' h' p ==>
     l4_edef env g h h' p) /\
  (!env g n a v b t u.
     l4_edef env g a a (L4Sort u) /\ l4_edef env g v v a /\
     l4_edef env (CONS a g) b b t ==>
     l4_edef env g (L4Let n a v b) (L4Let n a v b) (l4_inst v t)) /\
  (!env g n a v b t u.
     l4_edef env g a a (L4Sort u) /\ l4_edef env g v v a /\
     l4_edef env (CONS a g) b b t ==>
     l4_edef env g (L4Let n a v b) (l4_inst v b) (l4_inst v t)) /\
  (!env g d us vs.
    MEM d env /\ LENGTH (l4_entry_params d) = LENGTH us /\
    ALL2 l4_level_equiv us vs ==>
    l4_edef env g (L4Const (l4_entry_name d) us) (L4Const (l4_entry_name d) vs)
      (l4_expr_lsubst (l4_entry_type d) (l4_entry_params d) us)) /\
  (!env g d us.
    MEM d env /\ LENGTH (l4_entry_params d) = LENGTH us /\ l4_entry_transparent d ==>
    l4_edef env g (L4Const (l4_entry_name d) us)
      (l4_expr_lsubst (l4_entry_body d) (l4_entry_params d) us)
      (l4_expr_lsubst (l4_entry_type d) (l4_entry_params d) us)) /\
  (!env g d ns np nm rs isk c nf rhs us cls prefix cpars fields a.
    MEM d env /\
    l4_entry_tag d = L4Generated (L4RecursorRole ns np 0 1 nm rs isk F) /\
    MEM (L4RecRule c nf rhs) rs /\
    LENGTH (l4_entry_params d) = LENGTH us /\ LENGTH prefix = np + SUC nm /\
    LENGTH cpars = np /\ LENGTH fields = nf /\
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const c cls) (APPEND cpars fields)]))
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const c cls) (APPEND cpars fields)])) a /\
    l4_edef env g
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields))
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields)) a ==>
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const c cls) (APPEND cpars fields)]))
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields)) a) /\
  (!env g n.
    l4_edef env g (L4Const l4_nat_name []) (L4Const l4_nat_name [])
      (L4Sort (L4Succ L4Zero)) ==>
    l4_edef env g (L4NatLit n) (L4NatLit n) (L4Const l4_nat_name [])) /\
  (!env g.
    l4_edef env g (L4Const (L4String l4_nat_name [122;101;114;111]) [])
      (L4Const (L4String l4_nat_name [122;101;114;111]) []) (L4Const l4_nat_name []) ==>
    l4_edef env g (L4NatLit 0)
      (L4Const (L4String l4_nat_name [122;101;114;111]) []) (L4Const l4_nat_name [])) /\
  (!env g n.
    l4_edef env g (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Pi L4Anonymous (L4Const l4_nat_name []) (L4Const l4_nat_name [])) ==>
    l4_edef env g (L4NatLit (SUC n))
      (L4App (L4Const (L4String l4_nat_name [115;117;99;99]) []) (L4NatLit n))
      (L4Const l4_nat_name [])) /\
  (!env g d ns np ni nm rs isk c nf rhs us cls prefix cpars fields indices a.
    MEM d env /\
    l4_entry_tag d = L4Generated (L4RecursorRole ns np ni 1 nm rs isk F) /\
    MEM (L4RecRule c nf rhs) rs /\
    LENGTH (l4_entry_params d) = LENGTH us /\ LENGTH prefix = np + SUC nm /\
    LENGTH cpars = np /\ LENGTH fields = nf /\ LENGTH indices = ni /\
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us) (APPEND prefix
        (APPEND indices [l4_apps (L4Const c cls) (APPEND cpars fields)])))
      (l4_apps (L4Const (l4_entry_name d) us) (APPEND prefix
        (APPEND indices [l4_apps (L4Const c cls) (APPEND cpars fields)]))) a /\
    l4_edef env g
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields))
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields)) a ==>
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us) (APPEND prefix
        (APPEND indices [l4_apps (L4Const c cls) (APPEND cpars fields)])))
      (l4_apps (l4_expr_lsubst rhs (l4_entry_params d) us) (APPEND prefix fields)) a) /\
  (!env g ind ctor owner idx major us pars indices r scan ds u.
    MEM ind env /\ MEM ctor env /\
    l4_projection_meta ind ctor owner idx us pars indices /\
    l4_edef env g major major (l4_apps (L4Const owner us) (APPEND pars indices)) /\
    l4_edef env g (l4_apps (L4Const owner us) (APPEND pars indices))
      (l4_apps (L4Const owner us) (APPEND pars indices)) (L4Sort u) /\
    l4_edef env g (l4_apps (L4Const (l4_entry_name ctor) us) pars)
      (l4_apps (L4Const (l4_entry_name ctor) us) pars) r /\
    l4_proj_drop_ok pars (l4_expr_lsubst (l4_entry_type ctor) (l4_entry_params ctor) us) /\
    r = l4_proj_drop pars (l4_expr_lsubst (l4_entry_type ctor) (l4_entry_params ctor) us) /\
    scan = l4_proj_scan idx owner major 0 r /\
    ALL (\q. l4_is_pi (FST q)) scan /\
    MAP FST ds = MAP (\q. l4_pi_domain (FST q)) scan /\
    (!a v. MEM (a,v) ds ==> l4_edef env g a a (L4Sort v)) /\
    (l4_level_nonzero u \/
      ALL2 (\q d. SND q ==> l4_level_equiv (SND d) L4Zero) scan ds) ==>
    l4_edef env g (L4Proj owner idx major) (L4Proj owner idx major)
      (l4_proj_selected scan)) /\
  (!env g ctor role owner idx major us pars fields major_type a.
    MEM ctor env /\ l4_entry_tag ctor = L4Generated role /\
    l4_proj_ctor_args role owner idx pars fields /\
    LENGTH (l4_entry_params ctor) = LENGTH us /\
    l4_edef env g major (l4_apps (L4Const (l4_entry_name ctor) us) (APPEND pars fields)) major_type /\
    l4_edef env g (L4Proj owner idx major) (L4Proj owner idx major) a /\
    l4_edef env g (EL idx fields) (EL idx fields) a ==>
    l4_edef env g (L4Proj owner idx major) (EL idx fields) a) /\
  (!env g owner idx major major' b a.
    l4_edef env g major major' b /\
    l4_edef env g (L4Proj owner idx major) (L4Proj owner idx major) a /\
    l4_edef env g (L4Proj owner idx major') (L4Proj owner idx major') a ==>
    l4_edef env g (L4Proj owner idx major) (L4Proj owner idx major') a) /\
  (!env g ind ctor owner us pars nf major.
    MEM ind env /\ MEM ctor env /\ l4_eta_meta ind ctor owner us pars nf /\
    l4_edef env g major major (l4_apps (L4Const owner us) pars) /\
    l4_edef env g (l4_eta_expansion (l4_entry_name ctor) owner us pars nf major)
      (l4_eta_expansion (l4_entry_name ctor) owner us pars nf major)
      (l4_apps (L4Const owner us) pars) ==>
    l4_edef env g major (l4_eta_expansion (l4_entry_name ctor) owner us pars nf major)
      (l4_apps (L4Const owner us) pars)) /\
  (!env g d ctor k us cls prefix args a.
    MEM d env /\ MEM ctor env /\
    l4_quot_header d k /\ l4_quot_header ctor L4QuotCtor /\
    (k = L4QuotLift \/ k = L4QuotInd) /\
    LENGTH us = l4_quot_arity k /\ LENGTH cls = 1 /\
    LENGTH prefix = (if k = L4QuotLift then 5 else 4) /\ LENGTH args = 3 /\
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const (l4_entry_name ctor) cls) args]))
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const (l4_entry_name ctor) cls) args])) a /\
    l4_edef env g (L4App (EL 3 prefix) (EL 2 args))
      (L4App (EL 3 prefix) (EL 2 args)) a ==>
    l4_edef env g
      (l4_apps (L4Const (l4_entry_name d) us)
        (APPEND prefix [l4_apps (L4Const (l4_entry_name ctor) cls) args]))
      (L4App (EL 3 prefix) (EL 2 args)) a)`;;

let l4_fields_valid_RULES,l4_fields_valid_INDUCT,l4_fields_valid_CASES = new_inductive_definition
 `(l4_fields_valid env u []) /\
  (!fs. l4_fields_valid env u fs ==> l4_fields_valid env u (CONS L4Recursive fs)) /\
  (!a v fs. l4_params_expr a [] /\ l4_edef env [] a a (L4Sort v) /\
    l4_level_le v u /\ l4_fields_valid env u fs ==>
    l4_fields_valid env u (CONS (L4Data a) fs))`;;

let l4_econtext_RULES,l4_econtext_INDUCT,l4_econtext_CASES = new_inductive_definition
 `(!env. l4_econtext env []) /\
  (!env g a u. l4_econtext env g /\ l4_edef env g a a (L4Sort u) ==>
    l4_econtext env (CONS a g))`;;

let l4_family_fields_RULES,l4_family_fields_INDUCT,l4_family_fields_CASES = new_inductive_definition
 `(l4_family_fields env g ps u [] []) /\
  (!fs vs. l4_family_fields env g ps u fs vs ==>
    l4_family_fields env g ps u (CONS L4Recursive fs) (CONS u vs)) /\
  (!a v fs vs. l4_params_expr a ps /\ l4_edef env g a a (L4Sort v) /\
    (l4_level_equiv u L4Zero \/ l4_level_le v u) /\
    l4_family_fields env g ps u fs vs ==>
    l4_family_fields env g ps u (CONS (L4Data a) fs) (CONS v vs))`;;

let l4_family_ok = new_definition
 `!env i ps pars u cs vss large k claims. l4_family_ok env i ps pars u cs vss large k claims <=>
    l4_names_distinct ps /\ l4_params_level u ps /\
    ALL (\p. l4_params_expr (SND p) ps) pars /\
    l4_econtext env (REVERSE (MAP SND pars)) /\
    ALL2 (\c vs. l4_family_fields env (REVERSE (MAP SND pars)) ps u
      (l4_ctor_fields c) vs) cs vss /\
    (large <=> l4_family_large u cs vss) /\ (k <=> l4_family_k u cs) /\
    ~(MEM (l4_fresh_univ ps) ps) /\
    l4_names_distinct (MAP l4_entry_name
      (APPEND (l4_family_generated i ps pars u cs large k) env)) /\
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_family_generated i ps pars u cs large k) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_family_generated i ps pars u cs large k) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_family_generated i ps pars u cs large k) /\
    l4_metadata_matches claims (l4_family_generated i ps pars u cs large k) /\
    l4_family_primitive i ps pars u cs /\
    l4_no_nested_claims (l4_family_generated i ps pars u cs large k) /\
    l4_no_nested_claims claims`;;

let l4_index_fields_valid_RULES,l4_index_fields_valid_INDUCT,l4_index_fields_valid_CASES = new_inductive_definition
 `(!g j. l4_index_fields_valid env i ps p ni u g j [] []) /\
  (!g j f fs v vs.
    l4_index_positive i ni f /\ l4_params_expr (l4_index_dom i ps p j f) ps /\
    l4_edef env g (l4_index_dom i ps p j f) (l4_index_dom i ps p j f) (L4Sort v) /\
    (l4_level_equiv u L4Zero \/ l4_level_le v u) /\
    l4_index_fields_valid env i ps p ni u (CONS (l4_index_dom i ps p j f) g) (SUC j) fs vs ==>
    l4_index_fields_valid env i ps p ni u g j (CONS f fs) (CONS v vs))`;;

let l4_index_ok = new_definition
 `!env i ps pars inds u cs vss large k claims. l4_index_ok env i ps pars inds u cs vss large k claims <=>
    l4_names_distinct ps /\ l4_params_level u ps /\
    ALL (\p. l4_params_expr (SND p) ps) (APPEND pars inds) /\
    l4_econtext env (REVERSE (MAP SND pars)) /\
    (?v. l4_edef env [] (l4_entry_type (l4_index_header i ps pars inds u cs))
      (l4_entry_type (l4_index_header i ps pars inds u cs)) (L4Sort v)) /\
    ALL2 (\c vs. l4_index_fields_valid (CONS (l4_index_header i ps pars inds u cs) env)
      i ps (LENGTH pars) (LENGTH inds) u (REVERSE (MAP SND pars)) 0 (l4_index_fields c) vs) cs vss /\
    ALL (\c. LENGTH (l4_index_result c) = LENGTH inds /\
      ALL (\a. l4_without_const i a /\ l4_params_expr a ps) (l4_index_result c)) cs /\
    (large <=> l4_index_large u cs vss) /\ (k <=> l4_index_k u cs) /\
    ~(MEM (l4_fresh_univ ps) ps) /\
    l4_names_distinct (MAP l4_entry_name (APPEND (l4_index_generated i ps pars inds u cs large k) env)) /\
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_index_generated i ps pars inds u cs large k) /\
    ALL (\d. ?v. l4_edef (CONS (l4_index_header i ps pars inds u cs) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_index_ctor_entries i ps pars cs 0) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_index_generated i ps pars inds u cs large k) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_index_generated i ps pars inds u cs large k) /\
    l4_metadata_matches claims (l4_index_generated i ps pars inds u cs large k) /\
    ALL (\d. ~l4_protected_name (l4_entry_name d)) (l4_index_generated i ps pars inds u cs large k) /\
    l4_no_nested_claims (l4_index_generated i ps pars inds u cs large k) /\ l4_no_nested_claims claims`;;

let l4_evalid_RULES,l4_evalid_INDUCT,l4_evalid_CASES = new_inductive_definition
 `(l4_evalid policy []) /\
  (!env n ps a u.
    l4_evalid policy env /\
    MEM (L4Entry L4AxiomKind n ps a (L4Sort L4Zero)) policy /\
    ~(MEM n (MAP l4_entry_name env)) /\ l4_names_distinct ps /\
    l4_params_expr a ps /\ l4_edef env [] a a (L4Sort u) /\ ~l4_protected_name n ==>
    l4_evalid policy (CONS (L4Entry L4AxiomKind n ps a (L4Sort L4Zero)) env)) /\
  (!env k n ps a v u.
    l4_evalid policy env /\ l4_regular_kind k /\
    ~(MEM n (MAP l4_entry_name env)) /\ l4_names_distinct ps /\
    l4_params_expr a ps /\ l4_params_expr v ps /\
    l4_edef env [] a a (L4Sort u) /\ l4_edef env [] v v a /\
    (k = L4ThmKind ==> l4_level_equiv u L4Zero) /\ ~l4_protected_name n ==>
    l4_evalid policy (CONS (L4Entry k n ps a v) env)) /\
  (!env i u cs claims.
    l4_evalid policy env /\ l4_params_level u [] /\ l4_level_nonzero u /\
    ALL (\c. l4_fields_valid env u (l4_ctor_fields c)) cs /\
    l4_names_distinct (MAP l4_entry_name (APPEND (l4_generated i u cs) env)) /\
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_generated i u cs) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_generated i u cs) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_generated i u cs) /\
    l4_metadata_matches claims (l4_generated i u cs) /\ l4_primitive_block i u cs /\
    l4_no_nested_block i cs /\ l4_no_nested_claims claims ==>
    l4_evalid policy (APPEND (l4_generated i u cs) env)) /\
  (!env i ps pars u cs vss large k claims.
    l4_evalid policy env /\ l4_family_ok env i ps pars u cs vss large k claims ==>
    l4_evalid policy (APPEND (l4_family_generated i ps pars u cs large k) env)) /\
  (!env i ps pars inds u cs vss large k claims.
    l4_evalid policy env /\ l4_index_ok env i ps pars inds u cs vss large k claims ==>
    l4_evalid policy (APPEND (l4_index_generated i ps pars inds u cs large k) env)) /\
  (!env n ps a b.
    l4_evalid policy env /\ ~(MEM n (MAP l4_entry_name env)) /\
    l4_prim_definition_contract (l4_edef env) n ps a b ==>
    l4_evalid policy (CONS (L4Entry L4DefKind n ps a b) env)) /\
  (!env d k ind ctor u v w.
    l4_evalid policy env /\
    ~(MEM (l4_entry_name d) (MAP l4_entry_name env)) /\
    MEM ind env /\ MEM ctor env /\ l4_quot_eq_meta ind ctor u v /\
    l4_quot_header d k /\ l4_quot_dependencies env k /\
    l4_params_expr (l4_entry_type d) (l4_entry_params d) /\
    l4_edef env [] (l4_entry_type d) (l4_entry_type d) (L4Sort w) ==>
    l4_evalid policy (CONS d env))`;;

let l4_checked = new_definition
 `!policy env g e e' a. l4_checked policy env g e e' a <=>
    l4_evalid policy env /\ l4_econtext env g /\ l4_edef env g e e' a`;;

let l4_checked_typing = prove
 (`!policy env g e e' a. l4_checked policy env g e e' a ==> l4_edef env g e e' a`,
  SIMP_TAC [l4_checked]);;

let l4_evalid_permissions = prove
 (`!policy env. l4_evalid policy env ==>
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) env`,
  GEN_TAC THEN MATCH_MP_TAC (SPEC `policy:l4_entry list` l4_evalid_INDUCT) THEN
  REWRITE_TAC [l4_index_ok;l4_family_ok;ALL;ALL_APPEND;l4_entry_tag;l4_regular_kind] THEN
  MESON_TAC [distinctness "l4_entry_kind";ALL_IMP;l4_quot_header_not_axiom]);;

let l4_evalid_unique = prove
 (`!policy env. l4_evalid policy env ==>
    l4_names_distinct (MAP l4_entry_name env)`,
  GEN_TAC THEN MATCH_MP_TAC (SPEC `policy:l4_entry list` l4_evalid_INDUCT) THEN
  REWRITE_TAC [l4_index_ok;l4_family_ok;MAP;l4_names_distinct;l4_entry_name] THEN MESON_TAC []);;

let l4_checked_permissions = prove
 (`!policy env g e e' a. l4_checked policy env g e e' a ==>
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) env`,
  MESON_TAC [l4_checked;l4_evalid_permissions]);;

let l4_opaque_not_delta = prove
 (`!n ps a v. ~l4_entry_transparent (L4Entry L4OpaqueKind n ps a v)`,
  REWRITE_TAC [l4_entry_transparent;l4_entry_tag;distinctness "l4_entry_kind"]);;

let l4_generated_not_regular = prove
 (`!r. ~l4_regular_kind (L4Generated r)`,
  REWRITE_TAC [l4_regular_kind;distinctness "l4_entry_kind"]);;

let l4_generated_not_delta = prove
 (`!r n ps a v. ~l4_entry_transparent (L4Entry (L4Generated r) n ps a v)`,
  REWRITE_TAC [l4_entry_transparent;l4_entry_tag;distinctness "l4_entry_kind"]);;

let l4_quotient_not_regular = prove
 (`!k. ~l4_regular_kind (L4QuotientKind k)`,
  REWRITE_TAC [l4_regular_kind;distinctness "l4_entry_kind"]);;
let l4_quotient_not_delta = prove
 (`!k n ps a v. ~l4_entry_transparent (L4Entry (L4QuotientKind k) n ps a v)`,
  REWRITE_TAC [l4_entry_transparent;l4_entry_tag;distinctness "l4_entry_kind"]);;

let l4_inductive_checked = new_definition
 `!policy env i u cs claims. l4_inductive_checked policy env i u cs claims <=>
    (l4_evalid policy env /\ l4_params_level u [] /\ l4_level_nonzero u /\
     ALL (\c. l4_fields_valid env u (l4_ctor_fields c)) cs /\
     l4_names_distinct (MAP l4_entry_name (APPEND (l4_generated i u cs) env)) /\
     ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_generated i u cs) /\
     ALL (\d. ?v. l4_edef (APPEND (l4_generated i u cs) env) []
       (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_generated i u cs) /\
     l4_metadata_matches claims (l4_generated i u cs) /\ l4_primitive_block i u cs /\
     l4_no_nested_block i cs /\ l4_no_nested_claims claims) /\
    l4_evalid policy (APPEND (l4_generated i u cs) env)`;;

let l4_inductive_checked_metadata = prove
 (`!policy env i u cs claims. l4_inductive_checked policy env i u cs claims ==>
    l4_metadata_matches claims (l4_generated i u cs)`,
  SIMP_TAC [l4_inductive_checked]);;

let l4_inductive_checked_elimination = prove
 (`!policy env i u cs claims. l4_inductive_checked policy env i u cs claims ==>
    !rho. 0 < l4_eval_level u rho`,
  SIMP_TAC [l4_inductive_checked;l4_level_nonzero]);;

let l4_inductive_checked_primitives = prove
 (`!policy env i u cs claims. l4_inductive_checked policy env i u cs claims ==>
    l4_primitive_block i u cs`,
  SIMP_TAC [l4_inductive_checked]);;

let l4_inductive_checked_no_nested = prove
 (`!policy env i u cs claims. l4_inductive_checked policy env i u cs claims ==>
    l4_no_nested_block i cs /\ l4_no_nested_claims claims`,
  SIMP_TAC [l4_inductive_checked]);;

let l4_family_checked = new_definition
 `!policy env i ps pars u cs vss large k claims.
    l4_family_checked policy env i ps pars u cs vss large k claims <=>
    l4_evalid policy env /\ l4_family_ok env i ps pars u cs vss large k claims /\
    l4_evalid policy (APPEND (l4_family_generated i ps pars u cs large k) env)`;;

let l4_family_checked_metadata = prove
 (`!policy env i ps pars u cs vss large k claims.
    l4_family_checked policy env i ps pars u cs vss large k claims ==>
    l4_metadata_matches claims (l4_family_generated i ps pars u cs large k)`,
  SIMP_TAC [l4_family_checked;l4_family_ok]);;

let l4_family_checked_elimination = prove
 (`!policy env i ps pars u cs vss large k claims.
    l4_family_checked policy env i ps pars u cs vss large k claims ==>
    (large <=> l4_family_large u cs vss) /\ (k <=> l4_family_k u cs)`,
  SIMP_TAC [l4_family_checked;l4_family_ok]);;

let l4_family_checked_guards = prove
 (`!policy env i ps pars u cs vss large k claims.
    l4_family_checked policy env i ps pars u cs vss large k claims ==>
    l4_family_primitive i ps pars u cs /\ l4_no_nested_claims claims`,
  SIMP_TAC [l4_family_checked;l4_family_ok]);;

let l4_index_checked = new_definition
 `!policy env i ps pars inds u cs vss large k claims.
    l4_index_checked policy env i ps pars inds u cs vss large k claims <=>
    l4_evalid policy env /\ l4_index_ok env i ps pars inds u cs vss large k claims /\
    l4_evalid policy (APPEND (l4_index_generated i ps pars inds u cs large k) env)`;;
let l4_index_checked_metadata = prove
 (`!policy env i ps pars inds u cs vss large k claims.
    l4_index_checked policy env i ps pars inds u cs vss large k claims ==>
    l4_metadata_matches claims (l4_index_generated i ps pars inds u cs large k)`,
  SIMP_TAC [l4_index_checked;l4_index_ok]);;
let l4_index_checked_elimination = prove
 (`!policy env i ps pars inds u cs vss large k claims.
    l4_index_checked policy env i ps pars inds u cs vss large k claims ==>
    (large <=> l4_index_large u cs vss) /\ (k <=> l4_index_k u cs)`,
  SIMP_TAC [l4_index_checked;l4_index_ok]);;
let l4_index_checked_guards = prove
 (`!policy env i ps pars inds u cs vss large k claims.
    l4_index_checked policy env i ps pars inds u cs vss large k claims ==>
    l4_no_nested_claims claims /\
    ALL (\d. ~l4_protected_name (l4_entry_name d)) (l4_index_generated i ps pars inds u cs large k)`,
  SIMP_TAC [l4_index_checked;l4_index_ok]);;
