(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Loaded after the environment typing and context judgments, before EValid. *)
let l4_mutual_fields_valid_RULES,l4_mutual_fields_valid_INDUCT,l4_mutual_fields_valid_CASES =
 new_inductive_definition
 `(!g j. l4_mutual_fields_valid env ns ps p u g j []) /\
  (!g j f fs v.
    l4_mutual_positive ns f /\ l4_params_expr (l4_mutual_dom ps p j f) ps /\
    l4_edef env g (l4_mutual_dom ps p j f) (l4_mutual_dom ps p j f) (L4Sort v) /\
    (l4_level_equiv u L4Zero \/ l4_level_le v u) /\
    l4_mutual_fields_valid env ns ps p u (CONS (l4_mutual_dom ps p j f) g) (SUC j) fs ==>
    l4_mutual_fields_valid env ns ps p u g j (CONS f fs))`;;

let l4_mutual_ok = new_definition
 `!env ps pars u bs large claims. l4_mutual_ok env ps pars u bs large claims <=>
    1 < LENGTH bs /\
    l4_names_distinct ps /\ l4_params_level u ps /\
    ALL (\p. l4_params_expr (SND p) ps) pars /\
    l4_econtext env (REVERSE (MAP SND pars)) /\
    ALL (\d. ?v. l4_edef env [] (l4_entry_type d) (l4_entry_type d) (L4Sort v))
      (l4_mutual_headers ps pars u bs) /\
    ALL (\c. l4_mutual_fields_valid (APPEND (l4_mutual_headers ps pars u bs) env)
      (MAP l4_mutual_name bs) ps (LENGTH pars) u (REVERSE (MAP SND pars)) 0
      (l4_mutual_fields (SND c))) (l4_mutual_flat bs 0) /\
    (large <=> l4_level_nonzero u) /\ ~(MEM (l4_fresh_univ ps) ps) /\
    l4_names_distinct (MAP l4_entry_name (APPEND (l4_mutual_generated ps pars u bs large) env)) /\
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_mutual_generated ps pars u bs large) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_mutual_headers ps pars u bs) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_mutual_ctor_entries ps pars bs) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_mutual_generated ps pars u bs large) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_mutual_generated ps pars u bs large) /\
    l4_metadata_matches claims (l4_mutual_generated ps pars u bs large) /\
    ALL (\d. ~l4_protected_name (l4_entry_name d)) (l4_mutual_generated ps pars u bs large) /\
    l4_no_nested_claims (l4_mutual_generated ps pars u bs large) /\ l4_no_nested_claims claims`;;

let l4_mutual_ok_no_axioms = prove
 (`!env ps pars u bs large claims. l4_mutual_ok env ps pars u bs large claims ==>
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_mutual_generated ps pars u bs large)`,
  SIMP_TAC [l4_mutual_ok]);;
let l4_mutual_ok_unique = prove
 (`!env ps pars u bs large claims. l4_mutual_ok env ps pars u bs large claims ==>
    l4_names_distinct (MAP l4_entry_name (APPEND (l4_mutual_generated ps pars u bs large) env))`,
  SIMP_TAC [l4_mutual_ok]);;
