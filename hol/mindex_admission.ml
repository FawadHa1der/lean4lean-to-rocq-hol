(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_mindex_fields_valid_RULES,l4_mindex_fields_valid_INDUCT,l4_mindex_fields_valid_CASES =
 new_inductive_definition
 `(!g j. l4_mindex_fields_valid env bs ps p u g j []) /\
  (!g j f fs v.
    l4_mindex_positive bs f /\ l4_params_expr (l4_mindex_dom ps p j f) ps /\
    l4_edef env g (l4_mindex_dom ps p j f) (l4_mindex_dom ps p j f) (L4Sort v) /\
    (l4_level_equiv u L4Zero \/ l4_level_le v u) /\
    l4_mindex_fields_valid env bs ps p u (CONS (l4_mindex_dom ps p j f) g) (SUC j) fs ==>
    l4_mindex_fields_valid env bs ps p u g j (CONS f fs))`;;
let l4_mindex_ok = new_definition
 `!env ps pars u bs large claims. l4_mindex_ok env ps pars u bs large claims <=>
    1 < LENGTH bs /\ l4_names_distinct ps /\ l4_params_level u ps /\
    ALL (\p. l4_params_expr (SND p) ps) (APPEND pars (l4_mindex_all_indices bs)) /\
    l4_econtext env (REVERSE (MAP SND pars)) /\
    ALL (\d. ?v. l4_edef env [] (l4_entry_type d) (l4_entry_type d) (L4Sort v))
      (l4_mindex_headers ps pars u bs) /\
    ALL (\c. l4_mindex_fields_valid (APPEND (l4_mindex_headers ps pars u bs) env)
      bs ps (LENGTH pars) u (REVERSE (MAP SND pars)) 0
      (l4_mindex_fields (SND c))) (l4_mindex_flat bs 0) /\
    (large <=> l4_level_nonzero u) /\ ~(MEM (l4_fresh_univ ps) ps) /\
    l4_names_distinct (MAP l4_entry_name (APPEND (l4_mindex_generated ps pars u bs large) env)) /\
    ALL (\d. ~(l4_entry_tag d = L4AxiomKind)) (l4_mindex_generated ps pars u bs large) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_mindex_headers ps pars u bs) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_mindex_ctor_entries ps pars bs) /\
    ALL (\d. ?v. l4_edef (APPEND (l4_mindex_generated ps pars u bs large) env) []
      (l4_entry_type d) (l4_entry_type d) (L4Sort v)) (l4_mindex_generated ps pars u bs large) /\
    l4_metadata_matches claims (l4_mindex_generated ps pars u bs large) /\
    ALL (\d. ~l4_protected_name (l4_entry_name d)) (l4_mindex_generated ps pars u bs large) /\
    l4_no_nested_claims (l4_mindex_generated ps pars u bs large) /\ l4_no_nested_claims claims /\
    ALL (\c. LENGTH (l4_mindex_result (SND c)) = LENGTH (l4_mindex_indices (EL (FST c) bs)) /\
      ALL (\a. l4_mutual_without (MAP l4_mindex_name bs) a /\ l4_params_expr a ps)
        (l4_mindex_result (SND c))) (l4_mindex_flat bs 0)`;;
