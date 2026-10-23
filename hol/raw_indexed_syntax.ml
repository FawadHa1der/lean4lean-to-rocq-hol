(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Bounded function-recursive raw slice of pinned Inductive/Add.checkPositivity. *)
needs "hol/reducible_bridge.ml";;

let l4_raw_index_function_RULES,l4_raw_index_function_INDUCT,l4_raw_index_function_CASES =
  new_inductive_definition
 `(!env i ps p u g j e v.
    l4_head env e (l4_family_app i ps p j) /\ l4_params_expr e ps /\
    l4_raw_sort env g e v /\ l4_level_le v u ==>
    l4_raw_index_function env i ps p u g j [] e) /\
  (!env i ps p u g j e n a b d ds v w.
    l4_head env e (L4Pi n a b) /\ l4_without_const i a /\
    l4_anon a = l4_anon d /\ l4_params_expr e ps /\
    l4_raw_sort env g e v /\ l4_level_le v u /\ l4_raw_sort env g a w /\
    l4_raw_index_function env i ps p u (CONS a g) (SUC j) ds b ==>
    l4_raw_index_function env i ps p u g j (CONS d ds) e)`;;

let l4_raw_index_field = new_recursive_definition l4_index_field_RECURSION
 `(l4_raw_index_field env i ps p u g j (L4IndexData d) e <=>
    ?h. l4_head env e h /\ l4_without_const i h /\ l4_anon h = l4_anon d) /\
  (l4_raw_index_field env i ps p u g j (L4IndexRecursive xs) e <=>
    xs = [] /\ l4_raw_index_function env i ps p u g j [] e) /\
  (l4_raw_index_field env i ps p u g j (L4IndexFunction ds xs) e <=>
    ~(ds = []) /\ xs = [] /\ l4_raw_index_function env i ps p u g j ds e)`;;
let l4_raw_index_fields_RULES,l4_raw_index_fields_INDUCT,l4_raw_index_fields_CASES =
  new_inductive_definition
 `(!env i ps p u g j.
    l4_raw_index_fields env i ps p u g j [] (l4_family_app i ps p j)) /\
  (!env i ps p u g j f fs n a b v.
    l4_raw_index_field env i ps p u g j f a /\ l4_params_expr a ps /\
    l4_raw_sort env g a v /\ l4_level_le v u /\
    l4_raw_index_fields env i ps p u (CONS a g) (SUC j) fs b ==>
    l4_raw_index_fields env i ps p u g j (CONS f fs) (L4Pi n a b))`;;
let l4_raw_index_params_RULES,l4_raw_index_params_INDUCT,l4_raw_index_params_CASES =
  new_inductive_definition
 `(!env i ps p u g fs e. l4_raw_index_fields env i ps p u g 0 fs e ==>
    l4_raw_index_params env i ps p u g [] fs e) /\
  (!env i ps p u g (m:l4_name) d pars fs n a b h v.
    l4_head env a h /\ l4_anon h = l4_anon d /\ l4_params_expr a ps /\
    l4_raw_sort env g a v /\
    l4_raw_index_params env i ps p u (CONS a g) pars fs b ==>
    l4_raw_index_params env i ps p u g (CONS (m,d) pars) fs (L4Pi n a b))`;;

let l4_bridge_index_anchor = new_definition
 `l4_bridge_index_anchor policy canonical <=>
    ?prior i ps pars inds u cs vss large k.
      l4_index_checked policy prior i ps pars inds u cs vss large k canonical`;;
let l4_index_ctor_conversion_bridge = new_definition
 `l4_index_ctor_conversion_bridge policy env raw canonical <=>
    l4_evalid policy env /\ l4_bridge_index_anchor policy canonical /\
    (?prior. env = APPEND canonical prior) /\
    l4_names_distinct (MAP l4_entry_name raw) /\
    ALL (\d. MEM d env) canonical /\ l4_no_nested_claims raw /\
    ALL (\d. l4_is_constructor_kind (l4_entry_tag d) ==>
      ALL (\c. l4_bridge_forward_kind (l4_entry_tag c) ==>
        l4_without_const (l4_entry_name c) (l4_entry_type d)) canonical) raw /\
    ALL2 (l4_bridge_entry policy env) raw canonical`;;
let l4_raw_index_obligations = new_definition
 `!prior i ps pars u cs raw. l4_raw_index_obligations prior i ps pars u cs raw <=>
    ~(raw = []) /\ l4_entry_name (HD raw) = i /\
    (?v. l4_raw_sort prior [] (l4_entry_type (HD raw)) v) /\
    ALL2 (\c d. l4_index_name c = l4_entry_name d /\ l4_index_result c = [] /\
      (?v. l4_raw_sort (CONS (HD raw) prior) [] (l4_entry_type d) v) /\
      l4_raw_index_params (CONS (HD raw) prior) i ps (LENGTH pars) u [] pars
        (l4_index_fields c) (l4_entry_type d)) cs
      (FILTER (\d. l4_is_constructor_kind (l4_entry_tag d)) raw)`;;
let l4_raw_indexed_admitted = new_definition
 `!policy prior raw canonical env. l4_raw_indexed_admitted policy prior raw canonical env <=>
    l4_evalid policy env /\
    (?i ps pars u cs vss.
      l4_index_checked policy prior i ps pars [] u cs vss T F canonical /\
      canonical = l4_index_generated i ps pars [] u cs T F /\
      env = APPEND canonical prior /\ u = L4Succ L4Zero /\
      EX (\c. EX l4_index_reflexive (l4_index_fields c)) cs /\
      l4_raw_index_obligations prior i ps pars u cs raw /\
      l4_index_ctor_conversion_bridge policy env raw canonical)`;;
