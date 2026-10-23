(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Loaded by environment_rules.ml after its entry datatype is defined. *)
let l4_ctor_entries = new_recursive_definition list_RECURSION
 `(l4_ctor_entries i [] j = []) /\
  (l4_ctor_entries i (CONS c cs) j =
    CONS (L4Entry (L4Generated (L4ConstructorRole i j 0 (LENGTH (l4_ctor_fields c)) F))
      (l4_ctor_name c) [] (l4_ctor_type i c) (L4Sort L4Zero))
      (l4_ctor_entries i cs (SUC j)))`;;
let l4_generated = new_definition
 `l4_generated i u cs =
    CONS (L4Entry (L4Generated (L4InductiveRole 0 0 [i] (MAP l4_ctor_name cs) 0
      (EX (\c. EX l4_is_recursive (l4_ctor_fields c)) cs) F F))
      i [] (L4Sort u) (L4Sort L4Zero))
    (APPEND (l4_ctor_entries i cs 0)
      [L4Entry (L4Generated (L4RecursorRole [i] 0 0 1 (LENGTH cs)
        (l4_rec_rules_aux i cs cs 0) F F))
        (l4_rec_name i) [l4_elim_name] (l4_rec_type i cs) (L4Sort L4Zero)])`;;
let l4_anon_kind = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_anon_kind L4DefKind = L4DefKind) /\
  (l4_anon_kind L4ThmKind = L4ThmKind) /\
  (l4_anon_kind L4OpaqueKind = L4OpaqueKind) /\
  (l4_anon_kind L4AxiomKind = L4AxiomKind) /\
  (l4_anon_kind (L4Generated r) = L4Generated (l4_anon_role r))`;;
let l4_anon_entry = new_recursive_definition l4_entry_RECURSION
 `l4_anon_entry (L4Entry k n ps a v) =
    L4Entry (l4_anon_kind k) n ps (l4_anon a) (l4_anon v)`;;
let l4_metadata_matches = new_definition
 `l4_metadata_matches claims generated <=>
    LENGTH claims = LENGTH generated /\
    l4_names_distinct (MAP l4_entry_name claims) /\
    ALL (\d. MEM (l4_anon_entry d) (MAP l4_anon_entry generated)) claims`;;
let l4_metadata_matches_length = prove
 (`!claims generated. l4_metadata_matches claims generated ==> LENGTH claims = LENGTH generated`,
  SIMP_TAC [l4_metadata_matches]);;
let l4_metadata_matches_unique = prove
 (`!claims generated. l4_metadata_matches claims generated ==>
    l4_names_distinct (MAP l4_entry_name claims)`,
  SIMP_TAC [l4_metadata_matches]);;
let l4_metadata_matches_members = prove
 (`!claims generated. l4_metadata_matches claims generated ==>
    ALL (\d. MEM (l4_anon_entry d) (MAP l4_anon_entry generated)) claims`,
  SIMP_TAC [l4_metadata_matches]);;
let l4_regular_kind = new_definition
 `l4_regular_kind k <=> k = L4DefKind \/ k = L4ThmKind \/ k = L4OpaqueKind`;;

let l4_is_constructor_kind = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_is_constructor_kind L4DefKind <=> F) /\
  (l4_is_constructor_kind L4ThmKind <=> F) /\
  (l4_is_constructor_kind L4OpaqueKind <=> F) /\
  (l4_is_constructor_kind L4AxiomKind <=> F) /\
  (l4_is_constructor_kind (L4Generated r) <=> l4_is_constructor_role r)`;;
let l4_no_nested_claims = new_definition
 `l4_no_nested_claims claims <=> ALL (\d.
    l4_is_constructor_kind (l4_entry_tag d) ==> l4_no_nested_aux (l4_entry_type d)) claims`;;
