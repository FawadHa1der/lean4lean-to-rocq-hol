(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_index_header = new_definition
 `l4_index_header i ps pars inds u cs =
    L4Entry (L4Generated (L4InductiveRole (LENGTH pars) (LENGTH inds) [i]
      (MAP l4_index_name cs) 0 (EX (\c. EX l4_index_recursive (l4_index_fields c)) cs)
      (EX (\c. EX l4_index_reflexive (l4_index_fields c)) cs) F))
      i ps (l4_parameter_binders F pars (l4_parameter_binders F inds (L4Sort u))) (L4Sort L4Zero)`;;
let l4_index_ctor_entries = new_recursive_definition list_RECURSION
 `(l4_index_ctor_entries i ps pars [] j = []) /\
  (l4_index_ctor_entries i ps pars (CONS c cs) j =
    CONS (L4Entry (L4Generated (L4ConstructorRole i j (LENGTH pars)
      (LENGTH (l4_index_fields c)) F)) (l4_index_name c) ps
      (l4_index_ctor_type i ps pars c) (L4Sort L4Zero))
      (l4_index_ctor_entries i ps pars cs (SUC j)))`;;
let l4_index_generated = new_definition
 `l4_index_generated i ps pars inds u cs large k =
    CONS (l4_index_header i ps pars inds u cs)
      (APPEND (l4_index_ctor_entries i ps pars cs 0)
        [L4Entry (L4Generated (L4RecursorRole [i] (LENGTH pars) (LENGTH inds) 1 (LENGTH cs)
          (l4_index_rules i ps pars inds cs large cs 0) k F)) (l4_rec_name i)
          (l4_family_rec_params ps large) (l4_index_rec_type i ps pars inds cs large) (L4Sort L4Zero)])`;;
