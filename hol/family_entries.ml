(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Loaded after the environment entry datatype. *)
let l4_family_ctor_entries = new_recursive_definition list_RECURSION
 `(l4_family_ctor_entries i ps pars [] j = []) /\
  (l4_family_ctor_entries i ps pars (CONS c cs) j =
    CONS (L4Entry (L4Generated (L4ConstructorRole i j (LENGTH pars)
      (LENGTH (l4_ctor_fields c)) F)) (l4_ctor_name c) ps
      (l4_family_ctor_type i ps pars c) (L4Sort L4Zero))
      (l4_family_ctor_entries i ps pars cs (SUC j)))`;;
let l4_family_generated = new_definition
 `l4_family_generated i ps pars u cs large k =
    CONS (L4Entry (L4Generated (L4InductiveRole (LENGTH pars) 0 [i] (MAP l4_ctor_name cs) 0
      (EX (\c. EX l4_is_recursive (l4_ctor_fields c)) cs) F F))
      i ps (l4_parameter_binders F pars (L4Sort u)) (L4Sort L4Zero))
    (APPEND (l4_family_ctor_entries i ps pars cs 0)
      [L4Entry (L4Generated (L4RecursorRole [i] (LENGTH pars) 0 1 (LENGTH cs)
        (l4_family_rules i ps pars cs large cs 0) k F))
        (l4_rec_name i) (l4_family_rec_params ps large)
        (l4_family_rec_type i ps pars cs large) (L4Sort L4Zero)])`;;
let l4_family_primitive = new_definition
 `l4_family_primitive i (ps:l4_name list) (pars:(l4_name#l4_expr)list) u cs <=> l4_primitive_block i u cs /\
    ((i = l4_nat_name \/ i = l4_bool_name) ==> ps = [] /\ pars = [])`;;
