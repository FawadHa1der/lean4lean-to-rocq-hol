(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_mindex_headers = new_definition
 `l4_mindex_headers ps pars u bs =
    let ns = MAP l4_mindex_name bs in let cs = l4_mindex_flat bs 0 in
    MAP (\b. L4Entry (L4Generated (L4InductiveRole (LENGTH pars)
      (LENGTH (l4_mindex_indices b)) ns (MAP l4_mindex_ctor_name (l4_mindex_ctors b)) 0
      (EX (\c. EX l4_mindex_recursive (l4_mindex_fields (SND c))) cs)
      (EX (\c. EX l4_mindex_reflexive (l4_mindex_fields (SND c))) cs) F))
      (l4_mindex_name b) ps (l4_parameter_binders F pars
        (l4_parameter_binders F (l4_mindex_indices b) (L4Sort u))) (L4Sort L4Zero)) bs`;;
let l4_mindex_ctor_entries_aux = new_recursive_definition list_RECURSION
 `(l4_mindex_ctor_entries_aux i ps pars [] j = []) /\
  (l4_mindex_ctor_entries_aux i ps pars (CONS c cs) j =
    CONS (L4Entry (L4Generated (L4ConstructorRole i j (LENGTH pars)
      (LENGTH (l4_mindex_fields c)) F)) (l4_mindex_ctor_name c) ps
      (l4_mindex_ctor_type i ps pars c) (L4Sort L4Zero))
      (l4_mindex_ctor_entries_aux i ps pars cs (SUC j)))`;;
let l4_mindex_ctor_entries = new_recursive_definition list_RECURSION
 `(l4_mindex_ctor_entries ps pars [] = []) /\
  (l4_mindex_ctor_entries ps pars (CONS b bs) =
    APPEND (l4_mindex_ctor_entries_aux (l4_mindex_name b) ps pars (l4_mindex_ctors b) 0)
      (l4_mindex_ctor_entries ps pars bs))`;;
let l4_mindex_rec_entries = new_recursive_definition list_RECURSION
 `(l4_mindex_rec_entries bs ps pars cs large [] j = []) /\
  (l4_mindex_rec_entries bs ps pars cs large (CONS b rest) j =
    CONS (L4Entry (L4Generated (L4RecursorRole (MAP l4_mindex_name bs) (LENGTH pars)
      (LENGTH (l4_mindex_indices b)) (LENGTH bs) (LENGTH cs)
      (l4_mindex_rules bs ps pars cs large j cs 0) F F)) (l4_rec_name (l4_mindex_name b))
      (l4_family_rec_params ps large) (l4_mindex_rec_type bs ps pars cs large j) (L4Sort L4Zero))
      (l4_mindex_rec_entries bs ps pars cs large rest (SUC j)))`;;
let l4_mindex_generated = new_definition
 `l4_mindex_generated ps pars u bs large = APPEND (l4_mindex_headers ps pars u bs)
    (APPEND (l4_mindex_ctor_entries ps pars bs)
      (l4_mindex_rec_entries bs ps pars (l4_mindex_flat bs 0) large bs 0))`;;
