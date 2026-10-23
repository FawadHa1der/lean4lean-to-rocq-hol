(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_mutual_headers = new_definition
 `l4_mutual_headers ps pars u bs =
    let ns = MAP l4_mutual_name bs in let cs = l4_mutual_flat bs 0 in
    MAP (\b. L4Entry (L4Generated (L4InductiveRole (LENGTH pars) 0 ns
      (MAP l4_mutual_ctor_name (l4_mutual_ctors b)) 0
      (EX (\c. EX l4_mutual_recursive (l4_mutual_fields (SND c))) cs)
      (EX (\c. EX l4_mutual_reflexive (l4_mutual_fields (SND c))) cs) F))
      (l4_mutual_name b) ps (l4_parameter_binders F pars (L4Sort u)) (L4Sort L4Zero)) bs`;;
let l4_mutual_ctor_entries_aux = new_recursive_definition list_RECURSION
 `(l4_mutual_ctor_entries_aux i ps pars [] j = []) /\
  (l4_mutual_ctor_entries_aux i ps pars (CONS c cs) j =
    CONS (L4Entry (L4Generated (L4ConstructorRole i j (LENGTH pars)
      (LENGTH (l4_mutual_fields c)) F)) (l4_mutual_ctor_name c) ps
      (l4_mutual_ctor_type i ps pars c) (L4Sort L4Zero))
      (l4_mutual_ctor_entries_aux i ps pars cs (SUC j)))`;;
let l4_mutual_ctor_entries = new_recursive_definition list_RECURSION
 `(l4_mutual_ctor_entries ps pars [] = []) /\
  (l4_mutual_ctor_entries ps pars (CONS b bs) =
    APPEND (l4_mutual_ctor_entries_aux (l4_mutual_name b) ps pars (l4_mutual_ctors b) 0)
      (l4_mutual_ctor_entries ps pars bs))`;;
let l4_mutual_rec_entries = new_recursive_definition list_RECURSION
 `(l4_mutual_rec_entries ns ps pars cs large [] j = []) /\
  (l4_mutual_rec_entries ns ps pars cs large (CONS i is) j =
    CONS (L4Entry (L4Generated (L4RecursorRole ns (LENGTH pars) 0 (LENGTH ns) (LENGTH cs)
      (l4_mutual_rules ns ps pars cs large j cs 0) F F)) (l4_rec_name i)
      (l4_family_rec_params ps large) (l4_mutual_rec_type ns ps pars cs large j) (L4Sort L4Zero))
      (l4_mutual_rec_entries ns ps pars cs large is (SUC j)))`;;
let l4_mutual_generated = new_definition
 `l4_mutual_generated ps pars u bs large =
    APPEND (l4_mutual_headers ps pars u bs)
      (APPEND (l4_mutual_ctor_entries ps pars bs)
        (l4_mutual_rec_entries (MAP l4_mutual_name bs) ps pars
          (l4_mutual_flat bs 0) large (MAP l4_mutual_name bs) 0))`;;
