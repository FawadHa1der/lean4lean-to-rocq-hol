(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/inductive_syntax.ml";;

let l4_decimal_aux = new_recursive_definition num_RECURSION
 `(l4_decimal_aux 0 n = []) /\
  (l4_decimal_aux (SUC fuel) n = if n < 10 then [48+n]
    else APPEND (l4_decimal_aux fuel (n DIV 10)) [48 + n MOD 10])`;;
let l4_univ_candidate = new_definition
 `l4_univ_candidate j = if j = 0 then l4_elim_name
    else L4String L4Anonymous (APPEND [117;95] (l4_decimal_aux (SUC j) j))`;;
let l4_fresh_univ_aux = new_recursive_definition num_RECURSION
 `(l4_fresh_univ_aux 0 ps j = l4_univ_candidate j) /\
  (l4_fresh_univ_aux (SUC fuel) ps j =
    if MEM (l4_univ_candidate j) ps then l4_fresh_univ_aux fuel ps (SUC j)
    else l4_univ_candidate j)`;;
let l4_fresh_univ = new_definition
 `l4_fresh_univ ps = l4_fresh_univ_aux (SUC (LENGTH ps)) ps 0`;;
let l4_family_levels = new_definition `l4_family_levels ps = MAP L4Param ps`;;
let l4_family_rec_params = new_definition
 `l4_family_rec_params ps large = if large then CONS (l4_fresh_univ ps) ps else ps`;;
let l4_family_elim = new_definition
 `l4_family_elim ps large = if large then L4Param (l4_fresh_univ ps) else L4Zero`;;
let l4_parameter_binders = new_recursive_definition list_RECURSION
 `(l4_parameter_binders lam [] b = b) /\
  (l4_parameter_binders lam (CONS (p:l4_name#l4_expr) pars) b =
    l4_bind lam (SND p) (l4_parameter_binders lam pars b))`;;
let l4_family_app = new_definition
 `l4_family_app i ps p offset = l4_apps (L4Const i (l4_family_levels ps)) (l4_vars p offset)`;;
let l4_family_dom = new_recursive_definition l4_field_RECURSION
 `(l4_family_dom i ps p offset (L4Data a) = l4_lift a offset 0) /\
  (l4_family_dom i ps p offset L4Recursive = l4_family_app i ps p offset)`;;
let l4_family_binders = new_recursive_definition list_RECURSION
 `(l4_family_binders lam i ps p offset [] b = b) /\
  (l4_family_binders lam i ps p offset (CONS f fs) b =
    l4_bind lam (l4_family_dom i ps p offset f)
      (l4_family_binders lam i ps p (SUC offset) fs b))`;;
let l4_family_ctor_type = new_definition
 `l4_family_ctor_type i ps pars c =
    l4_parameter_binders F pars
      (l4_family_binders F i ps (LENGTH pars) 0 (l4_ctor_fields c)
        (l4_family_app i ps (LENGTH pars) (LENGTH (l4_ctor_fields c))))`;;
let l4_family_minor = new_definition
 `l4_family_minor i ps p c j =
    let fs = l4_ctor_fields c in
    let k = LENGTH fs in
    let positions = l4_rec_positions fs 0 in
    let r = LENGTH positions in
    l4_family_binders F i ps p (SUC j) fs
      (l4_ih_binders positions (j+k) k 0
        (L4App (L4BVar (j+k+r))
          (l4_apps (L4Const (l4_ctor_name c) (l4_family_levels ps))
            (APPEND (l4_vars p (SUC (j+k+r))) (l4_vars k r)))))`;;
let l4_family_minors = new_recursive_definition list_RECURSION
 `(l4_family_minors lam i ps p [] j b = b) /\
  (l4_family_minors lam i ps p (CONS c cs) j b =
    l4_bind lam (l4_family_minor i ps p c j)
      (l4_family_minors lam i ps p cs (SUC j) b))`;;
let l4_family_motive = new_definition
 `l4_family_motive i ps p large =
    L4Pi L4Anonymous (l4_family_app i ps p 0) (L4Sort (l4_family_elim ps large))`;;
let l4_family_rec_type = new_definition
 `l4_family_rec_type i ps pars cs large =
    l4_parameter_binders F pars
      (L4Pi L4Anonymous (l4_family_motive i ps (LENGTH pars) large)
        (l4_family_minors F i ps (LENGTH pars) cs 0
          (L4Pi L4Anonymous (l4_family_app i ps (LENGTH pars) (SUC (LENGTH cs)))
            (L4App (L4BVar (SUC (LENGTH cs))) (L4BVar 0)))))`;;
let l4_family_rhs = new_definition
 `l4_family_rhs i ps pars cs large j c =
    let fs = l4_ctor_fields c in
    let k = LENGTH fs in
    let m = LENGTH cs in
    let p = LENGTH pars in
    let rec = l4_apps (L4Const (l4_rec_name i)
      (l4_family_levels (l4_family_rec_params ps large)))
      (APPEND (l4_vars p (SUC (k+m))) (CONS (L4BVar (k+m)) (l4_vars m k))) in
    l4_parameter_binders T pars
      (L4Lam L4Anonymous (l4_family_motive i ps p large)
        (l4_family_minors T i ps p cs 0
          (l4_family_binders T i ps p (SUC m) fs
            (l4_apps (L4BVar (k+m-1-j))
              (APPEND (l4_vars k 0)
                (MAP (\pos. L4App rec (L4BVar (k-1-pos))) (l4_rec_positions fs 0)))))))`;;
let l4_family_rules = new_recursive_definition list_RECURSION
 `(l4_family_rules i ps pars all large [] j = []) /\
  (l4_family_rules i ps pars all large (CONS c cs) j =
    CONS (L4RecRule (l4_ctor_name c) (LENGTH (l4_ctor_fields c))
      (l4_family_rhs i ps pars all large j c))
      (l4_family_rules i ps pars all large cs (SUC j)))`;;
let l4_family_large = new_definition
 `l4_family_large u (cs:l4_ctor_spec list) vss <=> l4_level_nonzero u \/ cs = [] \/
    (LENGTH cs = 1 /\ ALL (ALL (\v. l4_level_equiv v L4Zero)) vss)`;;
let l4_family_k = new_definition
 `l4_family_k u cs <=> l4_level_equiv u L4Zero /\
    LENGTH cs = 1 /\ ALL (\c. l4_ctor_fields c = []) cs`;;
