(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Single-family adaptation of Lean4Lean Inductive/Add.lean at the pinned SHA. *)
needs "hol/family_syntax.ml";;

let l4_index_field_INDUCT,l4_index_field_RECURSION = define_type
 "l4_index_field = L4IndexData l4_expr | L4IndexRecursive (l4_expr list)";;
let l4_index_ctor_INDUCT,l4_index_ctor_RECURSION = define_type
 "l4_index_ctor = L4IndexCtor l4_name (l4_index_field list) (l4_expr list)";;
let l4_index_name = new_recursive_definition l4_index_ctor_RECURSION
 `l4_index_name (L4IndexCtor n fs xs) = n`;;
let l4_index_fields = new_recursive_definition l4_index_ctor_RECURSION
 `l4_index_fields (L4IndexCtor n fs xs) = fs`;;
let l4_index_result = new_recursive_definition l4_index_ctor_RECURSION
 `l4_index_result (L4IndexCtor n fs xs) = xs`;;
let l4_index_recursive = new_recursive_definition l4_index_field_RECURSION
 `(l4_index_recursive (L4IndexData a) <=> F) /\
  (l4_index_recursive (L4IndexRecursive xs) <=> T)`;;
let l4_without_const = new_recursive_definition l4_expr_RECURSION
 `(l4_without_const i (L4BVar j) <=> T) /\
  (l4_without_const i (L4Sort u) <=> T) /\
  (l4_without_const i (L4Const n us) <=> ~(i = n)) /\
  (l4_without_const i (L4App f a) <=> l4_without_const i f /\ l4_without_const i a) /\
  (l4_without_const i (L4Lam n a b) <=> l4_without_const i a /\ l4_without_const i b) /\
  (l4_without_const i (L4Pi n a b) <=> l4_without_const i a /\ l4_without_const i b) /\
  (l4_without_const i (L4Let n a v b) <=>
    l4_without_const i a /\ l4_without_const i v /\ l4_without_const i b) /\
  (l4_without_const i (L4NatLit lit) <=> T)`;;
let l4_index_positive = new_recursive_definition l4_index_field_RECURSION
 `(l4_index_positive i ni (L4IndexData a) <=> l4_without_const i a) /\
  (l4_index_positive i ni (L4IndexRecursive xs) <=>
    LENGTH xs = ni /\ ALL (l4_without_const i) xs)`;;
let l4_index_dom = new_recursive_definition l4_index_field_RECURSION
 `(l4_index_dom i ps p j (L4IndexData a) = a) /\
  (l4_index_dom i ps p j (L4IndexRecursive xs) =
    l4_apps (l4_family_app i ps p j) xs)`;;
let l4_index_binders = new_recursive_definition list_RECURSION
 `(l4_index_binders lam i ps p offset j [] b = b) /\
  (l4_index_binders lam i ps p offset j (CONS f fs) b =
    l4_bind lam (l4_lift (l4_index_dom i ps p j f) offset j)
      (l4_index_binders lam i ps p offset (SUC j) fs b))`;;
let l4_index_telescope = new_recursive_definition list_RECURSION
 `(l4_index_telescope offset j [] b = b) /\
  (l4_index_telescope offset j (CONS (p:l4_name#l4_expr) pars) b =
    l4_bind F (l4_lift (SND p) offset j)
      (l4_index_telescope offset (SUC j) pars b))`;;
let l4_index_ctor_type = new_definition
 `l4_index_ctor_type i ps pars c =
    l4_parameter_binders F pars
      (l4_index_binders F i ps (LENGTH pars) 0 0 (l4_index_fields c)
        (l4_apps (l4_family_app i ps (LENGTH pars) (LENGTH (l4_index_fields c)))
          (l4_index_result c)))`;;
let l4_index_positions = new_recursive_definition list_RECURSION
 `(l4_index_positions [] j = []) /\
  (l4_index_positions (CONS f fs) j =
    if l4_index_recursive f then CONS j (l4_index_positions fs (SUC j))
    else l4_index_positions fs (SUC j))`;;
let l4_index_args = new_recursive_definition l4_index_field_RECURSION
 `(l4_index_args (L4IndexData a) = []) /\
  (l4_index_args (L4IndexRecursive xs) = xs)`;;
let l4_index_move = new_definition
 `l4_index_move offset k pos h a = l4_lift (l4_lift (l4_lift a (k-pos) 0) offset k) h 0`;;
let l4_index_ihs = new_recursive_definition list_RECURSION
 `(l4_index_ihs fs offset k h [] b = b) /\
  (l4_index_ihs fs offset k h (CONS pos positions) b =
    l4_bind F (L4App (l4_apps (L4BVar (offset-1+k+h))
      (MAP (l4_index_move offset k pos h) (l4_index_args (EL pos fs)))) (L4BVar (k-1-pos+h)))
      (l4_index_ihs fs offset k (SUC h) positions b))`;;
let l4_index_minor = new_definition
 `l4_index_minor i ps p c j =
    let fs = l4_index_fields c in
    let k = LENGTH fs in
    let positions = l4_index_positions fs 0 in
    let r = LENGTH positions in
    l4_index_binders F i ps p (SUC j) 0 fs
      (l4_index_ihs fs (SUC j) k 0 positions
        (L4App (l4_apps (L4BVar (j+k+r))
          (MAP (\a. l4_lift (l4_lift a (SUC j) k) r 0) (l4_index_result c)))
          (l4_apps (L4Const (l4_index_name c) (l4_family_levels ps))
            (APPEND (l4_vars p (SUC (j+k+r))) (l4_vars k r)))))`;;
let l4_index_minors = new_recursive_definition list_RECURSION
 `(l4_index_minors lam i ps p [] j b = b) /\
  (l4_index_minors lam i ps p (CONS c cs) j b =
    l4_bind lam (l4_index_minor i ps p c j)
      (l4_index_minors lam i ps p cs (SUC j) b))`;;
let l4_index_motive = new_definition
 `l4_index_motive i ps p inds large =
    l4_index_telescope 0 0 inds
      (L4Pi L4Anonymous (l4_apps (l4_family_app i ps p (LENGTH inds)) (l4_vars (LENGTH inds) 0))
        (L4Sort (l4_family_elim ps large)))`;;
let l4_index_rec_type = new_definition
 `l4_index_rec_type i ps pars inds cs large =
    let p = LENGTH pars in let ni = LENGTH inds in let m = LENGTH cs in
    l4_parameter_binders F pars
      (L4Pi L4Anonymous (l4_index_motive i ps p inds large)
        (l4_index_minors F i ps p cs 0
          (l4_index_telescope (SUC m) 0 inds
            (L4Pi L4Anonymous
              (l4_apps (l4_family_app i ps p (SUC (m+ni))) (l4_vars ni 0))
              (L4App (l4_apps (L4BVar (SUC (m+ni))) (l4_vars ni 1)) (L4BVar 0))))))`;;
let l4_index_rhs = new_definition
 `l4_index_rhs i ps pars inds cs large j c =
    let fs = l4_index_fields c in let k = LENGTH fs in
    let m = LENGTH cs in let p = LENGTH pars in
    let rec = l4_apps (L4Const (l4_rec_name i)
      (l4_family_levels (l4_family_rec_params ps large)))
      (APPEND (l4_vars p (SUC (k+m))) (CONS (L4BVar (k+m)) (l4_vars m k))) in
    l4_parameter_binders T pars
      (L4Lam L4Anonymous (l4_index_motive i ps p inds large)
        (l4_index_minors T i ps p cs 0
          (l4_index_binders T i ps p (SUC m) 0 fs
            (l4_apps (L4BVar (k+m-1-j))
              (APPEND (l4_vars k 0)
                (MAP (\pos. L4App (l4_apps rec
                    (MAP (l4_index_move (SUC m) k pos 0) (l4_index_args (EL pos fs))))
                  (L4BVar (k-1-pos))) (l4_index_positions fs 0)))))))`;;
let l4_index_rules = new_recursive_definition list_RECURSION
 `(l4_index_rules i ps pars inds all large [] j = []) /\
  (l4_index_rules i ps pars inds all large (CONS c cs) j =
    CONS (L4RecRule (l4_index_name c) (LENGTH (l4_index_fields c))
      (l4_index_rhs i ps pars inds all large j c))
      (l4_index_rules i ps pars inds all large cs (SUC j)))`;;
let l4_index_large_fields = new_recursive_definition list_RECURSION
 `(l4_index_large_fields k xs j [] <=> T) /\
  (l4_index_large_fields k xs j (CONS v vs) <=>
    (l4_level_equiv v L4Zero \/ MEM (L4BVar (k-1-j)) xs) /\
    l4_index_large_fields k xs (SUC j) vs)`;;
let l4_index_large = new_definition
 `l4_index_large u (cs:l4_index_ctor list) vss <=> l4_level_nonzero u \/ cs = [] \/
    (LENGTH cs = 1 /\ ALL2 (\c vs. l4_index_large_fields (LENGTH (l4_index_fields c))
      (l4_index_result c) 0 vs) cs vss)`;;
let l4_index_k = new_definition
 `l4_index_k u cs <=> l4_level_equiv u L4Zero /\ LENGTH cs = 1 /\
    ALL (\c. l4_index_fields c = []) cs`;;
