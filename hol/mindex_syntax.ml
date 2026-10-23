(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Safe indexed mutual fragment of Lean4Lean Inductive/Add.lean,
   8223d223ed98661882e95d9d6a7126df7097cd76. *)
needs "hol/mutual_syntax.ml";;
let l4_mindex_field_INDUCT,l4_mindex_field_RECURSION = define_type
 "l4_mindex_field = L4MIndexData l4_expr |
    L4MIndexRec l4_name (l4_expr list) (l4_expr list)";;
let l4_mindex_ctor_INDUCT,l4_mindex_ctor_RECURSION = define_type
 "l4_mindex_ctor = L4MIndexCtor l4_name (l4_mindex_field list) (l4_expr list)";;
let l4_mindex_family_INDUCT,l4_mindex_family_RECURSION = define_type
 "l4_mindex_family = L4MIndexFamily l4_name ((l4_name#l4_expr)list) (l4_mindex_ctor list)";;
let l4_mindex_name = new_recursive_definition l4_mindex_family_RECURSION
 `l4_mindex_name (L4MIndexFamily n inds cs) = n`;;
let l4_mindex_indices = new_recursive_definition l4_mindex_family_RECURSION
 `l4_mindex_indices (L4MIndexFamily n inds cs) = inds`;;
let l4_mindex_ctors = new_recursive_definition l4_mindex_family_RECURSION
 `l4_mindex_ctors (L4MIndexFamily n inds cs) = cs`;;
let l4_mindex_all_indices = new_recursive_definition list_RECURSION
 `(l4_mindex_all_indices [] = []) /\
  (l4_mindex_all_indices (CONS b bs) = APPEND (l4_mindex_indices b) (l4_mindex_all_indices bs))`;;
let l4_mindex_ctor_name = new_recursive_definition l4_mindex_ctor_RECURSION
 `l4_mindex_ctor_name (L4MIndexCtor n fs xs) = n`;;
let l4_mindex_fields = new_recursive_definition l4_mindex_ctor_RECURSION
 `l4_mindex_fields (L4MIndexCtor n fs xs) = fs`;;
let l4_mindex_result = new_recursive_definition l4_mindex_ctor_RECURSION
 `l4_mindex_result (L4MIndexCtor n fs xs) = xs`;;
let l4_mindex_recursive = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_recursive (L4MIndexData a) <=> F) /\
  (l4_mindex_recursive (L4MIndexRec i ds xs) <=> T)`;;
let l4_mindex_reflexive = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_reflexive (L4MIndexData a) <=> F) /\
  (l4_mindex_reflexive (L4MIndexRec i ds xs) <=> ~(ds = []))`;;
let l4_mindex_target = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_target (L4MIndexData a) = L4Anonymous) /\
  (l4_mindex_target (L4MIndexRec i ds xs) = i)`;;
let l4_mindex_domains = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_domains (L4MIndexData a) = []) /\
  (l4_mindex_domains (L4MIndexRec i ds xs) = ds)`;;
let l4_mindex_args = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_args (L4MIndexData a) = []) /\
  (l4_mindex_args (L4MIndexRec i ds xs) = xs)`;;
let l4_mindex_arity = new_definition
 `l4_mindex_arity bs i = LENGTH (l4_mindex_indices (EL
    (l4_mutual_pos i (MAP l4_mindex_name bs)) bs))`;;
let l4_mindex_positive = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_positive bs (L4MIndexData a) <=> l4_mutual_without (MAP l4_mindex_name bs) a) /\
  (l4_mindex_positive bs (L4MIndexRec i ds xs) <=>
    MEM i (MAP l4_mindex_name bs) /\ LENGTH xs = l4_mindex_arity bs i /\
    ALL (l4_mutual_without (MAP l4_mindex_name bs)) (APPEND ds xs))`;;
let l4_mindex_flat = new_recursive_definition list_RECURSION
 `(l4_mindex_flat [] j = []) /\
  (l4_mindex_flat (CONS b bs) j = APPEND (MAP (\c. (j,c)) (l4_mindex_ctors b))
    (l4_mindex_flat bs (SUC j)))`;;
let l4_mindex_dom = new_recursive_definition l4_mindex_field_RECURSION
 `(l4_mindex_dom ps p j (L4MIndexData a) = a) /\
  (l4_mindex_dom ps p j (L4MIndexRec i ds xs) =
    l4_index_pi ds (l4_apps (l4_family_app i ps p (j + LENGTH ds)) xs))`;;
let l4_mindex_binders = new_recursive_definition list_RECURSION
 `(l4_mindex_binders lam ps p offset j [] b = b) /\
  (l4_mindex_binders lam ps p offset j (CONS f fs) b =
    l4_bind lam (l4_lift (l4_mindex_dom ps p j f) offset j)
      (l4_mindex_binders lam ps p offset (SUC j) fs b))`;;
let l4_mindex_ctor_type = new_definition
 `l4_mindex_ctor_type i ps pars c = l4_parameter_binders F pars
    (l4_mindex_binders F ps (LENGTH pars) 0 0 (l4_mindex_fields c)
      (l4_apps (l4_family_app i ps (LENGTH pars) (LENGTH (l4_mindex_fields c)))
        (l4_mindex_result c)))`;;
let l4_mindex_positions = new_recursive_definition list_RECURSION
 `(l4_mindex_positions [] j = []) /\
  (l4_mindex_positions (CONS f fs) j = if l4_mindex_recursive f
    then CONS j (l4_mindex_positions fs (SUC j)) else l4_mindex_positions fs (SUC j))`;;
let l4_mindex_motive = new_definition
 `l4_mindex_motive b ps p large j =
    let inds = l4_mindex_indices b in let ni = LENGTH inds in
    l4_index_telescope j 0 inds
      (L4Pi L4Anonymous (l4_apps (l4_family_app (l4_mindex_name b) ps p (j+ni)) (l4_vars ni 0))
        (L4Sort (l4_family_elim ps large)))`;;
let l4_mindex_motives = new_recursive_definition list_RECURSION
 `(l4_mindex_motives lam ps p large [] j b = b) /\
  (l4_mindex_motives lam ps p large (CONS f fs) j b =
    l4_bind lam (l4_mindex_motive f ps p large j)
      (l4_mindex_motives lam ps p large fs (SUC j) b))`;;
let l4_mindex_ih = new_definition
 `l4_mindex_ih ns fs offset k pos h =
    let f = EL pos fs in let ds = l4_mindex_domains f in let n = LENGTH ds in
    l4_index_funbinders F ds offset k pos h 0
      (L4App (l4_apps (L4BVar (offset-1-l4_mutual_pos (l4_mindex_target f) ns+k+h+n))
        (MAP (l4_index_under offset k pos h n) (l4_mindex_args f)))
        (l4_apps (L4BVar (k-1-pos+h+n)) (l4_vars n 0)))`;;
let l4_mindex_ihs = new_recursive_definition list_RECURSION
 `(l4_mindex_ihs ns fs offset k h [] b = b) /\
  (l4_mindex_ihs ns fs offset k h (CONS pos positions) b =
    l4_bind F (l4_mindex_ih ns fs offset k pos h)
      (l4_mindex_ihs ns fs offset k (SUC h) positions b))`;;
let l4_mindex_minor = new_definition
 `l4_mindex_minor ns ps p owner c j =
    let fs = l4_mindex_fields c in let k = LENGTH fs in
    let positions = l4_mindex_positions fs 0 in let r = LENGTH positions in
    let offset = LENGTH ns + j in
    l4_mindex_binders F ps p offset 0 fs
      (l4_mindex_ihs ns fs offset k 0 positions
        (L4App (l4_apps (L4BVar (offset-1-owner+k+r))
          (MAP (\a. l4_lift (l4_lift a offset k) r 0) (l4_mindex_result c)))
          (l4_apps (L4Const (l4_mindex_ctor_name c) (l4_family_levels ps))
            (APPEND (l4_vars p (offset+k+r)) (l4_vars k r)))))`;;
let l4_mindex_minors = new_recursive_definition list_RECURSION
 `(l4_mindex_minors lam ns ps p [] j b = b) /\
  (l4_mindex_minors lam ns ps p (CONS c cs) j b =
    l4_bind lam (l4_mindex_minor ns ps p (FST c) (SND c) j)
      (l4_mindex_minors lam ns ps p cs (SUC j) b))`;;
let l4_mindex_rec_type = new_definition
 `l4_mindex_rec_type bs ps pars cs large owner =
    let ns = MAP l4_mindex_name bs in let p = LENGTH pars in
    let inds = l4_mindex_indices (EL owner bs) in let ni = LENGTH inds in
    let q = LENGTH ns in let m = LENGTH cs in
    l4_parameter_binders F pars (l4_mindex_motives F ps p large bs 0
      (l4_mindex_minors F ns ps p cs 0 (l4_index_telescope (q+m) 0 inds
        (L4Pi L4Anonymous (l4_apps (l4_family_app (EL owner ns) ps p (q+m+ni)) (l4_vars ni 0))
          (L4App (l4_apps (L4BVar ((q+m+ni)-owner)) (l4_vars ni 1)) (L4BVar 0))))))`;;
let l4_mindex_call = new_definition
 `l4_mindex_call ns ps p large fs m k pos =
    let f = EL pos fs in let ds = l4_mindex_domains f in let n = LENGTH ds in
    let q = LENGTH ns in
    let rec = l4_apps (L4Const (l4_rec_name (l4_mindex_target f))
      (l4_family_levels (l4_family_rec_params ps large)))
      (APPEND (l4_vars p (k+m+q)) (APPEND (l4_vars q (k+m)) (l4_vars m k))) in
    l4_index_funbinders T ds (q+m) k pos 0 0
      (L4App (l4_apps (l4_lift rec n 0)
        (MAP (l4_index_under (q+m) k pos 0 n) (l4_mindex_args f)))
        (l4_apps (L4BVar (k-1-pos+n)) (l4_vars n 0)))`;;
let l4_mindex_rhs = new_definition
 `l4_mindex_rhs bs ps pars cs large j c =
    let ns = MAP l4_mindex_name bs in
    let fs = l4_mindex_fields c in let k = LENGTH fs in
    let m = LENGTH cs in let p = LENGTH pars in let q = LENGTH ns in
    l4_parameter_binders T pars (l4_mindex_motives T ps p large bs 0
      (l4_mindex_minors T ns ps p cs 0 (l4_mindex_binders T ps p (q+m) 0 fs
        (l4_apps (L4BVar (k+m-1-j)) (APPEND (l4_vars k 0)
          (MAP (l4_mindex_call ns ps p large fs m k) (l4_mindex_positions fs 0)))))))`;;
let l4_mindex_rules = new_recursive_definition list_RECURSION
 `(l4_mindex_rules bs ps pars all large owner [] j = []) /\
  (l4_mindex_rules bs ps pars all large owner (CONS c cs) j =
    if FST c = owner then CONS
      (L4RecRule (l4_mindex_ctor_name (SND c)) (LENGTH (l4_mindex_fields (SND c)))
        (l4_mindex_rhs bs ps pars all large j (SND c)))
      (l4_mindex_rules bs ps pars all large owner cs (SUC j))
    else l4_mindex_rules bs ps pars all large owner cs (SUC j))`;;
