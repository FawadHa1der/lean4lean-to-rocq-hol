(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Nonnested, nonindexed mutual fragment of Lean4Lean Inductive/Add.lean,
   pinned at 8223d223ed98661882e95d9d6a7126df7097cd76.
   The shared parameter telescope is implicit in recursive applications. *)
needs "hol/indexed_syntax.ml";;

let l4_mutual_field_INDUCT,l4_mutual_field_RECURSION = define_type
 "l4_mutual_field = L4MutualData l4_expr | L4MutualRec l4_name (l4_expr list)";;
let l4_mutual_ctor_INDUCT,l4_mutual_ctor_RECURSION = define_type
 "l4_mutual_ctor = L4MutualCtor l4_name (l4_mutual_field list)";;
let l4_mutual_family_INDUCT,l4_mutual_family_RECURSION = define_type
 "l4_mutual_family = L4MutualFamily l4_name (l4_mutual_ctor list)";;
let l4_mutual_name = new_recursive_definition l4_mutual_family_RECURSION
 `l4_mutual_name (L4MutualFamily n cs) = n`;;
let l4_mutual_ctors = new_recursive_definition l4_mutual_family_RECURSION
 `l4_mutual_ctors (L4MutualFamily n cs) = cs`;;
let l4_mutual_ctor_name = new_recursive_definition l4_mutual_ctor_RECURSION
 `l4_mutual_ctor_name (L4MutualCtor n fs) = n`;;
let l4_mutual_fields = new_recursive_definition l4_mutual_ctor_RECURSION
 `l4_mutual_fields (L4MutualCtor n fs) = fs`;;
let l4_mutual_recursive = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_recursive (L4MutualData a) <=> F) /\
  (l4_mutual_recursive (L4MutualRec i ds) <=> T)`;;
let l4_mutual_reflexive = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_reflexive (L4MutualData a) <=> F) /\
  (l4_mutual_reflexive (L4MutualRec i ds) <=> ~(ds = []))`;;
let l4_mutual_target = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_target (L4MutualData a) = L4Anonymous) /\
  (l4_mutual_target (L4MutualRec i ds) = i)`;;
let l4_mutual_domains = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_domains (L4MutualData a) = []) /\
  (l4_mutual_domains (L4MutualRec i ds) = ds)`;;
let l4_mutual_without = new_definition
 `l4_mutual_without ns a <=> ALL (\i. l4_without_const i a) ns`;;
let l4_mutual_positive = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_positive ns (L4MutualData a) <=> l4_mutual_without ns a) /\
  (l4_mutual_positive ns (L4MutualRec i ds) <=>
    MEM i ns /\ ALL (l4_mutual_without ns) ds)`;;
let l4_mutual_pos = new_recursive_definition list_RECURSION
 `(l4_mutual_pos i [] = 0) /\
  (l4_mutual_pos i (CONS n ns) = if i = n then 0 else SUC (l4_mutual_pos i ns))`;;
let l4_mutual_flat = new_recursive_definition list_RECURSION
 `(l4_mutual_flat [] j = []) /\
  (l4_mutual_flat (CONS b bs) j = APPEND (MAP (\c. (j,c)) (l4_mutual_ctors b))
    (l4_mutual_flat bs (SUC j)))`;;
let l4_mutual_dom = new_recursive_definition l4_mutual_field_RECURSION
 `(l4_mutual_dom ps p j (L4MutualData a) = a) /\
  (l4_mutual_dom ps p j (L4MutualRec i ds) =
    l4_index_pi ds (l4_family_app i ps p (j + LENGTH ds)))`;;
let l4_mutual_binders = new_recursive_definition list_RECURSION
 `(l4_mutual_binders lam ps p offset j [] b = b) /\
  (l4_mutual_binders lam ps p offset j (CONS f fs) b =
    l4_bind lam (l4_lift (l4_mutual_dom ps p j f) offset j)
      (l4_mutual_binders lam ps p offset (SUC j) fs b))`;;
let l4_mutual_ctor_type = new_definition
 `l4_mutual_ctor_type i ps pars c = l4_parameter_binders F pars
    (l4_mutual_binders F ps (LENGTH pars) 0 0 (l4_mutual_fields c)
      (l4_family_app i ps (LENGTH pars) (LENGTH (l4_mutual_fields c))))`;;
let l4_mutual_positions = new_recursive_definition list_RECURSION
 `(l4_mutual_positions [] j = []) /\
  (l4_mutual_positions (CONS f fs) j = if l4_mutual_recursive f
    then CONS j (l4_mutual_positions fs (SUC j)) else l4_mutual_positions fs (SUC j))`;;
let l4_mutual_motive = new_definition
 `l4_mutual_motive i ps p large j =
    L4Pi L4Anonymous (l4_family_app i ps p j) (L4Sort (l4_family_elim ps large))`;;
let l4_mutual_motives = new_recursive_definition list_RECURSION
 `(l4_mutual_motives lam ps p large [] j b = b) /\
  (l4_mutual_motives lam ps p large (CONS i ns) j b =
    l4_bind lam (l4_mutual_motive i ps p large j)
      (l4_mutual_motives lam ps p large ns (SUC j) b))`;;
let l4_mutual_ih = new_definition
 `l4_mutual_ih ns fs offset k pos h =
    let f = EL pos fs in let ds = l4_mutual_domains f in let n = LENGTH ds in
    l4_index_funbinders F ds offset k pos h 0
      (L4App (L4BVar (offset-1-l4_mutual_pos (l4_mutual_target f) ns+k+h+n))
        (l4_apps (L4BVar (k-1-pos+h+n)) (l4_vars n 0)))`;;
let l4_mutual_ihs = new_recursive_definition list_RECURSION
 `(l4_mutual_ihs ns fs offset k h [] b = b) /\
  (l4_mutual_ihs ns fs offset k h (CONS pos positions) b =
    l4_bind F (l4_mutual_ih ns fs offset k pos h)
      (l4_mutual_ihs ns fs offset k (SUC h) positions b))`;;
let l4_mutual_minor = new_definition
 `l4_mutual_minor ns ps p owner c j =
    let fs = l4_mutual_fields c in let k = LENGTH fs in
    let positions = l4_mutual_positions fs 0 in let r = LENGTH positions in
    let offset = LENGTH ns + j in
    l4_mutual_binders F ps p offset 0 fs
      (l4_mutual_ihs ns fs offset k 0 positions
        (L4App (L4BVar (offset-1-owner+k+r))
          (l4_apps (L4Const (l4_mutual_ctor_name c) (l4_family_levels ps))
            (APPEND (l4_vars p (offset+k+r)) (l4_vars k r)))))`;;
let l4_mutual_minors = new_recursive_definition list_RECURSION
 `(l4_mutual_minors lam ns ps p [] j b = b) /\
  (l4_mutual_minors lam ns ps p (CONS c cs) j b =
    l4_bind lam (l4_mutual_minor ns ps p (FST c) (SND c) j)
      (l4_mutual_minors lam ns ps p cs (SUC j) b))`;;
let l4_mutual_rec_type = new_definition
 `l4_mutual_rec_type ns ps pars cs large owner =
    let p = LENGTH pars in let q = LENGTH ns in let m = LENGTH cs in
    l4_parameter_binders F pars
      (l4_mutual_motives F ps p large ns 0
        (l4_mutual_minors F ns ps p cs 0
          (L4Pi L4Anonymous (l4_family_app (EL owner ns) ps p (q+m))
            (L4App (L4BVar ((q+m)-owner)) (L4BVar 0)))))`;;
let l4_mutual_call = new_definition
 `l4_mutual_call ns ps p large fs m k pos =
    let f = EL pos fs in let ds = l4_mutual_domains f in let n = LENGTH ds in
    let q = LENGTH ns in
    let rec = l4_apps (L4Const (l4_rec_name (l4_mutual_target f))
      (l4_family_levels (l4_family_rec_params ps large)))
      (APPEND (l4_vars p (k+m+q)) (APPEND (l4_vars q (k+m)) (l4_vars m k))) in
    l4_index_funbinders T ds (q+m) k pos 0 0
      (L4App (l4_lift rec n 0) (l4_apps (L4BVar (k-1-pos+n)) (l4_vars n 0)))`;;
let l4_mutual_rhs = new_definition
 `l4_mutual_rhs ns ps pars cs large j c =
    let fs = l4_mutual_fields c in let k = LENGTH fs in
    let m = LENGTH cs in let p = LENGTH pars in let q = LENGTH ns in
    l4_parameter_binders T pars
      (l4_mutual_motives T ps p large ns 0
        (l4_mutual_minors T ns ps p cs 0
          (l4_mutual_binders T ps p (q+m) 0 fs
            (l4_apps (L4BVar (k+m-1-j))
              (APPEND (l4_vars k 0)
                (MAP (l4_mutual_call ns ps p large fs m k) (l4_mutual_positions fs 0)))))))`;;
let l4_mutual_rules = new_recursive_definition list_RECURSION
 `(l4_mutual_rules ns ps pars all large owner [] j = []) /\
  (l4_mutual_rules ns ps pars all large owner (CONS c cs) j =
    if FST c = owner then CONS
      (L4RecRule (l4_mutual_ctor_name (SND c)) (LENGTH (l4_mutual_fields (SND c)))
        (l4_mutual_rhs ns ps pars all large j (SND c)))
      (l4_mutual_rules ns ps pars all large owner cs (SUC j))
    else l4_mutual_rules ns ps pars all large owner cs (SUC j))`;;
