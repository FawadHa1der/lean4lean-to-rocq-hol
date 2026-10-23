(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/declarations.ml";;

let l4_field_INDUCT,l4_field_RECURSION = define_type
 "l4_field = L4Data l4_expr | L4Recursive";;
let l4_ctor_spec_INDUCT,l4_ctor_spec_RECURSION = define_type
 "l4_ctor_spec = L4CtorSpec l4_name (l4_field list)";;
let l4_recrule_INDUCT,l4_recrule_RECURSION = define_type
 "l4_recrule = L4RecRule l4_name num l4_expr";;
let l4_role_INDUCT,l4_role_RECURSION = define_type
 "l4_role =
    L4InductiveRole num num (l4_name list) (l4_name list) num bool bool bool
  | L4ConstructorRole l4_name num num num bool
  | L4RecursorRole (l4_name list) num num num num (l4_recrule list) bool bool";;

let l4_ctor_name = new_recursive_definition l4_ctor_spec_RECURSION
 `l4_ctor_name (L4CtorSpec n fs) = n`;;
let l4_ctor_fields = new_recursive_definition l4_ctor_spec_RECURSION
 `l4_ctor_fields (L4CtorSpec n fs) = fs`;;
let l4_field_type = new_recursive_definition l4_field_RECURSION
 `(l4_field_type i (L4Data a) = a) /\
  (l4_field_type i L4Recursive = L4Const i [])`;;
let l4_is_recursive = new_recursive_definition l4_field_RECURSION
 `(l4_is_recursive (L4Data a) = F) /\ (l4_is_recursive L4Recursive = T)`;;
let l4_rec_name = new_definition `l4_rec_name i = L4String i [114;101;99]`;;
let l4_elim_name = new_definition `l4_elim_name = L4String L4Anonymous [117]`;;
let l4_apps = new_recursive_definition list_RECURSION
 `(l4_apps f [] = f) /\
  (l4_apps f (CONS a args) = l4_apps (L4App f a) args)`;;
let l4_vars = new_recursive_definition num_RECURSION
 `(l4_vars 0 k = []) /\
  (l4_vars (SUC n) k = CONS (L4BVar (k+n)) (l4_vars n k))`;;
let l4_bind = new_definition
 `l4_bind lam a b = if lam then L4Lam L4Anonymous a b else L4Pi L4Anonymous a b`;;
let l4_field_binders = new_recursive_definition list_RECURSION
 `(l4_field_binders lam i [] b = b) /\
  (l4_field_binders lam i (CONS f fs) b =
    l4_bind lam (l4_field_type i f) (l4_field_binders lam i fs b))`;;
let l4_rec_positions = new_recursive_definition list_RECURSION
 `(l4_rec_positions [] k = []) /\
  (l4_rec_positions (CONS f fs) k =
    if l4_is_recursive f then CONS k (l4_rec_positions fs (SUC k))
    else l4_rec_positions fs (SUC k))`;;
let l4_ih_binders = new_recursive_definition list_RECURSION
 `(l4_ih_binders [] m k j b = b) /\
  (l4_ih_binders (CONS p ps) m k j b =
    L4Pi L4Anonymous (L4App (L4BVar (m+j)) (L4BVar (k-1-p+j)))
      (l4_ih_binders ps m k (SUC j) b))`;;
let l4_ctor_type = new_definition
 `l4_ctor_type i c = l4_field_binders F i (l4_ctor_fields c) (L4Const i [])`;;
let l4_minor_type = new_definition
 `l4_minor_type i c j =
    let fs = l4_ctor_fields c in
    let k = LENGTH fs in
    let ps = l4_rec_positions fs 0 in
    let r = LENGTH ps in
    l4_field_binders F i fs
      (l4_ih_binders ps (j+k) k 0
        (L4App (L4BVar (j+k+r))
          (l4_apps (L4Const (l4_ctor_name c) []) (l4_vars k r))))`;;
let l4_minor_binders = new_recursive_definition list_RECURSION
 `(l4_minor_binders lam i [] j b = b) /\
  (l4_minor_binders lam i (CONS c cs) j b =
    l4_bind lam (l4_minor_type i c j) (l4_minor_binders lam i cs (SUC j) b))`;;
let l4_motive_type = new_definition
 `l4_motive_type i = L4Pi L4Anonymous (L4Const i []) (L4Sort (L4Param l4_elim_name))`;;
let l4_rec_type = new_definition
 `l4_rec_type i cs = L4Pi L4Anonymous (l4_motive_type i)
    (l4_minor_binders F i cs 0
      (L4Pi L4Anonymous (L4Const i [])
        (L4App (L4BVar (SUC (LENGTH cs))) (L4BVar 0))))`;;
let l4_rec_rhs = new_definition
 `l4_rec_rhs i cs j c =
    let fs = l4_ctor_fields c in
    let k = LENGTH fs in
    let m = LENGTH cs in
    let rec = l4_apps (L4Const (l4_rec_name i) [L4Param l4_elim_name])
      (CONS (L4BVar (k+m)) (l4_vars m k)) in
    L4Lam L4Anonymous (l4_motive_type i)
      (l4_minor_binders T i cs 0
        (l4_field_binders T i fs
          (l4_apps (L4BVar (k+m-1-j))
            (APPEND (l4_vars k 0)
              (MAP (\p. L4App rec (L4BVar (k-1-p))) (l4_rec_positions fs 0))))))`;;
let l4_rec_rules_aux = new_recursive_definition list_RECURSION
 `(l4_rec_rules_aux i all [] j = []) /\
  (l4_rec_rules_aux i all (CONS c cs) j =
    CONS (L4RecRule (l4_ctor_name c) (LENGTH (l4_ctor_fields c)) (l4_rec_rhs i all j c))
      (l4_rec_rules_aux i all cs (SUC j)))`;;
let l4_anon = new_recursive_definition l4_expr_RECURSION
 `(l4_anon (L4BVar i) = L4BVar i) /\
  (l4_anon (L4NatLit lit) = L4NatLit lit) /\
  (l4_anon (L4Proj owner idx major) = L4Proj owner idx (l4_anon major)) /\
  (l4_anon (L4Sort u) = L4Sort u) /\
  (l4_anon (L4Const n us) = L4Const n us) /\
  (l4_anon (L4App f a) = L4App (l4_anon f) (l4_anon a)) /\
  (l4_anon (L4Lam n a b) = L4Lam L4Anonymous (l4_anon a) (l4_anon b)) /\
  (l4_anon (L4Pi n a b) = L4Pi L4Anonymous (l4_anon a) (l4_anon b)) /\
  (l4_anon (L4Let n a v b) = L4Let L4Anonymous (l4_anon a) (l4_anon v) (l4_anon b))`;;
let l4_anon_rule = new_recursive_definition l4_recrule_RECURSION
 `l4_anon_rule (L4RecRule n k rhs) = L4RecRule n k (l4_anon rhs)`;;
let l4_anon_role = new_recursive_definition l4_role_RECURSION
 `(l4_anon_role (L4InductiveRole p x ns cs nested r f u) =
    L4InductiveRole p x ns cs nested r f u) /\
  (l4_anon_role (L4ConstructorRole n j p nf u) = L4ConstructorRole n j p nf u) /\
  (l4_anon_role (L4RecursorRole ns p x m k rs b u) =
    L4RecursorRole ns p x m k (MAP l4_anon_rule rs) b u)`;;
let l4_level_le = new_definition
 `l4_level_le u v <=> !rho. l4_eval_level u rho <= l4_eval_level v rho`;;
let l4_level_nonzero = new_definition
 `l4_level_nonzero u <=> !rho. 0 < l4_eval_level u rho`;;
