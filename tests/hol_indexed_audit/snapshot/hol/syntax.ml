(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)

let l4_name_INDUCT,l4_name_RECURSION = define_type
 "l4_name = L4Anonymous | L4String l4_name (num list)
                       | L4Numeric l4_name num";;

let l4_level_INDUCT,l4_level_RECURSION = define_type
 "l4_level = L4Zero | L4Succ l4_level | L4Max l4_level l4_level
            | L4IMax l4_level l4_level | L4Param l4_name";;

let l4_expr_INDUCT,l4_expr_RECURSION = define_type
 "l4_expr = L4BVar num | L4Sort l4_level | L4Const l4_name (l4_level list)
           | L4App l4_expr l4_expr | L4Lam l4_name l4_expr l4_expr
           | L4Pi l4_name l4_expr l4_expr
           | L4Let l4_name l4_expr l4_expr l4_expr | L4NatLit num";;

let l4_eval_level = new_recursive_definition l4_level_RECURSION
 `(l4_eval_level L4Zero rho = 0) /\
  (l4_eval_level (L4Succ u) rho = SUC (l4_eval_level u rho)) /\
  (l4_eval_level (L4Max u v) rho = MAX (l4_eval_level u rho) (l4_eval_level v rho)) /\
  (l4_eval_level (L4IMax u v) rho =
    if l4_eval_level v rho = 0 then 0
    else MAX (l4_eval_level u rho) (l4_eval_level v rho)) /\
  (l4_eval_level (L4Param n) rho = rho n)`;;

let l4_level_equiv = new_definition
 `l4_level_equiv u v <=> !rho:l4_name->num.
    l4_eval_level u rho = l4_eval_level v rho`;;

let l4_level_equiv_refl = prove
 (`!u. l4_level_equiv u u`, REWRITE_TAC [l4_level_equiv]);;

let l4_lift = new_recursive_definition l4_expr_RECURSION
 `(l4_lift (L4BVar i) d k = L4BVar (if i < k then i else i + d)) /\
  (l4_lift (L4Sort u) d k = L4Sort u) /\
  (l4_lift (L4Const n us) d k = L4Const n us) /\
  (l4_lift (L4App f a) d k = L4App (l4_lift f d k) (l4_lift a d k)) /\
  (l4_lift (L4Lam n a b) d k =
    L4Lam n (l4_lift a d k) (l4_lift b d (SUC k))) /\
  (l4_lift (L4Pi n a b) d k =
    L4Pi n (l4_lift a d k) (l4_lift b d (SUC k))) /\
  (l4_lift (L4Let n a v b) d k =
    L4Let n (l4_lift a d k) (l4_lift v d k) (l4_lift b d (SUC k))) /\
  (l4_lift (L4NatLit lit) d k = L4NatLit lit)`;;

let l4_subst = new_recursive_definition l4_expr_RECURSION
 `(l4_subst (L4BVar i) k s =
    if i < k then L4BVar i else if i = k then l4_lift s k 0
    else L4BVar (i - 1)) /\
  (l4_subst (L4Sort u) k s = L4Sort u) /\
  (l4_subst (L4Const n us) k s = L4Const n us) /\
  (l4_subst (L4App f a) k s = L4App (l4_subst f k s) (l4_subst a k s)) /\
  (l4_subst (L4Lam n a b) k s =
    L4Lam n (l4_subst a k s) (l4_subst b (SUC k) s)) /\
  (l4_subst (L4Pi n a b) k s =
    L4Pi n (l4_subst a k s) (l4_subst b (SUC k) s)) /\
  (l4_subst (L4Let n a v b) k s =
    L4Let n (l4_subst a k s) (l4_subst v k s) (l4_subst b (SUC k) s)) /\
  (l4_subst (L4NatLit lit) k s = L4NatLit lit)`;;

let l4_inst = new_definition `l4_inst s b = l4_subst b 0 s`;;
