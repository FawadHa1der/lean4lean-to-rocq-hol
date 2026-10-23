(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/judgments.ml";;

let l4_decl_kind_INDUCT,l4_decl_kind_RECURSION = define_type
 "l4_decl_kind = L4Definition | L4Theorem";;
let l4_decl_INDUCT,l4_decl_RECURSION = define_type
 "l4_decl = L4Decl l4_decl_kind l4_name (l4_name list) l4_expr l4_expr";;
let l4_decl_name = new_recursive_definition l4_decl_RECURSION
 `l4_decl_name (L4Decl k n ps a v) = n`;;
let l4_names_distinct = new_recursive_definition list_RECURSION
 `(l4_names_distinct [] <=> T) /\
  (l4_names_distinct (CONS (n:l4_name) ns) <=>
     ~(MEM n ns) /\ l4_names_distinct ns)`;;

let l4_params_level = new_recursive_definition l4_level_RECURSION
 `(l4_params_level L4Zero ps <=> T) /\
  (l4_params_level (L4Succ u) ps <=> l4_params_level u ps) /\
  (l4_params_level (L4Max u v) ps <=> l4_params_level u ps /\ l4_params_level v ps) /\
  (l4_params_level (L4IMax u v) ps <=> l4_params_level u ps /\ l4_params_level v ps) /\
  (l4_params_level (L4Param n) ps <=> MEM n ps)`;;
let l4_params_expr = new_recursive_definition l4_expr_RECURSION
 `(l4_params_expr (L4BVar i) ps <=> T) /\
  (l4_params_expr (L4NatLit lit) ps <=> T) /\
  (l4_params_expr (L4Proj owner idx major) ps <=> l4_params_expr major ps) /\
  (l4_params_expr (L4Sort u) ps <=> l4_params_level u ps) /\
  (l4_params_expr (L4Const n us) ps <=> ALL (\u. l4_params_level u ps) us) /\
  (l4_params_expr (L4App f a) ps <=> l4_params_expr f ps /\ l4_params_expr a ps) /\
  (l4_params_expr (L4Lam n a b) ps <=> l4_params_expr a ps /\ l4_params_expr b ps) /\
  (l4_params_expr (L4Pi n a b) ps <=> l4_params_expr a ps /\ l4_params_expr b ps) /\
  (l4_params_expr (L4Let n a v b) ps <=>
    l4_params_expr a ps /\ l4_params_expr v ps /\ l4_params_expr b ps)`;;

let l4_lparam = new_recursive_definition list_RECURSION
 `(l4_lparam [] us n = L4Param n) /\
  (l4_lparam (CONS p ps) us n =
    if p = n then HD us else l4_lparam ps (TL us) n)`;;
let l4_level_lsubst = new_recursive_definition l4_level_RECURSION
 `(l4_level_lsubst L4Zero ps us = L4Zero) /\
  (l4_level_lsubst (L4Succ u) ps us = L4Succ (l4_level_lsubst u ps us)) /\
  (l4_level_lsubst (L4Max u v) ps us =
    L4Max (l4_level_lsubst u ps us) (l4_level_lsubst v ps us)) /\
  (l4_level_lsubst (L4IMax u v) ps us =
    L4IMax (l4_level_lsubst u ps us) (l4_level_lsubst v ps us)) /\
  (l4_level_lsubst (L4Param n) ps us = l4_lparam ps us n)`;;
let l4_expr_lsubst = new_recursive_definition l4_expr_RECURSION
 `(l4_expr_lsubst (L4BVar i) ps us = L4BVar i) /\
  (l4_expr_lsubst (L4NatLit lit) ps us = L4NatLit lit) /\
  (l4_expr_lsubst (L4Proj owner idx major) ps us =
    L4Proj owner idx (l4_expr_lsubst major ps us)) /\
  (l4_expr_lsubst (L4Sort u) ps us = L4Sort (l4_level_lsubst u ps us)) /\
  (l4_expr_lsubst (L4Const n vs) ps us =
    L4Const n (MAP (\u. l4_level_lsubst u ps us) vs)) /\
  (l4_expr_lsubst (L4App f a) ps us =
    L4App (l4_expr_lsubst f ps us) (l4_expr_lsubst a ps us)) /\
  (l4_expr_lsubst (L4Lam n a b) ps us =
    L4Lam n (l4_expr_lsubst a ps us) (l4_expr_lsubst b ps us)) /\
  (l4_expr_lsubst (L4Pi n a b) ps us =
    L4Pi n (l4_expr_lsubst a ps us) (l4_expr_lsubst b ps us)) /\
  (l4_expr_lsubst (L4Let n a v b) ps us =
    L4Let n (l4_expr_lsubst a ps us) (l4_expr_lsubst v ps us)
      (l4_expr_lsubst b ps us))`;;

let l4_expand_RULES,l4_expand_INDUCT,l4_expand_CASES = new_inductive_definition
 `(!env i. l4_expand env (L4BVar i) (L4BVar i)) /\
  (!env u. l4_expand env (L4Sort u) (L4Sort u)) /\
  (!env f a f' a'. l4_expand env f f' /\ l4_expand env a a' ==>
    l4_expand env (L4App f a) (L4App f' a')) /\
  (!env n a b a' b'. l4_expand env a a' /\ l4_expand env b b' ==>
    l4_expand env (L4Lam n a b) (L4Lam n a' b')) /\
  (!env n a b a' b'. l4_expand env a a' /\ l4_expand env b b' ==>
    l4_expand env (L4Pi n a b) (L4Pi n a' b')) /\
  (!env n a v b a' v' b'.
    l4_expand env a a' /\ l4_expand env v v' /\ l4_expand env b b' ==>
    l4_expand env (L4Let n a v b) (L4Let n a' v' b')) /\
  (!env k n ps a v us v'.
    MEM (L4Decl k n ps a v) env /\ LENGTH ps = LENGTH us /\ l4_expand env v v' ==>
    l4_expand env (L4Const n us) (l4_expr_lsubst v' ps us)) /\
  (!env n. l4_expand env (L4NatLit n) (L4NatLit n)) /\
  (!env owner idx major major'. l4_expand env major major' ==>
    l4_expand env (L4Proj owner idx major) (L4Proj owner idx major'))`;;

let l4_admitted_RULES,l4_admitted_INDUCT,l4_admitted_CASES = new_inductive_definition
 `(l4_admitted []) /\
  (!env k n ps a v a' v' u.
    l4_admitted env /\ ~(MEM n (MAP l4_decl_name env)) /\
    l4_names_distinct ps /\ l4_params_expr a ps /\ l4_params_expr v ps /\
    l4_expand env a a' /\ l4_expand env v v' /\
    l4_defeq [] a' a' (L4Sort u) /\ l4_defeq [] v' v' a' /\
    (k = L4Theorem ==> l4_defeq [] a' a' (L4Sort L4Zero)) ==>
    l4_admitted (CONS (L4Decl k n ps a v) env))`;;

let l4_env_has_type_RULES,l4_env_has_type_INDUCT,l4_env_has_type_CASES =
  new_inductive_definition
 `!env e a e' a'. l4_admitted env /\ l4_expand env e e' /\
    l4_expand env a a' /\ l4_defeq [] e' e' a' ==>
    l4_env_has_type env e a`;;
