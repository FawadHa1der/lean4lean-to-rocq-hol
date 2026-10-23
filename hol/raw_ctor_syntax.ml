(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Bounded head-only positivity slice of Lean4Lean 8223d223 checkPositivity. *)
needs "hol/environment_rules.ml";;

let l4_head_stop = new_recursive_definition l4_expr_RECURSION
 `(l4_head_stop env (L4BVar j) <=> T) /\
  (l4_head_stop env (L4Sort u) <=> T) /\
  (l4_head_stop env (L4Const n us) <=>
    ALL (\d. l4_entry_name d = n ==> ~l4_entry_transparent d) env) /\
  (l4_head_stop env (L4App f a) <=> F) /\
  (l4_head_stop env (L4Lam n a b) <=> T) /\
  (l4_head_stop env (L4Pi n a b) <=> T) /\
  (l4_head_stop env (L4Let n a v b) <=> F) /\
  (l4_head_stop env (L4NatLit lit) <=> T) /\
  (l4_head_stop env (L4StrLit chars) <=> T) /\
  (l4_head_stop env (L4Proj n j e) <=> F)`;;
let l4_head_lambda = new_recursive_definition l4_expr_RECURSION
 `(l4_head_lambda (L4BVar j) <=> F) /\
  (l4_head_lambda (L4Sort u) <=> F) /\
  (l4_head_lambda (L4Const n us) <=> F) /\
  (l4_head_lambda (L4App f a) <=> F) /\
  (l4_head_lambda (L4Lam n a b) <=> T) /\
  (l4_head_lambda (L4Pi n a b) <=> F) /\
  (l4_head_lambda (L4Let n a v b) <=> F) /\
  (l4_head_lambda (L4NatLit lit) <=> F) /\
  (l4_head_lambda (L4StrLit chars) <=> F) /\
  (l4_head_lambda (L4Proj n j e) <=> F)`;;
let l4_head_RULES,l4_head_INDUCT,l4_head_CASES = new_inductive_definition
 `(!env e. l4_head_stop env e ==> l4_head env e e) /\
  (!env d us r. MEM d env /\ l4_entry_transparent d /\
    LENGTH (l4_entry_params d) = LENGTH us /\
    l4_head env (l4_expr_lsubst (l4_entry_body d) (l4_entry_params d) us) r ==>
    l4_head env (L4Const (l4_entry_name d) us) r) /\
  (!env n a v b r. l4_head env (l4_inst v b) r ==>
    l4_head env (L4Let n a v b) r) /\
  (!env f x n a b r. l4_head env f (L4Lam n a b) /\
    l4_head env (l4_inst x b) r ==> l4_head env (L4App f x) r) /\
  (!env f x h. l4_head env f h /\ ~l4_head_lambda h ==>
    l4_head env (L4App f x) (L4App h x))`;;

(* Fragment formation is not an environment certificate. Its caller must
   authenticate the exact prior/header-only entries separately. *)
let l4_raw_sort = new_definition
 `!env g e u. l4_raw_sort env g e u <=>
    l4_econtext env g /\ l4_edef env g e e (L4Sort u)`;;
let l4_raw_field = new_recursive_definition l4_field_RECURSION
 `(l4_raw_field i ps p j L4Recursive a <=> a = l4_family_app i ps p j) /\
  (l4_raw_field i ps p j (L4Data d) a <=>
    l4_without_const i a /\ l4_anon a = l4_anon (l4_lift d j 0))`;;
let l4_raw_fields_RULES,l4_raw_fields_INDUCT,l4_raw_fields_CASES = new_inductive_definition
 `(!env i ps p u g j. l4_raw_fields env i ps p u g j [] (l4_family_app i ps p j)) /\
  (!env i ps p u g j f fs n a b h v.
    l4_head env a h /\ l4_raw_field i ps p j f h /\
    l4_params_expr a ps /\ l4_raw_sort env g a v /\ l4_level_le v u /\
    l4_raw_fields env i ps p u (CONS a g) (SUC j) fs b ==>
    l4_raw_fields env i ps p u g j (CONS f fs) (L4Pi n a b))`;;
let l4_raw_params_RULES,l4_raw_params_INDUCT,l4_raw_params_CASES = new_inductive_definition
 `(!env i ps p u g fs e. l4_raw_fields env i ps p u g 0 fs e ==>
    l4_raw_params env i ps p u g [] fs e) /\
  (!env i ps p u g (m:l4_name) d pars fs n a b h v.
    (l4_anon a = l4_anon d \/
      l4_head env a h /\ l4_anon h = l4_anon d) /\
    l4_params_expr a ps /\ l4_raw_sort env g a v /\
    l4_raw_params env i ps p u (CONS a g) pars fs b ==>
    l4_raw_params env i ps p u g (CONS (m,d) pars) fs (L4Pi n a b))`;;

(* The directed clause remains available; the additional case is identity,
   not reduction of canonical parameter domains or arbitrary conversion. *)
let l4_raw_params_directed = prove
 (`!env i ps p u g (m:l4_name) d pars fs n a b h v.
    l4_head env a h /\ l4_anon h = l4_anon d /\
    l4_params_expr a ps /\ l4_raw_sort env g a v /\
    l4_raw_params env i ps p u (CONS a g) pars fs b ==>
    l4_raw_params env i ps p u g (CONS (m,d) pars) fs (L4Pi n a b)`,
  MESON_TAC [l4_raw_params_RULES]);;
