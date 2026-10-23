(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   The reserved namespace check follows Inductive/Add.lean:checkNoNestedAux.
   Binder display names and level parameter names are not constant references. *)
needs "hol/inductive_syntax.ml";;

let l4_nested_name = new_recursive_definition l4_name_RECURSION
 `(l4_nested_name L4Anonymous <=> F) /\
  (l4_nested_name (L4String n s) <=> l4_nested_name n \/
    (n = L4Anonymous /\ s = [95;110;101;115;116;101;100])) /\
  (l4_nested_name (L4Numeric n k) <=> l4_nested_name n)`;;

let l4_no_nested_aux = new_recursive_definition l4_expr_RECURSION
 `(l4_no_nested_aux (L4BVar j) <=> T) /\
  (l4_no_nested_aux (L4NatLit lit) <=> T) /\
  (l4_no_nested_aux (L4StrLit chars) <=> T) /\
  (l4_no_nested_aux (L4Proj owner idx major) <=>
    ~l4_nested_name owner /\ l4_no_nested_aux major) /\
  (l4_no_nested_aux (L4Sort u) <=> T) /\
  (l4_no_nested_aux (L4Const n us) <=> ~l4_nested_name n) /\
  (l4_no_nested_aux (L4App f a) <=> l4_no_nested_aux f /\ l4_no_nested_aux a) /\
  (l4_no_nested_aux (L4Lam n a b) <=> l4_no_nested_aux a /\ l4_no_nested_aux b) /\
  (l4_no_nested_aux (L4Pi n a b) <=> l4_no_nested_aux a /\ l4_no_nested_aux b) /\
  (l4_no_nested_aux (L4Let n a v b) <=>
    l4_no_nested_aux a /\ l4_no_nested_aux v /\ l4_no_nested_aux b)`;;

let l4_no_nested_block = new_definition
 `l4_no_nested_block i cs <=> ALL (\c. l4_no_nested_aux (l4_ctor_type i c)) cs`;;

let l4_no_nested_anon = prove
 (`!e. l4_no_nested_aux (l4_anon e) <=> l4_no_nested_aux e`,
  MATCH_MP_TAC l4_expr_INDUCT THEN REWRITE_TAC [l4_anon;l4_no_nested_aux] THEN MESON_TAC []);;

let l4_is_constructor_role = new_recursive_definition l4_role_RECURSION
 `(l4_is_constructor_role (L4InductiveRole p j ns cs k r x u) <=> F) /\
  (l4_is_constructor_role (L4ConstructorRole i j p f u) <=> T) /\
  (l4_is_constructor_role (L4RecursorRole ns p j m k rs x u) <=> F)`;;
