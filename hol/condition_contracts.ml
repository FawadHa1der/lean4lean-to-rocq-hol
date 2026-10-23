(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Boolean Condition.check / ite branch from Lean4Lean/Primitive.lean,
   commit 8223d223ed98661882e95d9d6a7126df7097cd76.
   This is a capability contract, not declaration admission or acceleration. *)
needs "hol/primitive_contracts.ml";;

let l4_condition_prop_type = new_definition
 `l4_condition_prop_type =
    L4Pi L4Anonymous l4_prim_bool (L4Sort L4Zero)`;;
let l4_condition_nat_selector = new_definition
 `l4_condition_nat_selector = L4Pi L4Anonymous l4_prim_bool l4_prim_binary`;;
let l4_condition_nat_ite = new_definition
 `l4_condition_nat_ite p d = L4Lam L4Anonymous l4_prim_bool
    (L4App (L4App (L4App
      (L4Const (L4String L4Anonymous [105;116;101]) [L4Succ L4Zero])
      l4_prim_nat) (L4App (l4_lift p 1 0) (L4BVar 0)))
      (L4App (l4_lift d 1 0) (L4BVar 0)))`;;
let l4_condition_select_true = new_definition
 `l4_condition_select_true = L4Lam L4Anonymous l4_prim_nat
    (L4Lam L4Anonymous l4_prim_nat (L4BVar 1))`;;
let l4_condition_select_false = new_definition
 `l4_condition_select_false = L4Lam L4Anonymous l4_prim_nat
    (L4Lam L4Anonymous l4_prim_nat (L4BVar 0))`;;

let l4_bool_condition_ite_contract = new_definition
 `l4_bool_condition_ite_contract J p d dt <=>
    J ([]:l4_expr list) d d dt /\
    J [] p p l4_condition_prop_type /\
    J [] (l4_condition_nat_ite p d) (l4_condition_nat_ite p d)
      l4_condition_nat_selector /\
    J [] (L4App (l4_condition_nat_ite p d) l4_prim_true)
      l4_condition_select_true l4_prim_binary /\
    J [] (L4App (l4_condition_nat_ite p d) l4_prim_false)
      l4_condition_select_false l4_prim_binary`;;

let l4_bool_condition_ite_mono = prove
 (`!J K p d dt.
    (!g e e' a. J g e e' a ==> K g e e' a) ==>
    l4_bool_condition_ite_contract J p d dt ==>
    l4_bool_condition_ite_contract K p d dt`,
  REWRITE_TAC [l4_bool_condition_ite_contract] THEN MESON_TAC []);;
let l4_bool_condition_ite_true = prove
 (`!J p d dt. l4_bool_condition_ite_contract J p d dt ==>
    J [] (L4App (l4_condition_nat_ite p d) l4_prim_true)
      l4_condition_select_true l4_prim_binary`,
  SIMP_TAC [l4_bool_condition_ite_contract]);;
let l4_bool_condition_ite_false = prove
 (`!J p d dt. l4_bool_condition_ite_contract J p d dt ==>
    J [] (L4App (l4_condition_nat_ite p d) l4_prim_false)
      l4_condition_select_false l4_prim_binary`,
  SIMP_TAC [l4_bool_condition_ite_contract]);;
