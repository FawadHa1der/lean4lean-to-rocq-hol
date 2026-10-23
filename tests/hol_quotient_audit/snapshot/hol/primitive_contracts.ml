(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Equations adapted from Lean4Lean/Primitive.lean at
   8223d223ed98661882e95d9d6a7126df7097cd76, checkNatAdd/Pred/Sub/Mul
   and checkNatBoolCases/BEq/BLE.
   J is deliberately abstract: no dependency on environment admission. *)
needs "hol/syntax.ml";;
needs "hol/primitive_names.ml";;

let l4_prim_nat = new_definition
 `l4_prim_nat = L4Const l4_nat_name []`;;
let l4_prim_zero = new_definition
 `l4_prim_zero = L4Const (L4String l4_nat_name [122;101;114;111]) []`;;
let l4_prim_succ = new_definition
 `l4_prim_succ x = L4App
    (L4Const (L4String l4_nat_name [115;117;99;99]) []) x`;;
let l4_prim_unary = new_definition
 `l4_prim_unary = L4Pi L4Anonymous l4_prim_nat l4_prim_nat`;;
let l4_prim_binary = new_definition
 `l4_prim_binary = L4Pi L4Anonymous l4_prim_nat l4_prim_unary`;;
let l4_prim_bool = new_definition
 `l4_prim_bool = L4Const l4_bool_name []`;;
let l4_prim_false = new_definition
 `l4_prim_false = L4Const (L4String l4_bool_name [102;97;108;115;101]) []`;;
let l4_prim_true = new_definition
 `l4_prim_true = L4Const (L4String l4_bool_name [116;114;117;101]) []`;;
let l4_prim_bool_binary = new_definition
 `l4_prim_bool_binary = L4Pi L4Anonymous l4_prim_nat
    (L4Pi L4Anonymous l4_prim_nat l4_prim_bool)`;;

(* In [Nat;Nat], BVar 1 is x and BVar 0 is y. These are symbolic
   judgments, not checks at selected natural-number literals. *)
let l4_prim_add_contract = new_definition
 `l4_prim_add_contract J b <=>
    J [] b b l4_prim_binary /\
    J [l4_prim_nat]
      (L4App (L4App b (L4BVar 0)) l4_prim_zero) (L4BVar 0) l4_prim_nat /\
    J [l4_prim_nat;l4_prim_nat]
      (L4App (L4App b (L4BVar 1)) (l4_prim_succ (L4BVar 0)))
      (l4_prim_succ (L4App (L4App b (L4BVar 1)) (L4BVar 0))) l4_prim_nat`;;

let l4_prim_pred_contract = new_definition
 `l4_prim_pred_contract J b <=>
    J [] b b l4_prim_unary /\
    J [] (L4App b l4_prim_zero) l4_prim_zero l4_prim_nat /\
    J [l4_prim_nat] (L4App b (l4_prim_succ (L4BVar 0))) (L4BVar 0) l4_prim_nat`;;

let l4_prim_sub_contract = new_definition
 `l4_prim_sub_contract J p b <=>
    l4_prim_pred_contract J p /\
    J [] b b l4_prim_binary /\
    J [l4_prim_nat]
      (L4App (L4App b (L4BVar 0)) l4_prim_zero) (L4BVar 0) l4_prim_nat /\
    J [l4_prim_nat;l4_prim_nat]
      (L4App (L4App b (L4BVar 1)) (l4_prim_succ (L4BVar 0)))
      (L4App p (L4App (L4App b (L4BVar 1)) (L4BVar 0))) l4_prim_nat`;;

let l4_prim_mul_contract = new_definition
 `l4_prim_mul_contract J a b <=>
    l4_prim_add_contract J a /\
    J [] b b l4_prim_binary /\
    J [l4_prim_nat]
      (L4App (L4App b (L4BVar 0)) l4_prim_zero) l4_prim_zero l4_prim_nat /\
    J [l4_prim_nat;l4_prim_nat]
      (L4App (L4App b (L4BVar 1)) (l4_prim_succ (L4BVar 0)))
      (L4App (L4App a (L4App (L4App b (L4BVar 1)) (L4BVar 0))) (L4BVar 1))
      l4_prim_nat`;;

let l4_prim_bool_cases_contract = new_definition
 `l4_prim_bool_cases_contract J b0s b <=>
    J [] b b l4_prim_bool_binary /\
    J [] (L4App (L4App b l4_prim_zero) l4_prim_zero) l4_prim_true l4_prim_bool /\
    J [l4_prim_nat]
      (L4App (L4App b l4_prim_zero) (l4_prim_succ (L4BVar 0))) b0s l4_prim_bool /\
    J [l4_prim_nat]
      (L4App (L4App b (l4_prim_succ (L4BVar 0))) l4_prim_zero)
      l4_prim_false l4_prim_bool /\
    J [l4_prim_nat;l4_prim_nat]
      (L4App (L4App b (l4_prim_succ (L4BVar 1))) (l4_prim_succ (L4BVar 0)))
      (L4App (L4App b (L4BVar 1)) (L4BVar 0)) l4_prim_bool`;;
let l4_prim_beq_contract = new_definition
 `l4_prim_beq_contract J b <=> l4_prim_bool_cases_contract J l4_prim_false b`;;
let l4_prim_ble_contract = new_definition
 `l4_prim_ble_contract J b <=> l4_prim_bool_cases_contract J l4_prim_true b`;;
let l4_prim_beq_body_typed = prove
 (`!J b. l4_prim_beq_contract J b ==> J [] b b l4_prim_bool_binary`,
  SIMP_TAC [l4_prim_beq_contract;l4_prim_bool_cases_contract]);;
let l4_prim_ble_body_typed = prove
 (`!J b. l4_prim_ble_contract J b ==> J [] b b l4_prim_bool_binary`,
  SIMP_TAC [l4_prim_ble_contract;l4_prim_bool_cases_contract]);;

let l4_prim_sub_dependency = prove
 (`!J p b. l4_prim_sub_contract J p b ==> l4_prim_pred_contract J p`,
  SIMP_TAC [l4_prim_sub_contract]);;
let l4_prim_mul_dependency = prove
 (`!J a b. l4_prim_mul_contract J a b ==> l4_prim_add_contract J a`,
  SIMP_TAC [l4_prim_mul_contract]);;

(* Monotonicity supplies the checked-to-raw bridge without importing a native
   environment judgment into this file. *)
let l4_prim_add_mono = prove
 (`!J K b. (!g e e' a. J g e e' a ==> K g e e' a) ==>
    l4_prim_add_contract J b ==> l4_prim_add_contract K b`,
  REWRITE_TAC [l4_prim_add_contract] THEN MESON_TAC []);;
let l4_prim_pred_mono = prove
 (`!J K b. (!g e e' a. J g e e' a ==> K g e e' a) ==>
    l4_prim_pred_contract J b ==> l4_prim_pred_contract K b`,
  REWRITE_TAC [l4_prim_pred_contract] THEN MESON_TAC []);;
let l4_prim_sub_mono = prove
 (`!J K p b. (!g e e' a. J g e e' a ==> K g e e' a) ==>
    l4_prim_sub_contract J p b ==> l4_prim_sub_contract K p b`,
  REWRITE_TAC [l4_prim_sub_contract;l4_prim_pred_contract] THEN MESON_TAC []);;
let l4_prim_mul_mono = prove
 (`!J K a b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_prim_mul_contract J a b ==> l4_prim_mul_contract K a b`,
  REWRITE_TAC [l4_prim_mul_contract;l4_prim_add_contract] THEN MESON_TAC []);;
let l4_prim_bool_cases_mono = prove
 (`!J K b0s b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_prim_bool_cases_contract J b0s b ==> l4_prim_bool_cases_contract K b0s b`,
  REWRITE_TAC [l4_prim_bool_cases_contract] THEN MESON_TAC []);;
let l4_prim_beq_mono = prove
 (`!J K b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_prim_beq_contract J b ==> l4_prim_beq_contract K b`,
  REWRITE_TAC [l4_prim_beq_contract] THEN MESON_TAC [l4_prim_bool_cases_mono]);;
let l4_prim_ble_mono = prove
 (`!J K b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_prim_ble_contract J b ==> l4_prim_ble_contract K b`,
  REWRITE_TAC [l4_prim_ble_contract] THEN MESON_TAC [l4_prim_bool_cases_mono]);;

let l4_prim_add_name = new_definition
 `l4_prim_add_name = L4String l4_nat_name [97;100;100]`;;
let l4_prim_pred_name = new_definition
 `l4_prim_pred_name = L4String l4_nat_name [112;114;101;100]`;;
let l4_prim_sub_name = new_definition
 `l4_prim_sub_name = L4String l4_nat_name [115;117;98]`;;
let l4_prim_mul_name = new_definition
 `l4_prim_mul_name = L4String l4_nat_name [109;117;108]`;;
let l4_prim_beq_name = new_definition
 `l4_prim_beq_name = L4String l4_nat_name [98;101;113]`;;
let l4_prim_ble_name = new_definition
 `l4_prim_ble_name = L4String l4_nat_name [98;108;101]`;;

(* Field-based, since l4_entry is declared by environment_rules.ml. The future
   native admission rule must hardcode L4DefKind and independently prove freshness. *)
let l4_prim_definition_header = new_definition
 `l4_prim_definition_header n (ps:l4_name list) a b <=>
    ps = [] /\ l4_params_expr a [] /\ l4_params_expr b [] /\
    ((n = l4_prim_add_name /\ l4_anon a = l4_prim_binary) \/
     (n = l4_prim_pred_name /\ l4_anon a = l4_prim_unary) \/
     (n = l4_prim_sub_name /\ l4_anon a = l4_prim_binary) \/
     (n = l4_prim_mul_name /\ l4_anon a = l4_prim_binary) \/
     (n = l4_prim_beq_name /\ l4_anon a = l4_prim_bool_binary) \/
     (n = l4_prim_ble_name /\ l4_anon a = l4_prim_bool_binary))`;;

let l4_prim_definition_contract = new_definition
 `l4_prim_definition_contract J n ps a b <=>
    l4_prim_definition_header n ps a b /\
    J [] a a (L4Sort (L4Succ L4Zero)) /\ J [] b b a /\
    ((n = l4_prim_add_name /\ l4_prim_add_contract J b) \/
     (n = l4_prim_pred_name /\ l4_prim_pred_contract J b) \/
     (n = l4_prim_sub_name /\
      l4_prim_sub_contract J (L4Const l4_prim_pred_name []) b) \/
     (n = l4_prim_mul_name /\
      l4_prim_mul_contract J (L4Const l4_prim_add_name []) b) \/
     (n = l4_prim_beq_name /\ l4_prim_beq_contract J b) \/
     (n = l4_prim_ble_name /\ l4_prim_ble_contract J b))`;;

let l4_prim_definition_mono = prove
 (`!J K n ps a b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_prim_definition_contract J n ps a b ==>
    l4_prim_definition_contract K n ps a b`,
  REWRITE_TAC [l4_prim_definition_contract] THEN
  MESON_TAC [l4_prim_add_mono;l4_prim_pred_mono;l4_prim_sub_mono;l4_prim_mul_mono;
    l4_prim_beq_mono;l4_prim_ble_mono]);;

let l4_prim_definition_header_required = prove
 (`!J n ps a b. l4_prim_definition_contract J n ps a b ==>
    l4_prim_definition_header n ps a b`,
  SIMP_TAC [l4_prim_definition_contract]);;
let l4_prim_definition_body_typed = prove
 (`!J n ps a b. l4_prim_definition_contract J n ps a b ==> J [] b b a`,
  SIMP_TAC [l4_prim_definition_contract]);;
let l4_prim_definition_type_formed = prove
 (`!J n ps a b. l4_prim_definition_contract J n ps a b ==>
    J [] a a (L4Sort (L4Succ L4Zero))`,
  SIMP_TAC [l4_prim_definition_contract]);;
