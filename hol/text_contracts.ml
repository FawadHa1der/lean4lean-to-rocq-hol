(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Adapted interface checks: Lean4Lean/Primitive.lean, pinned in UPSTREAM.md.
   Text primitive interfaces authorize no host arithmetic or string evaluation. *)
needs "hol/primitive_contracts.ml";;

let l4_text_char_name = new_definition
 `l4_text_char_name = L4String L4Anonymous [67;104;97;114]`;;
let l4_text_string_name = new_definition
 `l4_text_string_name = L4String L4Anonymous [83;116;114;105;110;103]`;;
let l4_text_list_name = new_definition
 `l4_text_list_name = L4String L4Anonymous [76;105;115;116]`;;
let l4_text_of_nat_name = new_definition
 `l4_text_of_nat_name = L4String l4_text_char_name [111;102;78;97;116]`;;
let l4_text_of_list_name = new_definition
 `l4_text_of_list_name = L4String l4_text_string_name [111;102;76;105;115;116]`;;
let l4_text_char = new_definition `l4_text_char = L4Const l4_text_char_name []`;;
let l4_text_string = new_definition `l4_text_string = L4Const l4_text_string_name []`;;
let l4_text_list_char = new_definition
 `l4_text_list_char = L4App (L4Const l4_text_list_name [L4Zero]) l4_text_char`;;
let l4_text_nil = new_definition
 `l4_text_nil = L4App (L4Const (L4String l4_text_list_name [110;105;108]) [L4Zero]) l4_text_char`;;
let l4_text_cons = new_definition
 `l4_text_cons = L4App (L4Const (L4String l4_text_list_name [99;111;110;115]) [L4Zero]) l4_text_char`;;
let l4_text_char_signature = new_definition
 `l4_text_char_signature = L4Pi L4Anonymous l4_prim_nat l4_text_char`;;
let l4_text_string_signature = new_definition
 `l4_text_string_signature = L4Pi L4Anonymous l4_text_list_char l4_text_string`;;
let l4_text_cons_signature = new_definition
 `l4_text_cons_signature = L4Pi L4Anonymous l4_text_char
    (L4Pi L4Anonymous l4_text_list_char l4_text_list_char)`;;

let l4_text_is_type = new_definition
 `l4_text_is_type (J:l4_expr list->l4_expr->l4_expr->l4_expr->bool) a <=>
    ?u. J [] a a (L4Sort u)`;;
let l4_text_char_contract = new_definition
 `l4_text_char_contract J b <=>
    J [] l4_prim_nat l4_prim_nat (L4Sort (L4Succ L4Zero)) /\
    l4_text_is_type J l4_text_char /\ J [] b b l4_text_char_signature`;;
let l4_text_string_contract = new_definition
 `l4_text_string_contract J b <=>
    l4_text_is_type J l4_text_list_char /\ l4_text_is_type J l4_text_char /\
    J [] l4_text_nil l4_text_nil l4_text_list_char /\
    J [] l4_text_cons l4_text_cons l4_text_cons_signature /\
    J [] b b l4_text_string_signature`;;
let l4_text_definition_header = new_definition
 `l4_text_definition_header n (ps:l4_name list) a b <=>
    ps = [] /\ l4_params_expr a [] /\ l4_params_expr b [] /\
    ((n = l4_text_of_nat_name /\ l4_anon a = l4_text_char_signature) \/
     (n = l4_text_of_list_name /\ l4_anon a = l4_text_string_signature))`;;
let l4_text_definition_contract = new_definition
 `l4_text_definition_contract J n ps a b <=>
    l4_text_definition_header n ps a b /\ l4_text_is_type J a /\ J [] b b a /\
    ((n = l4_text_of_nat_name /\ l4_text_char_contract J b) \/
     (n = l4_text_of_list_name /\ l4_text_string_contract J b))`;;
let l4_text_definition_mono = prove
 (`!J K n ps a b. (!g e e' t. J g e e' t ==> K g e e' t) ==>
    l4_text_definition_contract J n ps a b ==>
    l4_text_definition_contract K n ps a b`,
  REWRITE_TAC [l4_text_definition_contract;l4_text_char_contract;
    l4_text_string_contract;l4_text_is_type] THEN MESON_TAC []);;
let l4_text_definition_body_typed = prove
 (`!J n ps a b. l4_text_definition_contract J n ps a b ==> J [] b b a`,
  SIMP_TAC [l4_text_definition_contract]);;
let l4_text_definition_type_formed = prove
 (`!J n ps a b. l4_text_definition_contract J n ps a b ==>
    ?u. J [] a a (L4Sort u)`,
  SIMP_TAC [l4_text_definition_contract;l4_text_is_type]);;
