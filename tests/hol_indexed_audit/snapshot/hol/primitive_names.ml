(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/inductive_syntax.ml";;

let l4_nat_name = new_definition `l4_nat_name = L4String L4Anonymous [78;97;116]`;;
let l4_bool_name = new_definition `l4_bool_name = L4String L4Anonymous [66;111;111;108]`;;
let l4_primitive_names = new_definition
 `l4_primitive_names = [l4_bool_name;
    L4String (l4_bool_name) [102;97;108;115;101];
    L4String (l4_bool_name) [116;114;117;101];
    l4_nat_name;
    L4String (l4_nat_name) [122;101;114;111];
    L4String (l4_nat_name) [115;117;99;99];
    L4String (l4_nat_name) [97;100;100];
    L4String (l4_nat_name) [112;114;101;100];
    L4String (l4_nat_name) [115;117;98];
    L4String (l4_nat_name) [109;117;108];
    L4String (l4_nat_name) [112;111;119];
    L4String (l4_nat_name) [103;99;100];
    L4String (l4_nat_name) [109;111;100];
    L4String (l4_nat_name) [100;105;118];
    L4String (l4_nat_name) [98;101;113];
    L4String (l4_nat_name) [98;108;101];
    L4String (l4_nat_name) [98;105;116;119;105;115;101];
    L4String (l4_nat_name) [108;97;110;100];
    L4String (l4_nat_name) [108;111;114];
    L4String (l4_nat_name) [120;111;114];
    L4String (l4_nat_name) [115;104;105;102;116;76;101;102;116];
    L4String (l4_nat_name) [115;104;105;102;116;82;105;103;104;116];
    L4String (L4String L4Anonymous [83;116;114;105;110;103]) [111;102;76;105;115;116];
    L4String (L4String L4Anonymous [67;104;97;114]) [111;102;78;97;116]]`;;
let l4_protected_name = new_definition
 `l4_protected_name n <=> MEM n l4_primitive_names`;;
let l4_primitive_block = new_definition
 `l4_primitive_block i u cs <=>
    (i = l4_nat_name ==>
      u = L4Succ L4Zero /\
      cs = [L4CtorSpec (L4String (l4_nat_name) [122;101;114;111]) [];
            L4CtorSpec (L4String (l4_nat_name) [115;117;99;99]) [L4Recursive]]) /\
    (i = l4_bool_name ==>
      u = L4Succ L4Zero /\
      cs = [L4CtorSpec (L4String (l4_bool_name) [102;97;108;115;101]) [];
            L4CtorSpec (L4String (l4_bool_name) [116;114;117;101]) []]) /\
    ALL (\n. ~l4_protected_name n \/
      (i = l4_nat_name /\ MEM n [l4_nat_name;L4String (l4_nat_name) [122;101;114;111];L4String (l4_nat_name) [115;117;99;99]]) \/
      (i = l4_bool_name /\ MEM n [l4_bool_name;L4String (l4_bool_name) [102;97;108;115;101];L4String (l4_bool_name) [116;114;117;101]]))
      (CONS i (APPEND (MAP l4_ctor_name cs) [l4_rec_name i]))`;;
