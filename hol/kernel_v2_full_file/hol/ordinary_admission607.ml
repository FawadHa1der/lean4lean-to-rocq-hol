(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of Rocq Declarations.v10-67 plus explicitly limited dispatch.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE607.txt. No HOL axiom is introduced. *)
needs "hol/kernel_checker597.ml";;
needs "hol/universe_decision555.ml";;

let l4_reserved_names607 = new_definition
 `l4_reserved_names607 =
    [l4_core_nat_name533;l4_core_zero_name533;l4_core_succ_name533;
     L4String l4_core_nat_name533 [97;100;100];
     L4String l4_core_nat_name533 [112;114;101;100];
     L4String l4_core_nat_name533 [115;117;98];
     L4String l4_core_nat_name533 [109;117;108];
     L4String l4_core_nat_name533 [112;111;119];
     L4String l4_core_nat_name533 [103;99;100];
     L4String l4_core_nat_name533 [109;111;100];
     L4String l4_core_nat_name533 [100;105;118];
     L4String l4_core_nat_name533 [98;101;113];
     L4String l4_core_nat_name533 [98;108;101];
     L4String l4_core_nat_name533 [98;105;116;119;105;115;101];
     L4String l4_core_nat_name533 [108;97;110;100];
     L4String l4_core_nat_name533 [108;111;114];
     L4String l4_core_nat_name533 [120;111;114];
     L4String l4_core_nat_name533 [115;104;105;102;116;76;101;102;116];
     L4String l4_core_nat_name533 [115;104;105;102;116;82;105;103;104;116];
     l4_core_bool_name533;l4_core_false_name533;l4_core_true_name533;
     l4_core_string_of_list533;l4_core_char_of_nat533]`;;

let l4_input_safety_INDUCT607,l4_input_safety_RECURSION607 = define_type
 "l4_input_safety607 = L4InputSafe607 | L4InputPartial607 | L4InputUnsafe607";;
let l4_input_decl_INDUCT607,l4_input_decl_RECURSION607 = define_type
 "l4_input_decl607 =
    L4InputAxiom607 l4_name (l4_name list) l4_kexpr447 bool |
    L4InputDefinition607 l4_khints493 l4_name (l4_name list)
      l4_kexpr447 l4_kexpr447 l4_input_safety607 |
    L4InputTheorem607 l4_name (l4_name list) l4_kexpr447 l4_kexpr447 |
    L4InputOpaque607 l4_name (l4_name list) l4_kexpr447 l4_kexpr447 bool |
    L4InputUnsupported607";;

let l4_check_header607 = new_definition
 `l4_check_header607 fuel env n ps ty =
   match l4_kfind_decl493 env n with
   | SOME d -> L4KReject491 L4KDuplicateDeclaration491
   | NONE ->
     if ~l4_names_unique437 ps then L4KReject491 L4KDuplicateUniverse491 else
     if ~l4_kscoped447 ty 0 then L4KReject491 L4KMalformedDeclaration491 else
     l4_kr_bind491 (l4_infer597 fuel env ps l4_kempty_context532 ty) (\inferred.
       l4_kr_bind491 (l4_whnf597 fuel env ps l4_kempty_context532 inferred) (\reduced.
         match reduced with
         | L4KSort447 u -> L4KAccept491 one
         | _ -> L4KReject491 L4KExpectedSort491))`;;

let l4_check_proposition607 = new_definition
 `l4_check_proposition607 fuel env ps ty =
   l4_kr_bind491 (l4_infer597 fuel env ps l4_kempty_context532 ty) (\inferred.
     l4_kr_bind491 (l4_whnf597 fuel env ps l4_kempty_context532 inferred) (\reduced.
       match reduced with
       | L4KSort447 u ->
           l4_kr_bind491 (l4_klevel_equiv555 fuel u L4KZero447)
             (\is_zero. if is_zero then L4KAccept491 one
               else L4KReject491 L4KMalformedDeclaration491)
       | _ -> L4KReject491 L4KExpectedSort491))`;;

(* Internal record constructor after body/header checking. Its kind argument
   is not an admission license: generated kinds need their own checked driver. *)
let l4_checked_constant607 = new_definition
 `l4_checked_constant607 fuel env n ps ty body kind =
   l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header.
     l4_kr_bind491
       (match body with
        | NONE -> L4KAccept491 one
        | SOME value ->
            if l4_kscoped447 value 0
            then l4_check597 fuel env ps l4_kempty_context532 value ty
            else L4KReject491 L4KMalformedDeclaration491)
       (\checked. L4KAccept491
         (CONS (L4KDeclaration493 n ps ty body kind L4KHintOpaque493) env)))`;;

(* Deliberately restricted entry: safe definitions also decline until actual
   primitive signature/equation classification is ported. Not full admit. *)
let l4_admit_basic607 = new_definition
 `l4_admit_basic607 fuel env input =
   match input with
   | L4InputAxiom607 n ps ty unsafe ->
       if unsafe then L4KDecline491 L4KUnsupportedDeclaration491 else
       if l4_name_mem437 n l4_reserved_names607
       then L4KReject491 L4KMalformedDeclaration491 else
       l4_checked_constant607 fuel env n ps ty NONE L4KDAssumption493
   | L4InputDefinition607 hints n ps ty body safety ->
       L4KDecline491 L4KUnsupportedDeclaration491
   | L4InputTheorem607 n ps ty body ->
       if l4_name_mem437 n l4_reserved_names607
       then L4KReject491 L4KMalformedDeclaration491 else
       l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header.
         l4_kr_bind491 (l4_check_proposition607 fuel env ps ty) (\proposition.
           l4_checked_constant607 fuel env n ps ty (SOME body) L4KDTheorem493))
   | L4InputOpaque607 n ps ty body unsafe ->
       if unsafe then L4KDecline491 L4KUnsupportedDeclaration491 else
       if l4_name_mem437 n l4_reserved_names607
       then L4KReject491 L4KMalformedDeclaration491 else
       l4_checked_constant607 fuel env n ps ty (SOME body) L4KDOpaque493
   | L4InputUnsupported607 -> L4KDecline491 L4KUnsupportedDeclaration491`;;

let l4_check_basic_declarations607 = new_recursive_definition list_RECURSION
 `(l4_check_basic_declarations607 [] fuel env = L4KAccept491 env) /\
  (l4_check_basic_declarations607 (CONS input inputs) fuel env =
     l4_kr_bind491 (l4_admit_basic607 fuel env input)
       (\next. l4_check_basic_declarations607 inputs fuel next))`;;

