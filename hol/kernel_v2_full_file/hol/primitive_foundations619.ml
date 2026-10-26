(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447/493 port of rocq/Primitives.v13-140.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE619.txt and ../INTERFACE619.txt.
   These helpers assume separately admitted environments; metadata alone is
   not a certificate of a primitive's equations. *)
needs "hol/kernel_strings539.ml";;

let l4_primitive_name619 = new_recursive_definition l4_kprimitive_RECURSION493
 `(l4_primitive_name619 L4KPNatAdd493 = L4String l4_core_nat_name533 [97;100;100]) /\
  (l4_primitive_name619 L4KPNatPred493 = L4String l4_core_nat_name533 [112;114;101;100]) /\
  (l4_primitive_name619 L4KPNatSub493 = L4String l4_core_nat_name533 [115;117;98]) /\
  (l4_primitive_name619 L4KPNatMul493 = L4String l4_core_nat_name533 [109;117;108]) /\
  (l4_primitive_name619 L4KPNatPow493 = L4String l4_core_nat_name533 [112;111;119]) /\
  (l4_primitive_name619 L4KPNatGcd493 = L4String l4_core_nat_name533 [103;99;100]) /\
  (l4_primitive_name619 L4KPNatMod493 = L4String l4_core_nat_name533 [109;111;100]) /\
  (l4_primitive_name619 L4KPNatDiv493 = L4String l4_core_nat_name533 [100;105;118]) /\
  (l4_primitive_name619 L4KPNatBEq493 = L4String l4_core_nat_name533 [98;101;113]) /\
  (l4_primitive_name619 L4KPNatBLE493 = L4String l4_core_nat_name533 [98;108;101]) /\
  (l4_primitive_name619 L4KPNatBitwise493 = L4String l4_core_nat_name533 [98;105;116;119;105;115;101]) /\
  (l4_primitive_name619 L4KPNatLAnd493 = L4String l4_core_nat_name533 [108;97;110;100]) /\
  (l4_primitive_name619 L4KPNatLOr493 = L4String l4_core_nat_name533 [108;111;114]) /\
  (l4_primitive_name619 L4KPNatXor493 = L4String l4_core_nat_name533 [120;111;114]) /\
  (l4_primitive_name619 L4KPNatShiftLeft493 = L4String l4_core_nat_name533 [115;104;105;102;116;76;101;102;116]) /\
  (l4_primitive_name619 L4KPNatShiftRight493 = L4String l4_core_nat_name533 [115;104;105;102;116;82;105;103;104;116]) /\
  (l4_primitive_name619 L4KPCharOfNat493 = l4_core_char_of_nat533) /\
  (l4_primitive_name619 L4KPStringOfList493 = l4_core_string_of_list533)`;;

let l4_primitive_kinds619 = new_definition
 `l4_primitive_kinds619 =
   [L4KPNatAdd493;L4KPNatPred493;L4KPNatSub493;L4KPNatMul493;
    L4KPNatPow493;L4KPNatGcd493;L4KPNatMod493;L4KPNatDiv493;
    L4KPNatBEq493;L4KPNatBLE493;L4KPNatBitwise493;L4KPNatLAnd493;
    L4KPNatLOr493;L4KPNatXor493;L4KPNatShiftLeft493;L4KPNatShiftRight493;
    L4KPCharOfNat493;L4KPStringOfList493]`;;

(* List-first find exposes primitive recursion and retains first-match order. *)
let l4_primitive_lookup_in619 = new_recursive_definition list_RECURSION
 `(l4_primitive_lookup_in619 [] n = NONE) /\
  (l4_primitive_lookup_in619 (CONS op ops) n =
    if n = l4_primitive_name619 op then SOME op else l4_primitive_lookup_in619 ops n)`;;
let l4_primitive_lookup619 = new_definition
 `l4_primitive_lookup619 n = l4_primitive_lookup_in619 l4_primitive_kinds619 n`;;
let l4_primitive_bitwise_name619 = new_definition
 `l4_primitive_bitwise_name619 = L4String l4_core_nat_name533 [98;105;116;119;105;115;101]`;;
let l4_primitive_bool619 = new_definition
 `l4_primitive_bool619 = L4KConst447 l4_core_bool_name533 []`;;
let l4_primitive_char619 = new_definition
 `l4_primitive_char619 = L4KConst447 l4_core_char_name533 []`;;
let l4_primitive_string619 = new_definition
 `l4_primitive_string619 = L4KConst447 l4_core_string_name533 []`;;
let l4_primitive_list_char619 = new_definition
 `l4_primitive_list_char619 =
   L4KApp447 (L4KConst447 l4_core_list_name539 [L4KZero447]) l4_primitive_char619`;;
let l4_primitive_arrow619 = new_definition
 `l4_primitive_arrow619 a b = L4KPi447 L4Anonymous L4KDefault447 a b`;;
let l4_primitive_signature619 = new_definition
 `l4_primitive_signature619 op =
   match op with
   | L4KPNatPred493 -> l4_primitive_arrow619 l4_core_nat533 l4_core_nat533
   | L4KPNatBEq493 -> l4_primitive_arrow619 l4_core_nat533
       (l4_primitive_arrow619 l4_core_nat533 l4_primitive_bool619)
   | L4KPNatBLE493 -> l4_primitive_arrow619 l4_core_nat533
       (l4_primitive_arrow619 l4_core_nat533 l4_primitive_bool619)
   | L4KPNatBitwise493 ->
       l4_primitive_arrow619
         (l4_primitive_arrow619 l4_primitive_bool619
           (l4_primitive_arrow619 l4_primitive_bool619 l4_primitive_bool619))
         (l4_primitive_arrow619 l4_core_nat533
           (l4_primitive_arrow619 l4_core_nat533 l4_core_nat533))
   | L4KPCharOfNat493 -> l4_primitive_arrow619 l4_core_nat533 l4_primitive_char619
   | L4KPStringOfList493 -> l4_primitive_arrow619 l4_primitive_list_char619 l4_primitive_string619
   | _ -> l4_primitive_arrow619 l4_core_nat533
       (l4_primitive_arrow619 l4_core_nat533 l4_core_nat533)`;;
let l4_primitive_zero619 = new_definition
 `l4_primitive_zero619 = L4KConst447 l4_core_zero_name533 []`;;
let l4_primitive_succ619 = new_definition
 `l4_primitive_succ619 e = L4KApp447 (L4KConst447 l4_core_succ_name533 []) e`;;
let l4_primitive_one619 = new_definition
 `l4_primitive_one619 = l4_primitive_succ619 l4_primitive_zero619`;;
let l4_primitive_two619 = new_definition
 `l4_primitive_two619 = l4_primitive_succ619 l4_primitive_one619`;;
let l4_primitive_true619 = new_definition
 `l4_primitive_true619 = L4KConst447 l4_core_true_name533 []`;;
let l4_primitive_false619 = new_definition
 `l4_primitive_false619 = L4KConst447 l4_core_false_name533 []`;;
let l4_primitive_call619 = new_definition
 `l4_primitive_call619 op args =
   l4_kapply_exprs489 args (L4KConst447 (l4_primitive_name619 op) [])`;;

(* Only actual-side metadata is stripped. Pi display names/binder info do not
   affect these shape checks; aliases and other constructors are not unfolded. *)
let l4_primitive_check_signature619 = new_recursive_definition num_RECURSION
 `(l4_primitive_check_signature619 0 actual expected = L4KDecline491 L4KOutOfFuel491) /\
  (l4_primitive_check_signature619 (SUC fuel) actual expected =
    match (actual,expected) with
    | (L4KMData447 a,e) -> l4_primitive_check_signature619 fuel a e
    | (L4KPi447 n bi a b,L4KPi447 m bj c d) ->
        l4_kr_bind491 (l4_primitive_check_signature619 fuel a c)
          (\ignored. l4_primitive_check_signature619 fuel b d)
    | (L4KApp447 a b,L4KApp447 c d) ->
        l4_kr_bind491 (l4_primitive_check_signature619 fuel a c)
          (\ignored. l4_primitive_check_signature619 fuel b d)
    | _ -> if l4_kexpr_eqb480 actual expected then L4KAccept491 one
           else L4KReject491 L4KTypeMismatch491)`;;

let l4_primitive_authenticated619 = new_definition
 `l4_primitive_authenticated619 fuel env op =
   match l4_kfind_decl493 env (l4_primitive_name619 op) with
   | NONE -> L4KReject491 L4KMalformedDeclaration491
   | SOME d ->
     (match (l4_kdecl_kind493 d,l4_kdecl_value493 d) with
      | (L4KDPrimitive493 actual,SOME body) ->
          if l4_kprimitive_eqb493 actual op /\ LENGTH (l4_kdecl_params493 d) = 0
          then l4_primitive_check_signature619 fuel (l4_kdecl_type493 d)
            (l4_primitive_signature619 op)
          else L4KReject491 L4KMalformedDeclaration491
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

let l4_primitive_dependencies619 = new_definition
 `l4_primitive_dependencies619 fuel env op =
   if ~l4_core_nat_ready533 env then L4KReject491 L4KMalformedDeclaration491 else
   match op with
   | L4KPNatSub493 -> l4_primitive_authenticated619 fuel env L4KPNatPred493
   | L4KPNatMul493 -> l4_primitive_authenticated619 fuel env L4KPNatAdd493
   | L4KPNatPow493 -> l4_primitive_authenticated619 fuel env L4KPNatMul493
   | L4KPNatShiftLeft493 -> l4_primitive_authenticated619 fuel env L4KPNatMul493
   | L4KPNatShiftRight493 -> l4_primitive_authenticated619 fuel env L4KPNatDiv493
   | L4KPNatBEq493 -> if l4_core_bool_ready533 env then L4KAccept491 one
                    else L4KReject491 L4KMalformedDeclaration491
   | L4KPNatBLE493 -> if l4_core_bool_ready533 env then L4KAccept491 one
                    else L4KReject491 L4KMalformedDeclaration491
   | _ -> L4KAccept491 one`;;

let l4_primitive_closed619 = new_recursive_definition num_RECURSION
 `(l4_primitive_closed619 0 depth e = L4KDecline491 L4KOutOfFuel491) /\
  (l4_primitive_closed619 (SUC fuel) depth e =
    match e with
    | L4KBVar447 i -> if i < depth then L4KAccept491 one
                     else L4KReject491 L4KLooseBoundVariable491
    | L4KFVar447 n -> L4KReject491 L4KUnknownFreeVariable491
    | L4KMVar447 n -> L4KReject491 L4KMetaVariable491
    | L4KApp447 a b -> l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
        (\ignored. l4_primitive_closed619 fuel depth b)
    | L4KLam447 n bi a b -> l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
        (\ignored. l4_primitive_closed619 fuel (SUC depth) b)
    | L4KPi447 n bi a b -> l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
        (\ignored. l4_primitive_closed619 fuel (SUC depth) b)
    | L4KLet447 n a v b nd -> l4_kr_bind491 (l4_primitive_closed619 fuel depth a)
        (\ignored_type. l4_kr_bind491 (l4_primitive_closed619 fuel depth v)
          (\ignored_value. l4_primitive_closed619 fuel (SUC depth) b))
    | L4KProj447 n i a -> l4_primitive_closed619 fuel depth a
    | L4KMData447 a -> l4_primitive_closed619 fuel depth a
    | _ -> L4KAccept491 one)`;;

let l4_primitive_equation_INDUCT619,l4_primitive_equation_RECURSION619 = define_type
 "l4_primitive_equation619 = L4PrimitiveEquation619 l4_kcontext532 l4_kexpr447 l4_kexpr447";;
let l4_primitive_context619 = new_recursive_definition l4_primitive_equation_RECURSION619
 `l4_primitive_context619 (L4PrimitiveEquation619 g lhs rhs) = g`;;
let l4_primitive_lhs619 = new_recursive_definition l4_primitive_equation_RECURSION619
 `l4_primitive_lhs619 (L4PrimitiveEquation619 g lhs rhs) = lhs`;;
let l4_primitive_rhs619 = new_recursive_definition l4_primitive_equation_RECURSION619
 `l4_primitive_rhs619 (L4PrimitiveEquation619 g lhs rhs) = rhs`;;
let l4_primitive_equation_at619 = new_definition
 `l4_primitive_equation_at619 g lhs rhs = L4PrimitiveEquation619 g lhs rhs`;;
let l4_primitive_x_context619 = new_definition
 `l4_primitive_x_context619 = l4_kpush_binding532 l4_kempty_context532 l4_core_nat533 NONE`;;
let l4_primitive_xy_context619 = new_definition
 `l4_primitive_xy_context619 = l4_kpush_binding532 l4_primitive_x_context619 l4_core_nat533 NONE`;;
