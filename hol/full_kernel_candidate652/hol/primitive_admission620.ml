(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/Primitives.v144-189,712-772.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE620.txt and ../CONTRACT620.txt.
   No candidate verdict or proof callback is supplied by the caller. *)
needs "hol/primitive_foundations619.ml";;
needs "hol/kernel_checker597.ml";;
needs "hol/primitive_reflection621.ml";;
needs "hol/primitive_recursors622.ml";;

(* Equations use the candidate body at arbitrary de Bruijn variables. Calls
   to reserved names occur only for the separately authenticated dependencies. *)
let l4_primitive_equations620 = new_definition
 `l4_primitive_equations620 op body =
   let eq0 = l4_primitive_equation_at619 l4_kempty_context532 in
   let eqx = l4_primitive_equation_at619 l4_primitive_x_context619 in
   let eqxy = l4_primitive_equation_at619 l4_primitive_xy_context619 in
   let f = \x y. l4_kapply_exprs489 [x;y] body in
   let x = L4KBVar447 0 in
   let xx = L4KBVar447 1 in
   let y = L4KBVar447 0 in
   let base = \z. eqx (f x l4_primitive_zero619) z in
   let step = \z. eqxy (f xx (l4_primitive_succ619 y)) z in
   match op with
   | L4KPNatAdd493 -> SOME [base x;step (l4_primitive_succ619 (f xx y))]
   | L4KPNatPred493 -> SOME
       [eq0 (L4KApp447 body l4_primitive_zero619) l4_primitive_zero619;
        eqx (L4KApp447 body (l4_primitive_succ619 x)) x]
   | L4KPNatSub493 -> SOME
       [base x;step (l4_primitive_call619 L4KPNatPred493 [f xx y])]
   | L4KPNatMul493 -> SOME
       [base l4_primitive_zero619;
        step (l4_primitive_call619 L4KPNatAdd493 [f xx y;xx])]
   | L4KPNatPow493 -> SOME
       [base l4_primitive_one619;
        step (l4_primitive_call619 L4KPNatMul493 [f xx y;xx])]
   | L4KPNatShiftLeft493 -> SOME
       [base x;step (f (l4_primitive_call619 L4KPNatMul493 [l4_primitive_two619;xx]) y)]
   | L4KPNatShiftRight493 -> SOME
       [base x;step (l4_primitive_call619 L4KPNatDiv493 [f xx y;l4_primitive_two619])]
   | L4KPNatBEq493 -> SOME
       [eq0 (f l4_primitive_zero619 l4_primitive_zero619) l4_primitive_true619;
        eqx (f l4_primitive_zero619 (l4_primitive_succ619 x)) l4_primitive_false619;
        eqx (f (l4_primitive_succ619 x) l4_primitive_zero619) l4_primitive_false619;
        eqxy (f (l4_primitive_succ619 xx) (l4_primitive_succ619 y)) (f xx y)]
   | L4KPNatBLE493 -> SOME
       [eq0 (f l4_primitive_zero619 l4_primitive_zero619) l4_primitive_true619;
        eqx (f l4_primitive_zero619 (l4_primitive_succ619 x)) l4_primitive_true619;
        eqx (f (l4_primitive_succ619 x) l4_primitive_zero619) l4_primitive_false619;
        eqxy (f (l4_primitive_succ619 xx) (l4_primitive_succ619 y)) (f xx y)]
   | _ -> NONE`;;

(* List-first differs from Rocq's steps/fuel/env/list order. Only steps falls;
   each typed comparison receives the original fuel and empty universe list. *)
let l4_primitive_check_equations620 = new_recursive_definition list_RECURSION
 `(l4_primitive_check_equations620 [] steps fuel env = L4KAccept491 one) /\
  (l4_primitive_check_equations620 (CONS e es) steps fuel env =
    if steps = 0 then L4KDecline491 L4KOutOfFuel491 else
    l4_kr_bind491
      (l4_check_defeq597 fuel env [] (l4_primitive_context619 e)
        (l4_primitive_lhs619 e) (l4_primitive_rhs619 e))
      (\checked. l4_primitive_check_equations620 es (steps - 1) fuel env))`;;

let l4_primitive_is_text620 = new_definition
 `l4_primitive_is_text620 op <=>
   match op with
   | L4KPCharOfNat493 -> T
   | L4KPStringOfList493 -> T
   | _ -> F`;;

(* Rocq uses sort_of(checker ...), not the public guarded whnf wrapper. *)
let l4_primitive_ensure_type620 = new_definition
 `l4_primitive_ensure_type620 fuel env e =
   l4_kr_bind491
     (l4_sort_of543 (l4_checker597 fuel env []) l4_kempty_context532 e)
     (\sort. L4KAccept491 one)`;;

let l4_primitive_check_text_interface620 = new_definition
 `l4_primitive_check_text_interface620 fuel env op =
   match op with
   | L4KPCharOfNat493 ->
       if l4_core_nat_ready533 env
       then l4_primitive_ensure_type620 fuel env l4_primitive_char619
       else L4KReject491 L4KMalformedDeclaration491
   | L4KPStringOfList493 ->
       l4_kr_bind491 (l4_primitive_ensure_type620 fuel env l4_primitive_list_char619) (\list_ty.
         l4_kr_bind491 (l4_primitive_ensure_type620 fuel env l4_primitive_char619) (\char_ty.
           l4_kr_bind491
             (l4_check597 fuel env [] l4_kempty_context532
               (L4KApp447
                 (L4KConst447 (L4String l4_core_list_name539 [110;105;108]) [L4KZero447])
                 l4_primitive_char619)
               l4_primitive_list_char619)
             (\nil_checked.
               l4_check597 fuel env [] l4_kempty_context532
                 (L4KApp447
                   (L4KConst447 (L4String l4_core_list_name539 [99;111;110;115]) [L4KZero447])
                   l4_primitive_char619)
                 (l4_primitive_arrow619 l4_primitive_char619
                   (l4_primitive_arrow619 l4_primitive_list_char619 l4_primitive_list_char619)))))
   | _ -> L4KAccept491 one`;;

let l4_primitive_check_nat_equations620 = new_definition
 `l4_primitive_check_nat_equations620 fuel env op body =
   match l4_primitive_equations620 op body with
   | SOME equations ->
       l4_kr_bind491 (l4_primitive_dependencies619 fuel env op) (\dependencies_checked.
         l4_primitive_check_equations620 equations fuel fuel env)
   | NONE ->
       (match op with
        | L4KPNatMod493 -> l4_primitive_check_fuel_rec621 fuel env T body
        | L4KPNatDiv493 -> l4_primitive_check_fuel_rec621 fuel env F body
        | L4KPNatGcd493 -> l4_primitive_check_gcd622 fuel env body
        | L4KPNatBitwise493 -> l4_primitive_check_bitwise622 fuel env body
        | L4KPNatLAnd493 -> l4_primitive_check_bitwise_instance622 fuel env op body
        | L4KPNatLOr493 -> l4_primitive_check_bitwise_instance622 fuel env op body
        | L4KPNatXor493 -> l4_primitive_check_bitwise_instance622 fuel env op body
        | _ -> L4KDecline491 L4KUnsupportedDeclaration491)`;;

(* Internal classification assumes the admission driver has checked body:ty.
   Text primitives retain their deliberate interface-only certificate path. *)
let l4_classify_primitive620 = new_definition
 `l4_classify_primitive620 fuel env n (params:l4_name list) ty body =
   match l4_primitive_lookup619 n with
   | NONE ->
       if l4_name_mem437 n
         [l4_core_nat_name533;l4_core_zero_name533;l4_core_succ_name533;
          l4_core_bool_name533;l4_core_false_name533;l4_core_true_name533]
       then L4KReject491 L4KMalformedDeclaration491 else L4KAccept491 NONE
   | SOME op ->
       l4_kr_bind491
         (match l4_kfind_decl493 env n with
          | NONE -> L4KAccept491 one
          | SOME d -> L4KReject491 L4KDuplicateDeclaration491)
         (\not_duplicate.
           l4_kr_bind491
             (if LENGTH params = 0 then L4KAccept491 one else L4KReject491 L4KUniverseArity491)
             (\arity_checked.
               l4_kr_bind491
                 (l4_primitive_check_signature619 fuel ty (l4_primitive_signature619 op))
                 (\signature_checked.
                   l4_kr_bind491 (l4_primitive_closed619 fuel 0 body) (\closed.
                     l4_kr_bind491
                       (if l4_primitive_is_text620 op
                        then l4_primitive_check_text_interface620 fuel env op
                        else l4_primitive_check_nat_equations620 fuel env op body)
                       (\certificate_checked. L4KAccept491 (SOME op))))))`;;
