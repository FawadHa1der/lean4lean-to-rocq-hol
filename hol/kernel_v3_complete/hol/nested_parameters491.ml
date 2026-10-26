(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of Syntax.v, InductiveUtils.v and NestedTransform.v.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE491.txt. *)
needs "hol/kernel_locals489.ml";;
needs "hol/nested_allocation437.ml";;

(* Full local Rocq result vocabulary. Helper success is a returned value,
   never a declaration-acceptance theorem. Invalidity and inability differ. *)
let l4_kreject_INDUCT491,l4_kreject_RECURSION491 = define_type
 "l4_kreject491 = L4KUnknownConstant491 | L4KUnknownFreeVariable491 |
 L4KLooseBoundVariable491 | L4KUnknownUniverse491 | L4KUniverseArity491 |
 L4KExpectedSort491 | L4KExpectedPi491 | L4KTypeMismatch491 |
 L4KNotDefinitionallyEqual491 | L4KDuplicateDeclaration491 |
 L4KDuplicateUniverse491 | L4KMalformedDeclaration491 | L4KMetaVariable491";;

let l4_kdecline_INDUCT491,l4_kdecline_RECURSION491 = define_type
 "l4_kdecline491 = L4KOutOfFuel491 | L4KUnsupportedExpression491 | L4KUnsupportedDeclaration491";;

let l4_kresult_INDUCT491,l4_kresult_RECURSION491 = define_type
 "l4_kresult491 = L4KAccept491 A | L4KReject491 l4_kreject491 | L4KDecline491 l4_kdecline491";;

let l4_kr_bind491 = new_recursive_definition l4_kresult_RECURSION491
 `(l4_kr_bind491 (L4KAccept491 x) f = f x) /\
 (l4_kr_bind491 (L4KReject491 reason) f = L4KReject491 reason) /\
 (l4_kr_bind491 (L4KDecline491 decline_reason491) f = L4KDecline491 decline_reason491)`;;

let l4_kr_from_na491 = new_recursive_definition l4_na_result_RECURSION437
 `(l4_kr_from_na491 (L4NAOk437 x) = L4KAccept491 x) /\
 (l4_kr_from_na491 L4NAOutOfFuel437 = L4KDecline491 L4KOutOfFuel491) /\
 (l4_kr_from_na491 L4NAUnsupported437 = L4KDecline491 L4KUnsupportedDeclaration491)`;;

let l4_kbinding_INDUCT491,l4_kbinding_RECURSION491 = define_type
 "l4_kbinding491 = L4KBinding491 l4_kexpr447 (l4_kexpr447 option)";;

(* ind_state's context fields are flattened, retaining both full lists. *)
let l4_kstate_INDUCT491,l4_kstate_RECURSION491 = define_type
 "l4_kstate491 = L4KState491 num (l4_kbinding491 list) ((l4_name # l4_kbinding491) list)";;

let l4_kstate_next491 = new_recursive_definition l4_kstate_RECURSION491
 `l4_kstate_next491 (L4KState491 next bound free) = next`;;
let l4_kstate_bound491 = new_recursive_definition l4_kstate_RECURSION491
 `l4_kstate_bound491 (L4KState491 next bound free) = bound`;;
let l4_kstate_free491 = new_recursive_definition l4_kstate_RECURSION491
 `l4_kstate_free491 (L4KState491 next bound free) = free`;;

let l4_kinitial_state491 = new_definition
 `l4_kinitial_state491 = L4KState491 0 [] []`;;

let l4_kind_id491 = new_definition
 `l4_kind_id491 next = L4Numeric (L4String L4Anonymous [95;114;111;99;113;95;105;110;100]) next`;;

let l4_kind_fresh491 = new_recursive_definition l4_kstate_RECURSION491
 `l4_kind_fresh491 (L4KState491 next bound free) user bi ty =
   (L4KLocal489 (l4_kind_id491 next) user bi ty,
    L4KState491 (SUC next) bound
      (CONS (l4_kind_id491 next,L4KBinding491 ty NONE) free))`;;

(* No normalization or domain check: these are raw parameter Pis, matching
   nested_open_params, not the separately checked admission telescope. *)
let l4_nested_open_params491 = new_recursive_definition num_RECURSION
 `(l4_nested_open_params491 0 fuel state ty = L4KAccept491 ([],ty,state)) /\
 (l4_nested_open_params491 (SUC count) fuel state ty =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   match ty with
   | L4KPi447 user bi domain body ->
       let fresh = l4_kind_fresh491 state user bi domain in
       l4_kr_bind491
         (l4_nested_open_params491 count (fuel - 1) (SND fresh)
           (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
         (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))
   | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

let l4_nested_instantiate_params491 = new_recursive_definition list_RECURSION
 `(l4_nested_instantiate_params491 [] fuel ty = L4KAccept491 ty) /\
 (l4_nested_instantiate_params491 (CONS arg args) fuel ty =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   match ty with
   | L4KPi447 user bi domain body ->
       l4_nested_instantiate_params491 args (fuel - 1) (l4_kinst447 body arg)
   | _ -> L4KDecline491 L4KUnsupportedDeclaration491)`;;
