(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed pure HOL port of rocq/Checker.v490-515,585-589.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE557.txt. No admission claim. *)
needs "hol/kernel_context532.ml";;
needs "hol/nested_candidate494.ml";;

(* Recurse on the requested position, never instantiate or normalize a body.
   A Const head need not denote an inductive declaration in any environment. *)
let l4_core_major_induct557 = new_recursive_definition num_RECURSION
 `(l4_core_major_induct557 0 ty =
    match ty with
    | L4KPi447 n bi domain body ->
        (match FST (l4_ksplit_app489 domain) with
         | L4KConst447 owner us -> SOME owner
         | _ -> NONE)
    | _ -> NONE) /\
  (l4_core_major_induct557 (SUC idx) ty =
    match ty with
    | L4KPi447 n bi domain body -> l4_core_major_induct557 idx body
    | _ -> NONE)`;;

(* Total MAP (projection owner value) (seq start count), in ascending order. *)
let l4_core_project_fields557 = new_recursive_definition num_RECURSION
 `(l4_core_project_fields557 0 start owner value = []) /\
  (l4_core_project_fields557 (SUC count) start owner value =
    CONS (L4KProj447 owner start value)
      (l4_core_project_fields557 count (SUC start) owner value))`;;

(* Deliberately no core_structure/admission/type/universe/arity/owner test.
   Exact-kind, first-shadow lookup and a singleton constructor list suffice. *)
let l4_core_make_structure557 = new_definition
 `l4_core_make_structure557 env owner us args value =
   match l4_core_inductive532 env owner with
   | NONE -> NONE
   | SOME info ->
       (match l4_kind_ctors493 info with
        | [ctor] ->
            (match l4_core_constructor532 env ctor with
             | NONE -> NONE
             | SOME c -> SOME
                 (l4_kapply_exprs489
                   (APPEND (l4_kfirstn494 args (l4_kctor_num_params493 c))
                     (l4_core_project_fields557 (l4_kctor_num_fields493 c)
                       0 owner value))
                   (L4KConst447 ctor us)))
        | _ -> NONE)`;;

let l4_core_find_rule557 = new_recursive_definition list_RECURSION
 `(l4_core_find_rule557 n [] = NONE) /\
  (l4_core_find_rule557 n (CONS r rules) =
    if n = l4_krule_ctor493 r then SOME r else l4_core_find_rule557 n rules)`;;
