(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/InductiveSafety.v9-27.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE633.txt and ../INTERFACE633.txt.
   Uses the actual634 nested driver, pending independent source review.
   No input metadata, safety view or callback supplies an admission verdict. *)
needs "hol/safety_admission624.ml";;
needs "hol/nested_admission634.ml";;

let l4_mark_unsafe_inductive633 = new_definition
 `l4_mark_unsafe_inductive633 d =
   L4KDeclaration493 (l4_kdecl_name493 d) (l4_kdecl_params493 d)
     (l4_kdecl_type493 d) (l4_kdecl_value493 d)
     (L4KDUnsafe493 (l4_kdecl_kind493 d)) (l4_kdecl_hints493 d)`;;

let l4_inductive_input_unsafe633 = new_definition
 `l4_inductive_input_unsafe633 types <=>
   match types with
   | [] -> F
   | CONS d rest ->
       (match l4_kdecl_kind493 d with
        | L4KDInductive493 info -> l4_kind_is_unsafe493 info
        | _ -> F)`;;

(* Filtering uses the persistent original env, never its permissive view.
   Only new declarations are marked; the original tail is retained verbatim. *)
let l4_admit_inductive_extended633 = new_definition
 `l4_admit_inductive_extended633 fuel env types ctors recs =
   if l4_inductive_input_unsafe633 types then
     let view = l4_safety_environment624 L4InputUnsafe607 env in
     l4_kr_bind491 (l4_admit_inductive_nested634 fuel view types ctors recs) (\next.
       let generated = FILTER
         (\d. match l4_kfind_decl493 env (l4_kdecl_name493 d) with
              | NONE -> T
              | SOME old -> F) next in
       L4KAccept491 (APPEND (MAP l4_mark_unsafe_inductive633 generated) env))
   else l4_admit_inductive_nested634 fuel env types ctors recs`;;
