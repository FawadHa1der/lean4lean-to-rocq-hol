(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED. Missing list-concatenation constant for frozen498.
   Conservatively defined from stock list_RECURSION and APPEND, no new type.
   Load before ANY path reaching nested_family498.ml. See COMPATIBILITY650. *)
needs "lists.ml";;

(* Do not silently adopt an unrelated constant from an unreviewed session.
   Repeated ordinary needs of this same file is handled by HOL's loader. *)
let () =
  if can get_const_type "FLAT" then
    failwith "flatten650: FLAT already exists; use a fresh reviewed source selection";;

let l4_flat650 = new_recursive_definition list_RECURSION
 `(FLAT ([]:(A list)list) = []) /\
  (FLAT (CONS (xs:A list) xss) = APPEND xs (FLAT xss))`;;

(* Add only this defining theorem to the future canonical computation registry.
   The proposed properties/fixture expectations are not evaluator inputs. *)
let l4_flat_equations650 = [l4_flat650];;
