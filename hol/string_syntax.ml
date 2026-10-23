(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Expansion adapted from pinned Lean4Lean/Expr.lean:strLitToConstructor. *)
needs "hol/text_contracts.ml";;

let l4_unicode_scalar = new_definition
 `l4_unicode_scalar c <=> c < 1114112 /\ ~(55296 <= c /\ c < 57344)`;;
let l4_string_chars = new_recursive_definition list_RECURSION
 `(l4_string_chars [] = l4_text_nil) /\
  (l4_string_chars (CONS c cs) = L4App
    (L4App l4_text_cons (L4App (L4Const l4_text_of_nat_name []) (L4NatLit c)))
    (l4_string_chars cs))`;;
let l4_string_expand = new_definition
 `l4_string_expand cs = L4App (L4Const l4_text_of_list_name []) (l4_string_chars cs)`;;
