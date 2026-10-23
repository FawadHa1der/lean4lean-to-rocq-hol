(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447/493/607 port of rocq/Safety.v9-109.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE624.txt and ../INTERFACE624.txt.
   Checking-local views never replace the persistent restricted markers. *)
needs "hol/ordinary_admission620.ml";;

let l4_safety_eqb624 = new_definition
 `l4_safety_eqb624 (a:l4_input_safety607) b <=> a = b`;;

let l4_checking_view624 = new_definition
 `l4_checking_view624 mode d =
   let kind =
     match (l4_kdecl_kind493 d,mode) with
     | (L4KDUnsafe493 inner,L4InputUnsafe607) -> inner
     | (L4KDPartial493,L4InputPartial607) -> L4KDDefinition493
     | (L4KDPartial493,L4InputUnsafe607) -> L4KDDefinition493
     | (k,m) -> k in
   L4KDeclaration493 (l4_kdecl_name493 d) (l4_kdecl_params493 d)
     (l4_kdecl_type493 d) (l4_kdecl_value493 d) kind (l4_kdecl_hints493 d)`;;
let l4_safety_environment624 = new_definition
 `l4_safety_environment624 mode env = MAP (l4_checking_view624 mode) env`;;
let l4_safety_kind624 = new_recursive_definition l4_input_safety_RECURSION607
 `(l4_safety_kind624 L4InputSafe607 = L4KDDefinition493) /\
  (l4_safety_kind624 L4InputPartial607 = L4KDPartial493) /\
  (l4_safety_kind624 L4InputUnsafe607 = L4KDUnsafe493 L4KDDefinition493)`;;
let l4_safe_name624 = new_definition
 `l4_safe_name624 n =
   if l4_name_mem437 n l4_reserved_names607 then L4KReject491 L4KMalformedDeclaration491
   else L4KAccept491 one`;;
let l4_check_value624 = new_definition
 `l4_check_value624 fuel env ps ty value =
   if l4_kscoped447 value 0 then l4_check597 fuel env ps l4_kempty_context532 value ty
   else L4KReject491 L4KMalformedDeclaration491`;;
let l4_restricted_constant624 = new_definition
 `l4_restricted_constant624 n ps ty body kind =
   L4KDeclaration493 n ps ty body kind L4KHintOpaque493`;;
let l4_restricted_definition624 = new_definition
 `l4_restricted_definition624 hints n ps ty value kind =
   L4KDeclaration493 n ps ty (SOME value) kind hints`;;

let l4_admit_extended624 = new_definition
 `l4_admit_extended624 fuel env input =
   match input with
   | L4InputAxiom607 n ps ty T ->
       l4_kr_bind491 (l4_safe_name624 n) (\name_ok.
         let view = l4_safety_environment624 L4InputUnsafe607 env in
         l4_kr_bind491 (l4_check_header607 fuel view n ps ty) (\header.
           L4KAccept491 (CONS
             (l4_restricted_constant624 n ps ty NONE (L4KDUnsafe493 L4KDAssumption493)) env)))
   | L4InputDefinition607 hints n ps ty value L4InputUnsafe607 ->
       l4_kr_bind491 (l4_safe_name624 n) (\name_ok.
         let view = l4_safety_environment624 L4InputUnsafe607 env in
         l4_kr_bind491 (l4_check_header607 fuel view n ps ty) (\header.
           let self = l4_restricted_constant624 n ps ty NONE L4KDAssumption493 in
           l4_kr_bind491 (l4_check_value624 fuel (CONS self view) ps ty value) (\checked.
             L4KAccept491 (CONS (l4_restricted_definition624 hints n ps ty value
               (L4KDUnsafe493 L4KDDefinition493)) env))))
   | L4InputDefinition607 hints n ps ty value L4InputPartial607 ->
       l4_kr_bind491 (l4_safe_name624 n) (\name_ok.
         l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header.
           l4_kr_bind491 (l4_check_value624 fuel env ps ty value) (\checked.
             L4KAccept491 (CONS
               (l4_restricted_definition624 hints n ps ty value L4KDPartial493) env))))
   | L4InputOpaque607 n ps ty value T ->
       l4_kr_bind491 (l4_safe_name624 n) (\name_ok.
         l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header.
           l4_kr_bind491 (l4_check_value624 fuel env ps ty value) (\checked.
             L4KAccept491 (CONS (l4_restricted_constant624 n ps ty (SOME value)
               (L4KDUnsafe493 L4KDOpaque493)) env))))
   | _ -> l4_admit620 fuel env input`;;

let l4_mutual_name624 = new_definition
 `l4_mutual_name624 input =
   match input with
   | L4InputDefinition607 hints n ps ty value safety -> n
   | _ -> L4Anonymous`;;

(* List-first adapters; each entry receives the same checker fuel. Headers
   deliberately use the unchanged view, not earlier generated placeholders. *)
let l4_check_mutual_headers624 = new_recursive_definition list_RECURSION
 `(l4_check_mutual_headers624 [] fuel view ps mode = L4KAccept491 []) /\
  (l4_check_mutual_headers624 (CONS input inputs) fuel view ps mode =
    match input with
    | L4InputDefinition607 hints n qs ty value safety ->
        if ~(l4_safety_eqb624 safety mode /\ qs = ps)
        then L4KReject491 L4KMalformedDeclaration491 else
        l4_kr_bind491 (l4_safe_name624 n) (\name_ok.
          l4_kr_bind491 (l4_check_header607 fuel view n ps ty) (\header.
            l4_kr_bind491 (l4_check_mutual_headers624 inputs fuel view ps mode) (\rest.
              L4KAccept491 (CONS (l4_restricted_constant624 n ps ty NONE L4KDAssumption493) rest))))
    | _ -> L4KReject491 L4KMalformedDeclaration491)`;;
let l4_check_mutual_values624 = new_recursive_definition list_RECURSION
 `(l4_check_mutual_values624 [] fuel view = L4KAccept491 []) /\
  (l4_check_mutual_values624 (CONS input inputs) fuel view =
    match input with
    | L4InputDefinition607 hints n ps ty value safety ->
        l4_kr_bind491 (l4_check_value624 fuel view ps ty value) (\checked.
          l4_kr_bind491 (l4_check_mutual_values624 inputs fuel view) (\rest.
            L4KAccept491 (CONS
              (l4_restricted_definition624 hints n ps ty value (l4_safety_kind624 safety)) rest)))
    | _ -> L4KReject491 L4KMalformedDeclaration491)`;;
let l4_admit_mutual624 = new_definition
 `l4_admit_mutual624 fuel env inputs =
   match inputs with
   | CONS (L4InputDefinition607 hints n ps ty value mode) rest ->
       if l4_safety_eqb624 mode L4InputSafe607
       then L4KReject491 L4KMalformedDeclaration491 else
       if ~l4_names_unique437 (MAP l4_mutual_name624 inputs)
       then L4KReject491 L4KDuplicateDeclaration491 else
       let view = l4_safety_environment624 mode env in
       l4_kr_bind491 (l4_check_mutual_headers624 inputs fuel view ps mode) (\placeholders.
         l4_kr_bind491 (l4_check_mutual_values624 inputs fuel (APPEND placeholders view))
           (\generated. L4KAccept491 (APPEND generated env)))
   | _ -> L4KReject491 L4KMalformedDeclaration491`;;
