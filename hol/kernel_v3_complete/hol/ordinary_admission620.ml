(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447/491/493 port of rocq/Declarations.v68-105.
   SOURCE ONLY / UNCOMPILED. Actual classification is imported below, never
   supplied as a callback. No restricted/mutual safety admission is claimed. *)
needs "hol/ordinary_admission607.ml";;
needs "hol/primitive_admission620.ml";;

(* Safe definitions are the only changed607 branch. Preserve both the typed
   body check before classification and the caller's hints in the new record. *)
let l4_admit620 = new_definition
 `l4_admit620 fuel env input =
   match input with
   | L4InputDefinition607 hints n ps ty body L4InputSafe607 ->
       l4_kr_bind491 (l4_check_header607 fuel env n ps ty) (\header_checked.
         l4_kr_bind491
           (if l4_kscoped447 body 0 then L4KAccept491 one
            else L4KReject491 L4KMalformedDeclaration491)
           (\scope_checked.
             l4_kr_bind491 (l4_check597 fuel env ps l4_kempty_context532 body ty) (\body_checked.
               l4_kr_bind491 (l4_classify_primitive620 fuel env n ps ty body) (\primitive.
                 let kind = match primitive with
                   | SOME op -> L4KDPrimitive493 op
                   | NONE -> L4KDDefinition493 in
                 L4KAccept491 (CONS (L4KDeclaration493 n ps ty (SOME body) kind hints) env)))))
   | _ -> l4_admit_basic607 fuel env input`;;

(* List-first for HOL primitive recursion; Rocq is fuel/env/inputs. *)
let l4_check_declarations620 = new_recursive_definition list_RECURSION
 `(l4_check_declarations620 [] fuel env = L4KAccept491 env) /\
  (l4_check_declarations620 (CONS input inputs) fuel env =
    l4_kr_bind491 (l4_admit620 fuel env input)
      (\next. l4_check_declarations620 inputs fuel next))`;;
