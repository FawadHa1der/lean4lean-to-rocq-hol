(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of Syntax.v56-63 and Checker.v136-160,801-816.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE528.txt. Not environment admission. *)
needs "hol/kernel_universes488.ml";;
needs "hol/nested_parameters491.ml";;
needs "hol/kernel_declarations493.ml";;

let l4_level_wf528 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_level_wf528 ps L4KZero447 <=> T) /\
  (l4_level_wf528 ps (L4KSucc447 u) <=> l4_level_wf528 ps u) /\
  (l4_level_wf528 ps (L4KMax447 u v) <=> l4_level_wf528 ps u /\ l4_level_wf528 ps v) /\
  (l4_level_wf528 ps (L4KIMax447 u v) <=> l4_level_wf528 ps u /\ l4_level_wf528 ps v) /\
  (l4_level_wf528 ps (L4KParam447 n) <=> l4_name_mem437 n ps) /\
  (l4_level_wf528 ps (L4KLevelMVar447 n) <=> F)`;;

(* Meta-variable rejection takes precedence within ONE universe expression.
   The list checker below still preserves the first failing list element. *)
let l4_check_level528 = new_definition
 `l4_check_level528 ps u =
   if l4_klevel_meta447 u then L4KReject491 L4KMetaVariable491
   else if l4_level_wf528 ps u then L4KAccept491 one
   else L4KReject491 L4KUnknownUniverse491`;;

let l4_check_levels528 = new_recursive_definition list_RECURSION
 `(l4_check_levels528 ps [] = L4KAccept491 one) /\
  (l4_check_levels528 ps (CONS u us) =
    l4_kr_bind491 (l4_check_level528 ps u) (\ignored. l4_check_levels528 ps us))`;;

let l4_get_constant528 = new_definition
 `l4_get_constant528 env ps n us =
   match l4_kfind_decl493 env n with
   | NONE -> L4KReject491 L4KUnknownConstant491
   | SOME d ->
     match l4_kdecl_kind493 d with
     | L4KDUnsupported493 -> L4KDecline491 L4KUnsupportedDeclaration491
     | L4KDUnsafe493 role -> L4KReject491 L4KMalformedDeclaration491
     | L4KDPartial493 -> L4KReject491 L4KMalformedDeclaration491
     | _ ->
       if LENGTH (l4_kdecl_params493 d) = LENGTH us then
         l4_kr_bind491 (l4_check_levels528 ps us) (\ignored. L4KAccept491 d)
       else L4KReject491 L4KUniverseArity491`;;

(* A single delta step, not WHNF: no beta reduction, recursive unfolding or
   metadata stripping occurs here. Hints do not decide this primitive step. *)
let l4_core_unfold528 = new_definition
 `l4_core_unfold528 env ps e =
   let spine = l4_ksplit_app489 e in
   match FST spine with
   | L4KConst447 n us ->
     l4_kr_bind491 (l4_get_constant528 env ps n us)
       (\d. let reducible =
          match l4_kdecl_kind493 d with
          | L4KDDefinition493 -> T
          | L4KDTheorem493 -> T
          | L4KDPrimitive493 p -> T
          | _ -> F in
        if reducible then
          match l4_kdecl_value493 d with
          | NONE -> L4KReject491 L4KMalformedDeclaration491
          | SOME value ->
            L4KAccept491 (SOME (l4_kapply_exprs489 (SND spine)
              (if l4_kdecl_params493 d = [] then value
               else l4_ksubst_levels488 (l4_kdecl_params493 d) us value)))
        else L4KAccept491 NONE)
   | _ -> L4KAccept491 NONE`;;
