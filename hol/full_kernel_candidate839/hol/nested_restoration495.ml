(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/NestedAdmission.v:8-37; see ../NOTICE495.txt.
   SOURCE ONLY / UNCOMPILED. No executable checker integration. *)
needs "hol/kernel_locals489.ml";;

(* List-first argument order exposes structural recursion. The lookup key is
   the SECOND component for expression/name pairs, FIRST for name/name pairs. *)
let l4_krestore_lookup495 = new_recursive_definition list_RECURSION
 `(l4_krestore_lookup495 ([]:(l4_kexpr447#l4_name)list) n = NONE) /\
 (l4_krestore_lookup495 (CONS entry mapping) n =
   if n = SND entry then SOME (FST entry)
   else l4_krestore_lookup495 mapping n)`;;

let l4_krestore_name495 = new_recursive_definition list_RECURSION
 `(l4_krestore_name495 ([]:(l4_name#l4_name)list) n = n) /\
 (l4_krestore_name495 (CONS entry mapping) n =
   if FST entry = n then SND entry else l4_krestore_name495 mapping n)`;;

(* Guard before HD/TL: unmatched tails on either side are ignored. Only the
   local identifier matters, not its display name, annotation, or type. *)
let l4_klocal_replacement495 = new_recursive_definition list_RECURSION
 `(l4_klocal_replacement495 [] (values:l4_kexpr447 list) n = NONE) /\
 (l4_klocal_replacement495 (CONS p ps) values n =
   if values = [] then NONE
   else if n = l4_klocal_id489 p then SOME (HD values)
   else l4_klocal_replacement495 ps (TL values) n)`;;

(* Total option elimination; this never invokes substitution on the value. *)
let l4_kreplacement_at495 = new_recursive_definition option_RECURSION
 `(l4_kreplacement_at495 NONE n depth = L4KFVar447 n) /\
 (l4_kreplacement_at495 (SOME v) n depth = l4_klift447 v depth 0)`;;

(* Expression-first, then ps, values, depth. Only original FVar occurrences
   are substituted. Original BVars and all reference/display names survive. *)
let l4_kinstantiate_locals495 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kinstantiate_locals495 (L4KBVar447 i) ps values depth = L4KBVar447 i) /\
 (l4_kinstantiate_locals495 (L4KFVar447 n) ps values depth =
   l4_kreplacement_at495 (l4_klocal_replacement495 ps values n) n depth) /\
 (l4_kinstantiate_locals495 (L4KMVar447 n) ps values depth = L4KMVar447 n) /\
 (l4_kinstantiate_locals495 (L4KSort447 u) ps values depth = L4KSort447 u) /\
 (l4_kinstantiate_locals495 (L4KConst447 n us) ps values depth = L4KConst447 n us) /\
 (l4_kinstantiate_locals495 (L4KApp447 f a) ps values depth =
   L4KApp447 (l4_kinstantiate_locals495 f ps values depth)
     (l4_kinstantiate_locals495 a ps values depth)) /\
 (l4_kinstantiate_locals495 (L4KLam447 n bi a b) ps values depth =
   L4KLam447 n bi (l4_kinstantiate_locals495 a ps values depth)
     (l4_kinstantiate_locals495 b ps values (SUC depth))) /\
 (l4_kinstantiate_locals495 (L4KPi447 n bi a b) ps values depth =
   L4KPi447 n bi (l4_kinstantiate_locals495 a ps values depth)
     (l4_kinstantiate_locals495 b ps values (SUC depth))) /\
 (l4_kinstantiate_locals495 (L4KLet447 n a v b nd) ps values depth =
   L4KLet447 n (l4_kinstantiate_locals495 a ps values depth)
     (l4_kinstantiate_locals495 v ps values depth)
     (l4_kinstantiate_locals495 b ps values (SUC depth)) nd) /\
 (l4_kinstantiate_locals495 (L4KNatLit447 nat_value495) ps values depth = L4KNatLit447 nat_value495) /\
 (l4_kinstantiate_locals495 (L4KStrLit447 s) ps values depth = L4KStrLit447 s) /\
 (l4_kinstantiate_locals495 (L4KProj447 n i a) ps values depth =
   L4KProj447 n i (l4_kinstantiate_locals495 a ps values depth)) /\
 (l4_kinstantiate_locals495 (L4KMData447 a) ps values depth =
   L4KMData447 (l4_kinstantiate_locals495 a ps values depth))`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_instantiate_locals_nat899 = prove
 (`!m ps values depth.
    l4_kinstantiate_locals495 (L4KNatLit447 m) ps values depth = L4KNatLit447 m`,
  REWRITE_TAC[l4_kinstantiate_locals495]);;

let l4_instantiate_locals_name899 = prove
 (`!name values depth.
    l4_kinstantiate_locals495 (L4KFVar447 name) [] values depth = L4KFVar447 name`,
  REWRITE_TAC[l4_kinstantiate_locals495;l4_klocal_replacement495;l4_kreplacement_at495]);;
