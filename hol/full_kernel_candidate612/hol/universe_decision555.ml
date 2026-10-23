(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of local rocq/Universes.v and Checker.v40-46.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE555.txt. No default integration. *)
needs "hol/nested_parameters491.ml";;

let l4_ksublevel_INDUCT555,l4_ksublevel_RECURSION555 = define_type
 "l4_ksublevel555 = L4KSubConst555 (l4_name list) num |
  L4KSubVar555 (l4_name list) l4_name num";;

let l4_klevel_eval555 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_klevel_eval555 L4KZero447 rho = 0) /\
  (l4_klevel_eval555 (L4KSucc447 u) rho = SUC (l4_klevel_eval555 u rho)) /\
  (l4_klevel_eval555 (L4KMax447 u v) rho =
    MAX (l4_klevel_eval555 u rho) (l4_klevel_eval555 v rho)) /\
  (l4_klevel_eval555 (L4KIMax447 u v) rho =
    if l4_klevel_eval555 v rho = 0 then 0
    else MAX (l4_klevel_eval555 u rho) (l4_klevel_eval555 v rho)) /\
  (l4_klevel_eval555 (L4KParam447 n) rho = rho n) /\
  (l4_klevel_eval555 (L4KLevelMVar447 n) rho = 0)`;;

let l4_kguard_insert555 = new_definition
 `l4_kguard_insert555 n path =
   if l4_name_mem437 n path then path else CONS n path`;;
let l4_kconst_atom555 = new_definition
 `l4_kconst_atom555 (path:l4_name list) k =
   if k = 0 then [] else [L4KSubConst555 path k]`;;
let l4_kcombine_levels555 = new_definition
 `l4_kcombine_levels555 a b =
   l4_kr_bind491 a (\xs:l4_ksublevel555 list.
     l4_kr_bind491 b (\ys. L4KAccept491 (APPEND xs ys)))`;;

(* Fuel decreases on transformed IMAX terms. The wrapper below, not this
   raw function, checks for metas in branches which normalization can erase. *)
let l4_knormalize_aux555 = new_recursive_definition num_RECURSION
 `(l4_knormalize_aux555 0 (u:l4_klevel447) (path:l4_name list) k =
    L4KDecline491 L4KOutOfFuel491) /\
  (l4_knormalize_aux555 (SUC fuel) u path k =
    match u with
    | L4KZero447 -> L4KAccept491 (l4_kconst_atom555 path k)
    | L4KSucc447 v -> l4_knormalize_aux555 fuel v path (SUC k)
    | L4KMax447 a b ->
      l4_kcombine_levels555 (l4_knormalize_aux555 fuel a path k)
        (l4_knormalize_aux555 fuel b path k)
    | L4KParam447 n -> L4KAccept491
      (APPEND (l4_kconst_atom555 path k)
        [L4KSubVar555 (l4_kguard_insert555 n path) n k])
    | L4KLevelMVar447 n -> L4KReject491 L4KMetaVariable491
    | L4KIMax447 a b ->
      match b with
      | L4KZero447 -> L4KAccept491 (l4_kconst_atom555 path k)
      | L4KSucc447 v ->
        l4_kcombine_levels555 (l4_knormalize_aux555 fuel a path k)
          (l4_knormalize_aux555 fuel v path (SUC k))
      | L4KMax447 v w ->
        l4_kcombine_levels555
          (l4_knormalize_aux555 fuel (L4KIMax447 a v) path k)
          (l4_knormalize_aux555 fuel (L4KIMax447 a w) path k)
      | L4KIMax447 v w ->
        l4_kcombine_levels555
          (l4_knormalize_aux555 fuel (L4KIMax447 a w) path k)
          (l4_knormalize_aux555 fuel (L4KIMax447 v w) path k)
      | L4KParam447 n ->
        let guarded = l4_kguard_insert555 n path in
        l4_kr_bind491 (l4_knormalize_aux555 fuel a guarded k)
          (\xs. L4KAccept491 (APPEND (l4_kconst_atom555 path k)
            (CONS (L4KSubVar555 guarded n k) xs)))
      | L4KLevelMVar447 n -> L4KReject491 L4KMetaVariable491)`;;

let l4_knormalize_level555 = new_definition
 `l4_knormalize_level555 fuel u =
   if l4_klevel_meta447 u then L4KReject491 L4KMetaVariable491
   else l4_knormalize_aux555 fuel u [] 0`;;

let l4_kguard_subset555 = new_definition
 `l4_kguard_subset555 xs ys <=> ALL (\x. l4_name_mem437 x ys) xs`;;

(* The membership condition in Const<=Var is essential on arbitrary raw
   atoms: without it a zero-valued variable could dominate constant one. *)
let l4_ksublevel_le555 = new_recursive_definition l4_ksublevel_RECURSION555
 `(l4_ksublevel_le555 (L4KSubConst555 p k) b <=>
    match b with
    | L4KSubConst555 q j -> l4_kguard_subset555 q p /\ k <= j
    | L4KSubVar555 q n j ->
      l4_kguard_subset555 q p /\ l4_name_mem437 n q /\ k <= SUC j) /\
  (l4_ksublevel_le555 (L4KSubVar555 p n k) b <=>
    match b with
    | L4KSubConst555 q j -> F
    | L4KSubVar555 q m j ->
      l4_kguard_subset555 q p /\ n = m /\ k <= j)`;;

let l4_ksublevels_le555 = new_definition
 `l4_ksublevels_le555 xs ys <=> ALL (\x. EX (l4_ksublevel_le555 x) ys) xs`;;
let l4_klevel_le555 = new_definition
 `l4_klevel_le555 fuel u v =
   l4_kr_bind491 (l4_knormalize_level555 fuel u) (\xs.
     l4_kr_bind491 (l4_knormalize_level555 fuel v) (\ys.
       L4KAccept491 (l4_ksublevels_le555 xs ys)))`;;
let l4_klevel_equiv555 = new_definition
 `l4_klevel_equiv555 fuel u v =
   l4_kr_bind491 (l4_knormalize_level555 fuel u) (\xs.
     l4_kr_bind491 (l4_knormalize_level555 fuel v) (\ys.
       L4KAccept491 (l4_ksublevels_le555 xs ys /\ l4_ksublevels_le555 ys xs)))`;;

(* List first for structural recursion. Unequal lengths do not inspect
   unpaired levels. Each compared pair receives the same fuel value. *)
let l4_klevels_equiv555 = new_recursive_definition list_RECURSION
 `(l4_klevels_equiv555 [] fuel (vs:l4_klevel447 list) = L4KAccept491 (vs = [])) /\
  (l4_klevels_equiv555 (CONS u us) fuel vs =
    if NULL vs then L4KAccept491 F
    else l4_kr_bind491 (l4_klevel_equiv555 fuel u (HD vs))
      (\ok. if ok then l4_klevels_equiv555 us fuel (TL vs) else L4KAccept491 F))`;;

let l4_kguard_holds555 = new_definition
 `l4_kguard_holds555 (rho:l4_name->num) path <=> ALL (\n. ~(rho n = 0)) path`;;
let l4_ksublevel_eval555 = new_recursive_definition l4_ksublevel_RECURSION555
 `(l4_ksublevel_eval555 (L4KSubConst555 path k) rho =
    if l4_kguard_holds555 rho path then k else 0) /\
  (l4_ksublevel_eval555 (L4KSubVar555 path n k) rho =
    if l4_kguard_holds555 rho path then rho n + k else 0)`;;
let l4_ksublevels_eval555 = new_recursive_definition list_RECURSION
 `(l4_ksublevels_eval555 [] rho = 0) /\
  (l4_ksublevels_eval555 (CONS s ss) rho =
    MAX (l4_ksublevel_eval555 s rho) (l4_ksublevels_eval555 ss rho))`;;

(* False means "not syntactically definitely positive", not "equal to zero". *)
let l4_core_level_positive555 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_core_level_positive555 L4KZero447 <=> F) /\
  (l4_core_level_positive555 (L4KSucc447 u) <=> T) /\
  (l4_core_level_positive555 (L4KMax447 u v) <=>
    l4_core_level_positive555 u \/ l4_core_level_positive555 v) /\
  (l4_core_level_positive555 (L4KIMax447 u v) <=> l4_core_level_positive555 v) /\
  (l4_core_level_positive555 (L4KParam447 n) <=> F) /\
  (l4_core_level_positive555 (L4KLevelMVar447 n) <=> F)`;;
