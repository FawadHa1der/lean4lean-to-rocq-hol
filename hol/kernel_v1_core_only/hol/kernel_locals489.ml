(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/InductiveUtils.v; see ../NOTICE489.txt.
   SOURCE ONLY / UNCOMPILED. Not selected by the executable checker. *)
needs "hol/kernel_syntax447.ml";;

let l4_klocal_INDUCT489,l4_klocal_RECURSION489 = define_type
 "l4_klocal489 = L4KLocal489 l4_name l4_name l4_kbinder447 l4_kexpr447";;

let l4_klocal_id489 = new_recursive_definition l4_klocal_RECURSION489
 `l4_klocal_id489 (L4KLocal489 id user bi ty) = id`;;

let l4_klocal_user489 = new_recursive_definition l4_klocal_RECURSION489
 `l4_klocal_user489 (L4KLocal489 id user bi ty) = user`;;

let l4_klocal_binder489 = new_recursive_definition l4_klocal_RECURSION489
 `l4_klocal_binder489 (L4KLocal489 id user bi ty) = bi`;;

let l4_klocal_type489 = new_recursive_definition l4_klocal_RECURSION489
 `l4_klocal_type489 (L4KLocal489 id user bi ty) = ty`;;

let l4_klocal_expr489 = new_definition
 `l4_klocal_expr489 x = L4KFVar447 (l4_klocal_id489 x)`;;

(* Abstraction only replaces a matching free identifier. It does not shift
   existing loose bound variables or inspect the display names of binders. *)
let l4_kabstract_local489 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kabstract_local489 (L4KBVar447 i) id depth = L4KBVar447 i) /\
 (l4_kabstract_local489 (L4KFVar447 n) id depth =
   if id = n then L4KBVar447 depth else L4KFVar447 n) /\
 (l4_kabstract_local489 (L4KMVar447 n) id depth = L4KMVar447 n) /\
 (l4_kabstract_local489 (L4KSort447 u) id depth = L4KSort447 u) /\
 (l4_kabstract_local489 (L4KConst447 n us) id depth = L4KConst447 n us) /\
 (l4_kabstract_local489 (L4KApp447 a b) id depth =
   L4KApp447 (l4_kabstract_local489 a id depth) (l4_kabstract_local489 b id depth)) /\
 (l4_kabstract_local489 (L4KLam447 n bi a b) id depth =
   L4KLam447 n bi (l4_kabstract_local489 a id depth)
     (l4_kabstract_local489 b id (SUC depth))) /\
 (l4_kabstract_local489 (L4KPi447 n bi a b) id depth =
   L4KPi447 n bi (l4_kabstract_local489 a id depth)
     (l4_kabstract_local489 b id (SUC depth))) /\
 (l4_kabstract_local489 (L4KLet447 n a v b nd) id depth =
   L4KLet447 n (l4_kabstract_local489 a id depth)
     (l4_kabstract_local489 v id depth)
     (l4_kabstract_local489 b id (SUC depth)) nd) /\
 (l4_kabstract_local489 (L4KNatLit447 nat_value489) id depth = L4KNatLit447 nat_value489) /\
 (l4_kabstract_local489 (L4KStrLit447 s) id depth = L4KStrLit447 s) /\
 (l4_kabstract_local489 (L4KProj447 n i a) id depth =
   L4KProj447 n i (l4_kabstract_local489 a id depth)) /\
 (l4_kabstract_local489 (L4KMData447 a) id depth =
   L4KMData447 (l4_kabstract_local489 a id depth))`;;

(* Right fold: later binder domains remain inside the earlier abstraction. *)
let l4_kclose_pi489 = new_recursive_definition list_RECURSION
 `(l4_kclose_pi489 [] body = body) /\
 (l4_kclose_pi489 (CONS x xs) body =
   L4KPi447 (l4_klocal_user489 x) (l4_klocal_binder489 x)
     (l4_klocal_type489 x)
     (l4_kabstract_local489 (l4_kclose_pi489 xs body) (l4_klocal_id489 x) 0))`;;

let l4_kclose_lam489 = new_recursive_definition list_RECURSION
 `(l4_kclose_lam489 [] body = body) /\
 (l4_kclose_lam489 (CONS x xs) body =
   L4KLam447 (l4_klocal_user489 x) (l4_klocal_binder489 x)
     (l4_klocal_type489 x)
     (l4_kabstract_local489 (l4_kclose_lam489 xs body) (l4_klocal_id489 x) 0))`;;

(* List-first definitions expose primitive recursion while retaining fold-left
   application order. This argument order differs from the local Rocq helper. *)
let l4_kapply_exprs489 = new_recursive_definition list_RECURSION
 `(l4_kapply_exprs489 [] fn = fn) /\
 (l4_kapply_exprs489 (CONS a args) fn = l4_kapply_exprs489 args (L4KApp447 fn a))`;;

let l4_kapply_locals489 = new_definition
 `l4_kapply_locals489 args fn = l4_kapply_exprs489 (MAP l4_klocal_expr489 args) fn`;;

let l4_ksplit_app_aux489 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_ksplit_app_aux489 (L4KBVar447 i) args = (L4KBVar447 i,args)) /\
 (l4_ksplit_app_aux489 (L4KFVar447 n) args = (L4KFVar447 n,args)) /\
 (l4_ksplit_app_aux489 (L4KMVar447 n) args = (L4KMVar447 n,args)) /\
 (l4_ksplit_app_aux489 (L4KSort447 u) args = (L4KSort447 u,args)) /\
 (l4_ksplit_app_aux489 (L4KConst447 n us) args = (L4KConst447 n us,args)) /\
 (l4_ksplit_app_aux489 (L4KApp447 f a) args = l4_ksplit_app_aux489 f (CONS a args)) /\
 (l4_ksplit_app_aux489 (L4KLam447 n bi a b) args = (L4KLam447 n bi a b,args)) /\
 (l4_ksplit_app_aux489 (L4KPi447 n bi a b) args = (L4KPi447 n bi a b,args)) /\
 (l4_ksplit_app_aux489 (L4KLet447 n a v b nd) args = (L4KLet447 n a v b nd,args)) /\
 (l4_ksplit_app_aux489 (L4KNatLit447 nat_value489) args = (L4KNatLit447 nat_value489,args)) /\
 (l4_ksplit_app_aux489 (L4KStrLit447 s) args = (L4KStrLit447 s,args)) /\
 (l4_ksplit_app_aux489 (L4KProj447 n i a) args = (L4KProj447 n i a,args)) /\
 (l4_ksplit_app_aux489 (L4KMData447 a) args = (L4KMData447 a,args))`;;

let l4_ksplit_app489 = new_definition
 `l4_ksplit_app489 e = l4_ksplit_app_aux489 e []`;;
