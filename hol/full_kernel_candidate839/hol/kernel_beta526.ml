(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed HOL port of local rocq/Syntax.v and rocq/Checker.v.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE526.txt. No default integration. *)
needs "hol/kernel_locals489.ml";;

(* Values are innermost-first and live outside the entire removed block.
   The range test guards EL; inserted expressions are lifted, not substituted. *)
let l4_ksubst_many526 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_ksubst_many526 (L4KBVar447 i) k values =
    if i < k then L4KBVar447 i
    else if i - k < LENGTH values then
      if k = 0 then EL (i - k) values
      else l4_klift447 (EL (i - k) values) k 0
    else L4KBVar447 (i - LENGTH values)) /\
  (l4_ksubst_many526 (L4KFVar447 n) k values = L4KFVar447 n) /\
  (l4_ksubst_many526 (L4KMVar447 n) k values = L4KMVar447 n) /\
  (l4_ksubst_many526 (L4KSort447 u) k values = L4KSort447 u) /\
  (l4_ksubst_many526 (L4KConst447 n us) k values = L4KConst447 n us) /\
  (l4_ksubst_many526 (L4KApp447 f a) k values =
    L4KApp447 (l4_ksubst_many526 f k values) (l4_ksubst_many526 a k values)) /\
  (l4_ksubst_many526 (L4KLam447 n bi a b) k values =
    L4KLam447 n bi (l4_ksubst_many526 a k values)
      (l4_ksubst_many526 b (SUC k) values)) /\
  (l4_ksubst_many526 (L4KPi447 n bi a b) k values =
    L4KPi447 n bi (l4_ksubst_many526 a k values)
      (l4_ksubst_many526 b (SUC k) values)) /\
  (l4_ksubst_many526 (L4KLet447 n a v b nd) k values =
    L4KLet447 n (l4_ksubst_many526 a k values)
      (l4_ksubst_many526 v k values) (l4_ksubst_many526 b (SUC k) values) nd) /\
  (l4_ksubst_many526 (L4KNatLit447 nat_value526) k values = L4KNatLit447 nat_value526) /\
  (l4_ksubst_many526 (L4KStrLit447 s) k values = L4KStrLit447 s) /\
  (l4_ksubst_many526 (L4KProj447 n i e) k values =
    L4KProj447 n i (l4_ksubst_many526 e k values)) /\
  (l4_ksubst_many526 (L4KMData447 e) k values =
    L4KMData447 (l4_ksubst_many526 e k values))`;;

let l4_kinstantiate_many526 = new_definition
 `l4_kinstantiate_many526 body values =
    if values = [] then body else l4_ksubst_many526 body 0 values`;;

(* Structural recursion follows only an already visible lambda body.
   HD/TL are reached only for nonempty arguments. Non-lambda heads stop,
   even when simultaneous substitution exposes another lambda. *)
let l4_kcore_beta_collect526 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kcore_beta_collect526 (L4KBVar447 i) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KBVar447 i) values)) /\
  (l4_kcore_beta_collect526 (L4KFVar447 n) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KFVar447 n) values)) /\
  (l4_kcore_beta_collect526 (L4KMVar447 n) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KMVar447 n) values)) /\
  (l4_kcore_beta_collect526 (L4KSort447 u) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KSort447 u) values)) /\
  (l4_kcore_beta_collect526 (L4KConst447 n us) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KConst447 n us) values)) /\
  (l4_kcore_beta_collect526 (L4KApp447 f a) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KApp447 f a) values)) /\
  (l4_kcore_beta_collect526 (L4KLam447 n bi a b) args values =
    if args = [] then l4_kinstantiate_many526 (L4KLam447 n bi a b) values
    else l4_kcore_beta_collect526 b (TL args) (CONS (HD args) values)) /\
  (l4_kcore_beta_collect526 (L4KPi447 n bi a b) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KPi447 n bi a b) values)) /\
  (l4_kcore_beta_collect526 (L4KLet447 n a v b nd) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KLet447 n a v b nd) values)) /\
  (l4_kcore_beta_collect526 (L4KNatLit447 nat_value526) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KNatLit447 nat_value526) values)) /\
  (l4_kcore_beta_collect526 (L4KStrLit447 s) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KStrLit447 s) values)) /\
  (l4_kcore_beta_collect526 (L4KProj447 n i e) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KProj447 n i e) values)) /\
  (l4_kcore_beta_collect526 (L4KMData447 e) args values =
    l4_kapply_exprs489 args (l4_kinstantiate_many526 (L4KMData447 e) values))`;;

let l4_kcore_beta526 = new_definition
 `l4_kcore_beta526 head args = l4_kcore_beta_collect526 head args []`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_subst_many_nat899 = prove
 (`!m k values. l4_ksubst_many526 (L4KNatLit447 m) k values = L4KNatLit447 m`,
  REWRITE_TAC[l4_ksubst_many526]);;

let l4_subst_many_name899 = prove
 (`!name k values. l4_ksubst_many526 (L4KFVar447 name) k values = L4KFVar447 name`,
  REWRITE_TAC[l4_ksubst_many526]);;

let l4_beta_collect_nat899 = prove
 (`!m args values.
    l4_kcore_beta_collect526 (L4KNatLit447 m) args values =
      l4_kapply_exprs489 args (L4KNatLit447 m)`,
  REWRITE_TAC[l4_kcore_beta_collect526;l4_kinstantiate_many526;l4_ksubst_many526;COND_ID]);;

let l4_beta_collect_name899 = prove
 (`!name args values.
    l4_kcore_beta_collect526 (L4KFVar447 name) args values =
      l4_kapply_exprs489 args (L4KFVar447 name)`,
  REWRITE_TAC[l4_kcore_beta_collect526;l4_kinstantiate_many526;l4_ksubst_many526;COND_ID]);;
