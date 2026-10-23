(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider. See ../NOTICE447.txt.
   SOURCE ONLY / UNCOMPILED. Not selected by the current checker loader. *)
needs "hol/syntax.ml";;

let l4_kbinder_INDUCT447,l4_kbinder_RECURSION447 = define_type
 "l4_kbinder447 = L4KDefault447 | L4KImplicit447 |
                  L4KStrictImplicit447 | L4KInstImplicit447";;

let l4_klevel_INDUCT447,l4_klevel_RECURSION447 = define_type
 "l4_klevel447 = L4KZero447 | L4KSucc447 l4_klevel447 |
 L4KMax447 l4_klevel447 l4_klevel447 | L4KIMax447 l4_klevel447 l4_klevel447 |
 L4KParam447 l4_name | L4KLevelMVar447 l4_name";;

(* This matches Rocq's metadata-payload-erased syntax, not Lean serialization.
   Free locals, metavariables, binder information and nonDep remain distinct. *)
let l4_kexpr_INDUCT447,l4_kexpr_RECURSION447 = define_type
 "l4_kexpr447 = L4KBVar447 num | L4KFVar447 l4_name | L4KMVar447 l4_name |
 L4KSort447 l4_klevel447 | L4KConst447 l4_name (l4_klevel447 list) |
 L4KApp447 l4_kexpr447 l4_kexpr447 |
 L4KLam447 l4_name l4_kbinder447 l4_kexpr447 l4_kexpr447 |
 L4KPi447 l4_name l4_kbinder447 l4_kexpr447 l4_kexpr447 |
 L4KLet447 l4_name l4_kexpr447 l4_kexpr447 l4_kexpr447 bool |
 L4KNatLit447 num | L4KStrLit447 (num list) |
 L4KProj447 l4_name num l4_kexpr447 | L4KMData447 l4_kexpr447";;

let l4_klift447 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_klift447 (L4KBVar447 i) d k = L4KBVar447 (if i < k then i else i+d)) /\
 (l4_klift447 (L4KFVar447 n) d k = L4KFVar447 n) /\
 (l4_klift447 (L4KMVar447 n) d k = L4KMVar447 n) /\
 (l4_klift447 (L4KSort447 u) d k = L4KSort447 u) /\
 (l4_klift447 (L4KConst447 n us) d k = L4KConst447 n us) /\
 (l4_klift447 (L4KApp447 f a) d k = L4KApp447 (l4_klift447 f d k) (l4_klift447 a d k)) /\
 (l4_klift447 (L4KLam447 n bi a b) d k =
   L4KLam447 n bi (l4_klift447 a d k) (l4_klift447 b d (SUC k))) /\
 (l4_klift447 (L4KPi447 n bi a b) d k =
   L4KPi447 n bi (l4_klift447 a d k) (l4_klift447 b d (SUC k))) /\
 (l4_klift447 (L4KLet447 n a v b nd) d k =
   L4KLet447 n (l4_klift447 a d k) (l4_klift447 v d k) (l4_klift447 b d (SUC k)) nd) /\
 (l4_klift447 (L4KNatLit447 nat_value447) d k = L4KNatLit447 nat_value447) /\
 (l4_klift447 (L4KStrLit447 s) d k = L4KStrLit447 s) /\
 (l4_klift447 (L4KProj447 n i e) d k = L4KProj447 n i (l4_klift447 e d k)) /\
 (l4_klift447 (L4KMData447 e) d k = L4KMData447 (l4_klift447 e d k))`;;

let l4_ksubst447 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_ksubst447 (L4KBVar447 i) k s =
   if i < k then L4KBVar447 i else if i = k then l4_klift447 s k 0 else L4KBVar447 (i-1)) /\
 (l4_ksubst447 (L4KFVar447 n) k s = L4KFVar447 n) /\
 (l4_ksubst447 (L4KMVar447 n) k s = L4KMVar447 n) /\
 (l4_ksubst447 (L4KSort447 u) k s = L4KSort447 u) /\
 (l4_ksubst447 (L4KConst447 n us) k s = L4KConst447 n us) /\
 (l4_ksubst447 (L4KApp447 f a) k s = L4KApp447 (l4_ksubst447 f k s) (l4_ksubst447 a k s)) /\
 (l4_ksubst447 (L4KLam447 n bi a b) k s =
   L4KLam447 n bi (l4_ksubst447 a k s) (l4_ksubst447 b (SUC k) s)) /\
 (l4_ksubst447 (L4KPi447 n bi a b) k s =
   L4KPi447 n bi (l4_ksubst447 a k s) (l4_ksubst447 b (SUC k) s)) /\
 (l4_ksubst447 (L4KLet447 n a v b nd) k s =
   L4KLet447 n (l4_ksubst447 a k s) (l4_ksubst447 v k s) (l4_ksubst447 b (SUC k) s) nd) /\
 (l4_ksubst447 (L4KNatLit447 nat_value447) k s = L4KNatLit447 nat_value447) /\
 (l4_ksubst447 (L4KStrLit447 cs) k s = L4KStrLit447 cs) /\
 (l4_ksubst447 (L4KProj447 n i e) k s = L4KProj447 n i (l4_ksubst447 e k s)) /\
 (l4_ksubst447 (L4KMData447 e) k s = L4KMData447 (l4_ksubst447 e k s))`;;

let l4_kinst447 = new_definition `l4_kinst447 body value = l4_ksubst447 body 0 value`;;

let l4_kscoped447 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kscoped447 (L4KBVar447 i) k <=> i < k) /\
 (l4_kscoped447 (L4KFVar447 n) k <=> T) /\
 (l4_kscoped447 (L4KMVar447 n) k <=> T) /\
 (l4_kscoped447 (L4KSort447 u) k <=> T) /\
 (l4_kscoped447 (L4KConst447 n us) k <=> T) /\
 (l4_kscoped447 (L4KApp447 f a) k <=> l4_kscoped447 f k /\ l4_kscoped447 a k) /\
 (l4_kscoped447 (L4KLam447 n bi a b) k <=> l4_kscoped447 a k /\ l4_kscoped447 b (SUC k)) /\
 (l4_kscoped447 (L4KPi447 n bi a b) k <=> l4_kscoped447 a k /\ l4_kscoped447 b (SUC k)) /\
 (l4_kscoped447 (L4KLet447 n a v b nd) k <=>
   l4_kscoped447 a k /\ l4_kscoped447 v k /\ l4_kscoped447 b (SUC k)) /\
 (l4_kscoped447 (L4KNatLit447 nat_value447) k <=> T) /\
 (l4_kscoped447 (L4KStrLit447 s) k <=> T) /\
 (l4_kscoped447 (L4KProj447 n i e) k <=> l4_kscoped447 e k) /\
 (l4_kscoped447 (L4KMData447 e) k <=> l4_kscoped447 e k)`;;

(* Scoping bounds de Bruijn indices; it does not reject free/metavariables. *)
let l4_kfree447 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kfree447 (L4KBVar447 i) <=> F) /\
 (l4_kfree447 (L4KFVar447 n) <=> T) /\
 (l4_kfree447 (L4KMVar447 n) <=> F) /\
 (l4_kfree447 (L4KSort447 u) <=> F) /\
 (l4_kfree447 (L4KConst447 n us) <=> F) /\
 (l4_kfree447 (L4KApp447 f a) <=> l4_kfree447 f \/ l4_kfree447 a) /\
 (l4_kfree447 (L4KLam447 n bi a b) <=> l4_kfree447 a \/ l4_kfree447 b) /\
 (l4_kfree447 (L4KPi447 n bi a b) <=> l4_kfree447 a \/ l4_kfree447 b) /\
 (l4_kfree447 (L4KLet447 n a v b nd) <=> l4_kfree447 a \/ l4_kfree447 v \/ l4_kfree447 b) /\
 (l4_kfree447 (L4KNatLit447 nat_value447) <=> F) /\
 (l4_kfree447 (L4KStrLit447 s) <=> F) /\
 (l4_kfree447 (L4KProj447 n i e) <=> l4_kfree447 e) /\
 (l4_kfree447 (L4KMData447 e) <=> l4_kfree447 e)`;;

let l4_klevel_meta447 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_klevel_meta447 L4KZero447 <=> F) /\
 (l4_klevel_meta447 (L4KSucc447 u) <=> l4_klevel_meta447 u) /\
 (l4_klevel_meta447 (L4KMax447 u v) <=> l4_klevel_meta447 u \/ l4_klevel_meta447 v) /\
 (l4_klevel_meta447 (L4KIMax447 u v) <=> l4_klevel_meta447 u \/ l4_klevel_meta447 v) /\
 (l4_klevel_meta447 (L4KParam447 n) <=> F) /\
 (l4_klevel_meta447 (L4KLevelMVar447 n) <=> T)`;;

let l4_kmeta447 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_kmeta447 (L4KBVar447 i) <=> F) /\
 (l4_kmeta447 (L4KFVar447 n) <=> F) /\
 (l4_kmeta447 (L4KMVar447 n) <=> T) /\
 (l4_kmeta447 (L4KSort447 u) <=> l4_klevel_meta447 u) /\
 (l4_kmeta447 (L4KConst447 n us) <=> EX l4_klevel_meta447 us) /\
 (l4_kmeta447 (L4KApp447 f a) <=> l4_kmeta447 f \/ l4_kmeta447 a) /\
 (l4_kmeta447 (L4KLam447 n bi a b) <=> l4_kmeta447 a \/ l4_kmeta447 b) /\
 (l4_kmeta447 (L4KPi447 n bi a b) <=> l4_kmeta447 a \/ l4_kmeta447 b) /\
 (l4_kmeta447 (L4KLet447 n a v b nd) <=> l4_kmeta447 a \/ l4_kmeta447 v \/ l4_kmeta447 b) /\
 (l4_kmeta447 (L4KNatLit447 nat_value447) <=> F) /\
 (l4_kmeta447 (L4KStrLit447 s) <=> F) /\
 (l4_kmeta447 (L4KProj447 n i e) <=> l4_kmeta447 e) /\
 (l4_kmeta447 (L4KMData447 e) <=> l4_kmeta447 e)`;;

(* SPDX-License-Identifier: Apache-2.0
   Source-only regression propositions for the corrected syntax447 definitions.
   No proof check has been run on these statements yet. *)

let l4_nat_lift892 = prove
 (`!m d k. l4_klift447 (L4KNatLit447 m) d k = L4KNatLit447 m`,
  REWRITE_TAC[l4_klift447]);;

let l4_nat_subst892 = prove
 (`!m k s. l4_ksubst447 (L4KNatLit447 m) k s = L4KNatLit447 m`,
  REWRITE_TAC[l4_ksubst447]);;

let l4_nat_scoped892 = prove
 (`!m k. l4_kscoped447 (L4KNatLit447 m) k`,
  REWRITE_TAC[l4_kscoped447]);;

let l4_nat_free892 = prove
 (`!m. ~(l4_kfree447 (L4KNatLit447 m))`,
  REWRITE_TAC[l4_kfree447]);;

let l4_nat_meta892 = prove
 (`!m. ~(l4_kmeta447 (L4KNatLit447 m))`,
  REWRITE_TAC[l4_kmeta447]);;

let l4_name_lift892 = prove
 (`!n d k. l4_klift447 (L4KFVar447 n) d k = L4KFVar447 n`,
  REWRITE_TAC[l4_klift447]);;

let l4_name_subst892 = prove
 (`!n k s. l4_ksubst447 (L4KFVar447 n) k s = L4KFVar447 n`,
  REWRITE_TAC[l4_ksubst447]);;

let l4_name_scoped892 = prove
 (`!n k. l4_kscoped447 (L4KFVar447 n) k`,
  REWRITE_TAC[l4_kscoped447]);;

let l4_name_free892 = prove
 (`!n. l4_kfree447 (L4KFVar447 n)`,
  REWRITE_TAC[l4_kfree447]);;

let l4_name_meta892 = prove
 (`!n. ~(l4_kmeta447 (L4KFVar447 n))`,
  REWRITE_TAC[l4_kmeta447]);;

let l4_bvar_lift892 = prove
 (`l4_klift447 (L4KBVar447 0) 1 0 = L4KBVar447 1`,
  REWRITE_TAC[l4_klift447] THEN NUM_REDUCE_TAC);;

let l4_bvar_subst892 = prove
 (`!s. l4_ksubst447 (L4KBVar447 0) 0 s = l4_klift447 s 0 0`,
  REWRITE_TAC[l4_ksubst447] THEN NUM_REDUCE_TAC);;
