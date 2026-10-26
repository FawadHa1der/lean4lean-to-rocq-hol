(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of Syntax.v218-231,InductiveUtils.v15 and Checker.v30-63.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE532.txt. Not checked admission. *)
needs "hol/nested_parameters491.ml";;
needs "hol/kernel_declarations493.ml";;

let l4_kbinding_type532 = new_recursive_definition l4_kbinding_RECURSION491
 `l4_kbinding_type532 (L4KBinding491 ty value) = ty`;;
let l4_kbinding_value532 = new_recursive_definition l4_kbinding_RECURSION491
 `l4_kbinding_value532 (L4KBinding491 ty value) = value`;;

(* Context has no allocation counter. Reuse491's complete binding payload. *)
let l4_kcontext_INDUCT532,l4_kcontext_RECURSION532 = define_type
 "l4_kcontext532 = L4KContext532 (l4_kbinding491 list) ((l4_name # l4_kbinding491) list)";;
let l4_kcontext_bound532 = new_recursive_definition l4_kcontext_RECURSION532
 `l4_kcontext_bound532 (L4KContext532 bound free) = bound`;;
let l4_kcontext_free532 = new_recursive_definition l4_kcontext_RECURSION532
 `l4_kcontext_free532 (L4KContext532 bound free) = free`;;
let l4_kempty_context532 = new_definition
 `l4_kempty_context532 = L4KContext532 [] []`;;

let l4_kpush_binding532 = new_recursive_definition l4_kcontext_RECURSION532
 `l4_kpush_binding532 (L4KContext532 bound free) ty value =
   L4KContext532 (CONS (L4KBinding491 ty value) bound) free`;;

let l4_kfind_free532 = new_recursive_definition list_RECURSION
 `(l4_kfind_free532 n [] = NONE) /\
  (l4_kfind_free532 n (CONS entry rest) =
    if n = FST entry then SOME (SND entry) else l4_kfind_free532 n rest)`;;

(* Recover ist_context from the flattened491 state without altering any list. *)
let l4_kstate_context532 = new_recursive_definition l4_kstate_RECURSION491
 `l4_kstate_context532 (L4KState491 next bound free) = L4KContext532 bound free`;;

let l4_core_occurs532 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_core_occurs532 idx (L4KBVar447 i) <=> i = idx) /\
  (l4_core_occurs532 idx (L4KFVar447 n) <=> F) /\
  (l4_core_occurs532 idx (L4KMVar447 n) <=> F) /\
  (l4_core_occurs532 idx (L4KSort447 u) <=> F) /\
  (l4_core_occurs532 idx (L4KConst447 n us) <=> F) /\
  (l4_core_occurs532 idx (L4KApp447 a b) <=>
    l4_core_occurs532 idx a \/ l4_core_occurs532 idx b) /\
  (l4_core_occurs532 idx (L4KLam447 n bi a b) <=>
    l4_core_occurs532 idx a \/ l4_core_occurs532 (SUC idx) b) /\
  (l4_core_occurs532 idx (L4KPi447 n bi a b) <=>
    l4_core_occurs532 idx a \/ l4_core_occurs532 (SUC idx) b) /\
  (l4_core_occurs532 idx (L4KLet447 n a v b nd) <=>
    l4_core_occurs532 idx a \/ l4_core_occurs532 idx v \/ l4_core_occurs532 (SUC idx) b) /\
  (l4_core_occurs532 idx (L4KNatLit447 nat_value532) <=> F) /\
  (l4_core_occurs532 idx (L4KStrLit447 bytes) <=> F) /\
  (l4_core_occurs532 idx (L4KProj447 n i a) <=> l4_core_occurs532 idx a) /\
  (l4_core_occurs532 idx (L4KMData447 a) <=> l4_core_occurs532 idx a)`;;

let l4_core_inductive532 = new_definition
 `l4_core_inductive532 env n =
   match l4_kfind_decl493 env n with
   | NONE -> NONE
   | SOME d -> (match l4_kdecl_kind493 d with
                | L4KDInductive493 info -> SOME info
                | _ -> NONE)`;;

let l4_core_constructor532 = new_definition
 `l4_core_constructor532 env n =
   match l4_kfind_decl493 env n with
   | NONE -> NONE
   | SOME d -> (match l4_kdecl_kind493 d with
                | L4KDConstructor493 info -> SOME info
                | _ -> NONE)`;;

(* This three-field shape test assumes environment admission elsewhere. *)
let l4_core_structure532 = new_definition
 `l4_core_structure532 env n <=>
   match l4_core_inductive532 env n with
   | NONE -> F
   | SOME info -> ~l4_kind_is_rec493 info /\
       l4_kind_num_indices493 info = 0 /\ LENGTH (l4_kind_ctors493 info) = 1`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_occurs_nat899 = prove
 (`!idx m. ~(l4_core_occurs532 idx (L4KNatLit447 m))`,
  REWRITE_TAC[l4_core_occurs532]);;

let l4_occurs_name899 = prove
 (`!idx name. ~(l4_core_occurs532 idx (L4KFVar447 name))`,
  REWRITE_TAC[l4_core_occurs532]);;
