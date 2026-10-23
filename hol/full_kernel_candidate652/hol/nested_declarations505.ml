(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/NestedAdmission.v:160-225; see ../NOTICE505.txt.
   SOURCE ONLY / UNCOMPILED. Rebuilding syntax is NOT checked admission. *)
needs "hol/nested_expression499.ml";;

(* Constructor-name failure wins over RHS failure. Both get original fuel. *)
let l4_restore_rule505 = new_definition
 `l4_restore_rule505 fuel generated res rec_map r =
   l4_kr_bind491
     (l4_restore_ctor_name499 fuel generated res (l4_krule_ctor493 r))
     (\ctor. l4_kr_bind491
       (l4_restore_nested_type499 fuel generated res rec_map (l4_krule_rhs493 r))
       (\rhs. L4KAccept491 (L4KRecursorRule493 ctor (l4_krule_nfields493 r) rhs)))`;;

(* First declaration wins, even if it has the wrong kind. Never unwrap Unsafe.
   Type restoration precedes rules; mapping rules does not consume list fuel. *)
let l4_restore_recursor505 = new_definition
 `l4_restore_recursor505 fuel generated res rec_map all old =
   match l4_kfind_decl493 generated old with
   | NONE -> L4KReject491 L4KUnknownConstant491
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDRecursor493 info ->
        l4_kr_bind491
          (l4_restore_nested_type499 fuel generated res rec_map (l4_kdecl_type493 d))
          (\ty. l4_kr_bind491
            (l4_kmap_result499 (l4_krec_rules493 info)
              (l4_restore_rule505 fuel generated res rec_map))
            (\rules. L4KAccept491
              (L4KDeclaration493 (l4_krestore_name495 rec_map old)
                (l4_kdecl_params493 d) ty NONE
                (L4KDRecursor493 (L4KRecursorData493 all
                  (l4_krec_num_params493 info) (l4_krec_num_indices493 info)
                  (l4_krec_num_motives493 info) (l4_krec_num_minors493 info)
                  rules (l4_krec_k493 info) (l4_krec_is_unsafe493 info)))
                L4KHintOpaque493)))
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

(* Unlike a rule's constructor name, this declaration name is NOT restored.
   All five constructor metadata fields survive; recursor-name map is empty. *)
let l4_restore_constructor505 = new_definition
 `l4_restore_constructor505 fuel generated res n =
   match l4_kfind_decl493 generated n with
   | NONE -> L4KReject491 L4KUnknownConstant491
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDConstructor493 info ->
        l4_kr_bind491 (l4_restore_nested_type499 fuel generated res [] (l4_kdecl_type493 d))
          (\ty. L4KAccept491 (L4KDeclaration493 n (l4_kdecl_params493 d) ty NONE
            (L4KDConstructor493 info) L4KHintOpaque493))
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

(* This helper has NO fuel/type-restoration step. Only all and nested count
   change within the eight-field inductive metadata. Counts are not validated. *)
let l4_restore_inductive505 = new_definition
 `l4_restore_inductive505 generated res all n =
   match l4_kfind_decl493 generated n with
   | NONE -> L4KReject491 L4KUnknownConstant491
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDInductive493 info ->
        L4KAccept491 (L4KDeclaration493 n (l4_kdecl_params493 d) (l4_kdecl_type493 d) NONE
          (L4KDInductive493 (L4KInductiveData493
            (l4_kind_num_params493 info) (l4_kind_num_indices493 info) all
            (l4_kind_ctors493 info) (l4_knested_aux_count499 res)
            (l4_kind_is_rec493 info) (l4_kind_is_reflexive493 info)
            (l4_kind_is_unsafe493 info))) L4KHintOpaque493)
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

(* Name-first argument order exposes structural recursion on n.
   l4_name_prefix505 n prefix corresponds to Rocq name_prefix prefix n.
   Exact name equality, NOT string-prefix matching. *)
let l4_name_prefix505 = new_recursive_definition l4_name_RECURSION
 `(l4_name_prefix505 L4Anonymous prefix <=> prefix = L4Anonymous) /\
 (l4_name_prefix505 (L4String p s) prefix <=>
   if prefix = L4String p s then T else l4_name_prefix505 p prefix) /\
 (l4_name_prefix505 (L4Numeric p k) prefix <=>
   if prefix = L4Numeric p k then T else l4_name_prefix505 p prefix)`;;

(* ASCII "_nested" is one root string component. Projection OWNERS count;
   binder labels, locals, metavariables, universe names and string literals do not. *)
let l4_uses_reserved_nested505 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_uses_reserved_nested505 (L4KBVar447 i) <=> F) /\
 (l4_uses_reserved_nested505 (L4KFVar447 n) <=> F) /\
 (l4_uses_reserved_nested505 (L4KMVar447 n) <=> F) /\
 (l4_uses_reserved_nested505 (L4KSort447 u) <=> F) /\
 (l4_uses_reserved_nested505 (L4KConst447 n us) <=>
   l4_name_prefix505 n (L4String L4Anonymous [95;110;101;115;116;101;100])) /\
 (l4_uses_reserved_nested505 (L4KApp447 a b) <=>
   l4_uses_reserved_nested505 a \/ l4_uses_reserved_nested505 b) /\
 (l4_uses_reserved_nested505 (L4KLam447 n bi a b) <=>
   l4_uses_reserved_nested505 a \/ l4_uses_reserved_nested505 b) /\
 (l4_uses_reserved_nested505 (L4KPi447 n bi a b) <=>
   l4_uses_reserved_nested505 a \/ l4_uses_reserved_nested505 b) /\
 (l4_uses_reserved_nested505 (L4KLet447 n a v b nd) <=>
   (l4_uses_reserved_nested505 a \/ l4_uses_reserved_nested505 v) \/ l4_uses_reserved_nested505 b) /\
 (l4_uses_reserved_nested505 (L4KNatLit447 nat_value505) <=> F) /\
 (l4_uses_reserved_nested505 (L4KStrLit447 s) <=> F) /\
 (l4_uses_reserved_nested505 (L4KProj447 n i a) <=>
   l4_name_prefix505 n (L4String L4Anonymous [95;110;101;115;116;101;100]) \/
   l4_uses_reserved_nested505 a) /\
 (l4_uses_reserved_nested505 (L4KMData447 a) <=> l4_uses_reserved_nested505 a)`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_reserved_nat899 = prove
 (`!m. ~(l4_uses_reserved_nested505 (L4KNatLit447 m))`,
  REWRITE_TAC[l4_uses_reserved_nested505]);;

let l4_reserved_name899 = prove
 (`!name. ~(l4_uses_reserved_nested505 (L4KFVar447 name))`,
  REWRITE_TAC[l4_uses_reserved_nested505]);;
