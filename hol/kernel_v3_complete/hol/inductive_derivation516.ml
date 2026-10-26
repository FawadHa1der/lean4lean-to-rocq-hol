(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/Inductive.v and InductiveUtils.v; see ../NOTICE516.txt.
   SOURCE ONLY / UNCOMPILED. Pure records/metadata are NOT checked admission. *)
needs "hol/member_verification509.ml";;

let l4_kind_checked_INDUCT516,l4_kind_checked_RECURSION516 = define_type
 "l4_kind_checked516 = L4KIndChecked516 l4_kind_spec493
   (l4_klocal489 list) l4_klevel447";;
let l4_kind_stats_INDUCT516,l4_kind_stats_RECURSION516 = define_type
 "l4_kind_stats516 = L4KIndStats516 (l4_klocal489 list)
   (l4_kind_checked516 list) (l4_name list) (l4_klevel447 list)
   l4_klevel447 bool l4_kstate491";;
let l4_kind_motive_INDUCT516,l4_kind_motive_RECURSION516 = define_type
 "l4_kind_motive516 = L4KIndMotive516 l4_kind_checked516
   l4_klocal489 l4_klocal489";;
let l4_kind_recursive_arg_INDUCT516,l4_kind_recursive_arg_RECURSION516 = define_type
 "l4_kind_recursive_arg516 = L4KIndRecursiveArg516 l4_klocal489
   (l4_klocal489 list) num (l4_kexpr447 list)";;
let l4_kind_minor_INDUCT516,l4_kind_minor_RECURSION516 = define_type
 "l4_kind_minor516 = L4KIndMinor516 l4_kdeclaration493 num
   l4_klocal489 (l4_klocal489 list) (l4_kind_recursive_arg516 list)";;

let l4_kchecked_spec516 = new_recursive_definition l4_kind_checked_RECURSION516
 `l4_kchecked_spec516 (L4KIndChecked516 s xs u) = s`;;
let l4_kchecked_indices516 = new_recursive_definition l4_kind_checked_RECURSION516
 `l4_kchecked_indices516 (L4KIndChecked516 s xs u) = xs`;;
let l4_kchecked_level516 = new_recursive_definition l4_kind_checked_RECURSION516
 `l4_kchecked_level516 (L4KIndChecked516 s xs u) = u`;;
let l4_kstats_params516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_params516 (L4KIndStats516 ps ts ns us u unsafe state) = ps`;;
let l4_kstats_types516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_types516 (L4KIndStats516 ps ts ns us u unsafe state) = ts`;;
let l4_kstats_names516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_names516 (L4KIndStats516 ps ts ns us u unsafe state) = ns`;;
let l4_kstats_levels516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_levels516 (L4KIndStats516 ps ts ns us u unsafe state) = us`;;
let l4_kstats_result516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_result516 (L4KIndStats516 ps ts ns us u unsafe state) = u`;;
let l4_kstats_unsafe516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_unsafe516 (L4KIndStats516 ps ts ns us u unsafe state) = unsafe`;;
let l4_kstats_state516 = new_recursive_definition l4_kind_stats_RECURSION516
 `l4_kstats_state516 (L4KIndStats516 ps ts ns us u unsafe state) = state`;;
let l4_kmotive_type_info516 = new_recursive_definition l4_kind_motive_RECURSION516
 `l4_kmotive_type_info516 (L4KIndMotive516 t x major) = t`;;
let l4_kmotive_local516 = new_recursive_definition l4_kind_motive_RECURSION516
 `l4_kmotive_local516 (L4KIndMotive516 t x major) = x`;;
let l4_kmotive_major516 = new_recursive_definition l4_kind_motive_RECURSION516
 `l4_kmotive_major516 (L4KIndMotive516 t x major) = major`;;
let l4_kra_field516 = new_recursive_definition l4_kind_recursive_arg_RECURSION516
 `l4_kra_field516 (L4KIndRecursiveArg516 x args i indices) = x`;;
let l4_kra_arguments516 = new_recursive_definition l4_kind_recursive_arg_RECURSION516
 `l4_kra_arguments516 (L4KIndRecursiveArg516 x args i indices) = args`;;
let l4_kra_inductive516 = new_recursive_definition l4_kind_recursive_arg_RECURSION516
 `l4_kra_inductive516 (L4KIndRecursiveArg516 x args i indices) = i`;;
let l4_kra_indices516 = new_recursive_definition l4_kind_recursive_arg_RECURSION516
 `l4_kra_indices516 (L4KIndRecursiveArg516 x args i indices) = indices`;;
let l4_kminor_ctor516 = new_recursive_definition l4_kind_minor_RECURSION516
 `l4_kminor_ctor516 (L4KIndMinor516 c i x fields recs) = c`;;
let l4_kminor_owner516 = new_recursive_definition l4_kind_minor_RECURSION516
 `l4_kminor_owner516 (L4KIndMinor516 c i x fields recs) = i`;;
let l4_kminor_local516 = new_recursive_definition l4_kind_minor_RECURSION516
 `l4_kminor_local516 (L4KIndMinor516 c i x fields recs) = x`;;
let l4_kminor_fields516 = new_recursive_definition l4_kind_minor_RECURSION516
 `l4_kminor_fields516 (L4KIndMinor516 c i x fields recs) = fields`;;
let l4_kminor_recursive516 = new_recursive_definition l4_kind_minor_RECURSION516
 `l4_kminor_recursive516 (L4KIndMinor516 c i x fields recs) = recs`;;

(* Total structural occurrence, names-first as in Rocq. Unlike nested_has_new449,
   projection OWNER names count. Variables/binder labels/universes do not. *)
let l4_has_inductive516 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_has_inductive516 names (L4KBVar447 i) <=> F) /\
 (l4_has_inductive516 names (L4KFVar447 n) <=> F) /\
 (l4_has_inductive516 names (L4KMVar447 n) <=> F) /\
 (l4_has_inductive516 names (L4KSort447 u) <=> F) /\
 (l4_has_inductive516 names (L4KConst447 n us) <=> l4_name_mem437 n names) /\
 (l4_has_inductive516 names (L4KApp447 a b) <=>
   if l4_has_inductive516 names a then T else l4_has_inductive516 names b) /\
 (l4_has_inductive516 names (L4KLam447 n bi a b) <=>
   if l4_has_inductive516 names a then T else l4_has_inductive516 names b) /\
 (l4_has_inductive516 names (L4KPi447 n bi a b) <=>
   if l4_has_inductive516 names a then T else l4_has_inductive516 names b) /\
 (l4_has_inductive516 names (L4KLet447 n a v b nd) <=>
   if l4_has_inductive516 names a then T else
   if l4_has_inductive516 names v then T else l4_has_inductive516 names b) /\
 (l4_has_inductive516 names (L4KNatLit447 i) <=> F) /\
 (l4_has_inductive516 names (L4KStrLit447 bytes) <=> F) /\
 (l4_has_inductive516 names (L4KProj447 n i a) <=>
   if l4_name_mem437 n names then T else l4_has_inductive516 names a) /\
 (l4_has_inductive516 names (L4KMData447 a) <=> l4_has_inductive516 names a)`;;

(* Scan raw Pi domains only, not the terminal result or a normalized telescope. *)
let l4_recursive_constructor516 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_recursive_constructor516 names (L4KBVar447 i) <=> F) /\
 (l4_recursive_constructor516 names (L4KFVar447 n) <=> F) /\
 (l4_recursive_constructor516 names (L4KMVar447 n) <=> F) /\
 (l4_recursive_constructor516 names (L4KSort447 u) <=> F) /\
 (l4_recursive_constructor516 names (L4KConst447 n us) <=> F) /\
 (l4_recursive_constructor516 names (L4KApp447 a b) <=> F) /\
 (l4_recursive_constructor516 names (L4KLam447 n bi a b) <=> F) /\
 (l4_recursive_constructor516 names (L4KPi447 n bi a b) <=>
   if l4_has_inductive516 names a then T else l4_recursive_constructor516 names b) /\
 (l4_recursive_constructor516 names (L4KLet447 n a v b nd) <=> F) /\
 (l4_recursive_constructor516 names (L4KNatLit447 i) <=> F) /\
 (l4_recursive_constructor516 names (L4KStrLit447 bytes) <=> F) /\
 (l4_recursive_constructor516 names (L4KProj447 n i a) <=> F) /\
 (l4_recursive_constructor516 names (L4KMData447 a) <=> F)`;;

let l4_reflexive_constructor516 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_reflexive_constructor516 names (L4KBVar447 i) <=> F) /\
 (l4_reflexive_constructor516 names (L4KFVar447 n) <=> F) /\
 (l4_reflexive_constructor516 names (L4KMVar447 n) <=> F) /\
 (l4_reflexive_constructor516 names (L4KSort447 u) <=> F) /\
 (l4_reflexive_constructor516 names (L4KConst447 n us) <=> F) /\
 (l4_reflexive_constructor516 names (L4KApp447 a b) <=> F) /\
 (l4_reflexive_constructor516 names (L4KLam447 n bi a b) <=> F) /\
 (l4_reflexive_constructor516 names (L4KPi447 n bi a b) <=>
   if (match a with
       | L4KPi447 m bj c d -> l4_has_inductive516 names a
       | _ -> F) then T else l4_reflexive_constructor516 names b) /\
 (l4_reflexive_constructor516 names (L4KLet447 n a v b nd) <=> F) /\
 (l4_reflexive_constructor516 names (L4KNatLit447 i) <=> F) /\
 (l4_reflexive_constructor516 names (L4KStrLit447 bytes) <=> F) /\
 (l4_reflexive_constructor516 names (L4KProj447 n i a) <=> F) /\
 (l4_reflexive_constructor516 names (L4KMData447 a) <=> F)`;;

(* Shape recognition only: exact ordered Nat/Bool constructor pair, with
   source expr_eqb480 (binder labels/info ignored), no kind/safety admission. *)
let l4_check_primitive_inductive516 = new_definition
 `l4_check_primitive_inductive516 (ps:l4_name list) nparams specs <=>
   match (ps,nparams,specs) with
   | ([],0,[s]) ->
     let d = l4_kspec_decl493 s in
     if l4_kexpr_eqb480 (l4_kdecl_type493 d) (L4KSort447 (L4KSucc447 L4KZero447)) then
       (match l4_kspec_ctors493 s with
        | [a;b] ->
          let head = L4KConst447 (l4_kdecl_name493 d) [] in
          let natname = L4String L4Anonymous [78;97;116] in
          let boolname = L4String L4Anonymous [66;111;111;108] in
          if l4_kdecl_name493 d = natname then
            if l4_kdecl_name493 a = L4String natname [122;101;114;111] then
            if l4_kdecl_name493 b = L4String natname [115;117;99;99] then
            if l4_kexpr_eqb480 (l4_kdecl_type493 a) head then
              l4_kexpr_eqb480 (l4_kdecl_type493 b)
                (L4KPi447 L4Anonymous L4KDefault447 head head)
            else F else F else F
          else if l4_kdecl_name493 d = boolname then
            if l4_kdecl_name493 a = L4String boolname [102;97;108;115;101] then
            if l4_kdecl_name493 b = L4String boolname [116;114;117;101] then
            if l4_kexpr_eqb480 (l4_kdecl_type493 a) head then
              l4_kexpr_eqb480 (l4_kdecl_type493 b) head
            else F else F else F
          else F
        | _ -> F)
     else F
   | _ -> F`;;

(* Core lists.ml has no FLAT. This is a defined, polymorphic right fold. *)
let l4_kflatten516 = new_definition
 `l4_kflatten516 (xss:(A list)list) = ITLIST APPEND xss []`;;

(* All checked specs contribute flags, while this member supplies its own
   ctor-name list. Flatten preserves order and duplicates, unlike a set. *)
let l4_derived_inductive516 = new_definition
 `l4_derived_inductive516 stats t =
   let specs = MAP l4_kchecked_spec516 (l4_kstats_types516 stats) in
   let ctors = l4_kflatten516 (MAP l4_kspec_ctors493 specs) in
   let d = l4_kspec_decl493 (l4_kchecked_spec516 t) in
   L4KDeclaration493 (l4_kdecl_name493 d) (l4_kdecl_params493 d)
     (l4_kdecl_type493 d) NONE
     (L4KDInductive493
       (L4KInductiveData493 (LENGTH (l4_kstats_params516 stats))
         (LENGTH (l4_kchecked_indices516 t)) (l4_kstats_names516 stats)
         (MAP l4_kdecl_name493 (l4_kspec_ctors493 (l4_kchecked_spec516 t))) 0
         (EX (\c. l4_recursive_constructor516 (l4_kstats_names516 stats)
           (l4_kdecl_type493 c)) ctors)
         (EX (\c. l4_reflexive_constructor516 (l4_kstats_names516 stats)
           (l4_kdecl_type493 c)) ctors)
         (l4_kstats_unsafe516 stats))) (l4_kdecl_hints493 d)`;;

(* Exact kind pair first; supplied nested/unsafe decline precedes equality.
   This does not validate stats, scoping, positivity or the constructors. *)
let l4_verify_ind_metadata516 = new_definition
 `l4_verify_ind_metadata516 stats t =
   let generated = l4_derived_inductive516 stats t in
   match (l4_kdecl_kind493 (l4_kspec_decl493 (l4_kchecked_spec516 t)),
          l4_kdecl_kind493 generated) with
   | (L4KDInductive493 supplied,L4KDInductive493 actual) ->
     if ~(l4_kind_num_nested493 supplied = 0) then
       L4KDecline491 L4KUnsupportedDeclaration491
     else if l4_kind_is_unsafe493 supplied then
       L4KDecline491 L4KUnsupportedDeclaration491
     else if l4_inductive_data_eqb509 supplied actual then L4KAccept491 generated
     else L4KReject491 L4KMalformedDeclaration491
   | _ -> L4KReject491 L4KMalformedDeclaration491`;;
