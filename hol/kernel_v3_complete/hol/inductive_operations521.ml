(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local Inductive.v/InductiveUtils.v. See ../NOTICE521.txt.
   SOURCE ONLY / UNCOMPILED. Raw construction is NOT checked admission. *)
needs "hol/inductive_derivation516.ml";;
needs "hol/nested_expression499.ml";;

(* First matching entry wins. Parameters are compared as expressions, whereas
   indices must be free of occurrences of every name in the mutual block. *)
let l4_valid_ind_app_at521 = new_recursive_definition list_RECURSION
 `(l4_valid_ind_app_at521 [] stats head args idx = NONE) /\
  (l4_valid_ind_app_at521 (CONS t ts) stats head args idx =
    let d = l4_kspec_decl493 (l4_kchecked_spec516 t) in
    if l4_kexpr_eqb480 head (L4KConst447 (l4_kdecl_name493 d) (l4_kstats_levels516 stats)) /\
       LENGTH args = LENGTH (l4_kstats_params516 stats) + LENGTH (l4_kchecked_indices516 t) /\
       l4_klist_eqb509 l4_kexpr_eqb480
         (l4_kfirstn494 args (LENGTH (l4_kstats_params516 stats)))
         (MAP l4_klocal_expr489 (l4_kstats_params516 stats)) /\
       ~EX (l4_has_inductive516 (l4_kstats_names516 stats))
         (l4_kskipn499 args (LENGTH (l4_kstats_params516 stats)))
    then SOME idx else l4_valid_ind_app_at521 ts stats head args (SUC idx))`;;

let l4_valid_ind_app521 = new_definition
 `l4_valid_ind_app521 stats e =
   let split = l4_ksplit_app489 e in
   l4_valid_ind_app_at521 (l4_kstats_types516 stats) stats (FST split) (SND split) 0`;;

(* Deliberately raw projection: this does not first require a valid app. *)
let l4_ind_app_indices521 = new_definition
 `l4_ind_app_indices521 stats e =
   l4_kskipn499 (SND (l4_ksplit_app489 e)) (LENGTH (l4_kstats_params516 stats))`;;

let l4_raw_arity521 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_raw_arity521 (L4KBVar447 i) = 0) /\
  (l4_raw_arity521 (L4KFVar447 n) = 0) /\
  (l4_raw_arity521 (L4KMVar447 n) = 0) /\
  (l4_raw_arity521 (L4KSort447 u) = 0) /\
  (l4_raw_arity521 (L4KConst447 n us) = 0) /\
  (l4_raw_arity521 (L4KApp447 a b) = 0) /\
  (l4_raw_arity521 (L4KLam447 n bi a b) = 0) /\
  (l4_raw_arity521 (L4KPi447 n bi a b) = SUC (l4_raw_arity521 b)) /\
  (l4_raw_arity521 (L4KLet447 n a v b nd) = 0) /\
  (l4_raw_arity521 (L4KNatLit447 nat_value521) = 0) /\
  (l4_raw_arity521 (L4KStrLit447 bytes) = 0) /\
  (l4_raw_arity521 (L4KProj447 n i a) = 0) /\
  (l4_raw_arity521 (L4KMData447 a) = 0)`;;

(* A sufficient raw-level test, not a complete decision procedure. In imax
   only the right operand matters; succ is positive regardless of its child. *)
let l4_level_never_zero521 = new_recursive_definition l4_klevel_RECURSION447
 `(l4_level_never_zero521 L4KZero447 <=> F) /\
  (l4_level_never_zero521 (L4KSucc447 u) <=> T) /\
  (l4_level_never_zero521 (L4KMax447 u v) <=>
    l4_level_never_zero521 u \/ l4_level_never_zero521 v) /\
  (l4_level_never_zero521 (L4KIMax447 u v) <=> l4_level_never_zero521 v) /\
  (l4_level_never_zero521 (L4KParam447 n) <=> F) /\
  (l4_level_never_zero521 (L4KLevelMVar447 n) <=> F)`;;

let l4_fresh_elim_name521 = new_recursive_definition num_RECURSION
 `(l4_fresh_elim_name521 0 idx ps = L4KDecline491 L4KOutOfFuel491) /\
  (l4_fresh_elim_name521 (SUC fuel) idx ps =
    let n = L4Numeric (L4String L4Anonymous [95;114;111;99;113;95;101;108;105;109]) idx in
    if l4_name_mem437 n ps then l4_fresh_elim_name521 fuel (SUC idx) ps
    else L4KAccept491 n)`;;

(* Each entry allocates major then motive and threads the resulting full
   state into the next entry. The index locals are retained, not reallocated. *)
let l4_build_motives521 = new_recursive_definition list_RECURSION
 `(l4_build_motives521 [] stats elim state = ([],state)) /\
  (l4_build_motives521 (CONS t ts) stats elim state =
    let head = L4KConst447 (l4_kdecl_name493 (l4_kspec_decl493 (l4_kchecked_spec516 t)))
                 (l4_kstats_levels516 stats) in
    let major_ty = l4_kapply_locals489 (l4_kchecked_indices516 t)
                    (l4_kapply_locals489 (l4_kstats_params516 stats) head) in
    let major = l4_kind_fresh491 state (L4String L4Anonymous [116]) L4KDefault447 major_ty in
    let motive_ty = l4_kclose_pi489 (l4_kchecked_indices516 t)
                      (l4_kclose_pi489 [FST major] (L4KSort447 elim)) in
    let motive = l4_kind_fresh491 (SND major) (L4String L4Anonymous [109;111;116;105;118;101])
                   L4KDefault447 motive_ty in
    let rest = l4_build_motives521 ts stats elim (SND motive) in
    (CONS (L4KIndMotive516 t (FST motive) (FST major)) (FST rest),SND rest))`;;

(* Guard EL by the exact nth_error domain before constructing or allocating.
   Out-of-range references reject; no fabricated motive or default element. *)
let l4_build_ihs521 = new_recursive_definition list_RECURSION
 `(l4_build_ihs521 [] motives state = L4KAccept491 ([],state)) /\
  (l4_build_ihs521 (CONS a args) motives state =
    if l4_kra_inductive516 a < LENGTH motives then
      let m = EL (l4_kra_inductive516 a) motives in
      let ih_ty = l4_kclose_pi489 (l4_kra_arguments516 a)
        (L4KApp447
          (l4_kapply_exprs489 (l4_kra_indices516 a) (l4_klocal_expr489 (l4_kmotive_local516 m)))
          (l4_kapply_locals489 (l4_kra_arguments516 a) (l4_klocal_expr489 (l4_kra_field516 a)))) in
      let ih = l4_kind_fresh491 state (L4String L4Anonymous [105;104]) L4KDefault447 ih_ty in
      l4_kr_bind491 (l4_build_ihs521 args motives (SND ih))
        (\rest. L4KAccept491 (CONS (FST ih) (FST rest),SND rest))
    else L4KReject491 L4KMalformedDeclaration491)`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_arity_nat899 = prove
 (`!m. l4_raw_arity521 (L4KNatLit447 m) = 0`,
  REWRITE_TAC[l4_raw_arity521]);;

let l4_arity_name899 = prove
 (`!name. l4_raw_arity521 (L4KFVar447 name) = 0`,
  REWRITE_TAC[l4_raw_arity521]);;
