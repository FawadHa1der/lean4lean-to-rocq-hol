(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/Inductive.v:395-446,470-481; see ../NOTICE522.txt.
   SOURCE ONLY / UNCOMPILED. Raw construction is NOT checked derivation. *)
needs "hol/inductive_derivation516.ml";;
needs "hol/nested_expression499.ml";;

(* EL is used only under the strict bound, implementing nth_error without
   importing502's full worklist.489 apply helpers and499 map_result are list-first. *)
let l4_recursive_value522 = new_definition
 `l4_recursive_value522 stats rec_levels motives minors a =
   if l4_kra_inductive516 a < LENGTH (l4_kstats_names516 stats) then
     let n = EL (l4_kra_inductive516 a) (l4_kstats_names516 stats) in
     let f = l4_kapply_locals489 (l4_kstats_params516 stats)
       (L4KConst447 (l4_nested_rec_name437 n) rec_levels) in
     let f = l4_kapply_locals489 (MAP l4_kmotive_local516 motives) f in
     let f = l4_kapply_locals489 (MAP l4_kminor_local516 minors) f in
     let f = l4_kapply_exprs489 (l4_kra_indices516 a) f in
     L4KAccept491 (l4_kclose_lam489 (l4_kra_arguments516 a)
       (L4KApp447 f (l4_kapply_locals489 (l4_kra_arguments516 a)
         (l4_klocal_expr489 (l4_kra_field516 a)))))
   else L4KReject491 L4KMalformedDeclaration491`;;

let l4_build_rule522 = new_definition
 `l4_build_rule522 stats rec_levels motives minors m =
   l4_kr_bind491
     (l4_kmap_result499 (l4_kminor_recursive516 m)
       (l4_recursive_value522 stats rec_levels motives minors))
     (\rec_values.
       let body = l4_kapply_exprs489 rec_values
         (l4_kapply_locals489 (l4_kminor_fields516 m)
           (l4_klocal_expr489 (l4_kminor_local516 m))) in
       L4KAccept491 (L4KRecursorRule493 (l4_kdecl_name493 (l4_kminor_ctor516 m))
         (LENGTH (l4_kminor_fields516 m))
         (l4_kclose_lam489 (l4_kstats_params516 stats)
           (l4_kclose_lam489 (MAP l4_kmotive_local516 motives)
             (l4_kclose_lam489 (MAP l4_kminor_local516 minors)
               (l4_kclose_lam489 (l4_kminor_fields516 m) body))))))`;;

(* ALL minor locals bind the type and rule RHS and contribute rec_num_minors.
   ONLY the list of rules is owner-filtered, preserving original list order. *)
let l4_build_recursor522 = new_definition
 `l4_build_recursor522 stats rec_ps motives minors k idx m =
   let t = l4_kmotive_type_info516 m in
   let major = l4_kmotive_major516 m in
   let ty = l4_kclose_pi489 (l4_kstats_params516 stats)
     (l4_kclose_pi489 (MAP l4_kmotive_local516 motives)
       (l4_kclose_pi489 (MAP l4_kminor_local516 minors)
         (l4_kclose_pi489 (l4_kchecked_indices516 t)
           (l4_kclose_pi489 [major]
             (L4KApp447 (l4_kapply_locals489 (l4_kchecked_indices516 t)
               (l4_klocal_expr489 (l4_kmotive_local516 m))) (l4_klocal_expr489 major)))))) in
   l4_kr_bind491
     (l4_kmap_result499 (FILTER (\x. l4_kminor_owner516 x = idx) minors)
       (l4_build_rule522 stats (MAP L4KParam447 rec_ps) motives minors))
     (\rules. L4KAccept491
       (L4KDeclaration493
         (l4_nested_rec_name437 (l4_kdecl_name493 (l4_kspec_decl493 (l4_kchecked_spec516 t))))
         rec_ps ty NONE
         (L4KDRecursor493 (L4KRecursorData493 (l4_kstats_names516 stats)
           (LENGTH (l4_kstats_params516 stats)) (LENGTH (l4_kchecked_indices516 t))
           (LENGTH motives) (LENGTH minors) rules k (l4_kstats_unsafe516 stats)))
         L4KHintOpaque493))`;;

let l4_build_recursors522 = new_recursive_definition list_RECURSION
 `(l4_build_recursors522 [] idx stats rec_ps motives minors k = L4KAccept491 []) /\
 (l4_build_recursors522 (CONS m remaining) idx stats rec_ps motives minors k =
   l4_kr_bind491 (l4_build_recursor522 stats rec_ps motives minors k idx m)
     (\d. l4_kr_bind491
       (l4_build_recursors522 remaining (SUC idx) stats rec_ps motives minors k)
       (\ds. L4KAccept491 (CONS d ds))))`;;

(* Original sources/generated argument order; recursion is on generated.
   First source row wins, then ALL same-name source rows are consumed. *)
let l4_verify_recursors522 = new_recursive_definition list_RECURSION
 `(l4_verify_recursors522 sources [] =
   if LENGTH sources = 0 then L4KAccept491 one else L4KReject491 L4KMalformedDeclaration491) /\
 (l4_verify_recursors522 sources (CONS d ds) =
   match l4_kfind_decl493 sources (l4_kdecl_name493 d) with
   | NONE -> L4KReject491 L4KMalformedDeclaration491
   | SOME source ->
     l4_kr_bind491 (l4_verify_rec_metadata509 source d)
       (\ignored. l4_verify_recursors522
         (FILTER (\x. ~(l4_kdecl_name493 x = l4_kdecl_name493 d)) sources) ds))`;;
