(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of rocq/Inductive.v321-336,355-393.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE630.txt and ../INTERFACE630.txt. *)
needs "hol/inductive_operations521.ml";;
needs "hol/checked_telescope606.ml";;

(* Classify the saved body only after processing the tail. Even a skipped
   field retains all state allocated while opening it and processing its tail. *)
let l4_build_recursive_args630 = new_recursive_definition list_RECURSION
 `(l4_build_recursive_args630 [] fuel env ps stats state = L4KAccept491 ([],state)) /\
  (l4_build_recursive_args630 (CONS x fields) fuel env ps stats state =
    l4_kr_bind491
      (l4_open_telescope606 fuel fuel env ps state (l4_klocal_type489 x)) (\opened.
        l4_kr_bind491
          (l4_build_recursive_args630 fields fuel env ps stats (SND (SND opened)))
          (\tail.
            match l4_valid_ind_app521 stats (FST (SND opened)) with
            | NONE -> L4KAccept491 (FST tail,SND tail)
            | SOME i -> L4KAccept491
                (CONS (L4KIndRecursiveArg516 x (FST opened) i
                  (l4_ind_app_indices521 stats (FST (SND opened)))) (FST tail),
                 SND tail))))`;;

(* The owner bound is checked after IH construction, exactly as nth_error in
   Rocq. Constructor-body indices remain a raw projection, not a new gate. *)
let l4_build_minors630 = new_recursive_definition list_RECURSION
 `(l4_build_minors630 [] owner fuel env ps stats motives state = L4KAccept491 ([],state)) /\
  (l4_build_minors630 (CONS c ctors) owner fuel env ps stats motives state =
    l4_kr_bind491
      (l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 c))
      (\ty.
        l4_kr_bind491 (l4_open_telescope606 fuel fuel env ps state ty) (\opened.
          let fields = FST opened in
          let body = FST (SND opened) in
          l4_kr_bind491
            (l4_build_recursive_args630 fields fuel env ps stats (SND (SND opened)))
            (\recursive.
              l4_kr_bind491 (l4_build_ihs521 (FST recursive) motives (SND recursive)) (\ihs.
                if owner < LENGTH motives then
                  let m = EL owner motives in
                  let ctor_app = l4_kapply_locals489 fields
                    (l4_kapply_locals489 (l4_kstats_params516 stats)
                      (L4KConst447 (l4_kdecl_name493 c) (l4_kstats_levels516 stats))) in
                  let minor_ty = l4_kclose_pi489 fields (l4_kclose_pi489 (FST ihs)
                    (L4KApp447
                      (l4_kapply_exprs489 (l4_ind_app_indices521 stats body)
                        (l4_klocal_expr489 (l4_kmotive_local516 m))) ctor_app)) in
                  let minor = l4_kind_fresh491 (SND ihs) (l4_kdecl_name493 c) L4KDefault447 minor_ty in
                  l4_kr_bind491
                    (l4_build_minors630 ctors owner fuel env ps stats motives (SND minor))
                    (\tail. L4KAccept491
                      (CONS (L4KIndMinor516 c owner (FST minor) fields (FST recursive)) (FST tail),
                       SND tail))
                else L4KReject491 L4KMalformedDeclaration491)))))`;;

let l4_build_all_minors630 = new_recursive_definition list_RECURSION
 `(l4_build_all_minors630 [] owner fuel env ps stats motives state = L4KAccept491 ([],state)) /\
  (l4_build_all_minors630 (CONS t types) owner fuel env ps stats motives state =
    l4_kr_bind491
      (l4_build_minors630 (l4_kspec_ctors493 (l4_kchecked_spec516 t)) owner fuel env ps stats motives state)
      (\first.
        l4_kr_bind491
          (l4_build_all_minors630 types (SUC owner) fuel env ps stats motives (SND first))
          (\tail. L4KAccept491 (APPEND (FST first) (FST tail),SND tail))))`;;
