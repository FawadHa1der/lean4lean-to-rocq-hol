(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local rocq/NestedTransform.v:234-310. See ../NOTICE498.txt.
   SOURCE ONLY / UNCOMPILED. Provisional syntax, not checked admission. *)
needs "hol/nested_candidate494.ml";;
needs "hol/kernel_universes488.ml";;

let l4_knested_used_names498 = new_definition
 `l4_knested_used_names498 env w =
   APPEND (MAP l4_kdecl_name493 env)
    (APPEND (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) (l4_knw_specs494 w))
     (APPEND (MAP (\s. l4_nested_rec_name437 (l4_kdecl_name493 (l4_kspec_decl493 s)))
                   (l4_knw_specs494 w))
      (FLAT (MAP (\s. MAP l4_kdecl_name493 (l4_kspec_ctors493 s)) (l4_knw_specs494 w)))))`;;

(* Empty/mismatched name lists precede the fuel test. Metadata is rebuilt
   provisionally; the old constructor's owner/index/flags are not trusted. *)
let l4_nested_make_ctors498 = new_recursive_definition list_RECURSION
 `(l4_nested_make_ctors498 [] fuel env ps locals us params owner news idx =
   if news = [] then L4KAccept491 [] else L4KDecline491 L4KUnsupportedDeclaration491) /\
 (l4_nested_make_ctors498 (CONS old olds) fuel env ps locals us params owner news idx =
   if news = [] then L4KDecline491 L4KUnsupportedDeclaration491 else
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   match l4_kfind_decl493 env old with
   | NONE -> L4KDecline491 L4KUnsupportedDeclaration491
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDConstructor493 data ->
        if LENGTH (l4_kdecl_params493 d) = LENGTH us then
          l4_kr_bind491
           (l4_nested_instantiate_params491 params (fuel - 1)
             (l4_ksubst_levels488 (l4_kdecl_params493 d) us (l4_kdecl_type493 d)))
           (\ty. l4_kr_bind491
             (l4_nested_make_ctors498 olds (fuel - 1) env ps locals us params owner
               (TL news) (SUC idx))
             (\rest. L4KAccept491
               (CONS (L4KDeclaration493 (HD news) ps (l4_kclose_pi489 locals ty) NONE
                 (L4KDConstructor493
                   (L4KConstructorData493 owner idx (LENGTH locals) 0 F))
                 L4KHintOpaque493) rest)))
        else L4KReject491 L4KUniverseArity491
      | _ -> L4KDecline491 L4KUnsupportedDeclaration491))`;;

(* Family-first recursion, with the same depth-fuel budget passed to each
   sibling helper. State appends keep prior specs/mappings in first-match order. *)
let l4_nested_expand_family498 = new_recursive_definition list_RECURSION
 `(l4_nested_expand_family498 [] fuel env ps params locals us oldparams w = L4KAccept491 w) /\
 (l4_nested_expand_family498 (CONS old family) fuel env ps params locals us oldparams w =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   match l4_kfind_decl493 env old with
   | NONE -> L4KDecline491 L4KUnsupportedDeclaration491
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDInductive493 data ->
        if LENGTH (l4_kdecl_params493 d) = LENGTH us then
          if l4_kind_num_params493 data = LENGTH oldparams then
            l4_kr_bind491
             (l4_kr_from_na491
               (l4_nested_unique_aux437 (fuel - 1) (l4_knested_used_names498 env w)
                 old (l4_kind_ctors493 data) (l4_knw_next_aux494 w)))
             (\fresh.
               let aux = FST fresh in
               let names = FST (SND fresh) in
               let next = SND (SND fresh) in
               l4_kr_bind491
                (l4_nested_instantiate_params491 oldparams (fuel - 1)
                  (l4_ksubst_levels488 (l4_kdecl_params493 d) us (l4_kdecl_type493 d)))
                (\ty. l4_kr_bind491
                 (l4_kr_from_na491
                   (l4_nested_rebase449
                     (l4_kapply_exprs489 oldparams (L4KConst447 old us)) (fuel - 1)
                     (MAP l4_klocal_id489 locals) (MAP l4_klocal_id489 params)))
                 (\key. l4_kr_bind491
                  (l4_nested_make_ctors498 (l4_kind_ctors493 data) (fuel - 1)
                    env ps locals us oldparams aux names 0)
                  (\ctors.
                    let spec = L4KIndSpec493
                      (L4KDeclaration493 aux ps (l4_kclose_pi489 locals ty) NONE
                        (L4KDInductive493
                          (L4KInductiveData493 (LENGTH locals) 0 [] names 0 F F F))
                        L4KHintOpaque493) ctors in
                    l4_nested_expand_family498 family (fuel - 1) env ps params locals us oldparams
                      (L4KNestedWork494 (APPEND (l4_knw_specs494 w) [spec])
                        (APPEND (l4_knw_mapping494 w) [(key,aux)]) next
                        (l4_knw_next_local494 w))))))
          else L4KDecline491 L4KUnsupportedDeclaration491
        else L4KReject491 L4KUniverseArity491
      | _ -> L4KDecline491 L4KUnsupportedDeclaration491))`;;
