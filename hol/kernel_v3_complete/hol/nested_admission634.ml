(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/NestedAdmission.v226-257. See ../NOTICE634.txt.
   SOURCE ONLY / UNCOMPILED. Restoration alone is not checked admission. *)
needs "hol/checked_admission631.ml";;
needs "hol/nested_transform502.ml";;
needs "hol/nested_declarations505.ml";;
needs "hol/nested_names508.ml";;

(* The older elimination record holds a pair, whereas the full kernel uses
   a context constructor. Preserve both lists, including optional values. *)
let l4_nested_checked_context634 = new_definition
 `l4_nested_checked_context634 transformed =
    let context = l4_knested_context499 transformed in
    L4KContext532 (FST context) (SND context)`;;

let l4_admit_inductive_nested634 = new_definition
 `l4_admit_inductive_nested634 fuel env types ctors recs =
    l4_kr_bind491 (l4_prepare_inductive518 env types ctors recs) (\prepared.
      let ps = FST prepared in
      let np = FST (SND prepared) in
      let specs = SND (SND prepared) in
      if EX (\d. l4_uses_reserved_nested505 (l4_kdecl_type493 d)) ctors
      then L4KReject491 L4KMalformedDeclaration491 else
      l4_kr_bind491 (l4_eliminate_nested502 fuel env ps np specs) (\transformed.
        l4_kr_bind491
          (l4_derive_inductive631 fuel env ps np (l4_knested_specs499 transformed))
          (\generated.
            if l4_knested_aux_count499 transformed = 0 then
              l4_kr_bind491
                (l4_verify_members509 (APPEND types (APPEND ctors recs)) generated)
                (\verified. L4KAccept491 (APPEND generated env))
            else match types with
            | [] -> L4KReject491 L4KMalformedDeclaration491
            | CONS main rest ->
              let all = MAP l4_kdecl_name493 types in
              let auxiliary = l4_kskipn499
                (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s))
                  (l4_knested_specs499 transformed)) (LENGTH types) in
              let rec_map = l4_auxiliary_rec_names508 auxiliary (l4_kdecl_name493 main) 1 in
              l4_kr_bind491
                (l4_kmap_result499 all (l4_restore_inductive505 generated transformed all))
                (\restored_inds.
                  l4_kr_bind491
                    (l4_kmap_result499 (MAP l4_kdecl_name493 ctors)
                      (l4_restore_constructor505 fuel generated transformed))
                    (\restored_ctors.
                      l4_kr_bind491
                        (l4_kmap_result499 (MAP l4_nested_rec_name437 (APPEND all auxiliary))
                          (l4_restore_recursor505 fuel generated transformed rec_map all))
                        (\restored_recs.
                          let restored = APPEND restored_recs (APPEND restored_ctors restored_inds) in
                          l4_kr_bind491
                            (l4_verify_members509 (APPEND types (APPEND ctors recs)) restored)
                            (\verified.
                              let final_env = APPEND restored env in
                              l4_kr_bind491
                                (l4_kmap_result499 (l4_knested_mapping499 transformed)
                                  (\entry. l4_kr_bind491
                                    (l4_infer597 fuel final_env ps
                                      (l4_nested_checked_context634 transformed) (FST entry))
                                    (\inferred. L4KAccept491 one)))
                                (\inferred. L4KAccept491 final_env))))))))`;;
