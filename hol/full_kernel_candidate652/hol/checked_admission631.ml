(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/Inductive.v485-528,582-595. See ../NOTICE631.txt.
   SOURCE ONLY / UNCOMPILED. No caller-supplied logical verdicts. *)
needs "hol/inductive_preparation518.ml";;
needs "hol/ordinary_admission607.ml";;
needs "hol/checked_inductives629.ml";;
needs "hol/checked_minors630.ml";;
needs "hol/recursor_construction522.ml";;

let l4_inductive_derived_names631 = new_definition
 `l4_inductive_derived_names631 specs =
    let ns = MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) specs in
    APPEND ns (APPEND
      (ITLIST APPEND (MAP (\s. MAP l4_kdecl_name493 (l4_kspec_ctors493 s)) specs) [])
      (MAP l4_nested_rec_name437 ns))`;;

(* State from parameter/type/constructor checking flows into the motive and
   minor builders. Generated metadata is never copied from unverified rows. *)
let l4_derive_inductive631 = new_definition
 `l4_derive_inductive631 fuel env ps np specs =
    match specs with
    | [] -> L4KReject491 L4KMalformedDeclaration491
    | CONS first_spec rest ->
      let first = l4_kspec_decl493 first_spec in
      let unsafe = (match l4_kdecl_kind493 first with
        | L4KDInductive493 info -> l4_kind_is_unsafe493 info
        | _ -> F) in
      let ns = MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) specs in
      let derived_names = l4_inductive_derived_names631 specs in
      if ~l4_names_unique437 derived_names then
        L4KReject491 L4KDuplicateDeclaration491 else
      if ~ALL (\n. l4_kfind_decl493 env n = NONE) derived_names then
        L4KReject491 L4KDuplicateDeclaration491 else
      if ~l4_names_unique437 ps then L4KReject491 L4KDuplicateUniverse491 else
      if ~((~unsafe /\ l4_check_primitive_inductive516 ps np specs) \/
           ~EX (\n. l4_name_mem437 n l4_reserved_names607) derived_names)
      then L4KReject491 L4KMalformedDeclaration491 else
      l4_kr_bind491
        (l4_open_parameters606 np fuel env ps l4_kinitial_state491 (l4_kdecl_type493 first))
        (\opened.
          let params = FST opened in
          let s = SND (SND opened) in
          l4_kr_bind491 (l4_check_inductive_types629 specs fuel env ps params NONE s)
            (\checked_state.
              let checked = FST checked_state in
              let s = SND checked_state in
              match checked with
              | [] -> L4KReject491 L4KMalformedDeclaration491
              | CONS head tail ->
                let stats = L4KIndStats516 params checked ns (MAP L4KParam447 ps)
                  (l4_kchecked_level516 head) unsafe s in
                let inds = MAP (l4_derived_inductive516 stats) checked in
                let ind_env = APPEND inds env in
                l4_kr_bind491 (l4_check_all_ctors629 checked fuel ind_env ps stats s)
                  (\ctor_state.
                    let constructors = FST ctor_state in
                    let s = SND ctor_state in
                    let ctor_env = APPEND constructors ind_env in
                    l4_kr_bind491 (l4_large_elimination629 fuel ctor_env ps stats s)
                      (\large.
                        l4_kr_bind491 (l4_k_target629 fuel stats) (\k.
                          l4_kr_bind491 (l4_fresh_elim_name521 (SUC (LENGTH ps)) 0 ps)
                            (\fresh.
                              let elim = if large then L4KParam447 fresh else L4KZero447 in
                              let rec_ps = if large then CONS fresh ps else ps in
                              let motive_state = l4_build_motives521 checked stats elim s in
                              let motives = FST motive_state in
                              l4_kr_bind491
                                (l4_build_all_minors630 checked 0 fuel ctor_env rec_ps stats
                                  motives (SND motive_state))
                                (\minor_state.
                                  l4_kr_bind491
                                    (l4_build_recursors522 motives 0 stats rec_ps motives
                                      (FST minor_state) k)
                                    (\generated. L4KAccept491
                                      (APPEND generated (APPEND constructors inds))))))))))`;;

let l4_has_nested_inductive631 = new_definition
 `l4_has_nested_inductive631 types <=>
    EX (\d. match l4_kdecl_kind493 d with
      | L4KDInductive493 info -> ~(l4_kind_num_nested493 info = 0)
      | _ -> F) types`;;

(* Nested blocks are handled by a separate expansion driver. Even successful
   derivation is not admission until every supplied member matches it. *)
let l4_admit_inductive631 = new_definition
 `l4_admit_inductive631 fuel env types ctors recs =
    l4_kr_bind491 (l4_prepare_inductive518 env types ctors recs) (\prepared.
      if l4_has_nested_inductive631 types
      then L4KDecline491 L4KUnsupportedDeclaration491 else
      l4_kr_bind491
        (l4_derive_inductive631 fuel env (FST prepared) (FST (SND prepared))
          (SND (SND prepared)))
        (\generated.
          l4_kr_bind491 (l4_verify_members509 (APPEND types (APPEND ctors recs)) generated)
            (\verified. L4KAccept491 (APPEND generated env))))`;;
