(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of rocq/Inductive.v103-127,149-169,215-297.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE629.txt and ../API629.txt.
   Public argument order matches Rocq; all checking uses concrete597/606. *)
needs "hol/inductive_operations521.ml";;
needs "hol/checked_telescope606.ml";;
needs "hol/ordinary_admission607.ml";;
needs "hol/universe_decision555.ml";;

let l4_check_inductive_types629 = new_recursive_definition list_RECURSION
 `(l4_check_inductive_types629 [] fuel env ps params result_level state =
     L4KAccept491 ([],state)) /\
  (l4_check_inductive_types629 (CONS spec specs) fuel env ps params result_level state =
     let d = l4_kspec_decl493 spec in
     if ~(l4_kdecl_params493 d = ps) then L4KReject491 L4KMalformedDeclaration491 else
     l4_kr_bind491 (l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d))
       (\header. l4_kr_bind491
         (l4_apply_parameters606 params fuel env ps state (l4_kdecl_type493 d))
         (\ty. l4_kr_bind491 (l4_open_telescope606 fuel fuel env ps state ty)
           (\opened.
             let indices = FST opened in
             let body = FST (SND opened) in
             let next = SND (SND opened) in
             match body with
             | L4KSort447 u ->
                 l4_kr_bind491
                   (match result_level with
                    | NONE -> L4KAccept491 one
                    | SOME v -> l4_kr_bind491 (l4_klevel_equiv555 fuel u v)
                        (\ok. if ok then L4KAccept491 one
                          else L4KReject491 L4KMalformedDeclaration491))
                   (\same_level. l4_kr_bind491
                     (l4_check_inductive_types629 specs fuel env ps params (SOME u) next)
                     (\tail. L4KAccept491
                       (CONS (L4KIndChecked516 spec indices u) (FST tail),SND tail)))
             | _ -> L4KReject491 L4KExpectedSort491))))`;;

(* Raw occurrence is only a guard AFTER concrete WHNF. Pi recursion freshens
   the local and instantiates its body; an external stuck occurrence rejects. *)
let l4_check_positive629 = new_recursive_definition num_RECURSION
 `(l4_check_positive629 0 fuel env ps stats state e =
     L4KDecline491 L4KOutOfFuel491) /\
  (l4_check_positive629 (SUC depth) fuel env ps stats state e =
     l4_kr_bind491 (l4_whnf597 fuel env ps (l4_kstate_context532 state) e)
       (\reduced.
         if ~l4_has_inductive516 (l4_kstats_names516 stats) reduced
         then L4KAccept491 one else
         match reduced with
         | L4KPi447 n bi a b ->
             if l4_has_inductive516 (l4_kstats_names516 stats) a
             then L4KReject491 L4KMalformedDeclaration491 else
             let fresh = l4_kind_fresh491 state n bi a in
             l4_check_positive629 depth fuel env ps stats (SND fresh)
               (l4_kinst447 b (l4_klocal_expr489 (FST fresh)))
         | _ ->
             (match l4_valid_ind_app521 stats reduced with
              | SOME i -> L4KAccept491 one
              | NONE -> L4KReject491 L4KMalformedDeclaration491)))`;;

let l4_check_field629 = new_definition
 `l4_check_field629 fuel env ps stats state field =
   l4_kr_bind491 (l4_ind_sort606 fuel env ps state (l4_klocal_type489 field)) (\u.
     l4_kr_bind491 (l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447)
       (\prop. l4_kr_bind491
         (if prop then L4KAccept491 one else
          l4_kr_bind491 (l4_klevel_le555 fuel u (l4_kstats_result516 stats))
            (\ok. if ok then L4KAccept491 one
              else L4KReject491 L4KMalformedDeclaration491))
         (\level_ok. if l4_kstats_unsafe516 stats then L4KAccept491 one else
           l4_check_positive629 fuel fuel env ps stats state (l4_klocal_type489 field))))`;;

(* All field checks use the fully opened state. The map is list-first499 and
   returns a unit list; it is not a boolean forall or an unchecked predicate. *)
let l4_check_ctors629 = new_recursive_definition list_RECURSION
 `(l4_check_ctors629 [] owner idx fuel env ps stats state =
     L4KAccept491 ([],state)) /\
  (l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
     if ~(l4_kdecl_params493 d = ps) then L4KReject491 L4KMalformedDeclaration491 else
     l4_kr_bind491 (l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d))
       (\header. l4_kr_bind491
         (l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d))
         (\ty. l4_kr_bind491 (l4_open_telescope606 fuel fuel env ps state ty)
           (\opened.
             let fields = FST opened in
             let body = FST (SND opened) in
             let next = SND (SND opened) in
             l4_kr_bind491
               (l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next))
               (\checked_fields. l4_kr_bind491
                 (match l4_valid_ind_app521 stats body with
                  | NONE -> L4KReject491 L4KMalformedDeclaration491
                  | SOME i ->
                      if i < LENGTH (l4_kstats_names516 stats) then
                        if EL i (l4_kstats_names516 stats) = owner then L4KAccept491 one
                        else L4KReject491 L4KMalformedDeclaration491
                      else L4KReject491 L4KMalformedDeclaration491)
                 (\owner_ok.
                   let actual = L4KConstructorData493 owner idx
                     (LENGTH (l4_kstats_params516 stats)) (LENGTH fields)
                     (l4_kstats_unsafe516 stats) in
                   if ~(l4_raw_arity521 (l4_kdecl_type493 d) =
                        LENGTH (l4_kstats_params516 stats) + LENGTH fields)
                   then L4KReject491 L4KMalformedDeclaration491 else
                   let generated = L4KDeclaration493 (l4_kdecl_name493 d) ps
                     (l4_kdecl_type493 d) NONE (L4KDConstructor493 actual) (l4_kdecl_hints493 d) in
                   l4_kr_bind491 (l4_check_ctors629 ctors owner (SUC idx) fuel env ps stats next)
                     (\tail. L4KAccept491 (CONS generated (FST tail),SND tail))))))))`;;

let l4_check_all_ctors629 = new_recursive_definition list_RECURSION
 `(l4_check_all_ctors629 [] fuel env ps stats state = L4KAccept491 ([],state)) /\
  (l4_check_all_ctors629 (CONS t types) fuel env ps stats state =
     let spec = l4_kchecked_spec516 t in
     l4_kr_bind491
       (l4_check_ctors629 (l4_kspec_ctors493 spec) (l4_kdecl_name493 (l4_kspec_decl493 spec))
         0 fuel env ps stats state)
       (\first. l4_kr_bind491 (l4_check_all_ctors629 types fuel env ps stats (SND first))
         (\tail. L4KAccept491 (APPEND (FST first) (FST tail),SND tail))))`;;

(* Complete result-map precedes ALL: an accepted false field does NOT hide a
   later Reject/Decline. The raw never-zero shortcut is intentional Rocq order. *)
let l4_large_elimination629 = new_definition
 `l4_large_elimination629 fuel env ps stats state =
   if l4_level_never_zero521 (l4_kstats_result516 stats) then L4KAccept491 T else
   match l4_kstats_types516 stats with
   | [t] ->
       (match l4_kspec_ctors493 (l4_kchecked_spec516 t) with
        | [] -> L4KAccept491 T
        | [c] ->
            l4_kr_bind491
              (l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 c))
              (\ty. l4_kr_bind491 (l4_open_telescope606 fuel fuel env ps state ty)
                (\opened.
                  let fields = FST opened in
                  let body = FST (SND opened) in
                  let next = SND (SND opened) in
                  let args = SND (l4_ksplit_app489 body) in
                  l4_kr_bind491
                    (l4_kmap_result499 fields (\x.
                      l4_kr_bind491 (l4_ind_sort606 fuel env ps next (l4_klocal_type489 x))
                        (\u. l4_kr_bind491 (l4_klevel_equiv555 fuel u L4KZero447)
                          (\prop. L4KAccept491
                            (prop \/ EX (l4_kexpr_eqb480 (l4_klocal_expr489 x)) args)))))
                    (\checks. L4KAccept491 (ALL (\x. x) checks))))
        | _ -> L4KAccept491 F)
   | _ -> L4KAccept491 F`;;

let l4_k_target629 = new_definition
 `l4_k_target629 fuel stats =
   l4_kr_bind491 (l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447)
     (\prop. if prop then
       (match l4_kstats_types516 stats with
       | [t] ->
           (match l4_kspec_ctors493 (l4_kchecked_spec516 t) with
            | [c] -> L4KAccept491
                (l4_raw_arity521 (l4_kdecl_type493 c) <= LENGTH (l4_kstats_params516 stats))
            | _ -> L4KAccept491 F)
       | _ -> L4KAccept491 F)
       else L4KAccept491 F)`;;
