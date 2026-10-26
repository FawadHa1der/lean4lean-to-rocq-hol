(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed operational properties of the actual629 definitions.
   ALL SCRIPTS UNCOMPILED; no tactic acceptance or semantic soundness claimed. *)
needs "hol/checked_inductives629.ml";;

let l4_types_params_before_header629 = prove
 (`!spec specs fuel env ps params previous state.
     ~(l4_kdecl_params493 (l4_kspec_decl493 spec) = ps) ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params previous state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_inductive_types629; LET_DEF; LET_END_DEF]);;

let l4_types_header_reject629 = prove
 (`!spec specs fuel env ps params previous state reason.
     l4_kdecl_params493 (l4_kspec_decl493 spec) = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 (l4_kspec_decl493 spec)) ps
       (l4_kdecl_type493 (l4_kspec_decl493 spec)) = L4KReject491 reason ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params previous state =
       L4KReject491 reason`,
  SIMP_TAC[l4_check_inductive_types629; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let l4_types_header_decline629 = prove
 (`!spec specs fuel env ps params previous state reason.
     l4_kdecl_params493 (l4_kspec_decl493 spec) = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 (l4_kspec_decl493 spec)) ps
       (l4_kdecl_type493 (l4_kspec_decl493 spec)) = L4KDecline491 reason ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params previous state =
       L4KDecline491 reason`,
  SIMP_TAC[l4_check_inductive_types629; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let l4_types_success_threads_level_and_state629 = prove
 (`!spec specs fuel env ps params state ty indices u next rest final.
     l4_kdecl_params493 (l4_kspec_decl493 spec) = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 (l4_kspec_decl493 spec)) ps
       (l4_kdecl_type493 (l4_kspec_decl493 spec)) = L4KAccept491 one /\
     l4_apply_parameters606 params fuel env ps state (l4_kdecl_type493 (l4_kspec_decl493 spec)) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (indices,(L4KSort447 u,next)) /\
     l4_check_inductive_types629 specs fuel env ps params (SOME u) next =
       L4KAccept491 (rest,final) ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params NONE state =
       L4KAccept491 (CONS (L4KIndChecked516 spec indices u) rest,final)`,
  SIMP_TAC[l4_check_inductive_types629; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let l4_types_level_mismatch629 = prove
 (`!spec specs fuel env ps params state ty indices u v next.
     l4_kdecl_params493 (l4_kspec_decl493 spec) = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 (l4_kspec_decl493 spec)) ps
       (l4_kdecl_type493 (l4_kspec_decl493 spec)) = L4KAccept491 one /\
     l4_apply_parameters606 params fuel env ps state (l4_kdecl_type493 (l4_kspec_decl493 spec)) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (indices,(L4KSort447 u,next)) /\
     l4_klevel_equiv555 fuel u v = L4KAccept491 F ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params (SOME v) state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_inductive_types629; LET_DEF; LET_END_DEF; l4_kr_bind491]);;

let l4_positive_whnf_reject629 = prove
 (`!depth fuel env ps stats state e reason.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KReject491 reason ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e = L4KReject491 reason`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491]);;

let l4_positive_whnf_decline629 = prove
 (`!depth fuel env ps stats state e reason.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KDecline491 reason ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e = L4KDecline491 reason`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491]);;

let l4_positive_absent_after_whnf629 = prove
 (`!depth fuel env ps stats state e reduced.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 reduced /\
     ~l4_has_inductive516 (l4_kstats_names516 stats) reduced ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e = L4KAccept491 one`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491]);;

let l4_positive_negative_domain629 = prove
 (`!depth fuel env ps stats state e n bi a b.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 (L4KPi447 n bi a b) /\
     l4_has_inductive516 (l4_kstats_names516 stats) a ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491; l4_has_inductive516]);;

let l4_positive_pi_fresh_instantiation629 = prove
 (`!depth fuel env ps stats state e n bi a b.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 (L4KPi447 n bi a b) /\
     ~l4_has_inductive516 (l4_kstats_names516 stats) a /\
     l4_has_inductive516 (l4_kstats_names516 stats) b ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e =
       l4_check_positive629 depth fuel env ps stats
         (SND (l4_kind_fresh491 state n bi a))
         (l4_kinst447 b (l4_klocal_expr489 (FST (l4_kind_fresh491 state n bi a))))`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491; l4_has_inductive516; LET_DEF; LET_END_DEF]);;

let l4_positive_valid_application629 = prove
 (`!depth fuel env ps stats state e f a i.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 (L4KApp447 f a) /\
     l4_has_inductive516 (l4_kstats_names516 stats) (L4KApp447 f a) /\
     l4_valid_ind_app521 stats (L4KApp447 f a) = SOME i ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e = L4KAccept491 one`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491]);;

let l4_positive_stuck_application629 = prove
 (`!depth fuel env ps stats state e f a.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 (L4KApp447 f a) /\
     l4_has_inductive516 (l4_kstats_names516 stats) (L4KApp447 f a) /\
     l4_valid_ind_app521 stats (L4KApp447 f a) = NONE ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491]);;

let l4_field_sort_first629 = prove
 (`!fuel env ps stats state field reason.
     l4_ind_sort606 fuel env ps state (l4_klocal_type489 field) = L4KReject491 reason ==>
     l4_check_field629 fuel env ps stats state field = L4KReject491 reason`,
  SIMP_TAC[l4_check_field629; l4_kr_bind491]);;

let l4_field_prop_still_checks_positivity629 = prove
 (`!fuel env ps stats state field u.
     l4_ind_sort606 fuel env ps state (l4_klocal_type489 field) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 T /\
     ~l4_kstats_unsafe516 stats ==>
     l4_check_field629 fuel env ps stats state field =
       l4_check_positive629 fuel fuel env ps stats state (l4_klocal_type489 field)`,
  SIMP_TAC[l4_check_field629; l4_kr_bind491]);;

let l4_field_universe_bound_false629 = prove
 (`!fuel env ps stats state field u.
     l4_ind_sort606 fuel env ps state (l4_klocal_type489 field) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 F /\
     l4_klevel_le555 fuel u (l4_kstats_result516 stats) = L4KAccept491 F ==>
     l4_check_field629 fuel env ps stats state field = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_field629; l4_kr_bind491]);;

let l4_field_bound_decline_before_unsafe629 = prove
 (`!fuel env ps stats state field u reason.
     l4_ind_sort606 fuel env ps state (l4_klocal_type489 field) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 F /\
     l4_klevel_le555 fuel u (l4_kstats_result516 stats) = L4KDecline491 reason ==>
     l4_check_field629 fuel env ps stats state field = L4KDecline491 reason`,
  SIMP_TAC[l4_check_field629; l4_kr_bind491]);;

let l4_field_unsafe_after_level629 = prove
 (`!fuel env ps stats state field u.
     l4_ind_sort606 fuel env ps state (l4_klocal_type489 field) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 F /\
     l4_klevel_le555 fuel u (l4_kstats_result516 stats) = L4KAccept491 T /\
     l4_kstats_unsafe516 stats ==>
     l4_check_field629 fuel env ps stats state field = L4KAccept491 one`,
  SIMP_TAC[l4_check_field629; l4_kr_bind491]);;

let l4_ctors_params_before_header629 = prove
 (`!d ctors owner idx fuel env ps stats state.
     ~(l4_kdecl_params493 d = ps) ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_ctors629]);;

let l4_ctors_header_reject629 = prove
 (`!d ctors owner idx fuel env ps stats state reason.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) =
       L4KReject491 reason ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state = L4KReject491 reason`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491]);;

let l4_ctors_fields_before_result629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next reason.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KReject491 reason ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state = L4KReject491 reason`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_ctors_checked_metadata_and_state629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next checked i rest final.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KAccept491 checked /\
     l4_valid_ind_app521 stats body = SOME i /\
     i < LENGTH (l4_kstats_names516 stats) /\
     EL i (l4_kstats_names516 stats) = owner /\
     l4_raw_arity521 (l4_kdecl_type493 d) = LENGTH (l4_kstats_params516 stats) + LENGTH fields /\
     l4_check_ctors629 ctors owner (SUC idx) fuel env ps stats next = L4KAccept491 (rest,final) ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KAccept491
         (CONS (L4KDeclaration493 (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) NONE
           (L4KDConstructor493 (L4KConstructorData493 owner idx
             (LENGTH (l4_kstats_params516 stats)) (LENGTH fields) (l4_kstats_unsafe516 stats)))
           (l4_kdecl_hints493 d)) rest,final)`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_all_ctors_ordered_state629 = prove
 (`!t types fuel env ps stats state first next rest final.
     l4_check_ctors629 (l4_kspec_ctors493 (l4_kchecked_spec516 t))
       (l4_kdecl_name493 (l4_kspec_decl493 (l4_kchecked_spec516 t))) 0 fuel env ps stats state =
       L4KAccept491 (first,next) /\
     l4_check_all_ctors629 types fuel env ps stats next = L4KAccept491 (rest,final) ==>
     l4_check_all_ctors629 (CONS t types) fuel env ps stats state =
       L4KAccept491 (APPEND first rest,final)`,
  SIMP_TAC[l4_check_all_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_large_elimination_positive_shortcut629 = prove
 (`!fuel env ps stats state.
     l4_level_never_zero521 (l4_kstats_result516 stats) ==>
     l4_large_elimination629 fuel env ps stats state = L4KAccept491 T`,
  SIMP_TAC[l4_large_elimination629]);;

let l4_large_elimination_typecheck_before_membership629 = prove
 (`!fuel env ps stats state t c ty x body next reason.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\
     l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [c] /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 c) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 ([x],(body,next)) /\
     l4_ind_sort606 fuel env ps next (l4_klocal_type489 x) = L4KReject491 reason ==>
     l4_large_elimination629 fuel env ps stats state = L4KReject491 reason`,
  SIMP_TAC[l4_large_elimination629; l4_kmap_result499; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_k_target_universe_decline629 = prove
 (`!fuel stats reason.
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KDecline491 reason ==>
     l4_k_target629 fuel stats = L4KDecline491 reason`,
  SIMP_TAC[l4_k_target629; l4_kr_bind491]);;

let l4_k_target_nonprop629 = prove
 (`!fuel stats.
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 F ==>
     l4_k_target629 fuel stats = L4KAccept491 F`,
  SIMP_TAC[l4_k_target629; l4_kr_bind491]);;

let l4_k_target_singleton_arity629 = prove
 (`!fuel stats t c.
     l4_klevel_equiv555 fuel (l4_kstats_result516 stats) L4KZero447 = L4KAccept491 T /\
     l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [c] ==>
     l4_k_target629 fuel stats =
       L4KAccept491 (l4_raw_arity521 (l4_kdecl_type493 c) <= LENGTH (l4_kstats_params516 stats))`,
  SIMP_TAC[l4_k_target629; l4_kr_bind491]);;
