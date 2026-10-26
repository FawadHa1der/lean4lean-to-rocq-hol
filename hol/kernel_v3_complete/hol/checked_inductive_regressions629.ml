(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed positive/adversarial source regressions. ALL UNCOMPILED.
   Conditional premises are real kernel results, not alternative entry oracles. *)
needs "hol/checked_inductive_properties629.ml";;

let l4_empty_types_no_fuel629 = prove
 (`!env ps params previous state.
     l4_check_inductive_types629 [] 0 env ps params previous state = L4KAccept491 ([],state)`,
  REWRITE_TAC[l4_check_inductive_types629]);;

let l4_empty_ctors_no_fuel629 = prove
 (`!owner idx env ps stats state.
     l4_check_ctors629 [] owner idx 0 env ps stats state = L4KAccept491 ([],state)`,
  REWRITE_TAC[l4_check_ctors629]);;

let l4_empty_all_ctors_no_fuel629 = prove
 (`!env ps stats state.
     l4_check_all_ctors629 [] 0 env ps stats state = L4KAccept491 ([],state)`,
  REWRITE_TAC[l4_check_all_ctors629]);;

let l4_positive_depth_zero_before_absence629 = prove
 (`!fuel env ps stats state.
     l4_check_positive629 0 fuel env ps stats state (L4KSort447 L4KZero447) =
       L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC[l4_check_positive629]);;

let l4_positive_kernel_zero_before_absence629 = prove
 (`!depth env ps stats state.
     l4_check_positive629 (SUC depth) 0 env ps stats state (L4KSort447 L4KZero447) =
       L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC[l4_check_positive629; l4_whnf597; l4_kr_bind491]);;

let l4_positive_projection_owner_not_ignored629 = prove
 (`!depth fuel env ps stats state e n i a.
     l4_whnf597 fuel env ps (l4_kstate_context532 state) e = L4KAccept491 (L4KProj447 n i a) /\
     l4_name_mem437 n (l4_kstats_names516 stats) /\
     l4_valid_ind_app521 stats (L4KProj447 n i a) = NONE ==>
     l4_check_positive629 (SUC depth) fuel env ps stats state e =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_positive629; l4_kr_bind491; l4_has_inductive516]);;

let l4_types_non_sort_body629 = prove
 (`!spec specs fuel env ps params previous state ty indices n us next.
     l4_kdecl_params493 (l4_kspec_decl493 spec) = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 (l4_kspec_decl493 spec)) ps
       (l4_kdecl_type493 (l4_kspec_decl493 spec)) = L4KAccept491 one /\
     l4_apply_parameters606 params fuel env ps state (l4_kdecl_type493 (l4_kspec_decl493 spec)) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (indices,(L4KConst447 n us,next)) ==>
     l4_check_inductive_types629 (CONS spec specs) fuel env ps params previous state =
       L4KReject491 L4KExpectedSort491`,
  SIMP_TAC[l4_check_inductive_types629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_ctor_invalid_result629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next checked.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KAccept491 checked /\
     l4_valid_ind_app521 stats body = NONE ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_ctor_owner_out_of_range629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next checked i.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KAccept491 checked /\
     l4_valid_ind_app521 stats body = SOME i /\
     ~(i < LENGTH (l4_kstats_names516 stats)) ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_ctor_wrong_owner629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next checked i.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KAccept491 checked /\
     l4_valid_ind_app521 stats body = SOME i /\
     i < LENGTH (l4_kstats_names516 stats) /\
     ~(EL i (l4_kstats_names516 stats) = owner) ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_ctor_raw_arity_checked629 = prove
 (`!d ctors owner idx fuel env ps stats state ty fields body next checked i.
     l4_kdecl_params493 d = ps /\
     l4_check_header607 fuel env (l4_kdecl_name493 d) ps (l4_kdecl_type493 d) = L4KAccept491 one /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 d) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 (fields,(body,next)) /\
     l4_kmap_result499 fields (l4_check_field629 fuel env ps stats next) = L4KAccept491 checked /\
     l4_valid_ind_app521 stats body = SOME i /\
     i < LENGTH (l4_kstats_names516 stats) /\
     EL i (l4_kstats_names516 stats) = owner /\
     ~(l4_raw_arity521 (l4_kdecl_type493 d) = LENGTH (l4_kstats_params516 stats) + LENGTH fields) ==>
     l4_check_ctors629 (CONS d ctors) owner idx fuel env ps stats state =
       L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC[l4_check_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_all_ctors_first_decline629 = prove
 (`!t types fuel env ps stats state reason.
     l4_check_ctors629 (l4_kspec_ctors493 (l4_kchecked_spec516 t))
       (l4_kdecl_name493 (l4_kspec_decl493 (l4_kchecked_spec516 t))) 0 fuel env ps stats state =
       L4KDecline491 reason ==>
     l4_check_all_ctors629 (CONS t types) fuel env ps stats state = L4KDecline491 reason`,
  SIMP_TAC[l4_check_all_ctors629; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_large_elimination_empty_types629 = prove
 (`!fuel env ps stats state.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [] ==>
     l4_large_elimination629 fuel env ps stats state = L4KAccept491 F`,
  SIMP_TAC[l4_large_elimination629]);;

let l4_large_elimination_no_constructors629 = prove
 (`!fuel env ps stats state t.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [] ==>
     l4_large_elimination629 fuel env ps stats state = L4KAccept491 T`,
  SIMP_TAC[l4_large_elimination629]);;

let l4_large_elimination_two_constructors629 = prove
 (`!fuel env ps stats state t a b.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [a;b] ==>
     l4_large_elimination629 fuel env ps stats state = L4KAccept491 F`,
  SIMP_TAC[l4_large_elimination629]);;

let l4_large_elimination_false_does_not_hide_decline629 = prove
 (`!fuel env ps stats state t c ty x y body next u reason.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [c] /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 c) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 ([x;y],(body,next)) /\
     l4_ind_sort606 fuel env ps next (l4_klocal_type489 x) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 F /\
     ~EX (l4_kexpr_eqb480 (l4_klocal_expr489 x)) (SND (l4_ksplit_app489 body)) /\
     l4_ind_sort606 fuel env ps next (l4_klocal_type489 y) = L4KDecline491 reason ==>
     l4_large_elimination629 fuel env ps stats state = L4KDecline491 reason`,
  SIMP_TAC[l4_large_elimination629; l4_kmap_result499; l4_kr_bind491; LET_DEF; LET_END_DEF]);;

let l4_large_elimination_checked_field_acceptance629 = prove
 (`!fuel env ps stats state t c ty x body next u prop.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [t] /\
     l4_kspec_ctors493 (l4_kchecked_spec516 t) = [c] /\
     l4_apply_parameters606 (l4_kstats_params516 stats) fuel env ps state (l4_kdecl_type493 c) =
       L4KAccept491 ty /\
     l4_open_telescope606 fuel fuel env ps state ty = L4KAccept491 ([x],(body,next)) /\
     l4_ind_sort606 fuel env ps next (l4_klocal_type489 x) = L4KAccept491 u /\
     l4_klevel_equiv555 fuel u L4KZero447 = L4KAccept491 prop ==>
     l4_large_elimination629 fuel env ps stats state =
       L4KAccept491 (prop \/ EX (l4_kexpr_eqb480 (l4_klocal_expr489 x)) (SND (l4_ksplit_app489 body)))`,
  SIMP_TAC[l4_large_elimination629; l4_kmap_result499; l4_kr_bind491; LET_DEF; LET_END_DEF; ALL]);;

let l4_large_elimination_two_types629 = prove
 (`!fuel env ps stats state a b.
     ~l4_level_never_zero521 (l4_kstats_result516 stats) /\ l4_kstats_types516 stats = [a;b] ==>
     l4_large_elimination629 fuel env ps stats state = L4KAccept491 F`,
  SIMP_TAC[l4_large_elimination629]);;
