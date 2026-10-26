(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Focused SOURCE-ONLY regression scripts. ALL UNCOMPILED / NOT RUN. *)
needs "hol/checked_telescope_properties606.ml";;

let l4_annotation_phase606 = prove
 (`!f a. l4_consume_type_annotations_aux606 (L4KApp447 f a) T =
   l4_consume_type_annotations606 a`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_opt606 = prove
 (`!us domain default_value.
   l4_consume_type_annotations606
     (L4KApp447 (L4KApp447
       (L4KConst447 (L4String L4Anonymous [111;112;116;80;97;114;97;109]) us) domain)
       default_value) = l4_consume_type_annotations606 domain`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_auto606 = prove
 (`!us domain tactic.
   l4_consume_type_annotations606
     (L4KApp447 (L4KApp447
       (L4KConst447 (L4String L4Anonymous [97;117;116;111;80;97;114;97;109]) us) domain)
       tactic) = l4_consume_type_annotations606 domain`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_out606 = prove
 (`!us domain.
   l4_consume_type_annotations606
     (L4KApp447 (L4KConst447 (L4String L4Anonymous [111;117;116;80;97;114;97;109]) us) domain) =
     l4_consume_type_annotations606 domain`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_semi_out606 = prove
 (`!us domain.
   l4_consume_type_annotations606
     (L4KApp447
       (L4KConst447 (L4String L4Anonymous [115;101;109;105;79;117;116;80;97;114;97;109]) us) domain) =
     l4_consume_type_annotations606 domain`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_metadata_preserved606 = prove
 (`!e. l4_consume_type_annotations606 (L4KMData447 e) = L4KMData447 e`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_lambda_preserved606 = prove
 (`!n bi a b. l4_consume_type_annotations606 (L4KLam447 n bi a b) = L4KLam447 n bi a b`,
  REWRITE_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_annotation_binary_unrecognized606 = prove
 (`!n us domain other.
   ~(n = L4String L4Anonymous [111;112;116;80;97;114;97;109]) /\
   ~(n = L4String L4Anonymous [97;117;116;111;80;97;114;97;109]) ==>
   l4_consume_type_annotations606
     (L4KApp447 (L4KApp447 (L4KConst447 n us) domain) other) =
     L4KApp447 (L4KApp447 (L4KConst447 n us) domain) other`,
  SIMP_TAC [l4_consume_type_annotations606;l4_consume_type_annotations_aux606]);;

let l4_telescope_zero_depth606 = prove
 (`!fuel env ps state ty.
   l4_open_telescope606 0 fuel env ps state ty = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_open_telescope606]);;

let l4_parameters_zero_count_zero_fuel606 = prove
 (`!env ps state ty.
   l4_open_parameters606 0 0 env ps state ty = L4KAccept491 ([],(ty,state))`,
  REWRITE_TAC [l4_open_parameters606]);;

let l4_apply_empty_zero_fuel606 = prove
 (`!env ps state ty.
   l4_apply_parameters606 [] 0 env ps state ty = L4KAccept491 ty`,
  REWRITE_TAC [l4_apply_parameters606]);;

let l4_checked_unchanged_meta_zero_fuel606 = prove
 (`!env ps state n.
   l4_checked_domain606 0 env ps state (L4KMVar447 n) = L4KAccept491 (L4KMVar447 n)`,
  REWRITE_TAC [l4_checked_domain606;l4_consume_type_annotations606;
    l4_consume_type_annotations_aux606;l4_kexpr_eqb480;LET_DEF;LET_END_DEF]);;

let l4_ind_sort_zero_fuel606 = prove
 (`!env ps state e.
   l4_ind_sort606 0 env ps state e = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_ind_sort606;l4_infer597;l4_checker597;l4_checker_mode597;
    l4_infer_method543;l4_kr_bind491]);;

let l4_open_positive_zero_fuel606 = prove
 (`!n env ps state ty.
   l4_open_telescope606 (SUC n) 0 env ps state ty = L4KDecline491 L4KOutOfFuel491 /\
   l4_open_parameters606 (SUC n) 0 env ps state ty = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_open_telescope606;l4_open_parameters606;l4_whnf597;l4_kr_bind491]);;

let l4_apply_nonempty_zero_fuel606 = prove
 (`!x xs env ps state ty.
   l4_apply_parameters606 (CONS x xs) 0 env ps state ty = L4KDecline491 L4KOutOfFuel491`,
  REWRITE_TAC [l4_apply_parameters606;l4_whnf597;l4_kr_bind491]);;
