(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Proposed signature/prerequisite equations. ALL SCRIPTS UNCOMPILED / NOT RUN.
   Eq shape checks alone are not an environment-validity theorem. *)
needs "hol/quotient_terms608.ml";;

let l4_q_arrow_lifts608 = prove
 (`!a i. l4_q_arrow608 a (L4KBVar447 i) =
   L4KPi447 L4Anonymous L4KDefault447 a (L4KBVar447 (i + 1))`,
  REWRITE_TAC [l4_q_arrow608;l4_klift447;LT]);;

let l4_quotient_eq_signature608 = prove
 (`!u. l4_quotient_eq_type608 u =
   L4KPi447 (L4String L4Anonymous [97;108;112;104;97]) L4KImplicit447 (L4KSort447 u)
     (L4KPi447 L4Anonymous L4KDefault447 (L4KBVar447 0)
       (L4KPi447 L4Anonymous L4KDefault447 (L4KBVar447 1) (L4KSort447 L4KZero447)))`,
  REWRITE_TAC [l4_quotient_eq_type608;l4_q_local608;l4_kinitial_state491;
    l4_kind_fresh491;l4_q_arrow608;l4_klocal_expr489;l4_klocal_id489;
    l4_klocal_user489;l4_klocal_binder489;l4_klocal_type489;
    l4_kclose_pi489;l4_kabstract_local489;l4_klift447;LET_DEF;LET_END_DEF;FST;SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let l4_quotient_refl_signature608 = prove
 (`!u. l4_quotient_eq_refl_type608 u =
   L4KPi447 (L4String L4Anonymous [97;108;112;104;97]) L4KImplicit447 (L4KSort447 u)
     (L4KPi447 (L4String L4Anonymous [97]) L4KDefault447 (L4KBVar447 0)
       (L4KApp447
         (L4KApp447 (L4KApp447 (L4KConst447 l4_q_eq_name608 [u]) (L4KBVar447 1))
           (L4KBVar447 0)) (L4KBVar447 0)))`,
  REWRITE_TAC [l4_quotient_eq_refl_type608;l4_q_local608;l4_kinitial_state491;
    l4_kind_fresh491;l4_kind_id491;l4_klocal_expr489;l4_klocal_id489;
    l4_klocal_user489;l4_klocal_binder489;l4_klocal_type489;l4_kapply_exprs489;
    l4_kclose_pi489;l4_kabstract_local489;LET_DEF;LET_END_DEF;FST;SND;
    injectivity "l4_name";NOT_SUC;SUC_INJ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC []);;

let l4_quotient_type_identity608 = prove
 (`l4_kdecl_name493 (l4_canonical_quotient608 L4KQType493) = l4_q_name608 /\
   l4_kdecl_params493 (l4_canonical_quotient608 L4KQType493) =
     [L4String L4Anonymous [117]]`,
  REWRITE_TAC [l4_canonical_quotient608;l4_kdecl_name493;l4_kdecl_params493;
    LET_DEF;LET_END_DEF;FST;SND]);;
let l4_quotient_ctor_identity608 = prove
 (`l4_kdecl_name493 (l4_canonical_quotient608 L4KQCtor493) = l4_q_mk_name608 /\
   l4_kdecl_params493 (l4_canonical_quotient608 L4KQCtor493) =
     [L4String L4Anonymous [117]]`,
  REWRITE_TAC [l4_canonical_quotient608;l4_kdecl_name493;l4_kdecl_params493;
    LET_DEF;LET_END_DEF;FST;SND]);;
let l4_quotient_lift_identity608 = prove
 (`l4_kdecl_name493 (l4_canonical_quotient608 L4KQLift493) = l4_q_lift_name608 /\
   l4_kdecl_params493 (l4_canonical_quotient608 L4KQLift493) =
     [L4String L4Anonymous [117];L4String L4Anonymous [118]]`,
  REWRITE_TAC [l4_canonical_quotient608;l4_kdecl_name493;l4_kdecl_params493;
    LET_DEF;LET_END_DEF;FST;SND]);;
let l4_quotient_ind_identity608 = prove
 (`l4_kdecl_name493 (l4_canonical_quotient608 L4KQInd493) = l4_q_ind_name608 /\
   l4_kdecl_params493 (l4_canonical_quotient608 L4KQInd493) =
     [L4String L4Anonymous [117]]`,
  REWRITE_TAC [l4_canonical_quotient608;l4_kdecl_name493;l4_kdecl_params493;
    LET_DEF;LET_END_DEF;FST;SND]);;
let l4_quotient_generated_metadata608 = prove
 (`!kind. l4_kdecl_value493 (l4_canonical_quotient608 kind) = NONE /\
   l4_kdecl_kind493 (l4_canonical_quotient608 kind) = L4KDQuotient493 kind /\
   l4_kdecl_hints493 (l4_canonical_quotient608 kind) = L4KHintOpaque493`,
  MATCH_MP_TAC l4_kquotient_INDUCT493 THEN
  REWRITE_TAC [l4_canonical_quotient608;l4_kdecl_value493;l4_kdecl_kind493;
    l4_kdecl_hints493;LET_DEF;LET_END_DEF;FST;SND]);;

let l4_quotient_eq_missing608 = prove
 (`!env. l4_kfind_decl493 env l4_q_eq_name608 = NONE ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KUnknownConstant491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_not_inductive608 = prove
 (`!env d. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDAssumption493 ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_bad_universe_arity608 = prove
 (`!env d info. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [] ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_type_first608 = prove
 (`!env d info u. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [u] /\
   ~l4_kexpr_eqb480 (l4_kdecl_type493 d) (l4_quotient_eq_type608 (L4KParam447 u)) ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_empty_constructors608 = prove
 (`!env d info u. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [u] /\
   l4_kexpr_eqb480 (l4_kdecl_type493 d) (l4_quotient_eq_type608 (L4KParam447 u)) /\
   l4_kind_ctors493 info = [] ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_constructor_missing608 = prove
 (`!env d info u ctor. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [u] /\
   l4_kexpr_eqb480 (l4_kdecl_type493 d) (l4_quotient_eq_type608 (L4KParam447 u)) /\
   l4_kind_ctors493 info = [ctor] /\ l4_kfind_decl493 env ctor = NONE ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KUnknownConstant491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_wrong_parent608 = prove
 (`!env d info u ctor c ci v. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [u] /\
   l4_kexpr_eqb480 (l4_kdecl_type493 d) (l4_quotient_eq_type608 (L4KParam447 u)) /\
   l4_kind_ctors493 info = [ctor] /\ l4_kfind_decl493 env ctor = SOME c /\
   l4_kdecl_kind493 c = L4KDConstructor493 ci /\ l4_kdecl_params493 c = [v] /\
   ~(l4_kctor_induct493 ci = l4_q_eq_name608) ==>
   l4_quotient_check_eq608 env = L4KReject491 L4KMalformedDeclaration491`,
  SIMP_TAC [l4_quotient_check_eq608]);;
let l4_quotient_eq_success608 = prove
 (`!env d info u ctor c ci v. l4_kfind_decl493 env l4_q_eq_name608 = SOME d /\
   l4_kdecl_kind493 d = L4KDInductive493 info /\ l4_kdecl_params493 d = [u] /\
   l4_kexpr_eqb480 (l4_kdecl_type493 d) (l4_quotient_eq_type608 (L4KParam447 u)) /\
   l4_kind_ctors493 info = [ctor] /\ l4_kfind_decl493 env ctor = SOME c /\
   l4_kdecl_kind493 c = L4KDConstructor493 ci /\ l4_kdecl_params493 c = [v] /\
   l4_kctor_induct493 ci = l4_q_eq_name608 /\
   l4_kexpr_eqb480 (l4_kdecl_type493 c) (l4_quotient_eq_refl_type608 (L4KParam447 v)) ==>
   l4_quotient_check_eq608 env = L4KAccept491 one`,
  SIMP_TAC [l4_quotient_check_eq608]);;

(* These two equations guard the choice of Syntax.expr_eqb rather than raw
   record equality, bounded alpha, definitional equality or metadata stripping. *)
let l4_quotient_eqb_binder_flags608 = prove
 (`!n m bi bj u.
   l4_kexpr_eqb480
     (L4KPi447 n bi (L4KSort447 u) (L4KBVar447 0))
     (L4KPi447 m bj (L4KSort447 u) (L4KBVar447 0))`,
  REWRITE_TAC [l4_kexpr_eqb480]);;
let l4_quotient_eqb_keeps_metadata608 = prove
 (`!u. ~l4_kexpr_eqb480 (L4KSort447 u) (L4KMData447 (L4KSort447 u))`,
  REWRITE_TAC [l4_kexpr_eqb480;distinctness "l4_kexpr447"]);;
