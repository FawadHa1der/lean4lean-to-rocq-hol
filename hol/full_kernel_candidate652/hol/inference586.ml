(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of rocq/Checker.v714-785. SOURCE ONLY / UNCOMPILED.
   Internal structural inference step; not a public oracle-backed checker.
   See ../NOTICE586.txt for provenance and remaining obligations. *)
needs "hol/constant_operations528.ml";;
needs "hol/projection_typing577.ml";;
needs "hol/projection_quotient550.ml";;

(* Expression-first order exposes structural recursion. Recursive calls on
   syntax preserve the supplied fuel; genuine method callbacks consume depth
   in the eventual internally constructed checker, not in this definition. *)
let l4_infer_step586 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_infer_step586 (L4KBVar447 i) rec fuel env ps checking g =
    match l4_nth_error550 (l4_kcontext_bound532 g) i with
    | SOME b -> L4KAccept491 (l4_klift447 (l4_kbinding_type532 b) (SUC i) 0)
    | NONE -> L4KReject491 L4KLooseBoundVariable491) /\
  (l4_infer_step586 (L4KFVar447 n) rec fuel env ps checking g =
    match l4_kfind_free532 n (l4_kcontext_free532 g) with
    | SOME b -> L4KAccept491 (l4_kbinding_type532 b)
    | NONE -> L4KReject491 L4KUnknownFreeVariable491) /\
  (l4_infer_step586 (L4KMVar447 n) rec fuel env ps checking g =
    L4KReject491 L4KMetaVariable491) /\
  (l4_infer_step586 (L4KSort447 u) rec fuel env ps checking g =
    l4_kr_bind491 (l4_check_level528 ps u)
      (\ignored. L4KAccept491 (L4KSort447 (L4KSucc447 u)))) /\
  (l4_infer_step586 (L4KConst447 n us) rec fuel env ps checking g =
    l4_kr_bind491 (l4_get_constant528 env ps n us)
      (\d. L4KAccept491
        (if l4_kdecl_params493 d = [] then l4_kdecl_type493 d
         else l4_ksubst_levels488 (l4_kdecl_params493 d) us (l4_kdecl_type493 d)))) /\
  (l4_infer_step586 (L4KApp447 fn arg) rec fuel env ps checking g =
    l4_kr_bind491 (l4_infer_step586 fn rec fuel env ps checking g) (\ft.
      l4_kr_bind491 (l4_whnf_method543 rec g ft) (\reduced.
        match reduced with
        | L4KPi447 n bi domain body ->
          l4_kr_bind491
            (if checking then
              l4_kr_bind491 (l4_infer_step586 arg rec fuel env ps T g) (\arg_type.
                l4_kr_bind491 (l4_application_type_defeq543 rec g arg domain arg_type)
                  (\ok. if ok then L4KAccept491 one else L4KReject491 L4KTypeMismatch491))
             else L4KAccept491 one)
            (\ignored. L4KAccept491 (l4_kinst447 body arg))
        | _ -> L4KReject491 L4KExpectedPi491))) /\
  (l4_infer_step586 (L4KLam447 n bi domain body) rec fuel env ps checking g =
    l4_kr_bind491
      (if checking then
        l4_kr_bind491 (l4_infer_step586 domain rec fuel env ps T g) (\dt.
          l4_kr_bind491 (l4_whnf_method543 rec g dt) (\reduced.
            match reduced with
            | L4KSort447 u -> L4KAccept491 one
            | _ -> L4KReject491 L4KExpectedSort491))
       else L4KAccept491 one)
      (\ignored.
        l4_kr_bind491
          (l4_infer_step586 body rec fuel env ps checking (l4_kpush_binding532 g domain NONE))
          (\bt. L4KAccept491 (L4KPi447 n bi domain bt)))) /\
  (l4_infer_step586 (L4KPi447 n bi domain body) rec fuel env ps checking g =
    l4_kr_bind491 (l4_infer_step586 domain rec fuel env ps checking g) (\dt.
      l4_kr_bind491 (l4_whnf_method543 rec g dt) (\domain_type.
        l4_kr_bind491
          (match domain_type with
           | L4KSort447 u -> L4KAccept491 u
           | _ -> L4KReject491 L4KExpectedSort491)
          (\u. let gb = l4_kpush_binding532 g domain NONE in
            l4_kr_bind491 (l4_infer_step586 body rec fuel env ps checking gb) (\bt.
              l4_kr_bind491 (l4_whnf_method543 rec gb bt) (\body_type.
                l4_kr_bind491
                  (match body_type with
                   | L4KSort447 v -> L4KAccept491 v
                   | _ -> L4KReject491 L4KExpectedSort491)
                  (\v. L4KAccept491 (L4KSort447 (L4KIMax447 u v))))))))) /\
  (l4_infer_step586 (L4KLet447 n ty value body nd) rec fuel env ps checking g =
    l4_kr_bind491
      (if checking then
        l4_kr_bind491 (l4_infer_step586 ty rec fuel env ps T g) (\sort_type.
          l4_kr_bind491 (l4_whnf_method543 rec g sort_type) (\reduced.
            l4_kr_bind491
              (match reduced with
               | L4KSort447 u -> L4KAccept491 one
               | _ -> L4KReject491 L4KExpectedSort491)
              (\ignored.
                l4_kr_bind491 (l4_infer_step586 value rec fuel env ps T g) (\vt.
                  l4_kr_bind491 (l4_defeq_method543 rec g vt ty)
                    (\ok. if ok then L4KAccept491 one else L4KReject491 L4KTypeMismatch491)))))
       else L4KAccept491 one)
      (\ignored.
        l4_kr_bind491
          (l4_infer_step586 body rec fuel env ps checking (l4_kpush_binding532 g ty (SOME value)))
          (\bt. L4KAccept491 (l4_kinst447 bt value)))) /\
  (l4_infer_step586 (L4KNatLit447 nat_value586) rec fuel env ps checking g =
    if l4_core_nat_ready533 env
    then L4KAccept491 (L4KConst447 l4_core_nat_name533 [])
    else L4KDecline491 L4KUnsupportedExpression491) /\
  (l4_infer_step586 (L4KStrLit447 bytes) rec fuel env ps checking g =
    if l4_core_string_ready533 env then
      l4_kr_bind491 (l4_core_expand_string539 bytes)
        (\ignored. L4KAccept491 (L4KConst447 l4_core_string_name533 []))
    else L4KDecline491 L4KUnsupportedExpression491) /\
  (l4_infer_step586 (L4KProj447 owner idx value) rec fuel env ps checking g =
    match l4_core_inductive532 env owner with
    | NONE -> L4KDecline491 L4KUnsupportedExpression491
    | SOME info -> l4_core_infer_projection577
        (if checking then rec else l4_inference_only543 rec) fuel env g owner idx value) /\
  (l4_infer_step586 (L4KMData447 body) rec fuel env ps checking g =
    l4_infer_step586 body rec fuel env ps checking g)`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_infer_nat899 = prove
 (`!m methods fuel env ps checking g.
    l4_infer_step586 (L4KNatLit447 m) methods fuel env ps checking g =
      (if l4_core_nat_ready533 env
       then L4KAccept491 (L4KConst447 l4_core_nat_name533 [])
       else L4KDecline491 L4KUnsupportedExpression491)`,
  REWRITE_TAC[l4_infer_step586]);;

let l4_infer_metavar_name899 = prove
 (`!name methods fuel env ps checking g.
    l4_infer_step586 (L4KMVar447 name) methods fuel env ps checking g =
      L4KReject491 L4KMetaVariable491`,
  REWRITE_TAC[l4_infer_step586]);;
