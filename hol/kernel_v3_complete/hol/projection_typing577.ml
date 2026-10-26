(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of rocq/Checker.v215-275 and Lean4Lean inferProj.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE577.txt.
   Internal method-record helper, NOT a public checker or admission API. *)
needs "hol/kernel_control543.ml";;
needs "hol/universe_decision555.ml";;
needs "hol/nested_candidate494.ml";;

let l4_projection_verify_prop577 = new_definition
 `l4_projection_verify_prop577 rec fuel g domain =
   l4_kr_bind491 (l4_sort_of543 rec g domain) (\u.
     l4_kr_bind491 (l4_klevel_equiv555 fuel u L4KZero447) (\ok.
       if ok then L4KAccept491 one else L4KReject491 L4KTypeMismatch491))`;;

(* Skip-first structural recursion; fuel belongs to universe comparison and
   is reused unchanged. Each recursive callback belongs to rec, not this fuel.
   Always instantiate skipped binders, including the nondependent branch. *)
let l4_core_projection_field577 = new_recursive_definition num_RECURSION
 `(l4_core_projection_field577 0 rec fuel g owner value maybe_prop idx ty =
   l4_kr_bind491 (l4_whnf_method543 rec g ty) (\reduced.
     match reduced with
     | L4KPi447 user bi domain body ->
       l4_kr_bind491
         (if maybe_prop then l4_projection_verify_prop577 rec fuel g domain
          else L4KAccept491 one)
         (\ignored. L4KAccept491 domain)
     | _ -> L4KReject491 L4KExpectedPi491)) /\
  (l4_core_projection_field577 (SUC skip) rec fuel g owner value maybe_prop idx ty =
   l4_kr_bind491 (l4_whnf_method543 rec g ty) (\reduced.
     match reduced with
     | L4KPi447 user bi domain body ->
       l4_kr_bind491
         (if maybe_prop /\ l4_core_occurs532 0 body
          then l4_projection_verify_prop577 rec fuel g domain
          else L4KAccept491 one)
         (\ignored. l4_core_projection_field577 skip rec fuel g owner value
           maybe_prop (SUC idx) (l4_kinst447 body (L4KProj447 owner idx value)))
     | _ -> L4KReject491 L4KExpectedPi491))`;;

(* Preserve the local reference's observable error order. Metadata is assumed
   admitted by the eventual caller: no extra safety, universe-arity, recursive-
   inductive or constructor-parent checks are silently inserted here. *)
let l4_core_infer_projection577 = new_definition
 `l4_core_infer_projection577 rec fuel env g owner idx value =
   l4_kr_bind491 (l4_infer_method543 rec g value) (\inferred.
     l4_kr_bind491 (l4_whnf_method543 rec g inferred) (\st.
       let view = l4_ksplit_app489 st in
       match (FST view,l4_core_inductive532 env owner) with
       | (L4KConst447 n us,SOME info) ->
         if n = owner /\ LENGTH (SND view) =
             l4_kind_num_params493 info + l4_kind_num_indices493 info then
           (match l4_kind_ctors493 info with
            | [ctor] ->
              (match l4_kfind_decl493 env ctor with
               | SOME d ->
                 (match l4_kdecl_kind493 d with
                  | L4KDConstructor493 c ->
                    if idx < l4_kctor_num_fields493 c then
                      l4_kr_bind491
                        (l4_core_apply_type543
                          (l4_kfirstn494 (SND view) (l4_kind_num_params493 info)) rec g
                          (l4_ksubst_levels488 (l4_kdecl_params493 d) us
                            (l4_kdecl_type493 d)))
                        (\ty. l4_kr_bind491 (l4_sort_of543 rec g st) (\u.
                          l4_core_projection_field577 idx rec fuel g owner value
                            (~l4_core_level_positive555 u) 0 ty))
                    else L4KReject491 L4KTypeMismatch491
                  | _ -> L4KReject491 L4KMalformedDeclaration491)
               | NONE -> L4KReject491 L4KUnknownConstant491)
            | _ -> L4KReject491 L4KTypeMismatch491)
         else L4KReject491 L4KTypeMismatch491
       | _ -> L4KReject491 L4KTypeMismatch491))`;;
