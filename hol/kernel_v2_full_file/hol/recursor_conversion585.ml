(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of rocq/Checker.v517-583,591-634.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE585.txt.
   Internal smaller-method helper, not a public unchecked-callback checker. *)
needs "hol/recursor_helpers560.ml";;
needs "hol/kernel_control543.ml";;
needs "hol/universe_decision555.ml";;
needs "hol/kernel_naturals544.ml";;
needs "hol/kernel_strings539.ml";;
needs "hol/projection_quotient550.ml";;

(* Exactly the common branch of both Rocq constructor-head cases. The caller
   has already normalized value and ruled out a known constructor head.
   This raw helper alone neither checks those premises nor admits metadata. *)
let l4_core_to_structure585 = new_definition
 `l4_core_to_structure585 rec fuel env g owner k_rule reduced =
   if ~(k_rule \/ l4_core_structure532 env owner) then L4KAccept491 reduced else
   l4_kr_bind491 (l4_infer_method543 rec g reduced) (\inferred.
     l4_kr_bind491 (l4_whnf_method543 rec g inferred) (\ty.
       let view = l4_ksplit_app489 ty in
       match FST view with
       | L4KConst447 n us ->
         if ~(n = owner) then L4KAccept491 reduced else
         (match l4_core_make_structure557 env owner us (SND view) reduced with
          | NONE -> L4KAccept491 reduced
          | SOME candidate ->
            if k_rule then
              l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
                l4_kr_bind491 (l4_klevel_equiv555 fuel sort L4KZero447) (\prop.
                  if prop then
                    l4_kr_bind491 (l4_infer_method543 rec g candidate) (\ct.
                      l4_kr_bind491 (l4_defeq_method543 rec g ty ct) (\ok.
                        if ok then L4KAccept491 candidate else L4KAccept491 reduced))
                  else L4KAccept491 reduced))
            else
              l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
                if l4_core_level_positive555 sort then L4KAccept491 candidate
                else L4KAccept491 reduced))
       | _ -> L4KAccept491 reduced))`;;

let l4_core_to_constructor585 = new_definition
 `l4_core_to_constructor585 rec fuel env g owner k_rule value =
   l4_kr_bind491 (l4_whnf_method543 rec g value) (\reduced.
     match reduced with
     | L4KNatLit447 n ->
       if owner = l4_core_nat_name533 /\ l4_core_nat_ready533 env
       then L4KAccept491 (l4_core_nat_constructor544 n) else L4KAccept491 reduced
     | L4KStrLit447 bytes ->
       l4_kr_bind491 (l4_core_expand_string539 bytes)
         (\expanded. l4_whnf_method543 rec g expanded)
     | _ ->
       (match FST (l4_ksplit_app489 reduced) with
        | L4KConst447 n us ->
          (match l4_core_constructor532 env n with
           | SOME info -> L4KAccept491 reduced
           | NONE -> l4_core_to_structure585 rec fuel env g owner k_rule reduced)
        | _ -> l4_core_to_structure585 rec fuel env g owner k_rule reduced))`;;

(* Canonical550 supplies total nth_error and skipn with list-first arguments.
   Constructor universe arguments are deliberately ignored, as in Rocq.
   Only recursor universe arity is checked here, after major conversion. *)
let l4_core_reduce_recursor585 = new_definition
 `l4_core_reduce_recursor585 rec fuel env g e =
   let view = l4_ksplit_app489 e in
   let args = SND view in
   match FST view with
   | L4KConst447 n us ->
     (match l4_kfind_decl493 env n with
      | SOME d ->
        (match l4_kdecl_kind493 d with
         | L4KDRecursor493 info ->
           let first_index = l4_krec_num_params493 info +
             l4_krec_num_motives493 info + l4_krec_num_minors493 info in
           let major_index = first_index + l4_krec_num_indices493 info in
           (match l4_nth_error550 args major_index with
            | NONE -> L4KAccept491 NONE
            | SOME value ->
             (match l4_core_major_induct557 major_index (l4_kdecl_type493 d) with
              | NONE -> L4KReject491 L4KMalformedDeclaration491
              | SOME owner ->
                l4_kr_bind491
                  (l4_core_to_constructor585 rec fuel env g owner
                    (l4_krec_k493 info) value)
                  (\major.
                    let major_view = l4_ksplit_app489 major in
                    let fields = SND major_view in
                    match FST major_view with
                    | L4KConst447 cn ctor_us ->
                      (match (l4_core_find_rule557 cn (l4_krec_rules493 info),
                              l4_core_constructor532 env cn) with
                       | (SOME rule,SOME ci) ->
                         if l4_kctor_induct493 ci = owner /\
                            LENGTH fields = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci /\
                            l4_krule_nfields493 rule = l4_kctor_num_fields493 ci /\
                            LENGTH us = LENGTH (l4_kdecl_params493 d) then
                           L4KAccept491 (SOME (l4_kapply_exprs489
                             (APPEND (l4_kfirstn494 args first_index)
                               (APPEND (l4_skip550 fields (l4_kctor_num_params493 ci))
                                 (l4_skip550 args (SUC major_index))))
                             (l4_ksubst_levels488 (l4_kdecl_params493 d) us
                               (l4_krule_rhs493 rule))))
                         else L4KAccept491 NONE
                       | _ -> L4KAccept491 NONE)
                    | _ -> L4KAccept491 NONE)))
         | _ -> L4KAccept491 NONE)
      | NONE -> L4KAccept491 NONE)
   | _ -> L4KAccept491 NONE`;;
