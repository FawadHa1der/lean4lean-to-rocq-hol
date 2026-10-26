(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of local rocq/Checker.v conversion helpers.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE595.txt and ../INTERFACE595.txt.
   Internal methods only; no public oracle-backed checker or admission API. *)
needs "hol/kernel_control543.ml";;
needs "hol/universe_decision555.ml";;
needs "hol/kernel_fastpaths538.ml";;
needs "hol/projection_quotient550.ml";;

let l4_eta_compare595 = new_definition
 `l4_eta_compare595 rec g domain body other =
   l4_kr_bind491 (l4_infer_method543 rec g other) (\ty.
     l4_kr_bind491 (l4_whnf_method543 rec g ty) (\reduced.
       match reduced with
       | L4KPi447 n bi other_domain other_body ->
           l4_kr_bind491 (l4_defeq_method543 rec g domain other_domain) (\ok.
             if ok then
               l4_defeq_method543 rec (l4_kpush_binding532 g domain NONE) body
                 (L4KApp447 (l4_klift447 other 1 0) (L4KBVar447 0))
             else L4KAccept491 F)
       | _ -> L4KAccept491 F))`;;

(* List-first; no preliminary length test. The first false or error stops. *)
let l4_core_compare_args595 = new_recursive_definition list_RECURSION
 `(l4_core_compare_args595 [] rec g (ys:l4_kexpr447 list) =
     L4KAccept491 (ys = [])) /\
  (l4_core_compare_args595 (CONS x xs) rec g ys =
     match ys with
     | [] -> L4KAccept491 F
     | CONS y rest ->
         l4_kr_bind491 (l4_defeq_method543 rec g x y) (\ok.
           if ok then l4_core_compare_args595 xs rec g rest
           else L4KAccept491 F))`;;

let l4_core_same_head595 = new_definition
 `l4_core_same_head595 fuel t s =
   match (t,s) with
   | (L4KConst447 n us,L4KConst447 m vs) ->
       if n = m then l4_klevels_equiv555 us fuel vs else L4KAccept491 F
   | (L4KFVar447 n,L4KFVar447 m) -> L4KAccept491 (n = m)
   | (L4KBVar447 i,L4KBVar447 j) -> L4KAccept491 (i = j)
   | _ -> L4KAccept491 F`;;

let l4_core_congruent_apps595 = new_definition
 `l4_core_congruent_apps595 rec fuel g t s =
   match (t,s) with
   | (L4KApp447 f a,L4KApp447 h b) ->
       let tv = l4_ksplit_app489 t in
       let sv = l4_ksplit_app489 s in
       l4_kr_bind491 (l4_core_same_head595 fuel (FST tv) (FST sv)) (\same.
         if same /\ LENGTH (SND tv) = LENGTH (SND sv) then
           l4_core_compare_args595 (REVERSE (SND tv)) rec g (REVERSE (SND sv))
         else L4KAccept491 F)
   | _ -> L4KAccept491 F`;;

let l4_core_delta_congruent595 = new_definition
 `l4_core_delta_congruent595 rec fuel env g t s =
   match (l4_core_delta_info538 env t,l4_core_delta_info538 env s) with
   | (SOME dt,SOME ds) ->
       (match (l4_keffective_hints493 dt,l4_keffective_hints493 ds) with
        | (L4KHintRegular493 ht,L4KHintRegular493 hs) ->
            if ht = hs /\
               ~(l4_core_erasing_delta538 env t \/ l4_core_erasing_delta538 env s)
            then l4_core_congruent_apps595 rec fuel g t s
            else L4KAccept491 F
        | _ -> L4KAccept491 F)
   | _ -> L4KAccept491 F`;;

(* Unlike rigid congruence, this compares heads by callback and arguments in
   their original order. The left-lambda eta case precedes the right one. *)
let l4_compare_heads595 = new_definition
 `l4_compare_heads595 rec fuel g t s =
   match (t,s) with
   | (L4KConst447 n us,L4KConst447 m vs) -> l4_core_same_head595 fuel t s
   | (L4KBVar447 i,L4KBVar447 j) -> L4KAccept491 (i = j)
   | (L4KFVar447 n,L4KFVar447 m) -> L4KAccept491 (n = m)
   | (L4KProj447 n i a,L4KProj447 m j b) ->
       if n = m /\ i = j then l4_defeq_method543 rec g a b else L4KAccept491 F
   | (L4KApp447 f a,L4KApp447 h b) ->
       let tv = l4_ksplit_app489 t in
       let sv = l4_ksplit_app489 s in
       if LENGTH (SND tv) = LENGTH (SND sv) then
         l4_kr_bind491 (l4_defeq_method543 rec g (FST tv) (FST sv)) (\ok.
           if ok then l4_core_compare_args595 (SND tv) rec g (SND sv)
           else L4KAccept491 F)
       else L4KAccept491 F
   | (L4KLam447 n bi domain body,other) -> l4_eta_compare595 rec g domain body other
   | (other,L4KLam447 n bi domain body) -> l4_eta_compare595 rec g domain body other
   | _ -> L4KAccept491 F`;;

(* List-first; the old ascending index is used before advancing the tail. *)
let l4_core_compare_fields595 = new_recursive_definition list_RECURSION
 `(l4_core_compare_fields595 [] rec g owner value idx = L4KAccept491 T) /\
  (l4_core_compare_fields595 (CONS field fields) rec g owner value idx =
     l4_kr_bind491
       (l4_defeq_method543 rec g (L4KProj447 owner idx value) field) (\ok.
         if ok then l4_core_compare_fields595 fields rec g owner value (SUC idx)
         else L4KAccept491 F))`;;

let l4_core_structure_eta595 = new_definition
 `l4_core_structure_eta595 rec env g value constructed =
   let view = l4_ksplit_app489 constructed in
   match FST view with
   | L4KConst447 ctor us ->
       (match l4_core_constructor532 env ctor with
        | SOME c ->
            if l4_core_structure532 env (l4_kctor_induct493 c) /\
               LENGTH (SND view) = l4_kctor_num_params493 c + l4_kctor_num_fields493 c
            then l4_kr_bind491 (l4_infer_method543 rec g value) (\vt.
              l4_kr_bind491 (l4_infer_method543 rec g constructed) (\ct.
                l4_kr_bind491 (l4_defeq_method543 rec g vt ct) (\ok.
                  if ok then
                    l4_core_compare_fields595
                      (l4_skip550 (SND view) (l4_kctor_num_params493 c)) rec g
                      (l4_kctor_induct493 c) value 0
                  else L4KAccept491 F)))
            else L4KAccept491 F
        | NONE -> L4KAccept491 F)
   | _ -> L4KAccept491 F`;;

let l4_core_unit_like595 = new_definition
 `l4_core_unit_like595 rec env g t s =
   l4_kr_bind491 (l4_infer_method543 rec g t) (\inferred.
     l4_kr_bind491 (l4_whnf_method543 rec g inferred) (\ty.
       match FST (l4_ksplit_app489 ty) with
       | L4KConst447 owner us ->
           if l4_core_structure532 env owner then
             (match l4_core_inductive532 env owner with
              | SOME info ->
                  (match l4_kind_ctors493 info with
                   | [ctor] ->
                       (match l4_core_constructor532 env ctor with
                        | SOME c ->
                            if l4_kctor_num_fields493 c = 0 then
                              l4_kr_bind491 (l4_infer_method543 rec g s)
                                (\sty. l4_defeq_method543 rec g ty sty)
                            else L4KAccept491 F
                        | NONE -> L4KAccept491 F)
                   | _ -> L4KAccept491 F)
              | NONE -> L4KAccept491 F)
           else L4KAccept491 F
       | _ -> L4KAccept491 F))`;;
