(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of rocq/InductiveUtils.v91-162.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE606.txt and ../INTERFACE606.txt.
   Uses concrete597 kernel calls, never caller-supplied proof callbacks. *)
needs "hol/kernel_checker597.ml";;
needs "hol/nested_parameters491.ml";;
needs "hol/kernel_context532.ml";;
needs "hol/nested_keys480.ml";;

let l4_ind_sort606 = new_definition
 `l4_ind_sort606 fuel env ps state e =
   l4_kr_bind491 (l4_infer597 fuel env ps (l4_kstate_context532 state) e) (\ty.
     l4_kr_bind491 (l4_whnf597 fuel env ps (l4_kstate_context532 state) ty) (\reduced.
       match reduced with
       | L4KSort447 u -> L4KAccept491 u
       | _ -> L4KReject491 L4KExpectedSort491))`;;

(* take_arg=T is used only on the inner application of optParam/autoParam.
   It lets both calls descend through immediate children of447's recursor:
   outer App -> inner App -> domain. The public entry always supplies F.
   Other subterms, including metadata contents and defaults, are not visited. *)
let l4_consume_type_annotations_aux606 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_consume_type_annotations_aux606 (L4KBVar447 i) take_arg = L4KBVar447 i) /\
  (l4_consume_type_annotations_aux606 (L4KFVar447 n) take_arg = L4KFVar447 n) /\
  (l4_consume_type_annotations_aux606 (L4KMVar447 n) take_arg = L4KMVar447 n) /\
  (l4_consume_type_annotations_aux606 (L4KSort447 u) take_arg = L4KSort447 u) /\
  (l4_consume_type_annotations_aux606 (L4KConst447 n us) take_arg = L4KConst447 n us) /\
  (l4_consume_type_annotations_aux606 (L4KApp447 f a) take_arg =
     if take_arg then l4_consume_type_annotations_aux606 a F else
     match f with
     | L4KApp447 (L4KConst447 n us) domain ->
         if n = L4String L4Anonymous [111;112;116;80;97;114;97;109] \/
            n = L4String L4Anonymous [97;117;116;111;80;97;114;97;109]
         then l4_consume_type_annotations_aux606 f T else L4KApp447 f a
     | L4KConst447 n us ->
         if n = L4String L4Anonymous [111;117;116;80;97;114;97;109] \/
            n = L4String L4Anonymous [115;101;109;105;79;117;116;80;97;114;97;109]
         then l4_consume_type_annotations_aux606 a F else L4KApp447 f a
     | _ -> L4KApp447 f a) /\
  (l4_consume_type_annotations_aux606 (L4KLam447 n bi a b) take_arg = L4KLam447 n bi a b) /\
  (l4_consume_type_annotations_aux606 (L4KPi447 n bi a b) take_arg = L4KPi447 n bi a b) /\
  (l4_consume_type_annotations_aux606 (L4KLet447 n a v b nd) take_arg = L4KLet447 n a v b nd) /\
  (l4_consume_type_annotations_aux606 (L4KNatLit447 nat_value606) take_arg = L4KNatLit447 nat_value606) /\
  (l4_consume_type_annotations_aux606 (L4KStrLit447 bytes) take_arg = L4KStrLit447 bytes) /\
  (l4_consume_type_annotations_aux606 (L4KProj447 n i a) take_arg = L4KProj447 n i a) /\
  (l4_consume_type_annotations_aux606 (L4KMData447 a) take_arg = L4KMData447 a)`;;

let l4_consume_type_annotations606 = new_definition
 `l4_consume_type_annotations606 e = l4_consume_type_annotations_aux606 e F`;;

let l4_checked_domain606 = new_definition
 `l4_checked_domain606 fuel env ps state a =
   let cleaned = l4_consume_type_annotations606 a in
   if l4_kexpr_eqb480 a cleaned then L4KAccept491 a else
   l4_kr_bind491 (l4_defeq597 fuel env ps (l4_kstate_context532 state) a cleaned)
     (\ok. if ok then L4KAccept491 cleaned else L4KReject491 L4KTypeMismatch491)`;;

(* Success uses the existing right-nested491 payload: (locals,(body,state)).
   Depth controls this opening loop only; each concrete kernel call keeps fuel. *)
let l4_open_telescope606 = new_recursive_definition num_RECURSION
 `(l4_open_telescope606 0 fuel env ps state ty = L4KDecline491 L4KOutOfFuel491) /\
  (l4_open_telescope606 (SUC depth) fuel env ps state ty =
     l4_kr_bind491 (l4_whnf597 fuel env ps (l4_kstate_context532 state) ty) (\reduced.
       match reduced with
       | L4KPi447 user bi domain body ->
           l4_kr_bind491 (l4_checked_domain606 fuel env ps state domain) (\cleaned.
             let fresh = l4_kind_fresh491 state user bi cleaned in
             l4_kr_bind491
               (l4_open_telescope606 depth fuel env ps (SND fresh)
                 (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
               (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest)))
       | _ -> L4KAccept491 ([],(reduced,state))))`;;

let l4_open_parameters606 = new_recursive_definition num_RECURSION
 `(l4_open_parameters606 0 fuel env ps state ty = L4KAccept491 ([],(ty,state))) /\
  (l4_open_parameters606 (SUC count) fuel env ps state ty =
     l4_kr_bind491 (l4_whnf597 fuel env ps (l4_kstate_context532 state) ty) (\reduced.
       match reduced with
       | L4KPi447 user bi domain body ->
           l4_kr_bind491 (l4_checked_domain606 fuel env ps state domain) (\cleaned.
             let fresh = l4_kind_fresh491 state user bi cleaned in
             l4_kr_bind491
               (l4_open_parameters606 count fuel env ps (SND fresh)
                 (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
               (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest)))
       | _ -> L4KReject491 L4KMalformedDeclaration491))`;;

let l4_apply_parameters606 = new_recursive_definition list_RECURSION
 `(l4_apply_parameters606 [] fuel env ps state ty = L4KAccept491 ty) /\
  (l4_apply_parameters606 (CONS x xs) fuel env ps state ty =
     l4_kr_bind491 (l4_whnf597 fuel env ps (l4_kstate_context532 state) ty) (\reduced.
       match reduced with
       | L4KPi447 user bi domain body ->
           l4_kr_bind491
             (l4_defeq597 fuel env ps (l4_kstate_context532 state) domain (l4_klocal_type489 x))
             (\ok. if ok then
               l4_apply_parameters606 xs fuel env ps state (l4_kinst447 body (l4_klocal_expr489 x))
               else L4KReject491 L4KTypeMismatch491)
       | _ -> L4KReject491 L4KMalformedDeclaration491))`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_annotations_nat899 = prove
 (`!m take_arg.
    l4_consume_type_annotations_aux606 (L4KNatLit447 m) take_arg = L4KNatLit447 m`,
  REWRITE_TAC[l4_consume_type_annotations_aux606]);;

let l4_annotations_name899 = prove
 (`!name take_arg.
    l4_consume_type_annotations_aux606 (L4KFVar447 name) take_arg = L4KFVar447 name`,
  REWRITE_TAC[l4_consume_type_annotations_aux606]);;
