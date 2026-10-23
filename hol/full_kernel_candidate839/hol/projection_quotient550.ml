(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 object-language port of local rocq/Checker.v636-699.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE550.txt. Internal reduction, not
   checked admission or a public checker accepting method/verdict oracles. *)
needs "hol/kernel_control543.ml";;
needs "hol/kernel_context532.ml";;
needs "hol/kernel_declarations493.ml";;
needs "hol/kernel_locals489.ml";;
needs "hol/kernel_strings539.ml";;

(* Both helpers are list-first. nth matches Rocq nth_error's order; skip
   reverses Rocq skipn's order. Saturation avoids any partial HD/TL/EL. *)
let l4_nth_error550 = new_recursive_definition list_RECURSION
 `(l4_nth_error550 ([]:A list) idx = NONE) /\
  (l4_nth_error550 (CONS x xs) idx =
    if idx = 0 then SOME x else l4_nth_error550 xs (idx - 1))`;;

let l4_skip550 = new_recursive_definition list_RECURSION
 `(l4_skip550 ([]:A list) count = []) /\
  (l4_skip550 (CONS x xs) count =
    if count = 0 then CONS x xs else l4_skip550 xs (count - 1))`;;

let l4_core_reduce_projection_with550 = new_definition
 `l4_core_reduce_projection_with550 rec reduce env g owner idx value =
   l4_kr_bind491 (reduce g value) (\reduced.
     l4_kr_bind491
       (match reduced with
        | L4KStrLit447 bytes ->
            l4_kr_bind491 (l4_core_expand_string539 bytes)
              (\expanded. l4_whnf_method543 rec g expanded)
        | _ -> L4KAccept491 reduced)
       (\ready.
         match l4_ksplit_app489 ready with
         | (L4KConst447 n us,args) ->
             (match l4_core_constructor532 env n with
              | SOME ci ->
                  if l4_kctor_induct493 ci = owner /\
                     idx < l4_kctor_num_fields493 ci /\
                     LENGTH args = l4_kctor_num_params493 ci + l4_kctor_num_fields493 ci
                  then L4KAccept491
                    (l4_nth_error550 args (l4_kctor_num_params493 ci + idx))
                  else L4KAccept491 NONE
              | NONE -> L4KAccept491 NONE)
         | _ -> L4KAccept491 NONE))`;;

let l4_core_reduce_projection550 = new_definition
 `l4_core_reduce_projection550 rec =
    l4_core_reduce_projection_with550 rec (l4_whnf_method543 rec)`;;

let l4_core_reduce_quotient550 = new_definition
 `l4_core_reduce_quotient550 rec env g e =
   match l4_ksplit_app489 e with
   | (L4KConst447 n us,args) ->
       (match l4_kfind_decl493 env n with
        | NONE -> L4KAccept491 NONE
        | SOME d ->
            let major_pos =
              match l4_kdecl_kind493 d with
              | L4KDQuotient493 L4KQLift493 -> SOME 5
              | L4KDQuotient493 L4KQInd493 -> SOME 4
              | _ -> NONE in
            (match major_pos with
             | NONE -> L4KAccept491 NONE
             | SOME idx ->
                 (match (l4_nth_error550 args idx,l4_nth_error550 args 3) with
                  | (SOME major,SOME fn) ->
                      l4_kr_bind491 (l4_whnf_method543 rec g major) (\ready.
                        match l4_ksplit_app489 ready with
                        | (L4KConst447 cn cus,[cty;rel;representative]) ->
                            (match l4_kfind_decl493 env cn with
                             | SOME cd ->
                                 (match l4_kdecl_kind493 cd with
                                  | L4KDQuotient493 L4KQCtor493 ->
                                      L4KAccept491 (SOME
                                        (l4_kapply_exprs489 (l4_skip550 args (SUC idx))
                                          (L4KApp447 fn representative)))
                                  | _ -> L4KAccept491 NONE)
                             | NONE -> L4KAccept491 NONE)
                        | _ -> L4KAccept491 NONE)
                  | _ -> L4KAccept491 NONE)))
   | _ -> L4KAccept491 NONE`;;
