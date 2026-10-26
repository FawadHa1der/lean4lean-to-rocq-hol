(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of rocq/Checker.v701-711,831-922.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE594.txt.
   Internal smaller-method components, not an unchecked-callback checker. *)
needs "hol/kernel_beta526.ml";;
needs "hol/constant_operations528.ml";;
needs "hol/kernel_control543.ml";;
needs "hol/natural_reduction549.ml";;
needs "hol/projection_quotient550.ml";;
needs "hol/recursor_conversion585.ml";;
needs "hol/kernel_context532.ml";;
needs "hol/kernel_strings539.ml";;

let l4_core_reduce_head594 = new_definition
 `l4_core_reduce_head594 rec fuel env g e =
   l4_kr_bind491 (l4_core_reduce_nat549 rec fuel env g e) (\native.
     match native with
     | SOME value -> L4KAccept491 native
     | NONE ->
       l4_kr_bind491 (l4_core_reduce_quotient550 rec env g e) (\quotient.
         match quotient with
         | SOME value -> L4KAccept491 quotient
         | NONE -> l4_core_reduce_recursor585 rec fuel env g e))`;;

(* Core preserves delta heads. Its application path deliberately does not
   call core_reduce_head: only quotient and recursor reduction belong here. *)
let l4_whnf_core_step594 = new_definition
 `l4_whnf_core_step594 rec fuel env ps cheap g e =
   match e with
   | L4KApp447 f a ->
     let view = l4_ksplit_app489 e in
     let args = SND view in
     l4_kr_bind491 (l4_whnf_core_method543 rec cheap g (FST view)) (\fn.
       match fn with
       | L4KLam447 n bi domain body ->
         l4_whnf_core_method543 rec cheap g (l4_kcore_beta526 fn args)
       | _ ->
         let rebuilt = l4_kapply_exprs489 args fn in
         l4_kr_bind491 (l4_core_reduce_quotient550 rec env g rebuilt) (\quot.
           l4_kr_bind491
             (match quot with
              | SOME value -> L4KAccept491 (SOME value)
              | NONE -> l4_core_reduce_recursor585 rec fuel env g rebuilt)
             (\step. match step with
                     | SOME value -> l4_whnf_core_method543 rec cheap g value
                     | NONE -> L4KAccept491 rebuilt)))
   | L4KLet447 n ty value body nd ->
     l4_whnf_core_method543 rec cheap g (l4_kinst447 body value)
   | L4KMData447 body -> l4_whnf_core_method543 rec cheap g body
   | L4KBVar447 i ->
     (match l4_nth_error550 (l4_kcontext_bound532 g) i with
      | NONE -> L4KReject491 L4KLooseBoundVariable491
      | SOME b ->
        (match l4_kbinding_value532 b with
         | NONE -> L4KAccept491 e
         | SOME v -> l4_whnf_core_method543 rec cheap g (l4_klift447 v (SUC i) 0)))
   | L4KFVar447 n ->
     (match l4_kfind_free532 n (l4_kcontext_free532 g) with
      | NONE -> L4KReject491 L4KUnknownFreeVariable491
      | SOME b ->
        (match l4_kbinding_value532 b with
         | NONE -> L4KAccept491 e
         | SOME v -> l4_whnf_core_method543 rec cheap g v))
   | L4KConst447 n us ->
     l4_kr_bind491 (l4_get_constant528 env ps n us) (\ignored. L4KAccept491 e)
   | L4KSort447 u ->
     l4_kr_bind491 (l4_check_level528 ps u) (\ignored. L4KAccept491 e)
   | L4KMVar447 n -> L4KReject491 L4KMetaVariable491
   | L4KProj447 owner idx value ->
     l4_kr_bind491
       (l4_core_reduce_projection_with550 rec
         (if cheap then l4_whnf_core_method543 rec T else l4_whnf_method543 rec)
         env g owner idx value)
       (\step. match step with
               | SOME selected -> l4_whnf_core_method543 rec cheap g selected
               | NONE -> L4KAccept491 e)
   | L4KStrLit447 bytes ->
     l4_kr_bind491 (l4_core_expand_string539 bytes) (\ignored. L4KAccept491 e)
   | _ -> L4KAccept491 e`;;

let l4_whnf_step594 = new_definition
 `l4_whnf_step594 rec fuel env ps g e =
   l4_kr_bind491 (l4_whnf_core_step594 rec fuel env ps F g e) (\reduced.
     match reduced with
     | L4KConst447 n us ->
       if n = l4_core_zero_name533 /\ l4_core_nat_ready533 env
       then L4KAccept491 (L4KNatLit447 0)
       else l4_kr_bind491 (l4_core_unfold528 env ps reduced) (\unfolded.
         match unfolded with
         | SOME value -> l4_whnf_method543 rec g value
         | NONE -> L4KAccept491 reduced)
     | _ ->
       l4_kr_bind491 (l4_core_reduce_nat549 rec fuel env g reduced) (\native.
         match native with
         | SOME value -> L4KAccept491 value
         | NONE ->
           l4_kr_bind491 (l4_core_unfold528 env ps reduced) (\unfolded.
             match unfolded with
             | SOME value -> l4_whnf_method543 rec g value
             | NONE -> L4KAccept491 reduced)))`;;

let l4_finish_whnf_unfold594 = new_definition
 `l4_finish_whnf_unfold594 env ps e =
   l4_kr_bind491 (l4_core_unfold528 env ps e) (\unfolded.
     L4KAccept491
       (match unfolded with
        | SOME value -> L4WhnfContinue543 value
        | NONE -> L4WhnfDone543 e))`;;

let l4_whnf_round_step594 = new_definition
 `l4_whnf_round_step594 rec fuel env ps g e =
   l4_kr_bind491 (l4_whnf_core_step594 rec fuel env ps F g e) (\reduced.
     match reduced with
     | L4KConst447 n us ->
       if n = l4_core_zero_name533 /\ l4_core_nat_ready533 env
       then L4KAccept491 (L4WhnfDone543 (L4KNatLit447 0))
       else l4_finish_whnf_unfold594 env ps reduced
     | _ ->
       l4_kr_bind491 (l4_core_reduce_nat549 rec fuel env g reduced) (\native.
         match native with
         | SOME value -> L4KAccept491 (L4WhnfDone543 value)
         | NONE -> l4_finish_whnf_unfold594 env ps reduced))`;;

(* Only rounds decrease here. Recursive callbacks and reducer fuel retain
   their supplied predecessor depth throughout this loop, as in Rocq. *)
let l4_whnf_loop594 = new_definition
 `l4_whnf_loop594 rounds rec fuel env ps g e =
   l4_run_whnf_rounds543 rounds (l4_whnf_round_step594 rec fuel env ps g) e`;;
