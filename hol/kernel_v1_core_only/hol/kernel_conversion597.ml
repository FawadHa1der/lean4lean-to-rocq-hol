(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of Checker.v1238-1240,1288-1386.
   SOURCE ONLY / UNCOMPILED. No runtime or logical soundness claim. *)
needs "hol/conversion_fallback596.ml";;
needs "hol/natural_reduction549.ml";;
needs "hol/constant_operations528.ml";;

let l4_conversion_progress_INDUCT597,l4_conversion_progress_RECURSION597 = define_type
 "l4_conversion_progress597 = L4ConversionDone597 bool |
   L4ConversionStuck597 l4_kexpr447 l4_kexpr447";;

(* Only rounds decreases here. Smaller-method callbacks and their fuel remain
   unchanged across delta rounds. Some false is a decisive result, not None. *)
let l4_core_lazy_delta597 = new_recursive_definition num_RECURSION
 `(l4_core_lazy_delta597 0 rec fuel env ps g t s =
    L4KDecline491 L4KOutOfFuel491) /\
  (l4_core_lazy_delta597 (SUC rounds) rec fuel env ps g t s =
    l4_kr_bind491 (l4_core_quick596 rec fuel g t s) (\quick.
      match quick with
      | SOME ok -> L4KAccept491 (L4ConversionDone597 ok)
      | NONE ->
        l4_kr_bind491 (l4_core_offset596 rec env g t s) (\offset.
          match offset with
          | SOME ok -> L4KAccept491 (L4ConversionDone597 ok)
          | NONE ->
            let eligible = l4_pair_probe_guard543
              (l4_nat_probe_head543 env (l4_ksplit_app489 t))
              (l4_nat_probe_head543 env (l4_ksplit_app489 s))
              (\ignored. l4_nat_probe_allowed543 (l4_method_mode543 rec) t s) in
            l4_kr_bind491
              (if eligible then l4_core_reduce_nat549 rec fuel env g t
               else L4KAccept491 NONE) (\tn.
                match tn with
                | SOME value ->
                    l4_kr_bind491 (l4_defeq_method543 rec g value s)
                      (\ok. L4KAccept491 (L4ConversionDone597 ok))
                | NONE ->
                  l4_kr_bind491
                    (if eligible then l4_core_reduce_nat549 rec fuel env g s
                     else L4KAccept491 NONE) (\sn.
                      match sn with
                      | SOME value ->
                          l4_kr_bind491 (l4_defeq_method543 rec g t value)
                            (\ok. L4KAccept491 (L4ConversionDone597 ok))
                      | NONE ->
                        l4_kr_bind491 (l4_core_delta_congruent595 rec fuel env g t s) (\same.
                          if same then L4KAccept491 (L4ConversionDone597 T) else
                          l4_kr_bind491 (l4_core_opposite_projection596 rec env g t s) (\projected.
                            match projected with
                            | SOME pair -> l4_core_lazy_delta597 rounds rec fuel env ps g
                                (FST pair) (SND pair)
                            | NONE ->
                              let sides = l4_core_delta_sides538 env t s in
                              l4_kr_bind491
                                (if FST sides then l4_core_unfold528 env ps t
                                 else L4KAccept491 NONE) (\td.
                                  l4_kr_bind491
                                    (if SND sides then l4_core_unfold528 env ps s
                                     else L4KAccept491 NONE) (\sd.
                                      match (td,sd) with
                                      | (NONE,NONE) -> L4KAccept491 (L4ConversionStuck597 t s)
                                      | _ ->
                                        l4_kr_bind491
                                          (match td with
                                           | SOME value -> l4_whnf_core_method543 rec T g value
                                           | NONE -> L4KAccept491 t) (\tn.
                                            l4_kr_bind491
                                              (match sd with
                                               | SOME value -> l4_whnf_core_method543 rec T g value
                                               | NONE -> L4KAccept491 s) (\sn.
                                                l4_core_lazy_delta597 rounds rec fuel env ps g tn sn)))))))))))`;;

let l4_core_finish_conversion597 = new_definition
 `l4_core_finish_conversion597 rec fuel env g t s =
   let project = \e.
     let view = l4_ksplit_app489 e in
     match FST view with
     | L4KProj447 owner idx value ->
       l4_kr_bind491 (l4_core_reduce_projection550 rec env g owner idx value)
         (\field. L4KAccept491
           (match field with
            | NONE -> NONE
            | SOME f -> SOME (l4_kapply_exprs489 (SND view) f)))
     | _ -> L4KAccept491 NONE in
   l4_kr_bind491 (project t) (\tp.
     l4_kr_bind491 (project s) (\sp.
       match (tp,sp) with
       | (SOME tn,SOME sn) -> l4_defeq_method543 rec g tn sn
       | (SOME tn,NONE) -> l4_defeq_method543 rec g tn s
       | (NONE,SOME sn) -> l4_defeq_method543 rec g t sn
       | (NONE,NONE) -> l4_compare_after_whnf596 rec fuel env g t s))`;;

let l4_core_is_true597 = new_definition
 `l4_core_is_true597 e <=>
   match e with
   | L4KConst447 n [] -> n = l4_core_true_name533
   | _ -> F`;;

let l4_core_true_shortcut597 = new_definition
 `l4_core_true_shortcut597 rec env g t s =
   if l4_core_is_true597 s /\ l4_true_probe_allowed543 (l4_method_mode543 rec) t /\
      l4_core_bool_ready533 env then
     l4_kr_bind491 (l4_whnf_method543 rec g t) (\tn. L4KAccept491 (l4_core_is_true597 tn))
   else L4KAccept491 F`;;

let l4_defeq_step597 = new_definition
 `l4_defeq_step597 methods fuel env ps g t s =
   let rec = l4_inference_only543 methods in
   l4_kr_bind491 (l4_core_quick596 rec fuel g t s) (\quick.
     match quick with
     | SOME ok -> L4KAccept491 ok
     | NONE ->
       l4_kr_bind491 (l4_core_true_shortcut597 rec env g t s) (\shortcut.
         if shortcut then L4KAccept491 T else
         l4_kr_bind491 (l4_core_proof_irrel596 rec fuel g t s) (\irrelevant.
           match irrelevant with
           | SOME ok -> L4KAccept491 ok
           | NONE ->
             l4_kr_bind491 (l4_whnf_core_method543 rec T g t) (\tn.
               l4_kr_bind491 (l4_whnf_core_method543 rec T g s) (\sn.
                 l4_kr_bind491 (l4_core_lazy_delta597 (SUC fuel) rec fuel env ps g tn sn)
                   (\progress.
                     match progress with
                     | L4ConversionDone597 ok -> L4KAccept491 ok
                     | L4ConversionStuck597 left right ->
                         l4_core_finish_conversion597 rec fuel env g left right))))))`;;
