(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of local rocq/Checker.v1166-1286, excluding the
   conversion_progress datatype owned by597. SOURCE ONLY / UNCOMPILED.
   Internal methods are supplied by the future recursive checker, not a
   public oracle-based checking API. See ../NOTICE596.txt. *)
needs "hol/kernel_control543.ml";;
needs "hol/universe_decision555.ml";;
needs "hol/kernel_fastpaths538.ml";;
needs "hol/nested_keys480.ml";;
needs "hol/kernel_strings539.ml";;
needs "hol/projection_quotient550.ml";;
needs "hol/kernel_context532.ml";;
needs "hol/conversion_helpers595.ml";;

let l4_core_try_string_expansion596 = new_definition
 `l4_core_try_string_expansion596 rec g t s =
   let expand = \bytes other.
     l4_kr_bind491 (l4_core_expand_string539 bytes) (\expanded.
       l4_kr_bind491 (l4_defeq_method543 rec g expanded other)
         (\ok. L4KAccept491 (SOME ok))) in
   match (t,s) with
   | (L4KStrLit447 bytes,L4KApp447 (L4KConst447 n []) arg) ->
       if n = l4_core_string_of_list533 then expand bytes s
       else L4KAccept491 NONE
   | (L4KApp447 (L4KConst447 n []) arg,L4KStrLit447 bytes) ->
       if n = l4_core_string_of_list533 then expand bytes t
       else L4KAccept491 NONE
   | _ -> L4KAccept491 NONE`;;

let l4_core_compare_fallback596 = new_definition
 `l4_core_compare_fallback596 rec fuel env g t s =
   l4_kr_bind491 (l4_compare_heads595 rec fuel g t s) (\ok.
     if ok then L4KAccept491 T else
     l4_kr_bind491 (l4_core_structure_eta595 rec env g t s) (\ok.
       if ok then L4KAccept491 T else
       l4_kr_bind491 (l4_core_structure_eta595 rec env g s t) (\ok.
         if ok then L4KAccept491 T else
         l4_kr_bind491 (l4_core_try_string_expansion596 rec g t s) (\expanded.
           match expanded with
           | SOME ok -> L4KAccept491 ok
           | NONE -> l4_core_unit_like595 rec env g t s))))`;;

let l4_compare_after_whnf596 = new_definition
 `l4_compare_after_whnf596 rec fuel env g t s =
   if l4_core_alpha_eq538 t s then L4KAccept491 T else
   match (t,s) with
   | (L4KSort447 u,L4KSort447 v) -> l4_klevel_equiv555 fuel u v
   | (L4KNatLit447 n,L4KNatLit447 m) -> L4KAccept491 (n = m)
   | (L4KStrLit447 a,L4KStrLit447 b) -> L4KAccept491 (a = b)
   | (L4KLam447 n bi a b,L4KLam447 m bj c d) ->
       l4_kr_bind491 (l4_defeq_method543 rec g a c) (\ok.
         if ok then l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d
         else L4KAccept491 F)
   | (L4KPi447 n bi a b,L4KPi447 m bj c d) ->
       l4_kr_bind491 (l4_defeq_method543 rec g a c) (\ok.
         if ok then l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d
         else L4KAccept491 F)
   | _ ->
       l4_kr_bind491 (l4_infer_method543 rec g t) (\ty.
         l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
           l4_kr_bind491 (l4_klevel_equiv555 fuel sort L4KZero447) (\is_prop.
             if is_prop then
               l4_kr_bind491 (l4_infer_method543 rec g s)
                 (\sty. l4_defeq_method543 rec g ty sty)
             else l4_core_compare_fallback596 rec fuel env g t s)))`;;

(* Full literal equality includes the unequal literal-kind cases. Unlike
   compare_after_whnf these cases are decisive without inference. *)
let l4_core_quick596 = new_definition
 `l4_core_quick596 rec fuel g t s =
   if l4_core_alpha_eq538 t s then L4KAccept491 (SOME T) else
   match (t,s) with
   | (L4KSort447 u,L4KSort447 v) ->
       l4_kr_bind491 (l4_klevel_equiv555 fuel u v)
         (\ok. L4KAccept491 (SOME ok))
   | (L4KNatLit447 n,L4KNatLit447 m) -> L4KAccept491 (SOME (n = m))
   | (L4KStrLit447 a,L4KStrLit447 b) -> L4KAccept491 (SOME (a = b))
   | (L4KNatLit447 n,L4KStrLit447 b) -> L4KAccept491 (SOME F)
   | (L4KStrLit447 a,L4KNatLit447 m) -> L4KAccept491 (SOME F)
   | (L4KLam447 n bi a b,L4KLam447 m bj c d) ->
       l4_kr_bind491 (l4_defeq_method543 rec g a c) (\ok.
         if ok then
           l4_kr_bind491 (l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d)
             (\ok. L4KAccept491 (SOME ok))
         else L4KAccept491 (SOME F))
   | (L4KPi447 n bi a b,L4KPi447 m bj c d) ->
       l4_kr_bind491 (l4_defeq_method543 rec g a c) (\ok.
         if ok then
           l4_kr_bind491 (l4_defeq_method543 rec (l4_kpush_binding532 g a NONE) b d)
             (\ok. L4KAccept491 (SOME ok))
         else L4KAccept491 (SOME F))
   | (L4KMData447 a,L4KMData447 b) ->
       l4_kr_bind491 (l4_defeq_method543 rec g a b)
         (\ok. L4KAccept491 (SOME ok))
   | _ -> L4KAccept491 NONE`;;

(* SOME F is a conclusive refutation by this hook, not inapplicability. *)
let l4_core_proof_irrel596 = new_definition
 `l4_core_proof_irrel596 rec fuel g t s =
   l4_kr_bind491 (l4_infer_method543 rec g t) (\ty.
     l4_kr_bind491 (l4_sort_of543 rec g ty) (\sort.
       l4_kr_bind491 (l4_klevel_equiv555 fuel sort L4KZero447) (\is_prop.
         if is_prop then
           l4_kr_bind491 (l4_infer_method543 rec g s) (\sty.
             l4_kr_bind491 (l4_defeq_method543 rec g ty sty)
               (\ok. L4KAccept491 (SOME ok)))
         else L4KAccept491 NONE)))`;;

let l4_core_offset596 = new_definition
 `l4_core_offset596 rec env g t s =
   if l4_core_nat_ready533 env then
     let pred_of = \e. match e with
       | L4KNatLit447 n ->
           if n = 0 then NONE else SOME (L4KNatLit447 (n - 1))
       | L4KApp447 (L4KConst447 n []) a ->
           if n = l4_core_succ_name533 then SOME a else NONE
       | _ -> NONE in
     let zero = \e. match e with
       | L4KNatLit447 n -> n = 0
       | L4KConst447 n [] -> n = l4_core_zero_name533
       | _ -> F in
     if zero t /\ zero s then L4KAccept491 (SOME T) else
       (match (pred_of t,pred_of s) with
        | (SOME a,SOME b) ->
            l4_kr_bind491 (l4_defeq_method543 rec g a b)
              (\ok. L4KAccept491 (SOME ok))
        | _ -> L4KAccept491 NONE)
   else L4KAccept491 NONE`;;

let l4_core_try_unfold_proj_app596 = new_definition
 `l4_core_try_unfold_proj_app596 rec g e =
   match FST (l4_ksplit_app489 e) with
   | L4KProj447 owner idx value ->
       l4_kr_bind491 (l4_whnf_core_method543 rec F g e) (\reduced.
         L4KAccept491 (if l4_kexpr_eqb480 reduced e then NONE else SOME reduced))
   | _ -> L4KAccept491 NONE`;;

let l4_core_opposite_projection596 = new_definition
 `l4_core_opposite_projection596 rec env g t s =
   match (l4_core_delta_info538 env t,l4_core_delta_info538 env s) with
   | (SOME dt,NONE) ->
       l4_kr_bind491 (l4_core_try_unfold_proj_app596 rec g s) (\reduced.
         L4KAccept491 (match reduced with
           | SOME sn -> SOME (t,sn) | NONE -> NONE))
   | (NONE,SOME ds) ->
       l4_kr_bind491 (l4_core_try_unfold_proj_app596 rec g t) (\reduced.
         L4KAccept491 (match reduced with
           | SOME tn -> SOME (tn,s) | NONE -> NONE))
   | _ -> L4KAccept491 NONE`;;
