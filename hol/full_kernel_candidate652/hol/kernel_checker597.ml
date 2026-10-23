(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of Checker.v1410-1497. SOURCE ONLY / UNCOMPILED.
   Constructs its methods internally. Environment admission and file decoding
   remain separate obligations; this is not an end-to-end verified kernel. *)
needs "hol/kernel_conversion597.ml";;
needs "hol/inference586.ml";;
needs "hol/whnf_control594.ml";;

(* Fuel-first recursion allows the eager comparison field to choose another
   mode at the same strictly smaller depth. Calls stay under their lambdas. *)
let l4_checker_mode597 = new_recursive_definition num_RECURSION
 `(l4_checker_mode597 0 mode env ps =
    L4KMethods543
      (\g e. L4KDecline491 L4KOutOfFuel491)
      (\g e. L4KDecline491 L4KOutOfFuel491)
      (\g e. L4KDecline491 L4KOutOfFuel491)
      (\cheap g e. L4KDecline491 L4KOutOfFuel491)
      (\g t s. L4KDecline491 L4KOutOfFuel491)
      mode
      (\g t s. L4KDecline491 L4KOutOfFuel491)) /\
  (l4_checker_mode597 (SUC n) mode env ps =
    L4KMethods543
      (\g e. l4_infer_step586 e (l4_checker_mode597 n mode env ps) n env ps T g)
      (\g e. l4_infer_step586 e (l4_checker_mode597 n mode env ps) n env ps F g)
      (\g e. l4_whnf_loop594 (l4_whnf_round_limit543 mode)
        (l4_checker_mode597 n mode env ps) n env ps g e)
      (\cheap g e. l4_whnf_core_step594 (l4_checker_mode597 n mode env ps)
        n env ps cheap g e)
      (\g t s. l4_defeq_step597 (l4_checker_mode597 n mode env ps) n env ps g t s)
      mode
      (\g t s. l4_defeq_step597 (l4_checker_mode597 n L4EagerReduction543 env ps)
        n env ps g t s))`;;

let l4_checker597 = new_definition
 `l4_checker597 fuel env ps = l4_checker_mode597 fuel L4NormalReduction543 env ps`;;

let l4_infer597 = new_definition
 `l4_infer597 fuel env ps g e = l4_infer_method543 (l4_checker597 fuel env ps) g e`;;

let l4_whnf597 = new_definition
 `l4_whnf597 fuel env ps g e =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   if l4_core_supported533 env e then l4_whnf_method543 (l4_checker597 fuel env ps) g e
   else L4KDecline491 L4KUnsupportedExpression491`;;

let l4_defeq597 = new_definition
 `l4_defeq597 fuel env ps g t s =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   if l4_core_supported533 env t /\ l4_core_supported533 env s
   then l4_defeq_method543 (l4_checker597 fuel env ps) g t s
   else L4KDecline491 L4KUnsupportedExpression491`;;

let l4_check597 = new_definition
 `l4_check597 fuel env ps g e ty =
   l4_kr_bind491 (l4_sort_of543 (l4_checker597 fuel env ps) g ty) (\ignored.
     l4_kr_bind491 (l4_infer597 fuel env ps g e) (\et.
       l4_kr_bind491 (l4_defeq597 fuel env ps g et ty)
         (\ok. if ok then L4KAccept491 one else L4KReject491 L4KTypeMismatch491)))`;;

let l4_check_defeq597 = new_definition
 `l4_check_defeq597 fuel env ps g t s =
   l4_kr_bind491 (l4_infer597 fuel env ps g t) (\tt.
     l4_kr_bind491 (l4_infer597 fuel env ps g s) (\st.
       l4_kr_bind491 (l4_defeq597 fuel env ps g tt st) (\same_type.
         l4_kr_bind491
           (if same_type then L4KAccept491 one else L4KReject491 L4KTypeMismatch491)
           (\ignored.
             l4_kr_bind491 (l4_defeq597 fuel env ps g t s)
               (\same_term. if same_term then L4KAccept491 one
                 else L4KReject491 L4KNotDefinitionallyEqual491)))))`;;
