(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of EagerPolicy,WhnfPolicy,NatProbeDispatch and
   Checker method combinators. SOURCE ONLY / UNCOMPILED. See ../NOTICE543.txt.
   These are internal components,not a public checker accepting method oracles. *)
needs "hol/literal_readiness533.ml";;

let l4_reduction_mode_INDUCT543,l4_reduction_mode_RECURSION543 = define_type
 "l4_reduction_mode543 = L4NormalReduction543 | L4EagerReduction543";;

let l4_has_external_local_at543 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_has_external_local_at543 depth (L4KBVar447 i) <=> ~(i < depth)) /\
  (l4_has_external_local_at543 depth (L4KFVar447 n) <=> T) /\
  (l4_has_external_local_at543 depth (L4KMVar447 n) <=> F) /\
  (l4_has_external_local_at543 depth (L4KSort447 u) <=> F) /\
  (l4_has_external_local_at543 depth (L4KConst447 n us) <=> F) /\
  (l4_has_external_local_at543 depth (L4KApp447 a b) <=>
    l4_has_external_local_at543 depth a \/ l4_has_external_local_at543 depth b) /\
  (l4_has_external_local_at543 depth (L4KLam447 n bi a b) <=>
    l4_has_external_local_at543 depth a \/ l4_has_external_local_at543 (SUC depth) b) /\
  (l4_has_external_local_at543 depth (L4KPi447 n bi a b) <=>
    l4_has_external_local_at543 depth a \/ l4_has_external_local_at543 (SUC depth) b) /\
  (l4_has_external_local_at543 depth (L4KLet447 n a v b nd) <=>
    l4_has_external_local_at543 depth a \/ l4_has_external_local_at543 depth v \/
    l4_has_external_local_at543 (SUC depth) b) /\
  (l4_has_external_local_at543 depth (L4KNatLit447 nat_value543) <=> F) /\
  (l4_has_external_local_at543 depth (L4KStrLit447 bytes) <=> F) /\
  (l4_has_external_local_at543 depth (L4KProj447 n i a) <=> l4_has_external_local_at543 depth a) /\
  (l4_has_external_local_at543 depth (L4KMData447 a) <=> l4_has_external_local_at543 depth a)`;;

let l4_has_external_local543 = new_definition
 `l4_has_external_local543 e <=> l4_has_external_local_at543 0 e`;;
let l4_has_named_fvar543 = new_definition
 `l4_has_named_fvar543 e <=> l4_kfree447 e`;;

let l4_nat_probe_allowed543 = new_recursive_definition l4_reduction_mode_RECURSION543
 `(l4_nat_probe_allowed543 L4NormalReduction543 t s <=>
     ~l4_has_external_local543 t /\ ~l4_has_external_local543 s) /\
  (l4_nat_probe_allowed543 L4EagerReduction543 t s <=> T)`;;
let l4_true_probe_allowed543 = new_recursive_definition l4_reduction_mode_RECURSION543
 `(l4_true_probe_allowed543 L4NormalReduction543 t <=> ~l4_has_external_local543 t) /\
  (l4_true_probe_allowed543 L4EagerReduction543 t <=> T)`;;

let l4_eager_reduce_name543 = new_definition
 `l4_eager_reduce_name543 = L4String L4Anonymous [101;97;103;101;114;82;101;100;117;99;101]`;;
let l4_is_eager_reduce_argument543 = new_definition
 `l4_is_eager_reduce_argument543 e <=>
   match e with
   | L4KApp447 (L4KApp447 (L4KConst447 n us) ty) value -> n = l4_eager_reduce_name543
   | _ -> F`;;

(* Specialize NatProbeDispatch to the actual closed environment resolver and
   Nat.succ name used by Checker. This is eligibility,not a reduction verdict. *)
let l4_nat_probe_head543 = new_definition
 `l4_nat_probe_head543 env view <=>
   match view with
   | (L4KConst447 n [],[a]) ->
       if n = l4_core_succ_name533 then T else
       (match l4_kfind_decl493 env n with
        | SOME d -> (match l4_kdecl_kind493 d with
                     | L4KDPrimitive493 L4KPNatPred493 -> T | _ -> F)
        | NONE -> F)
   | (L4KConst447 n [],[a;b]) ->
       (match l4_kfind_decl493 env n with
        | SOME d -> (match l4_kdecl_kind493 d with
                     | L4KDPrimitive493 L4KPNatBitwise493 -> F
                     | L4KDPrimitive493 op -> T | _ -> F)
        | NONE -> F)
   | _ -> F`;;

let l4_pair_probe_guard543 = new_definition
 `l4_pair_probe_guard543 left right (eligible:1->bool) <=>
   if left \/ right then eligible one else F`;;

(* Retain all seven fields. The future fuel-recursive builder must populate
   these internally; a caller-supplied record is not a proof-checking API. *)
let l4_kmethods_INDUCT543,l4_kmethods_RECURSION543 = define_type
 "l4_kmethods543 = L4KMethods543
   (l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 l4_kresult491)
   (l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 l4_kresult491)
   (l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 l4_kresult491)
   (bool -> l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 l4_kresult491)
   (l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 -> bool l4_kresult491)
   l4_reduction_mode543
   (l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 -> bool l4_kresult491)";;

let l4_infer_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_infer_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = infer`;;
let l4_infer_type_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_infer_type_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = infer_type`;;
let l4_whnf_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_whnf_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = whnf`;;
let l4_whnf_core_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_whnf_core_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = whnf_core`;;
let l4_defeq_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_defeq_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = defeq`;;
let l4_method_mode543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_method_mode543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = mode`;;
let l4_eager_defeq_method543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_eager_defeq_method543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) = eager`;;

let l4_inference_only543 = new_recursive_definition l4_kmethods_RECURSION543
 `l4_inference_only543 (L4KMethods543 infer infer_type whnf whnf_core defeq mode eager) =
   L4KMethods543 infer_type infer_type whnf whnf_core defeq mode eager`;;

let l4_application_type_defeq543 = new_definition
 `l4_application_type_defeq543 rec g argument domain argument_type =
   if l4_is_eager_reduce_argument543 argument
   then l4_eager_defeq_method543 rec g domain argument_type
   else l4_defeq_method543 rec g domain argument_type`;;

let l4_sort_of543 = new_definition
 `l4_sort_of543 rec g e =
   l4_kr_bind491 (l4_infer_method543 rec g e) (\ty.
     l4_kr_bind491 (l4_whnf_method543 rec g ty) (\reduced.
       match reduced with
       | L4KSort447 u -> L4KAccept491 u
       | _ -> L4KReject491 L4KExpectedSort491))`;;

(* List-first argument order exposes primitive recursion; rec/g/ty are the
   remaining arguments. Empty application does not normalize its type. *)
let l4_core_apply_type543 = new_recursive_definition list_RECURSION
 `(l4_core_apply_type543 [] rec g ty = L4KAccept491 ty) /\
  (l4_core_apply_type543 (CONS a args) rec g ty =
   l4_kr_bind491 (l4_whnf_method543 rec g ty) (\reduced.
     match reduced with
     | L4KPi447 user bi domain body ->
         l4_core_apply_type543 args rec g (l4_kinst447 body a)
     | _ -> L4KReject491 L4KExpectedPi491))`;;

let l4_normal_whnf_rounds543 = new_definition `l4_normal_whnf_rounds543 = 100000`;;
let l4_eager_whnf_rounds543 = new_definition `l4_eager_whnf_rounds543 = 1000000`;;
let l4_whnf_round_limit543 = new_recursive_definition l4_reduction_mode_RECURSION543
 `(l4_whnf_round_limit543 L4NormalReduction543 = l4_normal_whnf_rounds543) /\
  (l4_whnf_round_limit543 L4EagerReduction543 = l4_eager_whnf_rounds543)`;;

let l4_whnf_round_INDUCT543,l4_whnf_round_RECURSION543 = define_type
 "l4_whnf_round543 = L4WhnfDone543 l4_kexpr447 | L4WhnfContinue543 l4_kexpr447";;

let l4_run_whnf_rounds543 = new_recursive_definition num_RECURSION
 `(l4_run_whnf_rounds543 0 step e = L4KDecline491 L4KOutOfFuel491) /\
  (l4_run_whnf_rounds543 (SUC remaining) step e =
   l4_kr_bind491 (step e) (\round.
     match round with
     | L4WhnfDone543 value -> L4KAccept491 value
     | L4WhnfContinue543 value -> l4_run_whnf_rounds543 remaining step value))`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_external_nat899 = prove
 (`!depth m. ~(l4_has_external_local_at543 depth (L4KNatLit447 m))`,
  REWRITE_TAC[l4_has_external_local_at543]);;

let l4_external_name899 = prove
 (`!depth name. l4_has_external_local_at543 depth (L4KFVar447 name)`,
  REWRITE_TAC[l4_has_external_local_at543]);;
