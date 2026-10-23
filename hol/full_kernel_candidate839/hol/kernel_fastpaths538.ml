(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full-syntax port of Checker.v core_alpha and delta-selection helpers.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE538.txt. No equality verdict on failure. *)
needs "hol/kernel_context532.ml";;
needs "hol/nested_keys480.ml";;

(* One shared node allowance, passed from each successful child to the next.
   The recursion is structural on the first expression, not on the allowance. *)
let l4_core_alpha538 = new_recursive_definition l4_kexpr_RECURSION447
 `(l4_core_alpha538 budget (L4KBVar447 i) s =
    if budget = 0 then (F,0) else ((s = L4KBVar447 i),budget - 1)) /\
  (l4_core_alpha538 budget (L4KFVar447 n) s =
    if budget = 0 then (F,0) else ((s = L4KFVar447 n),budget - 1)) /\
  (l4_core_alpha538 budget (L4KMVar447 n) s =
    if budget = 0 then (F,0) else ((s = L4KMVar447 n),budget - 1)) /\
  (l4_core_alpha538 budget (L4KSort447 u) s =
    if budget = 0 then (F,0) else ((s = L4KSort447 u),budget - 1)) /\
  (l4_core_alpha538 budget (L4KConst447 n us) s =
    if budget = 0 then (F,0) else ((s = L4KConst447 n us),budget - 1)) /\
  (l4_core_alpha538 budget (L4KApp447 a b) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KApp447 c d ->
        let r = l4_core_alpha538 (budget - 1) a c in
        if FST r then l4_core_alpha538 (SND r) b d else (F,SND r)
    | _ -> (F,budget - 1)) /\
  (l4_core_alpha538 budget (L4KLam447 n bi a b) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KLam447 m bj c d ->
        let r = l4_core_alpha538 (budget - 1) a c in
        if FST r then l4_core_alpha538 (SND r) b d else (F,SND r)
    | _ -> (F,budget - 1)) /\
  (l4_core_alpha538 budget (L4KPi447 n bi a b) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KPi447 m bj c d ->
        let r = l4_core_alpha538 (budget - 1) a c in
        if FST r then l4_core_alpha538 (SND r) b d else (F,SND r)
    | _ -> (F,budget - 1)) /\
  (l4_core_alpha538 budget (L4KLet447 n a v b nd) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KLet447 m c w d md ->
        let r = l4_core_alpha538 (budget - 1) a c in
        if FST r then
          let q = l4_core_alpha538 (SND r) v w in
          if FST q then l4_core_alpha538 (SND q) b d else (F,SND q)
        else (F,SND r)
    | _ -> (F,budget - 1)) /\
  (l4_core_alpha538 budget (L4KNatLit447 nat_value538) s =
    if budget = 0 then (F,0) else ((s = L4KNatLit447 nat_value538),budget - 1)) /\
  (l4_core_alpha538 budget (L4KStrLit447 bytes) s =
    if budget = 0 then (F,0) else ((s = L4KStrLit447 bytes),budget - 1)) /\
  (l4_core_alpha538 budget (L4KProj447 n i a) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KProj447 m j b ->
        if n = m /\ i = j then l4_core_alpha538 (budget - 1) a b
        else (F,budget - 1)
    | _ -> (F,budget - 1)) /\
  (l4_core_alpha538 budget (L4KMData447 a) s =
    if budget = 0 then (F,0) else
    match s with
    | L4KMData447 b -> l4_core_alpha538 (budget - 1) a b
    | _ -> (F,budget - 1))`;;

let l4_core_alpha_eq538 = new_definition
 `l4_core_alpha_eq538 t s <=> FST (l4_core_alpha538 256 t s)`;;

(* Hint selection inspects eligible delta heads; it neither validates headers
   nor unfolds. Missing/wrong-arity entries return NONE here, not Reject. *)
let l4_core_delta_info538 = new_definition
 `l4_core_delta_info538 env e =
   match FST (l4_ksplit_app489 e) with
   | L4KConst447 n us ->
     (match l4_kfind_decl493 env n with
      | NONE -> NONE
      | SOME d ->
        (match (l4_kdecl_kind493 d,l4_kdecl_value493 d) with
         | (L4KDDefinition493,SOME value) ->
             if LENGTH (l4_kdecl_params493 d) = LENGTH us then SOME d else NONE
         | (L4KDTheorem493,SOME value) ->
             if LENGTH (l4_kdecl_params493 d) = LENGTH us then SOME d else NONE
         | (L4KDPrimitive493 op,SOME value) ->
             if LENGTH (l4_kdecl_params493 d) = LENGTH us then SOME d else NONE
         | _ -> NONE))
   | _ -> NONE`;;

let l4_core_delta_head538 = new_definition
 `l4_core_delta_head538 env e <=>
   match l4_core_delta_info538 env e with NONE -> F | SOME d -> T`;;

let l4_core_delta_sides538 = new_definition
 `l4_core_delta_sides538 env t s =
   match (l4_core_delta_info538 env t,l4_core_delta_info538 env s) with
   | (SOME dt,SOME ds) ->
       if l4_khints_lt493 (l4_keffective_hints493 dt) (l4_keffective_hints493 ds)
       then (F,T)
       else if l4_khints_lt493 (l4_keffective_hints493 ds) (l4_keffective_hints493 dt)
       then (T,F) else (T,T)
   | _ -> (T,T)`;;

(* This heuristic intentionally checks only that a value lambda ignores its
   argument. Eligibility,arity,typing and declaration admission are elsewhere. *)
let l4_core_erasing_delta538 = new_definition
 `l4_core_erasing_delta538 env e <=>
   match l4_ksplit_app489 e with
   | (L4KConst447 n us,CONS arg rest) ->
     (match l4_kfind_decl493 env n with
      | NONE -> F
      | SOME d ->
        (match l4_kdecl_value493 d with
         | SOME (L4KLam447 user bi ty body) -> ~l4_core_occurs532 0 body
         | _ -> F))
   | _ -> F`;;

(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Source-only regression propositions. UNRUN; no proof-pass claim.
   Requires a separately selected source package containing the899 repairs. *)

let l4_alpha_nat899 = prove
 (`!budget m other.
    l4_core_alpha538 budget (L4KNatLit447 m) other =
      (if budget = 0 then (F,0) else ((other = L4KNatLit447 m),budget - 1))`,
  REWRITE_TAC[l4_core_alpha538]);;

let l4_alpha_name899 = prove
 (`!budget name other.
    l4_core_alpha538 budget (L4KFVar447 name) other =
      (if budget = 0 then (F,0) else ((other = L4KFVar447 name),budget - 1))`,
  REWRITE_TAC[l4_core_alpha538]);;
