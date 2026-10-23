(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of verified positive and negative definitional-equality
   memoization (EquivManager / DefEqCache). Proves exact refinement of uncached
   l4_defeq597 under cache soundness. Zero new axioms. *)
needs "hol/kernel_checker597.ml";;

let l4_defeq_cache_key_INDUCT964,l4_defeq_cache_key_RECURSION964 = define_type
 "l4_defeq_cache_key964 = L4DefEqKey964 num l4_kexpr447 l4_kexpr447";;

let l4_dck_depth964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_depth964 (L4DefEqKey964 d lhs_e rhs_e) = d`;;
let l4_dck_lhs964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_lhs964 (L4DefEqKey964 d lhs_e rhs_e) = lhs_e`;;
let l4_dck_rhs964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_rhs964 (L4DefEqKey964 d lhs_e rhs_e) = rhs_e`;;

let l4_key_of_query964 = new_definition
 `l4_key_of_query964 (g:l4_kcontext532) (t:l4_kexpr447) (s:l4_kexpr447) =
   L4DefEqKey964 (LENGTH (l4_kcontext_bound532 g)) t s`;;

let l4_cache_lookup964 = new_recursive_definition list_RECURSION
 `(l4_cache_lookup964 [] (k:l4_defeq_cache_key964) = NONE) /\
  (l4_cache_lookup964 (CONS (entry : l4_defeq_cache_key964 # bool) rest) k =
    if FST entry = k then SOME (SND entry)
    else l4_cache_lookup964 rest k)`;;

let l4_cache_insert964 = new_definition
 `l4_cache_insert964 (k:l4_defeq_cache_key964) (verdict:bool) cache =
   CONS (k, verdict) cache`;;

let l4_cache_apply_result964 = new_recursive_definition l4_kresult_RECURSION491
 `(l4_cache_apply_result964 k cache (L4KAccept491 verdict) =
    (l4_cache_insert964 k verdict cache, L4KAccept491 verdict)) /\
  (l4_cache_apply_result964 k cache (L4KReject491 err) =
    (cache, L4KReject491 err)) /\
  (l4_cache_apply_result964 k cache (L4KDecline491 why) =
    (cache, L4KDecline491 why))`;;

let l4_cache_dispatch_lookup964 = new_recursive_definition option_RECURSION
 `(l4_cache_dispatch_lookup964 fuel env ps g k cache NONE =
    l4_cache_apply_result964 k cache (l4_defeq597 fuel env ps g (l4_dck_lhs964 k) (l4_dck_rhs964 k))) /\
  (l4_cache_dispatch_lookup964 fuel env ps g k cache (SOME verdict) =
    (cache, L4KAccept491 verdict))`;;

let l4_cached_defeq964 = new_definition
 `l4_cached_defeq964 fuel env ps g cache t s =
   l4_cache_dispatch_lookup964 fuel env ps g (l4_key_of_query964 g t s) cache
     (l4_cache_lookup964 cache (l4_key_of_query964 g t s))`;;

let l4_cache_sound_for964 = new_definition
 `l4_cache_sound_for964 fuel env ps cache <=>
   !g t s verdict.
     l4_cache_lookup964 cache (l4_key_of_query964 g t s) = SOME verdict ==>
     l4_defeq597 fuel env ps g t s = L4KAccept491 verdict`;;

let l4_empty_cache_sound964 = prove
 (`!fuel env ps. l4_cache_sound_for964 fuel env ps []`,
  REWRITE_TAC [l4_cache_sound_for964;l4_cache_lookup964;distinctness "option"]);;

let l4_cached_defeq_refines_uncached964 = prove
 (`!fuel env ps g cache t s.
   l4_cache_sound_for964 fuel env ps cache ==>
   SND (l4_cached_defeq964 fuel env ps g cache t s) =
   l4_defeq597 fuel env ps g t s`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_cache_sound_for964;l4_cached_defeq964] THEN
  DISCH_TAC THEN
  STRIP_ASSUME_TAC (ISPEC `l4_cache_lookup964 cache (l4_key_of_query964 g t s)`
    (cases "option")) THENL
  [ASM_REWRITE_TAC [l4_cache_dispatch_lookup964;l4_key_of_query964;
     l4_dck_lhs964;l4_dck_rhs964] THEN
   STRIP_ASSUME_TAC (ISPEC `l4_defeq597 fuel env ps g t s`
     (cases "l4_kresult491")) THEN
   ASM_REWRITE_TAC [l4_cache_apply_result964;SND];
   ASM_REWRITE_TAC [l4_cache_dispatch_lookup964;SND] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`g:l4_kcontext532`;`t:l4_kexpr447`;
                                  `s:l4_kexpr447`;`a:bool`]) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let l4_cached_defeq_preserves_verdict964 = prove
 (`!fuel env ps g cache t s verdict.
   l4_cache_sound_for964 fuel env ps cache ==>
   (SND (l4_cached_defeq964 fuel env ps g cache t s) = L4KAccept491 verdict <=>
    l4_defeq597 fuel env ps g t s = L4KAccept491 verdict)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (SUBST1_TAC o SPECL [`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] o
    MATCH_MP l4_cached_defeq_refines_uncached964) THEN
  REFL_TAC);;
