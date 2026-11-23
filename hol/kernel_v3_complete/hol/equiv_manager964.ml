(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of full-context positive/negative definitional-
   equality memoization and pure-HOL union-find EquivManager
   (Lean4Lean/EquivManager.lean, parity with rocq/DefEqCache.v).
   Every cache key carries the ENTIRE l4_kcontext532 (bound types, bound
   let-values, and free context) so same-depth inequivalent contexts never
   alias (closing bugs/open-term-cache-context). Zero new axioms. *)
needs "hol/kernel_checker597.ml";;

(* ========================================================================= *)
(* 1. Full-Context Positive & Negative DefEq Cache                           *)
(* ========================================================================= *)

let l4_defeq_cache_key_INDUCT964,l4_defeq_cache_key_RECURSION964 = define_type
 "l4_defeq_cache_key964 = L4DefEqKey964 l4_kcontext532 l4_kexpr447 l4_kexpr447";;

let l4_dck_context964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_context964 (L4DefEqKey964 g lhs_e rhs_e) = g`;;
let l4_dck_lhs964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_lhs964 (L4DefEqKey964 g lhs_e rhs_e) = lhs_e`;;
let l4_dck_rhs964 = new_recursive_definition l4_defeq_cache_key_RECURSION964
 `l4_dck_rhs964 (L4DefEqKey964 g lhs_e rhs_e) = rhs_e`;;

let l4_key_of_query964 = new_definition
 `l4_key_of_query964 (g:l4_kcontext532) (t:l4_kexpr447) (s:l4_kexpr447) =
   L4DefEqKey964 g t s`;;

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
    l4_cache_apply_result964 k cache
      (l4_defeq597 fuel env ps g (l4_dck_lhs964 k) (l4_dck_rhs964 k))) /\
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

let l4_cache_insert_sound964 = prove
 (`!fuel env ps cache g t s verdict.
   l4_cache_sound_for964 fuel env ps cache /\
   l4_defeq597 fuel env ps g t s = L4KAccept491 verdict ==>
   l4_cache_sound_for964 fuel env ps
     (l4_cache_insert964 (l4_key_of_query964 g t s) verdict cache)`,
  REWRITE_TAC [l4_cache_sound_for964;l4_cache_insert964;l4_cache_lookup964;
    l4_key_of_query964;FST;SND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`g':l4_kcontext532`;`t':l4_kexpr447`;`s':l4_kexpr447`;`v':bool`] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [injectivity "option"] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [injectivity "l4_defeq_cache_key964"]) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [];
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;

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

let l4_cached_defeq_preserves_sound964 = prove
 (`!fuel env ps g cache t s.
   l4_cache_sound_for964 fuel env ps cache ==>
   l4_cache_sound_for964 fuel env ps
     (FST (l4_cached_defeq964 fuel env ps g cache t s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC [l4_cached_defeq964] THEN
  STRIP_ASSUME_TAC (ISPEC `l4_cache_lookup964 cache (l4_key_of_query964 g t s)`
    (cases "option")) THENL
  [ASM_REWRITE_TAC [l4_cache_dispatch_lookup964;l4_key_of_query964;
     l4_dck_lhs964;l4_dck_rhs964] THEN
   DISJ_CASES_THEN2
     (X_CHOOSE_THEN `v:bool` ASSUME_TAC)
     (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `err:l4_kreject491` ASSUME_TAC)
       (X_CHOOSE_THEN `why:l4_kdecline491` ASSUME_TAC))
     (ISPEC `l4_defeq597 fuel env ps g t s` (cases "l4_kresult491")) THEN
   ASM_REWRITE_TAC [l4_cache_apply_result964;FST] THEN
   MATCH_MP_TAC (REWRITE_RULE [l4_key_of_query964] l4_cache_insert_sound964) THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [l4_cache_dispatch_lookup964;FST]]);;

let l4_cached_defeq_preserves_verdict964 = prove
 (`!fuel env ps g cache t s verdict.
   l4_cache_sound_for964 fuel env ps cache ==>
   (SND (l4_cached_defeq964 fuel env ps g cache t s) = L4KAccept491 verdict <=>
    l4_defeq597 fuel env ps g t s = L4KAccept491 verdict)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (SUBST1_TAC o SPECL [`g:l4_kcontext532`;`t:l4_kexpr447`;`s:l4_kexpr447`] o
    MATCH_MP l4_cached_defeq_refines_uncached964) THEN
  REFL_TAC);;

(* Same-depth distinct contexts never alias (closes bugs/open-term-cache-context). *)
let l4_same_depth_distinct_types_never_alias964 = prove
 (`let g1 = l4_kpush_binding532 l4_kempty_context532 (L4KSort447 L4KZero447) NONE in
   let g2 = l4_kpush_binding532 l4_kempty_context532 (L4KSort447 (L4KSucc447 L4KZero447)) NONE in
   LENGTH (l4_kcontext_bound532 g1) = LENGTH (l4_kcontext_bound532 g2) /\
   ~(l4_key_of_query964 g1 (L4KBVar447 0) (L4KBVar447 0) =
     l4_key_of_query964 g2 (L4KBVar447 0) (L4KBVar447 0))`,
  REWRITE_TAC [LET_DEF;LET_END_DEF;l4_kpush_binding532;l4_kempty_context532;
    l4_kcontext_bound532;l4_key_of_query964;LENGTH;
    injectivity "l4_defeq_cache_key964";injectivity "l4_kcontext532";
    CONS_11;injectivity "l4_kbinding491";injectivity "l4_kexpr447";
    distinctness "l4_klevel447"]);;

let l4_same_depth_distinct_let_values_never_alias964 = prove
 (`let g1 = l4_kpush_binding532 l4_kempty_context532 (L4KSort447 L4KZero447) (SOME (L4KNatLit447 0)) in
   let g2 = l4_kpush_binding532 l4_kempty_context532 (L4KSort447 L4KZero447) (SOME (L4KNatLit447 1)) in
   LENGTH (l4_kcontext_bound532 g1) = LENGTH (l4_kcontext_bound532 g2) /\
   ~(l4_key_of_query964 g1 (L4KBVar447 0) (L4KBVar447 0) =
     l4_key_of_query964 g2 (L4KBVar447 0) (L4KBVar447 0))`,
  REWRITE_TAC [LET_DEF;LET_END_DEF;l4_kpush_binding532;l4_kempty_context532;
    l4_kcontext_bound532;l4_key_of_query964;LENGTH;
    injectivity "l4_defeq_cache_key964";injectivity "l4_kcontext532";
    CONS_11;injectivity "l4_kbinding491";injectivity "option";
    injectivity "l4_kexpr447"] THEN ARITH_TAC);;

(* ========================================================================= *)
(* 2. Pure-HOL Union-Find EquivManager (Lean4Lean/EquivManager.lean)         *)
(* ========================================================================= *)

let l4_equiv_manager_INDUCT964,l4_equiv_manager_RECURSION964 = define_type
 "l4_equiv_manager964 = L4EquivManager964 ((num # num) list) num (((l4_kcontext532 # l4_kexpr447) # num) list)";;

let l4_em_parent964 = new_recursive_definition l4_equiv_manager_RECURSION964
 `l4_em_parent964 (L4EquivManager964 parent next nodes) = parent`;;
let l4_em_next964 = new_recursive_definition l4_equiv_manager_RECURSION964
 `l4_em_next964 (L4EquivManager964 parent next nodes) = next`;;
let l4_em_nodes964 = new_recursive_definition l4_equiv_manager_RECURSION964
 `l4_em_nodes964 (L4EquivManager964 parent next nodes) = nodes`;;

let l4_em_empty964 = new_definition
 `l4_em_empty964 = L4EquivManager964 [] 0 []`;;

let l4_em_assoc_num964 = new_recursive_definition list_RECURSION
 `(l4_em_assoc_num964 [] (k:num) = NONE) /\
  (l4_em_assoc_num964 (CONS (entry : num # num) rest) k =
    if FST entry = k then SOME (SND entry)
    else l4_em_assoc_num964 rest k)`;;

let l4_em_assoc_node964 = new_recursive_definition list_RECURSION
 `(l4_em_assoc_node964 [] (k : l4_kcontext532 # l4_kexpr447) = NONE) /\
  (l4_em_assoc_node964 (CONS (entry : (l4_kcontext532 # l4_kexpr447) # num) rest) k =
    if FST entry = k then SOME (SND entry)
    else l4_em_assoc_node964 rest k)`;;

let l4_em_root_aux964 = new_recursive_definition num_RECURSION
 `(l4_em_root_aux964 0 parent n = n) /\
  (l4_em_root_aux964 (SUC fuel) parent n =
    match l4_em_assoc_num964 parent n with
    | NONE -> n
    | SOME p -> if p = n then n else l4_em_root_aux964 fuel parent p)`;;

let l4_em_root964 = new_definition
 `l4_em_root964 m n = l4_em_root_aux964 64 (l4_em_parent964 m) n`;;

let l4_em_to_node964 = new_definition
 `l4_em_to_node964 m g e =
   match l4_em_assoc_node964 (l4_em_nodes964 m) (g,e) with
   | SOME id -> (id, m)
   | NONE ->
       let id = l4_em_next964 m in
       (id, L4EquivManager964 (l4_em_parent964 m) (SUC id)
              (CONS ((g,e),id) (l4_em_nodes964 m)))`;;

let l4_em_merge964 = new_definition
 `l4_em_merge964 m n1 n2 =
   let r1 = l4_em_root964 m n1 in
   let r2 = l4_em_root964 m n2 in
   if r1 = r2 then m
   else L4EquivManager964 (CONS (r1,r2) (l4_em_parent964 m))
          (l4_em_next964 m) (l4_em_nodes964 m)`;;

let l4_em_add_equiv964 = new_definition
 `l4_em_add_equiv964 m g e1 e2 =
   let p1 = l4_em_to_node964 m g e1 in
   let p2 = l4_em_to_node964 (SND p1) g e2 in
   l4_em_merge964 (SND p2) (FST p1) (FST p2)`;;

let l4_em_eq_opt964 = define
 `(l4_em_eq_opt964 m (SOME n1) (SOME n2) <=> l4_em_root964 m n1 = l4_em_root964 m n2) /\
  (l4_em_eq_opt964 m (SOME n1) NONE <=> F) /\
  (l4_em_eq_opt964 m NONE (SOME n2) <=> F) /\
  (l4_em_eq_opt964 m NONE NONE <=> F)`;;

let l4_em_is_equiv_ro964 = new_definition
 `l4_em_is_equiv_ro964 m g e1 e2 <=>
   if l4_core_alpha_eq538 e1 e2 then T
   else
     l4_em_eq_opt964 m
       (l4_em_assoc_node964 (l4_em_nodes964 m) (g,e1))
       (l4_em_assoc_node964 (l4_em_nodes964 m) (g,e2))`;;

let l4_em_sound_for964 = new_definition
 `l4_em_sound_for964 (R : l4_kcontext532 -> l4_kexpr447 -> l4_kexpr447 -> bool) m <=>
   ?interp : num -> l4_kcontext532 -> l4_kexpr447 -> bool.
     (!g e id. l4_em_assoc_node964 (l4_em_nodes964 m) (g,e) = SOME id ==> interp id g e) /\
     (!id1 id2 g e1 e2.
       interp id1 g e1 /\ interp id2 g e2 /\
       l4_em_root964 m id1 = l4_em_root964 m id2 ==> R g e1 e2)`;;

let l4_em_empty_sound964 = prove
 (`!R. l4_em_sound_for964 R l4_em_empty964`,
  GEN_TAC THEN REWRITE_TAC [l4_em_sound_for964;l4_em_empty964;l4_em_nodes964;
    l4_em_assoc_node964;distinctness "option"] THEN
  EXISTS_TAC `(\id g e. F) : num -> l4_kcontext532 -> l4_kexpr447 -> bool` THEN
  REWRITE_TAC []);;

let l4_em_is_equiv_ro_sound964 = prove
 (`!R m g e1 e2.
   (!g a b. l4_core_alpha_eq538 a b ==> R g a b) /\
   l4_em_sound_for964 R m /\
   l4_em_is_equiv_ro964 m g e1 e2 ==>
   R g e1 e2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [l4_em_sound_for964;l4_em_is_equiv_ro964] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "h_alpha")
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `interp:num->l4_kcontext532->l4_kexpr447->bool`
        (CONJUNCTS_THEN2 (LABEL_TAC "h_assoc") (LABEL_TAC "h_root")))
      MP_TAC)) THEN
  ASM_CASES_TAC `l4_core_alpha_eq538 e1 e2` THENL
  [DISCH_THEN (K ALL_TAC) THEN USE_THEN "h_alpha" MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n1:num` ASSUME_TAC)
     (ISPEC `l4_em_assoc_node964 (l4_em_nodes964 m) (g,e1)` (cases "option")) THEN
   DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n2:num` ASSUME_TAC)
     (ISPEC `l4_em_assoc_node964 (l4_em_nodes964 m) (g,e2)` (cases "option")) THEN
   ASM_REWRITE_TAC [l4_em_eq_opt964] THEN
   DISCH_TAC THEN
   USE_THEN "h_root" MATCH_MP_TAC THEN
   EXISTS_TAC `n1:num` THEN EXISTS_TAC `n2:num` THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC THEN USE_THEN "h_assoc" MATCH_MP_TAC THEN ASM_REWRITE_TAC []]);;
