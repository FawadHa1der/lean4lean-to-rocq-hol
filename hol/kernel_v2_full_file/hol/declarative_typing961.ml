(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HOL Light formalization of Lean4Lean/Theory/{VLevel,VExpr,VDecl,VEnv}.lean
   and Lean4Lean/Theory/Typing/{Basic,Lemmas,Env,ChurchRosser,Injectivity}.lean:
   semantic universe levels, de Bruijn expressions, monotonic VEnv, 13-rule
   declarative VIsDefEq / VHasType, parallel reduction, multi-step confluence
   inversions, environment monotonicity, and head disjointness / Pi-injectivity.
   Zero new axioms. *)
needs "hol/ordinary_admission607.ml";;

(* 1. Semantic Universe Levels *)
let l4_vlevel_INDUCT961,l4_vlevel_RECURSION961 = define_type
 "l4_vlevel961 = L4VLZero961
               | L4VLSucc961 l4_vlevel961
               | L4VLMax961 l4_vlevel961 l4_vlevel961
               | L4VLIMax961 l4_vlevel961 l4_vlevel961
               | L4VLParam961 num";;

let l4_vlevel_imax_nat961 = new_definition
 `l4_vlevel_imax_nat961 (a:num) (b:num) =
   if b = 0 then 0 else MAX a b`;;

let l4_vnth_nat961 = new_recursive_definition list_RECURSION
 `(l4_vnth_nat961 [] (i:num) = 0) /\
  (l4_vnth_nat961 (CONS (x:num) xs) i =
    if i = 0 then x else l4_vnth_nat961 xs (i - 1))`;;

let l4_vlevel_eval961 = new_recursive_definition l4_vlevel_RECURSION961
 `(l4_vlevel_eval961 ls L4VLZero961 = 0) /\
  (l4_vlevel_eval961 ls (L4VLSucc961 v) = SUC (l4_vlevel_eval961 ls v)) /\
  (l4_vlevel_eval961 ls (L4VLMax961 a b) =
    MAX (l4_vlevel_eval961 ls a) (l4_vlevel_eval961 ls b)) /\
  (l4_vlevel_eval961 ls (L4VLIMax961 a b) =
    l4_vlevel_imax_nat961 (l4_vlevel_eval961 ls a) (l4_vlevel_eval961 ls b)) /\
  (l4_vlevel_eval961 ls (L4VLParam961 i) = l4_vnth_nat961 ls i)`;;

let l4_vlevel_wf961 = new_recursive_definition l4_vlevel_RECURSION961
 `(l4_vlevel_wf961 uvars L4VLZero961 <=> T) /\
  (l4_vlevel_wf961 uvars (L4VLSucc961 v) <=> l4_vlevel_wf961 uvars v) /\
  (l4_vlevel_wf961 uvars (L4VLMax961 a b) <=>
    l4_vlevel_wf961 uvars a /\ l4_vlevel_wf961 uvars b) /\
  (l4_vlevel_wf961 uvars (L4VLIMax961 a b) <=>
    l4_vlevel_wf961 uvars a /\ l4_vlevel_wf961 uvars b) /\
  (l4_vlevel_wf961 uvars (L4VLParam961 i) <=> i < uvars)`;;

let l4_vlevel_le961 = new_definition
 `l4_vlevel_le961 u v <=> !ls. l4_vlevel_eval961 ls u <= l4_vlevel_eval961 ls v`;;

let l4_vlevel_equiv961 = new_definition
 `l4_vlevel_equiv961 u v <=> !ls. l4_vlevel_eval961 ls u = l4_vlevel_eval961 ls v`;;

let l4_vnth_level961 = new_recursive_definition list_RECURSION
 `(l4_vnth_level961 [] (i:num) = L4VLZero961) /\
  (l4_vnth_level961 (CONS (u:l4_vlevel961) us) i =
    if i = 0 then u else l4_vnth_level961 us (i - 1))`;;

let l4_vlevel_inst961 = new_recursive_definition l4_vlevel_RECURSION961
 `(l4_vlevel_inst961 ks L4VLZero961 = L4VLZero961) /\
  (l4_vlevel_inst961 ks (L4VLSucc961 v) = L4VLSucc961 (l4_vlevel_inst961 ks v)) /\
  (l4_vlevel_inst961 ks (L4VLMax961 a b) =
    L4VLMax961 (l4_vlevel_inst961 ks a) (l4_vlevel_inst961 ks b)) /\
  (l4_vlevel_inst961 ks (L4VLIMax961 a b) =
    L4VLIMax961 (l4_vlevel_inst961 ks a) (l4_vlevel_inst961 ks b)) /\
  (l4_vlevel_inst961 ks (L4VLParam961 i) = l4_vnth_level961 ks i)`;;

let l4_vlevel_equiv_refl961 = prove
 (`!u. l4_vlevel_equiv961 u u`,
  REWRITE_TAC [l4_vlevel_equiv961]);;

let l4_vlevel_equiv_symm961 = prove
 (`!u v. l4_vlevel_equiv961 u v ==> l4_vlevel_equiv961 v u`,
  REWRITE_TAC [l4_vlevel_equiv961] THEN MESON_TAC []);;

let l4_vlevel_equiv_trans961 = prove
 (`!u v w. l4_vlevel_equiv961 u v /\ l4_vlevel_equiv961 v w ==> l4_vlevel_equiv961 u w`,
  REWRITE_TAC [l4_vlevel_equiv961] THEN MESON_TAC []);;

(* 2. Core Semantic Expressions (Lean4Lean/Theory/VExpr.lean) *)
let l4_vexpr_INDUCT961,l4_vexpr_RECURSION961 = define_type
 "l4_vexpr961 = L4VBVar961 num
              | L4VSort961 l4_vlevel961
              | L4VConst961 l4_name (l4_vlevel961 list)
              | L4VApp961 l4_vexpr961 l4_vexpr961
              | L4VLam961 l4_vexpr961 l4_vexpr961
              | L4VForallE961 l4_vexpr961 l4_vexpr961";;

let l4_vlift_var961 = new_definition
 `l4_vlift_var961 (n:num) (i:num) (k:num) = if i < k then i else n + i`;;

let l4_vliftN961 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vliftN961 (L4VBVar961 i) n k = L4VBVar961 (l4_vlift_var961 n i k)) /\
  (l4_vliftN961 (L4VSort961 u) n k = L4VSort961 u) /\
  (l4_vliftN961 (L4VConst961 c us) n k = L4VConst961 c us) /\
  (l4_vliftN961 (L4VApp961 f a) n k =
    L4VApp961 (l4_vliftN961 f n k) (l4_vliftN961 a n k)) /\
  (l4_vliftN961 (L4VLam961 dom body) n k =
    L4VLam961 (l4_vliftN961 dom n k) (l4_vliftN961 body n (SUC k))) /\
  (l4_vliftN961 (L4VForallE961 dom cod) n k =
    L4VForallE961 (l4_vliftN961 dom n k) (l4_vliftN961 cod n (SUC k)))`;;

let l4_vlift961 = new_definition
 `l4_vlift961 e = l4_vliftN961 e 1 0`;;

let l4_vinst_var961 = new_definition
 `l4_vinst_var961 (i:num) (v:l4_vexpr961) (k:num) =
   if i < k then L4VBVar961 i
   else if i = k then l4_vliftN961 v k 0
   else L4VBVar961 (i - 1)`;;

let l4_vinst961 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vinst961 (L4VBVar961 i) v k = l4_vinst_var961 i v k) /\
  (l4_vinst961 (L4VSort961 u) v k = L4VSort961 u) /\
  (l4_vinst961 (L4VConst961 c us) v k = L4VConst961 c us) /\
  (l4_vinst961 (L4VApp961 f a) v k =
    L4VApp961 (l4_vinst961 f v k) (l4_vinst961 a v k)) /\
  (l4_vinst961 (L4VLam961 dom body) v k =
    L4VLam961 (l4_vinst961 dom v k) (l4_vinst961 body v (SUC k))) /\
  (l4_vinst961 (L4VForallE961 dom cod) v k =
    L4VForallE961 (l4_vinst961 dom v k) (l4_vinst961 cod v (SUC k)))`;;

let l4_vinst0961 = new_definition
 `l4_vinst0961 e v = l4_vinst961 e v 0`;;

let l4_vinstL961 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vinstL961 ks (L4VBVar961 i) = L4VBVar961 i) /\
  (l4_vinstL961 ks (L4VSort961 u) = L4VSort961 (l4_vlevel_inst961 ks u)) /\
  (l4_vinstL961 ks (L4VConst961 c us) =
    L4VConst961 c (MAP (l4_vlevel_inst961 ks) us)) /\
  (l4_vinstL961 ks (L4VApp961 f a) =
    L4VApp961 (l4_vinstL961 ks f) (l4_vinstL961 ks a)) /\
  (l4_vinstL961 ks (L4VLam961 dom body) =
    L4VLam961 (l4_vinstL961 ks dom) (l4_vinstL961 ks body)) /\
  (l4_vinstL961 ks (L4VForallE961 dom cod) =
    L4VForallE961 (l4_vinstL961 ks dom) (l4_vinstL961 ks cod))`;;

let l4_vclosedN961 = new_recursive_definition l4_vexpr_RECURSION961
 `(l4_vclosedN961 (L4VBVar961 i) k <=> i < k) /\
  (l4_vclosedN961 (L4VSort961 u) k <=> T) /\
  (l4_vclosedN961 (L4VConst961 c us) k <=> T) /\
  (l4_vclosedN961 (L4VApp961 f a) k <=> l4_vclosedN961 f k /\ l4_vclosedN961 a k) /\
  (l4_vclosedN961 (L4VLam961 dom body) k <=>
    l4_vclosedN961 dom k /\ l4_vclosedN961 body (SUC k)) /\
  (l4_vclosedN961 (L4VForallE961 dom cod) k <=>
    l4_vclosedN961 dom k /\ l4_vclosedN961 cod (SUC k))`;;

let l4_vlift_var_zero961 = prove
 (`!i k. l4_vlift_var961 0 i k = i`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vlift_var961;ADD_CLAUSES] THEN
  COND_CASES_TAC THEN REFL_TAC);;

let l4_vliftN_zero961 = prove
 (`!e k. l4_vliftN961 e 0 k = e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REWRITE_TAC [l4_vliftN961;l4_vlift_var_zero961] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(* 3. Semantic Environments (Lean4Lean/Theory/VEnv.lean) *)
let l4_vconstant_INDUCT961,l4_vconstant_RECURSION961 = define_type
 "l4_vconstant961 = L4VConstant961 num l4_vexpr961";;

let l4_vc_uvars961 = new_recursive_definition l4_vconstant_RECURSION961
 `l4_vc_uvars961 (L4VConstant961 uvars ty) = uvars`;;

let l4_vc_type961 = new_recursive_definition l4_vconstant_RECURSION961
 `l4_vc_type961 (L4VConstant961 uvars ty) = ty`;;

let l4_vdefeq_INDUCT961,l4_vdefeq_RECURSION961 = define_type
 "l4_vdefeq961 = L4VDefEq961 num l4_vexpr961 l4_vexpr961 l4_vexpr961";;

let l4_vdf_uvars961 = new_recursive_definition l4_vdefeq_RECURSION961
 `l4_vdf_uvars961 (L4VDefEq961 uvars lhs_e rhs_e ty) = uvars`;;
let l4_vdf_lhs961 = new_recursive_definition l4_vdefeq_RECURSION961
 `l4_vdf_lhs961 (L4VDefEq961 uvars lhs_e rhs_e ty) = lhs_e`;;
let l4_vdf_rhs961 = new_recursive_definition l4_vdefeq_RECURSION961
 `l4_vdf_rhs961 (L4VDefEq961 uvars lhs_e rhs_e ty) = rhs_e`;;
let l4_vdf_type961 = new_recursive_definition l4_vdefeq_RECURSION961
 `l4_vdf_type961 (L4VDefEq961 uvars lhs_e rhs_e ty) = ty`;;

let l4_venv_INDUCT961,l4_venv_RECURSION961 = define_type
 "l4_venv961 = L4VEnv961 ((l4_name # l4_vconstant961) list) (l4_vdefeq961 list)";;

let l4_venv_consts_list961 = new_recursive_definition l4_venv_RECURSION961
 `l4_venv_consts_list961 (L4VEnv961 cs dfs) = cs`;;
let l4_venv_defeqs_list961 = new_recursive_definition l4_venv_RECURSION961
 `l4_venv_defeqs_list961 (L4VEnv961 cs dfs) = dfs`;;

let l4_venv_lookup_const961 = new_definition
 `l4_venv_lookup_const961 env c cinfo <=>
   MEM (c,cinfo) (l4_venv_consts_list961 env)`;;

let l4_venv_has_defeq961 = new_definition
 `l4_venv_has_defeq961 env df <=>
   MEM df (l4_venv_defeqs_list961 env)`;;

let l4_venv_ordered961 = new_definition
 `l4_venv_ordered961 env1 env2 <=>
   (!c cinfo. l4_venv_lookup_const961 env1 c cinfo ==> l4_venv_lookup_const961 env2 c cinfo) /\
   (!df. l4_venv_has_defeq961 env1 df ==> l4_venv_has_defeq961 env2 df)`;;

let l4_venv_ordered_refl961 = prove
 (`!env. l4_venv_ordered961 env env`,
  REWRITE_TAC [l4_venv_ordered961]);;

let l4_venv_ordered_trans961 = prove
 (`!env1 env2 env3.
   l4_venv_ordered961 env1 env2 /\ l4_venv_ordered961 env2 env3 ==>
   l4_venv_ordered961 env1 env3`,
  REWRITE_TAC [l4_venv_ordered961] THEN MESON_TAC []);;

(* 4. Context Lookup & 13-Rule Declarative Typing (Lean4Lean/Theory/Typing/Basic.lean) *)
let l4_vlookup_RULES961,l4_vlookup_INDUCT961,l4_vlookup_CASES961 =
  new_inductive_definition
 `(!a g. l4_vlookup961 (CONS a g) 0 (l4_vlift961 a)) /\
  (!a g i b. l4_vlookup961 g i b ==>
    l4_vlookup961 (CONS a g) (SUC i) (l4_vlift961 b))`;;

let l4_vis_defeq_RULES961,l4_vis_defeq_INDUCT961,l4_vis_defeq_CASES961 =
  new_inductive_definition
 `(!env uvars g i ty.
     l4_vlookup961 g i ty ==>
     l4_vis_defeq961 env uvars g (L4VBVar961 i) (L4VBVar961 i) ty) /\
  (!env uvars g e1 e2 ty.
     l4_vis_defeq961 env uvars g e1 e2 ty ==>
     l4_vis_defeq961 env uvars g e2 e1 ty) /\
  (!env uvars g e1 e2 e3 ty.
     l4_vis_defeq961 env uvars g e1 e2 ty /\
     l4_vis_defeq961 env uvars g e2 e3 ty ==>
     l4_vis_defeq961 env uvars g e1 e3 ty) /\
  (!env uvars g l1 l2.
     l4_vlevel_wf961 uvars l1 /\ l4_vlevel_wf961 uvars l2 /\
     l4_vlevel_equiv961 l1 l2 ==>
     l4_vis_defeq961 env uvars g (L4VSort961 l1) (L4VSort961 l2)
       (L4VSort961 (L4VLSucc961 l1))) /\
  (!env uvars g c cinfo ls1 ls2.
     l4_venv_lookup_const961 env c cinfo /\
     ALL (l4_vlevel_wf961 uvars) ls1 /\
     ALL (l4_vlevel_wf961 uvars) ls2 /\
     LENGTH ls1 = l4_vc_uvars961 cinfo /\
     ALL2 l4_vlevel_equiv961 ls1 ls2 ==>
     l4_vis_defeq961 env uvars g (L4VConst961 c ls1) (L4VConst961 c ls2)
       (l4_vinstL961 ls1 (l4_vc_type961 cinfo))) /\
  (!env uvars g f1 f2 a1 a2 dom cod.
     l4_vis_defeq961 env uvars g f1 f2 (L4VForallE961 dom cod) /\
     l4_vis_defeq961 env uvars g a1 a2 dom ==>
     l4_vis_defeq961 env uvars g (L4VApp961 f1 a1) (L4VApp961 f2 a2)
       (l4_vinst0961 cod a1)) /\
  (!env uvars g dom1 dom2 b1 b2 u cod.
     l4_vis_defeq961 env uvars g dom1 dom2 (L4VSort961 u) /\
     l4_vis_defeq961 env uvars (CONS dom1 g) b1 b2 cod ==>
     l4_vis_defeq961 env uvars g (L4VLam961 dom1 b1) (L4VLam961 dom2 b2)
       (L4VForallE961 dom1 cod)) /\
  (!env uvars g dom1 dom2 cod1 cod2 u v.
     l4_vis_defeq961 env uvars g dom1 dom2 (L4VSort961 u) /\
     l4_vis_defeq961 env uvars (CONS dom1 g) cod1 cod2 (L4VSort961 v) ==>
     l4_vis_defeq961 env uvars g (L4VForallE961 dom1 cod1) (L4VForallE961 dom2 cod2)
       (L4VSort961 (L4VLIMax961 u v))) /\
  (!env uvars g e1 e2 ty1 ty2 u.
     l4_vis_defeq961 env uvars g ty1 ty2 (L4VSort961 u) /\
     l4_vis_defeq961 env uvars g e1 e2 ty1 ==>
     l4_vis_defeq961 env uvars g e1 e2 ty2) /\
  (!env uvars g dom body arg cod.
     l4_vis_defeq961 env uvars (CONS dom g) body body cod /\
     l4_vis_defeq961 env uvars g arg arg dom ==>
     l4_vis_defeq961 env uvars g (L4VApp961 (L4VLam961 dom body) arg)
       (l4_vinst0961 body arg) (l4_vinst0961 cod arg)) /\
  (!env uvars g e dom cod.
     l4_vis_defeq961 env uvars g e e (L4VForallE961 dom cod) ==>
     l4_vis_defeq961 env uvars g
       (L4VLam961 dom (L4VApp961 (l4_vlift961 e) (L4VBVar961 0))) e
       (L4VForallE961 dom cod)) /\
  (!env uvars g p h1 h2.
     l4_vis_defeq961 env uvars g p p (L4VSort961 L4VLZero961) /\
     l4_vis_defeq961 env uvars g h1 h1 p /\
     l4_vis_defeq961 env uvars g h2 h2 p ==>
     l4_vis_defeq961 env uvars g h1 h2 p) /\
  (!env uvars g df ls.
     l4_venv_has_defeq961 env df /\
     ALL (l4_vlevel_wf961 uvars) ls /\
     LENGTH ls = l4_vdf_uvars961 df ==>
     l4_vis_defeq961 env uvars g
       (l4_vinstL961 ls (l4_vdf_lhs961 df))
       (l4_vinstL961 ls (l4_vdf_rhs961 df))
       (l4_vinstL961 ls (l4_vdf_type961 df)))`;;

let [l4_vis_defeq_bvar961;
     l4_vis_defeq_symm961;
     l4_vis_defeq_trans961;
     l4_vis_defeq_sort961;
     l4_vis_defeq_const961;
     l4_vis_defeq_app961;
     l4_vis_defeq_lam961;
     l4_vis_defeq_forall961;
     l4_vis_defeq_conv961;
     l4_vis_defeq_beta961;
     l4_vis_defeq_eta961;
     l4_vis_defeq_proof_irrel961;
     l4_vis_defeq_extra961] = CONJUNCTS l4_vis_defeq_RULES961;;

let l4_vhas_type961 = new_definition
 `l4_vhas_type961 env uvars g e ty <=> l4_vis_defeq961 env uvars g e e ty`;;

let l4_vis_type961 = new_definition
 `l4_vis_type961 env uvars g ty <=> ?u. l4_vhas_type961 env uvars g ty (L4VSort961 u)`;;

let l4_vis_defeq_u961 = new_definition
 `l4_vis_defeq_u961 env uvars g e1 e2 <=> ?ty. l4_vis_defeq961 env uvars g e1 e2 ty`;;

let l4_vis_defeq_refl_l961 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==> l4_vhas_type961 env uvars g e1 ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_symm961;l4_vis_defeq_trans961]);;

let l4_vis_defeq_refl_r961 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==> l4_vhas_type961 env uvars g e2 ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_vis_defeq_symm961;l4_vis_defeq_trans961]);;

let l4_vis_defeq_has_type_both961 = prove
 (`!env uvars g e1 e2 ty.
   l4_vis_defeq961 env uvars g e1 e2 ty ==>
   l4_vhas_type961 env uvars g e1 ty /\ l4_vhas_type961 env uvars g e2 ty`,
  MESON_TAC [l4_vis_defeq_refl_l961;l4_vis_defeq_refl_r961]);;

let l4_venv_ordered_preserve_vis_defeq961 = prove
 (`!env1 uvars g e1 e2 ty.
   l4_vis_defeq961 env1 uvars g e1 e2 ty ==>
   (!env2. l4_venv_ordered961 env1 env2 ==>
           l4_vis_defeq961 env2 uvars g e1 e2 ty)`,
  MATCH_MP_TAC l4_vis_defeq_INDUCT961 THEN
  REPEAT CONJ_TAC THENL
  [MESON_TAC [l4_vis_defeq_bvar961];
   MESON_TAC [l4_vis_defeq_symm961];
   MESON_TAC [l4_vis_defeq_trans961];
   MESON_TAC [l4_vis_defeq_sort961];
   MESON_TAC [l4_venv_ordered961;l4_vis_defeq_const961];
   MESON_TAC [l4_vis_defeq_app961];
   MESON_TAC [l4_vis_defeq_lam961];
   MESON_TAC [l4_vis_defeq_forall961];
   MESON_TAC [l4_vis_defeq_conv961];
   MESON_TAC [l4_vis_defeq_beta961];
   MESON_TAC [l4_vis_defeq_eta961];
   MESON_TAC [l4_vis_defeq_proof_irrel961];
   MESON_TAC [l4_venv_ordered961;l4_vis_defeq_extra961]]);;

let l4_venv_ordered_preserve_vhas_type961 = prove
 (`!env1 env2 uvars g e ty.
   l4_venv_ordered961 env1 env2 /\
   l4_vhas_type961 env1 uvars g e ty ==>
   l4_vhas_type961 env2 uvars g e ty`,
  REWRITE_TAC [l4_vhas_type961] THEN
  MESON_TAC [l4_venv_ordered_preserve_vis_defeq961]);;

(* 5. Parallel Reduction & Confluence / Injectivity Foundations *)
let l4_vpar_red_RULES961,l4_vpar_red_INDUCT961,l4_vpar_red_CASES961 =
  new_inductive_definition
 `(!i. l4_vpar_red961 (L4VBVar961 i) (L4VBVar961 i)) /\
  (!u. l4_vpar_red961 (L4VSort961 u) (L4VSort961 u)) /\
  (!c ls. l4_vpar_red961 (L4VConst961 c ls) (L4VConst961 c ls)) /\
  (!f f' a a'. l4_vpar_red961 f f' /\ l4_vpar_red961 a a' ==>
    l4_vpar_red961 (L4VApp961 f a) (L4VApp961 f' a')) /\
  (!dom dom' body body'. l4_vpar_red961 dom dom' /\ l4_vpar_red961 body body' ==>
    l4_vpar_red961 (L4VLam961 dom body) (L4VLam961 dom' body')) /\
  (!dom dom' cod cod'. l4_vpar_red961 dom dom' /\ l4_vpar_red961 cod cod' ==>
    l4_vpar_red961 (L4VForallE961 dom cod) (L4VForallE961 dom' cod')) /\
  (!dom body body' arg arg'. l4_vpar_red961 body body' /\ l4_vpar_red961 arg arg' ==>
    l4_vpar_red961 (L4VApp961 (L4VLam961 dom body) arg) (l4_vinst0961 body' arg'))`;;

let l4_vpar_red_refl961 = prove
 (`!e. l4_vpar_red961 e e`,
  MATCH_MP_TAC l4_vexpr_INDUCT961 THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [l4_vpar_red_RULES961]);;

let l4_vpar_red_sort_inv961 = prove
 (`!u e. l4_vpar_red961 (L4VSort961 u) e <=> e = L4VSort961 u`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_CASES961] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vpar_red_forall_inv961 = prove
 (`!dom cod e. l4_vpar_red961 (L4VForallE961 dom cod) e <=>
   ?dom' cod'. e = L4VForallE961 dom' cod' /\
               l4_vpar_red961 dom dom' /\ l4_vpar_red961 cod cod'`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [l4_vpar_red_CASES961] THEN
  REWRITE_TAC [distinctness "l4_vexpr961";injectivity "l4_vexpr961"] THEN
  MESON_TAC []);;

let l4_vpar_red_sort_forall_disjoint961 = prove
 (`!u dom cod c.
   ~(l4_vpar_red961 (L4VSort961 u) c /\ l4_vpar_red961 (L4VForallE961 dom cod) c)`,
  REWRITE_TAC [l4_vpar_red_sort_inv961;l4_vpar_red_forall_inv961;
    distinctness "l4_vexpr961"] THEN
  MESON_TAC [distinctness "l4_vexpr961"]);;

let l4_vpar_red_forall_injective961 = prove
 (`!dom1 cod1 dom2 cod2 c.
   l4_vpar_red961 (L4VForallE961 dom1 cod1) c /\
   l4_vpar_red961 (L4VForallE961 dom2 cod2) c ==>
   (?dom0. l4_vpar_red961 dom1 dom0 /\ l4_vpar_red961 dom2 dom0) /\
   (?cod0. l4_vpar_red961 cod1 cod0 /\ l4_vpar_red961 cod2 cod0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [l4_vpar_red_forall_inv961] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [injectivity "l4_vexpr961"]) THEN
  ASM_MESON_TAC []);;

(* 6. Multi-Step Parallel Reduction & Head Disjointness / Pi-Injectivity *)
let l4_vpar_red_star_RULES961,l4_vpar_red_star_INDUCT961,l4_vpar_red_star_CASES961 =
  new_inductive_definition
 `(!e. l4_vpar_red_star961 e e) /\
  (!a b c. l4_vpar_red961 a b /\ l4_vpar_red_star961 b c ==>
    l4_vpar_red_star961 a c)`;;

let l4_vpar_red_star_refl961 = prove
 (`!e. l4_vpar_red_star961 e e`,
  REWRITE_TAC [l4_vpar_red_star_RULES961]);;

let l4_vpar_red_star_single961 = prove
 (`!a b. l4_vpar_red961 a b ==> l4_vpar_red_star961 a b`,
  MESON_TAC [l4_vpar_red_star_RULES961]);;

let l4_vpar_red_star_trans961 = prove
 (`!a b. l4_vpar_red_star961 a b ==>
   (!c. l4_vpar_red_star961 b c ==> l4_vpar_red_star961 a c)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN
  MESON_TAC [l4_vpar_red_star_RULES961]);;

let l4_vpar_red_star_sort_inv_aux961 = prove
 (`!a b. l4_vpar_red_star961 a b ==>
   (!u. a = L4VSort961 u ==> b = L4VSort961 u)`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN
  CONJ_TAC THENL
  [MESON_TAC [];
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC (REWRITE_RULE [l4_vpar_red_sort_inv961]) THEN
   ASM_MESON_TAC []]);;

let l4_vpar_red_star_sort_inv961 = prove
 (`!u b. l4_vpar_red_star961 (L4VSort961 u) b <=> b = L4VSort961 u`,
  MESON_TAC [l4_vpar_red_star_sort_inv_aux961;l4_vpar_red_star_refl961]);;

let l4_vpar_red_star_forall_inv_aux961 = prove
 (`!a b. l4_vpar_red_star961 a b ==>
   (!dom cod. a = L4VForallE961 dom cod ==>
     ?dom' cod'. b = L4VForallE961 dom' cod' /\
                 l4_vpar_red_star961 dom dom' /\
                 l4_vpar_red_star961 cod cod')`,
  MATCH_MP_TAC l4_vpar_red_star_INDUCT961 THEN
  CONJ_TAC THENL
  [MESON_TAC [l4_vpar_red_star_refl961];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   UNDISCH_TAC `l4_vpar_red961 (L4VForallE961 dom cod) b` THEN
   REWRITE_TAC [l4_vpar_red_forall_inv961] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`dom':l4_vexpr961`;`cod':l4_vexpr961`]) THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`dom'':l4_vexpr961`;`cod'':l4_vexpr961`] THEN
   ASM_MESON_TAC [l4_vpar_red_star_RULES961]]);;

let l4_vpar_red_star_forall_inv961 = prove
 (`!dom cod b.
   l4_vpar_red_star961 (L4VForallE961 dom cod) b ==>
   ?dom' cod'. b = L4VForallE961 dom' cod' /\
               l4_vpar_red_star961 dom dom' /\
               l4_vpar_red_star961 cod cod'`,
  MESON_TAC [l4_vpar_red_star_forall_inv_aux961]);;

let l4_vpar_red_star_sort_forall_disjoint961 = prove
 (`!u dom cod c.
   ~(l4_vpar_red_star961 (L4VSort961 u) c /\
     l4_vpar_red_star961 (L4VForallE961 dom cod) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`dom:l4_vexpr961`;`cod:l4_vexpr961`;`c:l4_vexpr961`]
    l4_vpar_red_star_forall_inv961) THEN
  UNDISCH_TAC `l4_vpar_red_star961 (L4VSort961 u) c` THEN
  REWRITE_TAC [l4_vpar_red_star_sort_inv961] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC [distinctness "l4_vexpr961"]);;

let l4_vpar_red_star_forall_injective961 = prove
 (`!dom1 cod1 dom2 cod2 c.
   l4_vpar_red_star961 (L4VForallE961 dom1 cod1) c /\
   l4_vpar_red_star961 (L4VForallE961 dom2 cod2) c ==>
   (?dom0. l4_vpar_red_star961 dom1 dom0 /\ l4_vpar_red_star961 dom2 dom0) /\
   (?cod0. l4_vpar_red_star961 cod1 cod0 /\ l4_vpar_red_star961 cod2 cod0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`dom1:l4_vexpr961`;`cod1:l4_vexpr961`;`c:l4_vexpr961`]
    l4_vpar_red_star_forall_inv961) THEN
  MP_TAC (SPECL [`dom2:l4_vexpr961`;`cod2:l4_vexpr961`;`c:l4_vexpr961`]
    l4_vpar_red_star_forall_inv961) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `d2:l4_vexpr961`
    (X_CHOOSE_THEN `c2:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN (X_CHOOSE_THEN `d1:l4_vexpr961`
    (X_CHOOSE_THEN `c1:l4_vexpr961` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `c = L4VForallE961 d1 c1` THEN
  ASM_REWRITE_TAC [injectivity "l4_vexpr961"] THEN
  STRIP_TAC THEN ASM_MESON_TAC []);;
