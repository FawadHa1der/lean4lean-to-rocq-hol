(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of Rocq Quotient.v8-86. SOURCE ONLY / UNCOMPILED.
   Pure generated syntax and Eq prerequisite; not raw metadata admission. *)
needs "hol/kernel_declarations493.ml";;
needs "hol/nested_parameters491.ml";;
needs "hol/kernel_locals489.ml";;
needs "hol/nested_keys480.ml";;

let l4_q_name608 = new_definition
 `l4_q_name608 = L4String L4Anonymous [81;117;111;116]`;;
let l4_q_mk_name608 = new_definition
 `l4_q_mk_name608 = L4String l4_q_name608 [109;107]`;;
let l4_q_lift_name608 = new_definition
 `l4_q_lift_name608 = L4String l4_q_name608 [108;105;102;116]`;;
let l4_q_ind_name608 = new_definition
 `l4_q_ind_name608 = L4String l4_q_name608 [105;110;100]`;;
let l4_q_eq_name608 = new_definition
 `l4_q_eq_name608 = L4String L4Anonymous [69;113]`;;

let l4_q_arrow608 = new_definition
 `l4_q_arrow608 a b = L4KPi447 L4Anonymous L4KDefault447 a (l4_klift447 b 1 0)`;;
let l4_q_local608 = new_definition
 `l4_q_local608 s label bi ty = l4_kind_fresh491 s (L4String L4Anonymous label) bi ty`;;

let l4_quotient_eq_type608 = new_definition
 `l4_quotient_eq_type608 u =
   let fresh = l4_q_local608 l4_kinitial_state491 [97;108;112;104;97]
     L4KImplicit447 (L4KSort447 u) in
   let a = FST fresh in
   l4_kclose_pi489 [a]
     (l4_q_arrow608 (l4_klocal_expr489 a)
       (l4_q_arrow608 (l4_klocal_expr489 a) (L4KSort447 L4KZero447)))`;;

let l4_quotient_eq_refl_type608 = new_definition
 `l4_quotient_eq_refl_type608 u =
   let fresh_alpha = l4_q_local608 l4_kinitial_state491 [97;108;112;104;97]
     L4KImplicit447 (L4KSort447 u) in
   let alpha = FST fresh_alpha in
   let fresh_a = l4_q_local608 (SND fresh_alpha) [97] L4KDefault447
     (l4_klocal_expr489 alpha) in
   let a = FST fresh_a in
   l4_kclose_pi489 [alpha;a]
     (l4_kapply_exprs489
       [l4_klocal_expr489 alpha;l4_klocal_expr489 a;l4_klocal_expr489 a]
       (L4KConst447 l4_q_eq_name608 [u]))`;;

(* Match the exact local prerequisite, including its first-error order.
   Equality is Syntax.expr_eqb480, not defeq or raw expression equality. *)
let l4_quotient_check_eq608 = new_definition
 `l4_quotient_check_eq608 env =
   match l4_kfind_decl493 env l4_q_eq_name608 with
   | NONE -> L4KReject491 L4KUnknownConstant491
   | SOME d ->
     (match (l4_kdecl_kind493 d,l4_kdecl_params493 d) with
      | (L4KDInductive493 info,[u]) ->
        if ~l4_kexpr_eqb480 (l4_kdecl_type493 d)
          (l4_quotient_eq_type608 (L4KParam447 u))
        then L4KReject491 L4KMalformedDeclaration491 else
        (match l4_kind_ctors493 info with
         | [ctor] ->
           (match l4_kfind_decl493 env ctor with
            | NONE -> L4KReject491 L4KUnknownConstant491
            | SOME c ->
              (match (l4_kdecl_kind493 c,l4_kdecl_params493 c) with
               | (L4KDConstructor493 ci,[v]) ->
                 if l4_kctor_induct493 ci = l4_q_eq_name608 /\
                    l4_kexpr_eqb480 (l4_kdecl_type493 c)
                      (l4_quotient_eq_refl_type608 (L4KParam447 v))
                 then L4KAccept491 one else L4KReject491 L4KMalformedDeclaration491
               | _ -> L4KReject491 L4KMalformedDeclaration491))
         | _ -> L4KReject491 L4KMalformedDeclaration491)
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

(* Allocate a even in QType/QInd, as in Rocq. In QLift it is closed in sanity;
   the final outer telescope is alpha,relation,beta,f, not allocation order. *)
let l4_canonical_quotient608 = new_definition
 `l4_canonical_quotient608 kind =
   let un = L4String L4Anonymous [117] in
   let vn = L4String L4Anonymous [118] in
   let u = L4KParam447 un in
   let v = L4KParam447 vn in
   let fresh_alpha = l4_q_local608 l4_kinitial_state491 [97;108;112;104;97]
     L4KImplicit447 (L4KSort447 u) in
   let alpha = FST fresh_alpha in
   let av = l4_klocal_expr489 alpha in
   let fresh_relation = l4_q_local608 (SND fresh_alpha) [114]
     (match kind with
      | L4KQType493 -> L4KDefault447
      | L4KQCtor493 -> L4KDefault447
      | _ -> L4KImplicit447)
     (l4_q_arrow608 av (l4_q_arrow608 av (L4KSort447 L4KZero447))) in
   let relation = FST fresh_relation in
   let rv = l4_klocal_expr489 relation in
   let quot = l4_kapply_exprs489 [av;rv] (L4KConst447 l4_q_name608 [u]) in
   let fresh_a = l4_q_local608 (SND fresh_relation) [97] L4KDefault447 av in
   let a = FST fresh_a in
   let aa = l4_klocal_expr489 a in
   let built =
     match kind with
     | L4KQType493 ->
       (l4_q_name608,[un],l4_kclose_pi489 [alpha;relation] (L4KSort447 u))
     | L4KQCtor493 ->
       (l4_q_mk_name608,[un],l4_kclose_pi489 [alpha;relation;a] quot)
     | L4KQLift493 ->
       let fresh_beta = l4_q_local608 (SND fresh_a) [98;101;116;97]
         L4KImplicit447 (L4KSort447 v) in
       let beta = FST fresh_beta in
       let bv = l4_klocal_expr489 beta in
       let fresh_f = l4_q_local608 (SND fresh_beta) [102] L4KDefault447 (l4_q_arrow608 av bv) in
       let f = FST fresh_f in
       let fv = l4_klocal_expr489 f in
       let fresh_b = l4_q_local608 (SND fresh_f) [98] L4KDefault447 av in
       let b = FST fresh_b in
       let bb = l4_klocal_expr489 b in
       let equality = l4_kapply_exprs489 [bv;L4KApp447 fv aa;L4KApp447 fv bb]
         (L4KConst447 l4_q_eq_name608 [v]) in
       let sanity = l4_kclose_pi489 [a;b]
         (l4_q_arrow608 (l4_kapply_exprs489 [aa;bb] rv) equality) in
       (l4_q_lift_name608,[un;vn],l4_kclose_pi489 [alpha;relation;beta;f]
         (l4_q_arrow608 sanity (l4_q_arrow608 quot bv)))
     | L4KQInd493 ->
       let fresh_beta = l4_q_local608 (SND fresh_a) [98;101;116;97]
         L4KImplicit447 (l4_q_arrow608 quot (L4KSort447 L4KZero447)) in
       let beta = FST fresh_beta in
       let bv = l4_klocal_expr489 beta in
       let all_quot = l4_kclose_pi489 [a]
         (L4KApp447 bv (l4_kapply_exprs489 [av;rv;aa] (L4KConst447 l4_q_mk_name608 [u]))) in
       let fresh_q = l4_q_local608 (SND fresh_beta) [113] L4KImplicit447 quot in
       let q = FST fresh_q in
       (l4_q_ind_name608,[un],l4_kclose_pi489 [alpha;relation]
         (l4_kclose_pi489 [beta]
           (l4_q_arrow608 all_quot (l4_kclose_pi489 [q] (L4KApp447 bv (l4_klocal_expr489 q)))))) in
   L4KDeclaration493 (FST built) (FST (SND built)) (SND (SND built))
     NONE (L4KDQuotient493 kind) L4KHintOpaque493`;;
