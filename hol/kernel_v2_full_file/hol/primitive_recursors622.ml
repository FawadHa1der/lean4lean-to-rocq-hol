(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 port of rocq/Primitives.v469-711.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE622.txt and ../EXPORTS622.txt.
   All semantic checks use the concrete597 kernel, not a verdict callback. *)
needs "hol/checked_telescope606.ml";;
needs "hol/member_verification509.ml";;
needs "hol/primitive_foundations619.ml";;
needs "hol/primitive_reflection621.ml";;

let l4_primitive_whnf_core622 = new_definition
 `l4_primitive_whnf_core622 fuel env g e =
   l4_whnf_core_method543 (l4_checker597 fuel env []) F g e`;;

(* Unlike core_unfold528 this rejects neither missing bodies nor opaque heads:
   it declines both, and never unfolds a theorem. Getter failures come first. *)
let l4_primitive_unfold622 = new_definition
 `l4_primitive_unfold622 env e =
   let spine = l4_ksplit_app489 e in
   match FST spine with
   | L4KConst447 n us ->
       l4_kr_bind491 (l4_get_constant528 env [] n us) (\d.
         let reducible =
           match l4_kdecl_kind493 d with
           | L4KDDefinition493 -> T
           | L4KDPrimitive493 op -> T
           | _ -> F in
         if reducible then
           match l4_kdecl_value493 d with
           | SOME value -> L4KAccept491
               (l4_kapply_exprs489 (SND spine)
                 (l4_ksubst_levels488 (l4_kdecl_params493 d) us value))
           | NONE -> L4KDecline491 L4KUnsupportedDeclaration491
         else L4KDecline491 L4KUnsupportedDeclaration491)
   | _ -> L4KDecline491 L4KUnsupportedDeclaration491`;;

(* Depth-first already agrees with Rocq. Only metadata and lambdas consume
   depth; sort checking keeps the original kernel fuel and the raw domain. *)
let l4_primitive_lambda_telescope622 = new_recursive_definition num_RECURSION
 `(l4_primitive_lambda_telescope622 0 fuel env s e =
     L4KDecline491 L4KOutOfFuel491) /\
  (l4_primitive_lambda_telescope622 (SUC depth) fuel env s e =
     match e with
     | L4KMData447 a -> l4_primitive_lambda_telescope622 depth fuel env s a
     | L4KLam447 user bi ty body ->
         l4_kr_bind491 (l4_sort_of543 (l4_checker597 fuel env [])
           (l4_kstate_context532 s) ty) (\ignored.
             let fresh = l4_kind_fresh491 s user bi ty in
             l4_kr_bind491
               (l4_primitive_lambda_telescope622 depth fuel env (SND fresh)
                 (l4_kinst447 body (l4_klocal_expr489 (FST fresh))))
               (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest)))
     | _ -> L4KAccept491 ([],(e,s)))`;;

let l4_primitive_no_free622 = new_recursive_definition num_RECURSION
 `(l4_primitive_no_free622 0 n e = L4KDecline491 L4KOutOfFuel491) /\
  (l4_primitive_no_free622 (SUC fuel) n e =
     match e with
     | L4KFVar447 m ->
         if n = m then L4KReject491 L4KMalformedDeclaration491 else L4KAccept491 one
     | L4KApp447 a b ->
         l4_kr_bind491 (l4_primitive_no_free622 fuel n a)
           (\ignored. l4_primitive_no_free622 fuel n b)
     | L4KLam447 user bi a b ->
         l4_kr_bind491 (l4_primitive_no_free622 fuel n a)
           (\ignored. l4_primitive_no_free622 fuel n b)
     | L4KPi447 user bi a b ->
         l4_kr_bind491 (l4_primitive_no_free622 fuel n a)
           (\ignored. l4_primitive_no_free622 fuel n b)
     | L4KLet447 user a v b nd ->
         l4_kr_bind491 (l4_primitive_no_free622 fuel n a) (\ignored_a.
           l4_kr_bind491 (l4_primitive_no_free622 fuel n v)
             (\ignored_v. l4_primitive_no_free622 fuel n b))
     | L4KProj447 user idx a -> l4_primitive_no_free622 fuel n a
     | L4KMData447 a -> l4_primitive_no_free622 fuel n a
     | _ -> L4KAccept491 one)`;;

let l4_primitive_proof622 = new_definition
 `l4_primitive_proof622 fuel env g e =
   l4_kr_bind491 (l4_infer597 fuel env [] g e) (\ty.
     l4_kr_bind491 (l4_sort_of543 (l4_checker597 fuel env []) g ty) (\u.
       l4_kr_bind491 (l4_klevel_equiv555 fuel u L4KZero447)
         (\is_prop. if is_prop then L4KAccept491 one
           else L4KReject491 L4KTypeMismatch491)))`;;

let l4_primitive_probe_INDUCT622,l4_primitive_probe_RECURSION622 = define_type
 "l4_primitive_probe622 = L4PrimitiveProbe622 l4_kexpr447 l4_kexpr447 l4_kexpr447";;
let l4_primitive_probe_pack622 = new_recursive_definition l4_primitive_probe_RECURSION622
 `l4_primitive_probe_pack622 (L4PrimitiveProbe622 pack dom functional) = pack`;;
let l4_primitive_probe_dom622 = new_recursive_definition l4_primitive_probe_RECURSION622
 `l4_primitive_probe_dom622 (L4PrimitiveProbe622 pack dom functional) = dom`;;
let l4_primitive_probe_functional622 = new_recursive_definition l4_primitive_probe_RECURSION622
 `l4_primitive_probe_functional622 (L4PrimitiveProbe622 pack dom functional) = functional`;;

let l4_primitive_check_go622 = new_definition
 `l4_primitive_check_go622 fuel env s go =
   l4_kr_bind491 (l4_primitive_unfold622 env go) (\value.
     l4_kr_bind491 (l4_primitive_lambda_telescope622 fuel fuel env s value) (\opened.
       let st = SND (SND opened) in
       match (FST opened,FST (SND opened)) with
       | ([a0;a1;a2;f;t],L4KApp447 nat_rec t') ->
           if ~l4_kexpr_eqb480 t' (l4_klocal_expr489 t)
           then L4KReject491 L4KNotDefinitionallyEqual491 else
           l4_kr_bind491 (l4_primitive_no_free622 fuel (l4_klocal_id489 t) nat_rec)
             (\ignored_free.
               l4_kr_bind491 (l4_infer597 fuel env [] (l4_kstate_context532 st)
                 (l4_primitive_succ619 (l4_klocal_expr489 t))) (\ignored_succ.
                   let next = L4KApp447 nat_rec
                     (l4_primitive_succ619 (l4_klocal_expr489 t)) in
                   l4_kr_bind491 (l4_infer597 fuel env [] (l4_kstate_context532 st) next)
                     (\ignored_next.
                       l4_kr_bind491 (l4_primitive_whnf_core622 fuel env
                         (l4_kstate_context532 st) next) (\reduced.
                           l4_kr_bind491
                             (l4_primitive_lambda_telescope622 fuel fuel env st reduced)
                             (\opened_y.
                               let sty = SND (SND opened_y) in
                               match (FST opened_y,FST (SND opened_y)) with
                               | ([x;ignored_y],L4KApp447 fx ih) ->
                                   if ~l4_kexpr_eqb480 fx
                                     (L4KApp447 (l4_klocal_expr489 f) (l4_klocal_expr489 x))
                                   then L4KReject491 L4KNotDefinitionallyEqual491 else
                                   l4_kr_bind491
                                     (l4_primitive_lambda_telescope622 fuel fuel env sty ih)
                                     (\opened_z.
                                       let stz = SND (SND opened_z) in
                                       match (FST opened_z,FST (SND opened_z)) with
                                       | ([y;ignored_z],L4KApp447 recursive_call pf) ->
                                           l4_kr_bind491 (l4_primitive_proof622 fuel env
                                             (l4_kstate_context532 stz) pf) (\ignored_pf.
                                               if l4_kexpr_eqb480 recursive_call
                                                 (l4_kapply_exprs489
                                                   [l4_klocal_expr489 t;l4_klocal_expr489 y]
                                                   nat_rec)
                                               then L4KAccept491 one
                                               else L4KReject491 L4KNotDefinitionallyEqual491)
                                       | _ -> L4KDecline491 L4KUnsupportedDeclaration491)
                               | _ -> L4KDecline491 L4KUnsupportedDeclaration491)))))
       | _ -> L4KDecline491 L4KUnsupportedDeclaration491))`;;

(* Functional retyping below uses s, not st/sa: the opened recursion locals
   must not escape into F. The returned pack/dom are checked after closing. *)
let l4_primitive_unfold_nat_well_founded622 = new_definition
 `l4_primitive_unfold_nat_well_founded622 fuel env s e measure =
   l4_kr_bind491 (l4_primitive_lambda_telescope622 fuel fuel env s measure) (\opened.
     let locals = FST opened in
     let measure_body = FST (SND opened) in
     let st = SND (SND opened) in
     let applied = l4_kapply_locals489 locals e in
     l4_kr_bind491 (l4_infer597 fuel env [] (l4_kstate_context532 st) applied)
       (\ignored_applied.
         l4_kr_bind491 (l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st) applied)
           (\top0. l4_kr_bind491 (l4_primitive_unfold622 env top0) (\top1.
             l4_kr_bind491 (l4_primitive_whnf_core622 fuel env (l4_kstate_context532 st) top1)
               (\top2.
                 let spine = l4_ksplit_app489 top2 in
                 match spine with
                 | (L4KConst447 fix_name [u;v],[alpha;motive;meas;functional;packed]) ->
                     if ~(fix_name = l4_primitive_path621
                       [[87;101;108;108;70;111;117;110;100;101;100];[78;97;116];[102;105;120]])
                     then L4KReject491 L4KMalformedDeclaration491 else
                     l4_kr_bind491 (l4_infer597 fuel env [] (l4_kstate_context532 st) packed)
                       (\ty.
                         let fresh_a = l4_kind_fresh491 st L4Anonymous L4KDefault447 ty in
                         let sa = SND fresh_a in
                         let av = l4_klocal_expr489 (FST fresh_a) in
                         l4_kr_bind491 (l4_check597 fuel env [] (l4_kstate_context532 sa)
                           (L4KApp447 meas av) l4_core_nat533) (\ignored_meas_type.
                             l4_kr_bind491 (l4_check_defeq597 fuel env [] (l4_kstate_context532 sa)
                               (L4KApp447 meas packed) measure_body) (\ignored_measure.
                                 l4_kr_bind491 (l4_primitive_unfold622 env
                                   (l4_kapply_exprs489 [alpha;motive;meas;functional;av] (FST spine)))
                                   (\unfolded0.
                                     l4_kr_bind491 (l4_primitive_whnf_core622 fuel env
                                       (l4_kstate_context532 sa) unfolded0) (\unfolded1.
                                         let go_spine = l4_ksplit_app489 unfolded1 in
                                         match SND go_spine with
                                         | [alpha';motive';meas';functional';fuel_expr;av';pf] ->
                                             if ~l4_klist_eqb509 l4_kexpr_eqb480
                                               [alpha;motive;meas;functional;av]
                                               [alpha';motive';meas';functional';av']
                                             then L4KReject491 L4KNotDefinitionallyEqual491 else
                                             l4_kr_bind491 (l4_primitive_proof622 fuel env
                                               (l4_kstate_context532 sa) pf) (\ignored_pf.
                                                 match fuel_expr with
                                                 | L4KApp447 eager n ->
                                                     l4_kr_bind491 (l4_check_defeq597 fuel env []
                                                       (l4_kstate_context532 sa) n
                                                       (l4_primitive_succ619 (L4KApp447 meas av)))
                                                       (\ignored_fuel.
                                                         l4_kr_bind491
                                                           (l4_primitive_authenticated619 fuel env L4KPNatBEq493)
                                                           (\ignored_beq.
                                                             let fresh_x = l4_kind_fresh491 sa L4Anonymous
                                                               L4KDefault447 l4_core_nat533 in
                                                             let xv = l4_pq_embed621
                                                               (l4_klocal_expr489 (FST fresh_x)) in
                                                             l4_kr_bind491 (l4_check_defeq597 fuel env []
                                                               (l4_kstate_context532 (SND fresh_x))
                                                               (L4KApp447 eager (l4_klocal_expr489 (FST fresh_x)))
                                                               (l4_pq_run621
                                                                 (l4_primitive_condition_ite621 L4PCBool621
                                                                   l4_pq_nat621 [l4_pq_call621 L4KPNatBEq493 [xv;xv]]
                                                                   xv xv))) (\ignored_eager.
                                                                 l4_kr_bind491 (l4_primitive_check_go622
                                                                   fuel env s (FST go_spine)) (\ignored_go.
                                                                     l4_kr_bind491 (l4_infer597 fuel env []
                                                                       (l4_kstate_context532 s) functional) (\fty0.
                                                                         l4_kr_bind491 (l4_whnf597 fuel env []
                                                                           (l4_kstate_context532 s) fty0) (\fty1.
                                                                             match fty1 with
                                                                             | L4KPi447 user bi domain cod ->
                                                                                 l4_kr_bind491
                                                                                   (l4_check_defeq597 fuel env []
                                                                                     (l4_kstate_context532 st) ty domain)
                                                                                   (\ignored_domain.
                                                                                     let fresh_z = l4_kind_fresh491 s
                                                                                       L4Anonymous L4KDefault447 domain in
                                                                                     l4_kr_bind491 (l4_whnf597 fuel env []
                                                                                       (l4_kstate_context532 (SND fresh_z))
                                                                                       (l4_kinst447 cod
                                                                                         (l4_klocal_expr489 (FST fresh_z))))
                                                                                       (\cod1.
                                                                                         match cod1 with
                                                                                         | L4KPi447 user2 bi2 ih_domain rest ->
                                                                                             let dom = l4_kclose_lam489
                                                                                               [FST fresh_z] ih_domain in
                                                                                             let pack = l4_kclose_lam489 locals packed in
                                                                                             l4_kr_bind491 (l4_infer597 fuel env []
                                                                                               (l4_kstate_context532 s) pack)
                                                                                               (\ignored_pack.
                                                                                                 l4_kr_bind491 (l4_infer597 fuel env []
                                                                                                   (l4_kstate_context532 s) dom)
                                                                                                   (\ignored_dom. L4KAccept491
                                                                                                     (L4PrimitiveProbe622 pack dom functional)))
                                                                                         | _ -> L4KReject491 L4KExpectedPi491))
                                                                             | _ -> L4KReject491 L4KExpectedPi491))))))
                                                 | _ -> L4KDecline491 L4KUnsupportedDeclaration491)
                                         | _ -> L4KDecline491 L4KUnsupportedDeclaration491)))))
                 | _ -> L4KDecline491 L4KUnsupportedDeclaration491)))))`;;

(* rhs constructs an object-language term only. The concrete kernel checks
   both sides and their common type in the freshly extended ih context. *)
let l4_primitive_run_probe622 = new_definition
 `l4_primitive_run_probe622 fuel env s p args rhs =
   let a = l4_kapply_exprs489 args (l4_primitive_probe_pack622 p) in
   let fresh = l4_kind_fresh491 s L4Anonymous L4KDefault447
     (L4KApp447 (l4_primitive_probe_dom622 p) a) in
   l4_check_defeq597 fuel env [] (l4_kstate_context532 (SND fresh))
     (l4_kapply_exprs489 [a;l4_klocal_expr489 (FST fresh)] (l4_primitive_probe_functional622 p))
     (rhs (l4_klocal_expr489 (FST fresh)))`;;

let l4_primitive_first_measure622 = new_definition
 `l4_primitive_first_measure622 =
   l4_pq_run621 (l4_pq_lam621 l4_pq_nat621 (\m.
     l4_pq_lam621 l4_pq_nat621 (\ignored. m)))`;;

let l4_primitive_check_gcd622 = new_definition
 `l4_primitive_check_gcd622 fuel env body =
   if ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env)
   then L4KReject491 L4KMalformedDeclaration491 else
   l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatMod493) (\ignored_mod.
     l4_kr_bind491 (l4_primitive_check_condition621 fuel env L4PCBool621 T F)
       (\ignored_condition.
         l4_kr_bind491 (l4_primitive_unfold_nat_well_founded622 fuel env
           l4_kinitial_state491 body l4_primitive_first_measure622) (\p.
             let fresh_n = l4_kind_fresh491 l4_kinitial_state491 L4Anonymous
               L4KDefault447 l4_core_nat533 in
             let n = FST fresh_n in
             let sn = SND fresh_n in
             l4_kr_bind491 (l4_primitive_run_probe622 fuel env sn p
               [l4_primitive_zero619;l4_klocal_expr489 n] (\ignored. l4_klocal_expr489 n))
               (\ignored_base.
                 let fresh_m = l4_kind_fresh491 sn L4Anonymous L4KDefault447 l4_core_nat533 in
                 l4_primitive_run_probe622 fuel env (SND fresh_m) p
                   [l4_primitive_succ619 (l4_klocal_expr489 (FST fresh_m));l4_klocal_expr489 n]
                   (\ih.
                     let mm = l4_pq_embed621 (l4_klocal_expr489 (FST fresh_m)) in
                     let nn = l4_pq_embed621 (l4_klocal_expr489 n) in
                     l4_pq_run621 (l4_pq_apps621 (l4_pq_embed621 ih)
                       [l4_pq_apps621 (l4_pq_embed621 (l4_primitive_probe_pack622 p))
                         [l4_pq_call621 L4KPNatMod493 [nn;l4_pq_succ621 mm];l4_pq_succ621 mm];
                        l4_pq_apps621
                          (l4_pq_const621 [[78;97;116];[109;111;100;95;108;116]] [])
                          [nn;l4_pq_succ621 mm;
                           l4_pq_app621 (l4_pq_const621
                             [[78;97;116];[122;101;114;111;95;108;116;95;115;117;99;99]] []) mm]]))))))`;;

let l4_primitive_bool_operator_type622 = new_definition
 `l4_primitive_bool_operator_type622 =
   l4_primitive_arrow619 l4_primitive_bool619
     (l4_primitive_arrow619 l4_primitive_bool619 l4_primitive_bool619)`;;

let l4_primitive_check_bitwise622 = new_definition
 `l4_primitive_check_bitwise622 fuel env body =
   if ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env)
   then L4KReject491 L4KMalformedDeclaration491 else
   l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatAdd493) (\ignored_add.
     l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatDiv493) (\ignored_div.
       l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatMod493) (\ignored_mod.
         l4_kr_bind491 (l4_primitive_check_condition621 fuel env L4PCNatEq621 T T)
           (\ignored_nat_condition.
             l4_kr_bind491 (l4_primitive_check_condition621 fuel env L4PCBool621 T F)
               (\ignored_bool_condition.
                 let fresh_f = l4_kind_fresh491 l4_kinitial_state491 L4Anonymous
                   L4KDefault447 l4_primitive_bool_operator_type622 in
                 let f = FST fresh_f in
                 let sf = SND fresh_f in
                 l4_kr_bind491 (l4_primitive_unfold_nat_well_founded622 fuel env sf
                   (L4KApp447 body (l4_klocal_expr489 f)) l4_primitive_first_measure622) (\p.
                     let fresh_n = l4_kind_fresh491 sf L4Anonymous L4KDefault447 l4_core_nat533 in
                     let n = FST fresh_n in
                     let fresh_m = l4_kind_fresh491 (SND fresh_n) L4Anonymous L4KDefault447 l4_core_nat533 in
                     let m = FST fresh_m in
                     l4_primitive_run_probe622 fuel env (SND fresh_m) p
                       [l4_klocal_expr489 n;l4_klocal_expr489 m] (\ih.
                         let fq = l4_pq_embed621 (l4_klocal_expr489 f) in
                         let nq = l4_pq_embed621 (l4_klocal_expr489 n) in
                         let mq = l4_pq_embed621 (l4_klocal_expr489 m) in
                         let bool_ite = \b. l4_primitive_condition_ite621 L4PCBool621 l4_pq_nat621 [b] in
                         l4_pq_run621 (l4_primitive_condition_dite621 L4PCNatEq621 [nq;l4_pq_zero621]
                           (\ignored. bool_ite (l4_pq_apps621 fq [l4_pq_fal621;l4_pq_tru621]) mq l4_pq_zero621)
                           (\hn. l4_primitive_condition_ite621 L4PCNatEq621 l4_pq_nat621 [mq;l4_pq_zero621]
                             (bool_ite (l4_pq_apps621 fq [l4_pq_tru621;l4_pq_fal621]) nq l4_pq_zero621)
                             (let n' = l4_pq_call621 L4KPNatDiv493 [nq;l4_pq_two621] in
                              let m' = l4_pq_call621 L4KPNatDiv493 [mq;l4_pq_two621] in
                              let b1 = l4_primitive_condition_decide621 L4PCNatEq621
                                [l4_pq_call621 L4KPNatMod493 [nq;l4_pq_two621];l4_pq_one621] in
                              let b2 = l4_primitive_condition_decide621 L4PCNatEq621
                                [l4_pq_call621 L4KPNatMod493 [mq;l4_pq_two621];l4_pq_one621] in
                              let r = l4_pq_apps621 (l4_pq_embed621 ih)
                                [l4_pq_apps621 (l4_pq_embed621 (l4_primitive_probe_pack622 p)) [n';m'];
                                 l4_pq_apps621 (l4_pq_const621
                                   [[78;97;116];[98;105;116;119;105;115;101;95;114;101;99;95;108;101;109;109;97]] [])
                                   [nq;hn]] in
                              let rr = l4_pq_call621 L4KPNatAdd493 [r;r] in
                              bool_ite (l4_pq_apps621 fq [b1;b2])
                                (l4_pq_call621 L4KPNatAdd493 [rr;l4_pq_one621]) rr))))))))))`;;

let l4_primitive_check_boolean_operator622 = new_definition
 `l4_primitive_check_boolean_operator622 fuel env op operator =
   l4_kr_bind491 (l4_check597 fuel env [] l4_kempty_context532 operator
     l4_primitive_bool_operator_type622) (\ignored_type.
       let f = l4_pq_embed621 operator in
       let fx = \b. l4_pq_lam621 l4_pq_bool621 (\x. l4_pq_apps621 f [b;x]) in
       match op with
       | L4KPNatLAnd493 ->
           l4_kr_bind491 (l4_primitive_eq_closed621 fuel env (fx l4_pq_fal621)
             (l4_pq_lam621 l4_pq_bool621 (\ignored. l4_pq_fal621))) (\ignored_false.
               l4_primitive_eq_closed621 fuel env (fx l4_pq_tru621)
                 (l4_pq_lam621 l4_pq_bool621 (\x. x)))
       | L4KPNatLOr493 ->
           l4_kr_bind491 (l4_primitive_eq_closed621 fuel env (fx l4_pq_fal621)
             (l4_pq_lam621 l4_pq_bool621 (\x. x))) (\ignored_false.
               l4_primitive_eq_closed621 fuel env (fx l4_pq_tru621)
                 (l4_pq_lam621 l4_pq_bool621 (\ignored. l4_pq_tru621)))
       | L4KPNatXor493 ->
           l4_kr_bind491 (l4_primitive_eq_closed621 fuel env
             (l4_pq_apps621 f [l4_pq_fal621;l4_pq_fal621]) l4_pq_fal621) (\ignored_ff.
               l4_kr_bind491 (l4_primitive_eq_closed621 fuel env
                 (l4_pq_apps621 f [l4_pq_tru621;l4_pq_fal621]) l4_pq_tru621) (\ignored_tf.
                   l4_kr_bind491 (l4_primitive_eq_closed621 fuel env
                     (l4_pq_apps621 f [l4_pq_fal621;l4_pq_tru621]) l4_pq_tru621) (\ignored_ft.
                       l4_primitive_eq_closed621 fuel env
                         (l4_pq_apps621 f [l4_pq_tru621;l4_pq_tru621]) l4_pq_fal621)))
       | _ -> L4KDecline491 L4KUnsupportedDeclaration491)`;;

let l4_primitive_check_bitwise_instance622 = new_definition
 `l4_primitive_check_bitwise_instance622 fuel env op body =
   l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatBitwise493) (\ignored_bitwise.
     match body with
     | L4KApp447 (L4KConst447 n []) operator ->
         if n = l4_primitive_bitwise_name619
         then l4_primitive_check_boolean_operator622 fuel env op operator
         else L4KReject491 L4KMalformedDeclaration491
     | _ -> L4KDecline491 L4KUnsupportedDeclaration491)`;;
