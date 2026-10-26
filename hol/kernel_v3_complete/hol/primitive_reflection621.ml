(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed canonical full447 port of rocq/Primitives.v191-468.
   SOURCE ONLY / UNCOMPILED. See ../API621.txt and ../NOTICE621.txt.
   Construction functions return syntax. Checks use the actual597 kernel. *)
needs "hol/primitive_foundations619.ml";;
needs "hol/kernel_checker597.ml";;

(* List-first recursion implements fold_left NameStr without reversing parts. *)
let l4_primitive_path_aux621 = new_recursive_definition list_RECURSION
 `(l4_primitive_path_aux621 [] n = n) /\
  (l4_primitive_path_aux621 (CONS s ss) n =
    l4_primitive_path_aux621 ss (L4String n s))`;;
let l4_primitive_path621 = new_definition
 `l4_primitive_path621 parts = l4_primitive_path_aux621 parts L4Anonymous`;;
let l4_primitive_const621 = new_definition
 `l4_primitive_const621 parts us = L4KConst447 (l4_primitive_path621 parts) us`;;

(* Quotation terms are HOL functions num -> l4_kexpr447. Binder callbacks here
   construct syntax only. They are never supplied as logical verdict methods. *)
let l4_pq_embed621 = new_definition
 `l4_pq_embed621 e depth = l4_klift447 e depth 0`;;
let l4_pq_app621 = new_definition
 `l4_pq_app621 (f:num->l4_kexpr447) a depth = L4KApp447 (f depth) (a depth)`;;
let l4_pq_apps621 = new_definition
 `l4_pq_apps621 (f:num->l4_kexpr447) args depth =
    l4_kapply_exprs489 (MAP (\a. a depth) args) (f depth)`;;
let l4_pq_lam621 = new_definition
 `l4_pq_lam621 a b depth =
    L4KLam447 L4Anonymous L4KDefault447 (a depth)
      (b (\d. L4KBVar447 (d - SUC depth)) (SUC depth))`;;
let l4_pq_pi621 = new_definition
 `l4_pq_pi621 a b depth =
    L4KPi447 L4Anonymous L4KDefault447 (a depth)
      (b (\d. L4KBVar447 (d - SUC depth)) (SUC depth))`;;
let l4_pq_arrow621 = new_definition
 `l4_pq_arrow621 a b = l4_pq_pi621 a (\ignored. b)`;;
let l4_pq_run621 = new_definition
 `l4_pq_run621 (e:num->l4_kexpr447) = e 0`;;
let l4_pq_const621 = new_definition
 `l4_pq_const621 parts us = l4_pq_embed621 (l4_primitive_const621 parts us)`;;
let l4_pq_prop621 = new_definition
 `l4_pq_prop621 = l4_pq_embed621 (L4KSort447 L4KZero447)`;;
let l4_pq_type0621 = new_definition
 `l4_pq_type0621 = l4_pq_embed621 (L4KSort447 (L4KSucc447 L4KZero447))`;;
let l4_pq_nat621 = new_definition
 `l4_pq_nat621 = l4_pq_embed621 l4_core_nat533`;;
let l4_pq_bool621 = new_definition
 `l4_pq_bool621 = l4_pq_embed621 l4_primitive_bool619`;;
let l4_pq_tru621 = new_definition
 `l4_pq_tru621 = l4_pq_embed621 l4_primitive_true619`;;
let l4_pq_fal621 = new_definition
 `l4_pq_fal621 = l4_pq_embed621 l4_primitive_false619`;;
let l4_pq_zero621 = new_definition
 `l4_pq_zero621 = l4_pq_embed621 l4_primitive_zero619`;;
let l4_pq_one621 = new_definition
 `l4_pq_one621 = l4_pq_embed621 l4_primitive_one619`;;
let l4_pq_two621 = new_definition
 `l4_pq_two621 = l4_pq_embed621 l4_primitive_two619`;;
let l4_pq_succ621 = new_definition
 `l4_pq_succ621 n =
    l4_pq_app621 (l4_pq_embed621 (L4KConst447 l4_core_succ_name533 [])) n`;;
let l4_pq_call621 = new_definition
 `l4_pq_call621 op args =
    l4_pq_apps621 (l4_pq_embed621 (L4KConst447 (l4_primitive_name619 op) [])) args`;;
let l4_pq_eq621 = new_definition
 `l4_pq_eq621 a x y =
    l4_pq_apps621 (l4_pq_const621 [[69;113]] [L4KSucc447 L4KZero447]) [a;x;y]`;;
let l4_pq_refl621 = new_definition
 `l4_pq_refl621 a x =
    l4_pq_apps621 (l4_pq_const621 [[69;113];[114;101;102;108]]
      [L4KSucc447 L4KZero447]) [a;x]`;;
let l4_pq_not621 = new_definition
 `l4_pq_not621 p = l4_pq_app621 (l4_pq_const621 [[78;111;116]] []) p`;;
let l4_pq_dec621 = new_definition
 `l4_pq_dec621 p =
    l4_pq_app621 (l4_pq_const621 [[68;101;99;105;100;97;98;108;101]] []) p`;;
let l4_pq_is_true621 = new_definition
 `l4_pq_is_true621 p h = l4_pq_apps621
    (l4_pq_const621 [[68;101;99;105;100;97;98;108;101];[105;115;84;114;117;101]] []) [p;h]`;;
let l4_pq_is_false621 = new_definition
 `l4_pq_is_false621 p h = l4_pq_apps621
    (l4_pq_const621 [[68;101;99;105;100;97;98;108;101];[105;115;70;97;108;115;101]] []) [p;h]`;;
let l4_pq_ite621 = new_definition
 `l4_pq_ite621 ty p d t e = l4_pq_apps621
    (l4_pq_const621 [[105;116;101]] [L4KSucc447 L4KZero447]) [ty;p;d;t;e]`;;
let l4_pq_dite621 = new_definition
 `l4_pq_dite621 ty p d t e = l4_pq_apps621
    (l4_pq_const621 [[100;105;116;101]] [L4KSucc447 L4KZero447])
    [ty;p;d;l4_pq_lam621 p t;l4_pq_lam621 (l4_pq_not621 p) e]`;;
let l4_pq_bool_dec621 = new_definition
 `l4_pq_bool_dec621 b = l4_pq_apps621
    (l4_pq_const621 [[66;111;111;108];[100;101;99;69;113]] []) [b;l4_pq_tru621]`;;

let l4_primitive_reflection_INDUCT621,l4_primitive_reflection_RECURSION621 = define_type
 "l4_primitive_reflection621 =
   L4PrimitiveReflection621 l4_kexpr447 l4_kexpr447 l4_kexpr447 l4_kexpr447";;
let l4_reflection_type621 = new_recursive_definition l4_primitive_reflection_RECURSION621
 `l4_reflection_type621 (L4PrimitiveReflection621 ty yes no dec) = ty`;;
let l4_reflection_true621 = new_recursive_definition l4_primitive_reflection_RECURSION621
 `l4_reflection_true621 (L4PrimitiveReflection621 ty yes no dec) = yes`;;
let l4_reflection_false621 = new_recursive_definition l4_primitive_reflection_RECURSION621
 `l4_reflection_false621 (L4PrimitiveReflection621 ty yes no dec) = no`;;
let l4_reflection_dec621 = new_recursive_definition l4_primitive_reflection_RECURSION621
 `l4_reflection_dec621 (L4PrimitiveReflection621 ty yes no dec) = dec`;;

let l4_primitive_reflection_type621 = new_definition
 `l4_primitive_reflection_type621 false_eq =
    l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p.
      l4_pq_lam621 l4_pq_bool621 (\b.
        l4_pq_pi621 l4_pq_prop621 (\q. l4_pq_arrow621
          (l4_pq_arrow621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621) p)
            (l4_pq_arrow621 (l4_pq_arrow621
              (if false_eq then l4_pq_eq621 l4_pq_bool621 b l4_pq_fal621
               else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621))
              (l4_pq_not621 p)) q)) q))))`;;

let l4_primitive_reflection_make621 = new_definition
 `l4_primitive_reflection_make621 false_eq =
    let rt = l4_primitive_reflection_type621 false_eq in
    let relation = \p b. l4_pq_apps621 (l4_pq_embed621 rt) [p;b] in
    L4PrimitiveReflection621 rt
      (l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p.
        l4_pq_lam621 (relation p l4_pq_tru621) (\h. l4_pq_apps621 h [p;
          l4_pq_lam621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 l4_pq_tru621 l4_pq_tru621) p)
            (\hp. l4_pq_lam621 (l4_pq_arrow621
              (if false_eq then l4_pq_eq621 l4_pq_bool621 l4_pq_tru621 l4_pq_fal621
               else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 l4_pq_tru621 l4_pq_tru621))
              (l4_pq_not621 p)) (\ignored. l4_pq_app621 hp (l4_pq_refl621 l4_pq_bool621 l4_pq_tru621)))]))))
      (l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p.
        l4_pq_lam621 (relation p l4_pq_fal621) (\h. l4_pq_apps621 h [l4_pq_not621 p;
          l4_pq_lam621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 l4_pq_fal621 l4_pq_tru621) p)
            (\ignored. l4_pq_lam621 (l4_pq_arrow621
              (if false_eq then l4_pq_eq621 l4_pq_bool621 l4_pq_fal621 l4_pq_fal621
               else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 l4_pq_fal621 l4_pq_tru621))
              (l4_pq_not621 p))
              (\hn. l4_pq_app621 hn (if false_eq then l4_pq_refl621 l4_pq_bool621 l4_pq_fal621 else
                l4_pq_lam621 (l4_pq_eq621 l4_pq_bool621 l4_pq_fal621 l4_pq_tru621) (\bad.
                  l4_pq_apps621 (l4_pq_const621
                    [[66;111;111;108];[110;111;67;111;110;102;117;115;105;111;110]] [L4KZero447])
                    [l4_pq_const621 [[70;97;108;115;101]] [];l4_pq_fal621;l4_pq_tru621;bad]))))]))))
      (l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p.
        l4_pq_lam621 l4_pq_bool621 (\b. l4_pq_lam621 (relation p b) (\h.
          let pos = \hp. l4_pq_is_true621 p (l4_pq_apps621 h [p;
            l4_pq_lam621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621) p)
              (\yes. l4_pq_lam621 (l4_pq_arrow621
                (if false_eq then l4_pq_eq621 l4_pq_bool621 b l4_pq_fal621
                 else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621))
                (l4_pq_not621 p)) (\ignored. l4_pq_app621 yes hp))]) in
          let neg = \hn. l4_pq_is_false621 p (l4_pq_apps621 h [l4_pq_not621 p;
            l4_pq_lam621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621) p)
              (\ignored. l4_pq_lam621 (l4_pq_arrow621
                (if false_eq then l4_pq_eq621 l4_pq_bool621 b l4_pq_fal621
                 else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621))
                (l4_pq_not621 p)) (\no. l4_pq_app621 no hn))]) in
          if false_eq then
            l4_pq_app621 (l4_pq_apps621
              (l4_pq_const621 [[66;111;111;108];[114;101;99]] [L4KSucc447 L4KZero447])
              [l4_pq_lam621 l4_pq_bool621 (\b'. l4_pq_arrow621
                 (l4_pq_eq621 l4_pq_bool621 b b') (l4_pq_dec621 p));
               l4_pq_lam621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_fal621) neg;
               l4_pq_lam621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621) pos;b])
              (l4_pq_refl621 l4_pq_bool621 b)
          else l4_pq_dite621 (l4_pq_dec621 p) (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621)
            (l4_pq_bool_dec621 b) pos neg)))))`;;

let l4_primitive_reflection_ite621 = new_definition
 `l4_primitive_reflection_ite621 r =
    l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 l4_pq_bool621 (\b.
      l4_pq_lam621 (l4_pq_apps621 (l4_pq_embed621 (l4_reflection_type621 r)) [p;b]) (\h.
        l4_pq_lam621 l4_pq_type0621 (\a. l4_pq_apps621
          (l4_pq_const621 [[105;116;101]] [L4KSucc447 L4KZero447])
          [a;p;l4_pq_apps621 (l4_pq_embed621 (l4_reflection_dec621 r)) [p;b;h]])))))`;;
let l4_primitive_reflection_dite621 = new_definition
 `l4_primitive_reflection_dite621 r =
    l4_pq_run621 (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 l4_pq_bool621 (\b.
      l4_pq_lam621 (l4_pq_apps621 (l4_pq_embed621 (l4_reflection_type621 r)) [p;b]) (\h.
        l4_pq_apps621 (l4_pq_const621 [[100;105;116;101]] [L4KSucc447 L4KZero447])
          [l4_pq_nat621;p;l4_pq_apps621 (l4_pq_embed621 (l4_reflection_dec621 r)) [p;b;h]]))))`;;

let l4_primitive_eq_closed621 = new_definition
 `l4_primitive_eq_closed621 fuel env a b =
    l4_check_defeq597 fuel env [] l4_kempty_context532 (l4_pq_run621 a) (l4_pq_run621 b)`;;
let l4_primitive_check_closed621 = new_definition
 `l4_primitive_check_closed621 fuel env a ty =
    l4_check597 fuel env [] l4_kempty_context532 (l4_pq_run621 a) (l4_pq_run621 ty)`;;

let l4_primitive_check_reflection621 = new_definition
 `l4_primitive_check_reflection621 fuel env r with_ite with_dite =
    let relation = \p b. l4_pq_apps621 (l4_pq_embed621 (l4_reflection_type621 r)) [p;b] in
    l4_kr_bind491
      (l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_type621 r))
        (l4_pq_arrow621 l4_pq_prop621 (l4_pq_arrow621 l4_pq_bool621 l4_pq_prop621)))
      (\ignored_relation.
    l4_kr_bind491
      (if with_ite then
        let it = l4_pq_embed621 (l4_primitive_reflection_ite621 r) in
        l4_kr_bind491
          (l4_primitive_check_closed621 fuel env it
            (l4_pq_pi621 l4_pq_prop621 (\p. l4_pq_pi621 l4_pq_bool621 (\b.
              l4_pq_arrow621 (relation p b)
                (l4_pq_pi621 l4_pq_type0621 (\a. l4_pq_arrow621 a (l4_pq_arrow621 a a)))))))
          (\ignored_ite_type.
        l4_kr_bind491
          (l4_primitive_eq_closed621 fuel env
            (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 (relation p l4_pq_tru621)
              (\h. l4_pq_apps621 it [p;l4_pq_tru621;h])))
            (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 (relation p l4_pq_tru621)
              (\ignored. l4_pq_lam621 l4_pq_type0621 (\a.
                l4_pq_lam621 a (\x. l4_pq_lam621 a (\ignored. x)))))))
          (\ignored_ite_true.
            l4_primitive_eq_closed621 fuel env
              (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 (relation p l4_pq_fal621)
                (\h. l4_pq_apps621 it [p;l4_pq_fal621;h])))
              (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 (relation p l4_pq_fal621)
                (\ignored. l4_pq_lam621 l4_pq_type0621 (\a.
                  l4_pq_lam621 a (\ignored. l4_pq_lam621 a (\x. x))))))))
       else L4KAccept491 one)
      (\ignored_ite.
       if with_dite then
         let di = l4_pq_embed621 (l4_primitive_reflection_dite621 r) in
         l4_kr_bind491
           (l4_primitive_check_closed621 fuel env (l4_pq_const621 [[78;111;116]] [])
             (l4_pq_arrow621 l4_pq_prop621 l4_pq_prop621))
           (\ignored_not.
         l4_kr_bind491
           (l4_primitive_check_closed621 fuel env di
             (l4_pq_pi621 l4_pq_prop621 (\p. l4_pq_pi621 l4_pq_bool621 (\b.
               l4_pq_arrow621 (relation p b)
                 (l4_pq_arrow621 (l4_pq_arrow621 p l4_pq_nat621)
                   (l4_pq_arrow621 (l4_pq_arrow621 (l4_pq_not621 p) l4_pq_nat621) l4_pq_nat621))))))
           (\ignored_dite_type.
         l4_kr_bind491
           (l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_true621 r))
             (l4_pq_pi621 l4_pq_prop621 (\p. l4_pq_arrow621 (relation p l4_pq_tru621) p)))
           (\ignored_true.
         l4_kr_bind491
           (l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_reflection_false621 r))
             (l4_pq_pi621 l4_pq_prop621 (\p.
               l4_pq_arrow621 (relation p l4_pq_fal621) (l4_pq_not621 p))))
           (\ignored_false.
            let lhs = \b. l4_pq_lam621 l4_pq_prop621 (\p.
              l4_pq_lam621 (l4_pq_arrow621 p l4_pq_nat621) (\yes.
                l4_pq_lam621 (l4_pq_arrow621 (l4_pq_not621 p) l4_pq_nat621) (\no.
                  l4_pq_lam621 (relation p b) (\h. l4_pq_apps621 di [p;b;h;yes;no])))) in
            let rhs = \b positive. l4_pq_lam621 l4_pq_prop621 (\p.
              l4_pq_lam621 (l4_pq_arrow621 p l4_pq_nat621) (\yes.
                l4_pq_lam621 (l4_pq_arrow621 (l4_pq_not621 p) l4_pq_nat621) (\no.
                  l4_pq_lam621 (relation p b) (\h.
                    l4_pq_app621 (if positive then yes else no)
                      (l4_pq_apps621 (l4_pq_embed621
                        (if positive then l4_reflection_true621 r else l4_reflection_false621 r)) [p;h]))))) in
            l4_kr_bind491
              (l4_primitive_eq_closed621 fuel env (lhs l4_pq_tru621) (rhs l4_pq_tru621 T))
              (\ignored_positive.
                l4_primitive_eq_closed621 fuel env (lhs l4_pq_fal621) (rhs l4_pq_fal621 F))))))
       else L4KAccept491 one))`;;

let l4_primitive_condition_INDUCT621,l4_primitive_condition_RECURSION621 = define_type
 "l4_primitive_condition621 = L4PCBool621 | L4PCNatLE621 | L4PCNatEq621";;
let l4_primitive_condition_prop621 = new_recursive_definition l4_primitive_condition_RECURSION621
 `(l4_primitive_condition_prop621 L4PCBool621 =
      l4_pq_run621 (l4_pq_lam621 l4_pq_bool621 (\b. l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621))) /\
  (l4_primitive_condition_prop621 L4PCNatLE621 =
      l4_primitive_const621 [[78;97;116];[108;101]] []) /\
  (l4_primitive_condition_prop621 L4PCNatEq621 =
      L4KApp447 (l4_primitive_const621 [[69;113]] [L4KSucc447 L4KZero447]) l4_core_nat533)`;;
let l4_primitive_condition_dec621 = new_recursive_definition l4_primitive_condition_RECURSION621
 `(l4_primitive_condition_dec621 L4PCBool621 =
      l4_pq_run621 (l4_pq_lam621 l4_pq_bool621 l4_pq_bool_dec621)) /\
  (l4_primitive_condition_dec621 L4PCNatLE621 =
      l4_primitive_const621 [[78;97;116];[100;101;99;76;101]] []) /\
  (l4_primitive_condition_dec621 L4PCNatEq621 =
      l4_primitive_const621 [[78;97;116];[100;101;99;69;113]] [])`;;
let l4_primitive_condition_ite621 = new_definition
 `l4_primitive_condition_ite621 c a args t e =
    l4_pq_ite621 a (l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 c)) args)
      (l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_dec621 c)) args) t e`;;
let l4_primitive_condition_dite621 = new_definition
 `l4_primitive_condition_dite621 c args t e =
    l4_pq_dite621 l4_pq_nat621
      (l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 c)) args)
      (l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_dec621 c)) args) t e`;;
let l4_primitive_condition_decide621 = new_definition
 `l4_primitive_condition_decide621 c args =
    l4_primitive_condition_ite621 c l4_pq_bool621 args l4_pq_tru621 l4_pq_fal621`;;

(* Raw PCBool behavior of this builder is preserved; only the two Nat cases
   reach it through check_condition, so no extra construction-time guard. *)
let l4_primitive_condition_proof621 = new_definition
 `l4_primitive_condition_proof621 c =
    let is_eq = c = L4PCNatEq621 in
    l4_pq_run621 (l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_lam621 l4_pq_nat621 (\y.
      let p = l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 c)) [x;y] in
      let b = l4_pq_call621 (if is_eq then L4KPNatBEq493 else L4KPNatBLE493) [x;y] in
      l4_pq_lam621 l4_pq_prop621 (\q.
        l4_pq_lam621
          (l4_pq_arrow621 (l4_pq_arrow621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621) p)
            (l4_pq_arrow621 (l4_pq_arrow621
              (if is_eq then l4_pq_eq621 l4_pq_bool621 b l4_pq_fal621
               else l4_pq_not621 (l4_pq_eq621 l4_pq_bool621 b l4_pq_tru621))
              (l4_pq_not621 p)) q))
          (\h. l4_pq_apps621 h
            [l4_pq_apps621 (l4_pq_const621 [[78;97;116];
               (if is_eq then [101;113;95;111;102;95;98;101;113;95;101;113;95;116;114;117;101]
                else [108;101;95;111;102;95;98;108;101;95;101;113;95;116;114;117;101])] []) [x;y];
             l4_pq_apps621 (l4_pq_const621 [[78;97;116];
               (if is_eq then [110;101;95;111;102;95;98;101;113;95;101;113;95;102;97;108;115;101]
                else [110;111;116;95;108;101;95;111;102;95;110;111;116;95;98;108;101;95;101;113;95;116;114;117;101])]
               []) [x;y]])))))`;;

let l4_primitive_check_condition621 = new_definition
 `l4_primitive_check_condition621 fuel env c with_ite with_dite =
    if ~l4_core_bool_ready533 env then L4KReject491 L4KMalformedDeclaration491 else
    l4_kr_bind491
      (l4_infer597 fuel env [] l4_kempty_context532 (l4_primitive_condition_dec621 c))
      (\ignored_dec.
       if c = L4PCBool621 then
         l4_kr_bind491
           (l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_primitive_condition_prop621 c))
             (l4_pq_arrow621 l4_pq_bool621 l4_pq_prop621))
           (\ignored_prop.
         l4_kr_bind491
           (if with_ite then
             let it = l4_pq_lam621 l4_pq_bool621 (\b. l4_pq_apps621
               (l4_pq_const621 [[105;116;101]] [L4KSucc447 L4KZero447])
               [l4_pq_nat621;l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 c)) [b];
                l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_dec621 c)) [b]]) in
             l4_kr_bind491
               (l4_primitive_check_closed621 fuel env it
                 (l4_pq_arrow621 l4_pq_bool621
                   (l4_pq_arrow621 l4_pq_nat621 (l4_pq_arrow621 l4_pq_nat621 l4_pq_nat621))))
               (\ignored_ite_type.
             l4_kr_bind491
               (l4_primitive_eq_closed621 fuel env (l4_pq_app621 it l4_pq_tru621)
                 (l4_pq_lam621 l4_pq_nat621 (\a. l4_pq_lam621 l4_pq_nat621 (\ignored. a))))
               (\ignored_ite_true.
                 l4_primitive_eq_closed621 fuel env (l4_pq_app621 it l4_pq_fal621)
                   (l4_pq_lam621 l4_pq_nat621 (\ignored. l4_pq_lam621 l4_pq_nat621 (\a. a)))))
            else L4KAccept491 one)
           (\ignored_ite.
             if with_dite then L4KDecline491 L4KUnsupportedDeclaration491 else L4KAccept491 one))
       else
         let is_eq = c = L4PCNatEq621 in
         let op = if is_eq then L4KPNatBEq493 else L4KPNatBLE493 in
         l4_kr_bind491 (l4_primitive_authenticated619 fuel env op) (\ignored_authenticated.
           let r = l4_primitive_reflection_make621 is_eq in
           l4_kr_bind491 (l4_primitive_check_reflection621 fuel env r with_ite with_dite)
             (\ignored_reflection.
              let gadget = l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_lam621 l4_pq_nat621 (\y.
                l4_pq_apps621
                  (l4_pq_lam621 l4_pq_prop621 (\p. l4_pq_lam621 l4_pq_bool621 (\b.
                    l4_pq_lam621 (l4_pq_apps621 (l4_pq_embed621 (l4_reflection_type621 r)) [p;b])
                      (\h. l4_pq_apps621 (l4_pq_embed621 (l4_reflection_dec621 r)) [p;b;h]))))
                  [l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 c)) [x;y];
                   l4_pq_call621 op [x;y];
                   l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_proof621 c)) [x;y]])) in
              l4_primitive_eq_closed621 fuel env gadget (l4_pq_embed621 (l4_primitive_condition_dec621 c)))))`;;

let l4_primitive_go_name621 = new_definition
 `l4_primitive_go_name621 modulo =
    if modulo then l4_primitive_path621 [[78;97;116];[109;111;100;67;111;114;101];[103;111]]
    else l4_primitive_path621 [[78;97;116];[100;105;118];[103;111]]`;;
let l4_primitive_le621 = new_definition
 `l4_primitive_le621 x y =
    l4_pq_apps621 (l4_pq_embed621 (l4_primitive_condition_prop621 L4PCNatLE621)) [x;y]`;;
let l4_primitive_go_type621 = new_definition
 `l4_primitive_go_type621 = l4_pq_run621
    (l4_pq_pi621 l4_pq_nat621 (\y. l4_pq_arrow621 (l4_primitive_le621 l4_pq_one621 y)
      (l4_pq_pi621 l4_pq_nat621 (\fuel. l4_pq_pi621 l4_pq_nat621 (\x.
        l4_pq_arrow621 (l4_primitive_le621 (l4_pq_succ621 x) fuel) l4_pq_nat621)))))`;;
let l4_primitive_fuel_top621 = new_definition
 `l4_primitive_fuel_top621 modulo =
    let go = l4_pq_embed621 (L4KConst447 (l4_primitive_go_name621 modulo) []) in
    l4_pq_run621 (l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_lam621 l4_pq_nat621 (\y.
      let n = if modulo then l4_pq_succ621 x else x in
      let inner = l4_primitive_condition_dite621 L4PCNatLE621 [l4_pq_one621;y]
        (\hy. l4_pq_apps621 go [y;hy;l4_pq_succ621 n;n;
          l4_pq_app621 (l4_pq_const621
            [[78;97;116];[108;116;95;115;117;99;99;95;115;101;108;102]] []) n])
        (\ignored. if modulo then n else l4_pq_zero621) in
      if modulo then l4_primitive_condition_ite621 L4PCNatLE621 l4_pq_nat621 [y;n] inner n
      else inner)))`;;
let l4_primitive_fuel_step621 = new_definition
 `l4_primitive_fuel_step621 modulo rhs =
    let go = l4_pq_embed621 (L4KConst447 (l4_primitive_go_name621 modulo) []) in
    l4_pq_run621 (l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_lam621 l4_pq_nat621 (\y.
      l4_pq_lam621 (l4_primitive_le621 l4_pq_one621 y) (\hy. l4_pq_lam621 l4_pq_nat621 (\t.
        l4_pq_lam621 (l4_primitive_le621 (l4_pq_succ621 x) (l4_pq_succ621 t)) (\h.
          if rhs then l4_primitive_condition_dite621 L4PCNatLE621 [y;x]
            (\hle.
              let recursive = l4_pq_apps621 go [y;hy;t;l4_pq_call621 L4KPNatSub493 [x;y];
                l4_pq_apps621 (l4_pq_const621
                  [[78;97;116];[100;105;118;95;114;101;99;95;102;117;101;108;95;108;101;109;109;97]] [])
                  [x;y;t;hy;hle;h]] in
              if modulo then recursive else l4_pq_succ621 recursive)
            (\ignored. if modulo then x else l4_pq_zero621)
          else l4_pq_apps621 go [y;hy;l4_pq_succ621 t;x;h]))))))`;;

let l4_primitive_check_fuel_rec621 = new_definition
 `l4_primitive_check_fuel_rec621 fuel env modulo body =
    if ~(l4_core_nat_ready533 env /\ l4_core_bool_ready533 env)
    then L4KReject491 L4KMalformedDeclaration491 else
    l4_kr_bind491 (l4_primitive_authenticated619 fuel env L4KPNatSub493)
      (\ignored_authenticated.
    l4_kr_bind491
      (l4_primitive_check_closed621 fuel env (l4_pq_embed621 (l4_primitive_condition_prop621 L4PCNatLE621))
        (l4_pq_arrow621 l4_pq_nat621 (l4_pq_arrow621 l4_pq_nat621 l4_pq_prop621)))
      (\ignored_le.
    l4_kr_bind491
      (l4_check597 fuel env [] l4_kempty_context532
        (L4KConst447 (l4_primitive_go_name621 modulo) []) l4_primitive_go_type621)
      (\ignored_go.
    l4_kr_bind491 (l4_primitive_check_condition621 fuel env L4PCNatLE621 modulo T)
      (\ignored_condition.
    l4_kr_bind491
      (if modulo then l4_primitive_eq_closed621 fuel env
        (l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_apps621 (l4_pq_embed621 body) [l4_pq_zero621;x]))
        (l4_pq_lam621 l4_pq_nat621 (\ignored. l4_pq_zero621))
       else L4KAccept491 one)
      (\ignored_base.
    l4_kr_bind491
      (l4_primitive_eq_closed621 fuel env
        (l4_pq_lam621 l4_pq_nat621 (\x. l4_pq_lam621 l4_pq_nat621 (\y.
          l4_pq_apps621 (l4_pq_embed621 body) [(if modulo then l4_pq_succ621 x else x);y])))
        (l4_pq_embed621 (l4_primitive_fuel_top621 modulo)))
      (\ignored_top.
        l4_check_defeq597 fuel env [] l4_kempty_context532
          (l4_primitive_fuel_step621 modulo F) (l4_primitive_fuel_step621 modulo T)))))))`;;
