(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Lean4Lean/Primitive.lean:33-177, pinned at
   8223d223ed98661882e95d9d6a7126df7097cd76.
   Construction only: these definitions add no typing or conversion rules. *)
needs "hol/core.ml";;

let l4_r_embed = new_definition `l4_r_embed e d = l4_lift e d 0`;;
let l4_r_app = new_definition `l4_r_app f a d = L4App (f d) (a d)`;;
let l4_r_lam = new_definition
 `l4_r_lam a b d = L4Lam L4Anonymous (a d)
    (b (\k. L4BVar (k - SUC d)) (SUC d))`;;
let l4_r_pi = new_definition
 `l4_r_pi a b d = L4Pi L4Anonymous (a d)
    (b (\k. L4BVar (k - SUC d)) (SUC d))`;;
let l4_r_arrow = new_definition `l4_r_arrow a b = l4_r_pi a (\x. b)`;;
let l4_r_run = new_definition `l4_r_run e = e 0`;;
let l4_r_apps = new_definition
 `l4_r_apps f xs d = ITLIST (\a g. L4App g (a d)) (REVERSE xs) (f d)`;;

(* Fixed structured names, defined by equality to their quoted AST. This
   avoids a second host implementation of binding-sensitive templates. *)
let l4_r_atoms =
  let open Lean4hol in
  let atom id e = new_definition(mk_eq(mk_var("l4_r_"^id,`:num->l4_expr`),
    node "l4_r_embed" [quote_expr e])) in
  let const id parts us = atom id (Const(List.fold_left (fun n s -> Str(n,s)) Anonymous parts,us)) in
  [atom "prop" (Sort Zero); atom "type" (Sort(Succ Zero));
   const "nat" ["Nat"] []; const "bool" ["Bool"] [];
   const "true" ["Bool";"true"] []; const "false" ["Bool";"false"] [];
   const "eq" ["Eq"] [Succ Zero]; const "refl" ["Eq";"refl"] [Succ Zero];
   const "not" ["Not"] []; const "empty" ["False"] [];
   const "dec" ["Decidable"] [];
   const "yes" ["Decidable";"isTrue"] []; const "no" ["Decidable";"isFalse"] [];
   const "ite" ["ite"] [Succ Zero]; const "dite" ["dite"] [Succ Zero];
   const "bool_dec" ["Bool";"decEq"] [];
   const "bool_cases" ["Bool";"casesOn"] [Succ Zero];
   const "no_confusion" ["Bool";"noConfusion"] [Zero];
   const "le" ["LE";"le"] [Zero]; const "inst_le" ["instLENat"] [];
   const "ble" ["Nat";"ble"] []; const "beq" ["Nat";"beq"] [];
   const "dec_le" ["Nat";"decLe"] []; const "dec_eq" ["Nat";"decEq"] [];
   const "le_true" ["Nat";"le_of_ble_eq_true"] [];
   const "le_false" ["Nat";"not_le_of_not_ble_eq_true"] [];
   const "eq_true" ["Nat";"eq_of_beq_eq_true"] [];
   const "eq_false" ["Nat";"ne_of_beq_eq_false"] []];;

let l4_r_equal = new_definition
 `l4_r_equal b c = l4_r_apps l4_r_eq [l4_r_bool;b;c]`;;
let l4_r_negative = new_definition
 `l4_r_negative second b = if second then l4_r_equal b l4_r_false
    else l4_r_app l4_r_not (l4_r_equal b l4_r_true)`;;
let l4_reflection_type = new_definition
 `l4_reflection_type second = l4_r_run
   (l4_r_lam l4_r_prop (\p. l4_r_lam l4_r_bool (\b.
    l4_r_pi l4_r_prop (\q. l4_r_arrow
     (l4_r_arrow (l4_r_arrow (l4_r_equal b l4_r_true) p)
       (l4_r_arrow (l4_r_arrow (l4_r_negative second b) (l4_r_app l4_r_not p)) q)) q))))`;;
let l4_r_relation = new_definition
 `l4_r_relation rt p b = l4_r_apps (l4_r_embed rt) [p;b]`;;
let l4_reflection_true = new_definition
 `l4_reflection_true second = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_relation (l4_reflection_type second) p l4_r_true) (\h.
     l4_r_apps h [p;
      l4_r_lam (l4_r_arrow (l4_r_equal l4_r_true l4_r_true) p) (\hp.
       l4_r_lam (l4_r_arrow (l4_r_negative second l4_r_true) (l4_r_app l4_r_not p))
        (\hn. l4_r_app hp (l4_r_apps l4_r_refl [l4_r_bool;l4_r_true])))])))`;;
let l4_reflection_false = new_definition
 `l4_reflection_false second = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_relation (l4_reflection_type second) p l4_r_false) (\h.
     l4_r_apps h [l4_r_app l4_r_not p;
      l4_r_lam (l4_r_arrow (l4_r_equal l4_r_false l4_r_true) p) (\hp.
       l4_r_lam (l4_r_arrow (l4_r_negative second l4_r_false) (l4_r_app l4_r_not p))
        (\hn. l4_r_app hn (if second then
          l4_r_apps l4_r_refl [l4_r_bool;l4_r_false] else
          l4_r_lam (l4_r_equal l4_r_false l4_r_true) (\bad.
            l4_r_apps l4_r_no_confusion [l4_r_empty;l4_r_false;l4_r_true;bad]))))])))`;;
let l4_r_positive_proof = new_definition
 `l4_r_positive_proof second p b h hp = l4_r_apps h [p;
   l4_r_lam (l4_r_arrow (l4_r_equal b l4_r_true) p) (\yes.
    l4_r_lam (l4_r_arrow (l4_r_negative second b) (l4_r_app l4_r_not p))
     (\no. l4_r_app yes hp))]`;;
let l4_r_negative_proof = new_definition
 `l4_r_negative_proof second p b h hn = l4_r_apps h [l4_r_app l4_r_not p;
   l4_r_lam (l4_r_arrow (l4_r_equal b l4_r_true) p) (\yes.
    l4_r_lam (l4_r_arrow (l4_r_negative second b) (l4_r_app l4_r_not p))
     (\no. l4_r_app no hn))]`;;
let l4_reflection_dec = new_definition
 `l4_reflection_dec second = l4_r_run
   (l4_r_lam l4_r_prop (\p. l4_r_lam l4_r_bool (\b.
    l4_r_lam (l4_r_relation (l4_reflection_type second) p b) (\h.
     if second then l4_r_app
       (l4_r_apps l4_r_bool_cases
        [l4_r_lam l4_r_bool (\bb. l4_r_arrow (l4_r_equal b bb) (l4_r_app l4_r_dec p));b;
         l4_r_lam (l4_r_equal b l4_r_false) (\hn. l4_r_apps l4_r_no
           [p;l4_r_negative_proof second p b h hn]);
         l4_r_lam (l4_r_equal b l4_r_true) (\hp. l4_r_apps l4_r_yes
           [p;l4_r_positive_proof second p b h hp])])
       (l4_r_apps l4_r_refl [l4_r_bool;b])
     else l4_r_apps l4_r_dite
       [l4_r_app l4_r_dec p;l4_r_equal b l4_r_true;
        l4_r_apps l4_r_bool_dec [b;l4_r_true];
        l4_r_lam (l4_r_equal b l4_r_true) (\hp. l4_r_apps l4_r_yes
           [p;l4_r_positive_proof second p b h hp]);
        l4_r_lam (l4_r_negative second b) (\hn. l4_r_apps l4_r_no
           [p;l4_r_negative_proof second p b h hn])]))))`;;

let l4_reflection_ite = new_definition
 `l4_reflection_ite rt rd = l4_r_run (l4_r_lam l4_r_prop (\p.
   l4_r_lam l4_r_bool (\b. l4_r_lam (l4_r_relation rt p b) (\h.
    l4_r_lam l4_r_type (\a. l4_r_apps l4_r_ite
     [a;p;l4_r_apps (l4_r_embed rd) [p;b;h]])))))`;;
let l4_reflection_dite = new_definition
 `l4_reflection_dite rt rd = l4_r_run (l4_r_lam l4_r_prop (\p.
   l4_r_lam l4_r_bool (\b. l4_r_lam (l4_r_relation rt p b) (\h.
    l4_r_apps l4_r_dite [l4_r_nat;p;l4_r_apps (l4_r_embed rd) [p;b;h]]))))`;;
let l4_reflected_nat_gadget = new_definition
 `l4_reflected_nat_gadget rt rd cp cb ch = l4_r_run
   (l4_r_lam l4_r_nat (\x. l4_r_lam l4_r_nat (\y.
     l4_r_apps
      (l4_r_lam l4_r_prop (\p. l4_r_lam l4_r_bool (\b.
       l4_r_lam (l4_r_relation rt p b) (\h.
        l4_r_apps (l4_r_embed rd) [p;b;h]))))
      [l4_r_apps (l4_r_embed cp) [x;y];l4_r_apps (l4_r_embed cb) [x;y];
       l4_r_apps (l4_r_embed ch) [x;y]])))`;;

let l4_condition_bool_prop = new_definition
 `l4_condition_bool_prop = l4_r_run (l4_r_lam l4_r_bool
   (\b. l4_r_equal b l4_r_true))`;;
let l4_condition_bool_dec = new_definition
 `l4_condition_bool_dec = l4_r_run (l4_r_lam l4_r_bool
   (\b. l4_r_apps l4_r_bool_dec [b;l4_r_true]))`;;
let l4_condition_nat_prop = new_definition
 `l4_condition_nat_prop second = l4_r_run (if second then
    l4_r_app l4_r_eq l4_r_nat else l4_r_apps l4_r_le [l4_r_nat;l4_r_inst_le])`;;
let l4_condition_nat_dec = new_definition
 `l4_condition_nat_dec second = l4_r_run (if second then l4_r_dec_eq else l4_r_dec_le)`;;
let l4_condition_nat_bool = new_definition
 `l4_condition_nat_bool second = l4_r_run (if second then l4_r_beq else l4_r_ble)`;;
let l4_condition_nat_proof = new_definition
 `l4_condition_nat_proof second = l4_r_run (l4_r_lam l4_r_nat (\x.
   l4_r_lam l4_r_nat (\y.
    l4_r_lam l4_r_prop (\q.
     l4_r_lam
      (l4_r_arrow
       (l4_r_arrow (l4_r_equal (l4_r_apps (l4_r_embed (l4_condition_nat_bool second)) [x;y]) l4_r_true)
         (l4_r_apps (l4_r_embed (l4_condition_nat_prop second)) [x;y]))
       (l4_r_arrow
        (l4_r_arrow (l4_r_negative second (l4_r_apps (l4_r_embed (l4_condition_nat_bool second)) [x;y]))
          (l4_r_app l4_r_not (l4_r_apps (l4_r_embed (l4_condition_nat_prop second)) [x;y]))) q))
      (\h. l4_r_apps h
       [l4_r_apps (if second then l4_r_eq_true else l4_r_le_true) [x;y];
        l4_r_apps (if second then l4_r_eq_false else l4_r_le_false) [x;y]])))))`;;

(* General capture-avoidance equations, not just closed-template samples. *)
let l4_r_embed_under_binder = prove
 (`!a e. l4_r_run (l4_r_lam (l4_r_embed a) (\x. l4_r_embed e)) =
    L4Lam L4Anonymous (l4_lift a 0 0) (l4_lift e 1 0)`,
  REWRITE_TAC [l4_r_run;l4_r_lam;l4_r_embed;ONE]);;
let l4_r_two_distinct_binders = prove
 (`!a. l4_r_run (l4_r_lam (l4_r_embed a) (\x.
       l4_r_lam (l4_r_embed a) (\y. l4_r_app x y))) =
    L4Lam L4Anonymous (l4_lift a 0 0)
      (L4Lam L4Anonymous (l4_lift a 1 0) (L4App (L4BVar 1) (L4BVar 0)))`,
  REWRITE_TAC [l4_r_run;l4_r_lam;l4_r_embed;l4_r_app] THEN CONV_TAC NUM_REDUCE_CONV);;

let l4_reflection_syntax_equations =
 [l4_r_embed;l4_r_app;l4_r_lam;l4_r_pi;l4_r_arrow;l4_r_run;l4_r_apps;
  l4_r_equal;l4_r_negative;l4_reflection_type;l4_r_relation;l4_reflection_true;
  l4_reflection_false;l4_r_positive_proof;l4_r_negative_proof;l4_reflection_dec;
  l4_reflection_ite;l4_reflection_dite;l4_reflected_nat_gadget;
  l4_condition_bool_prop;l4_condition_bool_dec;l4_condition_nat_prop;
  l4_condition_nat_dec;l4_condition_nat_bool;l4_condition_nat_proof] @ l4_r_atoms;;
