(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Proof-bearing capability statements for Primitive.lean at
   8223d223ed98661882e95d9d6a7126df7097cd76.
   Closed lambda probes quantify over arbitrary branches, never Nat samples. *)
needs "hol/reflection_syntax.ml";;

let l4_reflection_type_type = new_definition
 `l4_reflection_type_type = l4_r_run
   (l4_r_arrow l4_r_prop (l4_r_arrow l4_r_bool l4_r_prop))`;;
let l4_reflection_selector_type = new_definition
 `l4_reflection_selector_type = l4_r_run
   (l4_r_pi l4_r_type (\a. l4_r_arrow a (l4_r_arrow a a)))`;;
let l4_reflection_ite_type = new_definition
 `l4_reflection_ite_type rt = l4_r_run
   (l4_r_pi l4_r_prop (\p. l4_r_pi l4_r_bool (\b.
    l4_r_arrow (l4_r_relation rt p b) (l4_r_embed l4_reflection_selector_type))))`;;
let l4_reflection_ite_probe = new_definition
 `l4_reflection_ite_probe rt rd positive = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_relation rt p (if positive then l4_r_true else l4_r_false)) (\h.
     l4_r_apps (l4_r_embed (l4_reflection_ite rt rd))
      [p;(if positive then l4_r_true else l4_r_false);h])))`;;
let l4_reflection_ite_expected = new_definition
 `l4_reflection_ite_expected rt positive = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_relation rt p (if positive then l4_r_true else l4_r_false)) (\h.
     l4_r_lam l4_r_type (\a. l4_r_lam a (\x. l4_r_lam a (\y.
      if positive then x else y))))))`;;
let l4_reflection_ite_probe_type = new_definition
 `l4_reflection_ite_probe_type rt positive = l4_r_run
   (l4_r_pi l4_r_prop (\p.
    l4_r_arrow (l4_r_relation rt p (if positive then l4_r_true else l4_r_false))
      (l4_r_embed l4_reflection_selector_type)))`;;
let l4_reflection_of_type = new_definition
 `l4_reflection_of_type rt positive = l4_r_run
   (l4_r_pi l4_r_prop (\p.
    l4_r_arrow (l4_r_relation rt p (if positive then l4_r_true else l4_r_false))
      (if positive then p else l4_r_app l4_r_not p)))`;;
let l4_reflection_dite_type = new_definition
 `l4_reflection_dite_type rt = l4_r_run
   (l4_r_pi l4_r_prop (\p. l4_r_pi l4_r_bool (\b.
    l4_r_arrow (l4_r_relation rt p b)
     (l4_r_arrow (l4_r_arrow p l4_r_nat)
      (l4_r_arrow (l4_r_arrow (l4_r_app l4_r_not p) l4_r_nat) l4_r_nat)))))`;;
let l4_reflection_dite_probe = new_definition
 `l4_reflection_dite_probe rt rd positive = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_arrow p l4_r_nat) (\yes.
     l4_r_lam (l4_r_arrow (l4_r_app l4_r_not p) l4_r_nat) (\no.
      l4_r_lam (l4_r_relation rt p (if positive then l4_r_true else l4_r_false)) (\h.
       l4_r_apps (l4_r_embed (l4_reflection_dite rt rd))
        [p;(if positive then l4_r_true else l4_r_false);h;yes;no])))))`;;
let l4_reflection_dite_expected = new_definition
 `l4_reflection_dite_expected rt rf positive = l4_r_run
   (l4_r_lam l4_r_prop (\p.
    l4_r_lam (l4_r_arrow p l4_r_nat) (\yes.
     l4_r_lam (l4_r_arrow (l4_r_app l4_r_not p) l4_r_nat) (\no.
      l4_r_lam (l4_r_relation rt p (if positive then l4_r_true else l4_r_false)) (\h.
       l4_r_app (if positive then yes else no)
        (l4_r_apps (l4_r_embed rf) [p;h]))))))`;;
let l4_reflection_dite_probe_type = new_definition
 `l4_reflection_dite_probe_type rt positive = l4_r_run
   (l4_r_pi l4_r_prop (\p.
    l4_r_arrow (l4_r_arrow p l4_r_nat)
     (l4_r_arrow (l4_r_arrow (l4_r_app l4_r_not p) l4_r_nat)
      (l4_r_arrow (l4_r_relation rt p (if positive then l4_r_true else l4_r_false)) l4_r_nat))))`;;

let l4_reflection_type_contract = new_definition
 `l4_reflection_type_contract J rt <=>
    J ([]:l4_expr list) (rt:l4_expr) rt l4_reflection_type_type`;;
let l4_reflection_ite_contract = new_definition
 `l4_reflection_ite_contract J rt rd <=>
    l4_reflection_type_contract J rt /\
    J ([]:l4_expr list) (l4_reflection_ite rt rd) (l4_reflection_ite rt rd)
      (l4_reflection_ite_type rt) /\
    J [] (l4_reflection_ite_probe rt rd T) (l4_reflection_ite_expected rt T)
      (l4_reflection_ite_probe_type rt T) /\
    J [] (l4_reflection_ite_probe rt rd F) (l4_reflection_ite_expected rt F)
      (l4_reflection_ite_probe_type rt F)`;;
let l4_reflection_dite_contract = new_definition
 `l4_reflection_dite_contract J rt ry rn rd <=>
    l4_reflection_type_contract J rt /\
    J ([]:l4_expr list) (l4_r_run l4_r_not) (l4_r_run l4_r_not)
      (l4_r_run (l4_r_arrow l4_r_prop l4_r_prop)) /\
    J [] (l4_reflection_dite rt rd) (l4_reflection_dite rt rd)
      (l4_reflection_dite_type rt) /\
    J [] ry ry (l4_reflection_of_type rt T) /\
    J [] rn rn (l4_reflection_of_type rt F) /\
    J [] (l4_reflection_dite_probe rt rd T) (l4_reflection_dite_expected rt ry T)
      (l4_reflection_dite_probe_type rt T) /\
    J [] (l4_reflection_dite_probe rt rd F) (l4_reflection_dite_expected rt rn F)
      (l4_reflection_dite_probe_type rt F)`;;
let l4_reflected_nat_contract = new_definition
 `l4_reflected_nat_contract J rt rd cp cb ch cd dt gt <=>
    J ([]:l4_expr list) cd cd dt /\
    l4_reflection_type_contract J rt /\
    J [] (l4_reflected_nat_gadget rt rd cp cb ch)
      (l4_reflected_nat_gadget rt rd cp cb ch) gt /\
    J [] (l4_reflected_nat_gadget rt rd cp cb ch) cd gt`;;

let l4_reflection_type_mono = prove
 (`!J K rt. (!g e e' a. J g e e' a ==> K g e e' a) ==>
   l4_reflection_type_contract J rt ==> l4_reflection_type_contract K rt`,
  REWRITE_TAC [l4_reflection_type_contract] THEN MESON_TAC []);;
let l4_reflection_ite_mono = prove
 (`!J K rt rd. (!g e e' a. J g e e' a ==> K g e e' a) ==>
   l4_reflection_ite_contract J rt rd ==> l4_reflection_ite_contract K rt rd`,
  REWRITE_TAC [l4_reflection_ite_contract;l4_reflection_type_contract] THEN MESON_TAC []);;
let l4_reflection_dite_mono = prove
 (`!J K rt ry rn rd. (!g e e' a. J g e e' a ==> K g e e' a) ==>
   l4_reflection_dite_contract J rt ry rn rd ==> l4_reflection_dite_contract K rt ry rn rd`,
  REWRITE_TAC [l4_reflection_dite_contract;l4_reflection_type_contract] THEN MESON_TAC []);;
let l4_reflected_nat_mono = prove
 (`!J K rt rd cp cb ch cd dt gt. (!g e e' a. J g e e' a ==> K g e e' a) ==>
   l4_reflected_nat_contract J rt rd cp cb ch cd dt gt ==>
   l4_reflected_nat_contract K rt rd cp cb ch cd dt gt`,
  REWRITE_TAC [l4_reflected_nat_contract;l4_reflection_type_contract] THEN MESON_TAC []);;
let l4_reflected_nat_dec_equation = prove
 (`!J rt rd cp cb ch cd dt gt. l4_reflected_nat_contract J rt rd cp cb ch cd dt gt ==>
    J [] (l4_reflected_nat_gadget rt rd cp cb ch) cd gt`,
  SIMP_TAC [l4_reflected_nat_contract]);;
let l4_reflected_nat_gadget_typed = prove
 (`!J rt rd cp cb ch cd dt gt. l4_reflected_nat_contract J rt rd cp cb ch cd dt gt ==>
    J [] (l4_reflected_nat_gadget rt rd cp cb ch)
      (l4_reflected_nat_gadget rt rd cp cb ch) gt`,
  SIMP_TAC [l4_reflected_nat_contract]);;

let l4_reflection_ite_branches = prove
 (`!J rt rd positive. l4_reflection_ite_contract J rt rd ==>
    J [] (l4_reflection_ite_probe rt rd positive)
      (l4_reflection_ite_expected rt positive)
      (l4_reflection_ite_probe_type rt positive)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `positive:bool` THEN
  SIMP_TAC [l4_reflection_ite_contract]);;
let l4_reflection_dite_true = prove
 (`!J rt ry rn rd. l4_reflection_dite_contract J rt ry rn rd ==>
    J [] (l4_reflection_dite_probe rt rd T) (l4_reflection_dite_expected rt ry T)
      (l4_reflection_dite_probe_type rt T)`,
  SIMP_TAC [l4_reflection_dite_contract]);;
let l4_reflection_dite_false = prove
 (`!J rt ry rn rd. l4_reflection_dite_contract J rt ry rn rd ==>
    J [] (l4_reflection_dite_probe rt rd F) (l4_reflection_dite_expected rt rn F)
      (l4_reflection_dite_probe_type rt F)`,
  SIMP_TAC [l4_reflection_dite_contract]);;

let l4_reflection_contract_equations =
 [l4_reflection_type_type;l4_reflection_selector_type;l4_reflection_ite_type;
  l4_reflection_ite_probe;l4_reflection_ite_expected;l4_reflection_ite_probe_type;
  l4_reflection_of_type;l4_reflection_dite_type;l4_reflection_dite_probe;
  l4_reflection_dite_expected;l4_reflection_dite_probe_type;
  l4_reflection_type_contract;l4_reflection_ite_contract;l4_reflection_dite_contract;
  l4_reflected_nat_contract];;
