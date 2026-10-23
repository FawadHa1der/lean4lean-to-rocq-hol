(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Canonical syntax from pinned Lean4Lean/Quot.lean. This file adds no
   typing, admission or computation rule for quotient constants. *)
needs "hol/inductive_syntax.ml";;

let l4_quot_kind_INDUCT,l4_quot_kind_RECURSION = define_type
 "l4_quot_kind = L4QuotType | L4QuotCtor | L4QuotLift | L4QuotInd";;
let l4_quot_base = new_definition
 `l4_quot_base = L4String L4Anonymous [81;117;111;116]`;;
let l4_quot_eq = new_definition
 `l4_quot_eq = L4String L4Anonymous [69;113]`;;
let l4_quot_name = new_recursive_definition l4_quot_kind_RECURSION
 `(l4_quot_name L4QuotType = l4_quot_base) /\
  (l4_quot_name L4QuotCtor = L4String l4_quot_base [109;107]) /\
  (l4_quot_name L4QuotLift = L4String l4_quot_base [108;105;102;116]) /\
  (l4_quot_name L4QuotInd = L4String l4_quot_base [105;110;100])`;;
let l4_quot_arity = new_recursive_definition l4_quot_kind_RECURSION
 `(l4_quot_arity L4QuotType = 1) /\
  (l4_quot_arity L4QuotCtor = 1) /\
  (l4_quot_arity L4QuotLift = 2) /\
  (l4_quot_arity L4QuotInd = 1)`;;
let l4_quot_pi = new_definition
 `l4_quot_pi a b = L4Pi L4Anonymous a b`;;
let l4_quot_arrow = new_definition
 `l4_quot_arrow a b = l4_quot_pi a (l4_lift b 1 0)`;;
let l4_quot_relation = new_definition
 `l4_quot_relation a = l4_quot_arrow a (l4_quot_arrow a (L4Sort L4Zero))`;;
let l4_quot_app = new_definition
 `l4_quot_app k u args = l4_apps (L4Const (l4_quot_name k) [u]) args`;;
let l4_quot_eq_type = new_definition
 `l4_quot_eq_type u = l4_quot_pi (L4Sort u) (l4_quot_relation (L4BVar 0))`;;
let l4_quot_refl_type = new_definition
 `l4_quot_refl_type u = l4_quot_pi (L4Sort u)
    (l4_quot_pi (L4BVar 0)
      (l4_apps (L4Const l4_quot_eq [u]) [L4BVar 1;L4BVar 0;L4BVar 0]))`;;

let l4_quot_signature = new_recursive_definition l4_quot_kind_RECURSION
 `(l4_quot_signature L4QuotType u v =
    l4_quot_pi (L4Sort u)
      (l4_quot_pi (l4_quot_relation (L4BVar 0)) (L4Sort u))) /\
  (l4_quot_signature L4QuotCtor u v =
    l4_quot_pi (L4Sort u)
      (l4_quot_pi (l4_quot_relation (L4BVar 0))
        (l4_quot_pi (L4BVar 1)
          (l4_quot_app L4QuotType u [L4BVar 2;L4BVar 1])))) /\
  (l4_quot_signature L4QuotLift u v =
    l4_quot_pi (L4Sort u)
      (l4_quot_pi (l4_quot_relation (L4BVar 0))
        (l4_quot_pi (L4Sort v)
          (l4_quot_pi (l4_quot_arrow (L4BVar 2) (L4BVar 0))
            (l4_quot_arrow
              (l4_quot_pi (L4BVar 3)
                (l4_quot_pi (L4BVar 4)
                  (l4_quot_arrow
                    (l4_apps (L4BVar 4) [L4BVar 1;L4BVar 0])
                    (l4_apps (L4Const l4_quot_eq [v])
                      [L4BVar 3;L4App (L4BVar 2) (L4BVar 1);
                       L4App (L4BVar 2) (L4BVar 0)]))))
              (l4_quot_arrow
                (l4_quot_app L4QuotType u [L4BVar 3;L4BVar 2]) (L4BVar 1))))))) /\
  (l4_quot_signature L4QuotInd u v =
    l4_quot_pi (L4Sort u)
      (l4_quot_pi (l4_quot_relation (L4BVar 0))
        (l4_quot_pi
          (l4_quot_arrow (l4_quot_app L4QuotType u [L4BVar 1;L4BVar 0]) (L4Sort L4Zero))
          (l4_quot_arrow
            (l4_quot_pi (L4BVar 2)
              (L4App (L4BVar 1)
                (l4_quot_app L4QuotCtor u [L4BVar 3;L4BVar 2;L4BVar 0])))
            (l4_quot_pi (l4_quot_app L4QuotType u [L4BVar 2;L4BVar 1])
              (L4App (L4BVar 1) (L4BVar 0)))))))`;;

let l4_quot_signature_unused_level = prove
 (`!k u v w. ~(k = L4QuotLift) ==>
     l4_quot_signature k u v = l4_quot_signature k u w`,
  MATCH_MP_TAC l4_quot_kind_INDUCT THEN
  REWRITE_TAC [l4_quot_signature;distinctness "l4_quot_kind"]);;
