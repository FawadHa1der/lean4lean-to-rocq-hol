(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Typed rules adapted from Lean4Lean/Theory/Typing/Basic.lean. *)
needs "hol/syntax.ml";;

let l4_defeq_RULES,l4_defeq_INDUCT,l4_defeq_CASES = new_inductive_definition
 `(!g i. i < LENGTH g ==>
     l4_defeq g (L4BVar i) (L4BVar i) (l4_lift (EL i g) (SUC i) 0)) /\
  (!g u v. l4_level_equiv u v ==>
     l4_defeq g (L4Sort u) (L4Sort v) (L4Sort (L4Succ u))) /\
  (!g f f' a a' n d b.
     l4_defeq g f f' (L4Pi n d b) /\ l4_defeq g a a' d ==>
     l4_defeq g (L4App f a) (L4App f' a') (l4_inst a b)) /\
  (!g n n' a a' b b' t u.
     l4_defeq g a a' (L4Sort u) /\ l4_defeq (CONS a g) b b' t ==>
     l4_defeq g (L4Lam n a b) (L4Lam n' a' b') (L4Pi n a t)) /\
  (!g n n' a a' b b' u v.
     l4_defeq g a a' (L4Sort u) /\ l4_defeq (CONS a g) b b' (L4Sort v) ==>
     l4_defeq g (L4Pi n a b) (L4Pi n' a' b') (L4Sort (L4IMax u v))) /\
  (!g a b e e' u.
     l4_defeq g a b (L4Sort u) /\ l4_defeq g e e' a ==>
     l4_defeq g e e' b) /\
  (!g e e' a. l4_defeq g e e' a ==> l4_defeq g e' e a) /\
  (!g e e' e'' a.
     l4_defeq g e e' a /\ l4_defeq g e' e'' a ==> l4_defeq g e e'' a) /\
  (!g n a b t v.
     l4_defeq (CONS a g) b b t /\ l4_defeq g v v a ==>
     l4_defeq g (L4App (L4Lam n a b) v) (l4_inst v b) (l4_inst v t)) /\
  (!g n a b e.
     l4_defeq g e e (L4Pi n a b) ==>
     l4_defeq g (L4Lam n a (L4App (l4_lift e 1 0) (L4BVar 0))) e
       (L4Pi n a b)) /\
  (!g p h h'.
     l4_defeq g p p (L4Sort L4Zero) /\ l4_defeq g h h p /\ l4_defeq g h' h' p ==>
     l4_defeq g h h' p) /\
  (!g n a v b t u.
     l4_defeq g a a (L4Sort u) /\ l4_defeq g v v a /\
     l4_defeq (CONS a g) b b t ==>
     l4_defeq g (L4Let n a v b) (L4Let n a v b) (l4_inst v t)) /\
  (!g n a v b t u.
     l4_defeq g a a (L4Sort u) /\ l4_defeq g v v a /\
     l4_defeq (CONS a g) b b t ==>
     l4_defeq g (L4Let n a v b) (l4_inst v b) (l4_inst v t))`;;

let l4_has_type = new_definition
 `l4_has_type g e a <=> l4_defeq g e e a`;;

let l4_context_RULES,l4_context_INDUCT,l4_context_CASES = new_inductive_definition
 `(l4_context []) /\
  (!g a u. l4_context g /\ l4_defeq g a a (L4Sort u) ==>
           l4_context (CONS a g))`;;
