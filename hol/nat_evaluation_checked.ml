(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/nat_evaluation.ml";;

let l4_checked_nat_recurrence = prove
 (`!policy env g f m.
    l4_checked policy env g f f l4_prim_unary /\
    l4_checked policy env g (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Const (L4String l4_nat_name [115;117;99;99]) []) l4_prim_unary /\
    l4_checked policy env g (L4App f (L4NatLit 0)) (L4NatLit m) l4_prim_nat /\
    (!n. l4_checked policy env g (L4App f (l4_prim_succ (L4NatLit n)))
      (l4_prim_succ (L4App f (L4NatLit n))) l4_prim_nat) ==>
    !n. l4_checked policy env g (L4App f (L4NatLit n))
      (L4NatLit (m+n)) l4_prim_nat`,
  REWRITE_TAC [l4_checked;l4_prim_unary;l4_prim_nat;l4_prim_succ] THEN
  MESON_TAC [l4_edef_nat_recurrence]);;
