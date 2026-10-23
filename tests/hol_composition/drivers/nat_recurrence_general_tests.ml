let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/nat_evaluation.ml";;
let expected_nat_recurrence =
 `!env g f m.
    l4_edef env g f f l4_prim_unary /\
    l4_edef env g (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Const (L4String l4_nat_name [115;117;99;99]) []) l4_prim_unary /\
    l4_edef env g (L4App f (L4NatLit 0)) (L4NatLit m) l4_prim_nat /\
    (!n. l4_edef env g (L4App f (l4_prim_succ (L4NatLit n)))
      (l4_prim_succ (L4App f (L4NatLit n))) l4_prim_nat) ==>
    !n. l4_edef env g (L4App f (L4NatLit n)) (L4NatLit (m+n)) l4_prim_nat`;;
let expected=(REWRITE_CONV [l4_prim_unary;l4_prim_nat;l4_prim_succ]) expected_nat_recurrence;;
if not(aconv(concl l4_edef_nat_recurrence) (rhs(concl expected))) then failwith "exact recurrence conclusion";;
if hyp l4_edef_nat_recurrence<>[] || frees(concl l4_edef_nat_recurrence)<>[] then failwith "recurrence not closed";;
if axioms()<>before_axioms then failwith "axiom change";;
if List.length(CONJUNCTS l4_edef_RULES)<>29 || List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))<>11 then failwith "rule change";;
print_endline "PRIVATE_NAT_EVALUATION_DONE 4_general_assertions unchanged_axioms";;
exit 0;;
