let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/add_evaluation.ml";;
let expected_add_evaluation =
 `!env body.
    l4_scoped body 0 /\ l4_prim_add_contract (l4_edef env) body /\
    l4_edef env [] l4_prim_nat l4_prim_nat (L4Sort (L4Succ L4Zero)) /\
    l4_edef env [l4_prim_nat] l4_prim_nat l4_prim_nat (L4Sort (L4Succ L4Zero)) /\
    l4_edef env [] l4_prim_zero l4_prim_zero l4_prim_nat /\
    l4_edef env [] (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Const (L4String l4_nat_name [115;117;99;99]) []) l4_prim_unary ==>
    !m n. l4_edef env [] (L4App (L4App body (L4NatLit m)) (L4NatLit n))
      (L4NatLit (m+n)) l4_prim_nat`;;
let expected=REWRITE_CONV [l4_prim_nat;l4_prim_zero;l4_prim_unary] expected_add_evaluation;;
if not(aconv(concl l4_edef_add_evaluation) (rhs(concl expected))) then failwith "exact add theorem";;
if hyp l4_edef_add_evaluation<>[] || frees(concl l4_edef_add_evaluation)<>[] then failwith "open add theorem";;
if axioms()<>before_axioms then failwith "axiom change";;
if List.length(CONJUNCTS l4_edef_RULES)<>29 || List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))<>11 then failwith "rule change";;
print_endline "PRIVATE_NAT_EVALUATION_DONE 4_add_general_assertions unchanged_axioms";;
exit 0;;
