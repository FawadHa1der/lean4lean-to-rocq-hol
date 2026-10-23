let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/sub_context_evaluation.ml";;
let expected_sub_context =
 `!env g pred body.
    l4_scoped pred 0 /\ l4_scoped body 0 /\
    l4_prim_sub_contract (\delta. l4_edef env (APPEND delta g)) pred body /\
    l4_edef env g l4_prim_nat l4_prim_nat (L4Sort (L4Succ L4Zero)) /\
    l4_edef env (CONS l4_prim_nat g) l4_prim_nat l4_prim_nat (L4Sort (L4Succ L4Zero)) /\
    l4_edef env g l4_prim_zero l4_prim_zero l4_prim_nat /\
    l4_edef env g (L4Const (L4String l4_nat_name [115;117;99;99]) [])
      (L4Const (L4String l4_nat_name [115;117;99;99]) []) l4_prim_unary ==>
    !m n. l4_edef env g (L4App (L4App body (L4NatLit m)) (L4NatLit n))
      (L4NatLit (m-n)) l4_prim_nat`;;
let expected=REWRITE_CONV [l4_prim_nat;l4_prim_zero;l4_prim_unary] expected_sub_context;;
if not(aconv(concl l4_edef_sub_evaluation_in_context)(rhs(concl expected))) then failwith "exact contextual sub theorem";;
if List.exists(fun th->hyp th<>[] || frees(concl th)<>[])
  [l4_edef_sub_evaluation_in_context;l4_edef_sub_evaluation_context_empty] then failwith "open sub theorem";;
if axioms()<>before_axioms then failwith "axiom change";;
if List.length(CONJUNCTS l4_edef_RULES)<>29 || List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))<>11 then failwith "rule change";;
print_endline "COMPOSED_WORK_PASS sub-general 4";;
