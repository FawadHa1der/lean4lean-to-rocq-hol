needs "hol/private_boot.ml";;
needs "hol/mindex_boundary_tests.ml";;
needs "hol/mutual_boundary_tests.ml";;
if private_native_rule_count<>29 || private_admission_rule_count<>11 ||
   List.length(CONJUNCTS l4_input_trace_RULES)<>3 || axioms()<>private_axioms then
  failwith "boundary count or axiom change";;
print_endline "PRIVATE_BOUNDARY_DONE prefixes28_10_and27_9 totals29_11 trace3 unchanged_axioms";;
