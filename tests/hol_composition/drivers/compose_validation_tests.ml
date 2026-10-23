needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
needs "hol/validation_tests.ml";;
if axioms()<>private_axioms then failwith "new axiom";;
if private_native_rule_count<>29 || private_admission_rule_count<>11 then failwith "wrong counts";;
print_endline "PRIVATE_COMPOSE_VALIDATION_DONE iterative_syntax rules29_11 unchanged_axioms";;
