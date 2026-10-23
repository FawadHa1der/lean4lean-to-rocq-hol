needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
needs "hol/string_literal_tests.ml";;
needs "hol/text_tests.ml";;
if axioms()<>private_axioms then failwith "axiom change";;
print_endline "PRIVATE_RAW_STRING_NATIVE_DONE literal_and_text unchanged_axioms";;
