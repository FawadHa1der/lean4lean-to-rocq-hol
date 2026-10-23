let reflection_library_initial_axioms=axioms();;
needs "hol/reflection.ml";;
if axioms()<>reflection_library_initial_axioms then failwith "library added HOL axioms";;
if List.length(CONJUNCTS l4_edef_RULES)<>29 then failwith "expected exactly 29 native rules";;
if List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))<>11 then
  failwith "expected exactly 11 admission rules";;
List.iter (fun h -> if hyp h<>[] || frees(concl h)<>[] then failwith "open library theorem")
  [l4_defeq_instantiation;l4_edef_instantiation;l4_checked_instantiation;
   l4_r_embed_under_binder;l4_r_two_distinct_binders;l4_bool_condition_ite_implies_base];;
needs "tests/hol_reflection/boundary_tests.ml";;
if axioms()<>reflection_library_initial_axioms then failwith "boundary controls added HOL axioms";;
Printf.printf "\nREFLECTION_LIBRARY_READY native=29 admission=11\n%!";;
