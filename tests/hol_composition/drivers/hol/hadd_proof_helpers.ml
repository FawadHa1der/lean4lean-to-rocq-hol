needs "hol/raw_ctor_admission.ml";;
let hadd_invariants env blocks h =
  let args=[Lean4hol_env.quote_policy env;Lean4hol_env.quote_env env;
    Lean4hol_input_certificate.history blocks] in
  List.iter(fun rule -> let th=MP(SPECL args rule)h in
    if hyp th<>[] || frees(concl th)<>[] then failwith "open history invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];;
let hadd_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
