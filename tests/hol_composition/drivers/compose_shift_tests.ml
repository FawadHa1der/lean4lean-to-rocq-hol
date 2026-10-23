needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let compose_policy_invariants args final =
  List.iter(fun theorem->let h=MP(SPECL args theorem)final in
    if hyp h<>[] || frees(concl h)<>[] then failwith "open policy invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];;
unset_jrh_lexer;;
let compose_shift_group = try Sys.getenv "COMPOSE_GROUP" with Not_found -> "all";;
let () = if compose_shift_group="all" || compose_shift_group="admission-gate" then
  needs "fixtures/compose_policy_resume_tests.ml";;
needs "frontend/hol_check.ml";;
let () =
  let cases=["admission-gate",0;"compute-one",0;"wrong-result",2] in
  let selected=if compose_shift_group="all" then cases else
    List.filter(fun(label,_)->label=compose_shift_group)cases in
  if selected=[] then failwith "unknown shift case";
  List.iter(fun(label,expected)->
    let code,message,cert=Hol_check.check_file_with_certificate("fixtures/shift/"^label^".ndjson") in
    Printf.printf "COMPOSE_SHIFT %s code=%d %s\n%!" label code message;
    if code<>expected then failwith "unexpected shiftLeft verdict";
    match code,cert with
    | 0,Some c ->
      ignore(Lean4hol_raw_ctor.exact
        (Lean4hol_input_certificate.expected c.Hol_check.environment c.Hol_check.raw_history)
        c.Hol_check.theorem);
      if frees(concl c.Hol_check.theorem)<>[] then failwith "free shift certificate variables"
    | 2,None -> ()
    | _ -> failwith "shift certificate mismatch")
    selected;
  if axioms()<>private_axioms then failwith "axiom change";
  if compose_shift_group="all" then
    print_endline "PRIVATE_COMPOSE_SHIFT_DONE two_positive_gates wrong_result_declines exact_certificates unchanged_axioms"
  else Printf.printf "PRIVATE_COMPOSE_SHIFT_CASE_DONE %s expected_verdict exact_certificate_if_accepted unchanged_axioms\n%!"
    compose_shift_group;;
