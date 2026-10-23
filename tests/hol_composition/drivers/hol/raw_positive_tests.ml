needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let private_invariant policy env blocks h th = MP(SPECL [policy;env;blocks] th)h;;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let code,message,cert=Hol_check.check_file_with_certificate
    "arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson" in
  print_endline(Printf.sprintf "RAW055 code=%d %s" code message);
  let c=match code,cert with 0,Some c->c | _->failwith "authentic055 declined" in
  let expected=Lean4hol_input_certificate.expected c.Hol_check.environment c.Hol_check.raw_history in
  if hyp c.Hol_check.theorem<>[] || not(aconv(concl c.Hol_check.theorem)expected) then
    failwith "inexact raw input theorem";
  let raw=List.find_map(fun(_,d)->match d with
    | Hol_input.Inductive cs->Some(List.map Hol_check.claim cs) | _->None)
    (Hol_input.read_file "arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson") in
  if Some(List.hd c.Hol_check.raw_history)<>raw then failwith "raw input replaced";
  let inst th=private_invariant (Lean4hol_env.quote_policy c.Hol_check.environment)
    (Lean4hol_env.quote_env c.Hol_check.environment)
    (Lean4hol_input_certificate.history c.Hol_check.raw_history) c.Hol_check.theorem th in
  List.iter(fun th->if hyp(inst th)<>[] then failwith "open invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];
  if private_native_rule_count<>29 || private_admission_rule_count<>11 then failwith "mutual rule counts changed";
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_RAW_POSITIVE_DONE exact_raw055 closed policy unique unchanged_axioms";;
