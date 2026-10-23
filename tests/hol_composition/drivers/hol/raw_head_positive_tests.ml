needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let private_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  List.iter(fun name->
    let path="build/raw-fixtures/"^name^".ndjson" in
    let code,message,cert=Hol_check.check_file_with_certificate path in
    print_endline(Printf.sprintf "HEAD_POSITIVE %s code=%d %s" name code message);
    match code,cert with
    | 0,Some c ->
      ignore(Lean4hol_raw_ctor.exact
        (Lean4hol_input_certificate.expected c.Hol_check.environment c.Hol_check.raw_history)
        c.Hol_check.theorem);
      let changed=match c.Hol_check.raw_history with
        | (d::ds)::rest -> ({d with Lean4hol_env.typ=Lean4hol.Sort Lean4hol.Zero}::ds)::rest
        | _ -> failwith "empty raw input history" in
      (match Lean4hol_input_certificate.finish c.Hol_check.environment changed
        (private_trace c.Hol_check.theorem) with
      | Error _ -> print_endline("HEAD_POSITIVE same_name_raw_history_tamper_declines "^name)
      | Ok _ -> failwith "raw history tampering accepted")
    | _ -> failwith("head reduction positive declined: "^name)) ["beta-param";"zeta-param"];
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_RAW_HEAD_POSITIVE_DONE beta_zeta exact_closed two_history_tamper_declines unchanged_axioms";;
