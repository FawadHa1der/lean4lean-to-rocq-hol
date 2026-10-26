(* SPDX-License-Identifier: Apache-2.0. All fixtures UNRUN / UNCOMPILED.
   Held one-case entrypoint. Invocation performs real local fixture-file I/O. *)
needs "hol/file_certificate649.ml";;
unset_jrh_lexer;;

module File_fixtures649 = struct
  type expected = Verdict of File_certificate649.verdict * int
                | Wire_error of Wire.error_kind * int
  let cases = [
    "empty", "empty.ndjson", 64, Verdict (File_certificate649.Accepted,0);
    "empty_zero_fuel", "empty.ndjson", 0, Verdict (File_certificate649.Accepted,0);
    "identity", "identity.ndjson", 64, Verdict (File_certificate649.Accepted,1);
    "identity_zero_fuel", "identity.ndjson", 0, Verdict (File_certificate649.Declined,1);
    "invalid_body", "invalid-body.ndjson", 64, Verdict (File_certificate649.Rejected,1);
    "late_invalid", "late-invalid.ndjson", 64, Verdict (File_certificate649.Rejected,2);
    "duplicate", "duplicate.ndjson", 64, Wire_error (Wire.Malformed,11);
    "late_unsupported", "late-unsupported.ndjson", 64, Wire_error (Wire.Unsupported,11)
  ]

  let run_case state name =
    let _,basename,fuel,expected =
      List.find (fun (label,_,_,_) -> label=name) cases in
    let path = Filename.concat "fixtures/649" basename in
    let observed =
      try Ok (File_certificate649.check_file state (Z.of_int fuel) path)
      with Wire.Error error -> Error error in
    match expected,observed with
    | Verdict (verdict,rows),Ok (File_certificate649.Certified certificate) ->
        if certificate.verdict <> verdict || certificate.row_count <> rows ||
           certificate.batch_count <> rows then failwith (name ^ ": wrong checked outcome");
        Some certificate.theorem
    | Wire_error (kind,line),Error error ->
        if error.kind <> kind || error.line <> line || error.message = "" then
          failwith (name ^ ": wrong transport refusal");
        None
    | _,Ok (File_certificate649.Inconclusive result) ->
        failwith (name ^ ": inconclusive, not a fixture pass: " ^ result.diagnostic)
    | _ -> failwith (name ^ ": expected and observed categories differ")
end;;

set_jrh_lexer;;
