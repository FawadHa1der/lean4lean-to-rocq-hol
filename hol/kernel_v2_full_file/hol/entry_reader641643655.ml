(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. Requires genuine host modules already loaded.
   Original641 fixture source MUST have parent's mandatory-scratch relocation. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/flatten_prelude650.ml";;
needs "hol/full_input610.ml";;
needs "hol/proposed_source_decoder_fixtures641.ml";;
needs "hol/proposed_fixtures643.ml";;
Candidate_entry655.check_state ();;

let entry_cases655 = [
  "reader641", (fun () ->
    let dir = Sys.getenv "LEAN4LEAN_FIXTURE_TMPDIR" in
    if dir = "" || Filename.is_relative dir then
      failwith "655: LEAN4LEAN_FIXTURE_TMPDIR must be absolute and outer-owned";
    proposed_source_decoder_fixtures641 ();
    Candidate_entry655.Native_checks
      ["reader641: original16 positive checks and30 refusal cases returned; no HOL theorem"]);
  "bindings643", (fun () ->
    proposed_fixtures643 ();
    Candidate_entry655.Native_checks
      ["bindings643: original quotation/binding stage returned; no HOL theorem"])
];;
let entry_case_names655 = List.map fst entry_cases655;;
let run_entry655 name = Candidate_entry655.run entry_cases655 name;;
