(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. Original649 fixture root must be relocated
   by parent to fixtures/649. No file reading/evaluator creation at load. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/flatten_prelude650.ml";;
needs "hol/proposed_file_fixtures649.ml";;
Candidate_entry655.check_state ();;

let entry_case_names655 =
  List.map (fun (name,_,_,_) -> name) File_fixtures649.cases;;
let run_entry655 name =
  let cases = List.map (fun label -> label,(fun () ->
    let state = File_certificate649.create () in
    match File_fixtures649.run_case state label with
    | Some theorem -> Candidate_entry655.Theorems [theorem]
    | None -> Candidate_entry655.Native_checks
        ["serialized649/" ^ label ^
         ": original expected Wire-error kind/line/message checks returned; no certificate"]))
    entry_case_names655 in
  Candidate_entry655.run cases name;;
