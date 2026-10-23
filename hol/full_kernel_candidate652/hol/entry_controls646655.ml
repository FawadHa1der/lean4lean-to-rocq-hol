(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. Exactly one selected case, no suite call.
   Source provenance and mechanical thunk correspondence: SOURCE_MAP655.json. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/proposed_fixtures648.ml";;
Candidate_entry655.check_state ();;

let entry_case_names655 = [
  "01-first-position";
  "02-middle-position";
  "03-last-position";
  "04-three-full-recursions";
  "05-zero-is-not-successor";
  "06-zero-base-and-one";
  "07-polymorphic-instance";
  "08-overapplication-compute-prefix";
  "09-overapplication-direct-refusal";
  "10-partial-arity-refusal";
  "11-wrong-head-refusal";
  "12-nonnumeral-refusal";
  "13-multiple-successor-positions";
  "14-shared-pattern-variable-refusal";
  "15-nested-successor-unsupported";
  "16-interleaved-forall-conjunction";
  "17-hypothesis-refusal";
  "18-rhs-only-variable-refusal";
  "19-variable-head-refusal";
  "20-expansion-only-is-not-progress";
  "21-missing-base-is-undecided";
  "22-stuck-closed-numeric-refusal";
  "23-stuck-closed-boolean-refusal";
  "24-open-query-refusal";
  "25-wrong-result-type-refusal";
  "26-literal-reflexivity-is-valid";
  "27-proved-predicate-and-negation";
  "28-list-empty-and-cons";
  "29-cond-both-directions";
  "30-cond-stuck-guard";
  "31-stock-cond-unselected-branch-not-visited";
  "32-genuine-attached-rewrite";
  "33-attached-reflexivity-refused";
  "34-attached-wrong-lhs-refused";
  "35-attached-hypothesis-refused";
  "36-attached-proposition-refused";
  "37-attached-rhs-only-variable-refused";
  "38-failed-attachment-allows-real-rule";
  "39-invalid-attachment-registration";
  "40-stock-swallows-attached-exception"
];;

let run_entry655 name =
  let cases = List.map (fun label -> label,(fun () ->
    let built = l4_proposed_cases648 () in
    if List.map fst built <> entry_case_names655 then
      failwith "655: controls648 catalogue differs";
    let action = List.assoc label built in
    action ();
    Candidate_entry655.Native_checks
      ["controls646/" ^ label ^ ": original648 native assertions returned; no theorem payload"]))
    entry_case_names655 in
  Candidate_entry655.run cases name;;
