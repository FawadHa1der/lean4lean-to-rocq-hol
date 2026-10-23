(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED CLOSED GOALS / UNCOMPILED / NOT EXECUTED.
   Expected tags are host-side test data, never checker inputs or HOL axioms.
   Each query observes the actual642 checker on literal closed fixture data. *)
needs "hol/full_file_data644.ml";;

(* Some0=expected Accept, Some1=expected Reject, Some2=expected Decline.
   None is reserved for an unknown expectation, never a passing test.
   Fuel64/96 are proposed inputs, not measured sufficient bounds. *)
let l4_fixture_cases644 =
 ["empty",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_empty644 [])`, Some `0`;
  "identity",
    `l4_fixture_result_tag644 (l4_check_file642 64 l4_fixture_identity644 [L4FileSingle642 0])`, Some `0`;
  "invalid_body_type",
    `l4_fixture_result_tag644 (l4_check_file642 64 l4_fixture_invalid_body644 [L4FileSingle642 0])`, Some `1`;
  "duplicate_headers",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_duplicate_headers644
      [L4FileSingle642 0;L4FileSingle642 1])`, Some `1`;
  "schedule_dropped",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_identity644 [])`, Some `1`;
  "schedule_duplicate",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_two644
      [L4FileSingle642 0;L4FileSingle642 0])`, Some `1`;
  "schedule_out_of_range",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_identity644 [L4FileSingle642 1])`, Some `1`;
  "forged_inductive_metadata",
    `l4_fixture_result_tag644 (l4_check_file642 64 l4_fixture_forged_inductive644 [L4FileSingle642 0])`, Some `1`;
  "unsafe_available_to_safe_theorem",
    `l4_fixture_result_tag644 (l4_check_file642 64 l4_fixture_unsafe_to_safe644
      [L4FileSingle642 0;L4FileSingle642 1])`, Some `1`;
  "complete_bool_block",
    `l4_fixture_result_tag644 (l4_check_file642 64 l4_fixture_bool644 [L4FileSingle642 0])`, Some `0`;
  "complete_nat_block",
    `l4_fixture_result_tag644 (l4_check_file642 96 l4_fixture_nat644 [L4FileSingle642 0])`, Some `0`;
  "bad_format",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_bad_format644 [])`, Some `2`;
  "identity_zero_fuel",
    `l4_fixture_result_tag644 (l4_check_file642 0 l4_fixture_identity644 [L4FileSingle642 0])`, Some `2`];;

(* These are term-valued proposed goals, NOT theorems or successful receipts. *)
let l4_fixture_closed_goals644 =
  List.fold_right
    (fun (name,query,expected) rest -> match expected with
     | None -> rest
     | Some literal -> (name,mk_eq(query,literal))::rest)
    l4_fixture_cases644 [];;
