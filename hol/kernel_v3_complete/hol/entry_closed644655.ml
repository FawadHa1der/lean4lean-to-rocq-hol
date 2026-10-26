(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. No case/evaluator creation on load. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/flatten_prelude650.ml";;
needs "hol/kernel_equations647.ml";;
needs "hol/held_runner644.ml";;
Candidate_entry655.check_state ();;

let entry_case_names655 = List.map (fun (name,_,_) -> name) l4_fixture_cases644;;
let run_entry655 name =
  let cases = List.map (fun label -> label,(fun () ->
    let state = Kernel_compute646.create
      ~conversions:l4_kernel_conversions647
      (l4_kernel_equations647 @ l4_fixture_equations644) in
    Candidate_entry655.Theorems [l4_fixture_prove644 state label]))
    entry_case_names655 in
  Candidate_entry655.run cases name;;
