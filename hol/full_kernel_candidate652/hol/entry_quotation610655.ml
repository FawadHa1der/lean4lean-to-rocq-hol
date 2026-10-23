(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. Original610 quotation/preflight stage,
   no file I/O. Requires genuine Wire/Zarith/Yojson already loaded by parent. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/flatten_prelude650.ml";;
needs "hol/proposed_fixtures610.ml";;
Candidate_entry655.check_state ();;

let entry_cases655 = [
  "quotation610", (fun () ->
    proposed_fixtures610 ();
    Candidate_entry655.Native_checks
      ["quotation610: original term-construction/preflight controls returned; no HOL theorem"])
];;
let entry_case_names655 = List.map fst entry_cases655;;
let run_entry655 name = Candidate_entry655.run entry_cases655 name;;
