(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED / UNEXECUTED. Exactly one selected case, no suite call.
   Source provenance and mechanical thunk correspondence: SOURCE_MAP655.json. *)
needs "hol/candidate_entry655.ml";;
Candidate_entry655.check_state ();;
needs "hol/flatten_prelude650.ml";;
needs "hol/nested_family498.ml";;
needs "hol/inductive_derivation516.ml";;
Candidate_entry655.check_state ();;

let prove_L4_FLAT_EMPTY650655 () = prove
 (`FLAT ([]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650]);;

let prove_L4_FLAT_EMPTY_ROW650655 () = prove
 (`FLAT ([[]]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_EMPTY_ROWS650655 () = prove
 (`FLAT ([[];[];[]]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_SINGLE_ROW650655 () = prove
 (`FLAT [[1;2;3]] = [1;2;3]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_ORDER650655 () = prove
 (`FLAT [[3;1];[];[2;4]] = [3;1;2;4]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_DUPLICATES650655 () = prove
 (`FLAT [[2];[1;2];[2]] = [2;1;2;2]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_BOOL650655 () = prove
 (`FLAT [[T;F];[];[F;T]] = [T;F;F;T]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

(* Exactly one layer is concatenated: the inner empty row is retained. *)
let prove_L4_FLAT_ONE_LAYER650655 () = prove
 (`FLAT ([[[1];[]];[];[[2;3]]]:(num list)list list) = [[1];[];[2;3]]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_MAP650655 () = prove
 (`FLAT (MAP (\xs:num list. MAP (\n:num. n) xs) [[1;2];[];[2]]) = [1;2;2]`,
  REWRITE_TAC[l4_flat650;MAP;APPEND]);;

let prove_L4_FLAT_APPEND_ROWS650655 () = prove
 (`FLAT (APPEND [[1];[]] [[2];[3]]) = [1;2;3]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let prove_L4_FLAT_ITLIST650655 () = prove
 (`!xss:(A list)list. FLAT xss = ITLIST APPEND xss []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[l4_flat650;ITLIST]);;

let prove_L4_FLAT_APPEND650655 () = prove
 (`!(xss:(A list)list) yss.
    FLAT (APPEND xss yss) = APPEND (FLAT xss) (FLAT yss)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[l4_flat650;APPEND;APPEND_ASSOC]);;

let prove_L4_FLAT_CANONICAL516650655 () = prove
 (`!xss:(A list)list. FLAT xss = l4_kflatten516 xss`,
  REWRITE_TAC[l4_kflatten516;(prove_L4_FLAT_ITLIST650655 ())]);;

let prove_L4_NESTED_USED_NAMES_FOLD650655 () = prove
 (`!env w. l4_knested_used_names498 env w =
   APPEND (MAP l4_kdecl_name493 env)
    (APPEND (MAP (\s. l4_kdecl_name493 (l4_kspec_decl493 s)) (l4_knw_specs494 w))
     (APPEND (MAP (\s. l4_nested_rec_name437 (l4_kdecl_name493 (l4_kspec_decl493 s)))
                   (l4_knw_specs494 w))
      (l4_kflatten516
        (MAP (\s. MAP l4_kdecl_name493 (l4_kspec_ctors493 s)) (l4_knw_specs494 w)))))`,
  REWRITE_TAC[l4_knested_used_names498;(prove_L4_FLAT_CANONICAL516650655 ())]);;

let entry_cases655 = [
  "L4_FLAT_EMPTY650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_EMPTY650655 ()]);
  "L4_FLAT_EMPTY_ROW650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_EMPTY_ROW650655 ()]);
  "L4_FLAT_EMPTY_ROWS650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_EMPTY_ROWS650655 ()]);
  "L4_FLAT_SINGLE_ROW650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_SINGLE_ROW650655 ()]);
  "L4_FLAT_ORDER650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_ORDER650655 ()]);
  "L4_FLAT_DUPLICATES650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_DUPLICATES650655 ()]);
  "L4_FLAT_BOOL650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_BOOL650655 ()]);
  "L4_FLAT_ONE_LAYER650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_ONE_LAYER650655 ()]);
  "L4_FLAT_MAP650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_MAP650655 ()]);
  "L4_FLAT_APPEND_ROWS650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_APPEND_ROWS650655 ()]);
  "L4_FLAT_ITLIST650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_ITLIST650655 ()]);
  "L4_FLAT_APPEND650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_APPEND650655 ()]);
  "L4_FLAT_CANONICAL516650", (fun () -> Candidate_entry655.Theorems [prove_L4_FLAT_CANONICAL516650655 ()]);
  "L4_NESTED_USED_NAMES_FOLD650", (fun () -> Candidate_entry655.Theorems [prove_L4_NESTED_USED_NAMES_FOLD650655 ()])
];;
let entry_case_names655 = List.map fst entry_cases655;;
let run_entry655 name = Candidate_entry655.run entry_cases655 name;;
