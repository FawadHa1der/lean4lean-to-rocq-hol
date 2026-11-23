(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Theorem-backed 13-constructor HOL Light v3 file checker (kernel_v3_complete).
   Loaded by HOL Light after hol/kernel_v3_complete/hol/file_certificate649.ml.
   Pre-builds the local Compute compset once in the warm parent before fork (),
   so each Arena case executes in an isolated forked child and certifies
   Accept (0), Reject (1), and Decline (2) via closed HOL theorems:
     |- l4_file_verdict649 fuel raw_file schedule = 0 | 1 | 2. *)

module Hol_check = struct
  let default_fuel =
    match Sys.getenv_opt "HOL_RUNNER_FUEL" with
    | Some raw ->
        let z = Z.of_string (String.trim raw) in
        if Z.lt z Z.zero then failwith "HOL_RUNNER_FUEL must be nonnegative" else z
    | None -> Z.of_int 50000

  (* Pre-build the local Compute compset once in the parent before fork(). *)
  let state = File_certificate649.create ()

  let check_file_with_certificate path =
    try
      if List.length (axioms ()) <> 3 then
        3, "kernel axiom count drifted from stock HOL Light (expected 3)", None
      else
        match File_certificate649.check_file state default_fuel path with
        | File_certificate649.Certified cert ->
            let th = cert.File_certificate649.theorem in
            if hyp th <> [] || frees (concl th) <> [] then
              3, "certificate theorem is not closed", None
            else if List.length (axioms ()) <> 3 then
              3, "kernel axiom count changed during check", None
            else
              let code, label = match cert.File_certificate649.verdict with
                | File_certificate649.Accepted -> 0, "accept"
                | File_certificate649.Rejected -> 1, "reject"
                | File_certificate649.Declined -> 2, "decline" in
              let msg = Printf.sprintf
                "%s: closed HOL v3 theorem |- l4_file_verdict649 ... = %d (rows=%d batches=%d fuel=%s axioms=%d)"
                label code cert.File_certificate649.row_count
                cert.File_certificate649.batch_count (Z.to_string default_fuel)
                (List.length (axioms ())) in
              code, msg, Some cert
        | File_certificate649.Inconclusive inc ->
            2, ("inconclusive: " ^ inc.File_certificate649.diagnostic), None
    with
    | Wire.Error e ->
        let msg = Printf.sprintf "line=%d %s" e.Wire.line e.Wire.message in
        Wire.error_exit_code e, msg, None
    | Full_input610.Invalid_input message -> 1, ("invalid input: " ^ message), None
    | Full_input610.Unsupported_decoder message -> 2, ("unsupported decoder: " ^ message), None
    | File_quotation643.Invalid_binding message -> 2, ("invalid schedule binding: " ^ message), None
    | File_certificate649.Invalid_certificate message -> 3, ("invalid certificate: " ^ message), None
    | Stack_overflow -> 2, "stack resource exhausted", None
    | Out_of_memory -> 2, "memory resource exhausted", None
    | Sys_error message -> 3, message, None
    | exn -> 3, Printexc.to_string exn, None

  let check_file path =
    let code, message, _ = check_file_with_certificate path in
    code, message
end;;
