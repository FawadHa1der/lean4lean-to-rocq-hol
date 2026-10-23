(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED. Three-way observer of actual full-file checking. *)
needs "hol/file_driver642.ml";;

let l4_file_verdict649 = new_definition
 `l4_file_verdict649 fuel input batches =
    match l4_check_file642 fuel input batches with
    | L4KAccept491 env -> 0
    | L4KReject491 reason -> 1
    | L4KDecline491 reason -> 2`;;
