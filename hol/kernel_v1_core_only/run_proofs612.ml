(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD source-only proposal. Execute only inside a fresh reviewed guarded
   stock HOL process with all inputs pinned. Not a standalone runner/grant. *)
use_file_raise_failure := true;;

let core612_entries =
 ["hol/projection_properties577.ml";
  "hol/recursor_conversion_properties585.ml";
  "hol/recursor_conversion_regressions585.ml";
  "hol/inference_properties586.ml";
  "hol/whnf_control_properties594.ml";
  "hol/whnf_control_regressions594.ml";
  "hol/conversion_properties595.ml";
  "hol/conversion_fallback_properties596.ml";
  "hol/conversion_fallback_regressions596.ml";
  "hol/kernel_properties597.ml"];;

let core612_stock_axioms = axioms();;
let () = try
  if List.length core612_stock_axioms <> 3 then failwith "CORE612 STOCK_AXIOM_COUNT";
  (* The reviewed outer runner must fix cwd to this immutable candidate.
     All project and two additional stock-library imports are bundled here. *)
  load_path := [Sys.getcwd()];
  List.iter (fun path ->
    let base = Filename.basename path in
    if List.exists (fun (loaded,_) -> loaded = base) !loaded_files
    then failwith ("CORE612 PRELOADED_ENTRY " ^ base)) core612_entries;
  print_endline "CORE612 BEGIN"; flush stdout;
  List.iteri (fun index path ->
    Printf.printf "CORE612 FILE_BEGIN %d %s\n%!" index (Filename.basename path);
    needs path;
    if axioms() <> core612_stock_axioms then failwith "CORE612 AXIOM_CHANGE";
    Printf.printf "CORE612 FILE_DONE %d %s\n%!" index (Filename.basename path)) core612_entries;
  print_endline "CORE612 COMPLETE source_files=10 axioms_unchanged=3";
  flush stdout;
  exit 0
with exn ->
  prerr_endline ("CORE612 FAILURE " ^ Printexc.to_string exn);
  flush stderr;
  exit 3;;

