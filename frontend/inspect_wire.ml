(* A transport diagnostic only: successful parsing is not proof acceptance. *)
let () =
  if Array.length Sys.argv <> 2 then (
    prerr_endline "usage: inspect-wire EXPORT.ndjson"; exit 3);
  try
    let e = Wire.read_file Sys.argv.(1) in
    Printf.printf "Parsed format=%s names=%d levels=%d expressions=%d declarations=%d\n"
      e.metadata.format_version e.name_count e.level_count e.expr_count
      (List.length e.declarations)
  with
  | Wire.Error e ->
    Printf.eprintf "line %d: %s\n" e.line e.message;
    exit (Wire.error_exit_code e)
  | Sys_error s -> prerr_endline s; exit 3
