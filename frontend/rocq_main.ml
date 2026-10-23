let () =
  let fuel = ref 512 and progress = ref 0 and input = ref None and line = ref 0 and checked = ref 0 in
  let set_input s = match !input with
    | None -> input := Some s | Some _ -> raise (Arg.Bad "exactly one export is required") in
  Arg.parse ["--fuel",Arg.Set_int fuel,"recursive checker depth (default 512)";
             "--progress",Arg.Set_int progress,"diagnostics every N checked declarations (0 disables)"] set_input
    "rocq-check [--fuel N] EXPORT.ndjson";
  let path = match !input with Some s -> s | None -> prerr_endline "missing export path"; exit 3 in
  let report code message =
    Printf.eprintf "line=%d checked=%d %s\n" !line !checked message; exit code in
  let stage label = if !progress > 0 then
    Printf.eprintf "stage=%s line=%d checked=%d cpu_seconds=%.3f\n%!" label !line !checked (Sys.time()) in
  try
    if !progress < 0 then report 3 "progress interval must be nonnegative";
    let fuel = Rocq_adapter.nat !fuel in
    stage "parse";
    let export = Wire.read_file path in
    stage "schedule";
    let batches = Replay.schedule export.declarations in
    stage "check";
    let st = Rocq_adapter.create () and state = ref Persistent_adapter.State.initial in
    let consume count result = match result with
      | Lean_arena.Accept next -> state := next; checked := !checked + count
      | Lean_arena.Reject why -> report 1 (Rocq_adapter.reject_reason why)
      | Lean_arena.Decline why -> report 2 (Rocq_adapter.decline_reason why) in
    List.iter (fun batch ->
      line := Replay.line batch;
      if !progress > 0 && !checked mod !progress = 0 then stage "declaration";
      let result = match batch with
        | Replay.Single(_,d) -> Persistent_adapter.State.admit fuel !state st d
        | Replay.Mutual(_,ds) -> Persistent_adapter.State.mutual fuel !state st ds in
      consume (Replay.count batch) result) batches;
    Printf.printf "accept: %d declarations checked by extracted Gallina\n" !checked
  with
  | Wire.Error e -> line := e.line; report (Wire.error_exit_code e) e.message
  | Rocq_adapter.Resource s | Rocq_adapter.Unsupported s -> report 2 s
  | Stack_overflow -> report 2 "stack resource exhausted"
  | Out_of_memory -> report 2 "memory resource exhausted"
  | Sys_error s -> report 3 s
  | exn -> report 3 (Printexc.to_string exn)
