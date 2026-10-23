(* Transport profiling only. A successful run is NOT a proof-checking verdict. *)
let stamp label =
  let memory=Gc.quick_stat() in
  Printf.printf "%s cpu_seconds=%.3f heap_words=%d\n%!" label (Sys.time()) memory.Gc.heap_words
let () =
  if Array.length Sys.argv<>2 then(failwith "inspect-replay EXPORT.ndjson");
  stamp "start";
  let input=Wire.read_file Sys.argv.(1) in
  stamp "parsed";
  Printf.printf "declaration_records=%d expression_nodes=%d\n%!"
    (List.length input.Wire.declarations) input.Wire.expr_count;
  let batches=Replay.schedule input.Wire.declarations in
  stamp "scheduled";
  Printf.printf "batches=%d covered_records=%d (NOT logically checked)\n%!"
    (List.length batches) (List.fold_left(fun n b->n+Replay.count b)0 batches)
