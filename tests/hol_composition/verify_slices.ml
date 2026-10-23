(* Original declaration and syntax-table bytes must survive whole-block selection. *)
let lines path =
  let ic=open_in path in
  let rec read acc=match input_line ic with
    | s -> read(s::acc)
    | exception End_of_file -> close_in ic;Array.of_list(List.rev acc) in
  read []
let () =
  let source=Sys.argv.(1) and dest=Sys.argv.(2) in
  let a=Wire.read_file source and b=Wire.read_file dest in
  let original=lines source and sliced=lines dest in
  let rows=Hashtbl.create 32 and kept=Hashtbl.create 32 in
  List.iter(fun(n,_)->Hashtbl.add rows n ())a.Wire.declarations;
  Array.iter(fun entry->Scanf.sscanf entry "%d %d" (fun out old->
    if sliced.(out-1)<>original.(old-1) || not(Hashtbl.mem rows old) then
      failwith "changed declaration bytes";
    Hashtbl.add kept old ()))(lines Sys.argv.(3));
  let expected=Array.to_list(Array.mapi(fun i s->i+1,s)original) |>
    List.filter_map(fun(n,s)->if not(Hashtbl.mem rows n) || Hashtbl.mem kept n then Some s else None) in
  if Array.of_list expected<>sliced then failwith "changed table bytes or order";
  if a.Wire.metadata<>b.Wire.metadata || a.Wire.name_count<>b.Wire.name_count ||
     a.Wire.level_count<>b.Wire.level_count || a.Wire.expr_count<>b.Wire.expr_count then
    failwith "changed syntax tables";
  if List.length b.Wire.declarations<>Hashtbl.length kept then failwith "changed declaration count";
  Printf.printf "HOL_SLICE_RETENTION_CHECKS_PASSED 4 declarations=%d lines=%d\n"
    (Hashtbl.length kept)(Array.length sliced)
