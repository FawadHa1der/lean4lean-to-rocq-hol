(* Isolated data-structure benchmark, never a kernel or Arena verdict. *)
module C = Environment_index_extracted

let bool b = if b then C.True else C.False
let binary z =
  let rec positive z =
    if Z.equal z Z.one then C.XH else
    let tail = positive (Z.shift_right z 1) in
    if Z.testbit z 0 then C.XI tail else C.XO tail in
  if Z.sign z < 0 then invalid_arg "negative name component";
  if Z.equal z Z.zero then C.N0 else C.Npos (positive z)
let ascii c =
  let n = Char.code c in
  let bit i = bool (n land (1 lsl i) <> 0) in
  C.Ascii (bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let string s =
  let result = ref C.EmptyString in
  for i = String.length s - 1 downto 0 do
    result := C.String (ascii s.[i], !result)
  done;
  !result
module NameMemo = Hashtbl.Make(struct
  type t = Wire.name
  let equal a b = a == b
  let hash = Hashtbl.hash
end)
module NameSet = Hashtbl.Make(struct
  type t = Wire.name
  let equal = Wire.equal_name
  let hash = Hashtbl.hash
end)
let convert_names =
  let memo = NameMemo.create 4096 in
  let rec name n = match NameMemo.find_opt memo n with
    | Some value -> value
    | None ->
      let value = match n with
        | Wire.Anonymous -> C.NameAnon
        | Wire.Str(p,s) -> C.NameStr(name p,string s)
        | Wire.Num(p,n) -> C.NameNum(name p,binary n) in
      NameMemo.add memo n value; value in
  name
let names = function
  | Wire.Axiom(h,_) | Wire.Theorem(h,_,_) | Wire.Opaque(h,_,_,_) | Wire.Quotient(h,_) -> [h.name]
  | Wire.Definition d -> [d.header.name]
  | Wire.Inductive(ts,cs,rs) ->
    List.map(fun (d:Wire.inductive)->d.ind_header.name)ts @
    List.map(fun (d:Wire.constructor)->d.ctor_header.name)cs @
    List.map(fun (d:Wire.recursor)->d.rec_header.name)rs
let rec natural = function C.O -> 0 | C.S n -> 1 + natural n
let rec ordinary_list = function C.Nil -> [] | C.Cons(x,xs) -> x :: ordinary_list xs
let emit fields =
  Yojson.Safe.to_channel stdout (`Assoc fields); output_char stdout '\n'; flush stdout
let int n = `Int n
let float n = `Float n
let text n = `String n
let flag n = `Bool n
let deadline = ref infinity
let check_budget () = if Unix.gettimeofday () >= !deadline then failwith "benchmark wall budget exhausted"

let allocated s = s.Gc.minor_words +. s.Gc.major_words -. s.Gc.promoted_words
let measure ~units f =
  check_budget ();
  Gc.full_major ();
  let before = Gc.quick_stat () in
  let cpu = Sys.time () and wall = Unix.gettimeofday () in
  let iterations = ref 0 and result = ref None in
  while !iterations = 0 || (!iterations < 32 && Sys.time () -. cpu < 0.15) do
    check_budget ();
    result := Some (f ()); incr iterations
  done;
  let cpu_seconds = Sys.time () -. cpu and wall_seconds = Unix.gettimeofday () -. wall in
  let after = Gc.quick_stat () in
  let words = allocated after -. allocated before in
  let operations = !iterations * units in
  Option.get !result, `Assoc [
    "iterations",int !iterations; "units_per_iteration",int units;
    "operations",int operations; "cpu_seconds",float cpu_seconds; "wall_seconds",float wall_seconds;
    "cpu_seconds_per_iteration",float (cpu_seconds /. Float.of_int !iterations);
    "cpu_microseconds_per_unit",float (1e6 *. cpu_seconds /. Float.of_int operations);
    "allocated_words",float words; "allocated_words_per_unit",float (words /. Float.of_int operations);
    "minor_collections",int (after.Gc.minor_collections - before.Gc.minor_collections);
    "major_collections",int (after.Gc.major_collections - before.Gc.major_collections)]

let lookup_batch lookup queries () =
  let found = ref 0 in
  Array.iteri (fun i n ->
    if i mod 128 = 0 then check_budget ();
    match lookup n with C.None -> () | C.Some _ -> incr found) queries;
  !found
let compare_all lookup queries expected =
  Array.iteri (fun i n ->
    if i mod 128 = 0 then check_budget ();
    if lookup n <> expected.(i) then
      failwith (Printf.sprintf "lookup mismatch at query %d" i)) queries;
  Array.length queries

let bucket_statistics index entries distinct =
  let lengths = List.map natural (ordinary_list (C.benchmark_bucket_lengths index)) in
  let buckets = List.length lengths in
  let total = List.fold_left (+) 0 lengths in
  if total <> entries then failwith "bucket accounting mismatch";
  `Assoc ["entries",int total; "distinct_names",int distinct; "buckets",int buckets;
    "distinct_name_collision_excess",int (distinct-buckets);
    "duplicate_entries",int (entries-distinct);
    "maximum_bucket_entries",int (List.fold_left max 0 lengths);
    "non_singleton_buckets",int (List.length (List.filter(fun n->n>1)lengths))]

let () =
  try
    let input = ref None and seconds = ref 100. in
    Arg.parse ["--seconds",Arg.Set_float seconds,"overall benchmark wall budget (maximum 110)"]
      (fun s -> match !input with None -> input := Some s | Some _ -> raise(Arg.Bad "one input required"))
      "environment-index-benchmark [--seconds N] PREFIX.ndjson";
    if !seconds <= 0. || !seconds > 110. then invalid_arg "wall budget must be in (0,110]";
    deadline := Unix.gettimeofday () +. !seconds;
    let path = match !input with Some s -> s | None -> invalid_arg "missing prefix" in
    let read_cpu = Sys.time () in
    let export = Wire.read_file path in
    let wire_names = Array.of_list(List.concat_map(fun (_,d)->names d)export.declarations) in
    let set = NameSet.create (Array.length wire_names) in
    Array.iter(fun n->if NameSet.mem set n then failwith "duplicate source declaration name";
                     NameSet.add set n ())wire_names;
    let present = Array.map convert_names wire_names in
    let absent = Array.map(fun n->C.NameStr(n,string "_environment_index_benchmark_absent"))present in
    let size = Array.length present in
    if size < 128 then failwith "expected the saved large Init prefix";
    let declarations = Array.mapi(fun i n->C.benchmark_dummy_declaration n (binary (Z.of_int(i+1))))present in
    let base = Array.fold_left(fun env d->C.Cons(d,env))C.Nil declarations in
    let duplicates = Array.init 128 (fun i ->
      C.benchmark_dummy_declaration present.(i * size / 128) (binary(Z.of_int(size+i+1)))) in
    let shadowed = Array.fold_left(fun env d->C.Cons(d,env))base duplicates in
    let queries = Array.append present absent in
    emit ["event",text "dataset"; "input",text path;
      "format",text export.metadata.format_version; "lean_version",text export.metadata.lean_version;
      "declaration_records",int (List.length export.declarations); "declared_names",int size;
      "wire_expression_nodes",int export.expr_count; "duplicate_shadow_records",int 128;
      "present_queries",int size; "absent_queries",int size;
      "read_convert_cpu_seconds",float(Sys.time() -. read_cpu);
      "dummy_payloads",flag true; "kernel_check_performed",flag false;
      "environment_order",text "reverse wire declaration/member enumeration; duplicate records prepended"];
    let candidates = ["rolling16",C.benchmark_hash16; "rolling32",C.benchmark_hash32;
                      "leaf16",C.benchmark_hash_leaf16; "constant0",C.benchmark_hash_constant] in
    List.iter(fun (dataset,env,entry_count)->
      check_budget ();
      let expected = Array.map(fun n->C.find_decl n env)queries in
      Array.iteri(fun i value -> match value with
        | C.Some _ when i<size -> ()
        | C.None when i>=size -> ()
        | _ -> failwith "present/absent query construction failed")expected;
      if dataset="shadowed" then Array.iter(fun d ->
        if C.find_decl d.C.decl_name env <> C.Some d then failwith "newest duplicate did not shadow")duplicates;
      let _,present_timing = measure ~units:size (lookup_batch(fun n->C.find_decl n env)present) in
      let _,absent_timing = measure ~units:size (lookup_batch(fun n->C.find_decl n env)absent) in
      emit ["event",text "baseline"; "dataset",text dataset; "entries",int entry_count;
            "present",present_timing; "absent",absent_timing];
      List.iter(fun (candidate,hash)->
        let index,build_timing = measure ~units:1 (fun ()->C.index_environment hash env) in
        let checked,validation_timing = measure ~units:(Array.length queries)
          (fun ()->compare_all(fun n->C.indexed_find_decl hash n index)queries expected) in
        let incremental_checks = if dataset="shadowed" then begin
          let initial = C.index_environment hash base in
          let updated = Array.fold_left(fun index d->C.index_declaration hash d index)initial duplicates in
          compare_all(fun n->C.indexed_find_decl hash n updated)queries expected
        end else 0 in
        let _,present_timing = measure ~units:size (lookup_batch(fun n->C.indexed_find_decl hash n index)present) in
        let _,absent_timing = measure ~units:size (lookup_batch(fun n->C.indexed_find_decl hash n index)absent) in
        let _,hash_timing = measure ~units:(Array.length queries) (fun ()->
          Array.fold_left(fun count n->match hash n with C.N0->count | C.Npos _->count+1)0 queries) in
        emit ["event",text "candidate"; "dataset",text dataset; "hash",text candidate;
          "all_lookup_results_equal",flag true; "queries_per_validation",int checked;
          "incremental_shadow_queries_equal",int incremental_checks;
          "bucket_statistics",bucket_statistics index entry_count size;
          "index_build",build_timing; "validation",validation_timing;
          "present",present_timing; "absent",absent_timing; "hash_only",hash_timing])candidates)
      ["base",base,size; "shadowed",shadowed,size+128];
    emit ["event",text "complete"; "datasets",int 2; "candidates_per_dataset",int 4;
          "kernel_check_performed",flag false]
  with exn ->
    emit ["event",text "error"; "message",text(Printexc.to_string exn)]; exit 2
