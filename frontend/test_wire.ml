open Wire

let failures = ref 0 and checks = ref 0
let assert_test label b =
  incr checks;
  if not b then (incr failures; prerr_endline ("FAIL: " ^ label))
let parse s =
  let path = Filename.temp_file "lean-wire-test-" ".ndjson" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    let oc = open_out_bin path in
    Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc s);
    read_file path)
let meta = "{\"meta\":{\"exporter\":{\"name\":\"test\",\"version\":\"1\"},\"lean\":{\"version\":\"test\",\"githash\":\"test\"},\"format\":{\"version\":\"3.1.0\"}}}\n"
let expect_error label kind input =
  try ignore (parse input); assert_test label false
  with Error e -> assert_test label (e.kind = kind)
let j x = Yojson.Safe.to_string x ^ "\n"

let () =
  let empty = parse meta in
  assert_test "implicit tables" (empty.name_count = 1 && empty.level_count = 1 && empty.expr_count = 0);
  assert_test "empty environment has no manufactured declarations" (empty.declarations = []);
  expect_error "missing metadata" Malformed "{\"sort\":0,\"ie\":0}\n";
  expect_error "empty file" Malformed "";
  expect_error "duplicate metadata" Malformed (meta ^ meta);
  expect_error "unsupported format" Unsupported
    "{\"meta\":{\"format\":{\"version\":\"99.0.0\"}}}\n";
  expect_error "negative bvar" Malformed (meta ^ "{\"bvar\":-1,\"ie\":0}\n");
  expect_error "float bvar" Malformed (meta ^ "{\"bvar\":1.0,\"ie\":0}\n");
  expect_error "undefined level" Malformed (meta ^ "{\"sort\":1,\"ie\":0}\n");
  expect_error "undefined name" Malformed (meta ^ "{\"param\":1,\"il\":1}\n");
  expect_error "no implicit expression zero" Malformed
    (meta ^ "{\"app\":{\"fn\":0,\"arg\":0},\"ie\":1}\n");
  expect_error "shadow anonymous name" Malformed
    (meta ^ "{\"str\":{\"pre\":0,\"str\":\"x\"},\"in\":0}\n");
  expect_error "shadow zero level" Malformed (meta ^ "{\"succ\":0,\"il\":0}\n");
  expect_error "duplicate expression" Malformed
    (meta ^ "{\"sort\":0,\"ie\":0}\n{\"sort\":0,\"ie\":0}\n");
  expect_error "cyclic expression" Malformed
    (meta ^ "{\"app\":{\"fn\":0,\"arg\":1},\"ie\":0}\n");
  expect_error "duplicate JSON field" Malformed
    (meta ^ "{\"sort\":0,\"sort\":1,\"ie\":0}\n");
  expect_error "duplicate nested JSON field" Malformed
    (meta ^ "{\"str\":{\"pre\":0,\"str\":\"x\",\"str\":\"y\"},\"in\":1}\n");
  expect_error "competing record tags" Malformed
    (meta ^ "{\"sort\":0,\"bvar\":0,\"ie\":0}\n");
  expect_error "invalid natural literal" Malformed (meta ^ "{\"natVal\":\"-3\",\"ie\":0}\n");
  expect_error "hex literal not decimal" Malformed (meta ^ "{\"natVal\":\"0xff\",\"ie\":0}\n");
  expect_error "table id cannot wrap" Resource
    (meta ^ "{\"sort\":0,\"ie\":99999999999999999999999999999999}\n");
  let huge = String.make 300 '9' in
  let input = meta ^ j (`Assoc ["str", `Assoc ["pre",`Int 0;"str",`String "A"];"in",`Int 1]) ^
    j (`Assoc ["natVal",`String huge;"ie",`Int 0]) ^
    j (`Assoc ["axiom",`Assoc ["name",`Int 1;"levelParams",`List [];"type",`Int 0;"isUnsafe",`Bool false]]) in
  (match (parse input).declarations with
   | [(_, Axiom ({ typ = NatLit n; _ }, false))] ->
     assert_test "unbounded literal parsed exactly" (Z.to_string n = huge)
   | _ -> assert_test "unbounded literal parsed exactly" false);
  (* Transport must not make this ill-typed axiom acceptable. The core checks it. *)
  assert_test "names do not flatten dots"
    (not (equal_name (Str (Anonymous, "a.b")) (dotted_name ["a";"b"])));
  assert_test "numeric and string names differ"
    (not (equal_name (Num (Anonymous, Z.one)) (Str (Anonymous, "1"))));
  assert_test "UTF8 ASCII" (valid_utf8 "abc\000");
  assert_test "UTF8 scalar" (valid_utf8 "\240\159\152\128");
  List.iter (fun (label, bytes) -> assert_test label (not (valid_utf8 bytes))) [
    "UTF8 rejects continuation", "\128";
    "UTF8 rejects overlong", "\192\128";
    "UTF8 rejects surrogate", "\237\160\128";
    "UTF8 rejects out-of-range", "\244\144\128\128";
    "UTF8 rejects truncated", "\226\130"
  ];
  Printf.printf "wire parser: %d checks, %d failures\n" !checks !failures;
  if !failures <> 0 then exit 1
