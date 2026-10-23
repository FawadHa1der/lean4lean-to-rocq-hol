let () =
  let reader, writer = Unix.pipe ~cloexec:true () in
  let duplicate = Unix.dup reader in
  Unix.dup2 ~cloexec:true reader duplicate;
  assert (Unix.write_substring writer "ok" 0 2 = 2);
  let bytes = Bytes.create 2 in
  assert (Unix.read duplicate bytes 0 2 = 2);
  assert (Bytes.to_string bytes = "ok");
  List.iter Unix.close [reader; writer; duplicate];
  let json = Yojson.Safe.from_string {|{"value":"1267650600228229401496703205376"}|} in
  let value = Yojson.Safe.Util.(json |> member "value" |> to_string) in
  assert (Z.equal (Z.of_string value) (Z.shift_left Z.one 100));
  assert (Smoke_extracted.successor 41 = 42);
  print_endline "OCAML_UNIX_YOJSON_ZARITH_EXTRACTION_OK"
