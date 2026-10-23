needs "hol/private_boot.ml";;
needs "hol/hadd_proof_helpers.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
needs "hadd_common.ml";;
let () =
  let module T=Hadd_test in
  let decode path=List.map(fun(_,d)->match d with
    | T.W.Inductive cs->List.map Hol_check.claim cs
    | T.W.Definition(h,v)->[T.raw_definition h v]
    | _->failwith "unexpected source declaration") (T.W.read_file path) in
  let raw=decode "arena/corpus/tutorial/119_reduceCtorParamRefl.mk.ndjson" in
  let poly=decode "fixtures/hadd-132.ndjson" in
  let path="fixtures/mixed-119-hadd.ndjson" in
  let original=raw@poly in
  if decode path<>original then failwith "table remapping changed decoded source declarations";
  Printf.printf "PRIVATE_MIXED_DECODED exact_original_blocks count=%d\n%!" (List.length original);
  let code,message,certificate=Hol_check.check_file_with_certificate path in
  Printf.printf "PRIVATE_MIXED_RESULT code=%d %s\n%!" code message;
  let c=match code,certificate with 0,Some c->c|_->failwith "mixed authentic input declined" in
  let env=c.Hol_check.environment and history=c.Hol_check.raw_history in
  if history<>List.rev original then failwith "mixed original history changed";
  ignore(T.R.exact(T.C.expected env history)c.Hol_check.theorem);
  T.closed c.Hol_check.theorem;
  hadd_invariants env history c.Hol_check.theorem;
  let tampered=match history with (d::ds)::rest->({d with T.A.typ=T.H.Sort T.H.Zero}::ds)::rest
    | _->failwith "empty mixed history" in
  (match T.C.finish env tampered (hadd_trace c.Hol_check.theorem) with
   | Error e when e.T.H.kind=T.H.Proof_failure -> ()
   | _->failwith "mixed tamper must be a proof failure");
  T.native();
  Printf.printf "PRIVATE_MIXED_DONE exact_original_raw_poly_history three_invariants tamper_proof_failure rules29_11 unchanged_axioms\n%!";;
