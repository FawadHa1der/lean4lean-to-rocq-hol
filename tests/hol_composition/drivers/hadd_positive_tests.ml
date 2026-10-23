needs "hol/private_boot.ml";;
needs "hol/hadd_proof_helpers.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
needs "hadd_common.ml";;
let () =
  let module T=Hadd_test in
  let group=Sys.getenv "COMPOSE_GROUP" in
  let path=match group with
    | "hadd"->"fixtures/hadd-132.ndjson"
    | "raw055"->"arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson"
    | _->failwith "unknown positive group" in
  let decoded=List.rev(List.map(fun(_,d)->match d with
    | T.W.Inductive cs->List.map Hol_check.claim cs
    | T.W.Definition(h,v)->[T.raw_definition h v]
    | _->failwith "unexpected positive declaration") (T.W.read_file path)) in
  let code,message,certificate=Hol_check.check_file_with_certificate path in
  Printf.printf "PRIVATE_POSITIVE_RESULT %s code=%d %s\n%!" group code message;
  let c=match code,certificate with 0,Some c->c|_->failwith "authentic input declined" in
  let env=c.Hol_check.environment and blocks=c.Hol_check.raw_history in
  ignore(T.R.exact(T.C.expected env blocks)c.Hol_check.theorem);
  T.closed c.Hol_check.theorem;
  if blocks<>decoded then failwith "original decoded history changed";
  hadd_invariants env blocks c.Hol_check.theorem;
  let tampered=match blocks with (d::ds)::rest->({d with T.A.typ=T.H.Sort T.H.Zero}::ds)::rest
    | _->failwith "empty history" in
  (match T.C.finish env tampered (hadd_trace c.Hol_check.theorem) with
   | Error e when e.T.H.kind=T.H.Proof_failure -> T.decline "history_tamper" (Error e)
   | _->failwith "history tamper must be a proof failure");
  T.native();
  Printf.printf "PRIVATE_POSITIVE_DONE %s exact_original_history three_invariants tamper_decline unchanged_axioms\n%!" group;;
