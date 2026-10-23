needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
needs "hol/raw_indexed_admission.ml";;
let indexed_file_invariants policy env blocks h =
  List.iter(fun rule -> let proof=MP(SPECL [policy;env;blocks] rule)h in
    if hyp proof<>[] || frees(concl proof)<>[] then failwith "open invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];;
let indexed_file_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let module C=Lean4hol_input_certificate in
  let module W=Hol_input in
  let group=Sys.getenv "COMPOSE_GROUP" in
  let stem=match group with "119"->"119_reduceCtorParamRefl.mk"
    | "120"->"120_reduceCtorParamRefl2.mk" | _->failwith "unknown authentic group" in
  let path="arena/corpus/tutorial/"^stem^".ndjson" in
  let decoded=List.rev(List.map(fun(_,d)->match d with
    | W.Inductive cs -> List.map Hol_check.claim cs
    | W.Definition(h,v) -> [{A.kind=A.Definition;name=Hol_check.name h.W.name;
        params=List.map Hol_check.name h.W.params;typ=Hol_check.expr h.W.typ;
        value=Some(Hol_check.expr v)}]
    | _ -> failwith "unexpected authentic declaration") (W.read_file path)) in
  let code,message,certificate=Hol_check.check_file_with_certificate path in
  Printf.printf "INDEXED_FILE %s code=%d %s\n%!" group code message;
  let c=match code,certificate with 0,Some c->c|_->failwith "authentic indexed raw input declined" in
  let env=c.Hol_check.environment and blocks=c.Hol_check.raw_history in
  ignore(Lean4hol_raw_ctor.exact(C.expected env blocks)c.Hol_check.theorem);
  if frees(concl c.Hol_check.theorem)<>[] || blocks<>decoded then failwith "inexact original history";
  indexed_file_invariants(A.quote_policy env)(A.quote_env env)(C.history blocks)c.Hol_check.theorem;
  let tampered=match blocks with (d::ds)::rest ->
    ({d with A.typ=H.Sort H.Zero}::ds)::rest | _->failwith "empty history" in
  (match C.finish env tampered (indexed_file_trace c.Hol_check.theorem) with
   | Error e when e.H.kind=H.Proof_failure -> ()
   | _->failwith "history tamper must be a proof failure");
  if private_native_rule_count<>29 || private_admission_rule_count<>11 || axioms()<>private_axioms then
    failwith "native rules or axioms changed";
  Printf.printf "PRIVATE_INDEXED_FILE_DONE %s exact_original_history three_invariants tamper_decline unchanged_axioms\n%!" group;;
