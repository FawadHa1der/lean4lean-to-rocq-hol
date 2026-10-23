needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let compose_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
let compose_invariants policy env blocks h =
  List.iter(fun rule ->
    let proof=MP(SPECL [policy;env;blocks] rule)h in
    if hyp proof<>[] || frees(concl proof)<>[] then failwith "open invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let module W=Hol_input in
  let module C=Lean4hol_input_certificate in
  let module R=Lean4hol_raw_ctor in
  let decoded path=List.rev(List.map(fun(_,d)->match d with
    | W.Inductive cs -> List.map Hol_check.claim cs
    | W.Quotient(h,k) ->
      let k=match k with W.Qtype->Lean4hol_quotient_model.Qtype
        | W.Qctor->Lean4hol_quotient_model.Qctor | W.Qlift->Lean4hol_quotient_model.Qlift
        | W.Qind->Lean4hol_quotient_model.Qind in
      [{A.kind=A.Quotient k;name=Hol_check.name h.W.name;params=List.map Hol_check.name h.W.params;
        typ=Hol_check.expr h.W.typ;value=None}]
    | d ->
      let kind,h,v=match d with
        | W.Definition(h,v) | W.Primitive_definition(h,v) | W.Text_primitive_definition(h,v) ->
          A.Definition,h,Some(Hol_check.expr v)
        | W.Theorem(h,v)->A.Theorem,h,Some(Hol_check.expr v)
        | W.Opaque(h,v)->A.Opaque,h,Some(Hol_check.expr v)
        | W.Axiom h->A.Axiom,h,None
        | _->failwith "unexpected fixture declaration" in
      [{A.kind=kind;name=Hol_check.name h.W.name;params=List.map Hol_check.name h.W.params;
        typ=Hol_check.expr h.W.typ;value=v}]) (W.read_file path)) in
  let files=match Sys.getenv "COMPOSE_GROUP" with
    | "quotient" -> ["130_quotLiftReduction";"131_quotIndReduction"]
    | "structure" -> ["075_typeSingletonRecReduction"]
    | "reflexive" -> ["121_rTreeRec";"122_rtreeRecReduction";"124_accRecReduction"]
    | _ -> failwith "unknown file group" in
  List.iter(fun name ->
    let path="arena/corpus/tutorial/"^name^".ndjson" in
    let code,message,certificate=Hol_check.check_file_with_certificate path in
    Printf.printf "COMPOSE_FILE %s code=%d %s\n%!" name code message;
    let c=match code,certificate with 0,Some c->c|_->failwith("declined "^name) in
    let env=c.Hol_check.environment and blocks=c.Hol_check.raw_history in
    ignore(R.exact(C.expected env blocks)c.Hol_check.theorem);
    if frees(concl c.Hol_check.theorem)<>[] then failwith "free certificate variables";
    if blocks<>decoded path then failwith "raw history changed";
    compose_invariants(A.quote_policy env)(A.quote_env env)(C.history blocks)c.Hol_check.theorem;
    let tampered=match blocks with (d::ds)::rest ->
      ({d with A.typ=H.Sort H.Zero}::ds)::rest | _->failwith "empty fixture" in
    (match C.finish env tampered (compose_trace c.Hol_check.theorem) with
     | Error {H.kind=H.Proof_failure;_}->()
     | Error _->failwith "history tamper did not fail the exact certificate guard"
     | Ok _->failwith "history tamper accepted"))files;
  if axioms()<>private_axioms then failwith "axiom change";
  Printf.printf "PRIVATE_COMPOSE_FILES_DONE %s %d_exact_histories invariants tamper_declines unchanged_axioms\n%!"
    (Sys.getenv "COMPOSE_GROUP") (List.length files);;
