needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let compose_mutual_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
let compose_mutual_invariants args h =
  List.iter(fun rule -> let theorem=MP(SPECL args rule)h in
    if hyp theorem<>[] || frees(concl theorem)<>[] then failwith "open invariant")
    [l4_input_valid_environment;l4_input_valid_unique;l4_input_valid_permissions];;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in let module A=Lean4hol_env in
  let module W=Hol_input in let module C=Lean4hol_input_certificate in
  let file,expected=match Sys.getenv "COMPOSE_GROUP" with
    | "empty" -> "ind_mutual_zero_ctor.ndjson",0
    | "recursive" -> "inmodel-first-block.ndjson",0
    | "forged" -> "inmodel-forged-motives.ndjson",2
    | _ -> failwith "unknown mutual trace group" in
  let path="fixtures/mutual/"^file in
  let decoded=List.rev(List.map(fun(_,d)->match d with
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
        | _->failwith "unsupported fixture declaration" in
      [{A.kind=kind;name=Hol_check.name h.W.name;params=List.map Hol_check.name h.W.params;
        typ=Hol_check.expr h.W.typ;value=v}]) (W.read_file path)) in
  let code,message,cert=Hol_check.check_file_with_certificate path in
  Printf.printf "COMPOSE_MUTUAL_FILE %s code=%d %s\n%!" file code message;
  if code<>expected then failwith "mutual trace verdict mismatch";
  (match code,cert with
   | 0,Some c ->
     let env=c.Hol_check.environment and blocks=c.Hol_check.raw_history in
     if blocks<>decoded then failwith "original mutual claims changed";
     ignore(Lean4hol_raw_ctor.exact(C.expected env blocks)c.Hol_check.theorem);
     if frees(concl c.Hol_check.theorem)<>[] then failwith "free certificate variables";
     compose_mutual_invariants [A.quote_policy env;A.quote_env env;C.history blocks] c.Hol_check.theorem;
     let bad=match blocks with (d::ds)::rest -> ({d with A.typ=H.Sort H.Zero}::ds)::rest
       | _ -> failwith "empty trace" in
     (match C.finish env bad (compose_mutual_trace c.Hol_check.theorem) with
      | Error {H.kind=H.Proof_failure;_} -> ()
      | Error _ -> failwith "tampered history did not fail the exact certificate guard"
      | Ok _ -> failwith "tampered history accepted")
   | 2,None -> ()
   | _ -> failwith "mutual certificate mismatch");
  if axioms()<>private_axioms then failwith "new axiom";
  let detail=if expected=0 then " exact_history invariants tamper_proof_failure"
    else " decline no_certificate" in
  print_endline("PRIVATE_MUTUAL_TRACE_DONE "^Sys.getenv "COMPOSE_GROUP"^detail^" unchanged_axioms");;
