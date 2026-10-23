needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let private_trace h = CONJUNCT1(REWRITE_RULE [l4_input_valid] h);;
let private_raw_string_predicates s =
  let q=Lean4hol.quote_expr(Lean4hol.Strlit s) in
  let tm=mk_eq(Lean4hol.node "l4_bridge_shape" [`F`;q],q) in
  let th=prove(tm,REWRITE_TAC [l4_bridge_shape]) in
  Lean4hol_raw_ctor.exact tm th;;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let module H=Lean4hol in
  let module A=Lean4hol_env in
  let module W=Hol_input in
  let module R=Lean4hol_raw_ctor in
  let original_blocks path = List.rev(List.map(fun(_,d)->match d with
    | W.Inductive cs -> List.map Hol_check.claim cs
    | d ->
      let kind,h,v=match d with
        | W.Definition(h,v) | W.Primitive_definition(h,v) | W.Text_primitive_definition(h,v) ->
          A.Definition,h,Some(Hol_check.expr v)
        | W.Theorem(h,v) -> A.Theorem,h,Some(Hol_check.expr v)
        | W.Opaque(h,v) -> A.Opaque,h,Some(Hol_check.expr v)
        | W.Axiom h -> A.Axiom,h,None
        | _ -> failwith "unexpected string fixture declaration" in
      [{A.kind=kind;name=Hol_check.name h.W.name;params=List.map Hol_check.name h.W.params;
        typ=Hol_check.expr h.W.typ;value=v}]) (W.read_file path)) in
  List.iter(fun label->
    let path="fixtures/string/"^label^".ndjson" in
    let code,message,cert=Hol_check.check_file_with_certificate path in
    Printf.printf "STRING_POSITIVE %s code=%d %s\n%!" label code message;
    let c=match code,cert with 0,Some c->c | _->failwith("string positive declined: "^label) in
    ignore(R.exact(Lean4hol_input_certificate.expected c.Hol_check.environment c.Hol_check.raw_history)
      c.Hol_check.theorem);
    if frees(concl c.Hol_check.theorem)<>[] then failwith "free variables in final certificate";
    if c.Hol_check.raw_history<>original_blocks path then failwith "text raw history changed";
    let flat=List.concat c.Hol_check.raw_history in
    List.iter(fun name->
      let full=H.Str(H.Str(H.Anonymous,fst name),snd name) in
      if not(List.exists(fun d->d.A.name=full && d.A.kind=A.Definition && d.A.value<>None)flat)
      then failwith "raw text primitive body missing") [("Char","ofNat");("String","ofList")];
    let changed=List.map(List.map(fun d->if d.A.name=H.Str(H.Str(H.Anonymous,"Char"),"ofNat")
      then {d with A.value=Some(H.Sort H.Zero)} else d))c.Hol_check.raw_history in
    (match Lean4hol_input_certificate.finish c.Hol_check.environment changed
      (private_trace c.Hol_check.theorem) with
     | Error _ -> () | Ok _ -> failwith "text raw body tampering accepted"))
    ["interfaces";"empty";"nul";"ascii";"unicode";"same-literal";"reverse-dependencies"];
  List.iter(fun s->
    ignore(private_raw_string_predicates s);
    match H.run 100000 [] [] (fun st->R.head st [] (H.Strlit s)) with
    | Ok(normal,h) when normal=H.Strlit s ->
      ignore(R.exact(H.node "l4_head" [R.entries [];H.quote_expr(H.Strlit s);H.quote_expr normal])h)
    | _ -> failwith "literal head changed") ["";"\000";"reduceCtorParam";"\240\144\128\128"];
  if private_native_rule_count<>29 || private_admission_rule_count<>11 then failwith "mutual rule counts changed";
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_RAW_STRING_POSITIVE_DONE seven_gates exact_text_history seven_tamper_declines neutral_literals unchanged_axioms";;
