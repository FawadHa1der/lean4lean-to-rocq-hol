needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let count=ref 0 in
  let check expected path =
    let code,message=Hol_check.check_file path in
    Printf.printf "STRING_CONTROL %s code=%d %s\n%!" path code message;
    if code<>expected then failwith("unexpected string control: "^path);
    incr count in
  check 0 "fixtures/string/interfaces.ndjson";
  let group=match Sys.getenv_opt "RAW_STRING_GROUP" with Some s->s | None->"a" in
  let names=match group with
    | "a" -> ["different-literal";"no-normalization";
     "Char.ofNat-unsafe";"Char.ofNat-partial";"Char.ofNat-missing";
     "Char.ofNat-bad-body";"Char.ofNat-universe"]
    | "b" -> ["String.ofList-unsafe";"String.ofList-partial";"String.ofList-missing";
     "String.ofList-bad-body";"String.ofList-universe";
     "nil-universe-arity";"cons-universe-arity";"literal-not-proof"]
    | "c" -> []
    | _ -> failwith "unknown string control group" in
  List.iter(fun name->check 2 ("fixtures/string/"^name^".ndjson")) names;
  if group="c" then begin
    List.iter(fun name->check 2 ("fixtures/extra/"^name^".ndjson")) ["literal-unsafe";"literal-partial"];
    List.iter(fun name->check 1 ("fixtures/extra/"^name^".ndjson"))
    ["Char.ofNat-invalid-safe-tag";"String.ofList-invalid-safe-tag";
     "utf-surrogate";"utf-overlong";"utf-continuation";"utf-out-of-range"]
  end;
  if axioms()<>private_axioms then failwith "axiom change";
  Printf.printf "PRIVATE_RAW_STRING_CONTROLS_DONE group_%s positive_gate %d_controls unchanged_axioms\n%!" group (!count-1);;
