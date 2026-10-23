needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
unset_jrh_lexer;;
needs "frontend/hol_check.ml";;
let () =
  let check expected path =
    let code,message=Hol_check.check_file path in
    print_endline(Printf.sprintf "E2E %s code=%d %s" path code message);
    if code<>expected then failwith("unexpected verdict: "^path) in
  check 0 "arena/corpus/tutorial/055_reduceCtorParam.mk.ndjson";
  List.iter(fun name->check 2 ("build/raw-fixtures/"^name^".ndjson"))
    ["nonuniform-beta";"opaque-alias";"wrong-field-count"];
  List.iter(fun name->check 0 ("arena/corpus/tutorial/"^name^".ndjson"))
    ["119_reduceCtorParamRefl.mk";"120_reduceCtorParamRefl2.mk"];
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_RAW_FILES_DONE authentic055_119_120_accept three_declines unchanged_axioms";;
