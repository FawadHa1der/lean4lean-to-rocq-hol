(* Compare the old 28/10 statements with the exact preserved base. *)
needs "hol/environment.ml";;
let l4_mindex_boundary_tests () =
  let channel=open_in "tests/hol_composition/reference_indexed_environment_rules.ml" in
  let source=really_input_string channel(in_channel_length channel) in close_in channel;
  let find marker=let rec scan i=
    if i+String.length marker>String.length source then failwith "reference marker"
    else if String.sub source i(String.length marker)=marker then i else scan(i+1) in scan 0 in
  let quotation marker=let left=String.index_from source(find marker)'`' in
    let right=String.index_from source(left+1)'`' in parse_term(String.sub source(left+1)(right-left-1)) in
  let take n xs=List.filteri(fun j _->j<n)xs in
  let old_native=quotation "let l4_edef_RULES," in
  let new_native=end_itlist CONJ(take 28(CONJUNCTS l4_edef_RULES)) in
  if hyp new_native<>[] || not(aconv(concl new_native)old_native)then failwith "native prefix changed";
  let old_valid=quotation "let l4_evalid_RULES," in
  let policy=List.find(fun v->fst(dest_var v)="policy")(frees old_valid) in
  let new_valid=end_itlist CONJ(take 10(CONJUNCTS(SPEC policy l4_evalid_RULES))) in
  if hyp new_valid<>[] || not(aconv(concl new_valid)old_valid)then failwith "admission prefix changed";
  print_endline "HOL_MINDEX_BOUNDARY_TESTS_PASSED 4";;
l4_mindex_boundary_tests();;
