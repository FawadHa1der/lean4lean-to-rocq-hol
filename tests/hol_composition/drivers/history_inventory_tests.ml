needs "hol/private_boot.ml";;
needs "hol/raw_ctor_admission.ml";;
let () =
  let a=`L4String L4Anonymous [65]` and b=`L4String L4Anonymous [66]`
  and c=`L4String L4Anonymous [67]` in
  let names xs=mk_list(xs,`:l4_name`) in
  let check truth xs ys =
    let tm=list_mk_comb(`l4_name_inventory`,[names xs;names ys]) in
    let claim=if truth then tm else mk_neg tm in
    let h=prove(claim,CONV_TAC Lean4hol_raw_ctor.calc) in
    if hyp h<>[] || frees(concl h)<>[] || not(aconv(concl h)claim) then
      failwith "inventory certificate mismatch" in
  check true [a;b] [b;a];
  check true [] [];
  check false [a;a] [a];
  check false [a] [a;a];
  check false [a;b] [a];
  check false [a] [a;b];
  check false [a;b] [a;c];
  List.iter(fun h->if hyp h<>[] then failwith "inventory lemma assumptions")
    [l4_name_inventory_refl;l4_name_inventory_members;l4_ordered_history_implies_valid];
  if axioms()<>private_axioms then failwith "axiom change";
  print_endline "PRIVATE_HISTORY_INVENTORY_DONE seven_controls three_general_lemmas unchanged_axioms";;
