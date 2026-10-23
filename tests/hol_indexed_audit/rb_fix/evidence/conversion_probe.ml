let rb_original_unfold tm =
  let h,args = strip_comb tm in
  match args with
  | n::_ when is_const h &&
      mem (fst(dest_const h)) ["l4_vars";"l4_decimal_aux";"l4_fresh_univ_aux"] &&
      is_numeral n && n<>`0` ->
    let rec first_argument k conv = if k=1 then RAND_CONV conv
      else RATOR_CONV(first_argument (k-1) conv) in
    (first_argument (List.length args) num_CONV THENC
      REWRITE_CONV [l4_vars;l4_decimal_aux;l4_fresh_univ_aux]) tm
  | _ -> failwith "not a successor variable list";;

let rb_saturated_unfold tm =
  let h,args = strip_comb tm in
  match args with
  | n::_ when is_const h &&
      mem (fst(dest_const h),List.length args)
        ["l4_vars",2;"l4_decimal_aux",2;"l4_fresh_univ_aux",3] &&
      is_numeral n && n<>`0` ->
    let rec first_argument k conv = if k=1 then RAND_CONV conv
      else RATOR_CONV(first_argument (k-1) conv) in
    (first_argument (List.length args) num_CONV THENC
      REWRITE_CONV [l4_vars;l4_decimal_aux;l4_fresh_univ_aux]) tm
  | _ -> failwith "not a saturated successor variable list";;

let () =
  let before=axioms() in
  let tm=`l4_vars 1 3` in
  let early=(DEPTH_CONV rb_original_unfold) tm in
  let reverted=(DEPTH_CONV rb_original_unfold THENC NUM_REDUCE_CONV) tm in
  let fixed=(DEPTH_CONV rb_saturated_unfold THENC NUM_REDUCE_CONV) tm in
  Printf.printf "RB_CONVERSION_EARLY %s\n%!" (string_of_term(rhs(concl early)));
  Printf.printf "RB_CONVERSION_REVERTED %s\n%!" (string_of_term(rhs(concl reverted)));
  Printf.printf "RB_CONVERSION_FIXED %s\n%!" (string_of_term(rhs(concl fixed)));
  if hyp fixed<>[] || not(aconv(concl fixed) `l4_vars 1 3 = [L4BVar 3]`) then
    failwith "converter probe is not a closed exact theorem";
  if before<>axioms() then failwith "converter probe changed axioms";
  print_endline "RB_CONVERSION_CLOSED_EXACT_NO_AXIOMS";;
