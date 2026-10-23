let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/bool_context_evaluation.ml";;

let run_bool_general () =
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let expected op checked =
    let env=`env:l4_entry list` and g=`g:l4_expr list` and body=`body:l4_expr`
    and policy=`policy:l4_entry list` and m=`m:num` and n=`n:num` in
    let raw=mk_comb(`l4_edef`,env) in
    let j gamma a b ty=list_mk_comb(raw,[gamma;a;b;ty]) in
    let nt=`l4_prim_nat` and bt=`l4_prim_bool` and level=`L4Sort (L4Succ L4Zero)` in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,mk_comb(raw,list_mk_comb
      (`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;g]))) in
    let law=list_mk_comb((if op="beq" then `l4_prim_beq_contract` else `l4_prim_ble_contract`),
      [relative;body]) in
    let successor=`L4Const (L4String l4_nat_name [115;117;99;99]) []` in
    let premises=[list_mk_comb(`l4_scoped`,[body;`0`]);law;
      j g nt nt level;j(list_mk_comb(`CONS:l4_expr->l4_expr list->l4_expr list`,[nt;g]))nt nt level;
      j g `l4_prim_zero` `l4_prim_zero` nt;j g successor successor `l4_prim_unary`;
      j g bt bt level;j g `l4_prim_true` `l4_prim_true` bt;
      j g `l4_prim_false` `l4_prim_false` bt] in
    let premises=if checked then list_mk_comb(`l4_evalid`,[policy;env])::
      list_mk_comb(`l4_econtext`,[env;g])::premises else premises in
    let call=list_mk_comb(`L4App`,[list_mk_comb(`L4App`,[body;mk_comb(`L4NatLit`,m)]);
      mk_comb(`L4NatLit`,n)]) in
    let condition=if op="beq" then mk_eq(m,n) else list_mk_comb(`(<=):num->num->bool`,[m;n]) in
    let answer=mk_cond(condition,`l4_prim_true`,`l4_prim_false`) in
    let result=if checked then list_mk_comb(`l4_checked`,[policy;env;g;call;answer;bt])
      else j g call answer bt in
    let statement=list_mk_forall((if checked then [policy;env;g;body] else [env;g;body]),
      mk_imp(list_mk_conj premises,list_mk_forall([m;n],result))) in
    rhs(concl(REWRITE_CONV [l4_prim_nat;l4_prim_bool;l4_prim_zero;l4_prim_unary;
      l4_prim_true;l4_prim_false] statement)) in
  List.iter(fun (op,raw,empty,checked)->
    test (op^" exact raw general statement") (aconv(concl raw)(expected op false));
    test (op^" exact checked general statement") (aconv(concl checked)(expected op true));
    List.iter(fun th->test (op^" closed theorem") (hyp th=[] && frees(concl th)=[]))
      [raw;empty;checked];
    let env=`env:l4_entry list` and g=`g:l4_expr list` and b=`body:l4_expr` in
    let specialized=SPECL [env;g;b] raw in
    let premise,_=dest_imp(concl specialized) in
    let parts=CONJUNCTS(ASSUME premise) in
    test (op^" exact nine raw premises") (List.length parts=9);
    List.iteri(fun i _->
      let remaining=List.filteri(fun k _->i<>k)parts in
      test (op^" omitted premise "^string_of_int i)
        (try ignore(MP specialized(end_itlist CONJ remaining));false with Failure _->true)) parts;
    let conditional=MP specialized(ASSUME premise) in
    test (op^" assumptions never discharged by evaluation") (hyp conditional<>[]);
    print_string("EXACT_THEOREM "^op^"_raw\n");print_thm raw;print_newline();
    print_string("EXACT_THEOREM "^op^"_checked\n");print_thm checked;print_newline())
    ["beq",l4_edef_beq_evaluation_in_context,l4_edef_beq_evaluation_context_empty,
      l4_checked_beq_evaluation_in_context;
     "ble",l4_edef_ble_evaluation_in_context,l4_edef_ble_evaluation_context_empty,
      l4_checked_ble_evaluation_in_context];
  test "native rule count unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission rule count unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "\nCOMPOSED_WORK_PASS bool-general %d\n%!" !count;;
