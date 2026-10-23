needs "tests/common.ml";;
let run_guard_controls () =
  let open Lean4hol in
  let open Early_test in
  let skip label g left right =
    let result=get label (run 100000 g [left;right]
      (fun st -> early_irrelevance st g left right)) in
    test label (result=None) in
  skip "Sort skips optional route" [] prop (Sort(Max(Zero,Zero)));
  skip "Pi skips optional route" [] p (Pi(Str(n,"renamed"),prop,Pi(n,Bvar 0,Bvar 1)));
  skip "inferred Sort skips optional route" [] (beta (Sort(Succ Zero)) prop) prop;
  let data_context=[Bvar 0;Sort(Succ Zero)] in
  let data_let=Let(n,Bvar 1,Bvar 0,Bvar 0) in
  skip "successor universe skips optional route" data_context data_let (Bvar 0);
  exact "successor fallback still proves typed conversion" data_context data_let (Bvar 0) (Bvar 1)
    (get "ordinary fallback" (convert data_context data_let (Bvar 0) (Bvar 1)));
  List.iter(fun level ->
    let g=[Bvar 1;Bvar 0;Sort level] in
    match get "equivalent-zero typed context" (run 100000 g [Bvar 0;Bvar 1]
      (fun st -> early_irrelevance st g (Bvar 0) (Bvar 1))) with
    | None -> failwith "equivalent-zero universe was excluded"
    | Some(typ,th) ->
      test "dependent proposition type retained" (typ=Bvar 2);
      exact "equivalent-zero rule10 certificate" g (Bvar 0) (Bvar 1) (Bvar 2) th)
    [Max(Zero,Zero);Imax(Param(Str(n,"u")),Zero)];
  test "helper zero fuel is skipped only for syntactic negative scheduling"
    (early_irrelevance {remaining=0} [] prop (Sort(Max(Zero,Zero)))=None);
  test "public zero fuel still reports Resource"
    (match convert ~fuel:0 [] prop (Sort(Max(Zero,Zero))) (Sort(Succ Zero)) with
     | Error {kind=Resource;_} -> true | _ -> false);
  test "performed inference Resource propagates"
    (try ignore(early_irrelevance {remaining=0} [] (beta p hp) hp);false
     with Stop {kind=Resource;_} -> true);
  test "performed inference Invalid propagates"
    (try ignore(early_irrelevance {remaining=100} [] (Bvar(-1)) hp);false
     with Stop {kind=Invalid_input;_} -> true);
  refusal "skipped shape is not acceptance" (convert [] prop (Sort(Succ Zero)) (Sort(Succ Zero)));
  refusal "malformed Pi context not trusted" (convert [] (Pi(n,Bvar 0,prop)) p prop);
  finish "guards";;
