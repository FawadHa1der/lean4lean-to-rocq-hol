needs "tests/common.ml";;
let run_early_typed () =
  let open Lean4hol in
  let open Early_test in
  List.iter(fun(typ,proof)->
    ignore(get "inhabited proposition" (check [] typ prop));
    List.iter(fun other->
      let budget={remaining=100000} in
      let answer=early_irrelevance budget [] other proof in
      (match answer with
       | None->failwith "actual typed early branch failed"
       | Some(inferred,th)->
         test "original proposition type retained" (inferred=typ);
         exact "actual rule10 proof" [] other proof typ th);
      test "early attempt spends the same supplied budget" (budget.remaining<100000 && budget.remaining>0);
      exact "public pure conversion" [] other proof typ
        (get "public conversion" (convert [] other proof typ));
      checked Lean4hol_env.empty [] other proof typ
        (get "public checked conversion" (Lean4hol_env.convert Lean4hol_env.empty [] other proof typ)))
      [beta typ proof;zeta typ proof]) [p,hp;q,hq];
  refusal "different proof types are not erased" (convert [] hp hq p);
  test "helper preserves Resource"
    (try ignore(early_irrelevance {remaining=0} [] (beta p hp) hp);false
     with Stop {kind=Resource;_}->true);
  test "helper preserves Invalid_input"
    (try ignore(early_irrelevance {remaining=100} [] (Bvar(-1)) hp);false
     with Stop {kind=Invalid_input;_}->true);
  finish "typed";;
