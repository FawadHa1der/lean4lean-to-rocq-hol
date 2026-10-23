needs "tests/common.ml";;
let run_early_observer variant =
  let open Lean4hol in
  let open Early_test in
  List.iter(fun(other,proof,typ)->
    let bodies=ref 0 and successes=ref 0 and comparisons=ref 0 in
    test_early_observer := (fun tag _ left right ->
      if tag="whnf" && (left=other || left=proof) then incr bodies;
      if tag="equal" && left=other && right=proof then incr comparisons;
      if tag="early-success" && left=other && right=proof then incr successes);
    let result=convert [] other proof typ in
    test_early_observer := (fun _ _ _ _->());
    exact "observed conversion remains exact and closed" [] other proof typ
      (get "observed conversion" result);
    test "observer reached the actual comparison" (!comparisons>0);
    if variant="baseline" then (
      test "baseline evaluates a proof body" (!bodies>0);
      test "baseline has no early success" (!successes=0))
    else (
      test "candidate does not WHNF either proof body" (!bodies=0);
      test "candidate completed actual early branch" (!successes>0));
    Printf.printf "EARLY_OBSERVE %s comparisons=%d proof_whnf=%d early_success=%d\n%!"
      variant !comparisons !bodies !successes)
    [beta p hp,hp,p;zeta q hq,hq,q];
  finish("observer-"^variant);;
