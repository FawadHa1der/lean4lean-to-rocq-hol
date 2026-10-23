needs "hol/private_boot.ml";;
let run_bridge_static_tests () =
  let module Bridge=Lean4hol_ctor_bridge in
  let module Core=Lean4hol in
  let count=ref 0 in
  let test label condition=if not condition then failwith label else incr count in
  let exact tm h=
    test "exact conclusion" (aconv tm (concl h));
    test "closed proof" (hyp h=[] && frees(concl h)=[]) in
  let good=`l4_params_expr (L4Sort L4Zero) []` in
  exact good (Bridge.static_premise good);
  let bad=`l4_anon (L4Sort L4Zero) = l4_anon (L4BVar 0)` in
  exact (mk_eq(bad,`F`)) (Bridge.calc bad);
  test "false metadata premise is only a proof failure"
    (try ignore(Bridge.static_premise bad);false with
     Core.Stop {Core.kind=Core.Proof_failure;_}->true | _->false);
  let residual=`!P:num->bool. (!n. P n) ==> P 0` in
  test "residual premise really needs inference" (rhs(concl(Bridge.calc residual))<>`T`);
  exact residual (Bridge.static_premise residual);
  test "native count" (private_native_rule_count=29);
  test "admission count" (private_admission_rule_count=11);
  test "no new axioms" (axioms()=private_axioms);
  Printf.printf "PRIVATE_BRIDGE_STATIC_DONE %d_assertions certified_false_is_decline unchanged_axioms\n%!" !count;;
run_bridge_static_tests ();;
