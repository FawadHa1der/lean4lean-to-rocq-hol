(* SPDX-License-Identifier: Apache-2.0
   Synthetic extraction/allocation controls, not logical Arena verdicts. *)
module C = Whnf_policy_native
let assertions = ref 0
let check label value = incr assertions; if not value then failwith label
let rec nat = function 0 -> C.O | n -> C.S(nat(n-1))
let int_of_nat value =
  let rec loop acc = function C.O -> acc | C.S n -> loop(acc+1)n in loop 0 value
let sort = C.ESort C.LZero
let () =
  check "normal exact upstream default" (int_of_nat C.normal_whnf_rounds=100000);
  check "eager exact upstream default" (int_of_nat C.eager_whnf_rounds=1000000);
  check "normal selects shared immutable limit" (C.whnf_round_limit C.NormalReduction == C.normal_whnf_rounds);
  check "eager selects shared immutable limit" (C.whnf_round_limit C.EagerReduction == C.eager_whnf_rounds);
  for _=1 to 1000 do
    check "normal selection does not recreate unary budget"
      (C.whnf_round_limit C.NormalReduction == C.normal_whnf_rounds);
    check "eager selection does not recreate unary budget"
      (C.whnf_round_limit C.EagerReduction == C.eager_whnf_rounds)
  done;
  for depth=0 to 32 do
    for rounds=0 to 35 do
      let calls=ref [] in
      let step e = calls:=e::!calls; match e with
        | C.EBVar C.O -> C.Accept(C.WhnfDone sort)
        | C.EBVar(C.S n) -> C.Accept(C.WhnfContinue(C.EBVar n))
        | _ -> C.Reject C.TypeMismatch in
      check "independent round result"
        (C.run_whnf_rounds(nat rounds)step(C.EBVar(nat depth))=
          if rounds>depth then C.Accept sort else C.Decline C.OutOfFuel);
      check "one callback per actual round" (List.length !calls=min rounds(depth+1));
      check "exact decreasing order" (List.rev !calls=
        List.init(min rounds(depth+1))(fun i -> C.EBVar(nat(depth-i))))
    done
  done;
  let errors=List.map(fun e -> C.Reject e) [C.UnknownConstant;C.UnknownFreeVariable;
    C.LooseBoundVariable;C.UnknownUniverse;C.UniverseArity;C.ExpectedSort;C.ExpectedPi;
    C.TypeMismatch;C.NotDefinitionallyEqual;C.DuplicateDeclaration;C.DuplicateUniverse;
    C.MalformedDeclaration;C.MetaVariable] @ List.map(fun d -> C.Decline d)
    [C.OutOfFuel;C.UnsupportedExpression;C.UnsupportedDeclaration] in
  List.iter(fun result -> for rounds=0 to 4 do
    let calls=ref 0 in
    let step _ = incr calls; result in
    let expected=match result with C.Reject e -> C.Reject e | C.Decline d -> C.Decline d
      | C.Accept _ -> failwith "error fixture" in
    check "exact error propagation" (C.run_whnf_rounds(nat rounds)step sort=
      if rounds=0 then C.Decline C.OutOfFuel else expected);
    check "no extra error callback" (!calls=(if rounds=0 then 0 else 1))
  done) errors;
  for rounds=0 to 16 do
    let calls=ref 0 in
    let step e = incr calls; C.Accept(C.WhnfContinue e) in
    check "cycle resource decline" (C.run_whnf_rounds(nat rounds)step sort=C.Decline C.OutOfFuel);
    check "cycle exact callback bound" (!calls=rounds)
  done;
  Printf.printf "WHNF_POLICY_CALLBACKS_PASS assertions=%d\n%!" !assertions
