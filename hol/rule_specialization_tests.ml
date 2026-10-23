(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   This uses synthetic environments only to compare rule specialization.
   It does not claim that these environments have been admitted. *)
needs "hol/environment.ml";;

let l4_rule_specialization_tests () =
  let open Lean4hol in
  let before=axioms() in
  let count=ref 0 in
  let check label b=if not b then failwith("rule specialization: "^label);
    incr count in
  let entry j = node "L4Entry" [`L4AxiomKind`;
    quote_name(Str(Anonymous,"benchmark"^string_of_int j));`[]:l4_name list`;
    quote_expr(Sort Zero);quote_expr(Sort Zero)] in
  let env=mk_list(List.init 100 entry,`:l4_entry`) in
  let symbolic=genvar(type_of env) in
  let rules=CONJUNCTS l4_edef_RULES in
  let eager rule=CONV_RULE computation (SPEC env rule) in
  let delayed rule=INST [env,symbolic]
    (CONV_RULE computation (SPEC symbolic rule)) in
  List.iter (fun rule ->
    let a=eager rule and b=delayed rule in
    check "same exact conclusion" (aconv(concl a)(concl b));
    check "eager closed" (hyp a=[]);
    check "delayed closed" (hyp b=[])) rules;
  let measure f =
    let start=Sys.time() in
    for i=1 to 100 do ignore(f(List.nth rules 1)) done;
    Sys.time()-.start in
  let old_seconds=measure eager and new_seconds=measure delayed in
  Printf.printf "HOL_RULE_SPECIALIZATION_BENCH eager_cpu=%.6f delayed_cpu=%.6f rules=%d entries=100 repetitions=100\n"
    old_seconds new_seconds (List.length rules);
  check "no new axioms" (axioms()=before);
  print_endline("HOL_RULE_SPECIALIZATION_TESTS_PASSED "^string_of_int !count);;

l4_rule_specialization_tests ();;
