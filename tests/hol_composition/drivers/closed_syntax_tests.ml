let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/closed_syntax.ml";;
needs "hol/core.ml";;
let run_closed_syntax_cases () =
  let open Lean4hol in
  let assertions=ref 0 in
  let test label ok=incr assertions;if not ok then failwith label in
  let failure f=try ignore(f());false with Failure _->true in
  let an=Anonymous and name=Str(Anonymous,"OpaqueName") in
  let z=Sort Zero and a=Sort(Succ Zero) in
  let closed=[z;Sort(Imax(Param name,Succ Zero));Const(name,[Param name]);
    App(Const(name,[]),z);Lam(an,a,Bvar 0);Pi(an,a,Bvar 0);
    Lam(an,a,Lam(an,a,Bvar 1));Let(an,a,z,Bvar 0);
    Natlit "10000000000000000000000000000000000000000";
    Proj(name,19,Lam(an,a,Bvar 0));Strlit "";Strlit "Lean"] in
  let certify expected proof =
    test "exact certificate" (aconv(concl proof) expected);
    test "closed certificate" (hyp proof=[] && frees(concl proof)=[]) in
  List.iter(fun e->
    let qe=quote_expr e in
    let scoped=node "l4_scoped" [qe;`0`] in
    let scope=prove(scoped,REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    certify scoped scope;
    let lift_rule=MP(SPEC qe l4_lift_closed) scope
    and subst_rule=MP(SPEC qe l4_subst_closed) scope
    and inst_rule=MP(SPEC qe l4_inst_closed) scope in
    List.iter(fun d->List.iter(fun k->
      let expected=mk_eq(node "l4_lift" [qe;number d;number k],qe) in
      certify expected (SPECL [number d;number k] lift_rule)
    ) [0;1;19]) [0;1;17];
    List.iter(fun s->
      let qs=quote_expr s in
      certify (mk_eq(node "l4_inst" [qs;qe],qe)) (SPEC qs inst_rule);
      List.iter(fun k->certify (mk_eq(node "l4_subst" [qe;number k;qs],qe))
        (SPECL [number k;qs] subst_rule)) [0;1;19]
    ) [Bvar 0;Bvar 7;Lam(an,Bvar 0,Bvar 1)]
  ) closed;
  List.iter(fun h->test "general theorem closed" (hyp h=[] && frees(concl h)=[]))
    [l4_lift_scoped;l4_subst_scoped;l4_scoped_mono;l4_lift_closed;l4_subst_closed;l4_inst_closed];
  List.iter(fun i->
    let q=quote_expr(Bvar i) in
    let open_term=node "l4_scoped" [q;`0`] in
    let denied=prove(mk_neg open_term,REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    certify (mk_neg open_term) denied;
    test "unrelated scope certificate refused" (failure(fun()->
      MP(SPEC q l4_lift_closed) (prove(node "l4_scoped" [quote_expr z;`0`],
        REWRITE_TAC [l4_scoped]))));
    let shifted=(REWRITE_CONV [l4_lift] THENC NUM_REDUCE_CONV)
      (node "l4_lift" [q;`1`;`0`]) in
    test "unbound variable really shifts" (not(aconv (rhs(concl shifted)) q))
  ) [0;1;19];
  let not_typed=`l4_scoped (L4StrLit [1114112]) 0` in
  certify not_typed (prove(not_typed,REWRITE_TAC [l4_scoped]));
  test "scope does not introduce typing rules" (List.length(CONJUNCTS l4_defeq_RULES)=13);
  test "no new axioms" (axioms()=before_axioms);
  Printf.printf "PRIVATE_CLOSED_SYNTAX_CASES_DONE %d_assertions twelve_closed_terms unchanged_axioms\n%!" !assertions;;
run_closed_syntax_cases ();;
exit 0;;
