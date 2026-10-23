(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Explicit opt-in only. Ordinary delegated checks retain individual fuel caps. *)
needs "hol/shift_left_context_evaluation.ml";;
needs "hol/shift_left_budget.ml";;
needs "hol/environment.ml";;

module Lean4hol_derived_shift_left : sig
  type certificate
  val prepare : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr list ->
    add:Lean4hol.expr -> mul:Lean4hol.expr -> Lean4hol.expr ->
    (certificate,Lean4hol.error) result
  val prepare_from_contract : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr list ->
    add:Lean4hol.expr -> mul:Lean4hol.expr -> Lean4hol.expr -> thm ->
    (certificate,Lean4hol.error) result
  val evaluate : ?fuel:int -> ?max_output_bits:int -> certificate -> string -> string ->
    (Lean4hol.expr * thm,Lean4hol.error) result
  val check_result : ?fuel:int -> ?max_output_bits:int -> certificate ->
    string -> string -> string -> (thm,Lean4hol.error) result
  val theorem : certificate -> thm
  val contract : certificate -> thm
  val body : certificate -> Lean4hol.expr
  val context : certificate -> Lean4hol.expr list
end = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Budget=Lean4hol_shift_left_budget
  type certificate={source:expr;gamma:expr list;judgment:term;law:thm;evaluation:thm}
  let theorem c=c.evaluation
  let contract c=c.law
  let body c=c.source
  let context c=c.gamma
  let get=function Ok x->x | Error e->raise(Stop e)
  let guard expected th=
    if hyp th<>[] || frees(concl th)<>[] || not(aconv(concl th) expected) then
      stop Proof_failure "derived shiftLeft certificate mismatch";
    th
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2
  let nn=Str(Anonymous,"Nat")
  let nat=Const(nn,[])
  let zero=Const(Str(nn,"zero"),[])
  let successor=Const(Str(nn,"succ"),[])
  let unary=Pi(Anonymous,nat,nat)
  let binary=Pi(Anonymous,nat,unary)
  let app2 b x y=App(App(b,x),y)
  let succ x=App(successor,x)
  let notation=[APPEND;l4_prim_binary;l4_prim_unary;l4_prim_nat;
    l4_prim_two;l4_prim_one;l4_prim_zero;l4_prim_succ;l4_nat_name]
  let relative env gamma=
    let delta=`delta:l4_expr list` in
    mk_abs(delta,node "l4_checked" [Env.quote_policy env;Env.quote_env env;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;quote_context gamma])])
  let expected_contract env gamma add mul source=node "l4_prim_shift_left_contract"
    [relative env gamma;quote_expr add;quote_expr mul;quote_expr source]
  let checked env g a b ty h=guard(node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr a;quote_expr b;quote_expr ty]) h
  let check fuel env g e ty=checked env g e e ty(get(Env.check ~fuel env g e ty))
  let convert fuel env g a b=checked env g a b nat(get(Env.convert ~fuel env g a b nat))
  let scope e=prove(node "l4_scoped" [quote_expr e;`0`],
    REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV)
  let assemble fuel env gamma add mul source law =
    let law=guard(expected_contract env gamma add mul source) law in
    let scopes=List.map scope [add;mul;source] in
    let qe=Env.quote_env env and qp=Env.quote_policy env and qg=quote_context gamma in
    let qa=quote_expr add and qm=quote_expr mul and qb=quote_expr source in
    let raw_law=MATCH_MP(SPECL [qp;qe;qg;qa;qm;qb] l4_shift_left_context_checked_raw) law in
    let hn=check fuel env gamma nat (Sort(Succ Zero)) in
    let hn1=check fuel env (nat::gamma) nat (Sort(Succ Zero)) in
    let hz=check fuel env gamma zero nat and hs=check fuel env gamma successor unary in
    let all=MP(REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qa;qm;qb] l4_edef_shift_left_evaluation_in_context))
      (end_itlist CONJ(scopes@[raw_law;raw hn;raw hn1;raw hz;raw hs])) in
    let valid,ctx=match CONJUNCTS(REWRITE_RULE [l4_checked] hn) with
      | [a;b;_]->a,b | _->stop Proof_failure "checked Nat premise shape" in
    let m=`m:num` and n=`n:num` in
    let call=node "L4App" [node "L4App" [qb;node "L4NatLit" [m]];node "L4NatLit" [n]] in
    let result=node "L4NatLit" [node "*" [m;node "EXP" [`2`;n]]] in
    let judgment=node "l4_checked" [qp;qe] in
    let expected=list_mk_comb(judgment,[qg;call;result;quote_expr nat]) in
    let evaluation=GENL [m;n](EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
      (CONJ valid(CONJ ctx(SPECL [m;n] all)))) in
    {source;gamma;judgment;law;evaluation=guard(list_mk_forall([m;n],expected)) evaluation}
  let prepare_from_contract ?(fuel=100000) env gamma ~add ~mul source law =
    run fuel [] (add::mul::source::gamma)(fun _->assemble fuel env gamma add mul source law)
  let prepare ?(fuel=100000) env gamma ~add ~mul source =
    run fuel [] (add::mul::source::gamma)(fun _->
      List.iter(fun e->ignore(scope e))[add;mul;source];
      let j=relative env gamma in
      let at b=check fuel env gamma b binary in
      let base b result=convert fuel env (nat::gamma)(app2 b (Bvar 0) zero) result in
      let step b result=convert fuel env (nat::nat::gamma)
        (app2 b (Bvar 1)(succ(Bvar 0))) result in
      let aeq=REWRITE_RULE notation(SPECL [j;quote_expr add] l4_prim_add_contract) in
      let alaw=EQ_MP(SYM aeq)(end_itlist CONJ
        [at add;base add(Bvar 0);step add(succ(app2 add(Bvar 1)(Bvar 0)))]) in
      let meq=REWRITE_RULE notation(SPECL [j;quote_expr add;quote_expr mul] l4_prim_mul_contract) in
      let mlaw=EQ_MP(SYM meq)(end_itlist CONJ
        [alaw;at mul;base mul zero;step mul(app2 add(app2 mul(Bvar 1)(Bvar 0))(Bvar 1))]) in
      let seq=REWRITE_RULE notation(REWR_CONV l4_prim_shift_left_contract
        (expected_contract env gamma add mul source)) in
      let law=EQ_MP(SYM seq)(end_itlist CONJ
        [mlaw;at source;base source(Bvar 0);
         step source(app2 source(app2 mul(succ(succ zero))(Bvar 1))(Bvar 0))]) in
      assemble fuel env gamma add mul source law)
  let allocation_bound max_output_bits left shift =
    match Budget.check ~max_output_bits left shift with
    | Budget.Allowed->()
    | Budget.Invalid msg->stop Invalid_input msg
    | Budget.Exhausted msg->stop Resource msg
  let evaluate ?(fuel=100000) ?(max_output_bits=4096) c left shift =
    run fuel [] [] (fun st->
      allocation_bound max_output_bits left shift;
      validate st [] [Natlit left;Natlit shift];
      let m=natural left and n=natural shift in
      let expression=node "*" [m;node "EXP" [`2`;n]] in
      (* Simplify a zero multiplier before numeral evaluation of the exponent. *)
      let arithmetic=(REWRITE_CONV [MULT_CLAUSES] THENC NUM_REDUCE_CONV) expression in
      let answer=rhs(concl arithmetic) in
      let result=Natlit(string_of_num(dest_numeral answer)) in
      let expected=list_mk_comb(c.judgment,[quote_context c.gamma;
        quote_expr(app2 c.source(Natlit left)(Natlit shift));quote_expr result;quote_expr nat]) in
      let proof=REWRITE_RULE [arithmetic](SPECL [m;n] c.evaluation) in
      result,guard expected proof)
  let check_result ?(fuel=100000) ?(max_output_bits=4096) c left shift answer =
    run fuel [] [] (fun st->
      if String.length answer>16384 then stop Resource "shiftLeft claimed output length cap";
      validate st [] [Natlit answer];
      let actual,proof=get(evaluate ~fuel ~max_output_bits c left shift) in
      if actual<>Natlit answer then stop Proof_failure "shiftLeft claimed result mismatch";
      proof)
end;;
