(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Opt-in theorem-producing evaluation; each delegated check has its own fuel cap. *)
needs "hol/add_context_evaluation.ml";;
needs "hol/environment.ml";;

module Lean4hol_derived_add : sig
  type certificate
  val prepare : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr list ->
    Lean4hol.expr -> (certificate,Lean4hol.error) result
  val evaluate : ?fuel:int -> certificate -> string -> string ->
    (Lean4hol.expr * thm,Lean4hol.error) result
  val theorem : certificate -> thm
  val body : certificate -> Lean4hol.expr
  val context : certificate -> Lean4hol.expr list
end = struct
  open Lean4hol
  module Env=Lean4hol_env
  type certificate={source:expr;gamma:expr list;judgment:term;evaluation:thm}
  let theorem c=c.evaluation
  let body c=c.source
  let context c=c.gamma
  let get=function Ok x->x | Error e->raise(Stop e)
  let guard expected th =
    if hyp th<>[] || frees(concl th)<>[] || not(aconv(concl th) expected) then
      stop Proof_failure "derived addition certificate mismatch";
    th
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2
  let nn=Str(Anonymous,"Nat")
  let nat=Const(nn,[])
  let zero=Const(Str(nn,"zero"),[])
  let successor=Const(Str(nn,"succ"),[])
  let unary=Pi(Anonymous,nat,nat)
  let prepare ?(fuel=100000) env gamma source = run fuel [] (source::gamma) (fun _->
    let qe=Env.quote_env env and qp=Env.quote_policy env
    and qg=quote_context gamma and qb=quote_expr source in
    let judgment=node "l4_checked" [qp;qe] in
    let checked g a b ty th=guard(list_mk_comb(judgment,
      [quote_context g;quote_expr a;quote_expr b;quote_expr ty])) th in
    let check g e ty=checked g e e ty(get(Env.check ~fuel env g e ty)) in
    let convert g a b=checked g a b nat(get(Env.convert ~fuel env g a b nat)) in
    let scope=prove(node "l4_scoped" [qb;`0`],
      REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
    let typed=check gamma source (Pi(Anonymous,nat,unary)) in
    let base=convert (nat::gamma) (App(App(source,Bvar 0),zero)) (Bvar 0) in
    let step=convert (nat::nat::gamma)
      (App(App(source,Bvar 1),App(successor,Bvar 0)))
      (App(successor,App(App(source,Bvar 1),Bvar 0))) in
    let delta=`delta:l4_expr list` in
    let relative=mk_abs(delta,node "l4_edef" [qe;
      list_mk_comb(`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;qg])]) in
    let equation=REWRITE_RULE [APPEND;l4_prim_binary;l4_prim_unary;
      l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_nat_name]
      (SPECL [relative;qb] l4_prim_add_contract) in
    let contract=EQ_MP(SYM equation)(end_itlist CONJ [raw typed;raw base;raw step]) in
    let hn=check gamma nat (Sort(Succ Zero)) in
    let hn1=check (nat::gamma) nat (Sort(Succ Zero)) in
    let hz=check gamma zero nat and hs=check gamma successor unary in
    let all=MP(REWRITE_RULE [l4_nat_name]
      (SPECL [qe;qg;qb] l4_edef_add_evaluation_in_context))
      (end_itlist CONJ [scope;contract;raw hn;raw hn1;raw hz;raw hs]) in
    let valid,ctx=match CONJUNCTS(REWRITE_RULE [l4_checked] hn) with
      | [a;b;_]->a,b | _->stop Proof_failure "checked Nat premise shape" in
    let m=`m:num` and n=`n:num` in
    let call=node "L4App" [node "L4App" [qb;node "L4NatLit" [m]];node "L4NatLit" [n]] in
    let expected=list_mk_comb(judgment,[qg;call;node "L4NatLit" [node "+" [m;n]];quote_expr nat]) in
    let instantiated=SPECL [m;n] all in
    let evaluation=GENL [m;n](EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
      (CONJ valid(CONJ ctx instantiated))) in
    let evaluation=guard(list_mk_forall([m;n],expected)) evaluation in
    {source;gamma;judgment;evaluation})
  let evaluate ?(fuel=100000) c left right = run fuel [] [Natlit left;Natlit right] (fun _->
    let m=natural left and n=natural right in
    let sum=rhs(concl(NUM_REDUCE_CONV(node "+" [m;n]))) in
    let result=Natlit(string_of_num(dest_numeral sum)) in
    let call=App(App(c.source,Natlit left),Natlit right) in
    let expected=list_mk_comb(c.judgment,[quote_context c.gamma;quote_expr call;
      quote_expr result;quote_expr nat]) in
    let proof=CONV_RULE NUM_REDUCE_CONV(SPECL [m;n] c.evaluation) in
    result,guard expected proof)
end;;
