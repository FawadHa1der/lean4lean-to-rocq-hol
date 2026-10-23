(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Opt-in contextual comparison certificates. No default runtime dispatch. *)
needs "hol/bool_context_evaluation.ml";;
needs "hol/environment.ml";;

module Lean4hol_derived_bool : sig
  type operation = Beq | Ble
  type certificate
  val prepare : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr list ->
    operation -> Lean4hol.expr -> (certificate,Lean4hol.error) result
  val of_contract : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr list ->
    operation -> Lean4hol.expr -> thm -> (certificate,Lean4hol.error) result
  val evaluate : ?fuel:int -> certificate -> string -> string ->
    (Lean4hol.expr * thm,Lean4hol.error) result
  val theorem : certificate -> thm
  val contract : certificate -> thm
  val body : certificate -> Lean4hol.expr
  val context : certificate -> Lean4hol.expr list
end = struct
  open Lean4hol
  module Env=Lean4hol_env
  type operation = Beq | Ble
  type certificate={source:expr;gamma:expr list;op:operation;judgment:term;
    evaluation:thm;law:thm}
  let theorem c=c.evaluation
  let contract c=c.law
  let body c=c.source
  let context c=c.gamma
  let get=function Ok x->x | Error e->raise(Stop e)
  let guard expected th =
    if hyp th<>[] || frees(concl th)<>[] || not(aconv(concl th) expected) then
      stop Proof_failure "derived Boolean certificate mismatch";
    th
  let nn=Str(Anonymous,"Nat") and bn=Str(Anonymous,"Bool")
  let nat=Const(nn,[]) and bool=Const(bn,[])
  let zero=Const(Str(nn,"zero"),[]) and successor=Const(Str(nn,"succ"),[])
  let tru=Const(Str(bn,"true"),[]) and fal=Const(Str(bn,"false"),[])
  let unary=Pi(Anonymous,nat,nat)
  let binary=Pi(Anonymous,nat,Pi(Anonymous,nat,bool))
  let app2 f x y=App(App(f,x),y)
  let name=function Beq->"l4_prim_beq_contract" | Ble->"l4_prim_ble_contract"
  let definition=function Beq->l4_prim_beq_contract | Ble->l4_prim_ble_contract
  let evaluation=function Beq->l4_edef_beq_evaluation_in_context
    | Ble->l4_edef_ble_evaluation_in_context
  let relative judgment gamma =
    let delta=`delta:l4_expr list` in
    mk_abs(delta,mk_comb(judgment,list_mk_comb
      (`APPEND:l4_expr list->l4_expr list->l4_expr list`,[delta;quote_context gamma])))
  let notation=[APPEND;l4_prim_bool_cases_contract;l4_prim_bool_binary;
    l4_prim_bool;l4_prim_nat;l4_prim_zero;l4_prim_succ;
    l4_prim_true;l4_prim_false;l4_nat_name;l4_bool_name]
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2
  let of_contract ?(fuel=100000) env gamma op source law =
    run fuel [] (source::gamma) (fun _->
      let qe=Env.quote_env env and qp=Env.quote_policy env
      and qg=quote_context gamma and qb=quote_expr source in
      let judgment=node "l4_checked" [qp;qe] in
      let expected=node (name op) [relative judgment gamma;qb] in
      let law=guard expected law in
      let checked g a b ty th=guard(list_mk_comb(judgment,
        [quote_context g;quote_expr a;quote_expr b;quote_expr ty])) th in
      let check g e ty=checked g e e ty(get(Env.check ~fuel env g e ty)) in
      let scope=prove(node "l4_scoped" [qb;`0`],
        REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
      let parts=CONJUNCTS(REWRITE_RULE(definition op::notation) law) in
      if List.length parts<>5 then stop Proof_failure "comparison contract arity";
      let raw_contract=node(name op)[relative(node "l4_edef" [qe]) gamma;qb] in
      let equation=REWRITE_CONV(definition op::notation) raw_contract in
      let raw_law=EQ_MP(SYM equation)(end_itlist CONJ(List.map raw parts)) in
      let hn=check gamma nat (Sort(Succ Zero)) in
      let hn1=check (nat::gamma) nat (Sort(Succ Zero)) in
      let hz=check gamma zero nat and hs=check gamma successor unary in
      let hbool=check gamma bool (Sort(Succ Zero)) in
      let ht=check gamma tru bool and hf=check gamma fal bool in
      let all=MP(REWRITE_RULE [l4_nat_name;l4_bool_name]
        (SPECL [qe;qg;qb](evaluation op)))
        (end_itlist CONJ [scope;raw_law;raw hn;raw hn1;raw hz;raw hs;
          raw hbool;raw ht;raw hf]) in
      let valid,ctx=match CONJUNCTS(REWRITE_RULE [l4_checked] hn) with
        | [a;b;_]->a,b | _->stop Proof_failure "checked Nat premise shape" in
      let m=`m:num` and n=`n:num` in
      let condition=match op with Beq->mk_eq(m,n) | Ble->node "<=" [m;n] in
      let call=node "L4App" [node "L4App" [qb;node "L4NatLit" [m]];node "L4NatLit" [n]] in
      let expected=list_mk_comb(judgment,[qg;call;
        mk_cond(condition,quote_expr tru,quote_expr fal);quote_expr bool]) in
      let proof=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected))
        (CONJ valid(CONJ ctx(SPECL [m;n] all))) in
      let evaluation=guard(list_mk_forall([m;n],expected))(GENL [m;n] proof) in
      {source;gamma;op;judgment;evaluation;law})
  let prepare ?(fuel=100000) env gamma op source =
    run fuel [] (source::gamma) (fun _->
      let qe=Env.quote_env env and qp=Env.quote_policy env in
      let judgment=node "l4_checked" [qp;qe] in
      let checked g a b ty th=guard(list_mk_comb(judgment,
        [quote_context g;quote_expr a;quote_expr b;quote_expr ty])) th in
      let check g e ty=checked g e e ty(get(Env.check ~fuel env g e ty)) in
      let convert g a b=checked g a b bool(get(Env.convert ~fuel env g a b bool)) in
      let typed=check gamma source binary in
      let zz=convert gamma (app2 source zero zero) tru in
      let zs=convert (nat::gamma) (app2 source zero (App(successor,Bvar 0)))
        (match op with Beq->fal | Ble->tru) in
      let sz=convert (nat::gamma) (app2 source (App(successor,Bvar 0)) zero) fal in
      let ss=convert (nat::nat::gamma)
        (app2 source (App(successor,Bvar 1)) (App(successor,Bvar 0)))
        (app2 source (Bvar 1) (Bvar 0)) in
      let statement=node(name op)[relative judgment gamma;quote_expr source] in
      let equation=REWRITE_CONV(definition op::notation) statement in
      let law=EQ_MP(SYM equation)(end_itlist CONJ [typed;zz;zs;sz;ss]) in
      get(of_contract ~fuel env gamma op source law))
  let evaluate ?(fuel=100000) c left right =
    run fuel [] [Natlit left;Natlit right] (fun _->
      let m=natural left and n=natural right in
      let condition=match c.op with Beq->mk_eq(m,n) | Ble->node "<=" [m;n] in
      let truth=rhs(concl(NUM_REDUCE_CONV condition)) in
      let result=if truth=`T` then tru else if truth=`F` then fal
        else stop Proof_failure "Boolean numeral comparison unresolved" in
      let expected=list_mk_comb(c.judgment,[quote_context c.gamma;
        quote_expr(app2 c.source (Natlit left) (Natlit right));
        quote_expr result;quote_expr bool]) in
      let proof=CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV [])
        (SPECL [m;n] c.evaluation) in
      result,guard expected proof)
end;;
