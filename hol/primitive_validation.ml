(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Proof-producing contracts only: no environment mutation or reduction. *)
needs "hol/primitive_contracts.ml";;
needs "hol/environment.ml";;

let l4_prim_definition_checked_raw = prove
 (`!policy env n ps a b.
    l4_prim_definition_contract (l4_checked policy env) n ps a b ==>
    l4_prim_definition_contract (l4_edef env) n ps a b`,
  MESON_TAC [l4_prim_definition_mono;l4_checked_typing]);;

let l4_prim_checked_conversion = prove
 (`!policy env g a a' e e' u.
    l4_checked policy env g a a' (L4Sort u) /\
    l4_checked policy env g e e' a ==>
    l4_checked policy env g e e' a'`,
  REWRITE_TAC [l4_checked] THEN
  MESON_TAC [List.nth (CONJUNCTS l4_edef_RULES) 5]);;

module Lean4hol_primitive : sig
  type add_certificate
  type pred_certificate
  type sub_certificate
  type mul_certificate
  type pow_certificate
  type shift_left_certificate
  type beq_certificate
  type ble_certificate
  type definition_certificate
  val check_add : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr ->
    (add_certificate,Lean4hol.error) result
  val check_pred : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr ->
    (pred_certificate,Lean4hol.error) result
  val check_sub : ?fuel:int -> Lean4hol_env.environment -> pred_certificate -> Lean4hol.expr ->
    (sub_certificate,Lean4hol.error) result
  val check_mul : ?fuel:int -> Lean4hol_env.environment -> add_certificate -> Lean4hol.expr ->
    (mul_certificate,Lean4hol.error) result
  val check_pow : ?fuel:int -> Lean4hol_env.environment -> mul_certificate -> Lean4hol.expr ->
    (pow_certificate,Lean4hol.error) result
  val check_shift_left : ?fuel:int -> Lean4hol_env.environment -> mul_certificate -> Lean4hol.expr ->
    (shift_left_certificate,Lean4hol.error) result
  val check_beq : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr ->
    (beq_certificate,Lean4hol.error) result
  val check_ble : ?fuel:int -> Lean4hol_env.environment -> Lean4hol.expr ->
    (ble_certificate,Lean4hol.error) result
  val add_body : add_certificate -> Lean4hol.expr
  val pred_body : pred_certificate -> Lean4hol.expr
  val sub_body : sub_certificate -> Lean4hol.expr
  val mul_body : mul_certificate -> Lean4hol.expr
  val pow_body : pow_certificate -> Lean4hol.expr
  val shift_left_body : shift_left_certificate -> Lean4hol.expr
  val beq_body : beq_certificate -> Lean4hol.expr
  val ble_body : ble_certificate -> Lean4hol.expr
  val add_theorem : add_certificate -> thm
  val pred_theorem : pred_certificate -> thm
  val sub_theorem : sub_certificate -> thm
  val mul_theorem : mul_certificate -> thm
  val pow_theorem : pow_certificate -> thm
  val shift_left_theorem : shift_left_certificate -> thm
  val beq_theorem : beq_certificate -> thm
  val ble_theorem : ble_certificate -> thm
  val check_definition : ?fuel:int -> Lean4hol_env.environment -> Lean4hol_env.declaration ->
    (definition_certificate,Lean4hol.error) result
  val definition_declaration : definition_certificate -> Lean4hol_env.declaration
  val definition_theorem : definition_certificate -> thm
  val definition_raw_theorem : definition_certificate -> thm
end = struct
  open Lean4hol
  module Env = Lean4hol_env
  type certified = {body:expr;judgment:term;proof:thm}
  type add_certificate = Add of certified
  type pred_certificate = Pred of certified
  type sub_certificate = Sub of certified
  type mul_certificate = Mul of certified * add_certificate
  type pow_certificate = Pow of certified
  type shift_left_certificate = Shift_left of certified
  type beq_certificate = Beq of certified
  type ble_certificate = Ble of certified
  type definition_certificate = {declaration:Env.declaration;checked_proof:thm;raw_proof:thm}
  let add_body (Add c) = c.body
  let pred_body (Pred c) = c.body
  let sub_body (Sub c) = c.body
  let mul_body (Mul(c,_)) = c.body
  let pow_body (Pow c) = c.body
  let shift_left_body (Shift_left c) = c.body
  let beq_body (Beq c) = c.body
  let ble_body (Ble c) = c.body
  let add_theorem (Add c) = c.proof
  let pred_theorem (Pred c) = c.proof
  let sub_theorem (Sub c) = c.proof
  let mul_theorem (Mul(c,_)) = c.proof
  let pow_theorem (Pow c) = c.proof
  let shift_left_theorem (Shift_left c) = c.proof
  let beq_theorem (Beq c) = c.proof
  let ble_theorem (Ble c) = c.proof
  let definition_declaration c = c.declaration
  let definition_theorem c = c.checked_proof
  let definition_raw_theorem c = c.raw_proof
  let nat = Str(Anonymous,"Nat")
  let nt = Const(nat,[])
  let zero = Const(Str(nat,"zero"),[])
  let succ e = App(Const(Str(nat,"succ"),[]),e)
  let unary = Pi(Anonymous,nt,nt)
  let binary = Pi(Anonymous,nt,unary)
  let bool = Str(Anonymous,"Bool")
  let bt = Const(bool,[])
  let fal = Const(Str(bool,"false"),[])
  let tru = Const(Str(bool,"true"),[])
  let bool_binary = Pi(Anonymous,nt,Pi(Anonymous,nt,bt))
  let app2 f x y = App(App(f,x),y)
  let judgment env = node "l4_checked" [Env.quote_policy env;Env.quote_env env]
  let get = function Ok h -> h | Error e -> raise(Stop e)
  let guard tm h =
    if hyp h<>[] || not(aconv (concl h) tm) then
      stop Proof_failure "primitive certificate conclusion or hypotheses mismatch";
    h
  let checked env g a b ty h = guard
    (list_mk_comb(judgment env,[quote_context g;quote_expr a;quote_expr b;quote_expr ty])) h
  let check fuel env b ty = checked env [] b b ty (get(Env.check ~fuel env [] b ty))
  let convert fuel env g a b = checked env g a b nt (get(Env.convert ~fuel env g a b nt))
  let notation = [l4_prim_nat;l4_prim_zero;l4_prim_succ;l4_prim_one;l4_prim_two;l4_prim_unary;
    l4_prim_binary;l4_nat_name;l4_prim_bool;l4_prim_false;l4_prim_true;
    l4_prim_bool_binary;l4_bool_name]
  let finish env b def dependencies proofs =
    let j=judgment env in
    let eq=REWRITE_RULE notation
      (SPECL (j::List.map quote_expr (dependencies@[b])) def) in
    let h=EQ_MP (SYM eq) (end_itlist CONJ proofs) in
    {body=b;judgment=j;proof=guard (lhs(concl eq)) h}
  let same_environment env c =
    if not(aconv (judgment env) c.judgment) then
      stop Unsupported "primitive dependency requires the same certified environment and policy"
  let check_add ?(fuel=100000) env b = run fuel [] [b] (fun _ ->
    let ht=check fuel env b binary in
    let hz=convert fuel env [nt] (app2 b (Bvar 0) zero) (Bvar 0) in
    let hs=convert fuel env [nt;nt] (app2 b (Bvar 1) (succ(Bvar 0)))
      (succ(app2 b (Bvar 1) (Bvar 0))) in
    Add(finish env b l4_prim_add_contract [] [ht;hz;hs]))
  let check_pred ?(fuel=100000) env b = run fuel [] [b] (fun _ ->
    let ht=check fuel env b unary in
    let hz=convert fuel env [] (App(b,zero)) zero in
    let hs=convert fuel env [nt] (App(b,succ(Bvar 0))) (Bvar 0) in
    Pred(finish env b l4_prim_pred_contract [] [ht;hz;hs]))
  let check_sub ?(fuel=100000) env (Pred p) b = run fuel [] [b] (fun _ ->
    same_environment env p;
    let ht=check fuel env b binary in
    let hz=convert fuel env [nt] (app2 b (Bvar 0) zero) (Bvar 0) in
    let hs=convert fuel env [nt;nt] (app2 b (Bvar 1) (succ(Bvar 0)))
      (App(p.body,app2 b (Bvar 1) (Bvar 0))) in
    Sub(finish env b l4_prim_sub_contract [p.body] [p.proof;ht;hz;hs]))
  let check_mul ?(fuel=100000) env ((Add a) as ac) b = run fuel [] [b] (fun _ ->
    same_environment env a;
    let ht=check fuel env b binary in
    let hz=convert fuel env [nt] (app2 b (Bvar 0) zero) zero in
    let hs=convert fuel env [nt;nt] (app2 b (Bvar 1) (succ(Bvar 0)))
      (app2 a.body (app2 b (Bvar 1) (Bvar 0)) (Bvar 1)) in
    Mul(finish env b l4_prim_mul_contract [a.body] [a.proof;ht;hz;hs],ac))
  let check_pow ?(fuel=100000) env (Mul(m,Add a)) b = run fuel [] [b] (fun _ ->
    same_environment env m;
    same_environment env a;
    let ht=check fuel env b binary in
    let hz=convert fuel env [nt] (app2 b (Bvar 0) zero) (succ zero) in
    let hs=convert fuel env [nt;nt] (app2 b (Bvar 1) (succ(Bvar 0)))
      (app2 m.body (app2 b (Bvar 1) (Bvar 0)) (Bvar 1)) in
    let j=judgment env in
    let statement=node "l4_prim_pow_contract"
      [j;quote_expr a.body;quote_expr m.body;quote_expr b] in
    let expansion=REWRITE_RULE notation (REWR_CONV l4_prim_pow_contract statement) in
    let h=EQ_MP (SYM expansion) (end_itlist CONJ [m.proof;ht;hz;hs]) in
    Pow{body=b;judgment=j;proof=guard statement h})
  let check_shift_left ?(fuel=100000) env (Mul(m,Add a)) b = run fuel [] [b] (fun _ ->
    same_environment env m;
    same_environment env a;
    let ht=check fuel env b binary in
    let hz=convert fuel env [nt] (app2 b (Bvar 0) zero) (Bvar 0) in
    let hs=convert fuel env [nt;nt] (app2 b (Bvar 1) (succ(Bvar 0)))
      (app2 b (app2 m.body (succ(succ zero)) (Bvar 1)) (Bvar 0)) in
    let j=judgment env in
    let statement=node "l4_prim_shift_left_contract"
      [j;quote_expr a.body;quote_expr m.body;quote_expr b] in
    let expansion=REWRITE_RULE notation (REWR_CONV l4_prim_shift_left_contract statement) in
    let h=EQ_MP (SYM expansion) (end_itlist CONJ [m.proof;ht;hz;hs]) in
    Shift_left{body=b;judgment=j;proof=guard statement h})

  let check_bool_cases fuel env b b0s kind def =
    let eq g x y=checked env g x y bt (get(Env.convert ~fuel env g x y bt)) in
    let ht=check fuel env b bool_binary in
    let h00=eq [] (app2 b zero zero) tru in
    let h0s=eq [nt] (app2 b zero (succ(Bvar 0))) b0s in
    let hs0=eq [nt] (app2 b (succ(Bvar 0)) zero) fal in
    let hss=eq [nt;nt] (app2 b (succ(Bvar 1)) (succ(Bvar 0)))
      (app2 b (Bvar 1) (Bvar 0)) in
    let j=judgment env in
    let statement=node kind [j;quote_expr b] in
    let expansion=REWRITE_RULE (l4_prim_bool_cases_contract::notation)
      (REWR_CONV def statement) in
    let h=EQ_MP (SYM expansion) (end_itlist CONJ [ht;h00;h0s;hs0;hss]) in
    {body=b;judgment=j;proof=guard statement h}
  let check_beq ?(fuel=100000) env b = run fuel [] [b] (fun _ ->
    Beq(check_bool_cases fuel env b fal "l4_prim_beq_contract" l4_prim_beq_contract))
  let check_ble ?(fuel=100000) env b = run fuel [] [b] (fun _ ->
    Ble(check_bool_cases fuel env b tru "l4_prim_ble_contract" l4_prim_ble_contract))

  let header_equations = notation @
    [l4_prim_add_name;l4_prim_pred_name;l4_prim_sub_name;l4_prim_mul_name;
     l4_prim_beq_name;l4_prim_ble_name;l4_prim_pow_name;l4_prim_shift_left_name;
     l4_prim_definition_header;l4_anon;l4_params_expr;l4_params_level;ALL;MEM;
     distinctness "l4_name";injectivity "l4_name";distinctness "list";injectivity "list";
     distinctness "l4_expr";injectivity "l4_expr"]
  let header_calc = REWRITE_CONV header_equations THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let add_body_typing fuel env b ty hop =
    if frees(concl hop)<>[] then
      stop Proof_failure "open primitive add contract";
    let hop=guard (node "l4_prim_add_contract" [judgment env;quote_expr b]) hop in
    let hb=checked env [] b b binary
      (REWRITE_RULE notation (CONJUNCT1(REWRITE_RULE [l4_prim_add_contract] hop))) in
    if ty=binary then hb else
    let level=Sort(Succ Zero) in
    let equality=checked env [] binary ty level
      (get(Env.convert ~fuel env [] binary ty level)) in
    let conversion=SPECL [Env.quote_policy env;Env.quote_env env;quote_context [];
      quote_expr binary;quote_expr ty;quote_expr b;quote_expr b;`L4Succ L4Zero`]
      l4_prim_checked_conversion in
    checked env [] b b ty (MP conversion (CONJ equality hb))
  let check_definition ?(fuel=100000) env d =
    run fuel [] (d.Env.typ::Sort(Param d.Env.name)::
      List.map (fun n -> Sort(Param n)) d.Env.params) (fun st ->
      let b=match d.Env.kind,d.Env.value with
        | Env.Definition,Some b -> b
        | Env.Definition,None -> stop Invalid_input "primitive definition requires a body"
        | _ -> stop Unsupported "primitive contract factory requires a definition" in
      validate st [] [b];
      let op=if d.Env.name=Str(nat,"add") then 0 else
        if d.Env.name=Str(nat,"pred") then 1 else
        if d.Env.name=Str(nat,"sub") then 2 else
        if d.Env.name=Str(nat,"mul") then 3 else
        if d.Env.name=Str(nat,"beq") then 4 else
        if d.Env.name=Str(nat,"ble") then 5 else
        if d.Env.name=Str(nat,"pow") then 6 else
        if d.Env.name=Str(nat,"shiftLeft") then 7 else
        stop Unsupported "primitive declaration contract is not implemented for this name" in
      let fields=[quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b] in
      tick st;
      let hh=prove(node "l4_prim_definition_header" fields,CONV_TAC header_calc) in
      let hop=match op with
        | 0 -> add_theorem(get(check_add ~fuel env b))
        | 1 -> pred_theorem(get(check_pred ~fuel env b))
        | 2 -> let pc=get(check_pred ~fuel env (Const(Str(nat,"pred"),[]))) in
          sub_theorem(get(check_sub ~fuel env pc b))
        | 3 -> let ac=get(check_add ~fuel env (Const(Str(nat,"add"),[]))) in
          mul_theorem(get(check_mul ~fuel env ac b))
        | 4 -> beq_theorem(get(check_beq ~fuel env b))
        | 5 -> ble_theorem(get(check_ble ~fuel env b))
        | 6 | 7 -> let ac=get(check_add ~fuel env (Const(Str(nat,"add"),[]))) in
          let mc=get(check_mul ~fuel env ac (Const(Str(nat,"mul"),[]))) in
          if op=6 then pow_theorem(get(check_pow ~fuel env mc b))
          else shift_left_theorem(get(check_shift_left ~fuel env mc b))
        | _ -> stop Unsupported "primitive declaration operation is not implemented" in
      let ht=check fuel env d.Env.typ (Sort(Succ Zero)) in
      let hb=if op=0 then add_body_typing fuel env b d.Env.typ hop
        else if (op=4 || op=5) && d.Env.typ=bool_binary then
          checked env [] b b d.Env.typ (REWRITE_RULE notation
            (MATCH_MP (if op=4 then l4_prim_beq_body_typed else l4_prim_ble_body_typed) hop))
        else if (op=6 || op=7) && d.Env.typ=binary then
          checked env [] b b d.Env.typ (REWRITE_RULE notation
            (MATCH_MP (if op=6 then l4_prim_pow_body_typed
              else l4_prim_shift_left_body_typed) hop))
        else check fuel env b d.Env.typ in
      let eq=REWR_CONV l4_prim_definition_contract
        (node "l4_prim_definition_contract" (judgment env::fields)) in
      let cases=List.nth (conjuncts(rhs(concl eq))) 3 in
      let hc=prove(cases,CONV_TAC (REWRITE_CONV (hop::header_equations) THENC
        NUM_REDUCE_CONV THENC REWRITE_CONV [])) in
      let proof=guard (lhs(concl eq)) (EQ_MP (SYM eq) (end_itlist CONJ [hh;ht;hb;hc])) in
      let raw=guard (node "l4_prim_definition_contract" (node "l4_edef" [Env.quote_env env]::fields))
        (MATCH_MP l4_prim_definition_checked_raw proof) in
      {declaration=d;checked_proof=proof;raw_proof=raw})
end;;
