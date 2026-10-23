(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Certificate factory only; it does not mutate an environment. *)
needs "hol/text_contracts.ml";;
needs "hol/environment.ml";;

let l4_text_definition_checked_raw = prove
 (`!policy env n ps a b.
    l4_text_definition_contract (l4_checked policy env) n ps a b ==>
    l4_text_definition_contract (l4_edef env) n ps a b`,
  MESON_TAC [l4_text_definition_mono;l4_checked_typing]);;

module Lean4hol_text : sig
  type certificate
  val check_definition : ?fuel:int -> Lean4hol_env.environment -> Lean4hol_env.declaration ->
    (certificate,Lean4hol.error) result
  val declaration : certificate -> Lean4hol_env.declaration
  val theorem : certificate -> thm
  val raw_theorem : certificate -> thm
end = struct
  open Lean4hol
  module Env = Lean4hol_env
  type certificate = {input:Env.declaration;proof:thm;raw:thm}
  let declaration c = c.input
  let theorem c = c.proof
  let raw_theorem c = c.raw
  let n s = Str(Anonymous,s)
  let char = Const(n "Char",[])
  let text = Const(n "String",[])
  let nat = Const(n "Nat",[])
  let list_char = App(Const(n "List",[Zero]),char)
  let nil = App(Const(Str(n "List","nil"),[Zero]),char)
  let cons = App(Const(Str(n "List","cons"),[Zero]),char)
  let arrow a b = Pi(Anonymous,a,b)
  let char_signature = arrow nat char
  let string_signature = arrow list_char text
  let cons_signature = arrow char (arrow list_char list_char)
  let notation = [l4_text_char_name;l4_text_string_name;l4_text_list_name;
    l4_text_of_nat_name;l4_text_of_list_name;l4_text_char;l4_text_string;
    l4_text_list_char;l4_text_nil;l4_text_cons;l4_text_char_signature;
    l4_text_string_signature;l4_text_cons_signature;l4_prim_nat;l4_nat_name]
  let equations = notation @ [l4_text_definition_header;l4_anon;l4_params_expr;
    l4_params_level;ALL;MEM;distinctness "l4_name";injectivity "l4_name";
    distinctness "list";injectivity "list";distinctness "l4_expr";injectivity "l4_expr"]
  let calc = REWRITE_CONV equations THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let get = function Ok x -> x | Error e -> raise(Stop e)
  let guard expected h =
    if hyp h<>[] || frees(concl h)<>[] || not(aconv(concl h)expected) then
      stop Proof_failure "text primitive certificate mismatch";
    h
  let judgment env = node "l4_checked" [Env.quote_policy env;Env.quote_env env]
  let checked fuel env e ty = guard
    (list_mk_comb(judgment env,[quote_context [];quote_expr e;quote_expr e;quote_expr ty]))
    (get(Env.check ~fuel env [] e ty))
  let ensure_type fuel env e =
    let ty,_ = get(Env.infer ~fuel env [] e) in
    let result = match ty with Sort _ -> ty | _ ->
      let result,_,_ = get(Env.normalize ~fuel env [] ty) in result in
    let u = match result with Sort u -> u | _ -> stop Proof_failure "text interface expected a type" in
    let h = checked fuel env e (Sort u) in
    let target = node "l4_text_is_type" [judgment env;quote_expr e] in
    let expansion = REWR_CONV l4_text_is_type target in
    guard target (EQ_MP (SYM expansion) (EXISTS(rhs(concl expansion),quote_level u) h))
  let contract fuel env b char_op =
    let def,kind,proofs = if char_op then
      l4_text_char_contract,"l4_text_char_contract",
      [checked fuel env nat (Sort(Succ Zero));ensure_type fuel env char;
       checked fuel env b char_signature]
    else l4_text_string_contract,"l4_text_string_contract",
      [ensure_type fuel env list_char;ensure_type fuel env char;
       checked fuel env nil list_char;checked fuel env cons cons_signature;
       checked fuel env b string_signature] in
    let target = node kind [judgment env;quote_expr b] in
    let expansion = REWRITE_RULE notation (REWR_CONV def target) in
    guard target (EQ_MP (SYM expansion) (end_itlist CONJ proofs))
  let check_definition ?(fuel=100000) env d =
    run fuel [] (d.Env.typ::Sort(Param d.Env.name)::
      List.map(fun n -> Sort(Param n))d.Env.params) (fun st ->
      let b = match d.Env.kind,d.Env.value with
        | Env.Definition,Some b -> b
        | Env.Definition,None -> stop Invalid_input "text primitive definition requires a body"
        | _ -> stop Unsupported "text primitive factory requires a definition" in
      validate st [] [b];
      let char_op = if d.Env.name=Str(n "Char","ofNat") then true
        else if d.Env.name=Str(n "String","ofList") then false
        else stop Unsupported "not a text primitive name" in
      let fields = [quote_name d.Env.name;mk_list(List.map quote_name d.Env.params,`:l4_name`);
        quote_expr d.Env.typ;quote_expr b] in
      tick st;
      let hh = prove(node "l4_text_definition_header" fields,CONV_TAC calc) in
      let ht = ensure_type fuel env d.Env.typ in
      let hb = checked fuel env b d.Env.typ in
      let hop = contract fuel env b char_op in
      let target = node "l4_text_definition_contract" (judgment env::fields) in
      let expansion = REWR_CONV l4_text_definition_contract target in
      let cases = List.nth(conjuncts(rhs(concl expansion)))3 in
      let hc = prove(cases,CONV_TAC(REWRITE_CONV(hop::equations) THENC
        NUM_REDUCE_CONV THENC REWRITE_CONV [])) in
      let proof = guard target (EQ_MP(SYM expansion)(end_itlist CONJ[hh;ht;hb;hc])) in
      let raw = guard
        (node "l4_text_definition_contract" (node "l4_edef" [Env.quote_env env]::fields))
        (MATCH_MP l4_text_definition_checked_raw proof) in
      {input=d;proof;raw})
end;;
