(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/core.ml";;
needs "hol/declarations.ml";;

module Lean4hol_admit : sig
  type kind = Definition | Theorem
  type declaration = {
    kind : kind; name : Lean4hol.name; params : Lean4hol.name list;
    typ : Lean4hol.expr; value : Lean4hol.expr
  }
  type environment
  val empty : environment
  val declarations : environment -> declaration list
  val quote_decl : declaration -> term
  val quote_env : environment -> term
  val certificate : environment -> thm
  val admit : ?fuel:int -> environment -> declaration ->
    (environment * thm, Lean4hol.error) result
  val check : ?fuel:int -> environment -> Lean4hol.expr -> Lean4hol.expr ->
    (thm, Lean4hol.error) result
end = struct
  open Lean4hol
  type kind = Definition | Theorem
  type declaration = {
    kind : kind; name : name; params : name list; typ : expr; value : expr
  }
  type environment = { decls : declaration list; proof : thm }
  let empty = {decls=[];proof=CONJUNCT1 l4_admitted_RULES}
  let declarations env = env.decls
  let certificate env = env.proof
  let quote_kind = function Definition -> `L4Definition` | Theorem -> `L4Theorem`
  let quote_params ps = mk_list(List.map quote_name ps,`:l4_name`)
  let quote_levels us = mk_list(List.map quote_level us,`:l4_level`)
  let quote_decl d = node "L4Decl"
    [quote_kind d.kind;quote_name d.name;quote_params d.params;quote_expr d.typ;quote_expr d.value]
  let quote_env env = mk_list(List.map quote_decl env.decls,`:l4_decl`)
  let guarded target th =
    if hyp th <> [] || not(aconv (concl th) target) then
      stop Proof_failure "declaration certificate mismatch";
    th
  let equations =
    [l4_decl_name;l4_names_distinct;l4_params_expr;l4_params_level;
     l4_expr_lsubst;l4_level_lsubst;l4_lparam;MEM;MAP;ALL;LENGTH;HD;TL;
     distinctness "l4_name";injectivity "l4_name";
     distinctness "list";injectivity "list"]
  let calc = REWRITE_CONV equations THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let objcalc = DEPTH_CONV (fun tm ->
    let head,_ = strip_comb tm in
    if is_const head && mem (fst(dest_const head)) ["l4_expr_lsubst";"LENGTH"]
    then CHANGED_CONV calc tm else failwith "not declaration computation")
  let decide st tm = tick st; prove(tm,CONV_TAC calc)
  let rules = Array.of_list(CONJUNCTS l4_expand_RULES)
  let expand_rule st i args premises =
    tick st;
    let h = CONV_RULE objcalc (SPECL args rules.(i)) in
    match premises with [] -> h | _ -> MP h (end_itlist CONJ premises)

  let instantiate = instantiate_levels

  let rec expand st env e =
    tick st;
    let qe = quote_env env in
    let e',h = match e with
    | Bvar i -> e,expand_rule st 0 [qe;number i] []
    | Natlit n -> e,expand_rule st 7 [qe;natural n] []
    | Strlit s -> e,expand_rule st 9 [qe;quote_string s] []
    | Proj(owner,idx,major) ->
      let major',h = expand st env major in
      Proj(owner,idx,major'),expand_rule st 8
        [qe;quote_name owner;number idx;quote_expr major;quote_expr major'] [h]
    | Sort u -> e,expand_rule st 1 [qe;quote_level u] []
    | App(f,a) ->
      let f',hf = expand st env f and a',ha = expand st env a in
      App(f',a'),expand_rule st 2 [qe;quote_expr f;quote_expr a;quote_expr f';quote_expr a'] [hf;ha]
    | Lam(n,a,b) | Pi(n,a,b) ->
      let a',ha = expand st env a and b',hb = expand st env b in
      let i,e' = match e with Lam _ -> 3,Lam(n,a',b') | _ -> 4,Pi(n,a',b') in
      e',expand_rule st i
        [qe;quote_name n;quote_expr a;quote_expr b;quote_expr a';quote_expr b'] [ha;hb]
    | Let(n,a,v,b) ->
      let a',ha = expand st env a and v',hv = expand st env v and b',hb = expand st env b in
      Let(n,a',v',b'),expand_rule st 5
        [qe;quote_name n;quote_expr a;quote_expr v;quote_expr b;
         quote_expr a';quote_expr v';quote_expr b'] [ha;hv;hb]
    | Const(n,us) ->
      let d = try List.find (fun d -> d.name=n) env.decls with Not_found ->
        stop Unsupported "constant is not in the admitted transparent environment" in
      if List.length us <> List.length d.params then
        stop Proof_failure "constant universe argument count mismatch";
      let v',hv = expand st env d.value in
      let result = instantiate st d.params us v' in
      let member = decide st (mk_comb(mk_comb(
        mk_const("MEM",[`:l4_decl`,`:A`]),quote_decl d),qe)) in
      let arity = decide st (mk_eq(number(List.length d.params),number(List.length us))) in
      result,expand_rule st 6
        [qe;quote_kind d.kind;quote_name d.name;quote_params d.params;quote_expr d.typ;
         quote_expr d.value;quote_levels us;quote_expr v'] [member;arity;hv] in
    e',guarded (node "l4_expand" [qe;quote_expr e;quote_expr e']) h

  let admit ?(fuel=100000) env d =
    run fuel [] [d.typ;d.value;Sort(Param d.name);
      Const(Anonymous,List.map (fun p -> Param p) d.params)] (fun st ->
      ignore(guarded (node "l4_admitted" [quote_env env]) env.proof);
      let names = List.map (fun d -> d.name) env.decls in
      if List.mem d.name names then stop Proof_failure "duplicate declaration name";
      let a,ha = expand st env d.typ in
      let v,hv = expand st env d.value in
      let u,hty = infer_sort st [] a in
      let hval = check_i st [] v a in
      let step = SPECL
        [quote_env env;quote_kind d.kind;quote_name d.name;quote_params d.params;
         quote_expr d.typ;quote_expr d.value;quote_expr a;quote_expr v;quote_level u]
        (CONJUNCT2 l4_admitted_RULES) in
      let conditions = conjuncts (fst(dest_imp(concl step))) in
      let at i = decide st (List.nth conditions i) in
      let theorem_type = match d.kind with
        | Definition -> prove(List.nth conditions 9,
            REWRITE_TAC [distinctness "l4_decl_kind"])
        | Theorem -> DISCH (fst(dest_imp(List.nth conditions 9)))
            (check_i st [] a (Sort Zero)) in
      let proof = MP step (end_itlist CONJ
        [env.proof;at 1;at 2;at 3;at 4;ha;hv;hty;hval;theorem_type]) in
      let result = {decls=d::env.decls;proof} in
      result,guarded (node "l4_admitted" [quote_env result]) proof)

  let check ?(fuel=100000) env e a =
    run fuel [] [e;a] (fun st ->
      ignore(guarded (node "l4_admitted" [quote_env env]) env.proof);
      let e',he = expand st env e in
      let a',ha = expand st env a in
      let h = check_i st [] e' a' in
      let th = MP (SPECL [quote_env env;quote_expr e;quote_expr a;quote_expr e';quote_expr a']
        l4_env_has_type_RULES) (end_itlist CONJ [env.proof;he;ha;h]) in
      guarded (node "l4_env_has_type" [quote_env env;quote_expr e;quote_expr a]) th)
end;;
