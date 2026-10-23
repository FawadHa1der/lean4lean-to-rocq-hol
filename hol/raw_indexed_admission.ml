(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   LCF construction of the bounded indexed raw-input admission contract. *)
needs "hol/raw_ctor_admission.ml";;
module Lean4hol_raw_indexed = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Raw=Lean4hol_raw_ctor
  module Bridge=Lean4hol_ctor_bridge
  let field = function
    | Env.Index_data a -> node "L4IndexData" [quote_expr a]
    | Env.Index_recursive xs -> node "L4IndexRecursive" [quote_context xs]
    | Env.Index_function(ds,xs) -> node "L4IndexFunction" [quote_context ds;quote_context xs]
  let fields fs=mk_list(List.map field fs,`:l4_index_field`)
  let specs cs=mk_list(List.map(fun c->node "L4IndexCtor"
    [quote_name c.Env.indexed_ctor_name;fields c.Env.indexed_fields;quote_context c.Env.result_indices])cs,
    `:l4_index_ctor`)
  let equations=Raw.equations @
    [l4_raw_index_field;l4_index_name;l4_index_fields;l4_index_result;
     l4_index_recursive;l4_index_reflexive;l4_index_positive;l4_index_pi;l4_index_dom;
     l4_index_binders;l4_index_telescope;l4_index_ctor_type;l4_index_positions;
     l4_index_args;l4_index_domains;l4_index_move;l4_index_under;l4_index_funbinders;
     l4_index_ih;l4_index_call;l4_index_ihs;l4_index_minor;l4_index_minors;
     l4_index_motive;l4_index_rec_type;l4_index_rhs;l4_index_rules;
     l4_index_header;l4_index_ctor_entries;l4_index_generated;PRE]
  let calc=REPEATC(CHANGED_CONV
    (computation THENC REWRITE_CONV equations THENC DEPTH_CONV Raw.unfold THENC NUM_REDUCE_CONV))
  let decide st tm=tick st;prove(tm,CONV_TAC calc)
  let rule st rules index args proofs =
    tick st;
    let th=SPECL args (List.nth(CONJUNCTS rules)index) in
    let result=if proofs=[] then th else
      let premise=fst(dest_imp(concl th)) in
      let evidence=EQ_MP(SYM(calc premise))(CONV_RULE calc(end_itlist CONJ proofs)) in
      MP th evidence in
    CONV_RULE calc result
  let bound v u=prove(node "l4_level_le" [quote_level v;quote_level u],
    REWRITE_TAC [l4_level_le;l4_eval_level;MAX] THEN ARITH_TAC)
  let base ds b=[Raw.entries ds;quote_name b.Env.indexed_name;Raw.names b.Env.indexed_level_params;
    number(List.length b.Env.indexed_parameters);quote_level b.Env.indexed_result_level]
  let scope st b e=decide st(node "l4_params_expr" [quote_expr e;Raw.names b.Env.indexed_level_params])
  let function_expected ds b g j domains e=node "l4_raw_index_function"
    (base ds b@[quote_context g;number j;quote_context domains;quote_expr e])
  let rec function_proof st ds b g j domains e =
    let v,hv=Raw.sort st ds g e in
    let le=bound v b.Env.indexed_result_level and scoped=scope st b e in
    let h,hh=Raw.head st ds e in
    let args=base ds b@[quote_context g;number j;quote_expr e] in
    let proof=match domains,h with
      | [],_ -> rule st l4_raw_index_function_RULES 0 (args@[quote_level v]) [hh;scoped;hv;le]
      | d::rest,Pi(n,a,body) ->
        let positive=decide st(node "l4_without_const" [quote_name b.Env.indexed_name;quote_expr a]) in
        let same=decide st(mk_eq(node "l4_anon" [quote_expr a],node "l4_anon" [quote_expr d])) in
        let w,hw=Raw.sort st ds g a in
        let tail=function_proof st ds b (a::g)(j+1)rest body in
        rule st l4_raw_index_function_RULES 1
          (args@[quote_name n;quote_expr a;quote_expr body;quote_expr d;quote_context rest;
                 quote_level v;quote_level w]) [hh;positive;same;scoped;hv;le;hw;tail]
      | _ -> stop Unsupported "raw function telescope mismatch" in
    Raw.exact(function_expected ds b g j domains e)proof
  let field_proof st ds b g j f e =
    let tm=node "l4_raw_index_field" (base ds b@[quote_context g;number j;field f;quote_expr e]) in
    let proof=match f with
      | Env.Index_data d ->
        let h,hh=Raw.head st ds e in
        let positive=decide st(node "l4_without_const" [quote_name b.Env.indexed_name;quote_expr h]) in
        let same=decide st(mk_eq(node "l4_anon" [quote_expr h],node "l4_anon" [quote_expr d])) in
        prove(tm,REWRITE_TAC [l4_raw_index_field] THEN EXISTS_TAC(quote_expr h) THEN
          REWRITE_TAC [hh;positive;same])
      | Env.Index_recursive [] ->
        let h=function_proof st ds b g j [] e in
        prove(tm,REWRITE_TAC [l4_raw_index_field;h])
      | Env.Index_function((_::_ as domains),[]) ->
        let h=function_proof st ds b g j domains e in
        prove(tm,REWRITE_TAC [l4_raw_index_field;h] THEN CONV_TAC calc)
      | _ -> stop Unsupported "raw indexed slice requires empty result indices" in
    Raw.exact tm proof
  let telescope st ds b fs typ =
    let prefix=base ds b in
    let rec field_go g j fs e = match fs,e with
      | [],_ -> Raw.exact(node "l4_raw_index_fields"
          (prefix@[quote_context g;number j;fields [];quote_expr e]))
          (rule st l4_raw_index_fields_RULES 0 (prefix@[quote_context g;number j]) [])
      | f::rest,Pi(n,a,body) ->
        let shape=field_proof st ds b g j f a in
        let v,hv=Raw.sort st ds g a in
        let tail=field_go(a::g)(j+1)rest body in
        rule st l4_raw_index_fields_RULES 1
          (prefix@[quote_context g;number j;field f;fields rest;quote_name n;quote_expr a;
                   quote_expr body;quote_level v])
          [shape;scope st b a;hv;bound v b.Env.indexed_result_level;tail]
      | _ -> stop Unsupported "raw indexed field telescope is not manifest" in
    let rec param_go g parameters e = match parameters,e with
      | [],_ -> rule st l4_raw_index_params_RULES 0
          (prefix@[quote_context g;fields fs;quote_expr e]) [field_go g 0 fs e]
      | (m,d)::rest,Pi(n,a,body) ->
        let h,hh=Raw.head st ds a in
        let same=decide st(mk_eq(node "l4_anon" [quote_expr h],node "l4_anon" [quote_expr d])) in
        let v,hv=Raw.sort st ds g a in
        let tail=param_go(a::g)rest body in
        rule st l4_raw_index_params_RULES 1
          (prefix@[quote_context g;quote_name m;quote_expr d;Raw.pars rest;fields fs;
                   quote_name n;quote_expr a;quote_expr body;quote_expr h;quote_level v])
          [hh;same;scope st b a;hv;tail]
      | _ -> stop Unsupported "raw indexed parameter telescope is not manifest" in
    param_go [] b.Env.indexed_parameters typ
  let bridge st stage env raw canonical detail =
    if List.length raw<>List.length canonical then stop Unsupported "raw indexed claim count mismatch";
    let head,args=strip_comb(concl detail) in
    if not(is_const head) || fst(dest_const head)<>"l4_index_checked" || List.length args<>12 then
      stop Unsupported "raw indexed bridge requires index anchor";
    let definition=SPECL [Env.quote_policy env;Raw.entries canonical] l4_bridge_index_anchor in
    let rec exists tm = function
      | [] -> Raw.exact tm detail
      | x::xs -> let v,body=dest_exists tm in EXISTS(tm,x)(exists(vsubst[x,v]body)xs) in
    let anchor=EQ_MP(SYM definition)
      (exists(rhs(concl definition))(List.init 10(fun j->List.nth args(j+1)))) in
    let terms=[Env.quote_policy env;Env.quote_env env;Raw.entries raw;Raw.entries canonical] in
    let definition=SPECL terms l4_index_ctor_conversion_bridge in
    let obligations=conjuncts(rhs(concl definition)) in
    if List.length obligations<>8 then stop Proof_failure "indexed bridge obligation mismatch";
    stage:="indexed bridge metadata and forward guards";
    let static=Env.certificate env::anchor::List.map(fun j->
      tick st;prove(List.nth obligations j,CONV_TAC Bridge.calc THEN MESON_TAC []))[2;3;4;5;6] in
    let entries=List.map2(Bridge.entry st stage env)raw canonical in
    let all_entries=prove(List.nth obligations 7,REWRITE_TAC(ALL2::entries)) in
    Raw.exact(node "l4_index_ctor_conversion_bridge" terms)
      (EQ_MP(SYM definition)(end_itlist CONJ(static@[all_entries])))
  let expected prior next raw canonical=node "l4_raw_indexed_admitted"
    [Env.quote_policy prior;Env.quote_env prior;Raw.entries raw;Raw.entries canonical;Env.quote_env next]
  let certify ?(fuel=100000) prior next raw b =
    let stage=ref "indexed anchor" in
    let result=run fuel [] [] (fun st ->
      if b.Env.indices<>[] || b.Env.indexed_result_level<>Succ Zero then
        stop Unsupported "raw indexed slice requires Type0 and no indices";
      let canonical=b.Env.indexed_claims in
      let header=match raw with h::_->h | []->stop Unsupported "missing raw indexed header" in
      let detail=Raw.get(Env.inductive_certificate next b.Env.indexed_name) in
      let _,args=strip_comb(concl detail) in
      if List.length args<>12 then stop Unsupported "raw indexed admission requires indexed anchor";
      let expected_detail=[Env.quote_policy prior;Env.quote_env prior;quote_name b.Env.indexed_name;
        Raw.names b.Env.indexed_level_params;Raw.pars b.Env.indexed_parameters;Raw.pars [];
        quote_level b.Env.indexed_result_level;specs b.Env.indexed_constructors;List.nth args 8;
        `T`;`F`;Raw.entries canonical] in
      ignore(Raw.exact(node "l4_index_checked" expected_detail)detail);
      let constructors=List.filter(fun d->match d.Env.kind with
        | Env.Generated(Env.Constructor_role _)->true|_->false)raw in
      if List.length constructors<>List.length b.Env.indexed_constructors then
        stop Unsupported "raw indexed constructor count mismatch";
      let fragment=header::Env.declarations prior in
      stage:="prior header formation";
      let hheader=Raw.sort_exists st (Env.declarations prior) [] header.Env.typ in
      let proofs=List.map2(fun c d ->
        if c.Env.indexed_ctor_name<>d.Env.name || c.Env.result_indices<>[] then
          stop Unsupported "raw indexed constructor name or result mismatch";
        stage:="header-only constructor formation";
        let formation=Raw.sort_exists st fragment [] d.Env.typ in
        stage:="typed directed function telescope";
        let checked=telescope st fragment b c.Env.indexed_fields d.Env.typ in
        formation,checked)b.Env.indexed_constructors constructors in
      let rawargs=[Env.quote_env prior;quote_name b.Env.indexed_name;Raw.names b.Env.indexed_level_params;
        Raw.pars b.Env.indexed_parameters;quote_level b.Env.indexed_result_level;
        specs b.Env.indexed_constructors;Raw.entries raw] in
      stage:="raw indexed obligations";
      let hraw=prove(node "l4_raw_index_obligations" rawargs,
        REWRITE_TAC [l4_raw_index_obligations] THEN CONV_TAC calc THEN
        REWRITE_TAC(hheader::List.concat_map(fun(a,b)->[a;b])proofs)) in
      let hbridge=bridge st stage next raw canonical detail in
      stage:="raw indexed admission assembly";
      let terms=[Env.quote_policy prior;Env.quote_env prior;Raw.entries raw;Raw.entries canonical;Env.quote_env next] in
      let definition=SPECL terms l4_raw_indexed_admitted in
      let witnesses=List.map(fun j->List.nth expected_detail j)[2;3;4;6;7;8] in
      let rec exists tm = function
        | [] -> prove(tm,REWRITE_TAC [detail;hraw;hbridge] THEN CONV_TAC calc)
        | x::xs -> let v,body=dest_exists tm in EXISTS(tm,x)(exists(vsubst[x,v]body)xs) in
      Raw.exact(expected prior next raw canonical)
        (EQ_MP(SYM definition)(CONJ(Env.certificate next)(exists(rand(rhs(concl definition)))witnesses)))) in
    match result with Ok _->result | Error e->Error {e with message="raw indexed " ^ !stage ^ ": " ^ e.message}
end;;
