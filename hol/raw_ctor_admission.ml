(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Raw input admission, separate from the canonical execution representation. *)
needs "hol/reducible_bridge.ml";;
needs "hol/raw_indexed_syntax.ml";;

let l4_raw_family_obligations = new_definition
 `!prior i ps pars u cs raw. l4_raw_family_obligations prior i ps pars u cs raw <=>
    ~(raw = []) /\ l4_entry_name (HD raw) = i /\
    (?v. l4_raw_sort prior [] (l4_entry_type (HD raw)) v) /\
    ALL2 (\c d. l4_ctor_name c = l4_entry_name d /\
      (?v. l4_raw_sort (CONS (HD raw) prior) [] (l4_entry_type d) v) /\
      l4_raw_params (CONS (HD raw) prior) i ps (LENGTH pars) u [] pars
        (l4_ctor_fields c) (l4_entry_type d)) cs
      (FILTER (\d. l4_is_constructor_kind (l4_entry_tag d)) raw)`;;
let l4_raw_family_slice = new_definition
 `!u cs. l4_raw_family_slice u cs <=>
    u = L4Succ L4Zero \/
    (l4_level_nonzero u /\
     ALL (\c. ALL (\f. ~l4_is_recursive f) (l4_ctor_fields c)) cs)`;;
let l4_raw_family_slice_type0 = prove
 (`!cs. l4_raw_family_slice (L4Succ L4Zero) cs`,
  REWRITE_TAC [l4_raw_family_slice]);;
let l4_raw_family_admitted = new_definition
 `!policy prior raw canonical env. l4_raw_family_admitted policy prior raw canonical env <=>
    l4_evalid policy env /\
    (?i ps pars u cs vss large k.
      l4_family_checked policy prior i ps pars u cs vss large k canonical /\
      canonical = l4_family_generated i ps pars u cs large k /\
      env = APPEND canonical prior /\ l4_raw_family_slice u cs /\
      l4_raw_family_obligations prior i ps pars u cs raw /\
      l4_ctor_conversion_bridge policy env raw canonical)`;;

let l4_raw_generated_admitted = new_definition
 `!policy prior raw canonical env.
    l4_raw_generated_admitted policy prior raw canonical env <=>
    l4_raw_family_admitted policy prior raw canonical env \/
    l4_raw_indexed_admitted policy prior raw canonical env`;;
let l4_raw_family_generated = prove
 (`!policy prior raw canonical env.
    l4_raw_family_admitted policy prior raw canonical env ==>
    l4_raw_generated_admitted policy prior raw canonical env`,
  SIMP_TAC [l4_raw_generated_admitted]);;
let l4_raw_indexed_generated = prove
 (`!policy prior raw canonical env.
    l4_raw_indexed_admitted policy prior raw canonical env ==>
    l4_raw_generated_admitted policy prior raw canonical env`,
  SIMP_TAC [l4_raw_generated_admitted]);;
let l4_raw_generated_valid = prove
 (`!policy prior raw canonical env.
    l4_raw_generated_admitted policy prior raw canonical env ==>
    l4_evalid policy env`,
  REWRITE_TAC [l4_raw_generated_admitted;l4_raw_family_admitted;
               l4_raw_indexed_admitted] THEN MESON_TAC []);;

let l4_input_trace_RULES,l4_input_trace_INDUCT,l4_input_trace_CASES = new_inductive_definition
 `(!policy. l4_input_trace policy [] []) /\
  (!policy prior history raw ds.
    l4_input_trace policy prior history /\ l4_evalid policy (APPEND ds prior) /\
    l4_metadata_matches raw ds ==>
    l4_input_trace policy (APPEND ds prior) (CONS raw history)) /\
  (!policy prior history raw canonical env.
    l4_input_trace policy prior history /\
    l4_raw_generated_admitted policy prior raw canonical env ==>
    l4_input_trace policy env (CONS raw history))`;;
let l4_input_trace_valid = prove
 (`!policy env history. l4_input_trace policy env history ==> l4_evalid policy env`,
  MATCH_MP_TAC l4_input_trace_INDUCT THEN
  SIMP_TAC [l4_evalid_RULES] THEN MESON_TAC [l4_raw_generated_valid]);;

(* The exact history is newest block first, entries within each block in input
   order. Names and all raw axioms are authenticated explicitly, not erased. *)
let l4_input_flat = new_recursive_definition list_RECURSION
 `(l4_input_flat [] = ([]:l4_entry list)) /\
  (l4_input_flat (CONS ds history) = APPEND ds (l4_input_flat history))`;;
let l4_name_inventory = new_definition
 `!xs ys. l4_name_inventory xs ys <=>
    l4_names_distinct xs /\ l4_names_distinct ys /\
    ALL (\n. MEM n ys) xs /\ ALL (\n. MEM n xs) ys`;;
let l4_name_inventory_refl = prove
 (`!xs. l4_names_distinct xs ==> l4_name_inventory xs xs`,
  REWRITE_TAC [l4_name_inventory;GSYM ALL_MEM] THEN MESON_TAC []);;
let l4_name_inventory_members = prove
 (`!xs ys. l4_name_inventory xs ys ==> (!n. MEM n xs <=> MEM n ys)`,
  REWRITE_TAC [l4_name_inventory;GSYM ALL_MEM] THEN MESON_TAC []);;
let l4_input_valid = new_definition
 `!policy env history. l4_input_valid policy env history <=>
    l4_input_trace policy env history /\
    l4_name_inventory (MAP l4_entry_name (l4_input_flat history)) (MAP l4_entry_name env) /\
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) (l4_input_flat history)`;;
let l4_ordered_history_implies_valid = prove
 (`!policy env history.
    l4_input_trace policy env history /\
    MAP l4_entry_name (l4_input_flat history) = MAP l4_entry_name env /\
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) (l4_input_flat history) ==>
    l4_input_valid policy env history`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [l4_input_valid] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC l4_name_inventory_refl THEN
  ASM_MESON_TAC [l4_input_trace_valid;l4_evalid_unique]);;
let l4_input_valid_environment = prove
 (`!policy env history. l4_input_valid policy env history ==> l4_evalid policy env`,
  MESON_TAC [l4_input_valid;l4_input_trace_valid]);;
let l4_input_valid_unique = prove
 (`!policy env history. l4_input_valid policy env history ==>
    l4_names_distinct (MAP l4_entry_name (l4_input_flat history))`,
  SIMP_TAC [l4_input_valid;l4_name_inventory]);;
let l4_input_valid_permissions = prove
 (`!policy env history. l4_input_valid policy env history ==>
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) (l4_input_flat history) /\
    ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) env`,
  MESON_TAC [l4_input_valid;l4_input_trace_valid;l4_evalid_permissions]);;

module Lean4hol_raw_ctor = struct
  open Lean4hol
  module Env = Lean4hol_env
  module Bridge = Lean4hol_ctor_bridge
  let entries = Bridge.entries
  let exact = Bridge.exact
  let get = Bridge.get
  let names ns = mk_list(List.map quote_name ns,`:l4_name`)
  let levels us = mk_list(List.map quote_level us,`:l4_level`)
  let field = function Env.Data a -> node "L4Data" [quote_expr a] | Env.Recursive -> `L4Recursive`
  let fields fs = mk_list(List.map field fs,`:l4_field`)
  let pars xs = mk_list(List.map(fun(n,a)->mk_pair(quote_name n,quote_expr a))xs,
    `:l4_name#l4_expr`)
  let specs cs = mk_list(List.map(fun(n,fs)->node "L4CtorSpec" [quote_name n;fields fs])cs,
    `:l4_ctor_spec`)
  let equations = Bridge.equations @
    [l4_head_stop;l4_head_lambda;l4_entry_transparent;l4_entry_body;
     l4_expr_lsubst;l4_level_lsubst;l4_lparam;LENGTH;HD;TL;FILTER;l4_input_flat;l4_name_inventory;
     l4_raw_field;l4_family_app;l4_family_levels;l4_apps;l4_vars;
     l4_lift;l4_inst;l4_subst;l4_ctor_name;l4_ctor_fields;
     l4_metadata_matches;l4_anon_entry;l4_anon_kind;l4_anon_role;l4_anon_rule;
     l4_family_generated;l4_family_ctor_entries;l4_family_ctor_type;
     l4_family_rec_type;l4_family_rules;l4_family_rhs;l4_family_minor;
     l4_family_binders;l4_family_dom;l4_family_motive;l4_parameter_binders;
     l4_family_minors;l4_family_elim;l4_family_rec_params;l4_rec_positions;l4_ih_binders;
     l4_fresh_univ;l4_fresh_univ_aux;l4_univ_candidate;l4_decimal_aux;
     l4_rec_name;l4_elim_name;l4_is_recursive;l4_bind;LET_DEF;LET_END_DEF;EX;
     l4_family_large;l4_family_k;l4_raw_family_slice;FST;SND;EL;REVERSE;
     distinctness "l4_level";injectivity "l4_level"]
  let unfold tm =
    let h,args=strip_comb tm in
    match args with
    | n::_ when is_const h && is_numeral n && n<>`0` &&
        mem (fst(dest_const h),List.length args)
          ["l4_vars",2;"l4_decimal_aux",2;"l4_fresh_univ_aux",3] ->
      let rec first k c = if k=1 then RAND_CONV c else RATOR_CONV(first(k-1)c) in
      (first (List.length args) num_CONV THENC
        REWRITE_CONV [l4_vars;l4_decimal_aux;l4_fresh_univ_aux])tm
    | _ -> failwith "not raw generator successor"
  let calc = REPEATC(CHANGED_CONV
    (computation THENC REWRITE_CONV equations THENC DEPTH_CONV unfold THENC NUM_REDUCE_CONV))
  let decide st tm = tick st; prove(tm,CONV_TAC calc)
  let level_arithmetic st def tm =
    tick st;
    prove(tm,REWRITE_TAC [def;l4_eval_level;MAX] THEN REPEAT GEN_TAC THEN
      REPEAT (fun goal -> tick st; COND_CASES_TAC goal) THEN
      (fun goal -> tick st; ASM_ARITH_TAC goal))
  let rule st rules idx args premises =
    tick st;
    let th=SPECL args (List.nth (CONJUNCTS rules) idx) in
    let result=if premises=[] then th else
      let p=fst(dest_imp(concl th)) in
      let hp=EQ_MP(SYM(calc p))(CONV_RULE calc(end_itlist CONJ premises)) in
      MP th hp in
    CONV_RULE calc result
  let head st ds e =
    let qe=entries ds in
    let rec go e =
      tick st;
      let result,proof=match e with
      | Const(n,us) ->
        (match List.find_opt(fun d->d.Env.name=n)ds with
        | Some ({Env.kind=(Env.Definition | Env.Theorem);params;value=Some v;_} as d) ->
          if List.length params<>List.length us then stop Unsupported "head universe arity";
          let r,hr=go(instantiate_levels st params us v) in
          let args=[qe;Env.quote_decl d;levels us;quote_expr r] in
          let th=SPECL args (List.nth(CONJUNCTS l4_head_RULES)1) in
          let goals=conjuncts(fst(dest_imp(concl th))) in
          r,rule st l4_head_RULES 1 args
            (List.map (decide st) (List.filteri(fun j _->j<3)goals)@[hr])
        | _ -> e,rule st l4_head_RULES 0 [qe;quote_expr e]
            [decide st (node "l4_head_stop" [qe;quote_expr e])])
      | Let(n,a,v,b) ->
        let r,hr=go(subst st 0 v b) in
        r,rule st l4_head_RULES 2
          [qe;quote_name n;quote_expr a;quote_expr v;quote_expr b;quote_expr r] [hr]
      | App(f,x) ->
        let h,hf=go f in
        (match h with
        | Lam(n,a,b) ->
          let r,hr=go(subst st 0 x b) in
          r,rule st l4_head_RULES 3
            [qe;quote_expr f;quote_expr x;quote_name n;quote_expr a;quote_expr b;quote_expr r]
            [hf;hr]
        | _ -> App(h,x),rule st l4_head_RULES 4 [qe;quote_expr f;quote_expr x;quote_expr h]
            [hf;decide st(mk_neg(node "l4_head_lambda" [quote_expr h]))])
      | Proj _ -> stop Unsupported "projection head reduction is outside raw positivity slice"
      | _ -> e,rule st l4_head_RULES 0 [qe;quote_expr e]
          [decide st(node "l4_head_stop" [qe;quote_expr e])] in
      result,exact (node "l4_head" [qe;quote_expr e;quote_expr result]) proof in
    go e
  let sort st ds g e = get(Env.fragment_sort ~fuel:st.remaining ds g e)
  let sort_exists st ds g e =
    let u,h=sort st ds g e in
    let tm=mk_exists(`v:l4_level`,node "l4_raw_sort"
      [entries ds;quote_context g;quote_expr e;`v:l4_level`]) in
    EXISTS(tm,quote_level u)h
  let telescope st ds (b:Env.inductive_family) fs typ =
    let base=[entries ds;quote_name b.Env.family_name;names b.Env.level_params;
      number(List.length b.Env.parameters);quote_level b.Env.result_level] in
    let scope a=decide st(node "l4_params_expr" [quote_expr a;names b.Env.level_params]) in
    let rec field_go g j fs e = match fs,e with
    | [],_ -> exact(node "l4_raw_fields" (base@[quote_context g;number j;fields [];quote_expr e]))
        (rule st l4_raw_fields_RULES 0 (base@[quote_context g;number j]) [])
    | f::rest,Pi(n,a,body) ->
      let h,hh=head st ds a in
      let shape=decide st(node "l4_raw_field"
        [quote_name b.Env.family_name;names b.Env.level_params;number(List.length b.Env.parameters);
         number j;field f;quote_expr h]) in
      let v,hv=sort st ds g a in
      let le=level_arithmetic st l4_level_le
        (node "l4_level_le" [quote_level v;quote_level b.Env.result_level]) in
      let tail=field_go(a::g)(j+1)rest body in
      rule st l4_raw_fields_RULES 1 (base@[quote_context g;number j;field f;fields rest;
        quote_name n;quote_expr a;quote_expr body;quote_expr h;quote_level v])
        [hh;shape;scope a;hv;le;tail]
    | _ -> stop Unsupported "raw field telescope is not manifest" in
    let rec param_go g ps e = match ps,e with
    | [],_ -> rule st l4_raw_params_RULES 0 (base@[quote_context g;fields fs;quote_expr e])
        [field_go g 0 fs e]
    | (m,d)::rest,Pi(n,a,body) ->
      let identity=mk_eq(node "l4_anon" [quote_expr a],node "l4_anon" [quote_expr d]) in
      let directed h=mk_conj(node "l4_head" [entries ds;quote_expr a;quote_expr h],
        mk_eq(node "l4_anon" [quote_expr h],node "l4_anon" [quote_expr d])) in
      let h,matching=if a=d then a,DISJ1 (decide st identity) (directed a) else
        let h,hh=head st ds a in
        let same=decide st(snd(dest_conj(directed h))) in
        h,DISJ2 identity (CONJ hh same) in
      let v,hv=sort st ds g a in
      let tail=param_go(a::g)rest body in
      rule st l4_raw_params_RULES 1 (base@[quote_context g;quote_name m;quote_expr d;pars rest;
        fields fs;quote_name n;quote_expr a;quote_expr body;quote_expr h;quote_level v])
        [matching;scope a;hv;tail]
    | _ -> stop Unsupported "raw parameter telescope is not manifest" in
    param_go [] b.Env.parameters typ
  let expected prior next raw canonical = node "l4_raw_family_admitted"
    [Env.quote_policy prior;Env.quote_env prior;entries raw;entries canonical;Env.quote_env next]
  let certify ?(fuel=100000) prior next raw (b:Env.inductive_family) =
    let stage=ref "family anchor" in
    let result=run fuel [] [] (fun st ->
    let canonical=b.Env.family_claims in
    let header=match raw with h::_->h | []->stop Unsupported "missing raw header" in
    let detail=get(Env.inductive_certificate next b.Env.family_name) in
    let _,args=strip_comb(concl detail) in
    if List.length args<>11 then stop Unsupported "raw admission needs family anchor";
    let expected_detail=[Env.quote_policy prior;Env.quote_env prior;quote_name b.Env.family_name;
      names b.Env.level_params;pars b.Env.parameters;quote_level b.Env.result_level;
      specs b.Env.family_constructors;List.nth args 7;`T`;`F`;entries canonical] in
    ignore(exact(node "l4_family_checked" expected_detail)detail);
    let rawctors=List.filter(fun d->match d.Env.kind with
      | Env.Generated(Env.Constructor_role _)->true | _->false)raw in
    if List.length rawctors<>List.length b.Env.family_constructors then
      stop Unsupported "raw constructor count mismatch";
    let ds=header::Env.declarations prior in
    stage:="prior header formation";
    let hheader=sort_exists st (Env.declarations prior) [] header.Env.typ in
    let ctor_proofs=List.map2(fun (n,fs) d ->
      if n<>d.Env.name then stop Unsupported "raw constructor order mismatch";
      stage:="header-only constructor formation";
      let hform=sort_exists st ds [] d.Env.typ in
      stage:="directed telescope and positivity";
      let ht=telescope st ds b fs d.Env.typ in
      hform,ht) b.Env.family_constructors rawctors in
    let rawargs=[Env.quote_env prior;quote_name b.Env.family_name;names b.Env.level_params;
      pars b.Env.parameters;quote_level b.Env.result_level;specs b.Env.family_constructors;entries raw] in
    let proofs=hheader::List.concat_map(fun(a,b)->[a;b])ctor_proofs in
    stage:="raw obligations assembly";
    let hraw=prove(node "l4_raw_family_obligations" rawargs,
      REWRITE_TAC [l4_raw_family_obligations] THEN CONV_TAC calc THEN REWRITE_TAC proofs) in
    stage:="typed metadata bridge";
    let bridge=get(Bridge.certify ~fuel:st.remaining next raw canonical) in
    stage:="raw admission assembly";
    let slice=node "l4_raw_family_slice"
      [quote_level b.Env.result_level;specs b.Env.family_constructors] in
    let hslice=if b.Env.result_level=Succ Zero then decide st slice else
      let hn=level_arithmetic st l4_level_nonzero
        (node "l4_level_nonzero" [quote_level b.Env.result_level]) in
      prove(slice,REWRITE_TAC [l4_raw_family_slice;hn] THEN CONV_TAC calc) in
    let tm=expected prior next raw canonical in
    let definition=SPECL [Env.quote_policy prior;Env.quote_env prior;entries raw;entries canonical;
      Env.quote_env next] l4_raw_family_admitted in
    let body=rand(rhs(concl definition)) in
    let witnesses=List.init 8(fun j->List.nth expected_detail(j+2)) in
    let rec exists tm = function
    | [] -> prove(tm,REWRITE_TAC [detail;hraw;bridge;hslice] THEN CONV_TAC calc)
    | x::xs -> let v,b=dest_exists tm in EXISTS(tm,x)(exists(vsubst[x,v]b)xs) in
    exact tm (EQ_MP(SYM definition)(CONJ(Env.certificate next)(exists body witnesses)))) in
    match result with Ok _ -> result | Error e ->
      Error {e with message="raw admission " ^ !stage ^ ": " ^ e.message}
end;;

module Lean4hol_input_certificate = struct
  open Lean4hol
  module Env = Lean4hol_env
  module Raw = Lean4hol_raw_ctor
  let trace_rules = Array.of_list(CONJUNCTS l4_input_trace_RULES)
  let distinct_prefix = prove
    (`!xs ys. l4_names_distinct (APPEND xs ys) ==> l4_names_distinct xs`,
     LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;l4_names_distinct;MEM_APPEND] THEN
     ASM_MESON_TAC [])
  let metadata_refl = prove
    (`!ds. l4_names_distinct (MAP l4_entry_name ds) ==> l4_metadata_matches ds ds`,
     REWRITE_TAC [l4_metadata_matches;GSYM ALL_MEM;MEM_MAP] THEN MESON_TAC [])
  let metadata_valid_prefix = prove
    (`!policy prior ds. l4_evalid policy (APPEND ds prior) ==> l4_metadata_matches ds ds`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC metadata_refl THEN
     MATCH_MP_TAC (SPECL [`MAP l4_entry_name ds`; `MAP l4_entry_name prior`] distinct_prefix) THEN
     REWRITE_TAC [GSYM MAP_APPEND] THEN ASM_MESON_TAC [l4_evalid_unique])
  let exact_rules = Hashtbl.create 17
  let exact_rule count = match Hashtbl.find_opt exact_rules count with
    | Some th -> th
    | None ->
      (* Resolve only the APPEND spine while entries and history are schematic.
         Metadata, environment validity and trace premises remain opaque. *)
      let prefix = [`policy:l4_entry list`; `prior:l4_entry list`;
                    `history:(l4_entry list) list`; `raw:l4_entry list`] in
      let ds = List.init count (fun j -> mk_var("d" ^ string_of_int j,`:l4_entry`)) in
      let step = GENL (prefix @ ds) (REWRITE_RULE [APPEND]
        (SPECL (prefix @ [mk_list(ds,`:l4_entry`)]) trace_rules.(1))) in
      let first = List.filteri (fun j _ -> j<2) prefix in
      let metadata = GENL (first @ ds) (REWRITE_RULE [APPEND]
        (SPECL (first @ [mk_list(ds,`:l4_entry`)]) metadata_valid_prefix)) in
      let th = step,metadata in
      if Hashtbl.length exact_rules >= 64 then Hashtbl.clear exact_rules;
      Hashtbl.replace exact_rules count th; th
  let history blocks = mk_list(List.map Raw.entries blocks,`:l4_entry list`)
  let trace env blocks = node "l4_input_trace" [Env.quote_policy env;Env.quote_env env;history blocks]
  let expected env blocks = node "l4_input_valid" [Env.quote_policy env;Env.quote_env env;history blocks]
  let start env = Raw.exact (trace env []) (SPEC(Env.quote_policy env)(CONJUNCT1 l4_input_trace_RULES))
  let append_exact prior next blocks raw previous = run 100000 [] [] (fun st ->
    ignore(Raw.exact(trace prior blocks)previous);
    let count=List.length(Env.declarations next)-List.length(Env.declarations prior) in
    if count<0 then stop Proof_failure "input environment shrank";
    let ds=List.filteri(fun j _->j<count)(Env.declarations next) in
    let step,metadata_rule=exact_rule count in
    let prefix=[Env.quote_policy prior;Env.quote_env prior] in
    let quoted=List.map Env.quote_decl ds in
    let qraw=Raw.entries raw and qds=Raw.entries ds in
    let metadata=node "l4_metadata_matches" [qraw;qds] in
    (* Identical quotations alone do not prove distinct names. The fast path
       obtains that obligation from the exact certified environment prefix. *)
    let hm=if aconv qraw qds then
      (tick st; Raw.exact metadata
        (MP (SPECL (prefix @ quoted) metadata_rule) (Env.certificate next)))
      else Raw.decide st metadata in
    tick st;
    Raw.exact(trace next (raw::blocks))
      (MP (SPECL (prefix @ [history blocks;qraw] @ quoted) step)
          (CONJ previous (CONJ (Env.certificate next) hm))))
  let append_generated prior next blocks raw canonical previous admission = run 100000 [] [] (fun st ->
    ignore(Raw.exact(trace prior blocks)previous);
    ignore(Raw.exact(node "l4_raw_generated_admitted"
      [Env.quote_policy prior;Env.quote_env prior;Raw.entries raw;Raw.entries canonical;Env.quote_env next])admission);
    tick st;
    Raw.exact(trace next(raw::blocks))
      (MP (SPECL [Env.quote_policy prior;Env.quote_env prior;history blocks;
        Raw.entries raw;Raw.entries canonical;Env.quote_env next] trace_rules.(2))
        (CONJ previous admission)))
  let append_raw prior next blocks raw canonical previous admission =
    let injected=run 100000 [] [] (fun _ ->
      ignore(Raw.exact(Raw.expected prior next raw canonical)admission);
      MP (SPECL [Env.quote_policy prior;Env.quote_env prior;Raw.entries raw;
        Raw.entries canonical;Env.quote_env next] l4_raw_family_generated) admission) in
    match injected with Error e->Error e | Ok proof->
      append_generated prior next blocks raw canonical previous proof
  let append_indexed prior next blocks raw canonical previous admission =
    let injected=run 100000 [] [] (fun _ ->
      let args=[Env.quote_policy prior;Env.quote_env prior;Raw.entries raw;
        Raw.entries canonical;Env.quote_env next] in
      ignore(Raw.exact(node "l4_raw_indexed_admitted" args)admission);
      MP (SPECL args l4_raw_indexed_generated) admission) in
    match injected with Error e->Error e | Ok proof->
      append_generated prior next blocks raw canonical previous proof
  let finish env blocks previous = run 100000 [] [] (fun st ->
    ignore(Raw.exact(trace env blocks)previous);
    let definition=SPECL [Env.quote_policy env;Env.quote_env env;history blocks] l4_input_valid in
    let obligations=conjuncts(rhs(concl definition)) in
    Raw.exact(expected env blocks)(EQ_MP(SYM definition)
      (end_itlist CONJ(previous::List.map(Raw.decide st)(List.tl obligations)))))
end;;
