(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/core.ml";;
needs "hol/environment_rules.ml";;
needs "hol/inductive_model.ml";;

module Lean4hol_env : sig
  include module type of Lean4hol_model
  type axiom_permission = {
    axiom_name : Lean4hol.name; axiom_params : Lean4hol.name list;
    axiom_type : Lean4hol.expr
  }
  type environment
  val empty : environment
  val with_axioms : ?fuel:int -> axiom_permission list -> (environment,Lean4hol.error) result
  val declarations : environment -> declaration list
  val permissions : environment -> axiom_permission list
  val quote_decl : declaration -> term
  val quote_env : environment -> term
  val quote_policy : environment -> term
  val certificate : environment -> thm
  val admit : ?fuel:int -> environment -> declaration -> (environment * thm,Lean4hol.error) result
  val admit_inductive : ?fuel:int -> environment -> inductive_block ->
    (environment * thm,Lean4hol.error) result
  val admit_inductive_family : ?fuel:int -> environment -> inductive_family ->
    (environment * thm,Lean4hol.error) result
  val inductive_certificate : environment -> Lean4hol.name -> (thm,Lean4hol.error) result
  val infer : ?fuel:int -> environment -> Lean4hol.expr list -> Lean4hol.expr ->
    (Lean4hol.expr * thm,Lean4hol.error) result
  val check : ?fuel:int -> environment -> Lean4hol.expr list -> Lean4hol.expr -> Lean4hol.expr ->
    (thm,Lean4hol.error) result
  val convert : ?fuel:int -> environment -> Lean4hol.expr list -> Lean4hol.expr -> Lean4hol.expr ->
    Lean4hol.expr -> (thm,Lean4hol.error) result
end = struct
  open Lean4hol
  include Lean4hol_model
  type axiom_permission = {axiom_name:name;axiom_params:name list;axiom_type:expr}
  type environment = {entries:declaration list;grants:axiom_permission list;proof:thm;
    inductive_proofs:(name * thm) list}
  let declarations env = env.entries
  let permissions env = env.grants
  let certificate env = env.proof
  let inductive_certificate env n = match List.assoc_opt n env.inductive_proofs with
    | Some th -> Ok th
    | None -> Error {kind=Unsupported;message="no inductive admission certificate for this name"}
  let quote_names ns = mk_list(List.map quote_name ns,`:l4_name`)
  let quote_bool b = if b then `T` else `F`
  let quote_rec_rule r = node "L4RecRule" [quote_name r.ctor;number r.num_fields;quote_expr r.rhs]
  let quote_role = function
    | Inductive_role r -> node "L4InductiveRole" [number r.num_params;number r.num_indices;
        quote_names r.all;quote_names r.ctors;number r.num_nested;
        quote_bool r.is_rec;quote_bool r.is_reflexive;quote_bool r.is_unsafe]
    | Constructor_role r -> node "L4ConstructorRole" [quote_name r.induct;number r.index;
        number r.num_params;number r.num_fields;quote_bool r.is_unsafe]
    | Recursor_role r -> node "L4RecursorRole" [quote_names r.all;number r.num_params;
        number r.num_indices;number r.num_motives;number r.num_minors;
        mk_list(List.map quote_rec_rule r.rules,`:l4_recrule`);quote_bool r.k;quote_bool r.is_unsafe]
  let quote_kind = function
    | Definition -> `L4DefKind` | Theorem -> `L4ThmKind`
    | Opaque -> `L4OpaqueKind` | Axiom -> `L4AxiomKind`
    | Generated r -> node "L4Generated" [quote_role r]
  let quote_params ps = mk_list(List.map quote_name ps,`:l4_name`)
  let quote_levels us = mk_list(List.map quote_level us,`:l4_level`)
  let body d = match d.kind,d.value with
    | (Axiom | Generated _),None -> Sort Zero
    | (Axiom | Generated _),Some _ -> stop Invalid_input "axiom/generated entry has no body"
    | _,Some v -> v
    | _,None -> stop Invalid_input "definition/theorem/opaque body required"
  let quote_decl d = node "L4Entry"
    [quote_kind d.kind;quote_name d.name;quote_params d.params;quote_expr d.typ;quote_expr(body d)]
  let as_axiom p = {kind=Axiom;name=p.axiom_name;params=p.axiom_params;typ=p.axiom_type;value=None}
  let quote_entries ds = mk_list(List.map quote_decl ds,`:l4_entry`)
  let quote_env env = quote_entries env.entries
  let quote_policy env = quote_entries (List.map as_axiom env.grants)
  let guarded tm th =
    if hyp th<>[] || not(aconv (concl th) tm) then
      stop Proof_failure "environment theorem conclusion or hypotheses mismatch";
    th
  let valid_term env = node "l4_evalid" [quote_policy env;quote_env env]
  let empty = {entries=[];grants=[];inductive_proofs=[];
    proof=CONJUNCT1(SPEC `[]:l4_entry list` l4_evalid_RULES)}
  let validation_terms d =
    [d.typ;body d;Sort(Param d.name);Const(Anonymous,List.map (fun n -> Param n) d.params)]
  let with_axioms ?(fuel=100000) grants =
    run fuel [] [] (fun st ->
      tick st;
      List.iter (fun p -> validate st [] (validation_terms(as_axiom p))) grants;
      let policy = quote_entries(List.map as_axiom grants) in
      let proof = CONJUNCT1(SPEC policy l4_evalid_RULES) in
      let env = {entries=[];grants;proof;inductive_proofs=[]} in
      ignore(guarded (valid_term env) proof); env)

  let equations =
    [l4_entry_tag;l4_entry_name;l4_entry_params;l4_entry_type;l4_entry_body;l4_entry_transparent;
     l4_expr_lsubst;l4_level_lsubst;l4_lparam;l4_names_distinct;l4_params_expr;l4_params_level;
     MEM;MAP;ALL;ALL2;LENGTH;HD;TL;distinctness "l4_name";injectivity "l4_name";
     distinctness "l4_entry_kind";injectivity "l4_entry";
     distinctness "list";injectivity "list";l4_regular_kind;
     l4_apps;APPEND;l4_anon;l4_anon_rule;l4_anon_role;l4_anon_kind;l4_anon_entry;
     l4_metadata_matches;distinctness "l4_role";injectivity "l4_role";
     injectivity "l4_entry_kind";injectivity "l4_recrule";
     l4_protected_name;l4_primitive_names;l4_nat_name;l4_bool_name;
     l4_primitive_block;l4_rec_name;l4_ctor_name;
     l4_nested_name;l4_no_nested_aux;l4_no_nested_block;l4_no_nested_claims;
     l4_is_constructor_kind;l4_is_constructor_role]
  let calc = REWRITE_CONV equations THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let object_calc = computation THENC DEPTH_CONV (fun tm ->
    let head,_ = strip_comb tm in
    if is_const head && mem (fst(dest_const head))
      ["l4_entry_tag";"l4_entry_name";"l4_entry_params";"l4_entry_type";"l4_entry_body";
       "l4_expr_lsubst";"l4_apps";"APPEND";"LENGTH";"l4_nat_name"]
    then CHANGED_CONV calc tm else failwith "not environment object computation")
  let decide st tm = tick st; prove(tm,CONV_TAC calc)
  let native_rules = Array.of_list(CONJUNCTS l4_edef_RULES)

  module Native (Env : sig val entries : declaration list end) = Engine(struct
    let qe = quote_entries Env.entries
    let judgment g e e' a = node "l4_edef" [qe;quote_context g;quote_expr e;quote_expr e';quote_expr a]
    let rule st i args premises =
      tick st;
      let th = CONV_RULE object_calc (SPECL (qe::args) native_rules.(i)) in
      match premises with [] -> th | _ -> MP th (end_itlist CONJ premises)
    let find n us =
      let d = try List.find (fun d -> d.name=n) Env.entries with Not_found ->
        stop Unsupported "constant not in the certified environment" in
      if List.length d.params<>List.length us then stop Proof_failure "constant universe arity mismatch";
      d
    let member st d = decide st
      (mk_comb(mk_comb(mk_const("MEM",[`:l4_entry`,`:A`]),quote_decl d),qe))
    let arity st d us = decide st (mk_eq(number(List.length d.params),number(List.length us)))
    let constant st g n us vs =
      let d = find n us in
      if List.length us<>List.length vs then stop Proof_failure "constant conversion arity mismatch";
      let heqs = List.map2 (level_proof st) us vs in
      let all2 = prove
        (list_mk_comb(mk_const("ALL2",[`:l4_level`,`:A`;`:l4_level`,`:B`]),
          [`l4_level_equiv`;quote_levels us;quote_levels vs]),REWRITE_TAC (ALL2::heqs)) in
      let ty = instantiate_levels st d.params us d.typ in
      ty,rule st 13 [quote_context g;quote_decl d;quote_levels us;quote_levels vs]
        [member st d;arity st d us;all2]
    let delta st g n us =
      let d = find n us in
      match d.kind with
      | Axiom | Opaque | Generated _ -> None
      | Definition | Theorem ->
        let v = instantiate_levels st d.params us (body d) in
        let ty = instantiate_levels st d.params us d.typ in
        let allowed = decide st (node "l4_entry_transparent" [quote_decl d]) in
        Some(v,ty,rule st 14 [quote_context g;quote_decl d;quote_levels us]
          [member st d;arity st d us;allowed])
    let nat_name = Str(Anonymous,"Nat")
    let nat_type = Const(nat_name,[])
    let nat_constant st g n ty =
      let _,h = constant st g n [] [] in
      guarded (judgment g (Const(n,[])) (Const(n,[])) ty) h
    let nat_literal st g s =
      let qn = natural s in
      let hn = nat_constant st g nat_name (Sort(Succ Zero)) in
      let h = rule st 16 [quote_context g;qn] [hn] in
      nat_type,guarded (judgment g (Natlit s) (Natlit s) nat_type) h
    let nat_literal_step st g s =
      let qn = natural s in
      let target,h = if s="0" then
        let z = Str(nat_name,"zero") in
        let hz = nat_constant st g z nat_type in
        Const(z,[]),rule st 17 [quote_context g] [hz]
      else
        let succ = Str(nat_name,"succ") in
        let hs = nat_constant st g succ (Pi(Anonymous,nat_type,nat_type)) in
        tick st;
        let pred = rhs(concl(NUM_REDUCE_CONV (mk_comb(`PRE`,qn)))) in
        let previous = string_of_num(dest_numeral pred) in
        let h = CONV_RULE NUM_REDUCE_CONV (rule st 18 [quote_context g;pred] [hs]) in
        App(Const(succ,[]),Natlit previous),h in
      target,nat_type,guarded (judgment g (Natlit s) target nat_type) h
    let rec spine args = function App(f,a) -> spine (a::args) f | f -> f,args
    let major e = match spine [] e with
      | (Const(n,_) as f),args ->
        (match List.find_opt (fun d -> d.name=n) Env.entries with
         | Some {kind=Generated(Recursor_role info);_}
           when List.length args=info.num_params+info.num_minors+2 ->
           let rev=List.rev args in
           Some(List.hd rev,fun x -> apps f (List.rev(List.tl rev)@[x]))
         | _ -> None)
      | _ -> None
    let iota st g e =
      match spine [] e with
      | Const(n,us),args ->
        let d = find n us in
        (match d.kind with
         | Generated(Recursor_role info) when List.length args=info.num_params+info.num_minors+2 ->
           let rev = List.rev args in
           let major = List.hd rev and prefix = List.rev(List.tl rev) in
           (match spine [] major with
            | Const(c,cls),cargs when List.length cargs>=info.num_params ->
              let rec split n xs = if n=0 then [],xs else
                let before,after=split (n-1) (List.tl xs) in List.hd xs::before,after in
              let cpars,fields=split info.num_params cargs in
              (match List.find_opt (fun r -> r.ctor=c) info.rules with
               | Some r when List.length fields=r.num_fields ->
                 let rhs = apps (instantiate_levels st d.params us r.rhs) (prefix@fields) in
                 let prove_step a hl hr =
                   let th = CONV_RULE object_calc (SPECL
                     [qe;quote_context g;quote_decl d;quote_names info.all;number info.num_params;
                      number info.num_minors;mk_list(List.map quote_rec_rule info.rules,`:l4_recrule`);
                      quote_bool info.k;quote_name c;number r.num_fields;quote_expr r.rhs;
                      quote_levels us;quote_levels cls;quote_context prefix;quote_context cpars;
                      quote_context fields;quote_expr a] native_rules.(15)) in
                   let conditions = conjuncts(fst(dest_imp(concl th))) in
                   let side = List.init 7 (fun i -> decide st (List.nth conditions i)) in
                   MP th (end_itlist CONJ (side@[hl;hr])) in
                 Some(rhs,prove_step)
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None
    let context_empty = SPEC qe (CONJUNCT1 l4_econtext_RULES)
    let context_extend = SPEC qe (CONJUNCT2 l4_econtext_RULES)
  end)

  let with_env fuel env g es f =
    run fuel [] (g@es) (fun st -> ignore(guarded (valid_term env) env.proof); f st)
  let checked env g e e' a hctx h =
    let tm = node "l4_checked"
      [quote_policy env;quote_env env;quote_context g;quote_expr e;quote_expr e';quote_expr a] in
    let definition = SPECL
      [quote_policy env;quote_env env;quote_context g;quote_expr e;quote_expr e';quote_expr a] l4_checked in
    guarded tm (EQ_MP (SYM definition) (CONJ env.proof (CONJ hctx h)))

  let admit ?(fuel=100000) env d =
    (* Keep shape validation inside the classified-error boundary. *)
    with_env fuel env [] [d.typ;Sort(Param d.name);
      Const(Anonymous,List.map (fun n -> Param n) d.params)] (fun st ->
      let v = body d in validate st [] [v];
      (match d.kind with Generated _ -> stop Unsupported "generated entries require inductive admission" | _ -> ());
      let module Native = Native(struct let entries = env.entries end) in
      let u,hty = Native.infer_sort st [] d.typ in
      let rules = CONJUNCTS(SPEC (quote_policy env) l4_evalid_RULES) in
      let proof = match d.kind with
      | Generated _ -> stop Unsupported "generated entries require inductive admission"
      | Axiom ->
        let grant = {axiom_name=d.name;axiom_params=d.params;axiom_type=d.typ} in
        if not(List.mem grant env.grants) then stop Unsupported "axiom absent from exact permission policy";
        let step = SPECL [quote_env env;quote_name d.name;quote_params d.params;
          quote_expr d.typ;quote_level u] (List.nth rules 1) in
        let conditions = conjuncts(fst(dest_imp(concl step))) in
        let at i = decide st (List.nth conditions i) in
        MP step (end_itlist CONJ [env.proof;at 1;at 2;at 3;at 4;hty;at 6])
      | Definition | Theorem | Opaque ->
        let hv = Native.check_i st [] v d.typ in
        let step = SPECL [quote_env env;quote_kind d.kind;quote_name d.name;quote_params d.params;
          quote_expr d.typ;quote_expr v;quote_level u] (List.nth rules 2) in
        let conditions = conjuncts(fst(dest_imp(concl step))) in
        let at i = decide st (List.nth conditions i) in
        let theorem_prop = match d.kind with
          | Theorem -> DISCH (fst(dest_imp(List.nth conditions 8))) (level_proof st u Zero)
          | _ -> at 8 in
        MP step (end_itlist CONJ [env.proof;at 1;at 2;at 3;at 4;at 5;hty;hv;theorem_prop;at 9]) in
      let env' = {env with entries=d::env.entries;proof} in
      env',guarded (valid_term env') proof)

  let generator_equations = equations @
    [l4_generated;l4_ctor_entries;l4_ctor_name;l4_ctor_fields;l4_ctor_type;
     l4_field_type;l4_is_recursive;l4_rec_name;l4_elim_name;l4_vars;l4_bind;
     l4_field_binders;l4_rec_positions;l4_ih_binders;l4_minor_type;l4_minor_binders;
     l4_motive_type;l4_rec_type;l4_rec_rhs;l4_rec_rules_aux;EX;LET_DEF;LET_END_DEF;
     l4_lift;SND;FST;REVERSE;l4_decimal_aux;l4_univ_candidate;l4_fresh_univ_aux;l4_fresh_univ;
     l4_family_levels;l4_family_rec_params;l4_family_elim;l4_parameter_binders;
     l4_family_app;l4_family_dom;l4_family_binders;l4_family_ctor_type;l4_family_minor;
     l4_family_minors;l4_family_motive;l4_family_rec_type;l4_family_rhs;l4_family_rules;
     l4_family_ctor_entries;l4_family_generated;l4_family_primitive]
  let vars_unfold tm =
    let h,args = strip_comb tm in
    match args with
    | n::_ when is_const h &&
        mem (fst(dest_const h)) ["l4_vars";"l4_decimal_aux";"l4_fresh_univ_aux"] &&
        is_numeral n && n<>`0` ->
      let rec first_argument k conv = if k=1 then RAND_CONV conv
        else RATOR_CONV(first_argument (k-1) conv) in
      (first_argument (List.length args) num_CONV THENC
        REWRITE_CONV [l4_vars;l4_decimal_aux;l4_fresh_univ_aux]) tm
    | _ -> failwith "not a successor variable list"
  let generator_calc = REPEATC (CHANGED_CONV
    (REWRITE_CONV generator_equations THENC DEPTH_CONV vars_unfold THENC NUM_REDUCE_CONV))
  let arithmetic st def tm =
    tick st;
    prove(tm,REWRITE_TAC [def;l4_eval_level;MAX] THEN REPEAT GEN_TAC THEN
      REPEAT (fun goal -> tick st; COND_CASES_TAC goal) THEN
      (fun goal -> tick st; ASM_ARITH_TAC goal))
  let quote_field = function Data a -> node "L4Data" [quote_expr a] | Recursive -> `L4Recursive`
  let quote_specs cs = mk_list(List.map (fun (n,fs) -> node "L4CtorSpec"
    [quote_name n;mk_list(List.map quote_field fs,`:l4_field`)]) cs,`:l4_ctor_spec`)
  let role_terms = function
    | Inductive_role r -> List.map (fun n -> Sort(Param n)) (r.all@r.ctors)
    | Constructor_role r -> [Sort(Param r.induct)]
    | Recursor_role r -> List.map (fun n -> Sort(Param n)) r.all @
        List.concat_map (fun rr -> [Sort(Param rr.ctor);rr.rhs]) r.rules
  let admit_inductive ?(fuel=100000) env b =
    with_env fuel env [] [Sort(Param b.inductive_name);Sort b.inductive_level] (fun st ->
      List.iter (fun (n,fs) -> validate st [] [Sort(Param n)];
        List.iter (function Recursive -> tick st | Data a -> validate st [] [a]) fs) b.constructors;
      List.iter (fun d -> validate st [] (validation_terms d);
        match d.kind with Generated r -> validate st [] (role_terms r)
        | _ -> stop Unsupported "inductive claims must have generated roles") b.claims;
      let generated = generate st b in
      List.iter (fun d -> validate st [] (validation_terms d)) generated;
      let qi = quote_name b.inductive_name and qu = quote_level b.inductive_level in
      let qcs = quote_specs b.constructors in
      let hgen = generator_calc (node "l4_generated" [qi;qu;qcs]) in
      if not(aconv (rhs(concl hgen)) (quote_entries generated)) then
        stop Proof_failure "candidate inductive generator differs from HOL definition";
      let step = REWRITE_RULE [hgen;APPEND] (SPECL
        [quote_env env;qi;qu;qcs;quote_entries b.claims]
        (List.nth (CONJUNCTS(SPEC (quote_policy env) l4_evalid_RULES)) 3)) in
      let conditions = conjuncts(fst(dest_imp(concl step))) in
      let at i = tick st; prove(List.nth conditions i,CONV_TAC generator_calc) in
      let no_nested = at 9 and no_nested_claims = at 10 in
      let module Prior = Native(struct let entries = env.entries end) in
      let frules = CONJUNCTS(SPECL [quote_env env;qu] l4_fields_valid_RULES) in
      let rec fields = function
        | [] -> List.nth frules 0
        | Recursive::fs -> tick st;
          MP (SPEC (mk_list(List.map quote_field fs,`:l4_field`)) (List.nth frules 1)) (fields fs)
        | Data a::fs ->
          let v,h = Prior.infer_sort st [] a in
          let step = SPECL [quote_expr a;quote_level v;mk_list(List.map quote_field fs,`:l4_field`)]
            (List.nth frules 2) in
          let conditions = conjuncts(fst(dest_imp(concl step))) in
          let scoped = decide st (List.nth conditions 0) in
          let bound = arithmetic st l4_level_le (List.nth conditions 2) in
          MP step (end_itlist CONJ [scoped;h;bound;fields fs]) in
      let hfields = List.map (fun (_,fs) -> fields fs) b.constructors in
      let hallfields = prove(List.nth conditions 3,REWRITE_TAC (ALL::l4_ctor_fields::hfields)) in
      (* Provisional signatures are used only for internal formation proofs;
         no certified environment exists until the admission rule is applied. *)
      let entries = generated@env.entries in
      let module Form = Native(struct let entries = entries end) in
      let formations = List.map (fun d ->
        let v,h = Form.infer_sort st [] d.typ in
        let tm = mk_exists(`v:l4_level`,node "l4_edef"
          [quote_entries entries;quote_context [];quote_expr d.typ;quote_expr d.typ;
           node "L4Sort" [`v:l4_level`]]) in
        EXISTS(tm,quote_level v) h) generated in
      let hallform = prove(List.nth conditions 6,REWRITE_TAC (ALL::l4_entry_type::formations)) in
      let nonzero = arithmetic st l4_level_nonzero (List.nth conditions 2) in
      let premises = end_itlist CONJ
        [env.proof;at 1;nonzero;hallfields;at 4;at 5;hallform;at 7;at 8;
         no_nested;no_nested_claims] in
      let proof = MP step premises in
      let args = [quote_policy env;quote_env env;qi;qu;qcs;quote_entries b.claims] in
      let detail_def = REWRITE_RULE [hgen;APPEND] (SPECL args l4_inductive_checked) in
      let detail = guarded (node "l4_inductive_checked" args)
        (EQ_MP (SYM detail_def) (CONJ premises proof)) in
      let env' = {env with entries;proof;inductive_proofs=(b.inductive_name,detail)::env.inductive_proofs} in
      env',guarded (valid_term env') proof)

  let rec level_sample st value = function
    | Zero -> tick st; 0
    | Param _ -> tick st; value
    | Succ u -> tick st; 1 + level_sample st value u
    | Max(u,v) -> tick st; max (level_sample st value u) (level_sample st value v)
    | Imax(u,v) -> tick st;
      let n=level_sample st value v in if n=0 then 0 else max (level_sample st value u) n
  let level_truth st def tm positive counter =
    if positive then EQT_INTRO(arithmetic st def tm) else
    let valuation=mk_abs(`n:l4_name`,number counter) in
    let h=prove(mk_neg tm,
      DISCH_THEN (fun h -> MP_TAC(SPEC valuation (REWRITE_RULE [def] h))) THEN
      REWRITE_TAC [l4_eval_level;MAX] THEN CONV_TAC NUM_REDUCE_CONV) in
    EQF_INTRO h
  let quote_parameters pars = mk_list(List.map (fun (n,a) -> mk_pair(quote_name n,quote_expr a)) pars,
    `:l4_name#l4_expr`)
  let quote_level_lists vss = mk_list(List.map quote_levels vss,`:l4_level list`)

  let admit_inductive_family ?(fuel=100000) env b =
    with_env fuel env [] [Sort(Param b.family_name);Sort b.result_level] (fun st ->
      List.iter (fun n -> validate st [] [Sort(Param n)]) b.level_params;
      List.iter (fun (n,a) -> validate st [] [Sort(Param n);a]) b.parameters;
      List.iter (fun (n,fs) -> validate st [] [Sort(Param n)];
        List.iter (function Recursive -> tick st | Data a -> validate st [] [a]) fs) b.family_constructors;
      List.iter (fun d -> validate st [] (validation_terms d);
        match d.kind with Generated r -> validate st [] (role_terms r)
        | _ -> stop Unsupported "family claims must have generated roles") b.family_claims;
      let qi=quote_name b.family_name and qps=quote_params b.level_params in
      let qpars=quote_parameters b.parameters and qu=quote_level b.result_level in
      let qcs=quote_specs b.family_constructors and qclaims=quote_entries b.family_claims in
      let ctx=List.rev(List.map snd b.parameters) in
      let qctx=quote_context ctx in
      let module Prior = Native(struct let entries=env.entries end) in
      let hctx=Prior.context st ctx in
      let result_zero=level_sample st 1 b.result_level=0 in
      let result_nonzero=level_sample st 0 b.result_level>0 in
      let frules=CONJUNCTS(SPECL [quote_env env;qctx;qps;qu] l4_family_fields_RULES) in
      if List.length frules<>3 then stop Proof_failure "family field-rule shape mismatch";
      let rec fields = function
        | [] -> [],List.nth frules 0
        | Recursive::fs ->
          tick st;
          let vs,h=fields fs in
          b.result_level::vs,MP (SPECL [mk_list(List.map quote_field fs,`:l4_field`);quote_levels vs]
            (List.nth frules 1)) h
        | Data a::fs ->
          let v,h=Prior.infer_sort st ctx a in
          let vs,rest=fields fs in
          let step=SPECL [quote_expr a;quote_level v;mk_list(List.map quote_field fs,`:l4_field`);
            quote_levels vs] (List.nth frules 2) in
          let conditions=conjuncts(fst(dest_imp(concl step))) in
          let bound=if result_zero then
              DISJ1 (level_proof st b.result_level Zero) (snd(dest_disj(List.nth conditions 2)))
            else DISJ2 (fst(dest_disj(List.nth conditions 2)))
              (arithmetic st l4_level_le (snd(dest_disj(List.nth conditions 2)))) in
          v::vs,MP step (end_itlist CONJ [decide st (List.nth conditions 0);h;bound;rest]) in
      let checked_fields=List.map (fun (_,fs) -> fields fs) b.family_constructors in
      let vss=List.map fst checked_fields and hfields=List.map snd checked_fields in
      let large=result_nonzero || b.family_constructors=[] ||
        (List.length b.family_constructors=1 &&
         List.for_all (List.for_all (fun v -> level_sample st 1 v=0)) vss) in
      let k=result_zero && (match b.family_constructors with [_,[]] -> true | _ -> false) in
      let qlarge=quote_bool large and qk=quote_bool k and qvss=quote_level_lists vss in
      let generated=generate_family st b ~large ~k in
      List.iter (fun d -> validate st [] (validation_terms d)) generated;
      let hgen=generator_calc (node "l4_family_generated" [qi;qps;qpars;qu;qcs;qlarge;qk]) in
      if not(aconv (rhs(concl hgen)) (quote_entries generated)) then
        stop Proof_failure "candidate family generator differs from HOL definition";
      let args=[quote_env env;qi;qps;qpars;qu;qcs;qvss;qlarge;qk;qclaims] in
      let definition=CONV_RULE object_calc (SUBS [hgen] (SPECL args l4_family_ok)) in
      let conditions=conjuncts(rhs(concl definition)) in
      if List.length conditions<>15 then stop Proof_failure
        ("family obligation shape: "^string_of_int(List.length conditions)^" instead of 15");
      let at i = tick st; prove(List.nth conditions i,CONV_TAC generator_calc) in
      let static=List.map (fun i -> i,at i) [0;1;2;7;8;9;11;12;13;14] in
      let hn=level_truth st l4_level_nonzero (node "l4_level_nonzero" [qu]) result_nonzero 0 in
      let zeros=List.map (fun v -> level_truth st l4_level_equiv
        (node "l4_level_equiv" [quote_level v;`L4Zero`]) (level_sample st 1 v=0) 1)
        (b.result_level::List.concat vss) in
      let flags i=prove(List.nth conditions i,
        REWRITE_TAC ([l4_family_large;l4_family_k;ALL;LENGTH;l4_ctor_fields;
          distinctness "list";injectivity "list";hn] @ zeros) THEN
        CONV_TAC NUM_REDUCE_CONV) in
      let context=EQ_MP (SYM(generator_calc (List.nth conditions 3))) hctx in
      let allfields=prove(List.nth conditions 4,
        REWRITE_TAC ([ALL2;l4_ctor_fields;REVERSE;MAP;SND;APPEND] @ hfields)) in
      let entries=generated@env.entries in
      let module Form = Native(struct let entries=entries end) in
      let formations=List.map (fun d ->
        let v,h=Form.infer_sort st [] d.typ in
        let tm=mk_exists(`v:l4_level`,node "l4_edef"
          [quote_entries entries;quote_context [];quote_expr d.typ;quote_expr d.typ;
           node "L4Sort" [`v:l4_level`]]) in
        EXISTS(tm,quote_level v) h) generated in
      let allform=prove(List.nth conditions 10,REWRITE_TAC (ALL::l4_entry_type::formations)) in
      let proofs=static @ [3,context;4,allfields;5,flags 5;6,flags 6;10,allform] in
      let hok=EQ_MP (SYM definition) (end_itlist CONJ (List.init 15 (fun i -> List.assoc i proofs))) in
      let step=REWRITE_RULE [hgen;APPEND] (SPECL args
        (List.nth(CONJUNCTS(SPEC (quote_policy env) l4_evalid_RULES)) 4)) in
      let proof=MP step (CONJ env.proof hok) in
      let detail_args=quote_policy env::args in
      let detail_def=REWRITE_RULE [hgen;APPEND] (SPECL detail_args l4_family_checked) in
      let detail=guarded (node "l4_family_checked" detail_args)
        (EQ_MP (SYM detail_def) (CONJ env.proof (CONJ hok proof))) in
      let env'={env with entries;proof;inductive_proofs=(b.family_name,detail)::env.inductive_proofs} in
      env',guarded (valid_term env') proof)

  let infer ?(fuel=100000) env g e = with_env fuel env g [e] (fun st ->
    let module Native = Native(struct let entries = env.entries end) in
    let ctx = Native.context st g in
    let a,h = Native.infer_i st g e in a,checked env g e e a ctx h)
  let check ?(fuel=100000) env g e a = with_env fuel env g [e;a] (fun st ->
    let module Native = Native(struct let entries = env.entries end) in
    let ctx = Native.context st g in checked env g e e a ctx (Native.check_i st g e a))
  let convert ?(fuel=100000) env g e e' a = with_env fuel env g [e;e';a] (fun st ->
    let module Native = Native(struct let entries = env.entries end) in
    let ctx = Native.context st g in
    ignore(Native.check_i st g e a); ignore(Native.check_i st g e' a);
    checked env g e e' a ctx (Native.cast st g (Native.equal_i st g e e') a))
end;;
