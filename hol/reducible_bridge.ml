(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Private bridge prototype, not an environment-admission rule.
   Reference: Lean4Lean 8223d223, Inductive/Add.lean:checkConstructors. *)
needs "hol/environment.ml";;

(* Only manifest outer binders may change their annotations. Results and
   computational RHSs remain identical modulo binder names. *)
let l4_bridge_shape = new_recursive_definition l4_expr_RECURSION
 `(l4_bridge_shape lam (L4BVar i) = L4BVar i) /\
  (l4_bridge_shape lam (L4Sort u) = L4Sort u) /\
  (l4_bridge_shape lam (L4Const n us) = L4Const n us) /\
  (l4_bridge_shape lam (L4App f a) = l4_anon (L4App f a)) /\
  (l4_bridge_shape lam (L4Lam n a b) =
    if lam then L4Lam L4Anonymous (L4Sort L4Zero) (l4_bridge_shape lam b)
    else l4_anon (L4Lam n a b)) /\
  (l4_bridge_shape lam (L4Pi n a b) =
    if lam then l4_anon (L4Pi n a b)
    else L4Pi L4Anonymous (L4Sort L4Zero) (l4_bridge_shape lam b)) /\
  (l4_bridge_shape lam (L4Let n a v b) = l4_anon (L4Let n a v b)) /\
  (l4_bridge_shape lam (L4NatLit lit) = L4NatLit lit) /\
  (l4_bridge_shape lam (L4StrLit chars) = L4StrLit chars) /\
  (l4_bridge_shape lam (L4Proj n i e) = l4_anon (L4Proj n i e))`;;
let l4_bridge_rule_shape = new_recursive_definition l4_recrule_RECURSION
 `l4_bridge_rule_shape (L4RecRule c nf r) = L4RecRule c nf (l4_bridge_shape T r)`;;
let l4_bridge_rhs = new_recursive_definition l4_recrule_RECURSION
 `l4_bridge_rhs (L4RecRule c nf r) = r`;;
let l4_bridge_role = new_recursive_definition l4_role_RECURSION
 `(l4_bridge_role (L4InductiveRole p ix ns cs nn r rf un) =
    L4InductiveRole p ix ns cs nn r rf un) /\
  (l4_bridge_role (L4ConstructorRole i j p nf un) = L4ConstructorRole i j p nf un) /\
  (l4_bridge_role (L4RecursorRole ns p ix mo mi rs k un) =
    L4RecursorRole ns p ix mo mi (MAP l4_bridge_rule_shape rs) k un)`;;
let l4_bridge_role_rules = new_recursive_definition l4_role_RECURSION
 `(l4_bridge_role_rules (L4InductiveRole p ix ns cs nn r rf un) = []) /\
  (l4_bridge_role_rules (L4ConstructorRole i j p nf un) = []) /\
  (l4_bridge_role_rules (L4RecursorRole ns p ix mo mi rs k un) = rs)`;;
let l4_bridge_forward_role = new_recursive_definition l4_role_RECURSION
 `(l4_bridge_forward_role (L4InductiveRole p ix ns cs nn r rf un) = F) /\
  (l4_bridge_forward_role (L4ConstructorRole i j p nf un) = T) /\
  (l4_bridge_forward_role (L4RecursorRole ns p ix mo mi rs k un) = T)`;;
let l4_bridge_forward_kind = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_bridge_forward_kind L4DefKind = T) /\
  (l4_bridge_forward_kind L4ThmKind = T) /\
  (l4_bridge_forward_kind L4OpaqueKind = T) /\
  (l4_bridge_forward_kind L4AxiomKind = T) /\
  (l4_bridge_forward_kind (L4Generated r) = l4_bridge_forward_role r) /\
  (l4_bridge_forward_kind (L4QuotientKind k) = T)`;;
let l4_bridge_kind = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_bridge_kind L4DefKind = L4DefKind) /\
  (l4_bridge_kind L4ThmKind = L4ThmKind) /\
  (l4_bridge_kind L4OpaqueKind = L4OpaqueKind) /\
  (l4_bridge_kind L4AxiomKind = L4AxiomKind) /\
  (l4_bridge_kind (L4Generated r) = L4Generated (l4_bridge_role r)) /\
  (l4_bridge_kind (L4QuotientKind k) = L4QuotientKind k)`;;
let l4_bridge_rules = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_bridge_rules L4DefKind = []) /\
  (l4_bridge_rules L4ThmKind = []) /\
  (l4_bridge_rules L4OpaqueKind = []) /\
  (l4_bridge_rules L4AxiomKind = []) /\
  (l4_bridge_rules (L4Generated r) = l4_bridge_role_rules r) /\
  (l4_bridge_rules (L4QuotientKind k) = [])`;;
let l4_bridge_entry_shape = new_recursive_definition l4_entry_RECURSION
 `l4_bridge_entry_shape (L4Entry k n ps a v) =
    L4Entry (l4_bridge_kind k) n ps (l4_bridge_shape F a) v`;;
let l4_bridge_entry = new_definition
 `l4_bridge_entry policy env raw canonical <=>
    (?r. l4_entry_tag canonical = L4Generated r) /\
    l4_bridge_entry_shape raw = l4_bridge_entry_shape canonical /\
    (~l4_bridge_forward_kind (l4_entry_tag canonical) ==>
      l4_anon (l4_entry_type raw) = l4_anon (l4_entry_type canonical)) /\
    l4_params_expr (l4_entry_type raw) (l4_entry_params raw) /\
    (?u. l4_checked policy env [] (l4_entry_type raw) (l4_entry_type canonical) (L4Sort u)) /\
    ALL2 (\r s.
      l4_params_expr (l4_bridge_rhs r) (l4_entry_params raw) /\
      (?a. l4_checked policy env [] (l4_bridge_rhs r) (l4_bridge_rhs s) a))
      (l4_bridge_rules (l4_entry_tag raw)) (l4_bridge_rules (l4_entry_tag canonical))`;;
let l4_bridge_family_anchor = new_definition
 `l4_bridge_family_anchor policy canonical <=>
    ?prior i ps pars u cs vss large k.
      l4_family_checked policy prior i ps pars u cs vss large k canonical`;;
let l4_ctor_conversion_bridge = new_definition
 `l4_ctor_conversion_bridge policy env raw canonical <=>
    l4_evalid policy env /\
    l4_bridge_family_anchor policy canonical /\
    (?prior. env = APPEND canonical prior) /\
    l4_names_distinct (MAP l4_entry_name raw) /\
    ALL (\d. MEM d env) canonical /\
    l4_no_nested_claims raw /\
    ALL (\d. l4_is_constructor_kind (l4_entry_tag d) ==>
      ALL (\c. l4_bridge_forward_kind (l4_entry_tag c) ==>
        l4_without_const (l4_entry_name c) (l4_entry_type d)) canonical) raw /\
    ALL2 (l4_bridge_entry policy env) raw canonical`;;
let l4_ctor_conversion_bridge_valid = prove
 (`!policy env raw canonical. l4_ctor_conversion_bridge policy env raw canonical ==>
    l4_evalid policy env`, SIMP_TAC [l4_ctor_conversion_bridge]);;

module Lean4hol_ctor_bridge = struct
  open Lean4hol
  module Env = Lean4hol_env
  let entries ds = mk_list(List.map Env.quote_decl ds,`:l4_entry`)
  let expected env raw canonical = node "l4_ctor_conversion_bridge"
    [Env.quote_policy env;Env.quote_env env;entries raw;entries canonical]
  let equations =
    [l4_bridge_entry;l4_bridge_entry_shape;l4_bridge_kind;l4_bridge_role;
     l4_bridge_rule_shape;l4_bridge_shape;l4_bridge_rhs;l4_bridge_rules;l4_bridge_role_rules;
     l4_bridge_forward_kind;l4_bridge_forward_role;l4_without_const;
     l4_entry_tag;l4_entry_name;l4_entry_params;l4_entry_type;l4_anon;
     l4_params_expr;l4_params_level;l4_names_distinct;MAP;MEM;ALL;ALL2;APPEND;
     l4_no_nested_claims;l4_no_nested_aux;l4_nested_name;
     l4_is_constructor_kind;l4_is_constructor_role;
     distinctness "l4_entry_kind";injectivity "l4_entry_kind";
     distinctness "l4_expr";injectivity "l4_expr";
     distinctness "l4_name";injectivity "l4_name";
     injectivity "l4_entry";distinctness "list";injectivity "list";
     injectivity "l4_role";distinctness "l4_role";injectivity "l4_recrule";
     UNWIND_THM1;UNWIND_THM2]
  let calc = REWRITE_CONV equations THENC NUM_REDUCE_CONV
  let static_premise tm =
    let h=calc tm in
    if rhs(concl h)=`T` then EQT_ELIM h
    else if rhs(concl h)=`F` then
      stop Proof_failure "certified false bridge premise"
    else prove(tm,CONV_TAC calc THEN MESON_TAC [])
  let get = function Ok v -> v | Error e -> raise(Stop e)
  let exact tm th =
    if hyp th<>[] || not(aconv (concl th) tm) then
      stop Proof_failure "conversion bridge certificate mismatch";
    th
  let entry st stage env (r:Env.declaration) (c:Env.declaration) =
    tick st;
    stage:="metadata shape";
    let entry_def=SPECL [Env.quote_policy env;Env.quote_env env;Env.quote_decl r;Env.quote_decl c]
      l4_bridge_entry in
    let entry_obligations=conjuncts(rhs(concl entry_def)) in
    if List.length entry_obligations<>6 then stop Proof_failure "bridge entry shape mismatch";
    List.iter (fun j -> tick st;
      ignore(static_premise(List.nth entry_obligations j))) [0;1;2;3];
    stage:="signature inference";
    let typ,_=get(Env.infer ~fuel:st.remaining env [] r.Env.typ) in
    let u=match typ with Sort u -> u | _ ->
      stop Proof_failure "raw generated signature is not a type" in
    stage:="signature conversion";
    let h=get(Env.convert ~fuel:st.remaining env [] r.Env.typ c.Env.typ (Sort u)) in
    let tm=mk_exists(`u:l4_level`,node "l4_checked"
      [Env.quote_policy env;Env.quote_env env;quote_context [];quote_expr r.Env.typ;
       quote_expr c.Env.typ;node "L4Sort" [`u:l4_level`]]) in
    let ht=EXISTS(tm,quote_level u) h in
    let rules d=match d.Env.kind with Env.Generated(Env.Recursor_role rr)->rr.Env.rules | _ -> [] in
    let rhs_proofs=List.map2 (fun (rr:Env.rec_rule) (cr:Env.rec_rule) ->
      tick st;
      stage:="rule inference";
      let ty,_=get(Env.infer ~fuel:st.remaining env [] rr.Env.rhs) in
      stage:="rule conversion";
      let h=get(Env.convert ~fuel:st.remaining env [] rr.Env.rhs cr.Env.rhs ty) in
      let tm=mk_exists(`a:l4_expr`,node "l4_checked"
        [Env.quote_policy env;Env.quote_env env;quote_context [];quote_expr rr.Env.rhs;
         quote_expr cr.Env.rhs;`a:l4_expr`]) in
      EXISTS(tm,quote_expr ty) h) (rules r) (rules c) in
    let tm=node "l4_bridge_entry" [Env.quote_policy env;Env.quote_env env;
      Env.quote_decl r;Env.quote_decl c] in
    stage:="entry certificate";
    let result=prove(tm,REWRITE_TAC equations THEN REWRITE_TAC (ht::rhs_proofs) THEN
      CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC []) in
    exact tm result
  let certify ?(fuel=100000) env raw canonical =
    let stage=ref "validation" in
    let result=run fuel [] [] (fun st ->
      if List.length raw<>List.length canonical then
        stop Proof_failure "conversion bridge claim count mismatch";
      let header=match canonical with
        | ({Env.kind=Env.Generated(Env.Inductive_role _);_} as h)::_ -> h
        | _ -> stop Unsupported "bridge requires a complete canonical family block" in
      let detail=get(Env.inductive_certificate env header.Env.name) in
      let head,args=strip_comb(concl detail) in
      if not(is_const head) || fst(dest_const head)<>"l4_family_checked" || List.length args<>11 then
        stop Unsupported "bridge requires a family admission detail certificate";
      let definition=SPECL [Env.quote_policy env;entries canonical] l4_bridge_family_anchor in
      let witnesses=List.init 9 (fun j -> List.nth args (j+1)) in
      let rec exists tm = function
        | [] -> exact tm detail
        | a::rest ->
          let v,body=dest_exists tm in
          EXISTS(tm,a) (exists (vsubst [a,v] body) rest) in
      let anchor=EQ_MP (SYM definition) (exists (rhs(concl definition)) witnesses) in
      let definition=SPECL [Env.quote_policy env;Env.quote_env env;entries raw;entries canonical]
        l4_ctor_conversion_bridge in
      let obligations=conjuncts(rhs(concl definition)) in
      if List.length obligations<>8 then stop Proof_failure "bridge obligation shape mismatch";
      stage:="block metadata and scope";
      let static=Env.certificate env::anchor::List.map (fun j ->
        tick st; prove(List.nth obligations j,CONV_TAC calc THEN MESON_TAC [])) [2;3;4;5;6] in
      let conversions=List.map2 (entry st stage env) raw canonical in
      let tm=expected env raw canonical in
      stage:="block certificate";
      let all_entries=prove(List.nth obligations 7,REWRITE_TAC (ALL2::conversions)) in
      exact tm (EQ_MP (SYM definition) (end_itlist CONJ (static@[all_entries])))) in
    match result with Ok _ -> result | Error e ->
      Error {e with message="constructor bridge " ^ !stage ^ ": " ^ e.message}
end;;
