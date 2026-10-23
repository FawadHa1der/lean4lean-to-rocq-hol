(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let mindex_axioms_before=axioms();;
needs "hol/environment.ml";;
let l4_mindex_tests group =
  let open Lean4hol in let module Env=Lean4hol_env in
  let count=ref 0 in
  let test label ok=if not ok then failwith("mindex: "^label) else
    (incr count;print_endline("mindex check: "^label)) in
  let get label=function Ok x->x|Error e->failwith(label^": "^e.message) in
  let decline label=function Error{kind=(Proof_failure|Unsupported);_}->test label true
    |Error e->failwith(label^": "^e.message)|Ok _->failwith("accepted: "^label) in
  let exact label tm h=test(label^" closed")(hyp h=[] && frees(concl h)=[]);
    test(label^" exact")(aconv(concl h)tm) in
  let n s=Str(Anonymous,s) and child i s=Str(i,s) and one=Succ Zero in
  let app=Env.apps and pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) in
  let c name fields xs={Env.mindex_ctor_name=name;mindex_fields=fields;mindex_result_indices=xs} in
  let fam name inds cs={Env.mindex_name=name;mindex_indices=inds;mindex_constructors=cs} in
  let seal b large={b with Env.mindex_claims=Env.generate_mindex {remaining=500000} b ~large} in
  let spec ps pars u bs large=seal{Env.mindex_level_params=ps;mindex_parameters=pars;
    mindex_result_level=u;mindex_families=bs;mindex_claims=[]}large in
  let stmt env g x y a=node "l4_checked"[Env.quote_policy env;Env.quote_env env;
    quote_context g;quote_expr x;quote_expr y;quote_expr a] in
  let equal label env g x y a=exact label(stmt env g x y a)
    (get label(Env.convert ~fuel:500000 env g x y a)) in
  let admit label env b=
    let next,h=get label(Env.admit_indexed_mutual ~fuel:500000 env b) in
    exact(label^" admission")(node "l4_evalid"[Env.quote_policy next;Env.quote_env next])h;
    List.iter(fun f->let detail=get label(Env.inductive_certificate next f.Env.mindex_name) in
      test(label^" detail closed")(hyp detail=[] && frees(concl detail)=[]);
      let head,args=strip_comb(concl detail) in
      test(label^" detail judgment")(is_const head && fst(dest_const head)="l4_mindex_checked");
      test(label^" original claims retained")(aconv(List.nth args 7)
        (mk_list(List.map Env.quote_decl b.Env.mindex_claims,`:l4_entry`)));
      let hm=MATCH_MP(SPECL args l4_mindex_checked_metadata)detail
      and hf=MATCH_MP(SPECL args l4_mindex_checked_fields)detail in
      test(label^" metadata and field proofs closed")(hyp hm=[] && hyp hf=[]))b.Env.mindex_families;
    test(label^" permission invariant closed")
      (hyp(MATCH_MP(SPECL[Env.quote_policy next;Env.quote_env next]l4_evalid_permissions)h)=[]);
    next in
  let nat=n "Nat" and nt=Const(n "Nat",[]) in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000}nb} in
  let base,_=get "Nat"(Env.admit_inductive Env.empty nb) in
  let a=n "IxA" and b=n "IxB" in
  let at x=App(Const(a,[]),x) and bt x=App(Const(b,[]),x) in
  let succ x=App(Const(child nat "succ",[]),x) in
  let az=child a "base" and an=child a "step" and bn=child b "step" in
  let pair u=spec[][]u
    [fam a[n "n",nt][c az[Env.Mindex_data nt][Bvar 0];
      c an[Env.Mindex_data nt;Env.Mindex_recursive(b,[],[Bvar 0])][succ(Bvar 1)]];
     fam b[n "n",nt][c bn[Env.Mindex_data nt;Env.Mindex_recursive(a,[],[Bvar 0])][succ(Bvar 1)]]]
    (u=one) in
  if List.mem group ["type";"metadata_a";"metadata_b";"metadata_c";"indices_a";"indices_b"] then (
    let input=pair one in
    let env=admit "Type indexed mutual baseline" base input in
    if group="type" then (
      let ma=lam nt(lam(bt(Bvar 0))(lam nt(succ(Bvar 0))))
      and mb=lam nt(lam(at(Bvar 0))(lam nt(succ(Bvar 0)))) in
      let prefix=[lam nt(lam(at(Bvar 0))nt);lam nt(lam(bt(Bvar 0))nt);lam nt(Natlit "0");ma;mb] in
      let bv=app(Const(bn,[]))[Natlit "0";App(Const(az,[]),Natlit "0")] in
      let av=app(Const(an,[]))[Natlit "1";bv] in
      let rec_a x major=app(Const(child a "rec",[one]))(prefix@[x;major]) in
      equal "indexed iota across both families" env[](rec_a(Natlit "2")av)(Natlit "2")nt;
      equal "second indexed family iota" env[]
        (app(Const(child b "rec",[one]))(prefix@[Natlit "1";bv]))(Natlit "1")nt;
      decline "wrong recursor major index"(Env.check env[](rec_a(Natlit "3")av)nt);
      let neutral=rec_a(Natlit "0")(Bvar 0) in
      let r,ty,h=get "neutral indexed major"(Env.normalize env[at(Natlit "0")]neutral) in
      test "recursive indexed major does not eta expand"(r=neutral);
      exact "neutral indexed conversion"(stmt env[at(Natlit "0")]neutral r ty)h);
    if List.mem group ["metadata_a";"metadata_b";"metadata_c"] then (
      let change label edit=decline label(Env.admit_indexed_mutual base
        {input with Env.mindex_claims=List.map edit input.Env.mindex_claims}) in
      if group="metadata_a" then (
      change "forged motive count"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
        {d with Env.kind=Env.Generated(Env.Recursor_role{r with Env.num_motives=1})}|_->d);
      change "forged index count"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
        {d with Env.kind=Env.Generated(Env.Recursor_role{r with Env.num_indices=0})}|_->d);
      change "forged recursive RHS index"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
        {d with Env.kind=Env.Generated(Env.Recursor_role{r with Env.rules=List.map
          (fun r->{r with Env.rhs=Sort Zero})r.Env.rules})}|_->d));
      if group="metadata_b" then (
      change "forged ownership"(fun d->match d.Env.kind with Env.Generated(Env.Constructor_role r)->
        {d with Env.kind=Env.Generated(Env.Constructor_role{r with Env.induct=b})}|_->d);
      change "forged K"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
        {d with Env.kind=Env.Generated(Env.Recursor_role{r with Env.k=true})}|_->d);
      change "unsafe constructor metadata"(fun d->match d.Env.kind with Env.Generated(Env.Constructor_role r)->
        {d with Env.kind=Env.Generated(Env.Constructor_role{r with Env.is_unsafe=true})}|_->d));
      if group="metadata_c" then (
      change "nested header metadata"(fun d->match d.Env.kind with Env.Generated(Env.Inductive_role r)->
        {d with Env.kind=Env.Generated(Env.Inductive_role{r with Env.num_nested=1})}|_->d);
      change "inconsistent result universe"(fun d->if d.Env.name=b then
        {d with Env.typ=pi nt(Sort(Succ one))}else d);
      decline "duplicate claim"(Env.admit_indexed_mutual base
        {input with Env.mindex_claims=List.hd input.Env.mindex_claims::input.Env.mindex_claims})));
    if group="indices_a" || group="indices_b" then (
      let replace fields xs=let bs=[fam a[n "n",nt][c an fields xs];List.nth input.Env.mindex_families 1] in
        spec[][]one bs true in
      if group="indices_a" then (
      decline "ill-typed recursive index"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt;Env.Mindex_recursive(b,[],[Sort Zero])][Bvar 1]));
      decline "recursive index count"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt;Env.Mindex_recursive(b,[],[])][Bvar 1]));
      decline "forward recursive index"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_recursive(b,[],[Bvar 0])][Natlit "0"]));
      decline "ill-typed result index"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt][Sort Zero])));
      if group="indices_b" then (
      decline "family occurrence in index"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt;Env.Mindex_recursive(b,[],[at(Bvar 0)])][Bvar 1]));
      decline "negative cross-family data"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt;Env.Mindex_data(pi(bt(Bvar 0))nt)][Bvar 1]));
      decline "negative cross-family function domain"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data nt;Env.Mindex_recursive(a,[bt(Bvar 0)],[Bvar 1])][Bvar 1]));
      decline "field universe exceeds result"(Env.admit_indexed_mutual base
        (replace[Env.Mindex_data(Sort one)][Natlit "0"]));
      test "fuel zero stays Resource"(match Env.admit_indexed_mutual ~fuel:0 base input with
        Error{kind=Resource;_}->true|_->false))));
  if group="higher" then (
    let ha=n "FnIxA" and hb=n "FnIxB" in
    let hat x=App(Const(ha,[]),x) and hbt x=App(Const(hb,[]),x) in
    let mk=child ha "mk" and z=child hb "base" and step=child hb "step" in
    let ft=pi nt(hbt(succ(Bvar 0))) in
    let input=spec[][]one
      [fam ha[n "n",nt][c mk[Env.Mindex_data nt;
        Env.Mindex_recursive(hb,[nt],[succ(Bvar 0)])][Bvar 1]];
       fam hb[n "n",nt][c z[Env.Mindex_data nt][Bvar 0];
        c step[Env.Mindex_data nt;Env.Mindex_recursive(ha,[],[Bvar 0])][succ(Bvar 1)]]]true in
    let env=admit "function-bound recursive indices" base input in
    let prefix=[lam nt(lam(hat(Bvar 0))nt);lam nt(lam(hbt(Bvar 0))nt);
      lam nt(lam ft(lam(pi nt nt)(succ(App(Bvar 0,Natlit "0")))));
      lam nt(Natlit "0");lam nt(lam(hat(Bvar 0))(lam nt(succ(Bvar 0))))] in
    let inner=lam nt(App(Const(z,[]),succ(Bvar 0))) in
    let fn=lam nt(app(Const(step,[]))[Bvar 0;app(Const(mk,[]))[Bvar 0;inner]]) in
    let major=app(Const(mk,[]))[Natlit "7";fn] in
    equal "function-index iota through both motives" env[]
      (app(Const(child ha "rec",[one]))(prefix@[Natlit "7";major]))(Natlit "3")nt;
    decline "function result index mismatch"(Env.check env[]
      (app(Const(mk,[]))[Natlit "7";lam nt(App(Const(z,[]),Natlit "42"))])(hat(Natlit "7"))));
  if group="mixed" then (
    let ma=n "MixedA" and mb=n "MixedB" in
    let mat=Const(ma,[]) and mbt x=App(Const(mb,[]),x) in
    let mk=child ma "mk" and z=child mb "base" and step=child mb "step" in
    let input=spec[][]one
      [fam ma[][c mk[Env.Mindex_data nt;Env.Mindex_recursive(mb,[],[Bvar 0])][]];
       fam mb[n "n",nt][c z[Env.Mindex_data nt][Bvar 0];
        c step[Env.Mindex_data nt;Env.Mindex_recursive(ma,[],[])][succ(Bvar 1)]]]true in
    let env=admit "mixed zero/nonzero index arities" base input in
    let prefix=[lam mat nt;lam nt(lam(mbt(Bvar 0))nt);
      lam nt(lam(mbt(Bvar 0))(lam nt(succ(Bvar 0))));
      lam nt(Natlit "0");lam nt(lam mat(lam nt(succ(Bvar 0))))] in
    let inner=app(Const(mk,[]))[Natlit "0";App(Const(z,[]),Natlit "0")] in
    let major=app(Const(mk,[]))[Natlit "1";app(Const(step,[]))[Natlit "0";inner]] in
    equal "mixed iota uses both preserved and appended clauses" env[]
      (app(Const(child ma "rec",[one]))(prefix@[major]))(Natlit "3")nt);
  if group="prop" then (
    let input=pair Zero in
    let env=admit "Prop indexed mutual baseline" base input in
    test "all Prop recursors small and not K"(List.for_all(fun d->match d.Env.kind with
      Env.Generated(Env.Recursor_role r)->not r.Env.k && d.Env.params=[]|_->true)input.Env.mindex_claims);
    decline "forged Prop large elimination"(Env.admit_indexed_mutual base(seal input true));
    let typea=at(Natlit "0") in
    let hd=List.find(fun d->d.Env.name=a)(Env.declarations env)
    and ct=List.find(fun d->d.Env.name=az)(Env.declarations env) in
    let eta=mk_neg(node "l4_eta_meta"[Env.quote_decl hd;Env.quote_decl ct;quote_name a;
      mk_list([],`:l4_level`);quote_context[];`1`]) in
    exact "indexed recursive eta forbidden"eta(prove(eta,MESON_TAC[l4_eta_recursive_excluded]));
    ignore typea);
  if List.mem group ["dependent";"uniform_levels";"uniform_params"] then (
    let u=n "u" and v=n "v" and da=n "DepIxA" and db=n "DepIxB" in
    let input=spec[u;v][n "X",Sort(Succ(Param u));n "Y",pi(Bvar 0)(Sort(Succ(Param v)))]
      (Max(Succ(Param u),Succ(Param v)))
      [fam da[n "x",Bvar 1][c(child da "mk")
        [Env.Mindex_data(Bvar 1);Env.Mindex_recursive(db,[App(Bvar 1,Bvar 0)],[Bvar 1;Bvar 0])][Bvar 1]];
       fam db[n "x",Bvar 1;n "y",App(Bvar 1,Bvar 0)]
        [c(child db "base")[Env.Mindex_data(Bvar 1);Env.Mindex_data(App(Bvar 1,Bvar 0))][Bvar 1;Bvar 0];
         c(child db "step")[Env.Mindex_data(Bvar 1);Env.Mindex_data(App(Bvar 1,Bvar 0));
           Env.Mindex_recursive(da,[],[Bvar 1])][Bvar 2;Bvar 1]]]true in
    ignore(admit "dependent cross-family function indices" Env.empty input);
    test "unequal dependent index arities"(List.map(fun f->List.length f.Env.mindex_indices)input.Env.mindex_families=[1;2]);
    if group="uniform_levels" then (
      let claims=List.map(fun d->if d.Env.name=db then {d with Env.params=[v;u]}else d)input.Env.mindex_claims in
      decline "nonuniform level parameter order"(Env.admit_indexed_mutual Env.empty{input with Env.mindex_claims=claims}));
    if group="uniform_params" then (
      let rec swap = function
        |App(App(App(App(Const(i,us),x),y),a),b) when i=db->
          app(Const(i,us))[y;x;a;b]
        |Pi(n,a,b)->Pi(n,swap a,swap b)
        |App(f,a)->App(swap f,swap a)
        |e->e in
      let claims=List.map(fun d->if d.Env.name=child da "mk" then
        {d with Env.typ=swap d.Env.typ}else d)input.Env.mindex_claims in
      test "uniformity mutation changed only candidate claim"(claims<>input.Env.mindex_claims);
      decline "nonuniform recursive parameter claim"(Env.admit_indexed_mutual Env.empty{input with Env.mindex_claims=claims})));
  test "29 native rules"(List.length(CONJUNCTS l4_edef_RULES)=29);
  test "11 admission rules"(List.length(CONJUNCTS(SPEC `[]:l4_entry list`l4_evalid_RULES))=11);
  test "no new HOL axioms"(axioms()=mindex_axioms_before);
  Printf.printf "HOL_MINDEX_%s_TESTS_PASSED %d\n%!"(String.uppercase_ascii group)!count;;
