(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let mutual_axioms_before=axioms();;
needs "hol/environment.ml";;

let l4_mutual_tests group =
  let open Lean4hol in let module Env=Lean4hol_env in
  let count=ref 0 in
  let test label ok=if not ok then failwith("mutual: "^label) else
    (incr count;print_endline("mutual check: "^label)) in
  let get label=function Ok x->x|Error e->failwith(label^": "^e.message) in
  let decline label=function
    | Error {kind=(Unsupported|Proof_failure);_}->test label true
    | Error e->failwith(label^": unexpected error: "^e.message)
    | Ok _->failwith("accepted: "^label) in
  let exact label tm h=test(label^" closed")(hyp h=[] && frees(concl h)=[]);
    test(label^" conclusion")(aconv(concl h)tm) in
  let n s=Str(Anonymous,s) and child i s=Str(i,s) and one=Succ Zero in
  let pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) and app=Env.apps in
  let ctor n fs={Env.mutual_ctor_name=n;mutual_fields=fs} in
  let family n cs={Env.mutual_name=n;mutual_constructors=cs} in
  let seal b large={b with Env.mutual_claims=Env.generate_mutual {remaining=500000} b ~large} in
  let candidate ps pars u bs large=seal {Env.mutual_level_params=ps;mutual_parameters=pars;
    mutual_result_level=u;mutual_families=bs;mutual_claims=[]}large in
  let stmt env g x y a=node "l4_checked"[Env.quote_policy env;Env.quote_env env;
    quote_context g;quote_expr x;quote_expr y;quote_expr a] in
  let equal label env g x y a=exact label(stmt env g x y a)
    (get label(Env.convert ~fuel:500000 env g x y a)) in
  let admit label env b=
    let next,h=get label(Env.admit_mutual_inductive ~fuel:500000 env b) in
    exact(label^" admission")(node "l4_evalid"[Env.quote_policy next;Env.quote_env next])h;
    List.iter(fun f->let detail=get label(Env.inductive_certificate next f.Env.mutual_name) in
      test(label^" detail closed")(hyp detail=[] && frees(concl detail)=[]);
      let head,args=strip_comb(concl detail) in
      test(label^" detail judgment")(is_const head && fst(dest_const head)="l4_mutual_checked");
      test(label^" original claims retained")(aconv(List.nth args 7)
        (mk_list(List.map Env.quote_decl b.Env.mutual_claims,`:l4_entry`)));
      let hm=MATCH_MP(SPECL args l4_mutual_checked_metadata)detail in
      let hf=MATCH_MP(SPECL args l4_mutual_checked_fields)detail in
      test(label^" derived metadata and field certificates")(hyp hm=[] && hyp hf=[]))b.Env.mutual_families;
    exact(label^" policy invariant")
      (mk_comb(mk_comb(`ALL:(l4_entry->bool)->l4_entry list->bool`,
        mk_abs(`d:l4_entry`,mk_imp(mk_eq(node "l4_entry_tag"[`d:l4_entry`],`L4AxiomKind`),
          mk_comb(mk_comb(`MEM:l4_entry->l4_entry list->bool`,`d:l4_entry`),Env.quote_policy next)))),
        Env.quote_env next))
      (MATCH_MP(SPECL[Env.quote_policy next;Env.quote_env next]l4_evalid_permissions)h);
    next in
  let nt=Const(n "Nat",[]) and nat=n "Nat" in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000}nb} in
  let base,_=get "Nat"(Env.admit_inductive Env.empty nb) in
  let a=n "EvenTree" and b=n "OddTree" in
  let at=Const(a,[]) and bt=Const(b,[]) in
  let zero=child a "zero" and an=child a "next" and bn=child b "next" in
  let spec=candidate [] [] one
    [family a[ctor zero[];ctor an[Env.Mutual_recursive(b,[])]];
     family b[ctor bn[Env.Mutual_recursive(a,[])]]]true in
  if group="positive" then (
    let minorA=pi bt(pi(App(Bvar 2,Bvar 0))(App(Bvar 4,App(Const(an,[]),Bvar 1)))) in
    test "independent cross-family minor selects second motive"
      (Env.mutual_minor {remaining=100000}[a;b][]0(0,List.nth(List.hd spec.Env.mutual_families).Env.mutual_constructors 1)1=minorA);
    let env=admit "direct two-family" base spec in
    let succ=Const(child nat "succ",[]) in
    let ma=lam bt(lam nt(App(succ,Bvar 0))) and mb=lam at(lam nt(App(succ,Bvar 0))) in
    let prefix=[lam at nt;lam bt nt;Natlit "0";ma;mb] in
    let av=Const(zero,[]) and bv=App(Const(bn,[]),Const(zero,[])) in
    equal "second family constructor iota" env [] (app(Const(child b "rec",[one]))(prefix@[bv]))(Natlit "1")nt;
    equal "joint recursion through both families" env []
      (app(Const(child a "rec",[one]))(prefix@[App(Const(an,[]),bv)]))(Natlit "2")nt;
    let x,ty,h=get "neutral recursive major"(Env.normalize env [at]
      (app(Const(child a "rec",[one]))(prefix@[Bvar 0]))) in
    test "recursive neutral major is not eta expanded"
      (x=app(Const(child a "rec",[one]))(prefix@[Bvar 0]));
    exact "neutral mutual recursor"(stmt env[at]x x ty)h;
    decline "no mutual recursive unit eta"(Env.convert env[at]
      (app(Const(child a "rec",[one]))(prefix@[Bvar 0]))(Natlit "0")nt);
    ignore(admit "permuted claim table" base {spec with Env.mutual_claims=List.rev spec.Env.mutual_claims});
    let c=n "ThirdFamily" in
    let tri=candidate[][]one
      [family a[ctor zero[];ctor an[Env.Mutual_recursive(b,[])]];
       family b[ctor bn[Env.Mutual_recursive(c,[])]];
       family c[ctor(child c "next")[Env.Mutual_recursive(a,[])]]]true in
    let tri_env=admit "three-family joint motives" base tri in
    let cv=App(Const(child c "next",[]),av) in
    let prefix3=[lam at nt;lam bt nt;lam(Const(c,[]))nt;Natlit "0";
      ma;lam(Const(c,[]))(lam nt(App(succ,Bvar 0)));mb] in
    equal "three-family cycle iota" tri_env []
      (app(Const(child a "rec",[one]))(prefix3@[App(Const(an,[]),App(Const(bn,[]),cv))]))(Natlit "3")nt
  );
  if group="higher" then (
    let t=n "MutFunctionTree" and f=n "MutFunctionForest" in
    let tt=Const(t,[]) and ft=Const(f,[]) in
    let leaf=child t "leaf" and branch=child t "branch" and nil=child f "nil" and cons=child f "cons" in
    let spec=candidate[][]one
      [family t[ctor leaf[];ctor branch[Env.Mutual_recursive(f,[nt])]];
       family f[ctor nil[];ctor cons[Env.Mutual_recursive(t,[]);Env.Mutual_recursive(t,[nt]);
         Env.Mutual_recursive(f,[])]]]true in
    let env=admit "cross-family function recursion" base spec in
    test "recursive and reflexive flags shared by all families"
      (List.for_all(fun d->match d.Env.kind with Env.Generated(Env.Inductive_role r)->
        r.Env.is_rec && r.Env.is_reflexive|_->true)spec.Env.mutual_claims);
    let succ=Const(child nat "succ",[]) in
    let branchcase=lam(pi nt ft)(lam(pi nt nt)(App(succ,App(Bvar 0,Natlit "0")))) in
    let conscase=lam tt(lam(pi nt tt)(lam ft(lam nt(lam(pi nt nt)(lam nt
      (App(succ,App(Bvar 1,Natlit "0")))))))) in
    let prefix=[lam tt nt;lam ft nt;Natlit "0";branchcase;Natlit "0";conscase] in
    let leafv=Const(leaf,[]) in
    let tree_major=App(Const(branch,[]),lam nt(app(Const(cons,[]))
      [leafv;lam nt leafv;Const(nil,[])])) in
    equal "higher-order cross-family iota" env [] (app(Const(child t "rec",[one]))(prefix@[tree_major]))(Natlit "2")nt
  );
  if group="dependent" then (
    let u=n "u" and v=n "v" and da=n "DependentMutA" and db=n "DependentMutB" in
    let dep=candidate[u;v][n "X",Sort(Succ(Param u));n "Y",pi(Bvar 0)(Sort(Succ(Param v)))]
      (Max(Succ(Param u),Succ(Param v)))
      [family da[ctor(child da "mk")[Env.Mutual_data(Bvar 1);Env.Mutual_data(App(Bvar 1,Bvar 0));
        Env.Mutual_recursive(db,[Bvar 3;App(Bvar 3,Bvar 0)]);Env.Mutual_recursive(da,[])]];
       family db[ctor(child db "base")[];ctor(child db "mk")[Env.Mutual_recursive(da,[Bvar 1])]]]true in
    let denv=admit "dependent parameter and prior-field telescopes" Env.empty dep in
    let header=List.find(fun d->d.Env.name=da)(Env.declarations denv) in
    let constructor_decl=List.find(fun d->d.Env.name=child da "mk")(Env.declarations denv) in
    let eta=mk_neg(node "l4_eta_meta"[Env.quote_decl header;Env.quote_decl constructor_decl;quote_name da;
      mk_list([quote_level Zero;quote_level Zero],`:l4_level`);quote_context[nt;lam nt nt];`4`]) in
    exact "mutual recursive eta metadata excluded" eta(prove(eta,MESON_TAC[l4_eta_recursive_excluded]))
  );
  if group="prop" then (
    let pa=n "MutPropA" and pb=n "MutPropB" in
    let prop=candidate[][]Zero[family pa[ctor(child pa "mk")[Env.Mutual_recursive(pb,[])]];
      family pb[ctor(child pb "mk")[Env.Mutual_recursive(pa,[])];ctor(child pb "base")[]]]false in
    let penv=admit "Prop mutual small elimination" Env.empty prop in
    test "mutual Prop has no K and no extra eliminator universe"
      (List.for_all(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
        not r.Env.k && d.Env.params=[]|_->true)(Env.declarations penv));
    decline "mutual Prop cannot claim large elimination"(Env.admit_mutual_inductive Env.empty(seal prop true));
    let empty=candidate[][]Zero[family(n "EmptyMutA")[];family(n "EmptyMutB")[]]false in
    ignore(admit "empty Prop pair still small elimination" Env.empty empty)
  );
  if group="metadata" || group="metadata2" then (
    let number=ref 0 in
    let change label edit=incr number;
      if (!number<=7)=(group="metadata") then decline label(Env.admit_mutual_inductive base
        {spec with Env.mutual_claims=List.map edit spec.Env.mutual_claims}) in
    change "forged owner"(fun d->match d.Env.kind with Env.Generated(Env.Constructor_role r)->
      {d with Env.kind=Env.Generated(Env.Constructor_role {r with Env.induct=b})}|_->d);
    change "forged motive count"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.num_motives=1})}|_->d);
    change "forged minor count"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.num_minors=2})}|_->d);
    change "forged recursive flag"(fun d->match d.Env.kind with Env.Generated(Env.Inductive_role r)->
      {d with Env.kind=Env.Generated(Env.Inductive_role {r with Env.is_rec=false})}|_->d);
    change "forged reflexive flag"(fun d->match d.Env.kind with Env.Generated(Env.Inductive_role r)->
      {d with Env.kind=Env.Generated(Env.Inductive_role {r with Env.is_reflexive=true})}|_->d);
    change "forged K"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.k=true})}|_->d);
    change "forged cross-family RHS"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.rules=List.map
        (fun rule->{rule with Env.rhs=Sort Zero})r.Env.rules})}|_->d);
    change "forged rule owner"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.rules=List.map
        (fun rule->{rule with Env.ctor=zero})r.Env.rules})}|_->d);
    change "inconsistent result sort"(fun d->if d.Env.name=b then {d with Env.typ=Sort(Succ one)}else d);
    change "inconsistent level parameters"(fun d->if d.Env.name=b then {d with Env.params=[n "v"]}else d);
    change "forged index metadata"(fun d->match d.Env.kind with Env.Generated(Env.Inductive_role r)->
      {d with Env.kind=Env.Generated(Env.Inductive_role {r with Env.num_indices=1})}|_->d);
    change "forged family list"(fun d->match d.Env.kind with Env.Generated(Env.Recursor_role r)->
      {d with Env.kind=Env.Generated(Env.Recursor_role {r with Env.all=[a]})}|_->d);
    change "extra constructor result index"(fun d->if d.Env.name=an
      then {d with Env.typ=pi bt(App(at,Natlit "0"))}else d);
    if group="metadata2" then (
    decline "missing original family claim"(Env.admit_mutual_inductive base
      {spec with Env.mutual_claims=List.filter(fun d->d.Env.name<>b)spec.Env.mutual_claims});
    decline "missing generated family"(Env.admit_mutual_inductive base
      {spec with Env.mutual_families=[List.hd spec.Env.mutual_families]});
    decline "duplicate original claim"(Env.admit_mutual_inductive base
      {spec with Env.mutual_claims=List.hd spec.Env.mutual_claims::spec.Env.mutual_claims}))
  );
  if group="negative" then (
    let bad fields=candidate[][]one[family a[ctor an fields];family b[ctor bn[]]]true in
    decline "cross-family negative data occurrence"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_data(pi bt nt)]));
    decline "cross-family domain occurrence"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_recursive(a,[bt])]));
    decline "nested cross-family domain occurrence"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_recursive(a,[pi nt bt])]));
    decline "data field hiding positive occurrence"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_data(pi nt bt)]));
    decline "recursive telescope forward reference"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_recursive(b,[Bvar 0])]));
    decline "ill-typed telescope domain"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_recursive(b,[nt;Bvar 0])]));
    decline "field universe exceeds result"(Env.admit_mutual_inductive base
      (bad[Env.Mutual_data(Sort one)]));
    let unknown={spec with Env.mutual_families=[family a[ctor an[Env.Mutual_recursive(n "Absent",[])]];
      family b[ctor bn[]]]} in
    decline "target outside entire block"(Env.admit_mutual_inductive base unknown);
    let u=n "u" in
    let param=candidate[u][n "X",Sort(Param u)](Param u)
      [family a[ctor an[Env.Mutual_recursive(b,[])]];family b[ctor bn[]]]false in
    decline "inconsistent parameter header"(Env.admit_mutual_inductive base
      {param with Env.mutual_claims=List.map(fun d->if d.Env.name=b
        then {d with Env.typ=pi(Sort(Succ(Param u)))(Sort(Param u))}else d)param.Env.mutual_claims});
    decline "nonuniform recursive parameter claim"(Env.admit_mutual_inductive base
      {param with Env.mutual_claims=List.map(fun d->if d.Env.name=an
        then {d with Env.typ=pi(Sort(Param u))(pi(App(Const(b,[Param u]),nt))
          (App(Const(a,[Param u]),Bvar 1)))}else d)param.Env.mutual_claims});
    test "explicit fuel decline"(match Env.admit_mutual_inductive ~fuel:0 base spec with
      Error {kind=Resource;_}->true|_->false)
  );
  test "29 equality clauses including indexed mutual iota"(List.length(CONJUNCTS l4_edef_RULES)=29);
  test "11 admission clauses including indexed mutual admission"
    (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms"(axioms()=mutual_axioms_before);
  Printf.printf "HOL_MUTUAL_%s_TESTS_PASSED %d\n%!"(String.uppercase_ascii group)!count;;
