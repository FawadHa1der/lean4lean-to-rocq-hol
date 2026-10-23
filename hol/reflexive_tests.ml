(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let reflexive_axioms_before=axioms();;
needs "hol/environment.ml";;
needs "hol/reflexive_certificates.ml";;

let l4_reflexive_tests () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let before=reflexive_axioms_before and count=ref 0 in
  let test label p=if not p then failwith("reflexive: "^label) else
    (incr count; print_endline("reflexive check: "^label)) in
  let get label=function Ok x->x|Error e->failwith(label^": "^e.message) in
  let decline label=function
    | Error {kind=(Unsupported|Proof_failure);_}->test label true
    | Error e->failwith(label^": unexpected classification: "^e.message)
    | Ok _->failwith("accepted: "^label) in
  let exact label tm h = test (label^" closed") (hyp h=[] && frees(concl h)=[]);
    test (label^" conclusion") (aconv(concl h) tm) in
  let n s=Str(Anonymous,s) and child i s=Str(i,s) and one=Succ Zero in
  let pi a b=Pi(Anonymous,a,b) and lam a b=Lam(Anonymous,a,b) and app=Env.apps in
  let ctor name fields result={Env.indexed_ctor_name=name;indexed_fields=fields;result_indices=result} in
  let seal b large = {b with Env.indexed_claims=Env.generate_indexed {remaining=200000} b ~large ~k:false} in
  let candidate i ps pars inds level cs large=seal
    {Env.indexed_name=i;indexed_level_params=ps;indexed_parameters=pars;indices=inds;
     indexed_result_level=level;indexed_constructors=cs;indexed_claims=[]} large in
  let admit label env b =
    let after,h=get label (Env.admit_indexed_inductive ~fuel:300000 env b) in
    exact (label^" admission") (node "l4_evalid" [Env.quote_policy after;Env.quote_env after]) h;
    let detail=get label (Env.inductive_certificate after b.Env.indexed_name) in
    test (label^" detail closed") (hyp detail=[] && frees(concl detail)=[]);
    let head,args=strip_comb(concl detail) in
    test (label^" detail judgment") (is_const head && fst(dest_const head)="l4_index_checked");
    let meta=MATCH_MP (SPECL args l4_index_checked_metadata) detail in
    test (label^" certified metadata") (hyp meta=[]);
    let fields=MATCH_MP (SPECL args l4_index_checked_fields) detail in
    test (label^" certified field judgments") (hyp fields=[] && frees(concl fields)=[]);
    let generated=List.nth args 11 in
    test (label^" claims retained") (aconv generated
      (mk_list(List.map Env.quote_decl b.Env.indexed_claims,`:l4_entry`)));
    after in
  let stmt env g x y a=node "l4_checked" [Env.quote_policy env;Env.quote_env env;quote_context g;
    quote_expr x;quote_expr y;quote_expr a] in
  let equal label env g x y a=exact label (stmt env g x y a)
    (get label(Env.convert ~fuel:300000 env g x y a)) in
  let nt=Const(n "Nat",[]) and nat=n "Nat" in
  let nb={Env.inductive_name=nat;inductive_level=one;
    constructors=[child nat "zero",[];child nat "succ",[Env.Recursive]];claims=[]} in
  let nb={nb with Env.claims=Env.generate {remaining=100000} nb} in
  let env,_=get "Nat"(Env.admit_inductive Env.empty nb) in
  let tree=n "FunctionTree" in let tt=Const(tree,[]) in
  let leaf=child tree "leaf" and branch=child tree "branch" in
  let tb=candidate tree [] [] [] one
    [ctor leaf [] [];ctor branch [Env.Index_function([nt],[])] []] true in
  let mot=pi tt (Sort(Param(n "u"))) in
  let minor=pi (pi nt tt) (pi (pi nt (App(Bvar 3,App(Bvar 1,Bvar 0))))
    (App(Bvar 3,App(Const(branch,[]),Bvar 1)))) in
  test "independent function-field minor"
    (Env.index_minor {remaining=100000} tree [] 0 (List.nth tb.Env.indexed_constructors 1) 1=minor);
  let recfn=app(Const(child tree "rec",[Param(n "u")]))[Bvar 3;Bvar 2;Bvar 1] in
  let expected_rhs=lam mot (lam (App(Bvar 0,Const(leaf,[]))) (lam minor
    (lam (pi nt tt) (app(Bvar 1)[Bvar 0;
      lam nt (App(lift {remaining=10000} 1 0 recfn,App(Bvar 1,Bvar 0)))])))) in
  test "independent lambda-wrapped recursive RHS"
    (Env.index_rhs {remaining=100000} tree [] [] [] tb.Env.indexed_constructors true 1
      (List.nth tb.Env.indexed_constructors 1)=expected_rhs);
  test "reflexive and recursive flags generated"
    (match (List.hd tb.Env.indexed_claims).Env.kind with Env.Generated(Env.Inductive_role r)->r.Env.is_rec && r.Env.is_reflexive|_->false);
  let env=admit "function tree" env tb in
  let leafv=Const(leaf,[]) and successor=Const(child nat "succ",[]) in
  let nodev=App(Const(branch,[]),lam nt leafv) in
  let minorv=lam (pi nt tt) (lam (pi nt nt) (App(successor,App(Bvar 0,Natlit "0")))) in
  let recapp=app(Const(child tree "rec",[one]))[lam tt nt;Natlit "0";minorv;nodev] in
  equal "higher-order constructor iota" env [] recapp (Natlit "1") nt;
  let deep=App(Const(branch,[]),lam nt nodev) in
  equal "nested higher-order recursion" env []
    (app(Const(child tree "rec",[one]))[lam tt nt;Natlit "0";minorv;deep]) (Natlit "2") nt;
  let acc=n "AccessFamily" and u=n "u" in
  let ab=candidate acc [u]
    [n "A",Sort(Param u);n "r",pi (Bvar 0) (pi (Bvar 1) (Sort Zero))]
    [n "a",Bvar 1] Zero
    [ctor (child acc "intro") [Env.Index_data(Bvar 1);
      Env.Index_function([Bvar 2;app(Bvar 2)[Bvar 0;Bvar 1]],[Bvar 1])] [Bvar 1]] true in
  let env=admit "dependent Acc telescope" env ab in
  let acc_role=List.hd ab.Env.indexed_claims and acc_ctor=List.nth ab.Env.indexed_claims 1 in
  let eta_false=mk_neg(node "l4_eta_meta" [Env.quote_decl acc_role;Env.quote_decl acc_ctor;
    quote_name acc;mk_list([quote_level one],`:l4_level`);quote_context [nt;lam nt(lam nt(Sort Zero))];`2`]) in
  exact "recursive Acc cannot satisfy structure eta metadata" eta_false
    (prove(eta_false,MESON_TAC [l4_eta_recursive_excluded]));
  let p=n "EmptyRelation" in
  let pb={Env.family_name=p;level_params=[];parameters=[];result_level=Zero;
    family_constructors=[];family_claims=[]} in
  let pb={pb with Env.family_claims=Env.generate_family {remaining=100000} pb ~large:true ~k:false} in
  let env,_=get "relation Prop"(Env.admit_inductive_family env pb) in
  let prop=Const(p,[]) in
  let rel=lam nt (lam nt prop) in
  let acct x=app(Const(acc,[one]))[nt;rel;x] in
  let field=pi nt (pi prop (acct(Bvar 1))) in
  let minoracc=lam nt (lam field (lam (pi nt (pi prop nt)) (Natlit "7"))) in
  let accrec=app(Const(child acc "rec",[one;one]))
    [nt;rel;lam nt(lam(acct(Bvar 0))nt);minoracc;Natlit "0";Bvar 0] in
  let g=[acct(Natlit "0")] in
  let result,ty,h=get "neutral Acc recursor"(Env.normalize env g accrec) in
  test "no forbidden neutral Acc eta" (result=accrec);
  exact "neutral Acc certificate" (stmt env g accrec result ty) h;
  decline "neutral Acc recursor is not its minor result" (Env.convert env g accrec (Natlit "7") nt);
  let family=n "DependentBranches" and v=n "v" in
  let db=candidate family [u;v]
    [n "A",Sort(Succ(Param u));n "B",pi(Bvar 0)(Sort(Succ(Param v)))]
    [n "x",Bvar 1;n "y",App(Bvar 1,Bvar 0)] (Max(Succ(Param u),Succ(Param v)))
    [ctor(child family "mk") [Env.Index_data(Bvar 1);Env.Index_data(App(Bvar 1,Bvar 0));
      Env.Index_function([Bvar 3;App(Bvar 3,Bvar 0)],[Bvar 1;Bvar 0]);
      Env.Index_recursive[Bvar 2;Bvar 1]] [Bvar 3;Bvar 2]] true in
  ignore(admit "dependent domains indices and mixed recursion" Env.empty db);
  let pair=n "FunctionPair" in
  let fb=candidate pair [] [n "A",Sort one] [] one
    [ctor(child pair "mk") [Env.Index_function([Bvar 0],[]);
      Env.Index_function([Bvar 1],[])] []] true in
  ignore(admit "consecutive function IH binders" Env.empty fb);
  let bad_acc={ab with Env.indexed_constructors=[ctor(child acc "intro")
    [Env.Index_data(Bvar 1);Env.Index_function([Bvar 2;app(Bvar 2)[Bvar 0;Bvar 1]],[Bvar 2])] [Bvar 1]]} in
  decline "same-type recursive index substitution" (Env.admit_indexed_inductive Env.empty bad_acc);
  let bad=n "BadRecursive" in
  let bad_block fs inds results=candidate bad [] [] inds one
    [ctor(child bad "mk") fs results] true in
  decline "negative occurrence in recursive domain" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([Const(bad,[])],[])] [] []));
  decline "nested domain family occurrence" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([pi(Const(bad,[]))nt],[])] [] []));
  decline "family hidden in data function" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_data(pi nt (Const(bad,[])))] [] []));
  decline "recursive telescope forward variable" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([Bvar 0],[])] [] []));
  decline "ill-typed dependent domain" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([nt;Bvar 0],[])] [] []));
  decline "recursive index arity" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([nt],[])] [n "x",nt] [Natlit "0"]));
  decline "recursive index wrong type" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([nt],[Sort Zero])] [n "x",nt] [Natlit "0"]));
  decline "recursive index contains family" (Env.admit_indexed_inductive env
    (bad_block [Env.Index_function([nt],[App(Const(bad,[]),Natlit "0")])]
      [n "x",Sort one] [nt]));
  let fresh_tree={tb with Env.indexed_name=tree} in
  let mutate label change = decline label (Env.admit_indexed_inductive
    (fst(get "fresh Nat base"(Env.admit_inductive Env.empty nb)))
    {fresh_tree with Env.indexed_claims=List.map change tb.Env.indexed_claims}) in
  mutate "forged nonreflexive metadata" (fun d->match d.Env.kind with
    | Env.Generated(Env.Inductive_role r)->{d with Env.kind=Env.Generated(Env.Inductive_role {r with Env.is_reflexive=false})}|_->d);
  mutate "forged nonrecursive metadata" (fun d->match d.Env.kind with
    | Env.Generated(Env.Inductive_role r)->{d with Env.kind=Env.Generated(Env.Inductive_role {r with Env.is_rec=false})}|_->d);
  mutate "forged recursor IH type" (fun d->match d.Env.kind with
    | Env.Generated(Env.Recursor_role _)->{d with Env.typ=Sort one}|_->d);
  mutate "forged recursor rule RHS" (fun d->match d.Env.kind with
    | Env.Generated(Env.Recursor_role r)->{d with Env.kind=Env.Generated(Env.Recursor_role
      {r with Env.rules=List.map(fun rule->{rule with Env.rhs=Sort Zero})r.Env.rules})}|_->d);
  mutate "forged recursive-field rule count" (fun d->match d.Env.kind with
    | Env.Generated(Env.Recursor_role r)->{d with Env.kind=Env.Generated(Env.Recursor_role
      {r with Env.rules=List.map(fun (rule:Env.rec_rule)->{rule with Env.num_fields=0})r.Env.rules})}|_->d);
  let uniform=n "UniformBranch" in
  let ub=candidate uniform [] [n "A",Sort one] [] one
    [ctor(child uniform "mk") [Env.Index_function([Bvar 0],[])] []] true in
  let wrong=pi (Sort one) (pi (pi(Bvar 0)(App(Const(uniform,[]),nt)))
    (App(Const(uniform,[]),Bvar 1))) in
  decline "nonuniform recursive parameter claim" (Env.admit_indexed_inductive env
    {ub with Env.indexed_claims=List.map(fun d->if d.Env.name=child uniform "mk"
      then {d with Env.typ=wrong} else d)ub.Env.indexed_claims});
  test "resource is a decline" (match Env.admit_indexed_inductive ~fuel:0 Env.empty ab with
    Error {kind=Resource;_}->true|_->false);
  test "29 equality clauses with indexed mutual appended" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "11 admission clauses with indexed mutual appended" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "no new HOL axioms" (axioms()=before);
  Printf.printf "HOL_REFLEXIVE_TESTS_PASSED %d\n%!" !count;;
l4_reflexive_tests();;
