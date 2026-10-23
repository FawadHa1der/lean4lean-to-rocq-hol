needs "tests/hol_reflection/nat_instantiation_tests.ml";;

module Lean4hol_unified_tests = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Old=Lean4hol_nat_tests
  module Fix=Lean4hol_reflection_fixture
  module Syn=Lean4hol_reflection_syntax
  module Ref=Lean4hol_reflection
  module Cond=Lean4hol_reflected_condition
  module Comp=Lean4hol_nat_instantiation
  let count=ref 0
  let test label b=if not b then failwith label else
    (incr count;Printf.printf "UNIFIED_CHECK %d %s\n%!" !count label)
  let exact label target h=test label
    (hyp h=[] && frees(concl h)=[] && aconv target (concl h))
  let get=Fix.get
  let frozen=ref None
  let env ()=match !frozen with Some(e,q,p) ->
      if not(aconv q (Env.quote_env !Old.env)) || not(aconv p (Env.quote_policy !Old.env)) then
        failwith "final environment changed after seal";e
    | None -> failwith "environment not sealed"
  let seal ()=let e= !Old.env in frozen:=Some(e,Env.quote_env e,Env.quote_policy e);
    test "one final empty policy" (Env.permissions e=[])
  let j ()=node "l4_checked" [Env.quote_policy(env());Env.quote_env(env())]
  let raw ()=node "l4_edef" [Env.quote_env(env())]
  let contract second kind =
    let r=Syn.reflection second in
    if kind="ite" then "l4_reflection_ite_contract",List.map quote_expr [r.Syn.typ;r.Syn.to_dec]
    else "l4_reflection_dite_contract",List.map quote_expr
      [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec]
  let goals second kind =
    let id,args=contract second kind in let v=genvar(type_of(j())) in
    conjuncts(rhs(concl(INST [j(),v] (Syn.calc(node id (v::args))))))
  let proofs=ref []
  let remember target h=exact "prepared exact final-environment judgment" target h;
    proofs:=h::!proofs
  let find target=List.find_opt (fun h -> aconv target (concl h)) (!proofs @ !Old.prepared)
  let decode_goal target=match snd(strip_comb target) with
    | [p;e;g;l;r;t] when aconv p (Env.quote_policy(env())) &&
        aconv e (Env.quote_env(env())) && aconv g (quote_context []) ->
      Syn.decode l,Syn.decode r,Syn.decode t
    | _ -> failwith "unexpected closed capability obligation"
  let prepare_type second kind i=
    let target=List.nth (goals second kind) i in
    let h=match find target with Some h -> h | None ->
      let l,r,t=decode_goal target in
      if l<>r then failwith "type stage was given an equation";
      get "genuine capability typing" (Env.check ~fuel:200000 (env()) [] l t) in
    remember target h
  let branch=ref None
  let peel l r t =
    let rec go g l r t=match l,r,t with
      | Lam(_,a,b),Lam(_,a',b'),Pi(_,d,u) when a=a' && a=d -> go (a::g) b b' u
      | _ -> g,l,r,t in go [] l r t
  let branch_body second kind positive=
    let i=(if kind="ite" then 2 else 5)+(if positive then 0 else 1) in
    let target=List.nth (goals second kind) i in
    let l,r,t=decode_goal target in
    let g,l,r,t=peel l r t in
    let proof=Comp.convert (env()) g l r t in
    ignore(Comp.pack (env()) g l r t proof.Comp.h);
    branch:=Some(target,proof);
    test "body equation in original typed context" true
  let close_branch ()=match !branch with None -> failwith "missing branch body" | Some(target,h) ->
    let rec close h=if h.Comp.g=[] then h else close(Comp.close h) in
    let h=close h in remember target h.Comp.h;branch:=None
  let certificates=ref []
  let certify second kind=
    let gs=goals second kind in
    let ps=List.map (fun g -> match find g with Some h->h | None->failwith "missing obligation") gs in
    let r=Syn.reflection second in
    let c=get "whole reflection capability" (if kind="ite" then
      Ref.check_ite_using ps (env()) r else Ref.check_nat_dite_using ps (env()) r) in
    let id,args=contract second kind in
    exact (Printf.sprintf "defn%d %s whole checked" (if second then 2 else 1) kind)
      (node id (j()::args)) (Ref.theorem c);
    exact (Printf.sprintf "defn%d %s whole raw" (if second then 2 else 1) kind)
      (node id (raw()::args)) (Ref.raw_theorem c);
    certificates:=((second,kind),c)::!certificates
  let cap second kind=List.assoc (second,kind) !certificates
  let nat_base=ref None
  let capture_nat ()=
    let gs=Old.goals false in
    let ps=List.filter (fun h -> List.exists (fun g -> aconv g (concl h)) gs) !Old.prepared in
    let c=get "whole NatLE in final environment" (Ref.check_nat_condition_using ps (env())
      (Syn.nat_condition false) ~dec_type:(Old.dec_type false) ~gadget_type:(Old.gadget_type false)) in
    exact "NatLE whole checked" (Old.target false) (Ref.theorem c);
    exact "NatLE whole raw" (node "l4_reflected_nat_contract" (raw()::Old.args false)) (Ref.raw_theorem c);
    nat_base:=Some c
  let base ()=match !nat_base with Some c->Ref.theorem c|None->failwith "no NatLE base"
  let flags=[false,false;true,false;false,true;true,true]
  let assert_bundle label hs rs c=
    let actual=Cond.theorems c and raws=Cond.raw_theorems c in
    test (label^" exact checked length") (List.length actual=List.length hs);
    test (label^" exact raw length") (List.length raws=List.length rs);
    List.iter2 (fun want got->exact (label^" checked contract") (concl want) got) hs actual;
    List.iter2 (fun want got->exact (label^" raw contract") (concl want) got) rs raws
  let nat_dispatch ()=
    let b=match !nat_base with Some c->c|None->failwith "missing NatLE" in
    let i=cap false "ite" and d=cap false "dite" in
    List.iter (fun (ite,dite)->
      let c=get "prepared NatLE dispatcher" (Cond.check_prepared ~ite ~dite
        ~ite_proof:(Ref.theorem i) ~dite_proof:(Ref.theorem d)
        (env()) (Cond.Reflected_nat(Syn.nat_condition false)) (Ref.theorem b)) in
      let cs=[b]@(if ite then [i] else [])@(if dite then [d] else []) in
      assert_bundle (Printf.sprintf "NatLE flags %b %b" ite dite)
        (List.map Ref.theorem cs) (List.map Ref.raw_theorem cs) c) flags
  let bool_base=ref None and bool_ite=ref None
  let bool_condition ()=let p,d=Syn.bool_condition() in Cond.Boolean(p,d)
  let bool_default ite dite=
    let result=Cond.check ~fuel:200000 ~ite ~dite (env()) (bool_condition()) in
    if dite then (match result with Error{kind=Unsupported;_}->test "default Bool DITE unsupported" true
      | _->failwith "default Bool DITE expected Unsupported")
    else let c=get "default Boolean dispatch" result in
      test "default Boolean checked/raw bundle length"
        (List.length(Cond.theorems c)=(if ite then 2 else 1) &&
         List.length(Cond.raw_theorems c)=(if ite then 2 else 1));
      List.iter (fun h->test "default Boolean closed proof" (hyp h=[] && frees(concl h)=[]))
        (Cond.theorems c @ Cond.raw_theorems c);
      if ite then bool_ite:=Some c else bool_base:=Some c
  let bool_prepared ()=
    let b=match !bool_base with Some c->c|None->failwith "missing bool base" in
    let i=match !bool_ite with Some c->c|None->failwith "missing bool ite" in
    List.iter (fun (ite,dite)->
      let result=Cond.check_prepared ~ite ~dite ~ite_proof:(List.nth(Cond.theorems i) 1)
        (env()) (bool_condition()) (List.hd(Cond.theorems b)) in
      if dite then (match result with Error{kind=Unsupported;_}->test "prepared Bool DITE unsupported" true
        | _->failwith "prepared Bool DITE expected Unsupported")
      else let c=get "prepared Boolean dispatch" result in
        let wanted=if ite then i else b in
        assert_bundle (Printf.sprintf "Bool flags %b %b" ite dite)
          (Cond.theorems wanted) (Cond.raw_theorems wanted) c) flags
  let reject label=function
    | Ok _->failwith(label^": accepted")
    | Error{kind=Resource;message}->failwith(label^": resource-only failure: "^message)
    | Error e->Printf.printf "UNIFIED_NEGATIVE %s %s\n%!" label e.message;test label true
  let bad_branch kind positive=
    let i=(if kind="ite" then 2 else 5)+(if positive then 0 else 1) in
    let l,r,t=decode_goal(List.nth(goals true kind) i) in
    let rec poison=function Lam(n,a,b)->Lam(n,a,poison b) | _->
      if kind="ite" then Bvar(if positive then 0 else 1) else Fix.c ["Nat";"zero"] [] in
    let bad=poison r in
    ignore(get "poisoned branch genuinely typed" (Env.check ~fuel:200000 (env()) [] bad t));
    test "typed poisoned branch" true;
    let g,l,bad,t=peel l bad t in
    reject "wrong symbolic branch equation" (Env.convert ~fuel:200000 (env()) g l bad t)
  let controls ()=
    let c=Syn.nat_condition false in
    let i=Ref.theorem(cap false "ite") and d=Ref.theorem(cap false "dite") in
    let check ?(ite=false) ?(dite=false) ?ite_proof ?dite_proof e c b=
      Cond.check_prepared ~ite ~dite ?ite_proof ?dite_proof e (Cond.Reflected_nat c) b in
    reject "missing requested ITE" (check ~ite:true (env()) c (base()));
    reject "missing requested DITE" (check ~dite:true (env()) c (base()));
    reject "hypothesis-bearing base" (check (env()) c (ASSUME(concl(base()))));
    reject "unrelated base theorem" (check (env()) c TRUTH);
    ignore(get "changed source independently typed" (Env.infer (env()) [] Fix.nt));
    test "changed source genuinely typed" true;
    reject "typed changed condition source" (check (env()) {c with Syn.dec=Fix.nt} (base()));
    reject "wrong reflection optional proof even with flag false"
      (check ~ite_proof:(Ref.theorem(cap true "ite")) (env()) c (base()));
    reject "wrong kind optional proof" (check ~ite_proof:d (env()) c (base()));
    reject "hypothesis-bearing optional proof" (check ~dite_proof:(ASSUME(concl d)) (env()) c (base()));
    let later=Fix.def (env()) ["Unified";"later"] [] Fix.nt (Fix.c ["Nat";"zero"] []) in
    reject "stale base environment" (check later c (base()));
    let other=get "different policy" (Env.with_axioms
      [{Env.axiom_name=Fix.name ["Unused"];axiom_params=[];axiom_type=Sort Zero}]) in
    reject "changed policy environment" (check ~ite:true ~dite:true ~ite_proof:i ~dite_proof:d other c (base()));
    let id,args=contract false "dite" in
    test "same source/environment different policy target does not match"
      (not(aconv (concl d) (node id (node "l4_checked"
        [Env.quote_policy other;Env.quote_env(env())]::args))));
    test "prepared zero fuel is Resource" (match Cond.check_prepared ~fuel:0 (env())
      (Cond.Reflected_nat c) (base()) with Error{kind=Resource;_}->true|_->false);
    let r=Syn.reflection true in
    ignore(get "false helper independently typed" (Env.infer (env()) [] r.Syn.of_false));
    reject "typed swapped true helper" (Ref.check_nat_dite (env()) {r with Syn.of_true=r.Syn.of_false});
    ignore(get "true helper independently typed" (Env.infer (env()) [] r.Syn.of_true));
    reject "typed swapped false helper" (Ref.check_nat_dite (env()) {r with Syn.of_false=r.Syn.of_true})
  let invariants ()=
    test "all capabilities use one final empty policy" (Env.permissions(env())=[]);
    test "unchanged HOL axioms" (axioms()=nat_initial_axioms);
    test "exactly 29 native rules" (List.length(CONJUNCTS l4_edef_RULES)=29);
    test "exactly 11 admission rules"
      (List.length(CONJUNCTS(SPEC (Env.quote_policy(env())) l4_evalid_RULES))=11)
  let run phase=
    let before= !count in Printf.printf "\nUNIFIED_WORK_START %s\n%!" phase;
    try
      (match String.split_on_char '-' phase with
       | ["seal";"env"]->seal()
       | ["nat";"capture"]->capture_nat()
       | ["nat";"dispatch"]->nat_dispatch()
       | ["bool";"default";a;b]->bool_default (a="1") (b="1")
       | ["bool";"prepared"]->bool_prepared()
       | ["controls"]->controls()
       | ["invariants"]->invariants()
       | ["bad";kind;b]->bad_branch kind (b="true")
       | [which;kind;"type";n]->prepare_type (which="d2") kind (int_of_string n)
       | [which;kind;b;"body"]->branch_body (which="d2") kind (b="true")
       | [_;_;_;"close"]->close_branch()
       | [which;kind;"whole"]->certify (which="d2") kind
       | _->failwith("unknown phase "^phase));
      Printf.printf "UNIFIED_WORK_PASS %s %d\n%!" phase (!count-before)
    with exn->Printf.printf "UNIFIED_WORK_FAIL %s %s\n%!" phase (Printexc.to_string exn);raise exn
end;;
Printf.printf "\nUNIFIED_SETUP_READY\n%!";;
