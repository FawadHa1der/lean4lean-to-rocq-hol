let nat_initial_axioms=axioms();;
needs "hol/reflected_condition.ml";;
needs "tests/hol_reflection/reflection_nat_fixtures.ml";;

module Lean4hol_nat_tests = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Fix=Lean4hol_reflection_fixture
  module Nfix=Lean4hol_reflection_nat_fixture
  module Syn=Lean4hol_reflection_syntax
  module Ref=Lean4hol_reflection
  let count=ref 0
  let test label b=if not b then failwith label else
    (incr count;Printf.printf "NAT_CHECK %d %s\n%!" !count label)
  let exact label tm h=test label (hyp h=[] && frees(concl h)=[] && aconv tm (concl h))
  let get=Fix.get
  let env=ref(Lean4hol_reflection_boolean_fixture.add(Fix.base()))
  let check_invariants () =
    test "empty policy" (Env.permissions !env=[]);
    test "axioms unchanged" (axioms()=nat_initial_axioms);
    test "29 native rules" (List.length(CONJUNCTS l4_edef_RULES)=29);
    test "11 admission rules" (List.length(CONJUNCTS(SPEC (Env.quote_policy !env) l4_evalid_RULES))=11)
  let prepared=ref []
  let dec_types=ref [] and gadget_types=ref []
  let condition second=Syn.nat_condition second
  let typ second =
    let c=condition second in let open Fix.Quote in
    run(pi nn (fun n -> pi nn (fun m -> dec(apps (embed c.Syn.prop) [n;m]))))
  let dec_type second=List.assoc second !dec_types
  let gadget_type second=List.assoc second !gadget_types
  let gadget c=Syn.template "l4_reflected_nat_gadget" (List.map quote_expr
    [c.Syn.reflect.Syn.typ;c.Syn.reflect.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;c.Syn.proof])
  let infer_type second is_dec =
    let c=condition second in
    let e=if is_dec then c.Syn.dec else gadget c in
    let ty,h=get "genuine original type inference" (Env.infer ~fuel:200000 !env [] e) in
    exact "inferred type certificate" (node "l4_checked" [Env.quote_policy !env;Env.quote_env !env;
      quote_context [];quote_expr e;quote_expr e;quote_expr ty]) h;
    let types=if is_dec then dec_types else gadget_types in
    types:=(second,ty)::List.remove_assoc second !types;
    prepared:=h::!prepared
  let args second =
    let c=condition second in
    List.map quote_expr [c.Syn.reflect.Syn.typ;c.Syn.reflect.Syn.to_dec;c.Syn.prop;
      c.Syn.as_bool;c.Syn.proof;c.Syn.dec;dec_type second;gadget_type second]
  let target second = node "l4_reflected_nat_contract"
    (node "l4_checked" [Env.quote_policy !env;Env.quote_env !env]::args second)
  let goals second =
    let j=node "l4_checked" [Env.quote_policy !env;Env.quote_env !env] in
    let v=genvar(type_of j) in
    conjuncts(rhs(concl(INST [j,v] (Syn.calc(node "l4_reflected_nat_contract" (v::args second))))))
  let prepare second i =
    let tm=List.nth (goals second) i in
    let h=match List.find_opt (fun h -> aconv tm (concl h)) !prepared with
    | Some h -> Printf.printf "NAT_PREP_REUSE %b %d\n%!" second i;h
    | None ->
      let head,xs=strip_comb tm in
      match fst(dest_const head),xs with
      | "l4_checked",[p;e;g;x;y;t] when aconv p (Env.quote_policy !env) &&
          aconv e (Env.quote_env !env) && aconv g (quote_context []) ->
        let x=Syn.decode x and y=Syn.decode y and t=Syn.decode t in
        Printf.printf "NAT_PREP_NATIVE %b %d\n%!" second i;
        get "native Nat condition obligation" (if x=y then Env.check ~fuel:200000 !env [] x t
          else Env.convert ~fuel:200000 !env [] x y t)
      | _ -> failwith "unexpected Nat obligation" in
    exact "prepared exact closed judgment" tm h;prepared:=h::!prepared
  let positive second =
    let gs=goals second in
    let proofs=List.filter (fun h -> List.exists (fun g -> aconv g (concl h)) gs) !prepared in
    test "all four genuine obligations prepared" (List.for_all (fun g ->
      List.exists (fun h -> aconv g (concl h)) proofs) gs);
    let c=get "whole canonical reflected Nat contract"
      (Ref.check_nat_condition_using proofs !env (condition second)
        ~dec_type:(dec_type second) ~gadget_type:(gadget_type second)) in
    exact "whole checked contract" (target second) (Ref.theorem c);
    exact "whole raw contract" (node "l4_reflected_nat_contract"
      (node "l4_edef" [Env.quote_env !env]::args second)) (Ref.raw_theorem c);
    check_invariants()
  let decline label = function
    | Error {kind=Resource;message} -> failwith(label^": resource-only failure: "^message)
    | Error e -> Printf.printf "NAT_NEGATIVE %s %s\n%!" label e.message;test label true
    | Ok _ -> failwith(label^": unexpectedly certified")
  let typed_negatives second =
    let c=condition second in
    let open Fix.Quote in
    let wrong=run(lam nn (fun _ -> lam nn (fun _ -> con ["Nat";"zero"] []))) in
    let wrong_bool=run(lam nn (fun _ -> lam nn (fun _ -> tt))) in
    let _,h=get "poison is independently typed" (Env.infer !env [] wrong) in
    test "typed poison closed" (hyp h=[] && frees(concl h)=[]);
    let _,h=get "same-signature Bool poison typed" (Env.infer !env [] wrong_bool) in
    test "same-signature Bool poison closed" (hyp h=[] && frees(concl h)=[]);
    let check c=Ref.check_nat_condition_using [] !env c
      ~dec_type:(dec_type second) ~gadget_type:(gadget_type second) in
    decline "typed wrong decision" (check {c with Syn.dec=wrong});
    (* Reuse only the unchanged decision and reflection-type obligations;
       the poisoned gadget still has to pass the real checker. *)
    let common=List.filter (fun h -> List.exists (fun g -> aconv g (concl h))
      [List.nth (goals second) 0;List.nth (goals second) 1]) !prepared in
    decline "typed wrong reflection proof" (Ref.check_nat_condition_using common !env
      {c with Syn.proof=wrong} ~dec_type:(dec_type second) ~gadget_type:(gadget_type second));
    decline "typed wrong asBool" (Ref.check_nat_condition_using common !env
      {c with Syn.as_bool=wrong} ~dec_type:(dec_type second) ~gadget_type:(gadget_type second));
    decline "same-signature wrong asBool" (Ref.check_nat_condition_using common !env
      {c with Syn.as_bool=wrong_bool} ~dec_type:(dec_type second) ~gadget_type:(gadget_type second));
    decline "wrong universe candidate" (Ref.check_nat_condition_using [] !env c
      ~dec_type:(Sort(Succ Zero)) ~gadget_type:(gadget_type second));
    decline "unbound proof expression" (Ref.check_nat_condition_using [] !env
      {c with Syn.proof=Bvar 0} ~dec_type:(dec_type second) ~gadget_type:(gadget_type second));
    decline "genuine missing dependency" (Ref.check_nat_condition_using [] Env.empty c
      ~dec_type:(dec_type second) ~gadget_type:(gadget_type second));
    check_invariants()
  let proof_negatives second =
    let c=condition second in
    let gs=goals second in
    let ps=List.filter (fun h -> List.exists (fun g -> aconv g (concl h)) gs) !prepared in
    let check proofs env c=Ref.check_nat_condition_using proofs env c
      ~dec_type:(dec_type second) ~gadget_type:(gadget_type second) in
    decline "hypothesis is not a certificate" (check [ASSUME(List.hd gs)] !env c);
    decline "unrelated closed theorem" (check [TRUTH] !env c);
    decline "wrong source proof" (check ps !env {c with Syn.dec=Fix.nt});
    let later=Fix.def !env ["NatFixture";"later"] [] Fix.nt (Fix.c ["Nat";"zero"] []) in
    decline "stale environment proof" (check ps later c);
    test "zero fuel is Resource" (match Ref.check_nat_condition_using ~fuel:0 ps !env c
      ~dec_type:(dec_type second) ~gadget_type:(gadget_type second) with
      Error {kind=Resource;_}->true|_->false);
    check_invariants()
  let probes () =
    let open Fix.Quote in
    let f=arrow nn bb in
    let items=["declared-type",Nfix.nat2ty bb;
      "recursor",Fix.c ["Nat";"rec"] [Fix.one];
      "constant-bool-rec",run(lam nn (fun n -> Nfix.natrec Fix.one (lam nn (fun _ -> bb)) tt
        (lam nn (fun _ -> lam bb (fun _ -> ff))) n));
      "function-rec",run(lam nn (fun n -> Nfix.natrec Fix.one (lam nn (fun _ -> f))
        (lam nn (fun _ -> tt)) (lam nn (fun _ -> lam f (fun ih -> ih))) n));
      "beq-body",run(Nfix.beq_body())] in
    List.iter (fun (label,e) ->
      Printf.printf "NAT_PROBE_START %s\n%!" label;
      match Env.infer !env [] e with
      | Ok(ty,h) -> Printf.printf "NAT_PROBE_OK %s\n%!" label;print_term(quote_expr ty);print_newline()
      | Error err -> Printf.printf "NAT_PROBE_ERROR %s %s\n%!" label err.message) items
  (* A smaller, fully typed symbolic equation. It is deliberately NOT a Nat
     condition certificate: the arithmetic instantiations are still absent. *)
  let symbolic second =
    let r=Syn.reflection second in
    let open Fix.Quote in
    let forward p b=arrow (eq bb b tt) p in
    let backward p b=arrow (if second then eq bb b ff else nott(eq bb b tt)) (nott p) in
    let bind k=lam pp (fun p -> lam bb (fun b ->
      lam (forward p b) (fun yes -> lam (backward p b) (fun no -> k p b yes no)))) in
    let lhs=run(bind (fun p b yes no ->
      let h=lam pp (fun q -> lam (arrow (forward p b) (arrow (backward p b) q))
        (fun use -> apps use [yes;no])) in
      apps (embed r.Syn.to_dec) [p;b;h])) in
    let rhs=run(bind (fun p b yes no ->
      let pos h=apps (con ["Decidable";"isTrue"] []) [p;app yes h] in
      let neg h=apps (con ["Decidable";"isFalse"] []) [p;app no h] in
      if second then apps (con ["Bool";"casesOn"] [Fix.one])
        [lam bb (fun b' -> arrow (eq bb b b') (dec p));b;
         lam (eq bb b ff) neg;lam (eq bb b tt) pos;refl bb b]
      else apps (con ["dite"] [Fix.one])
        [dec p;eq bb b tt;apps (con ["Bool";"decEq"] []) [b;tt];
         lam (eq bb b tt) pos;lam (nott(eq bb b tt)) neg])) in
    let ty=run(pi pp (fun p -> pi bb (fun b ->
      pi (forward p b) (fun _ -> pi (backward p b) (fun _ -> dec p))))) in
    let rec open_expr g e=match e with Lam(_,a,b) -> open_expr (a::g) b | _ -> g,e in
    let rec open_type g e=match e with Pi(_,a,b) -> open_type (a::g) b | _ -> g,e in
    let g,lhs=open_expr [] lhs and g',rhs=open_expr [] rhs and gt,ty=open_type [] ty in
    test "symbolic exact four-binder context" (g=g' && g=gt && List.length g=4);
    let h=get "whole generic typed reflection decision equation"
      (Env.convert ~fuel:200000 !env g lhs rhs ty) in
    exact "symbolic equation checked" (node "l4_checked"
      [Env.quote_policy !env;Env.quote_env !env;quote_context g;quote_expr lhs;quote_expr rhs;quote_expr ty]) h;
    exact "symbolic equation raw" (node "l4_edef"
      [Env.quote_env !env;quote_context g;quote_expr lhs;quote_expr rhs;quote_expr ty])
      (MATCH_MP l4_checked_typing h);
    check_invariants()
  let run phase =
    let before= !count in Printf.printf "\nNAT_WORK_START %s\n%!" phase;
    try
      (if List.mem_assoc phase Nfix.stages then (env:=(List.assoc phase Nfix.stages) !env; check_invariants())
       else match phase with
       | "eq-0" -> prepare true 0 | "eq-1" -> prepare true 1
       | "eq-2" -> prepare true 2 | "eq-3" -> prepare true 3
       | "le-0" -> prepare false 0 | "le-1" -> prepare false 1
       | "le-2" -> prepare false 2 | "le-3" -> prepare false 3
       | "eq-positive" -> positive true | "le-positive" -> positive false
       | "eq-dec-infer" -> infer_type true true | "eq-gadget-infer" -> infer_type true false
       | "le-dec-infer" -> infer_type false true | "le-gadget-infer" -> infer_type false false
       | "eq-negatives" -> typed_negatives true | "le-negatives" -> typed_negatives false
       | "eq-proof-negatives" -> proof_negatives true | "le-proof-negatives" -> proof_negatives false
       | "probes" -> probes()
       | "symbolic-eq" -> symbolic true | "symbolic-le" -> symbolic false
       | _ -> failwith "unknown Nat phase");
      Printf.printf "\nNAT_WORK_PASS %s %d\n%!" phase (!count-before)
    with e -> Printf.printf "\nNAT_WORK_FAIL %s %s\n%!" phase (Printexc.to_string e)
end;;
Lean4hol_nat_tests.check_invariants();;
Printf.printf "\nNAT_SETUP_READY\n%!";;
