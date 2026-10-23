needs "tests/hol_reflection/nat_condition_tests.ml";;
needs "hol/nat_instantiation.ml";;

module Lean4hol_nat_composition_tests = struct
  open Lean4hol
  module Old=Lean4hol_nat_tests
  module Comp=Lean4hol_nat_instantiation
  module Env=Lean4hol_env
  module Fix=Lean4hol_reflection_fixture
  module Syn=Lean4hol_reflection_syntax
  let current=ref None and wrapper=ref None and delta=ref None
  let value r=match !r with Some x -> x | None -> failwith "missing completed preparation"
  let env ()= !(Old.env)
  let g=[Fix.nt;Fix.nt]
  let c second=Syn.nat_condition second
  let whole_body second = match Old.gadget(c second) with
    | Lam(_,a,Lam(_,b,e)) when a=Fix.nt && b=Fix.nt -> e
    | _ -> failwith "canonical Nat gadget telescope changed"
  let rec spine acc=function App(f,a)->spine (a::acc) f | f->f,acc
  let setup second =
    let j=Comp.seed (env()) second in
    Old.test "generic equation in exact target environment with Nat context"
      (List.length j.Comp.g=6);
    current:=Some j;wrapper:=None;delta:=None
  let close ()=current:=Some(Comp.close(value current))
  let arg second index =
    let j=value current in Comp.same (env()) j;
    current:=Some(Comp.apply_symbolic j (List.nth(Comp.arguments second) index));
    Old.test "completed audited typed symbolic argument" true
  let init_wrapper second =
    let head,args=spine [] (whole_body second) in
    Old.test "exact three-argument gadget wrapper" (List.length args=3);
    wrapper:=Some(Comp.infer (env()) g head)
  let wrapper_arg second index =
    let _,args=spine [] (whole_body second) in
    let source=List.nth args index in
    let h=if index=0 then
        let desired=List.hd(Comp.arguments second) in
        if source=desired then Comp.infer (env()) g source
        else Comp.convert (env()) g source desired (Sort Zero)
      else Comp.infer (env()) g source in
    let w=value wrapper in Comp.same (env()) w;
    wrapper:=Some(Comp.apply_wrapper w h);
    Old.test "completed typed wrapper beta step" true
  let link_proof () =
    let w=value wrapper and j=value current in Comp.same (env()) w;Comp.same (env()) j;
    match w.Comp.right,j.Comp.left with
    | App(f,p),App(f',q) when f=f' ->
      let hf,_,dom,_=Comp.pi(Comp.infer (env()) g f) in
      let hp=Comp.proof_irrelevance (env()) g dom p q in
      wrapper:=Some(Comp.trans w (Comp.app hf hp));
      Old.test "proof irrelevance backed by both actual typed proofs" true
    | _ -> failwith "instantiated and wrapped decision heads differ"
  let prepare_delta second =
    let d=(c second).Syn.dec in
    let _,_,h=Old.get "actual declaration delta" (Env.normalize ~fuel:200000 (env()) [] d) in
    let h=Comp.unpack (env()) h in
    (match h.Comp.right with Lam(_,_,Lam(_,_,_))->()|_->failwith "decision delta not a two-lambda body");
    delta:=Some h
  let finish second =
    let j=Comp.trans (value wrapper) (value current) in
    let j=Comp.close(Comp.close j) in
    let d=value delta in
    Old.test "direct decision body matches actual admitted delta body" (j.Comp.right=d.Comp.right);
    let j=Comp.trans j (Comp.sym d) in
    let j=Comp.cast j (Old.gadget_type second) in
    let goal=List.nth(Old.goals second) 3 in
    Old.exact "whole Nat conversion composed from closed proofs" goal j.Comp.h;
    Old.prepared:=j.Comp.h::!(Old.prepared)
  let negative label f =
    try ignore(f());failwith(label^": unexpectedly succeeded") with
    | Stop {kind=Resource;message} -> failwith(label^": resource-only: "^message)
    | Stop _ -> Old.test label true
    | Failure s when not(String.ends_with ~suffix:"unexpectedly succeeded" s) -> Old.test label true
  let negatives second =
    let p=List.hd(Comp.arguments second) in
    let ha=Comp.infer (env()) g (Sort Zero) in
    let hb=Comp.check (env()) (Sort Zero::g) (Bvar 0) (Sort Zero) in
    let hv=Comp.check (env()) g p (Sort Zero) in
    let good=Comp.instantiated_typing ha hb hv in
    Old.test "native instantiation control has exact substituted source" (good.Comp.left=p && good.Comp.right=p);
    let wrong=Comp.infer (env()) g Fix.tru in
    negative "wrong typed instantiation argument" (fun () -> Comp.instantiated_typing ha hb wrong);
    negative "wrong instantiation context" (fun () -> Comp.instantiated_typing ha {hb with Comp.g=g} hv);
    negative "wrong instantiation body source" (fun () -> Comp.instantiated_typing ha {hb with Comp.left=Fix.tru} hv);
    negative "hypothesis-bearing instantiation input" (fun () ->
      Comp.instantiated_typing ha {hb with Comp.h=ASSUME(concl hb.Comp.h)} hv);
    let later=Fix.def (env()) ["NatInstantiation";"later"] [] Fix.nt (Fix.c ["Nat";"zero"] []) in
    negative "stale symbolic proof environment" (fun () -> Comp.unpack later (value current).Comp.h);
    negative "stale typed instantiation environment" (fun () -> Comp.instantiated_typing {ha with Comp.env=later} hb hv);
    Old.check_invariants()
  let run phase =
    let before= !(Old.count) in
    Printf.printf "\nNAT_WORK_START %s\n%!" phase;
    try
      let second=String.starts_with ~prefix:"eq-" phase in
      let suffix=String.sub phase 3 (String.length phase-3) in
      (match suffix with
       | "seed"->setup second | "close-1" | "close-2" | "close-3" | "close-4"->close()
       | "arg-1"->arg second 0 | "arg-2"->arg second 1
       | "arg-3"->arg second 2 | "arg-4"->arg second 3
       | "wrapper-init"->init_wrapper second
       | "wrapper-1"->wrapper_arg second 0 | "wrapper-2"->wrapper_arg second 1
       | "wrapper-3"->wrapper_arg second 2 | "proof-link"->link_proof()
       | "delta"->prepare_delta second | "finish"->finish second
       | "inst-negatives"->negatives second
       | _ -> failwith "unknown composed Nat stage");
      Printf.printf "\nNAT_WORK_PASS %s %d\n%!" phase (!(Old.count)-before)
    with e -> Printf.printf "\nNAT_WORK_FAIL %s %s\n%!" phase (Printexc.to_string e)
end;;
Lean4hol_nat_tests.check_invariants();;
List.iter (fun h -> if hyp h<>[] || frees(concl h)<>[] then failwith "open instantiation theorem")
  [l4_defeq_instantiation;l4_edef_instantiation;l4_checked_instantiation];;
Printf.printf "\nNAT_INSTANTIATION_SETUP_READY\n%!";;
