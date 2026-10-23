module Hadd_test = struct
  module H=Lean4hol
  module A=Lean4hol_env
  module W=Hol_input
  module R=Lean4hol_raw_ctor
  module C=Lean4hol_input_certificate
  let get = function Ok x->x | Error e->failwith e.H.message
  let decline label = function
    | Error e when e.H.kind<>H.Resource ->
      Printf.printf "\nPRIVATE_DECLINE %s %s\n%!" label e.H.message
    | Error _ -> failwith (label ^ ": resource is not negative evidence")
    | Ok _ -> failwith (label ^ ": unexpectedly accepted")
  let declarations () = W.read_file "fixtures/hadd-132.ndjson"
  let raw_definition h v = {A.kind=A.Definition;name=Hol_check.name h.W.name;
    params=List.map Hol_check.name h.W.params;typ=Hol_check.expr h.W.typ;
    value=Some(Hol_check.expr v)}
  let setup () =
    let env=ref(get(A.with_axioms [])) in
    let blocks=ref [] and trace=ref(C.start !env) in
    let ds=declarations() in
    List.iter(fun(_,d)->
      let raw,next=match d with
      | W.Inductive cs -> List.map Hol_check.claim cs,fst(get(Hol_check.admit_generated !env cs))
      | W.Definition(h,v) -> let r=raw_definition h v in [r],fst(get(A.admit !env r))
      | _->failwith "unexpected prefix declaration" in
      trace:=get(C.append_exact !env next !blocks raw !trace);
      blocks:=raw::!blocks; env:=next) (List.filter(fun(n,_)->n<132)ds);
    let cs=match List.assoc 132 ds with W.Inductive cs->cs|_->failwith "missing HAdd" in
    !env,!blocks,!trace,cs,List.map Hol_check.claim cs
  let canonical prior cs =
    let b=Hol_check.inductive_family cs in
    let claims=get(H.run 100000 [] [] (fun st->A.generate_family st b ~large:true ~k:false)) in
    let b={b with A.family_claims=claims} in
    b,fst(get(A.admit_inductive_family prior b))
  let closed th = if hyp th<>[] || frees(concl th)<>[] then failwith "open typed control"
  let typed label ds e =
    let _,h=get(A.fragment_sort ds [] e) in closed h;
    Printf.printf "PRIVATE_TYPED %s closed_formation\n%!" label
  let lift e n = get(H.run 100000 [] [] (fun st->H.lift st n 0 e))
  let nth_domain n f e =
    let rec go n = function
      | H.Pi(x,a,b) when n=0 -> H.Pi(x,f a,b)
      | H.Pi(x,a,b) -> H.Pi(x,a,go(n-1)b)
      | _ -> failwith "missing constructor binder" in go n e
  let result f e =
    let rec go = function H.Pi(n,a,b)->H.Pi(n,a,go b) | e->f e in go e
  let map_ctor f raw = List.map(fun d->match d.A.kind with
    | A.Generated(A.Constructor_role _)->f d | _->d)raw
  let ctor raw = List.find(fun d->match d.A.kind with
    | A.Generated(A.Constructor_role _)->true | _->false)raw
  let typed_ctors label prior raw =
    let ds=List.hd raw::A.declarations prior in
    List.iter(fun d->typed label ds d.A.typ)
      (List.filter(fun d->match d.A.kind with A.Generated(A.Constructor_role _)->true|_->false)raw)
  let raw_reject label prior next raw b = decline label (R.certify prior next raw b)
  let native () =
    if private_native_rule_count<>29 || private_admission_rule_count<>11 || axioms()<>private_axioms then
      failwith "native rules or axioms changed"
end;;
