(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Private syntax candidates only. No admission or verdict is returned here. *)
module Reducible_candidate = struct
  module H = Lean4hol
  module A = Lean4hol_env
  let head st env e =
    let rec norm e =
      H.tick st;
      match e with
      | H.Const(n,us) ->
        (match List.find_opt(fun d->d.A.name=n) (A.declarations env) with
        | Some {A.kind=(A.Definition | A.Theorem);params;value=Some v;_}
          when List.length params=List.length us ->
            norm(H.instantiate_levels st params us v)
        | _ -> e)
      | H.App(f,a) ->
        let f=norm f in
        (match f with H.Lam(_,_,b)->norm(H.subst st 0 a b) | _ -> H.App(f,a))
      | H.Let(_,_,v,b) -> norm(H.subst st 0 v b)
      | _ -> e in norm e
  let family ?(fuel=100000) env raw = H.run fuel [] [] (fun st ->
    let norm=head st env in
    let unsupported s=H.stop H.Unsupported s in
    let inds=List.filter(fun d->match d.A.kind with
      | A.Generated(A.Inductive_role _)->true | _->false)raw in
    let header,info=match inds with
      | [({A.kind=A.Generated(A.Inductive_role info);_} as d)]
        when info.A.num_indices=0 && info.A.num_nested=0 && not info.A.is_unsafe -> d,info
      | _ -> unsupported "candidate needs one safe nonindexed nonnested family" in
    let rec telescope n = function
      | e when n=0 -> [],e
      | H.Pi(b,a,t) -> let rest,r=telescope(n-1)t in (b,a)::rest,r
      | _ -> unsupported "constructor telescope itself must be manifest Pi" in
    let pars,result=telescope info.A.num_params header.A.typ in
    let u=match result with H.Sort u->u | _->unsupported "manifest result sort required" in
    let i=header.A.name and ps=header.A.params in
    let rec contains = function
      | H.Const(n,_) -> n=i
      | H.Pi(_,a,b) | H.Lam(_,a,b) | H.App(a,b) -> contains a || contains b
      | H.Let(_,a,v,b) -> contains a || contains v || contains b
      | H.Proj(n,_,e) -> n=i || contains e
      | _ -> false in
    let rec lower count depth = function
      | H.Bvar j when j<depth -> H.Bvar j
      | H.Bvar j when j<depth+count -> unsupported "dependent field candidate outside family slice"
      | H.Bvar j -> H.Bvar(j-count)
      | H.App(f,a) -> H.App(lower count depth f,lower count depth a)
      | H.Lam(n,a,b) -> H.Lam(n,lower count depth a,lower count(depth+1)b)
      | H.Pi(n,a,b) -> H.Pi(n,lower count depth a,lower count(depth+1)b)
      | H.Let(n,a,v,b) -> H.Let(n,lower count depth a,lower count depth v,lower count(depth+1)b)
      | H.Proj(n,j,e) -> H.Proj(n,j,lower count depth e)
      | e -> e in
    let rec fields offset = function
      | H.Pi(_,a,b) ->
        (* Do not normalize application arguments: uniform parameters are
           syntactically compared after head reduction by pinned Lean4Lean. *)
        let a=norm a in
        let f=if a=A.family_app i ps info.A.num_params offset then A.Recursive
          else if contains a then unsupported "function-valued or non-direct recursion outside bridge candidate slice"
          else A.Data(lower offset 0 a) in
        f::fields(offset+1)b
      | e when e=A.family_app i ps info.A.num_params offset -> []
      | _ -> unsupported "constructor result must retain exact uniform parameters" in
    let cs=List.map(fun n ->
      match List.find_opt(fun d->d.A.name=n)raw with
      | Some {A.kind=A.Generated(A.Constructor_role _);typ;_} ->
        let _,body=telescope info.A.num_params typ in n,fields 0 body
      | _ -> unsupported "missing constructor")info.A.ctors in
    let b={A.family_name=i;level_params=ps;parameters=pars;result_level=u;
      family_constructors=cs;family_claims=[]} in
    (* Beyond the original Type0 slice, only nonrecursive data families with
       a manifest nonzero result are proposed. HOL proves the actual bound. *)
    let rec positive = function
      | H.Succ _ -> true
      | H.Max(a,b) -> positive a || positive b
      | _ -> false in
    let data_only=List.for_all(fun(_,fs)->
      List.for_all(function A.Data _->true | A.Recursive->false)fs)cs in
    if u<>H.Succ H.Zero && not(data_only && positive u) then
      unsupported "raw candidate requires Type zero or nonrecursive nonzero data";
    let canonical=A.generate_family st b ~large:true ~k:false in
    {b with A.family_claims=canonical})
  let indexed ?(fuel=100000) env raw = H.run fuel [] [] (fun st ->
    let norm=head st env in
    let unsupported message=H.stop H.Unsupported message in
    let inds=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)raw in
    let header,info=match inds with
      | [({A.kind=A.Generated(A.Inductive_role info);_} as d)]
        when info.A.num_indices=0 && info.A.num_nested=0 && not info.A.is_unsafe -> d,info
      | _ -> unsupported "raw function candidate requires one safe family without indices" in
    let rec telescope n e=if n=0 then [],e else match e with
      | H.Pi(b,a,t)->let rest,r=telescope(n-1)t in (b,a)::rest,r
      | _ -> unsupported "raw function parameters must be manifest" in
    let parameters,result=telescope info.A.num_params header.A.typ in
    let u=match result with H.Sort u when u=H.Succ H.Zero->u
      | _ -> unsupported "raw function candidate requires Type zero" in
    let i=header.A.name and ps=header.A.params in
    let rec contains = function
      | H.Const(n,_)->n=i
      | H.App(a,b) | H.Pi(_,a,b) | H.Lam(_,a,b)->contains a || contains b
      | H.Let(_,a,v,b)->contains a || contains v || contains b
      | H.Proj(n,_,e)->n=i || contains e
      | _ -> false in
    let family j=A.family_app i ps info.A.num_params j in
    let rec recursive j domains e =
      let h=norm e in
      if h=family j then Some(List.rev domains) else match h with
      | H.Pi(_,a,b) ->
        if contains a then unsupported "raw function domain contains family before domain reduction";
        recursive(j+1)(a::domains)b
      | _ when contains h -> unsupported "raw function result is not an exact uniform application"
      | _ -> None in
    let rec fields j = function
      | H.Pi(_,a,b) ->
        let f=match recursive j [] a with
          | Some [] -> A.Index_recursive []
          | Some domains -> A.Index_function(domains,[])
          | None ->
            let h=norm a in
            if contains h then unsupported "raw function data field contains family";
            A.Index_data h in
        f::fields(j+1)b
      | e when e=family j -> []
      | _ -> unsupported "raw function constructor result must retain exact parameters" in
    let constructors=List.map(fun n->match List.find_opt(fun d->d.A.name=n)raw with
      | Some {A.kind=A.Generated(A.Constructor_role _);typ;_} ->
        let _,body=telescope info.A.num_params typ in
        {A.indexed_ctor_name=n;indexed_fields=fields 0 body;result_indices=[]}
      | _ -> unsupported "missing raw function constructor")info.A.ctors in
    if not(List.exists(fun c->List.exists(function A.Index_function(_::_,[])->true|_->false)
      c.A.indexed_fields)constructors) then unsupported "raw indexed candidate requires a recursive function field";
    let b={A.indexed_name=i;indexed_level_params=ps;indexed_parameters=parameters;indices=[];
      indexed_result_level=u;indexed_constructors=constructors;indexed_claims=[]} in
    {b with A.indexed_claims=A.generate_indexed st b ~large:true ~k:false})
end
