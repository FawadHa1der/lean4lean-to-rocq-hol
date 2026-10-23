(* Loaded by HOL Light after hol/environment.ml and bytecompiled Hol_input. *)
module Hol_check = struct
  module H = Lean4hol
  module A = Lean4hol_env
  module W = Hol_input
  let rec name = function
    | W.Anonymous -> H.Anonymous | W.Str(n,s) -> H.Str(name n,s)
    | W.Num(n,s) -> H.Num(name n,s)
  let rec level = function
    | W.Zero -> H.Zero | W.Succ u -> H.Succ(level u)
    | W.Max(u,v) -> H.Max(level u,level v)
    | W.Imax(u,v) -> H.Imax(level u,level v) | W.Param n -> H.Param(name n)
  let rec expr = function
    | W.Bvar i -> H.Bvar i | W.Sort u -> H.Sort(level u)
    | W.Const(n,us) -> H.Const(name n,List.map level us)
    | W.App(f,a) -> H.App(expr f,expr a)
    | W.Lam(n,a,b) -> H.Lam(name n,expr a,expr b)
    | W.Pi(n,a,b) -> H.Pi(name n,expr a,expr b)
    | W.Let(n,a,v,b) -> H.Let(name n,expr a,expr v,expr b)
    | W.Natlit n -> H.Natlit n
  exception Verdict of int * string
  let unsupported message = raise(Verdict(2,message))
  let rule (r:W.rec_rule) : A.rec_rule =
    {A.ctor=name r.W.ctor;num_fields=r.W.num_fields;rhs=expr r.W.rhs}
  let claim (c:W.claim) : A.declaration =
    let role=match c.W.role with
      | W.Inductive_role i -> A.Inductive_role{
          A.num_params=i.W.num_params;num_indices=i.W.num_indices;all=List.map name i.W.all;
          ctors=List.map name i.W.ctors;num_nested=i.W.num_nested;is_rec=i.W.is_rec;
          is_reflexive=i.W.is_reflexive;is_unsafe=i.W.is_unsafe}
      | W.Constructor_role i -> A.Constructor_role{
          A.induct=name i.W.induct;index=i.W.index;num_params=i.W.num_params;
          num_fields=i.W.num_fields;is_unsafe=i.W.is_unsafe}
      | W.Recursor_role i -> A.Recursor_role{
          A.all=List.map name i.W.all;num_params=i.W.num_params;num_indices=i.W.num_indices;
          num_motives=i.W.num_motives;num_minors=i.W.num_minors;rules=List.map rule i.W.rules;
          k=i.W.k;is_unsafe=i.W.is_unsafe} in
    {A.kind=A.Generated role;name=name c.W.header.W.name;params=List.map name c.W.header.W.params;
      typ=expr c.W.header.W.typ;value=None}
  let rec closed depth = function
    | H.Bvar i -> i<depth
    | H.Sort _ | H.Const _ | H.Natlit _ -> true
    | H.App(a,b) -> closed depth a && closed depth b
    | H.Lam(_,a,b) | H.Pi(_,a,b) -> closed depth a && closed (depth+1) b
    | H.Let(_,a,v,b) -> closed depth a && closed depth v && closed (depth+1) b
  let inductive_block claims =
    let claims=List.map claim claims in
    let inds=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)claims in
    match inds with
    | [{A.kind=A.Generated(A.Inductive_role info);name=i;params=[];typ=H.Sort u;value=None}]
        when info.A.num_params=0 && info.A.num_indices=0 && info.A.num_nested=0 && not info.A.is_unsafe ->
      let rec fields = function
        | H.Pi(_,a,b) ->
          let field=if a=H.Const(i,[]) then A.Recursive else
            if closed 0 a then A.Data a else unsupported "HOL dependent constructor fields are pending" in
          field::fields b
        | H.Const(j,[]) when i=j -> []
        | _ -> unsupported "HOL indexed or reducible constructor telescope is pending" in
      let constructors=List.map(fun n->
        match List.find_opt(fun d->d.A.name=n)claims with
        | Some {A.kind=A.Generated(A.Constructor_role _);typ;_} -> n,fields typ
        | _ -> unsupported "HOL constructor claim is absent or malformed")info.A.ctors in
      {A.inductive_name=i;inductive_level=u;constructors;claims}
    | _ -> unsupported "HOL polymorphic, indexed, mutual, nested or unsafe inductives are pending"
  let inductive_family claims =
    let claims=List.map claim claims in
    let inds=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)claims in
    match inds with
    | [{A.kind=A.Generated(A.Inductive_role info);name=i;params=ps;typ;value=None}]
        when info.A.num_indices=0 && info.A.num_nested=0 && not info.A.is_unsafe ->
      let rec telescope n e =
        if n=0 then [],e else match e with
        | H.Pi(b,a,t) -> let rest,r=telescope (n-1) t in (b,a)::rest,r
        | _ -> unsupported "HOL reducible parameter telescopes are pending" in
      let parameters,result=telescope info.A.num_params typ in
      let result_level=match result with H.Sort u->u
        | _ -> unsupported "HOL indexed or reducible family result is pending" in
      let levels=List.map(fun p->H.Param p)ps in
      let family_app offset=List.fold_left(fun f a->H.App(f,a)) (H.Const(i,levels))
        (List.init info.A.num_params(fun j->H.Bvar(offset+info.A.num_params-1-j))) in
      (* Field descriptions refer to parameters only. Retain each original
         constructor claim so HOL also checks the removed parameter prefix. *)
      let rec lower count depth = function
        | H.Bvar j when j<depth -> H.Bvar j
        | H.Bvar j when j<depth+count -> unsupported "HOL dependent constructor fields are pending"
        | H.Bvar j -> H.Bvar(j-count)
        | (H.Sort _ | H.Const _ | H.Natlit _) as e -> e
        | H.App(f,a) -> H.App(lower count depth f,lower count depth a)
        | H.Lam(n,a,b) -> H.Lam(n,lower count depth a,lower count (depth+1) b)
        | H.Pi(n,a,b) -> H.Pi(n,lower count depth a,lower count (depth+1) b)
        | H.Let(n,a,v,b) -> H.Let(n,lower count depth a,lower count depth v,lower count (depth+1) b) in
      let rec fields offset = function
        | H.Pi(_,a,b) ->
          let field=if a=family_app offset then A.Recursive else A.Data(lower offset 0 a) in
          field::fields (offset+1) b
        | result when result=family_app offset -> []
        | _ -> unsupported "HOL indexed or reducible constructor result is pending" in
      let constructors=List.map(fun n->
        match List.find_opt(fun d->d.A.name=n)claims with
        | Some {A.kind=A.Generated(A.Constructor_role _);typ;_} ->
          let _,body=telescope info.A.num_params typ in n,fields 0 body
        | _ -> unsupported "HOL constructor claim is absent or malformed")info.A.ctors in
      {A.family_name=i;level_params=ps;parameters;result_level;
        family_constructors=constructors;family_claims=claims}
    | _ -> unsupported "HOL indexed, mutual, nested or unsafe families are pending"
  let admit_generated env claims =
    let legacy=try Some(A.admit_inductive env (inductive_block claims))
      with Verdict(2,_) -> None in
    match legacy with
    | Some(Ok _ as result) -> result
    | Some(Error {H.kind=(H.Invalid_input | H.Resource);_} as result) -> result
    | _ -> A.admit_inductive_family env (inductive_family claims)
  let environment_judgment env = list_mk_comb (`l4_evalid`,[A.quote_policy env;A.quote_env env])
  let check_file path =
    let line=ref 0 and checked=ref 0 in
    let stop code message = raise(Verdict(code,message)) in
    let describe message = Printf.sprintf "line=%d checked=%d %s" !line !checked message in
    try
      let declarations=W.read_file path in
      let permissions=List.filter_map(fun(_,d)->match d with
        | W.Axiom h -> Some {A.axiom_name=name h.W.name;
            axiom_params=List.map name h.W.params;axiom_type=expr h.W.typ}
        | _ -> None) declarations in
      let env=ref(match A.with_axioms permissions with
        | Ok env -> env | Error e -> stop 2 e.H.message) in
      List.iter(fun(n,d)->
        line:=n;
        let result=match d with
          | W.Inductive claims -> admit_generated !env claims
          | W.Unsupported message -> stop 2 message
          | d ->
          let kind,h,v=match d with
          | W.Definition(h,v) -> A.Definition,h,Some(expr v)
          | W.Theorem(h,v) -> A.Theorem,h,Some(expr v)
          | W.Opaque(h,v) -> A.Opaque,h,Some(expr v)
          | W.Axiom h -> A.Axiom,h,None
          | W.Unsupported message -> stop 2 message
          | W.Inductive _ -> stop 3 "internal declaration dispatch mismatch" in
          let input={A.kind=kind;name=name h.W.name;params=List.map name h.W.params;
                   typ=expr h.W.typ;value=v} in
          A.admit !env input in
        match result with
        | Ok(next,th) ->
          if hyp th <> [] || not(aconv(concl th)(environment_judgment next))
          then stop 3 "admission certificate mismatch";
          env:=next; incr checked
        | Error e ->
          (* Failed proof search is a decline, not a proof of invalidity. *)
          stop (match e.H.kind with H.Invalid_input -> 1 | _ -> 2) e.H.message) declarations;
      let th=A.certificate !env in
      if hyp th <> [] || not(aconv(concl th)(environment_judgment !env))
      then stop 3 "final environment certificate mismatch";
      0,describe "accept: closed HOL environment certificate relative to explicit object-axiom policy"
    with
    | Verdict(code,message) -> code,describe message
    | Wire.Error e -> line:=e.Wire.line; Wire.error_exit_code e,describe e.Wire.message
    | Stack_overflow -> 2,describe "stack resource exhausted"
    | Out_of_memory -> 2,describe "memory resource exhausted"
    | Sys_error message -> 3,describe message
    | exn -> 3,describe(Printexc.to_string exn)
end;;
