(* Loaded by HOL Light after hol/environment.ml and bytecompiled Hol_input. *)
needs "hol/primitive_validation.ml";;
needs "hol/text_validation.ml";;
needs "hol/raw_ctor_admission.ml";;
needs "hol/raw_indexed_admission.ml";;
needs "frontend/reducible_candidate.ml";;
module Hol_check = struct
  module H = Lean4hol
  module A = Lean4hol_env
  module W = Hol_input
  module P = Lean4hol_primitive
  module T = Lean4hol_text
  module R = Lean4hol_raw_ctor
  module I = Lean4hol_raw_indexed
  module C = Lean4hol_input_certificate
  module Names = Hashtbl.Make(struct
    type t = W.name
    let equal a b = a == b
    let hash = Hashtbl.hash
  end)
  module Levels = Hashtbl.Make(struct
    type t = W.level
    let equal a b = a == b
    let hash = Hashtbl.hash
  end)
  module Exprs = Hashtbl.Make(struct
    type t = W.expr
    let equal a b = a == b
    let hash = Hashtbl.hash
  end)
  let names = Names.create 127
  let levels = Levels.create 127
  let exprs = Exprs.create 127
  let reset_syntax () = Names.clear names; Levels.clear levels; Exprs.clear exprs
  let rec name n = match Names.find_opt names n with
    | Some result -> result
    | None -> let result = match n with
    | W.Anonymous -> H.Anonymous | W.Str(n,s) -> H.Str(name n,s)
    | W.Num(n,s) -> H.Num(name n,s) in
      if Names.length names >= 4096 then Names.clear names;
      Names.replace names n result; result
  let rec level u = match Levels.find_opt levels u with
    | Some result -> result
    | None -> let result = match u with
    | W.Zero -> H.Zero | W.Succ u -> H.Succ(level u)
    | W.Max(u,v) -> H.Max(level u,level v)
    | W.Imax(u,v) -> H.Imax(level u,level v) | W.Param n -> H.Param(name n) in
      if Levels.length levels >= 4096 then Levels.clear levels;
      Levels.replace levels u result; result
  (* Preserve immutable input sharing without trusting hashes as syntax equality. *)
  let rec expr e = match Exprs.find_opt exprs e with
    | Some result -> result
    | None -> let result = match e with
    | W.Bvar i -> H.Bvar i | W.Sort u -> H.Sort(level u)
    | W.Const(n,us) -> H.Const(name n,List.map level us)
    | W.App(f,a) -> H.App(expr f,expr a)
    | W.Lam(n,a,b) -> H.Lam(name n,expr a,expr b)
    | W.Pi(n,a,b) -> H.Pi(name n,expr a,expr b)
    | W.Let(n,a,v,b) -> H.Let(name n,expr a,expr v,expr b)
    | W.Natlit n -> H.Natlit n
    | W.Strlit s -> H.Strlit s
    | W.Proj(n,i,e) -> H.Proj(name n,i,expr e) in
      if Exprs.length exprs >= 4096 then Exprs.clear exprs;
      Exprs.replace exprs e result; result
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
    | H.Sort _ | H.Const _ | H.Natlit _ | H.Strlit _ -> true
    | H.Proj(_,_,e) -> closed depth e
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
        | (H.Sort _ | H.Const _ | H.Natlit _ | H.Strlit _) as e -> e
        | H.Proj(n,i,e) -> H.Proj(n,i,lower count depth e)
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
  let indexed_inductive claims =
    let claims=List.map claim claims in
    let inds=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)claims in
    match inds with
    | [{A.kind=A.Generated(A.Inductive_role info);name=i;params=ps;typ;value=None}]
        when info.A.num_nested=0 && not info.A.is_unsafe ->
      let rec telescope n e =
        if n=0 then [],e else match e with
        | H.Pi(b,a,t) -> let rest,r=telescope (n-1) t in (b,a)::rest,r
        | _ -> unsupported "HOL reducible indexed telescopes are pending" in
      let parameters,body=telescope info.A.num_params typ in
      let indices,result=telescope info.A.num_indices body in
      let result_level=match result with H.Sort u->u
        | _ -> unsupported "HOL reducible indexed result sort is pending" in
      let levels=List.map(fun p->H.Param p)ps in
      let rec app_head args = function
        | H.App(f,a) -> app_head (a::args) f
        | head -> head,args in
      let rec split n xs =
        if n=0 then [],xs else match xs with
        | x::xs -> let front,back=split (n-1) xs in x::front,back
        | [] -> unsupported "HOL indexed application has too few parameters" in
      let family_indices offset e =
        let head,args=app_head [] e in
        if head<>H.Const(i,levels) || List.length args<>info.A.num_params+info.A.num_indices
        then None else
        let parameters,indices=split info.A.num_params args in
        let expected=List.init info.A.num_params(fun j->H.Bvar(offset+info.A.num_params-1-j)) in
        if parameters=expected then Some indices else None in
      (* Indexed fields remain in the full parameter/preceding-field context.
         The native generator proves agreement with every original claim. *)
      let recursive_field offset a =
        let rec descend depth ds = function
          | H.Pi(_,d,b) -> descend (depth+1) (d::ds) b
          | result -> match family_indices (offset+depth) result with
            | Some xs -> Some(if depth=0 then A.Index_recursive xs
                else A.Index_function(List.rev ds,xs))
            | None -> None in
        descend 0 [] a in
      let rec fields offset = function
        | H.Pi(_,a,b) ->
          let field=match recursive_field offset a with
            | Some f -> f
            | None -> A.Index_data a in
          let rest,result=fields (offset+1) b in field::rest,result
        | result -> match family_indices offset result with
          | Some xs -> [],xs
          | None -> unsupported "HOL nonuniform or reducible indexed constructor result is pending" in
      let constructors=List.map(fun n->
        match List.find_opt(fun d->d.A.name=n)claims with
        | Some {A.kind=A.Generated(A.Constructor_role _);typ;_} ->
          let _,body=telescope info.A.num_params typ in
          let fs,result=fields 0 body in
          {A.indexed_ctor_name=n;indexed_fields=fs;result_indices=result}
        | _ -> unsupported "HOL indexed constructor claim is absent or malformed")info.A.ctors in
      {A.indexed_name=i;indexed_level_params=ps;indexed_parameters=parameters;indices;
        indexed_result_level=result_level;indexed_constructors=constructors;indexed_claims=claims}
    | _ -> unsupported "HOL mutual, nested or unsafe indexed families are pending"
  let mutual_inductive original =
    let claims=List.map claim original in
    let headers=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)claims in
    let first,info=match headers with
      | ({A.kind=A.Generated(A.Inductive_role info);_} as d)::_ when List.length headers>1 -> d,info
      | _ -> unsupported "HOL mutual candidate needs at least two families" in
    let rec telescope n e=if n=0 then [],e else match e with
      | H.Pi(b,a,t)->let rest,r=telescope(n-1)t in (b,a)::rest,r
      | _->unsupported "HOL raw/reducible mutual telescopes are pending" in
    let pars,result=telescope info.A.num_params first.A.typ in
    let u=match result with H.Sort u->u|_->unsupported "HOL indexed mutual families are pending" in
    let ps=first.A.params and ns=info.A.all in
    let levels=List.map(fun n->H.Param n)ps in
    let rec spine args=function H.App(f,a)->spine(a::args)f|f->f,args in
    let target offset e=match spine [] e with
      | H.Const(i,us),args when List.mem i ns && us=levels &&
          args=List.init info.A.num_params(fun j->H.Bvar(offset+info.A.num_params-1-j))->Some i
      | _->None in
    let recursive_field offset a=
      let rec loop depth ds=function
        | H.Pi(_,d,b)->loop(depth+1)(d::ds)b
        | result->match target(offset+depth)result with
          | Some i->A.Mutual_recursive(i,List.rev ds)|None->A.Mutual_data a in
      loop 0 [] a in
    let rec fields owner offset=function
      | H.Pi(_,a,b)->recursive_field offset a::fields owner(offset+1)b
      | result when target offset result=Some owner->[]
      | _->unsupported "HOL nonuniform/indexed/reducible mutual constructor result is pending" in
    let families=List.map(fun i->
      match List.find_opt(fun d->d.A.name=i)headers with
      | Some {A.kind=A.Generated(A.Inductive_role ri);_}
          when ri.A.num_indices=0 && ri.A.num_nested=0 && not ri.A.is_unsafe ->
        let constructors=List.map(fun c->match List.find_opt(fun d->d.A.name=c)claims with
          | Some {A.kind=A.Generated(A.Constructor_role _);typ;_}->
            let _,body=telescope info.A.num_params typ in
            {A.mutual_ctor_name=c;mutual_fields=fields i 0 body}
          | _->unsupported "HOL mutual constructor claim is missing")ri.A.ctors in
        {A.mutual_name=i;mutual_constructors=constructors}
      | _->unsupported "HOL missing, indexed, nested or unsafe mutual family")ns in
    {A.mutual_level_params=ps;mutual_parameters=pars;mutual_result_level=u;
     mutual_families=families;mutual_claims=claims}
  let indexed_mutual original =
    let claims=List.map claim original in
    let headers=List.filter(fun d->match d.A.kind with A.Generated(A.Inductive_role _)->true|_->false)claims in
    let first,info=match headers with
      |({A.kind=A.Generated(A.Inductive_role info);_}as d)::_ when List.length headers>1->d,info
      |_->unsupported "HOL indexed mutual candidate needs at least two families" in
    let rec telescope n e=if n=0 then [],e else match e with
      |H.Pi(b,a,t)->let rest,r=telescope(n-1)t in (b,a)::rest,r
      |_->unsupported "HOL raw/reducible indexed mutual telescopes are pending" in
    let pars,rest=telescope info.A.num_params first.A.typ in
    let _,result=telescope info.A.num_indices rest in
    let u=match result with H.Sort u->u|_->unsupported "HOL indexed mutual header must end in a sort" in
    let ps=first.A.params and ns=info.A.all and p=info.A.num_params in
    let levels=List.map(fun n->H.Param n)ps in
    let header i=match List.find_opt(fun d->d.A.name=i)headers with
      |Some({A.kind=A.Generated(A.Inductive_role ri);_}as d)
          when ri.A.num_nested=0 && not ri.A.is_unsafe->d,ri
      |_->unsupported "HOL missing, nested or unsafe indexed mutual family" in
    let rec split n xs=if n=0 then [],xs else match xs with
      |x::xs->let before,after=split(n-1)xs in x::before,after
      |[]->unsupported "HOL indexed mutual parameter arity" in
    let rec spine args=function H.App(f,a)->spine(a::args)f|f->f,args in
    let target offset e=match spine [] e with
      |H.Const(i,us),args when List.mem i ns && us=levels->
        let _,ri=header i in
        if List.length args<>p+ri.A.num_indices then None else
        let params,indices=split p args in
        if params=List.init p(fun j->H.Bvar(offset+p-1-j))then Some(i,indices)else None
      |_->None in
    let recursive_field offset a=
      let rec loop depth ds=function H.Pi(_,d,b)->loop(depth+1)(d::ds)b
        |result->match target(offset+depth)result with
          |Some(i,xs)->A.Mindex_recursive(i,List.rev ds,xs)|None->A.Mindex_data a in
      loop 0 [] a in
    let rec fields owner offset=function
      |H.Pi(_,a,b)->let fs,xs=fields owner(offset+1)b in recursive_field offset a::fs,xs
      |result->match target offset result with
        |Some(i,xs)when i=owner->[],xs
        |_->unsupported "HOL nonuniform/reducible indexed mutual constructor result" in
    let families=List.map(fun i->let d,ri=header i in
      let _,rest=telescope p d.A.typ in let inds,_=telescope ri.A.num_indices rest in
      let constructors=List.map(fun c->match List.find_opt(fun d->d.A.name=c)claims with
        |Some{A.kind=A.Generated(A.Constructor_role _);typ;_}->
          let _,body=telescope p typ in let fs,xs=fields i 0 body in
          {A.mindex_ctor_name=c;mindex_fields=fs;mindex_result_indices=xs}
        |_->unsupported "HOL indexed mutual constructor claim missing")ri.A.ctors in
      {A.mindex_name=i;mindex_indices=inds;mindex_constructors=constructors})ns in
    {A.mindex_level_params=ps;mindex_parameters=pars;mindex_result_level=u;
     mindex_families=families;mindex_claims=claims}
  let admit_generated env claims =
    let legacy=try Some(A.admit_inductive env (inductive_block claims))
      with Verdict(2,_) -> None in
    match legacy with
    | Some(Ok _ as result) -> result
    | Some(Error {H.kind=(H.Invalid_input | H.Resource);_} as result) -> result
    | _ ->
      let family=try Some(A.admit_inductive_family env (inductive_family claims))
        with Verdict(2,_) -> None in
      match family with
      | Some(Ok _ as result) -> result
      | Some(Error {H.kind=(H.Invalid_input | H.Resource);_} as result) -> result
      | _ ->
        let indexed=try Some(A.admit_indexed_inductive env(indexed_inductive claims))
          with Verdict(2,_)->None in
        match indexed with
        | Some result->result
        | None->
          let mutual=try Some(A.admit_mutual_inductive env(mutual_inductive claims))
            with Verdict(2,_)->None in
          match mutual with Some result->result
          |None->A.admit_indexed_mutual env(indexed_mutual claims)
  let environment_judgment env = list_mk_comb (`l4_evalid`,[A.quote_policy env;A.quote_env env])
  type input_certificate = {
    environment : A.environment;
    raw_history : A.declaration list list;
    theorem : thm
  }
  type raw_admission =
    | Raw_family of A.declaration list * thm
    | Raw_indexed of A.declaration list * thm
  let check_file_with_certificate path =
    reset_syntax();
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
      let blocks=ref [] in
      let trace=ref(C.start !env) in
      List.iter(fun(n,d)->
        line:=n;
        let raw=ref [] and raw_admission=ref None in
        let result=match d with
          | W.Inductive claims ->
            raw:=List.map claim claims;
            let ordinary=try admit_generated !env claims with
              Verdict(2,message)->Error {H.kind=H.Unsupported;message} in
            (match ordinary with
            | Ok _ -> ordinary
            | Error {H.kind=(H.Invalid_input | H.Resource);_} -> ordinary
            | Error _ ->
              let family=match Reducible_candidate.family !env !raw with
              | Error e -> Error e
              | Ok b -> match A.admit_inductive_family !env b with
                | Error e -> Error e
                | Ok(next,th) -> match R.certify !env next !raw b with
                  | Error e -> Error e
                  | Ok proof -> raw_admission:=Some(Raw_family(b.A.family_claims,proof)); Ok(next,th) in
              (match family with
               | Ok _ | Error {H.kind=(H.Invalid_input | H.Resource);_} -> family
               | Error _ -> match Reducible_candidate.indexed !env !raw with
                 | Error e -> Error e
                 | Ok b -> match A.admit_indexed_inductive !env b with
                   | Error e -> Error e
                   | Ok(next,th) -> match I.certify !env next !raw b with
                     | Error e -> Error e
                     | Ok proof -> raw_admission:=Some(Raw_indexed(b.A.indexed_claims,proof)); Ok(next,th)))
          | W.Quotient(h,k) ->
            let k=match k with W.Qtype -> Lean4hol_quotient_model.Qtype
              | W.Qctor -> Lean4hol_quotient_model.Qctor
              | W.Qlift -> Lean4hol_quotient_model.Qlift
              | W.Qind -> Lean4hol_quotient_model.Qind in
            let input={A.kind=A.Quotient k;name=name h.W.name;
              params=List.map name h.W.params;typ=expr h.W.typ;value=None} in
            raw:=[input]; A.admit_quotient !env input
          | W.Unsupported message -> stop 2 message
          | d ->
          let kind,h,v=match d with
          | W.Definition(h,v) -> A.Definition,h,Some(expr v)
          | W.Primitive_definition(h,v) -> A.Definition,h,Some(expr v)
          | W.Text_primitive_definition(h,v) -> A.Definition,h,Some(expr v)
          | W.Theorem(h,v) -> A.Theorem,h,Some(expr v)
          | W.Opaque(h,v) -> A.Opaque,h,Some(expr v)
          | W.Axiom h -> A.Axiom,h,None
          | W.Unsupported message -> stop 2 message
          | W.Inductive _ | W.Quotient _ -> stop 3 "internal declaration dispatch mismatch" in
          let input={A.kind=kind;name=name h.W.name;params=List.map name h.W.params;
                   typ=expr h.W.typ;value=v} in
          raw:=[input];
          (match d with
           | W.Primitive_definition _ ->
             (match P.check_definition !env input with
              | Ok certificate -> A.admit_primitive !env input (P.definition_raw_theorem certificate)
              | Error e -> Error e)
           | W.Text_primitive_definition _ ->
             (match T.check_definition !env input with
              | Ok certificate -> A.admit_text_primitive !env input (T.raw_theorem certificate)
              | Error e -> Error e)
           | _ -> A.admit !env input) in
        match result with
        | Ok(next,th) ->
          if hyp th <> [] || not(aconv(concl th)(environment_judgment next))
          then stop 3 "admission certificate mismatch";
          let traced=match !raw_admission with
            | None -> C.append_exact !env next !blocks !raw !trace
            | Some(Raw_family(canonical,proof)) -> C.append_raw !env next !blocks !raw canonical !trace proof
            | Some(Raw_indexed(canonical,proof)) -> C.append_indexed !env next !blocks !raw canonical !trace proof in
          (match traced with Ok h -> trace:=h | Error e -> stop 2 e.H.message);
          blocks:= !raw :: !blocks;
          env:=next; incr checked
        | Error e ->
          (* Failed proof search is a decline, not a proof of invalidity. *)
          stop (match e.H.kind with H.Invalid_input -> 1 | _ -> 2) e.H.message) declarations;
      let th=A.certificate !env in
      if hyp th <> [] || not(aconv(concl th)(environment_judgment !env))
      then stop 3 "final environment certificate mismatch";
      let theorem=match C.finish !env !blocks !trace with
        | Ok h -> h | Error e -> stop 2 e.H.message in
      if hyp theorem<>[] || not(aconv(concl theorem)(C.expected !env !blocks))
      then stop 3 "final raw input certificate mismatch";
      0,describe "accept: closed exact HOL raw-input and environment certificate",
        Some {environment= !env;raw_history= !blocks;theorem}
    with
    | Verdict(code,message) -> code,describe message,None
    | Wire.Error e -> line:=e.Wire.line; Wire.error_exit_code e,describe e.Wire.message,None
    | Stack_overflow -> 2,describe "stack resource exhausted",None
    | Out_of_memory -> 2,describe "memory resource exhausted",None
    | Sys_error message -> 3,describe message,None
    | exn -> 3,describe(Printexc.to_string exn),None
  let check_file path =
    let code,message,_=check_file_with_certificate path in code,message
end;;
