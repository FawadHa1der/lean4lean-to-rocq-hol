(* Dependency ordering and batching only. Every declaration reaches the kernel;
   this module never establishes typing or interprets an expected verdict. *)
type batch = Single of int * Wire.declaration | Mutual of int * Wire.definition list
module Names = Hashtbl.Make(struct
  type t = Wire.name
  let equal = Wire.equal_name
  let hash = Hashtbl.hash
end)
module Exprs = Hashtbl.Make(struct
  type t = Wire.expr
  let equal a b = a == b
  (* Large exports contain many syntax nodes with the same short prefix. *)
  let hash = Hashtbl.hash_param 50 256
end)

let names = function
  | Wire.Axiom(h,_) | Wire.Theorem(h,_,_) | Wire.Opaque(h,_,_,_) | Wire.Quotient(h,_) -> [h.name]
  | Wire.Definition d -> [d.header.name]
  | Wire.Inductive(ts,cs,rs) ->
    List.map(fun (d:Wire.inductive)->d.ind_header.name)ts @
    List.map(fun (d:Wire.constructor)->d.ctor_header.name)cs @
    List.map(fun (d:Wire.recursor)->d.rec_header.name)rs

let expressions = function
  | Wire.Axiom(h,_) | Wire.Quotient(h,_) -> [h.typ]
  | Wire.Theorem(h,v,_) | Wire.Opaque(h,v,_,_) -> [h.typ;v]
  | Wire.Definition d -> [d.header.typ;d.value]
  | Wire.Inductive(ts,cs,rs) ->
    List.map(fun (d:Wire.inductive)->d.ind_header.typ)ts @
    List.map(fun (d:Wire.constructor)->d.ctor_header.typ)cs @
    List.concat_map(fun (d:Wire.recursor)->
      d.rec_header.typ :: List.map(fun (r:Wire.rule)->r.rhs)d.rules)rs

let line = function Single(n,_) | Mutual(n,_) -> n
let declarations = function
  | Single(_,d) -> [d]
  | Mutual(_,ds) -> List.map(fun d->Wire.Definition d)ds
let count = function Single _ -> 1 | Mutual(_,ds) -> List.length ds

let nat_dependencies = List.map Wire.dotted_name [["Nat"];["Nat";"zero"];["Nat";"succ"]]
let string_dependencies = List.map Wire.dotted_name
  [["String"];["Char"];["Char";"ofNat"];["String";"ofList"];["List"];["List";"nil"];["List";"cons"]]
let eq_dependency = Wire.dotted_name ["Eq"]

let prepare input =
  let rows=Array.of_list input in
  let size=Array.length rows in
  let index=Names.create (max 16 size) in
  Array.iteri(fun i (line,d)->List.iter(fun name->
    if Names.mem index name then Wire.bad line "duplicate declaration name";
    Names.add index name i)(names d))rows;
  let unique line names =
    let seen=Names.create 16 in
    List.iter(fun n->
      if Names.mem seen n then Wire.bad line "duplicate mutual group member";
      Names.add seen n ())names in
  let same_set a b =
    List.length a=List.length b && List.for_all(fun n->List.exists(Wire.equal_name n)b)a in
  let consumed=Array.make size false and owner=Array.make size (-1) in
  let batches=ref [] and next=ref 0 in
  Array.iteri(fun i (line,d)->if not consumed.(i) then begin
    let batch,members=match d with
      | Wire.Definition first when first.safety=Wire.Partial ||
          (first.safety=Wire.Unsafe && List.length first.all>1) ->
        unique line first.all;
        if not(List.exists(Wire.equal_name first.header.name)first.all) then
          Wire.bad line "definition is absent from its mutual group";
        let members=List.map(fun n->match Names.find_opt index n with
          | Some j -> j | None -> Wire.bad line "missing mutual group declaration")first.all in
        let ds=List.map(fun j->
          if consumed.(j) then Wire.bad line "overlapping mutual definition groups";
          match snd rows.(j) with
          | Wire.Definition d when same_set first.all d.all ->
            unique (fst rows.(j)) d.all; d
          | _ -> Wire.bad line "inconsistent mutual definition group")members in
        Mutual(line,ds),members
      | _ -> Single(line,d),[i] in
    List.iter(fun j->consumed.(j)<-true;owner.(j)<- !next)members;
    batches:=batch:: !batches; incr next
  end)rows;
  let batches=Array.of_list(List.rev !batches) in
  index,owner,batches

type strategy = Input_order | Dependency_graph
type statistics = { strategy : strategy; summarized_exprs : int }
type summary_step = Enter of Wire.expr | Leave of Wire.expr

(* A maximum is sufficient to certify input order, but not to reconstruct
   edges. Cache by physical identity within this invocation's owner map. *)
let input_ordered index owner batches =
  let cache=Exprs.create 8192 in
  let referenced name=match Names.find_opt index name with
    | Some row -> owner.(row) | None -> -1 in
  let maximum names=List.fold_left(fun acc n->max acc (referenced n)) (-1) names in
  let nat=maximum nat_dependencies and string=maximum string_dependencies in
  let eq=referenced eq_dependency in
  let summary root =
    (* Carry completed child summaries instead of looking them up again. *)
    let todo=ref [Enter root] and values=ref [] in
    let save e value = Exprs.add cache e value; values:=value:: !values in
    while !todo<>[] do
      match !todo with
      | [] -> ()
      | step::rest ->
        todo:=rest;
        match step with
        | Enter e ->
          (match Exprs.find_opt cache e with
          | Some value -> values:=value:: !values
          | None -> match e with
          | Wire.Const(n,_) -> save e (referenced n)
          | Wire.NatLit _ -> save e nat
          | Wire.StringLit _ -> save e string
          | Wire.BVar _ | Wire.Sort _ -> save e (-1)
          | Wire.App(a,b) | Wire.Lam(_,a,b,_) | Wire.Pi(_,a,b,_) ->
            todo:=Enter a::Enter b::Leave e::rest
          | Wire.Let(_,a,v,b,_) -> todo:=Enter a::Enter v::Enter b::Leave e::rest
          | Wire.Proj(_,_,a) | Wire.MData a -> todo:=Enter a::Leave e::rest)
        | Leave e ->
          let value,tail=match e, !values with
            | (Wire.App _ | Wire.Lam _ | Wire.Pi _),b::a::tail -> max a b,tail
            | Wire.Let _,b::v::a::tail -> max a (max v b),tail
            | Wire.Proj(n,_,_),a::tail -> max (referenced n) a,tail
            | Wire.MData _,a::tail -> a,tail
            | _ -> assert false in
          values:=tail;
          save e value
    done;
    match !values with [value]->value | _ -> assert false in
  let i=ref 0 in
  while !i<Array.length batches &&
    List.for_all(fun d->
      (match d with Wire.Quotient _ -> eq <= !i | _ -> true) &&
      List.for_all(fun e->summary e <= !i)(expressions d))
      (declarations batches.(!i)) do incr i done;
  !i=Array.length batches,Exprs.length cache

(* The exact dependency graph remains the fallback for any forward edge. *)
let graph_order index owner batches =
  let n=Array.length batches in
  let deps=Array.init n (fun _->Hashtbl.create 16) in
  let visited=Exprs.create 8192 in
  Array.iteri(fun i batch->
    let add name=match Names.find_opt index name with
      | Some row when owner.(row)<>i -> Hashtbl.replace deps.(i) owner.(row) ()
      | _ -> () in
    let todo=ref [] in
    List.iter(fun d->
      (match d with Wire.Quotient _ -> add eq_dependency | _ -> ());
      todo:=List.rev_append (expressions d) !todo)(declarations batch);
    while !todo<>[] do
      match !todo with
      | [] -> ()
      | e::rest ->
        todo:=rest;
        if Exprs.find_opt visited e<>Some i then begin
          Exprs.replace visited e i;
          match e with
          | Wire.Const(n,_) -> add n
          | Wire.App(a,b) | Wire.Lam(_,a,b,_) | Wire.Pi(_,a,b,_) -> todo:=a::b:: !todo
          | Wire.Let(_,a,v,b,_) -> todo:=a::v::b:: !todo
          | Wire.Proj(n,_,a) -> add n;todo:=a:: !todo
          | Wire.MData a -> todo:=a:: !todo
          | Wire.NatLit _ -> List.iter add nat_dependencies
          | Wire.StringLit _ -> List.iter add string_dependencies
          | Wire.BVar _ | Wire.Sort _ -> ()
        end
    done)batches;
  let remaining=Array.map Hashtbl.length deps in
  let users=Array.make n [] in
  Array.iteri(fun i ds->Hashtbl.iter(fun dependency ()->
    users.(dependency)<-i::users.(dependency))ds)deps;
  let ready=Queue.create() in
  Array.iteri(fun i degree->if degree=0 then Queue.add i ready)remaining;
  let result=ref [] and emitted=ref 0 in
  while not(Queue.is_empty ready) do
    let i=Queue.take ready in
    result:=batches.(i):: !result;incr emitted;
    List.iter(fun user->
      remaining.(user)<-remaining.(user)-1;
      if remaining.(user)=0 then Queue.add user ready)(List.rev users.(i))
  done;
  if !emitted<>n then begin
    let i=ref 0 in
    while !i<n && remaining.(!i)=0 do incr i done;
    Wire.bad (line batches.(!i)) "cyclic dependency outside a checked mutual block"
  end;
  List.rev !result

(* force_graph is a diagnostic/test control, never an unchecked fast path. *)
let schedule_with_stats ?(force_graph=false) input =
  let index,owner,batches=prepare input in
  let ordered,summarized_exprs=
    if force_graph then false,0 else input_ordered index owner batches in
  if ordered then Array.to_list batches,{strategy=Input_order;summarized_exprs}
  else graph_order index owner batches,{strategy=Dependency_graph;summarized_exprs}

let schedule input = fst (schedule_with_stats input)
