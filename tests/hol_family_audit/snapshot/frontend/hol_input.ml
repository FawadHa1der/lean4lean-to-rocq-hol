(* Bytecompiled transport bridge with Camlp5-compatible constructor spellings.
   This module parses and translates syntax; it never establishes typing. *)
type name = Anonymous | Str of name * string | Num of name * string
type level = Zero | Succ of level | Max of level * level
           | Imax of level * level | Param of name
type expr = Bvar of int | Sort of level | Const of name * level list
          | App of expr * expr | Lam of name * expr * expr
          | Pi of name * expr * expr | Let of name * expr * expr * expr
          | Natlit of string
type constant = {name:name; params:name list; typ:expr}
type rec_rule = {ctor:name; num_fields:int; rhs:expr}
type ind_info = {num_params:int; num_indices:int; all:name list; ctors:name list;
  num_nested:int; is_rec:bool; is_reflexive:bool; is_unsafe:bool}
type ctor_info = {induct:name; index:int; num_params:int; num_fields:int; is_unsafe:bool}
type rec_info = {all:name list; num_params:int; num_indices:int; num_motives:int;
  num_minors:int; rules:rec_rule list; k:bool; is_unsafe:bool}
type role = Inductive_role of ind_info | Constructor_role of ctor_info | Recursor_role of rec_info
type claim = {header:constant; role:role}
type declaration = Definition of constant * expr | Theorem of constant * expr
                 | Axiom of constant | Opaque of constant * expr
                 | Inductive of claim list
                 | Unsupported of string
exception Unavailable of string
let rec name = function
  | Wire.Anonymous -> Anonymous | Wire.Str(p,s) -> Str(name p,s)
  | Wire.Num(p,n) -> Num(name p,Z.to_string n)
let rec level = function
  | Wire.Zero -> Zero | Wire.Succ u -> Succ(level u)
  | Wire.Max(u,v) -> Max(level u,level v)
  | Wire.IMax(u,v) -> Imax(level u,level v) | Wire.Param n -> Param(name n)
module Exprs = Hashtbl.Make(struct
  type t=Wire.expr
  let equal a b = a == b
  let hash=Hashtbl.hash
end)
let rec expr memo e = match Exprs.find_opt memo e with
  | Some result -> result
  | None ->
    let result=match e with
      | Wire.BVar n ->
        if not(Z.fits_int n) then raise(Unavailable "bound-variable index exceeds address range");
        Bvar(Z.to_int n)
      | Wire.Sort u -> Sort(level u)
      | Wire.Const(n,us) -> Const(name n,List.map level us)
      | Wire.App(f,a) -> App(expr memo f,expr memo a)
      | Wire.Lam(n,a,b,_) -> Lam(name n,expr memo a,expr memo b)
      | Wire.Pi(n,a,b,_) -> Pi(name n,expr memo a,expr memo b)
      | Wire.Let(n,a,v,b,_) -> Let(name n,expr memo a,expr memo v,expr memo b)
      | Wire.MData e -> expr memo e
      | Wire.Proj _ -> raise(Unavailable "HOL projection judgment not yet implemented")
      | Wire.NatLit n -> Natlit(Z.to_string n)
      | Wire.StringLit _ -> raise(Unavailable "HOL string literal judgment not yet implemented") in
    Exprs.add memo e result; result
let constant memo (h:Wire.constant) = {name=name h.name;params=List.map name h.params;typ=expr memo h.typ}
let index n = if not(Z.fits_int n) then raise(Unavailable "HOL metadata index exceeds address range") else Z.to_int n
let inductive memo (i:Wire.inductive) =
  {header=constant memo i.ind_header;role=Inductive_role{
    num_params=index i.ind_num_params;num_indices=index i.num_indices;all=List.map name i.ind_all;
    ctors=List.map name i.constructors;num_nested=index i.num_nested;is_rec=i.is_rec;
    is_reflexive=i.is_reflexive;is_unsafe=i.ind_unsafe}}
let constructor memo (c:Wire.constructor) =
  {header=constant memo c.ctor_header;role=Constructor_role{
    induct=name c.induct;index=index c.cidx;num_params=index c.ctor_num_params;
    num_fields=index c.num_fields;is_unsafe=c.ctor_unsafe}}
let recursor memo (r:Wire.recursor) =
  {header=constant memo r.rec_header;role=Recursor_role{
    all=List.map name r.rec_all;num_params=index r.rec_num_params;num_indices=index r.rec_num_indices;
    num_motives=index r.num_motives;num_minors=index r.num_minors;k=r.k;is_unsafe=r.rec_unsafe;
    rules=List.map(fun (r:Wire.rule)->{ctor=name r.ctor;num_fields=index r.nfields;rhs=expr memo r.rhs})r.rules}}
let protected = List.map Wire.dotted_name
  [["Nat"];["Nat";"zero"];["Nat";"succ"];["Bool"];["Bool";"false"];["Bool";"true"];
   ["Nat";"add"];["Nat";"pred"];["Nat";"sub"];["Nat";"mul"];["Nat";"pow"];
   ["Nat";"gcd"];["Nat";"mod"];["Nat";"div"];["Nat";"beq"];["Nat";"ble"];
   ["Nat";"bitwise"];["Nat";"land"];["Nat";"lor"];["Nat";"xor"];
   ["Nat";"shiftLeft"];["Nat";"shiftRight"];["String";"ofList"];["Char";"ofNat"]]
let check_name n = if List.exists (Wire.equal_name n) protected then
  raise(Unavailable "HOL primitive declaration validation not yet implemented")
let declaration memo d = try match d with
  | Wire.Definition d ->
    check_name d.header.name;
    if d.safety <> Wire.Safe then raise(Unavailable "HOL unsafe/partial declarations not yet implemented");
    Definition(constant memo d.header,expr memo d.value)
  | Wire.Theorem(h,v,_) ->
    check_name h.name; Theorem(constant memo h,expr memo v)
  | Wire.Axiom (h,unsafe) ->
    check_name h.name;
    if unsafe then Unsupported "HOL unsafe axiom admission not yet implemented"
    else Axiom (constant memo h)
  | Wire.Opaque (h,v,unsafe,_) ->
    check_name h.name;
    if unsafe then Unsupported "HOL unsafe opaque admission not yet implemented"
    else Opaque (constant memo h,expr memo v)
  | Wire.Inductive (types,ctors,recs) ->
    Inductive (List.map (inductive memo) types @ List.map (constructor memo) ctors @ List.map (recursor memo) recs)
  | Wire.Quotient _ -> Unsupported "HOL quotient admission not yet implemented"
  with Unavailable reason -> Unsupported reason
let translate_export export =
  let memo=Exprs.create export.Wire.expr_count in
  List.map(function
    | Replay.Single(line,d) -> line,declaration memo d
    | Replay.Mutual(line,_) ->
      line,Unsupported "HOL unsafe/partial mutual declaration admission not yet implemented")
    (Replay.schedule export.Wire.declarations)
let read_file path = translate_export (Wire.read_file path)
