(* Transport from immutable wire syntax to structurally extracted Gallina.
   No logical decisions, unchecked casts, or expected-test data belong here. *)
module C = Lean_arena

exception Resource of string
exception Unsupported of string

let bool b = if b then C.True else C.False
let list f xs = List.fold_left (fun tail x -> C.Cons (f x,tail)) C.Nil (List.rev xs)
let nat i =
  if i < 0 || i > 1_000_000 then raise (Resource "unary index/fuel exceeds 1000000");
  let rec loop n acc = if n = 0 then acc else loop (n-1) (C.S acc) in
  loop i C.O
let index z =
  if not (Z.fits_int z) then raise (Resource "index exceeds address range");
  nat (Z.to_int z)
let binary z =
  if Z.sign z < 0 then invalid_arg "negative natural";
  let rec positive z =
    if Z.equal z Z.one then C.XH else
    let tail = positive (Z.shift_right z 1) in
    if Z.testbit z 0 then C.XI tail else C.XO tail in
  if Z.equal z Z.zero then C.N0 else C.Npos (positive z)
let ascii c =
  let n = Char.code c in
  let bit i = bool (n land (1 lsl i) <> 0) in
  C.Ascii (bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let string s =
  let result = ref C.EmptyString in
  for i = String.length s - 1 downto 0 do
    result := C.String (ascii s.[i], !result)
  done;
  !result

(* Physical memoization preserves export DAG sharing. Hash collisions never
   merge unequal nodes: equality is physical identity, not the hash value. *)
module Names = Hashtbl.Make(struct
  type t = Wire.name
  let equal a b = a == b
  let hash = Hashtbl.hash
end)
module Levels = Hashtbl.Make(struct
  type t = Wire.level
  let equal a b = a == b
  let hash = Hashtbl.hash
end)
module Exprs = Hashtbl.Make(struct
  type t = Wire.expr
  let equal a b = a == b
  let hash = Hashtbl.hash
end)
type state = { names : C.name Names.t; levels : C.level Levels.t; exprs : C.expr Exprs.t }
let create () = {names=Names.create 1024;levels=Levels.create 1024;exprs=Exprs.create 8192}
let rec name st n = match Names.find_opt st.names n with
  | Some result -> result
  | None ->
    let result = match n with
      | Wire.Anonymous -> C.NameAnon
      | Wire.Str (p,s) -> C.NameStr (name st p,string s)
      | Wire.Num (p,n) -> C.NameNum (name st p,binary n) in
    Names.add st.names n result; result
let rec level st u = match Levels.find_opt st.levels u with
  | Some result -> result
  | None ->
    let result = match u with
      | Wire.Zero -> C.LZero
      | Wire.Succ v -> C.LSucc (level st v)
      | Wire.Max (a,b) -> C.LMax (level st a,level st b)
      | Wire.IMax (a,b) -> C.LIMax (level st a,level st b)
      | Wire.Param n -> C.LParam (name st n) in
    Levels.add st.levels u result; result
let binder = function
  | Wire.Explicit -> C.BDefault | Wire.Implicit -> C.BImplicit
  | Wire.StrictImplicit -> C.BStrictImplicit | Wire.InstanceImplicit -> C.BInstImplicit
let rec expr st e = match Exprs.find_opt st.exprs e with
  | Some result -> result
  | None ->
    let result = match e with
      | Wire.BVar i -> C.EBVar (index i)
      | Wire.Sort u -> C.ESort (level st u)
      | Wire.Const (n,us) -> C.EConst (name st n,list (level st) us)
      | Wire.App (f,a) -> C.EApp (expr st f,expr st a)
      | Wire.Lam (n,a,b,bi) -> C.ELam (name st n,binder bi,expr st a,expr st b)
      | Wire.Pi (n,a,b,bi) -> C.EPi (name st n,binder bi,expr st a,expr st b)
      | Wire.Let (n,a,v,b,nd) -> C.ELet (name st n,expr st a,expr st v,expr st b,bool nd)
      | Wire.Proj (n,i,a) -> C.EProj (name st n,index i,expr st a)
      | Wire.NatLit n -> C.ELit (C.LitNat (binary n))
      | Wire.StringLit s -> C.ELit (C.LitString (string s))
      | Wire.MData a -> C.EMData (expr st a) in
    Exprs.add st.exprs e result; result
let hints = function
  | Wire.OpaqueHint -> C.HintOpaque
  | Wire.Abbrev -> C.HintAbbrev
  | Wire.Regular height -> C.HintRegular (binary height)
let definition st (d : Wire.definition) =
  let h = d.header in
  let safety = match d.safety with Wire.Safe -> C.InputSafe
    | Wire.Partial -> C.InputPartial | Wire.Unsafe -> C.InputUnsafe in
  C.InputDefinition (hints d.hints,name st h.name,list (name st) h.params,expr st h.typ,expr st d.value,safety)
let declaration st = function
  | Wire.Axiom (h,unsafe) ->
    C.InputAxiom (name st h.name,list (name st) h.params,expr st h.typ,bool unsafe)
  | Wire.Definition d ->
    definition st d
  | Wire.Theorem (h,v,_) ->
    C.InputTheorem (name st h.name,list (name st) h.params,expr st h.typ,expr st v)
  | Wire.Opaque (h,v,unsafe,_) ->
    C.InputOpaque (name st h.name,list (name st) h.params,expr st h.typ,expr st v,bool unsafe)
  | Wire.Inductive _ -> raise (Unsupported "inductive admission/metadata validation is not yet implemented")
  | Wire.Quotient _ -> raise (Unsupported "quotient admission is not yet implemented")

let raw_constant st (h : Wire.constant) kind = {
  C.decl_hints = C.HintOpaque; decl_name = name st h.name; decl_params = list (name st) h.params;
  decl_type = expr st h.typ; decl_value = C.None; decl_kind_of = kind
}
let inductive st (i : Wire.inductive) =
  raw_constant st i.ind_header (C.DInductive {
    C.ind_num_params = index i.ind_num_params; ind_num_indices = index i.num_indices;
    ind_all = list (name st) i.ind_all; ind_ctors = list (name st) i.constructors;
    ind_num_nested = index i.num_nested; ind_is_rec = bool i.is_rec;
    ind_is_reflexive = bool i.is_reflexive; ind_is_unsafe = bool i.ind_unsafe
  })
let constructor st (c : Wire.constructor) =
  raw_constant st c.ctor_header (C.DConstructor {
    C.ctor_induct = name st c.induct; ctor_index = index c.cidx;
    ctor_num_params = index c.ctor_num_params; ctor_num_fields = index c.num_fields;
    ctor_is_unsafe = bool c.ctor_unsafe
  })
let rule st (r : Wire.rule) = {
  C.rule_ctor = name st r.ctor; rule_nfields = index r.nfields; rule_rhs = expr st r.rhs
}
let recursor st (r : Wire.recursor) =
  raw_constant st r.rec_header (C.DRecursor {
    C.rec_all = list (name st) r.rec_all; rec_num_params = index r.rec_num_params;
    rec_num_indices = index r.rec_num_indices; rec_num_motives = index r.num_motives;
    rec_num_minors = index r.num_minors; rec_rules = list (rule st) r.rules;
    rec_k = bool r.k; rec_is_unsafe = bool r.rec_unsafe
  })

let admit fuel env st = function
  | Wire.Inductive (types,ctors,recs) -> C.admit_inductive_extended fuel env
      (list (inductive st) types) (list (constructor st) ctors) (list (recursor st) recs)
  | Wire.Quotient (h,k) ->
    let kind = match k with Wire.QuotType -> C.QType | Wire.QuotCtor -> C.QCtor
      | Wire.QuotLift -> C.QLift | Wire.QuotInd -> C.QInd in
    C.admit_quotient fuel env (name st h.name) (list (name st) h.params) (expr st h.typ) kind
  | d -> C.admit_extended fuel env (declaration st d)

let mutual fuel env st ds = C.admit_mutual fuel env (list (definition st) ds)

let reject_reason = function
  | C.UnknownConstant -> "unknown constant" | C.UnknownFreeVariable -> "unknown free variable"
  | C.LooseBoundVariable -> "loose bound variable" | C.UnknownUniverse -> "undeclared universe"
  | C.UniverseArity -> "universe argument arity" | C.ExpectedSort -> "expected sort"
  | C.ExpectedPi -> "expected function type" | C.TypeMismatch -> "type mismatch"
  | C.NotDefinitionallyEqual -> "not definitionally equal" | C.DuplicateDeclaration -> "duplicate declaration"
  | C.DuplicateUniverse -> "duplicate universe parameter" | C.MalformedDeclaration -> "malformed declaration"
  | C.MetaVariable -> "metavariable in kernel input"
let decline_reason = function
  | C.OutOfFuel -> "checker fuel exhausted"
  | C.UnsupportedExpression -> "unsupported expression: literal/projection"
  | C.UnsupportedDeclaration -> "unsupported declaration: primitive/unsafe/partial"
