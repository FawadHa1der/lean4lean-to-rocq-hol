(* Test-only explicit canonical encoding of every field of result environment.
   No casts, Marshal, or production verdict calls. *)
module C = Lean_arena
let tag n xs : Yojson.Safe.t = `List (`String n :: xs)
let boolean = function C.True -> `Bool true | C.False -> `Bool false
let natural n =
  let rec loop acc = function C.O -> acc | C.S n -> loop (acc+1) n in `Int (loop 0 n)
let rec positive = function
  | C.XH -> Z.one | C.XO p -> Z.shift_left (positive p) 1
  | C.XI p -> Z.succ (Z.shift_left (positive p) 1)
let binary = function C.N0 -> `String "0" | C.Npos p -> `String (Z.to_string (positive p))
let ascii (C.Ascii(a,b,c,d,e,f,g,h)) =
  let bit = function C.True -> 1 | C.False -> 0 in
  Char.chr (bit a + 2*bit b + 4*bit c + 8*bit d + 16*bit e + 32*bit f + 64*bit g + 128*bit h)
let string s =
  let rec loop acc = function C.EmptyString -> `List (List.rev acc)
    | C.String(c,s) -> loop (`Int (Char.code (ascii c))::acc) s in
  tag "StringBytes" [loop [] s]
let list f xs =
  let rec loop acc = function C.Nil -> `List (List.rev acc) | C.Cons(x,xs) -> loop (f x::acc) xs in loop [] xs
let option f = function C.None -> tag "None" [] | C.Some x -> tag "Some" [f x]
let rec name = function
  | C.NameAnon -> tag "NameAnon" [] | C.NameStr(n,s) -> tag "NameStr" [name n;string s]
  | C.NameNum(n,i) -> tag "NameNum" [name n;binary i]
let rec level = function
  | C.LZero -> tag "LZero" [] | C.LSucc u -> tag "LSucc" [level u]
  | C.LMax(u,v) -> tag "LMax" [level u;level v] | C.LIMax(u,v) -> tag "LIMax" [level u;level v]
  | C.LParam n -> tag "LParam" [name n]
  | C.LMVar n -> tag "LMVar" [name n]
let binder = function
  | C.BDefault -> `String "BDefault" | C.BImplicit -> `String "BImplicit"
  | C.BStrictImplicit -> `String "BStrictImplicit" | C.BInstImplicit -> `String "BInstImplicit"
let literal = function C.LitNat n -> tag "LitNat" [binary n] | C.LitString s -> tag "LitString" [string s]
let rec expr = function
  | C.EBVar i -> tag "EBVar" [natural i] | C.EFVar n -> tag "EFVar" [name n]
  | C.EMVar n -> tag "EMVar" [name n] | C.ESort u -> tag "ESort" [level u]
  | C.EConst(n,us) -> tag "EConst" [name n;list level us]
  | C.EApp(f,a) -> tag "EApp" [expr f;expr a]
  | C.ELam(n,bi,a,b) -> tag "ELam" [name n;binder bi;expr a;expr b]
  | C.EPi(n,bi,a,b) -> tag "EPi" [name n;binder bi;expr a;expr b]
  | C.ELet(n,a,v,b,nd) -> tag "ELet" [name n;expr a;expr v;expr b;boolean nd]
  | C.ELit l -> tag "ELit" [literal l]
  | C.EProj(n,i,a) -> tag "EProj" [name n;natural i;expr a]
  | C.EMData a -> tag "EMData" [expr a]
let primitive p = `String (match p with
  | C.PNatAdd -> "PNatAdd" | C.PNatPred -> "PNatPred" | C.PNatSub -> "PNatSub"
  | C.PNatMul -> "PNatMul" | C.PNatPow -> "PNatPow" | C.PNatGcd -> "PNatGcd"
  | C.PNatMod -> "PNatMod" | C.PNatDiv -> "PNatDiv" | C.PNatBEq -> "PNatBEq"
  | C.PNatBLE -> "PNatBLE" | C.PNatLAnd -> "PNatLAnd" | C.PNatLOr -> "PNatLOr"
  | C.PNatXor -> "PNatXor" | C.PNatBitwise -> "PNatBitwise" | C.PNatShiftLeft -> "PNatShiftLeft"
  | C.PNatShiftRight -> "PNatShiftRight" | C.PCharOfNat -> "PCharOfNat" | C.PStringOfList -> "PStringOfList")
let quotient q = `String (match q with C.QType -> "QType" | C.QCtor -> "QCtor" | C.QLift -> "QLift" | C.QInd -> "QInd")
let inductive i = tag "inductive_data" [natural i.C.ind_num_params;natural i.C.ind_num_indices;
  list name i.C.ind_all;list name i.C.ind_ctors;natural i.C.ind_num_nested;
  boolean i.C.ind_is_rec;boolean i.C.ind_is_reflexive;boolean i.C.ind_is_unsafe]
let constructor c = tag "constructor_data" [name c.C.ctor_induct;natural c.C.ctor_index;
  natural c.C.ctor_num_params;natural c.C.ctor_num_fields;boolean c.C.ctor_is_unsafe]
let rule r = tag "recursor_rule" [name r.C.rule_ctor;natural r.C.rule_nfields;expr r.C.rule_rhs]
let recursor r = tag "recursor_data" [list name r.C.rec_all;natural r.C.rec_num_params;
  natural r.C.rec_num_indices;natural r.C.rec_num_motives;natural r.C.rec_num_minors;
  list rule r.C.rec_rules;boolean r.C.rec_k;boolean r.C.rec_is_unsafe]
let rec kind = function
  | C.DAssumption -> tag "DAssumption" [] | C.DDefinition -> tag "DDefinition" []
  | C.DTheorem -> tag "DTheorem" [] | C.DOpaque -> tag "DOpaque" []
  | C.DUnsupported -> tag "DUnsupported" [] | C.DPartial -> tag "DPartial" []
  | C.DInductive i -> tag "DInductive" [inductive i] | C.DConstructor c -> tag "DConstructor" [constructor c]
  | C.DRecursor r -> tag "DRecursor" [recursor r] | C.DPrimitive p -> tag "DPrimitive" [primitive p]
  | C.DQuotient q -> tag "DQuotient" [quotient q] | C.DUnsafe k -> tag "DUnsafe" [kind k]
let hints = function
  | C.HintOpaque -> tag "HintOpaque" []
  | C.HintAbbrev -> tag "HintAbbrev" []
  | C.HintRegular height -> tag "HintRegular" [binary height]
let declaration d = tag "declaration" [name d.C.decl_name;list name d.C.decl_params;
  expr d.C.decl_type;option expr d.C.decl_value;kind d.C.decl_kind_of;hints d.C.decl_hints]
let reject = function
  | C.UnknownConstant -> "UnknownConstant" | C.UnknownFreeVariable -> "UnknownFreeVariable"
  | C.LooseBoundVariable -> "LooseBoundVariable" | C.UnknownUniverse -> "UnknownUniverse"
  | C.UniverseArity -> "UniverseArity" | C.ExpectedSort -> "ExpectedSort" | C.ExpectedPi -> "ExpectedPi"
  | C.TypeMismatch -> "TypeMismatch" | C.NotDefinitionallyEqual -> "NotDefinitionallyEqual"
  | C.DuplicateDeclaration -> "DuplicateDeclaration" | C.DuplicateUniverse -> "DuplicateUniverse"
  | C.MalformedDeclaration -> "MalformedDeclaration" | C.MetaVariable -> "MetaVariable"
let decline = function C.OutOfFuel -> "OutOfFuel" | C.UnsupportedExpression -> "UnsupportedExpression"
  | C.UnsupportedDeclaration -> "UnsupportedDeclaration"
let result = function
  | C.Accept env -> tag "Accept" [list declaration env]
  | C.Reject why -> tag "Reject" [`String (reject why)]
  | C.Decline why -> tag "Decline" [`String (decline why)]
