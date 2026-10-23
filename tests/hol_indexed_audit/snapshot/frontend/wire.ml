(* Lean export transport only. All logical checking belongs to the two cores.
   Schema: leanprover/lean4export format_ndjson.md, format version 3.1.0. *)

type name = Anonymous | Str of name * string | Num of name * Z.t
type level = Zero | Succ of level | Max of level * level
           | IMax of level * level | Param of name
type binder = Explicit | Implicit | StrictImplicit | InstanceImplicit
type expr =
  | BVar of Z.t
  | Sort of level
  | Const of name * level list
  | App of expr * expr
  | Lam of name * expr * expr * binder
  | Pi of name * expr * expr * binder
  | Let of name * expr * expr * expr * bool
  | Proj of name * Z.t * expr
  | NatLit of Z.t
  | StringLit of string
  | MData of expr
type safety = Safe | Partial | Unsafe
type hints = OpaqueHint | Abbrev | Regular of Z.t
type constant = { name : name; params : name list; typ : expr }
type definition = {
  header : constant; value : expr; safety : safety; hints : hints;
  all : name list
}
type inductive = {
  ind_header : constant; ind_num_params : Z.t; num_indices : Z.t;
  ind_all : name list; constructors : name list; num_nested : Z.t;
  is_rec : bool; ind_unsafe : bool; is_reflexive : bool
}
type constructor = {
  ctor_header : constant; induct : name; cidx : Z.t;
  ctor_num_params : Z.t; num_fields : Z.t; ctor_unsafe : bool
}
type rule = { ctor : name; nfields : Z.t; rhs : expr }
type recursor = {
  rec_header : constant; rec_all : name list; rec_num_params : Z.t;
  rec_num_indices : Z.t; num_motives : Z.t; num_minors : Z.t;
  rules : rule list; k : bool; rec_unsafe : bool
}
type quotient_kind = QuotType | QuotCtor | QuotLift | QuotInd
type declaration =
  | Axiom of constant * bool
  | Definition of definition
  | Theorem of constant * expr * name list
  | Opaque of constant * expr * bool * name list
  | Quotient of constant * quotient_kind
  | Inductive of inductive list * constructor list * recursor list
type metadata = { format_version : string; lean_version : string; lean_hash : string }
type export = {
  metadata : metadata; declarations : (int * declaration) list;
  name_count : int; level_count : int; expr_count : int
}
type error_kind = Malformed | Unsupported | Resource
type error = { line : int; kind : error_kind; message : string }
exception Error of error

let fail line kind message = raise (Error { line; kind; message })
let bad line message = fail line Malformed message

(* Yojson preserves string bytes. Reject invalid Unicode rather than allowing
   adapters to interpret the same byte string differently. *)
let valid_utf8 s =
  let len = String.length s in
  let byte i = Char.code s.[i] in
  let cont i = i < len && byte i >= 0x80 && byte i <= 0xbf in
  let rec loop i =
    if i = len then true else
    let a = byte i in
    if a < 0x80 then loop (i + 1)
    else if a >= 0xc2 && a <= 0xdf then
      cont (i + 1) && loop (i + 2)
    else if a >= 0xe0 && a <= 0xef then
      cont (i + 1) && cont (i + 2) &&
      (a <> 0xe0 || byte (i + 1) >= 0xa0) &&
      (a <> 0xed || byte (i + 1) <= 0x9f) && loop (i + 3)
    else if a >= 0xf0 && a <= 0xf4 then
      cont (i + 1) && cont (i + 2) && cont (i + 3) &&
      (a <> 0xf0 || byte (i + 1) >= 0x90) &&
      (a <> 0xf4 || byte (i + 1) <= 0x8f) && loop (i + 4)
    else false
  in loop 0

let rec validate_json line = function
  | `Assoc fields ->
    let seen = Hashtbl.create (List.length fields) in
    List.iter (fun (key, value) ->
      if not (valid_utf8 key) then bad line "invalid UTF-8 object key";
      if Hashtbl.mem seen key then bad line ("duplicate JSON field: " ^ key);
      Hashtbl.add seen key ();
      validate_json line value) fields
  | `List xs -> List.iter (validate_json line) xs
  | `String s -> if not (valid_utf8 s) then bad line "invalid UTF-8 string"
  | `Tuple _ | `Variant _ -> bad line "non-standard JSON syntax"
  | `Null | `Bool _ | `Int _ | `Intlit _ | `Float _ -> ()

let obj line = function `Assoc xs -> xs | _ -> bad line "expected object"
let field line key value =
  match List.assoc_opt key (obj line value) with
  | Some v -> v | None -> bad line ("missing field: " ^ key)
let text line = function `String s -> s | _ -> bad line "expected string"
let bool line = function `Bool b -> b | _ -> bad line "expected boolean"
let list line = function `List xs -> xs | _ -> bad line "expected array"
let natural line = function
  | `Int i when i >= 0 -> Z.of_int i
  | `Intlit s ->
    (try let n = Z.of_string s in
      if Z.sign n < 0 then bad line "negative natural number";
      n
     with Invalid_argument _ -> bad line "invalid integer")
  | _ -> bad line "expected nonnegative integer"
let decimal line s =
  if String.length s = 0 ||
     not (String.for_all (fun c -> c >= '0' && c <= '9') s)
  then bad line "invalid decimal natural literal";
  try Z.of_string s with Invalid_argument _ -> bad line "invalid natural literal"
let table_id line v =
  let n = natural line v in
  if not (Z.fits_int n) then fail line Resource "table identifier exceeds native address range";
  Z.to_int n
let find line what table value =
  let id = table_id line value in
  match Hashtbl.find_opt table id with
  | Some x -> x
  | None -> bad line ("undefined or forward " ^ what ^ " reference: " ^ string_of_int id)
let add line what table value x =
  let id = table_id line value in
  if Hashtbl.mem table id then bad line ("duplicate " ^ what ^ " identifier");
  Hashtbl.add table id x
let binder line = function
  | `String "default" -> Explicit | `String "implicit" -> Implicit
  | `String "strictImplicit" -> StrictImplicit | `String "instImplicit" -> InstanceImplicit
  | _ -> bad line "invalid binderInfo"
let safety line = function
  | `String "safe" -> Safe | `String "partial" -> Partial | `String "unsafe" -> Unsafe
  | _ -> bad line "invalid declaration safety"
let hints line = function
  | `String "opaque" -> OpaqueHint | `String "abbrev" -> Abbrev
  | `Assoc ["regular", n] -> Regular (natural line n)
  | _ -> bad line "invalid reducibility hints"

let read_channel ic =
  let names = Hashtbl.create 1024 and levels = Hashtbl.create 1024 in
  let exprs = Hashtbl.create 8192 in
  Hashtbl.add names 0 Anonymous;
  Hashtbl.add levels 0 Zero;
  let meta = ref None and decls = ref [] and lineno = ref 0 in
  let parse_line source =
    let line = !lineno in
    let json = try Yojson.Safe.from_string source
      with Yojson.Json_error message -> bad line ("invalid JSON: " ^ message) in
    validate_json line json;
    let f = field line in
    let name = find line "name" names and level = find line "level" levels in
    let expr = find line "expression" exprs in
    let ns j = List.map name (list line j) in
    let header v = {
      name = name (f "name" v); params = ns (f "levelParams" v);
      typ = expr (f "type" v)
    } in
    let z key v = natural line (f key v) in
    let b key v = bool line (f key v) in
    let ind v = {
      ind_header = header v; ind_num_params = z "numParams" v;
      num_indices = z "numIndices" v; ind_all = ns (f "all" v);
      constructors = ns (f "ctors" v); num_nested = z "numNested" v;
      is_rec = b "isRec" v; ind_unsafe = b "isUnsafe" v;
      is_reflexive = b "isReflexive" v
    } in
    let ctor v = {
      ctor_header = header v; induct = name (f "induct" v); cidx = z "cidx" v;
      ctor_num_params = z "numParams" v; num_fields = z "numFields" v;
      ctor_unsafe = b "isUnsafe" v
    } in
    let rule v = {
      ctor = name (f "ctor" v); nfields = z "nfields" v; rhs = expr (f "rhs" v)
    } in
    let recursor v = {
      rec_header = header v; rec_all = ns (f "all" v);
      rec_num_params = z "numParams" v; rec_num_indices = z "numIndices" v;
      num_motives = z "numMotives" v; num_minors = z "numMinors" v;
      rules = List.map rule (list line (f "rules" v)); k = b "k" v;
      rec_unsafe = b "isUnsafe" v
    } in
    let fields = obj line json in
    let tags = List.filter (fun (key, _) -> key <> "in" && key <> "il" && key <> "ie") fields in
    let tag, v = match tags with [pair] -> pair | _ -> bad line "expected one record tag" in
    if tag <> "meta" && !meta = None then bad line "missing initial metadata";
    let decl d =
      if List.length fields <> 1 then bad line "unexpected declaration fields";
      decls := (line, d) :: !decls
    in
    let node what key table x =
      if List.length fields <> 2 then bad line "unexpected node fields";
      add line what table (f key json) x
    in
    match tag with
    | "meta" ->
      if !meta <> None || line <> 1 || List.length fields <> 1 then
        bad line "metadata must occur exactly once at the beginning";
      let format_version = text line (f "version" (f "format" v)) in
      if format_version <> "3.1.0" then
        fail line Unsupported ("unsupported export format: " ^ format_version);
      meta := Some {
        format_version; lean_version = text line (f "version" (f "lean" v));
        lean_hash = text line (f "githash" (f "lean" v))
      }
    | "str" -> node "name" "in" names (Str (name (f "pre" v), text line (f "str" v)))
    | "num" -> node "name" "in" names (Num (name (f "pre" v), z "i" v))
    | "succ" -> node "level" "il" levels (Succ (level v))
    | "max" | "imax" ->
      let a, b = match list line v with [a; b] -> level a, level b
        | _ -> bad line "max/imax requires two arguments" in
      node "level" "il" levels (if tag = "max" then Max (a,b) else IMax (a,b))
    | "param" -> node "level" "il" levels (Param (name v))
    | "bvar" -> node "expression" "ie" exprs (BVar (natural line v))
    | "sort" -> node "expression" "ie" exprs (Sort (level v))
    | "const" -> node "expression" "ie" exprs
      (Const (name (f "name" v), List.map level (list line (f "us" v))))
    | "app" -> node "expression" "ie" exprs (App (expr (f "fn" v), expr (f "arg" v)))
    | "lam" | "forallE" ->
      let n = name (f "name" v) and t = expr (f "type" v) in
      let body = expr (f "body" v) and bi = binder line (f "binderInfo" v) in
      node "expression" "ie" exprs (if tag = "lam" then Lam (n,t,body,bi) else Pi (n,t,body,bi))
    | "letE" -> node "expression" "ie" exprs
      (Let (name (f "name" v), expr (f "type" v), expr (f "value" v),
            expr (f "body" v), b "nondep" v))
    | "proj" -> node "expression" "ie" exprs
      (Proj (name (f "typeName" v), z "idx" v, expr (f "struct" v)))
    | "natVal" -> node "expression" "ie" exprs (NatLit (decimal line (text line v)))
    | "strVal" -> node "expression" "ie" exprs (StringLit (text line v))
    | "mdata" ->
      ignore (obj line (f "data" v));
      node "expression" "ie" exprs (MData (expr (f "expr" v)))
    | "axiom" -> decl (Axiom (header v, b "isUnsafe" v))
    | "def" -> decl (Definition {
        header = header v; value = expr (f "value" v);
        safety = safety line (f "safety" v); hints = hints line (f "hints" v);
        all = ns (f "all" v) })
    | "thm" -> decl (Theorem (header v, expr (f "value" v), ns (f "all" v)))
    | "opaque" -> decl (Opaque (header v, expr (f "value" v), b "isUnsafe" v, ns (f "all" v)))
    | "quot" ->
      let kind = match text line (f "kind" v) with
        | "type" -> QuotType | "ctor" -> QuotCtor | "lift" -> QuotLift | "ind" -> QuotInd
        | _ -> bad line "invalid quotient kind" in
      decl (Quotient (header v, kind))
    | "inductive" -> decl (Inductive (
        List.map ind (list line (f "types" v)),
        List.map ctor (list line (f "ctors" v)),
        List.map recursor (list line (f "recs" v))))
    | _ -> bad line ("unknown record tag: " ^ tag)
  in
  try
    (try while true do
      let source = input_line ic in
      incr lineno;
      parse_line source
    done with End_of_file -> ());
    let metadata = match !meta with Some m -> m | None -> bad 0 "empty export" in
    { metadata; declarations = List.rev !decls;
      name_count = Hashtbl.length names; level_count = Hashtbl.length levels;
      expr_count = Hashtbl.length exprs }
  with
  | Stack_overflow -> fail !lineno Resource "parser stack exhausted"
  | Out_of_memory -> fail !lineno Resource "parser memory exhausted"

let read_file path =
  if path = "-" then read_channel stdin else
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> read_channel ic)

let error_exit_code = function
  | { kind = Malformed; _ } -> 1
  | { kind = Unsupported | Resource; _ } -> 2

let rec equal_name a b = match a, b with
  | Anonymous, Anonymous -> true
  | Str (p,s), Str (q,t) -> s = t && equal_name p q
  | Num (p,n), Num (q,m) -> Z.equal n m && equal_name p q
  | _ -> false

let dotted_name segments = List.fold_left (fun n s -> Str (n,s)) Anonymous segments
