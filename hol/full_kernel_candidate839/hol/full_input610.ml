(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED. See ../CONTRACT610.txt and ../NOTICE610.txt.
   Requires the genuine Wire module and its dependencies already available.
   No checker invocation, admission, primitive classification or file I/O. *)
needs "hol/kernel_declarations493.ml";;

(* Wire.BVar, Wire.IMax and Z require ordinary OCaml identifier lexing. *)
unset_jrh_lexer;;

module Full_input610 = struct
  exception Invalid_input of string
  exception Unsupported_decoder of string

  let node tag args = list_mk_comb (mk_const (tag,[]),args)
  let list ty xs = mk_list (xs,parse_type ty)
  let bool b = node (if b then "T" else "F") []
  let natural n =
    if Z.sign n < 0 then raise (Invalid_input "negative natural");
    mk_numeral (num_of_string (Z.to_string n))

  (* Both names and full447 string literals contain bytes, not Unicode scalars. *)
  let bytes s =
    if not (Wire.valid_utf8 s) then raise (Invalid_input "invalid UTF-8");
    list "num" (List.init (String.length s)
      (fun i -> mk_small_numeral (Char.code s.[i])))

  let rec name = function
    | Wire.Anonymous -> node "L4Anonymous" []
    | Wire.Str (p,s) -> node "L4String" [name p;bytes s]
    | Wire.Num (p,n) -> node "L4Numeric" [name p;natural n]
  let names ns = list "l4_name" (List.map name ns)

  let rec level = function
    | Wire.Zero -> node "L4KZero447" []
    | Wire.Succ u -> node "L4KSucc447" [level u]
    | Wire.Max (u,v) -> node "L4KMax447" [level u;level v]
    | Wire.IMax (u,v) -> node "L4KIMax447" [level u;level v]
    | Wire.Param n -> node "L4KParam447" [name n]
  let levels us = list "l4_klevel447" (List.map level us)
  let binder b = node (match b with
    | Wire.Explicit -> "L4KDefault447"
    | Wire.Implicit -> "L4KImplicit447"
    | Wire.StrictImplicit -> "L4KStrictImplicit447"
    | Wire.InstanceImplicit -> "L4KInstImplicit447") []

  (* Physical keys preserve a shared Wire DAG without treating hashes as equality.
     The caller owns this per-quotation cache; it is not a source verdict cache. *)
  module Exprs = Hashtbl.Make(struct
    type t = Wire.expr
    let equal a b = a == b
    let hash = Hashtbl.hash
  end)
  let create () = Exprs.create 127
  let rec expr memo e = match Exprs.find_opt memo e with
    | Some tm -> tm
    | None ->
      let tm = match e with
        | Wire.BVar i -> node "L4KBVar447" [natural i]
        | Wire.Sort u -> node "L4KSort447" [level u]
        | Wire.Const (n,us) -> node "L4KConst447" [name n;levels us]
        | Wire.App (f,a) -> node "L4KApp447" [expr memo f;expr memo a]
        | Wire.Lam (n,a,b,bi) ->
          node "L4KLam447" [name n;binder bi;expr memo a;expr memo b]
        | Wire.Pi (n,a,b,bi) ->
          node "L4KPi447" [name n;binder bi;expr memo a;expr memo b]
        | Wire.Let (n,a,v,b,nd) ->
          node "L4KLet447" [name n;expr memo a;expr memo v;expr memo b;bool nd]
        | Wire.Proj (n,i,a) -> node "L4KProj447" [name n;natural i;expr memo a]
        | Wire.NatLit n -> node "L4KNatLit447" [natural n]
        | Wire.StringLit s -> node "L4KStrLit447" [bytes s]
        | Wire.MData a -> node "L4KMData447" [expr memo a] in
      Exprs.add memo e tm; tm

  (* These constructors have no Wire decoder cases. These are explicit quotation
     APIs for a supplied name, never a claim that a serialized node was decoded. *)
  let fvar n = node "L4KFVar447" [name n]
  let mvar n = node "L4KMVar447" [name n]
  let level_mvar n = node "L4KLevelMVar447" [name n]

  let hints = function
    | Wire.OpaqueHint -> node "L4KHintOpaque493" []
    | Wire.Abbrev -> node "L4KHintAbbrev493" []
    | Wire.Regular n -> node "L4KHintRegular493" [natural n]
  let quotient = function
    | Wire.QuotType -> node "L4KQType493" []
    | Wire.QuotCtor -> node "L4KQCtor493" []
    | Wire.QuotLift -> node "L4KQLift493" []
    | Wire.QuotInd -> node "L4KQInd493" []

  type header = { qname : term; qparams : term; qtype : term }
  let header memo (h:Wire.constant) =
    {qname=name h.name; qparams=names h.params; qtype=expr memo h.typ}

  let inductive_data (i:Wire.inductive) = node "L4KInductiveData493"
    [natural i.ind_num_params; natural i.num_indices; names i.ind_all;
     names i.constructors; natural i.num_nested; bool i.is_rec;
     bool i.is_reflexive; bool i.ind_unsafe]
  let constructor_data (c:Wire.constructor) = node "L4KConstructorData493"
    [name c.induct; natural c.cidx; natural c.ctor_num_params;
     natural c.num_fields; bool c.ctor_unsafe]
  let rule memo (r:Wire.rule) = node "L4KRecursorRule493"
    [name r.ctor; natural r.nfields; expr memo r.rhs]
  let recursor_data memo (r:Wire.recursor) = node "L4KRecursorData493"
    [names r.rec_all; natural r.rec_num_params; natural r.rec_num_indices;
     natural r.num_motives; natural r.num_minors;
     list "l4_krecursor_rule493" (List.map (rule memo) r.rules);
     bool r.k; bool r.rec_unsafe]

  (* Only raw inductive claims are packaged as493 declarations. Ordinary input
     safety and scheduling metadata must not be guessed from raw decl kinds. *)
  let raw_claim memo h kind =
    let q = header memo h in
    let none = parse_term "NONE:l4_kexpr447 option" in
    node "L4KDeclaration493"
      [q.qname; q.qparams; q.qtype; none; kind; hints Wire.OpaqueHint]
  let inductive memo (i:Wire.inductive) =
    raw_claim memo i.ind_header (node "L4KDInductive493" [inductive_data i])
  let constructor memo (c:Wire.constructor) =
    raw_claim memo c.ctor_header (node "L4KDConstructor493" [constructor_data c])
  let recursor memo (r:Wire.recursor) =
    raw_claim memo r.rec_header (node "L4KDRecursor493" [recursor_data memo r])

  (* Host transport envelopes, not HOL datatypes or admission results. Every term
     payload uses the actual447/493 type; all/safety remain explicit. *)
  type definition = {
    qheader : header; qvalue : term; qsafety : Wire.safety;
    qhints : term; qall : term
  }
  type declaration =
    | Axiom of header * bool
    | Definition of definition
    | Theorem of header * term * term
    | Opaque of header * term * bool * term
    | Quotient of header * term
    | Inductive of term list * term list * term list
  let definition memo (d:Wire.definition) =
    {qheader=header memo d.header; qvalue=expr memo d.value;
     qsafety=d.safety; qhints=hints d.hints; qall=names d.all}
  let declaration memo = function
    | Wire.Axiom (h,unsafe) -> Axiom (header memo h,unsafe)
    | Wire.Definition d -> Definition (definition memo d)
    | Wire.Theorem (h,v,all) -> Theorem (header memo h,expr memo v,names all)
    | Wire.Opaque (h,v,unsafe,all) -> Opaque (header memo h,expr memo v,unsafe,names all)
    | Wire.Quotient (h,k) -> Quotient (header memo h,quotient k)
    | Wire.Inductive (inds,ctors,recs) -> Inductive
      (List.map (inductive memo) inds,List.map (constructor memo) ctors,
       List.map (recursor memo) recs)

  type export = {
    qmetadata : Wire.metadata; qdeclarations : (int * declaration) list;
    qname_count : int; qlevel_count : int; qexpr_count : int
  }
  let export (e:Wire.export) =
    if e.metadata.format_version <> "3.1.0" then
      raise (Unsupported_decoder "export format is not 3.1.0");
    let memo = create () in
    {qmetadata=e.metadata;
     qdeclarations=List.map (fun (line,d) -> line,declaration memo d) e.declarations;
     qname_count=e.name_count; qlevel_count=e.level_count; qexpr_count=e.expr_count}

  (* Pre-decode loss screen, not a decoder or a file-checking entry point.
     A future caller must bind these original JSON records to the SAME bytes
     decoded by Wire; applying this to an already decoded export is too late. *)
  let preflight_record line json =
    Wire.validate_json line json;
    let exact label keys j =
      let fields = Wire.obj line j in
      List.iter (fun (key,_) -> if not (List.mem key keys) then
        raise (Unsupported_decoder (label ^ ": unsupported field " ^ key))) fields;
      List.iter (fun key -> ignore (Wire.field line key j)) keys in
    let f = Wire.field line in
    let header_keys = ["name";"levelParams";"type"] in
    let fields = Wire.obj line json in
    let tags = List.filter
      (fun (k,_) -> k <> "in" && k <> "il" && k <> "ie") fields in
    let tag,v = match tags with
      | [pair] -> pair | _ -> Wire.bad line "expected one record tag" in
    let node id keys = exact "record" [id;tag] json; exact tag keys v in
    let scalar_node id = exact "record" [id;tag] json in
    let decl keys = exact "record" [tag] json; exact tag keys v in
    match tag with
    | "meta" ->
      decl ["format";"lean"];
      exact "format" ["version"] (f "format" v);
      exact "lean" ["version";"githash"] (f "lean" v)
    | "str" -> node "in" ["pre";"str"]
    | "num" -> node "in" ["pre";"i"]
    | "succ" | "max" | "imax" | "param" -> scalar_node "il"
    | "bvar" | "sort" | "natVal" | "strVal" -> scalar_node "ie"
    | "const" -> node "ie" ["name";"us"]
    | "app" -> node "ie" ["fn";"arg"]
    | "lam" | "forallE" -> node "ie" ["name";"type";"body";"binderInfo"]
    | "letE" -> node "ie" ["name";"type";"value";"body";"nondep"]
    | "proj" -> node "ie" ["typeName";"idx";"struct"]
    | "mdata" ->
      node "ie" ["expr";"data"];
      if Wire.obj line (f "data" v) <> [] then
        raise (Unsupported_decoder "nonempty metadata payload cannot be retained by Wire/full447")
    | "axiom" -> decl (header_keys @ ["isUnsafe"])
    | "def" ->
      decl (header_keys @ ["value";"safety";"hints";"all"]);
      ignore (Wire.hints line (f "hints" v))
    | "thm" -> decl (header_keys @ ["value";"all"])
    | "opaque" -> decl (header_keys @ ["value";"isUnsafe";"all"])
    | "quot" -> decl (header_keys @ ["kind"])
    | "inductive" ->
      decl ["types";"ctors";"recs"];
      List.iter (exact "inductive type" (header_keys @
        ["numParams";"numIndices";"all";"ctors";"numNested";
         "isRec";"isUnsafe";"isReflexive"])) (Wire.list line (f "types" v));
      List.iter (exact "constructor" (header_keys @
        ["induct";"cidx";"numParams";"numFields";"isUnsafe"]))
        (Wire.list line (f "ctors" v));
      List.iter (fun r ->
        exact "recursor" (header_keys @ ["all";"numParams";"numIndices";
          "numMotives";"numMinors";"rules";"k";"isUnsafe"]) r;
        List.iter (exact "recursor rule" ["ctor";"nfields";"rhs"])
          (Wire.list line (f "rules" r))) (Wire.list line (f "recs" v))
    | _ -> raise (Unsupported_decoder ("unsupported decoder tag: " ^ tag))
end;;

set_jrh_lexer;;
