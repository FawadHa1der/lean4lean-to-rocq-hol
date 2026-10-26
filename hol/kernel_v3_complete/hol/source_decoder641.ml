(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed reader-only adaptation of frontend/wire.ml143-271.
   SOURCE ONLY / UNCOMPILED / UNEXECUTED. See ../CONTRACT641.txt.
   Genuine Wire/Zarith/Yojson and Full_input610 must already be loaded.
   Quotation and logical admission are separate; no binary or source loader. *)
unset_jrh_lexer;;

module Source_decoder641 : sig
  val read_channel : in_channel -> Wire.export
  val read_file : string -> Wire.export
end = struct
  open Wire

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
      (try Full_input610.preflight_record line json with
       | Full_input610.Unsupported_decoder message -> fail line Unsupported message);
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
end;;

set_jrh_lexer;;
