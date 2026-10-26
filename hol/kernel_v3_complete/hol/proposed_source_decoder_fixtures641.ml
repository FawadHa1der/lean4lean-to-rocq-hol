(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Fixture SOURCE DRAFTS only: UNCOMPILED / NOT RUN / no HOL proof claim.
   Explicit invocation would perform temporary source-file I/O; this file
   defines the function but NEVER invokes it. Genuine Wire and610 are prerequisites. *)
needs "hol/source_decoder641.ml";;
unset_jrh_lexer;;

let proposed_source_decoder_fixtures641 () =
  let scratch = Sys.getenv "LEAN4LEAN_FIXTURE_TMPDIR" in
  if Filename.is_relative scratch then failwith "641: absolute owned scratch path required";
  let check label b = if not b then failwith ("641: " ^ label) in
  let with_source text f =
    let path, oc = Filename.open_temp_file
      ~temp_dir:scratch "fixture641-" ".ndjson" in
    Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
      Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () ->
        output_string oc text; flush oc);
      f path)
  in
  let parse text = with_source text Source_decoder641.read_file in
  let meta =
    "{\"meta\":{\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"version\":\"fixture\",\"githash\":\"source641\"}}}" ^ "\n" in
  let sort = "{\"ie\":0,\"sort\":0}" ^ "\n" in
  let expect_error label kind line input =
    let observed =
      try ignore (parse input); None with Wire.Error e -> Some e
    in
    match observed with
    | None -> failwith ("641 accepted error fixture: " ^ label)
    | Some e ->
        check (label ^ ": kind") (e.kind = kind);
        check (label ^ ": line") (e.line = line);
        check (label ^ ": nonempty error") (e.message <> "");
        check (label ^ ": exit class")
          (Wire.error_exit_code e = (if kind = Wire.Malformed then 1 else 2))
  in
  let empty = parse meta in
  check "metadata retained" (empty.metadata.format_version = "3.1.0" &&
    empty.metadata.lean_version = "fixture" && empty.metadata.lean_hash = "source641");
  check "implicit tables only" (empty.name_count = 1 && empty.level_count = 1 &&
    empty.expr_count = 0 && empty.declarations = []);
  let huge = "18446744073709551617" in
  let rows = [
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A.with.dot\"}}";
    "{\"in\":2,\"num\":{\"pre\":1,\"i\":18446744073709551617}}";
    "{\"il\":1,\"succ\":0}";
    "{\"il\":2,\"param\":2}";
    "{\"il\":3,\"max\":[1,2]}";
    "{\"il\":4,\"imax\":[3,0]}";
    "{\"ie\":0,\"sort\":4}";
    "{\"ie\":1,\"bvar\":18446744073709551617}";
    "{\"ie\":2,\"const\":{\"name\":2,\"us\":[4,1]}}";
    "{\"ie\":3,\"app\":{\"fn\":2,\"arg\":1}}";
    "{\"ie\":4,\"lam\":{\"name\":2,\"type\":0,\"body\":1,\"binderInfo\":\"strictImplicit\"}}";
    "{\"ie\":5,\"forallE\":{\"name\":2,\"type\":0,\"body\":1,\"binderInfo\":\"instImplicit\"}}";
    "{\"ie\":6,\"letE\":{\"name\":2,\"type\":0,\"value\":3,\"body\":1,\"nondep\":true}}";
    "{\"ie\":7,\"natVal\":\"18446744073709551617\"}";
    "{\"ie\":8,\"strVal\":\"\\u0000\\u00e9\"}";
    "{\"ie\":9,\"proj\":{\"typeName\":2,\"idx\":18446744073709551617,\"struct\":3}}";
    "{\"ie\":10,\"mdata\":{\"expr\":9,\"data\":{}}}";
    "{\"axiom\":{\"name\":1,\"levelParams\":[2,1,2],\"type\":4,\"isUnsafe\":true}}";
    "{\"def\":{\"name\":2,\"levelParams\":[1],\"type\":5,\"value\":6,\"safety\":\"partial\",\"hints\":{\"regular\":18446744073709551617},\"all\":[1,2,1]}}";
    "{\"thm\":{\"name\":1,\"levelParams\":[],\"type\":0,\"value\":7,\"all\":[2,1]}}";
    "{\"opaque\":{\"name\":2,\"levelParams\":[1],\"type\":0,\"value\":8,\"isUnsafe\":true,\"all\":[2,2]}}";
    "{\"quot\":{\"name\":1,\"levelParams\":[],\"type\":0,\"kind\":\"lift\"}}";
    "{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[2],\"type\":0,\"numParams\":2,\"numIndices\":3,\"all\":[1,2,1],\"ctors\":[2,1],\"numNested\":5,\"isRec\":true,\"isUnsafe\":true,\"isReflexive\":false}],\"ctors\":[{\"name\":2,\"levelParams\":[1],\"type\":10,\"induct\":1,\"cidx\":7,\"numParams\":11,\"numFields\":13,\"isUnsafe\":true}],\"recs\":[{\"name\":1,\"levelParams\":[2,2],\"type\":0,\"all\":[2,1,2],\"numParams\":17,\"numIndices\":19,\"numMotives\":23,\"numMinors\":29,\"rules\":[{\"ctor\":2,\"nfields\":31,\"rhs\":1},{\"ctor\":2,\"nfields\":37,\"rhs\":10}],\"k\":true,\"isUnsafe\":false}]}}"
  ] in
  (* Transport-only data is deliberately not claimed to be a well-typed block. *)
  let full = meta ^ String.concat "\n" rows ^ "\n" in
  let exported = parse full in
  let a = Wire.Str (Wire.Anonymous,"A.with.dot") in
  let n = Wire.Num (a,Z.of_string huge) in
  let u = Wire.IMax (Wire.Max (Wire.Succ Wire.Zero,Wire.Param n),Wire.Zero) in
  let ty = Wire.Sort u and variable = Wire.BVar (Z.of_string huge) in
  let fn = Wire.Const (n,[u;Wire.Succ Wire.Zero]) in
  let app = Wire.App (fn,variable) in
  let wrapped = Wire.MData (Wire.Proj (n,Z.of_string huge,app)) in
  check "all physical lines retained" (List.map fst exported.declarations = [19;20;21;22;23;24]);
  check "all table nodes counted" (exported.name_count=3 && exported.level_count=5 &&
    exported.expr_count=11);
  (match List.map snd exported.declarations with
   | [Wire.Axiom (h,true); Wire.Definition d; Wire.Theorem (th,tv,ta);
      Wire.Opaque (oh,ov,true,oa); Wire.Quotient (qh,Wire.QuotLift);
      Wire.Inductive ([i],[c],[r])] ->
       check "axiom header and binder" (h.name=a && h.params=[n;a;n] &&
         h.typ=Wire.Lam (n,ty,variable,Wire.StrictImplicit));
       check "definition fields" (d.header.name=n && d.header.params=[a] &&
         d.header.typ=Wire.Pi (n,ty,variable,Wire.InstanceImplicit) &&
         d.value=Wire.Let (n,ty,app,variable,true) && d.safety=Wire.Partial &&
         d.hints=Wire.Regular (Z.of_string huge) && d.all=[a;n;a]);
       check "theorem fields" (th.name=a && th.params=[] && th.typ=ty &&
         tv=Wire.NatLit (Z.of_string huge) && ta=[n;a]);
       check "opaque string bytes" (oh.name=n && oh.params=[a] && oh.typ=ty &&
         ov=Wire.StringLit "\000\195\169" && oa=[n;n]);
       check "quotient header" (qh.name=a && qh.params=[] && qh.typ=ty);
       check "inductive fields" (i.ind_header.name=a && i.ind_header.params=[n] &&
         i.ind_header.typ=ty && Z.equal i.ind_num_params (Z.of_int 2) &&
         Z.equal i.num_indices (Z.of_int 3) && i.ind_all=[a;n;a] &&
         i.constructors=[n;a] && Z.equal i.num_nested (Z.of_int 5) &&
         i.is_rec && i.ind_unsafe && not i.is_reflexive);
       check "constructor fields and metadata wrapper" (c.ctor_header.name=n &&
         c.ctor_header.params=[a] && c.ctor_header.typ=wrapped && c.induct=a &&
         Z.equal c.cidx (Z.of_int 7) && Z.equal c.ctor_num_params (Z.of_int 11) &&
         Z.equal c.num_fields (Z.of_int 13) && c.ctor_unsafe);
       check "recursor fields" (r.rec_header.name=a && r.rec_header.params=[n;n] &&
         r.rec_header.typ=ty && r.rec_all=[n;a;n] &&
         Z.equal r.rec_num_params (Z.of_int 17) && Z.equal r.rec_num_indices (Z.of_int 19) &&
         Z.equal r.num_motives (Z.of_int 23) && Z.equal r.num_minors (Z.of_int 29) &&
         r.k && not r.rec_unsafe);
       (match r.rules with
        | [r1;r2] -> check "rule order and duplicate constructors"
            (r1.ctor=n && Z.equal r1.nfields (Z.of_int 31) && r1.rhs=variable &&
             r2.ctor=n && Z.equal r2.nfields (Z.of_int 37) && r2.rhs=wrapped)
        | _ -> failwith "641: rule list")
   | _ -> failwith "641: declaration partition/order");
  check "last line without newline retained"
    ((parse (meta ^ "{\"ie\":0,\"sort\":0}")).expr_count=1);
  with_source full (fun path ->
    let ic = open_in_bin path in
    Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
      let same = Source_decoder641.read_channel ic in
      check "channel/file result identity" (same=exported);
      seek_in ic 0;
      check "caller channel remains open" (input_char ic='{')));
  List.iter (fun (label,kind,line,input) -> expect_error label kind line input) [
    "empty export", Wire.Malformed, 0, "";
    "missing initial metadata", Wire.Malformed, 1, sort;
    "duplicate metadata", Wire.Malformed, 2, meta ^ meta;
    "missing metadata field", Wire.Malformed, 1,
      "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}" ^ "\n";
    "complete unsupported format", Wire.Unsupported, 1,
      "{\"meta\":{\"format\":{\"version\":\"99\"},\"lean\":{\"version\":\"x\",\"githash\":\"y\"}}}" ^ "\n";
    "extra exporter is not erased", Wire.Unsupported, 1,
      "{\"meta\":{\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"version\":\"x\",\"githash\":\"y\"},\"exporter\":{\"name\":\"test\"}}}" ^ "\n";
    "unsupported decoder tag", Wire.Unsupported, 2, meta ^ "{\"ie\":0,\"fvar\":0}" ^ "\n";
    "unknown field before undefined references", Wire.Unsupported, 2,
      meta ^ "{\"ie\":0,\"app\":{\"fn\":99,\"arg\":98,\"extra\":true}}" ^ "\n";
    "nonempty metadata before undefined reference", Wire.Unsupported, 2,
      meta ^ "{\"ie\":0,\"mdata\":{\"expr\":99,\"data\":{\"x\":1}}}" ^ "\n";
    "duplicate top-level key", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"ie\":1,\"sort\":0}" ^ "\n";
    "duplicate nested key", Wire.Malformed, 2,
      meta ^ "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"x\",\"str\":\"y\"}}" ^ "\n";
    "duplicates precede unsupported metadata", Wire.Malformed, 2,
      meta ^ "{\"ie\":0,\"mdata\":{\"expr\":99,\"data\":{\"x\":1,\"x\":2}}}" ^ "\n";
    "missing binder field", Wire.Malformed, 2,
      meta ^ "{\"ie\":0,\"lam\":{\"name\":0,\"type\":99,\"body\":99}}" ^ "\n";
    "negative index", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"bvar\":-1}" ^ "\n";
    "floating index", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"bvar\":1.0}" ^ "\n";
    "oversized table id", Wire.Resource, 2,
      meta ^ "{\"ie\":999999999999999999999999999999,\"sort\":0}" ^ "\n";
    "undefined level", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"sort\":1}" ^ "\n";
    "forward expression", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"app\":{\"fn\":0,\"arg\":1}}" ^ "\n";
    "duplicate expression id", Wire.Malformed, 3, meta ^ sort ^ sort;
    "shadow anonymous name", Wire.Malformed, 2,
      meta ^ "{\"in\":0,\"str\":{\"pre\":0,\"str\":\"x\"}}" ^ "\n";
    "shadow zero level", Wire.Malformed, 2, meta ^ "{\"il\":0,\"succ\":0}" ^ "\n";
    "nondecimal literal", Wire.Malformed, 2, meta ^ "{\"ie\":0,\"natVal\":\"0xff\"}" ^ "\n";
    "invalid JSON", Wire.Malformed, 2, meta ^ "{\n";
    "blank physical line", Wire.Malformed, 2, meta ^ "\n";
    "two JSON records on one line", Wire.Malformed, 2,
      meta ^ "{\"ie\":0,\"sort\":0} {\"ie\":1,\"sort\":0}" ^ "\n";
    "late preflight failure forbids prefix return", Wire.Unsupported, 3,
      meta ^ sort ^ "{\"ie\":1,\"mdata\":{\"expr\":0,\"data\":{\"late\":true}}}" ^ "\n";
    "malformed metadata payload", Wire.Malformed, 3,
      meta ^ sort ^ "{\"ie\":1,\"mdata\":{\"expr\":0,\"data\":[]}}" ^ "\n";
    "invalid UTF-8", Wire.Malformed, 2,
      meta ^ "{\"ie\":0,\"strVal\":\"\192\128\"}\n";
    "unknown constructor field", Wire.Unsupported, 2,
      meta ^ "{\"inductive\":{\"types\":[],\"ctors\":[{\"name\":0,\"levelParams\":[],\"type\":99,\"induct\":0,\"cidx\":0,\"numParams\":0,\"numFields\":0,\"isUnsafe\":false,\"extra\":true}],\"recs\":[]}}" ^ "\n";
    "unknown recursor rule field", Wire.Unsupported, 2,
      meta ^ "{\"inductive\":{\"types\":[],\"ctors\":[],\"recs\":[{\"name\":0,\"levelParams\":[],\"type\":99,\"all\":[],\"numParams\":0,\"numIndices\":0,\"numMotives\":0,\"numMinors\":0,\"rules\":[{\"ctor\":0,\"nfields\":0,\"rhs\":99,\"extra\":true}],\"k\":false,\"isUnsafe\":false}]}}" ^ "\n"
  ];
  ()
;;

set_jrh_lexer;;
