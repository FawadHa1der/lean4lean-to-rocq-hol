(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED / UNCOMPILED / UNEXECUTED. These are term-construction regressions,
   not HOL proofs, checker results, a native-load receipt or an acceptance test.
   Loading this file defines the function; it does not run the fixtures. *)
needs "hol/full_input610.ml";;
unset_jrh_lexer;;

let proposed_fixtures610 () =
  let module Q = Full_input610 in
  let memo = Q.create () in
  let n = Wire.Anonymous in
  let a = Wire.Sort Wire.Zero and b = Wire.BVar Z.zero in
  let huge = Z.of_string "18446744073709551617" in
  let expect label actual expected =
    if not (aconv actual (parse_term expected)) then failwith label in
  let check label p = if not p then failwith label in
  let invalid label f =
    let refused = try ignore (f ()); false with Q.Invalid_input _ -> true in
    check label refused in
  let unsupported label f =
    let refused = try ignore (f ()); false with Q.Unsupported_decoder _ -> true in
    check label refused in
  let preflight s = Q.preflight_record 1 (Yojson.Safe.from_string s) in
  expect "numeric names are not machine integers"
    (Q.name (Wire.Num (Wire.Str (n,"x"),huge)))
    "L4Numeric (L4String L4Anonymous [120]) 18446744073709551617";
  expect "name strings are UTF-8 bytes" (Q.name (Wire.Str (n,"\195\169")))
    "L4String L4Anonymous [195;169]";
  expect "all wire levels" (Q.level (Wire.IMax (Wire.Max
    (Wire.Zero,Wire.Succ Wire.Zero),Wire.Param n)))
    "L4KIMax447 (L4KMax447 L4KZero447 (L4KSucc447 L4KZero447)) (L4KParam447 L4Anonymous)";
  List.iter (fun (bi,tag) ->
    expect "lambda binder information" (Q.expr memo (Wire.Lam (n,a,b,bi)))
      ("L4KLam447 L4Anonymous " ^ tag ^ " (L4KSort447 L4KZero447) (L4KBVar447 0)");
    expect "Pi binder information" (Q.expr memo (Wire.Pi (n,a,b,bi)))
      ("L4KPi447 L4Anonymous " ^ tag ^ " (L4KSort447 L4KZero447) (L4KBVar447 0)"))
    [Wire.Explicit,"L4KDefault447"; Wire.Implicit,"L4KImplicit447";
     Wire.StrictImplicit,"L4KStrictImplicit447"; Wire.InstanceImplicit,"L4KInstImplicit447"];
  expect "let nonDep true" (Q.expr memo (Wire.Let (n,a,b,b,true)))
    "L4KLet447 L4Anonymous (L4KSort447 L4KZero447) (L4KBVar447 0) (L4KBVar447 0) T";
  expect "let nonDep false" (Q.expr memo (Wire.Let (n,a,b,b,false)))
    "L4KLet447 L4Anonymous (L4KSort447 L4KZero447) (L4KBVar447 0) (L4KBVar447 0) F";
  expect "nested metadata wrappers" (Q.expr memo (Wire.MData (Wire.MData b)))
    "L4KMData447 (L4KMData447 (L4KBVar447 0))";
  expect "string literal bytes, not decoded scalars"
    (Q.expr memo (Wire.StringLit "\000\195\169\240\159\152\128"))
    "L4KStrLit447 [0;195;169;240;159;152;128]";
  expect "empty string" (Q.expr memo (Wire.StringLit "")) "L4KStrLit447 []";
  expect "large BVar" (Q.expr memo (Wire.BVar huge)) "L4KBVar447 18446744073709551617";
  expect "large literal" (Q.expr memo (Wire.NatLit huge)) "L4KNatLit447 18446744073709551617";
  expect "large projection index" (Q.expr memo (Wire.Proj (n,huge,b)))
    "L4KProj447 L4Anonymous 18446744073709551617 (L4KBVar447 0)";
  expect "application/universe order"
    (Q.expr memo (Wire.App (Wire.Const (n,[Wire.Succ Wire.Zero;Wire.Zero]),b)))
    "L4KApp447 (L4KConst447 L4Anonymous [L4KSucc447 L4KZero447;L4KZero447]) (L4KBVar447 0)";
  expect "explicit free variable" (Q.fvar n) "L4KFVar447 L4Anonymous";
  expect "explicit expression metavariable" (Q.mvar n) "L4KMVar447 L4Anonymous";
  expect "explicit universe metavariable" (Q.level_mvar n) "L4KLevelMVar447 L4Anonymous";
  expect "opaque hints" (Q.hints Wire.OpaqueHint) "L4KHintOpaque493";
  expect "abbrev hints" (Q.hints Wire.Abbrev) "L4KHintAbbrev493";
  expect "unbounded regular height" (Q.hints (Wire.Regular huge))
    "L4KHintRegular493 18446744073709551617";
  List.iter (fun (k,expected) -> expect "quotient kind" (Q.quotient k) expected)
    [Wire.QuotType,"L4KQType493"; Wire.QuotCtor,"L4KQCtor493";
     Wire.QuotLift,"L4KQLift493"; Wire.QuotInd,"L4KQInd493"];
  let h : Wire.constant = {name=n;params=[n;n];typ=a} in
  List.iter (fun safety ->
    let d : Wire.definition = {header=h;value=b;safety;hints=Wire.Regular huge;all=[n;n]} in
    match Q.declaration memo (Wire.Definition d) with
    | Q.Definition q ->
      check "safety is not reclassified" (q.qsafety = safety);
      expect "definition all retains duplicates/order" q.qall "[L4Anonymous;L4Anonymous]";
      expect "header parameters retained" q.qheader.qparams "[L4Anonymous;L4Anonymous]";
      expect "definition hints retained" q.qhints "L4KHintRegular493 18446744073709551617"
    | _ -> failwith "definition role") [Wire.Safe;Wire.Partial;Wire.Unsafe];
  let i : Wire.inductive = {ind_header=h;ind_num_params=Z.of_int 2;
    num_indices=Z.of_int 3;ind_all=[n;n];constructors=[n];num_nested=Z.of_int 5;
    is_rec=true;ind_unsafe=true;is_reflexive=false} in
  expect "inductive metadata field order" (Q.inductive_data i)
    "L4KInductiveData493 2 3 [L4Anonymous;L4Anonymous] [L4Anonymous] 5 T F T";
  let c : Wire.constructor = {ctor_header=h;induct=n;cidx=Z.of_int 7;
    ctor_num_params=Z.of_int 11;num_fields=Z.of_int 13;ctor_unsafe=true} in
  expect "constructor metadata field order" (Q.constructor_data c)
    "L4KConstructorData493 L4Anonymous 7 11 13 T";
  let r1 : Wire.rule = {ctor=n;nfields=Z.of_int 17;rhs=b} in
  let r2 : Wire.rule = {ctor=n;nfields=Z.of_int 19;rhs=Wire.MData b} in
  let r : Wire.recursor = {rec_header=h;rec_all=[n;n];rec_num_params=Z.of_int 23;
    rec_num_indices=Z.of_int 29;num_motives=Z.of_int 31;num_minors=Z.of_int 37;
    rules=[r1;r2];k=false;rec_unsafe=true} in
  expect "recursor rules retain first-shadow order and all fields" (Q.recursor_data memo r)
    "L4KRecursorData493 [L4Anonymous;L4Anonymous] 23 29 31 37 [L4KRecursorRule493 L4Anonymous 17 (L4KBVar447 0);L4KRecursorRule493 L4Anonymous 19 (L4KMData447 (L4KBVar447 0))] F T";
  expect "raw claim has NONE value and opaque hint" (Q.constructor memo c)
    "L4KDeclaration493 L4Anonymous [L4Anonymous;L4Anonymous] (L4KSort447 L4KZero447) NONE (L4KDConstructor493 (L4KConstructorData493 L4Anonymous 7 11 13 T)) L4KHintOpaque493";
  let metadata : Wire.metadata = {format_version="3.1.0";lean_version="fixture";lean_hash="fixture"} in
  let input : Wire.export = {metadata;name_count=4;level_count=5;expr_count=6;
    declarations=[10,Wire.Axiom (h,true);11,Wire.Theorem (h,b,[n;n]);
      12,Wire.Opaque (h,b,true,[n;n]);13,Wire.Quotient (h,Wire.QuotLift);
      14,Wire.Inductive ([i;i],[c],[r;r])]} in
  let q = Q.export input in
  check "export identity fields" (q.qmetadata=metadata && q.qname_count=4 &&
    q.qlevel_count=5 && q.qexpr_count=6);
  check "all rows and source lines, no scheduling" (List.map fst q.qdeclarations=[10;11;12;13;14]);
  (match List.map snd q.qdeclarations with
   | [Q.Axiom (_,true);Q.Theorem (_,_,all1);Q.Opaque (_,_,true,all2);
      Q.Quotient (_,kind);Q.Inductive (inds,ctors,recs)] ->
     expect "theorem all" all1 "[L4Anonymous;L4Anonymous]";
     expect "opaque all" all2 "[L4Anonymous;L4Anonymous]";
     expect "quotient role" kind "L4KQLift493";
     check "inductive partitions not flattened" (List.length inds=2 && List.length ctors=1 && List.length recs=2)
   | _ -> failwith "declaration roles/safety changed");
  invalid "negative BVar" (fun () -> Q.expr memo (Wire.BVar Z.minus_one));
  invalid "negative name component" (fun () -> Q.name (Wire.Num (n,Z.minus_one)));
  invalid "negative height" (fun () -> Q.hints (Wire.Regular Z.minus_one));
  invalid "negative metadata count" (fun () -> Q.constructor_data {c with num_fields=Z.minus_one});
  invalid "invalid UTF-8 does not become replacement scalar"
    (fun () -> Q.expr memo (Wire.StringLit "\192\128"));
  preflight "{\"ie\":1,\"mdata\":{\"expr\":0,\"data\":{}}}";
  unsupported "nonempty metadata is not silently dropped" (fun () ->
    preflight "{\"ie\":1,\"mdata\":{\"expr\":0,\"data\":{\"x\":1}}}");
  unsupported "unknown binder field is not silently dropped" (fun () ->
    preflight "{\"ie\":1,\"lam\":{\"name\":0,\"type\":0,\"body\":0,\"binderInfo\":\"default\",\"extra\":true}}");
  List.iter (fun tag -> unsupported "unsupported local/metavariable decoder tag"
    (fun () -> preflight ("{\"ie\":1,\"" ^ tag ^ "\":0}"))) ["fvar";"mvar"];
  unsupported "unsupported level metavariable decoder tag"
    (fun () -> preflight "{\"il\":1,\"mvar\":0}");
  unsupported "unsupported export format" (fun () ->
    Q.export {input with metadata={metadata with format_version="future"}});
  let duplicate_refused = try
    preflight "{\"ie\":1,\"ie\":2,\"bvar\":0}"; false
    with Wire.Error _ -> true in
  check "duplicate JSON keys fail before quotation" duplicate_refused;
  ()
;;

set_jrh_lexer;;
