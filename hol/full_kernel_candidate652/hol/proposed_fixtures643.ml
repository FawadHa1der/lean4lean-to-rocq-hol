(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED / UNCOMPILED / UNEXECUTED. Term/binding fixtures, NOT HOL proofs
   or accepted-file witnesses. Loading defines this function but does not run it. *)
needs "hol/file_quotation643.ml";;
unset_jrh_lexer;;

let proposed_fixtures643 () =
  let module F = File_quotation643 in
  let module Q = Full_input610 in
  let check label b = if not b then failwith label in
  let expect label actual expected =
    check label (aconv actual (parse_term expected)) in
  let binding_error label f =
    let refused = try ignore (f ()); false with F.Invalid_binding _ -> true in
    check label refused in
  let n s = Wire.Str (Wire.Anonymous,s) in
  let a = n "a" and b = n "b" in
  let sort = Wire.Sort Wire.Zero and var = Wire.BVar Z.zero in
  let header name typ : Wire.constant = {name;params=[];typ} in
  let ha = header a sort and hb = header b sort in
  let metadata : Wire.metadata =
    {format_version="3.1.0";lean_version="\195\169";lean_hash="h"} in
  let export declarations : Wire.export =
    {metadata;declarations;name_count=7;level_count=11;expr_count=13} in
  let definition h safety all : Wire.definition =
    {header=h;value=var;safety;hints=Wire.Abbrev;all} in
  let quote d = F.raw_declaration (Q.declaration (Q.create ()) d) in

  let empty = F.prepare_export (export []) in
  expect "metadata bytes/counts and original empty rows" empty.raw_file_term
    "L4FileInput642 [51;46;49;46;48] [195;169] [104] 7 11 13 []";
  expect "empty schedule" empty.schedule_term "([]:l4_file_batch642 list)";
  check "observed metadata/count bookkeeping"
    (empty.metadata=metadata && empty.name_count=7 && empty.level_count=11 &&
     empty.expr_count=13 && empty.row_count=0 && empty.batch_count=0);

  expect "axiom has empty all and exact unsafe flag" (quote (Wire.Axiom (ha,true)))
    "L4FileOrdinary642 (L4InputAxiom607 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) T) []";
  List.iter (fun (mode,tag) ->
    expect "definition safety/all/hints retained"
      (quote (Wire.Definition (definition ha mode [b;a;b])))
      ("L4FileOrdinary642 (L4InputDefinition607 L4KHintAbbrev493 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) (L4KBVar447 0) " ^ tag ^
       ") [L4String L4Anonymous [98];L4String L4Anonymous [97];L4String L4Anonymous [98]]"))
    [Wire.Safe,"L4InputSafe607";Wire.Partial,"L4InputPartial607";Wire.Unsafe,"L4InputUnsafe607"];
  expect "theorem all is not erased" (quote (Wire.Theorem (ha,var,[b;a;b])))
    "L4FileOrdinary642 (L4InputTheorem607 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) (L4KBVar447 0)) [L4String L4Anonymous [98];L4String L4Anonymous [97];L4String L4Anonymous [98]]";
  expect "opaque all and unsafe flag are not erased" (quote (Wire.Opaque (ha,var,true,[b;a])))
    "L4FileOrdinary642 (L4InputOpaque607 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) (L4KBVar447 0) T) [L4String L4Anonymous [98];L4String L4Anonymous [97]]";
  List.iter (fun (kind,tag) ->
    expect "quotient kind remains493" (quote (Wire.Quotient (ha,kind)))
      ("L4FileQuotient642 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) " ^ tag))
    [Wire.QuotType,"L4KQType493";Wire.QuotCtor,"L4KQCtor493";
     Wire.QuotLift,"L4KQLift493";Wire.QuotInd,"L4KQInd493"];

  let rich = Wire.MData (Wire.Let (a,sort,var,
    Wire.Lam (b,sort,Wire.BVar Z.one,Wire.InstanceImplicit),true)) in
  let huge = Z.of_string "18446744073709551617" in
  let rh : Wire.constant = {name=a;params=[b;a];typ=rich} in
  let rd : Wire.definition = {header=rh;value=Wire.Const (b,[Wire.Succ Wire.Zero;Wire.Zero]);
    safety=Wire.Unsafe;hints=Wire.Regular huge;all=[a]} in
  expect "full447 metadata/let/binder/universes and arbitrary hint height"
    (quote (Wire.Definition rd))
    "L4FileOrdinary642 (L4InputDefinition607 (L4KHintRegular493 18446744073709551617) (L4String L4Anonymous [97]) [L4String L4Anonymous [98];L4String L4Anonymous [97]] (L4KMData447 (L4KLet447 (L4String L4Anonymous [97]) (L4KSort447 L4KZero447) (L4KBVar447 0) (L4KLam447 (L4String L4Anonymous [98]) L4KInstImplicit447 (L4KSort447 L4KZero447) (L4KBVar447 1)) T)) (L4KConst447 (L4String L4Anonymous [98]) [L4KSucc447 L4KZero447;L4KZero447]) L4InputUnsafe607) [L4String L4Anonymous [97]]";

  let ind : Wire.inductive = {ind_header=ha;ind_num_params=huge;num_indices=Z.of_int 2;
    ind_all=[b;a;b];constructors=[b];num_nested=Z.of_int 3;is_rec=true;
    ind_unsafe=true;is_reflexive=false} in
  let ctor : Wire.constructor = {ctor_header=hb;induct=a;cidx=Z.of_int 5;
    ctor_num_params=Z.of_int 7;num_fields=Z.of_int 11;ctor_unsafe=true} in
  let rule : Wire.rule = {ctor=b;nfields=Z.of_int 13;rhs=Wire.MData var} in
  let recursor : Wire.recursor = {rec_header=header (n "r") sort;rec_all=[b;a];
    rec_num_params=Z.of_int 17;rec_num_indices=Z.of_int 19;num_motives=Z.of_int 23;
    num_minors=Z.of_int 29;rules=[rule;rule];k=false;rec_unsafe=true} in
  expect "inductive partitions and all raw metadata/rule duplicates survive"
    (quote (Wire.Inductive ([ind],[ctor],[recursor])))
    "L4FileInductive642 [L4KDeclaration493 (L4String L4Anonymous [97]) [] (L4KSort447 L4KZero447) NONE (L4KDInductive493 (L4KInductiveData493 18446744073709551617 2 [L4String L4Anonymous [98];L4String L4Anonymous [97];L4String L4Anonymous [98]] [L4String L4Anonymous [98]] 3 T F T)) L4KHintOpaque493] [L4KDeclaration493 (L4String L4Anonymous [98]) [] (L4KSort447 L4KZero447) NONE (L4KDConstructor493 (L4KConstructorData493 (L4String L4Anonymous [97]) 5 7 11 T)) L4KHintOpaque493] [L4KDeclaration493 (L4String L4Anonymous [114]) [] (L4KSort447 L4KZero447) NONE (L4KDRecursor493 (L4KRecursorData493 [L4String L4Anonymous [98];L4String L4Anonymous [97]] 17 19 23 29 [L4KRecursorRule493 (L4String L4Anonymous [98]) 13 (L4KMData447 (L4KBVar447 0));L4KRecursorRule493 (L4String L4Anonymous [98]) 13 (L4KMData447 (L4KBVar447 0))] F T)) L4KHintOpaque493]";
  let block = F.prepare_export (export [41,Wire.Inductive ([ind],[ctor],[recursor])]) in
  check "inductive block is one source row" (block.row_count=1 && block.source_lines=[41]);
  expect "inductive block remains one scheduled row" block.schedule_term "[L4FileSingle642 0]";

  let da = Wire.Axiom (header a (Wire.Const (b,[])),false) in
  let db = Wire.Axiom (hb,false) in
  let forward = F.prepare_export (export [10,da;30,db]) in
  expect "forward dependency changes only schedule" forward.schedule_term
    "[L4FileSingle642 1;L4FileSingle642 0]";
  check "raw source order and per-batch source lines"
    (forward.source_lines=[10;30] && List.map fst forward.raw_rows=[10;30] &&
     List.map (fun (x:F.batch_binding) -> x.source_lines) forward.batches=[[30];[10]]);
  expect "raw file contains source-order declarations and lines" forward.raw_file_term
    "L4FileInput642 [51;46;49;46;48] [195;169] [104] 7 11 13 [(10,L4FileOrdinary642 (L4InputAxiom607 (L4String L4Anonymous [97]) [] (L4KConst447 (L4String L4Anonymous [98]) []) F) []);(30,L4FileOrdinary642 (L4InputAxiom607 (L4String L4Anonymous [98]) [] (L4KSort447 L4KZero447) F) [])]";

  let pa = definition ha Wire.Partial [b;a] in
  let pb = definition hb Wire.Partial [b;a] in
  let mutual = F.prepare_export (export [10,Wire.Definition pa;30,Wire.Definition pb]) in
  expect "mutual leader is not first member" mutual.schedule_term "[L4FileMutual642 0 [1;0]]";
  check "mutual source-line bookkeeping follows member order"
    (match mutual.batches with
     | [x] -> x.leader_index=0 && x.member_indices=[1;0] && x.source_lines=[30;10]
     | _ -> false);
  let partial = F.prepare_export (export [5,Wire.Definition (definition ha Wire.Partial [a])]) in
  expect "singleton partial still mutual" partial.schedule_term "[L4FileMutual642 0 [0]]";
  let unsafe = F.prepare_export (export [5,Wire.Definition (definition ha Wire.Unsafe [a])]) in
  expect "singleton unsafe remains single" unsafe.schedule_term "[L4FileSingle642 0]";
  let mixed = F.prepare_export (export
    [10,Wire.Definition pa;30,Wire.Definition {pb with safety=Wire.Unsafe}]) in
  expect "scheduling does not repair mixed safety" mixed.schedule_term "[L4FileMutual642 0 [1;0]]";
  check "mixed safety survives for642/624 to check"
    (aconv (snd (List.nth mixed.raw_rows 1))
      (quote (Wire.Definition {pb with safety=Wire.Unsafe})));

  binding_error "omitted row" (fun () -> F.bind_schedule [10,da;30,db] [Replay.Single (10,da)]);
  binding_error "repeated row" (fun () -> F.bind_schedule [10,da]
    [Replay.Single (10,da);Replay.Single (10,da)]);
  binding_error "foreign leader line" (fun () -> F.bind_schedule [10,da] [Replay.Single (11,da)]);
  binding_error "same source line twice" (fun () -> F.bind_schedule [10,da;10,db] []);
  binding_error "nonpositive source line" (fun () -> F.bind_schedule [0,da] []);
  binding_error "descending source lines" (fun () -> F.bind_schedule [30,da;10,db] []);
  binding_error "different single content" (fun () -> F.bind_schedule [10,da] [Replay.Single (10,db)]);
  binding_error "same name with changed mutual body" (fun () ->
    F.bind_schedule [10,Wire.Definition pa;30,Wire.Definition pb]
      [Replay.Mutual (10,[pb;{pa with value=sort}])]);
  binding_error "mutual leader missing" (fun () ->
    F.bind_schedule [10,Wire.Definition pa;30,Wire.Definition pb] [Replay.Mutual (10,[pb])]);
  binding_error "repeated mutual member" (fun () ->
    F.bind_schedule [10,Wire.Definition pa] [Replay.Mutual (10,[pa;pa])]);
  binding_error "unknown mutual member" (fun () ->
    F.bind_schedule [10,Wire.Definition pa] [Replay.Mutual (10,[pa;pb])]);
  binding_error "empty mutual cannot own leader" (fun () ->
    F.bind_schedule [10,Wire.Definition pa] [Replay.Mutual (10,[])]);
  ()
;;

set_jrh_lexer;;
