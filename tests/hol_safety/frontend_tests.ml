let checks=ref 0
let test label ok = incr checks; if not ok then failwith label
module M=Hol_safety_input
module W=Wire
let n s=W.Str(W.Anonymous,s)
let p=W.Const(n "P",[])
let definition name safety all =
  {W.header={W.name=n name;params=[];typ=p};value=W.Const(n name,[]);
    safety;hints=W.Regular(Z.of_int 7);all=List.map n all}
let metadata={W.format_version="3.1.0";lean_version="offline";lean_hash="offline"}
let export ds={W.metadata;declarations=ds;name_count=10;level_count=1;expr_count=10}
let bad label f=try ignore(f());test label false with W.Error _->test label true
let ()=
  let a=definition "a" W.Unsafe ["a"] in
  (match M.translate_export(export[1,W.Definition a]) with
  | [1,M.Restricted(M.Unsafe_single,[d])]->
    test "unsafe annotation" (d.M.safety=M.Unsafe);
    test "body not erased" (d.M.value=Hol_input.Const(Hol_input.Str(Hol_input.Anonymous,"a"),[]));
    test "hint preserved" (d.M.hint=M.Regular_hint "7");
    test "all preserved" (d.M.all=[Hol_input.Str(Hol_input.Anonymous,"a")])
  |_->failwith "unsafe singleton dispatch");
  let partial={a with W.safety=W.Partial} in
  (match M.translate_export(export[1,W.Definition partial]) with
  | [1,M.Restricted(M.Restricted_mutual,[_])]->test "partial export singleton is mutual" true
  |_->failwith "partial export operation");
  (match M.translate_batch (Hol_input.Exprs.create 10) (Replay.Single(1,W.Definition partial)) with
  | 1,M.Restricted(M.Partial_single,[_])->test "direct partial stays direct" true
  |_->failwith "direct partial operation");
  let a=definition "a" W.Partial ["a";"b"] in
  let b=definition "b" W.Partial ["b";"a"] in
  (match M.translate_export(export[10,W.Definition a;20,W.Definition b]) with
  | [10,M.Restricted(M.Restricted_mutual,[x;y])]->
    test "two members preserved" (x.M.header.Hol_input.name<>y.M.header.Hol_input.name);
    test "different all orders retained" (x.M.all=List.rev y.M.all)
  |_->failwith "two member grouping");
  let safe={a with W.safety=W.Safe} in
  (match M.translate_export(export[1,W.Definition safe]) with
  | [1,M.Safe_input(Hol_input.Definition _,m)]->
    test "safe multi-all not mutually admitted" (List.length m.M.all=2)
  |_->failwith "safe multi-all dispatch");
  bad "missing mutual member" (fun()->M.translate_export(export[1,W.Definition a]));
  bad "duplicate member" (fun()->M.translate_export(export[1,W.Definition{a with W.all=[n "a";n "a"]}]));
  bad "member omits self" (fun()->M.translate_export(export[1,W.Definition{a with W.all=[n "b"]};2,W.Definition b]));
  bad "inconsistent member set" (fun()->M.translate_export(export[1,W.Definition a;2,W.Definition{b with W.all=[n "b"]}]));
  bad "duplicate declaration name" (fun()->M.translate_export(export[1,W.Definition a;2,W.Definition a]));
  let h={W.name=n "excluded";params=[];typ=p} in
  List.iter(fun d->match M.translate_export(export[1,d]) with
    |[1,M.Unsupported _]->test "excluded declarations explicitly unsupported" true
    |_->failwith "unsafe axiom/opaque skipped or granted")
    [W.Axiom(h,true);W.Opaque(h,W.Const(n "excluded",[]),true,[n "excluded"])];
  let mixed={b with W.safety=W.Unsafe} in
  (match M.translate_export(export[1,W.Definition a;2,W.Definition mixed]) with
  |[1,M.Restricted(M.Restricted_mutual,[x;y])]->test "safety retained for kernel check" (x.M.safety<>y.M.safety)
  |_->failwith "mixed safety metadata erased");
  List.iter(fun(name,op)->
    match M.read_file("arena/corpus/tutorial/"^name^".ndjson") with
    |[17,M.Safe_input(Hol_input.Inductive _,_);20,M.Restricted(actual,[d]);22,M.Safe_input(Hol_input.Theorem _,_)]->
      test "Arena operation retained" (actual=op);
      test "Arena body and all preserved" (List.length d.M.all=1 && d.M.hint=M.Opaque_hint)
    |_->failwith("unexpected decoded Arena shape "^name))
    ["140_falseFromUnsafe",M.Unsafe_single;"141_falseFromPartial",M.Restricted_mutual];
  Printf.printf "SAFETY_FRONTEND_OFFLINE_PASSED %d no_logical_verdicts\n%!" !checks
