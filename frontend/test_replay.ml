let failures=ref 0 and checks=ref 0
let check label condition = incr checks;if not condition then(incr failures;Printf.eprintf "FAIL %s\n" label)
let n s=Wire.dotted_name [s]
let ty=Wire.Sort(Wire.Succ Wire.Zero)
let header name={Wire.name=n name;params=[];typ=ty}
let definition ?(all=[]) ?(safety=Wire.Safe) name value =
  Wire.Definition{Wire.header=header name;value;safety;hints=Wire.Abbrev;
                  all=if all=[] then [n name] else List.map n all}
let constant name=Wire.Const(n name,[])
let atom name=definition name (Wire.Sort Wire.Zero)
let existing_cases schedule =
  let order rows=List.map Replay.line (schedule rows) in
  let malformed rows=try ignore(schedule rows);false with Wire.Error e->e.kind=Wire.Malformed in
  check "empty" (order []=[]);
  check "preserve independent order" (order [1,atom "a";2,atom "b"]=[1;2]);
  check "forward body dependency" (order [1,definition "a" (constant "b");2,atom "b"]=[2;1]);
  check "forward type dependency" (order [1,Wire.Axiom({(header "a")with typ=constant "b"},false);2,atom "b"]=[2;1]);
  check "opaque body dependency" (order [1,Wire.Opaque(header "a",constant "b",false,[n "a"]);2,atom "b"]=[2;1]);
  check "theorem proof dependency" (order [1,Wire.Theorem(header "a",constant "b",[n "a"]);2,atom "b"]=[2;1]);
  check "missing constants still reach kernel" (order [1,definition "a" (constant "absent")]=[1]);
  check "self reference still reaches kernel" (order [1,definition "a" (constant "a")]=[1]);
  check "duplicate declarations" (malformed [1,atom "a";2,atom "a"]);
  check "cyclic safe definitions" (malformed [1,definition "a" (constant "b");2,definition "b" (constant "a")]);
  let mutual name value=definition ~all:["a";"b"] ~safety:Wire.Unsafe name value in
  let rows=[1,mutual "a" (constant "b");2,atom "c";3,mutual "b" (constant "c")] in
  let batches=schedule rows in
  check "noncontiguous mutual dependency" (List.map Replay.line batches=[2;1]);
  check "all input declarations covered" (List.fold_left(fun total b->total+Replay.count b)0 batches=3);
  check "mutual batch contains both names" (match batches with
    | [_;Replay.Mutual(_,ds)]->List.map(fun(d:Wire.definition)->d.header.name)ds=[n "a";n "b"]|_->false);
  check "missing mutual member" (malformed [1,mutual "a" (constant "b")]);
  check "member is not definition" (malformed [1,mutual "a" (constant "b");2,Wire.Axiom(header "b",true)]);
  check "inconsistent mutual list" (malformed [1,mutual "a" (constant "b");2,atom "b"]);
  check "duplicate mutual member" (malformed [1,definition ~safety:Wire.Unsafe ~all:["a";"a"] "a" ty]);
  check "mutual list omits self" (malformed [1,definition ~safety:Wire.Unsafe ~all:["b";"c"] "a" ty;2,atom "b";3,atom "c"]);
  check "safe all is not an admission group" (order [1,definition ~all:["a";"notExported"] "a" ty]=[1]);
  check "opaque all is not an admission group" (order [1,Wire.Opaque(header "a",ty,false,[n "a";n "notExported"])]=[1]);
  check "partial singleton grouped" (match schedule [1,definition ~safety:Wire.Partial "a" (constant "a")]with
    | [Replay.Mutual(_,[_])]->true|_->false);
  let shared=Wire.App(constant "b",constant "b") in
  check "shared DAG dependency" (order [1,definition "a" (Wire.App(shared,shared));2,atom "b"]=[2;1]);
  check "metadata dependency" (order [1,definition "a" (Wire.MData(constant "b"));2,atom "b"]=[2;1]);
  check "nat literal implicit dependency" (order [1,definition "a" (Wire.NatLit Z.zero);2,atom "Nat"]=[2;1]);
  let deep=ref(constant "b") in
  for _=1 to 20000 do deep:=Wire.MData !deep done;
  check "iterative deep traversal" (order [1,definition "a" !deep;2,atom "b"]=[2;1])

let graph rows=fst(Replay.schedule_with_stats ~force_graph:true rows)
let same_declaration a b = a==b || match a,b with
  | Wire.Definition a,Wire.Definition b -> a==b
  | _ -> false
let exact_records rows batches =
  let output=List.concat_map Replay.declarations batches in
  List.length output=List.length rows &&
  List.for_all(fun (_,d)->List.length(List.filter(same_declaration d)output)=1)rows
let error schedule rows =
  try ignore(schedule rows);None with Wire.Error e->Some(e.line,e.kind,e.message)
let inductive ?(ity=ty) ?(cty=ty) ?(rty=ty) ?(rhs=ty) () =
  Wire.Inductive(
    [{Wire.ind_header={(header "I")with typ=ity};ind_num_params=Z.zero;num_indices=Z.zero;
      ind_all=[n "I"];constructors=[n "I_ctor"];num_nested=Z.zero;
      is_rec=false;ind_unsafe=false;is_reflexive=false}],
    [{Wire.ctor_header={(header "I_ctor")with typ=cty};induct=n "I";cidx=Z.zero;
      ctor_num_params=Z.zero;num_fields=Z.zero;ctor_unsafe=false}],
    [{Wire.rec_header={(header "I_rec")with typ=rty};rec_all=[n "I"];
      rec_num_params=Z.zero;rec_num_indices=Z.zero;num_motives=Z.one;num_minors=Z.one;
      rules=[{Wire.ctor=n "I_ctor";nfields=Z.zero;rhs}];k=false;rec_unsafe=false}])

let forward_case label d =
  let rows=[10,d;20,atom "dep"] in
  let batches,stats=Replay.schedule_with_stats rows in
  check (label^" falls back") (stats.Replay.strategy=Replay.Dependency_graph);
  check (label^" orders dependency") (List.map Replay.line batches=[20;10]);
  check (label^" exact fallback coverage") (exact_records rows batches && exact_records rows (graph rows));
  let rows=List.rev rows in
  let batches,stats=Replay.schedule_with_stats rows in
  check (label^" accepts topological input")
    (stats.Replay.strategy=Replay.Input_order && List.map Replay.line batches=[20;10] && exact_records rows batches)

let extra_cases () =
  let rows=[1,atom "a";2,definition "b" (constant "a");3,atom "c"] in
  let fast,stats=Replay.schedule_with_stats rows in
  check "topological fast order differs legitimately from Kahn"
    (stats.Replay.strategy=Replay.Input_order && List.map Replay.line fast=[1;2;3] &&
     List.map Replay.line (graph rows)=[1;3;2]);
  check "both orders contain every original record once" (exact_records rows fast && exact_records rows (graph rows));
  check "forced graph does not allocate summaries"
    ((snd(Replay.schedule_with_stats ~force_graph:true rows)).Replay.summarized_exprs=0);
  let dep=constant "dep" in
  List.iter(fun(label,value)->forward_case label (definition "use" value)) [
    "application function",Wire.App(dep,ty); "application argument",Wire.App(ty,dep);
    "lambda domain",Wire.Lam(n "x",dep,ty,Wire.Explicit);
    "lambda body",Wire.Lam(n "x",ty,dep,Wire.Explicit);
    "Pi domain",Wire.Pi(n "x",dep,ty,Wire.Explicit);
    "Pi body",Wire.Pi(n "x",ty,dep,Wire.Explicit);
    "let type",Wire.Let(n "x",dep,ty,ty,false);
    "let value",Wire.Let(n "x",ty,dep,ty,false);
    "let body",Wire.Let(n "x",ty,ty,dep,true);
    "projection owner",Wire.Proj(n "dep",Z.zero,ty);
    "projection argument",Wire.Proj(n "absent",Z.zero,dep);
    "mdata body",Wire.MData dep];
  List.iter(fun(label,d)->forward_case label d) [
    "axiom type",Wire.Axiom({(header "use")with typ=dep},false);
    "opaque type",Wire.Opaque({(header "use")with typ=dep},ty,false,[n "use"]);
    "opaque value",Wire.Opaque(header "use",dep,false,[n "use"]);
    "theorem type",Wire.Theorem({(header "use")with typ=dep},ty,[n "use"]);
    "theorem proof",Wire.Theorem(header "use",dep,[n "use"]);
    "inductive type",inductive ~ity:dep ();
    "constructor type",inductive ~cty:dep ();
    "recursor type",inductive ~rty:dep ();
    "recursor rule RHS",inductive ~rhs:dep ()];
  let literal label value parts =
    let target=Wire.dotted_name parts in
    let rows=[1,definition "use" value;2,Wire.Axiom({(header "unused")with name=target},false)] in
    let batches,stats=Replay.schedule_with_stats rows in
    check (label^" implicit forward edge")
      (stats.Replay.strategy=Replay.Dependency_graph && List.map Replay.line batches=[2;1] &&
       List.map Replay.line (graph rows)=[2;1]);
    let batches,stats=Replay.schedule_with_stats (List.rev rows) in
    check (label^" implicit earlier edge")
      (stats.Replay.strategy=Replay.Input_order && List.map Replay.line batches=[2;1]) in
  List.iter(fun parts->literal (String.concat "." parts) (Wire.NatLit Z.zero) parts)
    [["Nat"];["Nat";"zero"];["Nat";"succ"]];
  List.iter(fun parts->literal (String.concat "." parts) (Wire.StringLit "x") parts)
    [["String"];["Char"];["Char";"ofNat"];["String";"ofList"];["List"];["List";"nil"];["List";"cons"]];
  List.iter(fun kind->
    let rows=[1,Wire.Quotient(header "Q",kind);2,atom "Eq"] in
    let batches,stats=Replay.schedule_with_stats rows in
    check "quotient implicit Eq fallback"
      (stats.Replay.strategy=Replay.Dependency_graph && List.map Replay.line batches=[2;1]);
    check "quotient implicit Eq fast"
      ((snd(Replay.schedule_with_stats (List.rev rows))).Replay.strategy=Replay.Input_order))
    [Wire.QuotType;Wire.QuotCtor;Wire.QuotLift;Wire.QuotInd];
  let mutual name value=definition ~all:["a";"b"] ~safety:Wire.Unsafe name value in
  let rows=[1,mutual "a" (constant "b");2,atom "middle";3,mutual "b" (constant "a")] in
  let batches,stats=Replay.schedule_with_stats rows in
  check "noncontiguous mutual owners allow fast order"
    (stats.Replay.strategy=Replay.Input_order && List.map Replay.line batches=[1;2] && exact_records rows batches);
  check "noncontiguous mutual forced graph coverage" (exact_records rows (graph rows));
  let self=[1,inductive ~rty:(constant "I_ctor") ~rhs:(constant "I_rec") ()] in
  check "inductive member owners are self edges"
    ((snd(Replay.schedule_with_stats self)).Replay.strategy=Replay.Input_order && exact_records self (graph self));
  let missing=[1,definition "x" (constant "not_present")] in
  check "unknown references are not transport verdicts"
    ((snd(Replay.schedule_with_stats missing)).Replay.strategy=Replay.Input_order && exact_records missing (graph missing));
  let malformed_rows=[
    [1,atom "x";2,atom "x"];
    [1,mutual "a" ty];
    [1,mutual "a" ty;2,Wire.Axiom(header "b",false)];
    [1,mutual "a" ty;2,atom "b"];
    [1,definition ~all:["a";"a"] ~safety:Wire.Unsafe "a" ty];
    [1,mutual "a" ty;2,mutual "b" ty;3,definition ~all:["b";"c"] ~safety:Wire.Unsafe "c" ty];
    [1,definition "a" (constant "b");2,definition "b" (constant "a")]] in
  List.iter(fun rows->let result=error Replay.schedule rows in
    check "fast probe and forced graph preserve exact malformed diagnostic"
      (result<>None && result=error graph rows))malformed_rows;
  let shared=ref(constant "base") in
  for _=1 to 128 do shared:=Wire.App(!shared,!shared) done;
  let rows=(1,definition "base" ty)::List.init 1000(fun i->i+2,definition ("user"^string_of_int i) !shared) in
  let batches,stats=Replay.schedule_with_stats rows in
  check "shared DAG summarized once across declarations"
    (stats.Replay.strategy=Replay.Input_order && stats.Replay.summarized_exprs=130 && exact_records rows batches);
  let rows=[1,definition "base" ty;2,definition "user" !shared] in
  ignore(Replay.schedule rows);
  check "cache does not leak between owner maps"
    ((snd(Replay.schedule_with_stats (List.rev rows))).Replay.strategy=Replay.Dependency_graph);
  let deep=ref(constant "base") in
  for _=1 to 20000 do deep:=Wire.MData !deep done;
  check "iterative postorder fast traversal"
    ((snd(Replay.schedule_with_stats [1,definition "base" ty;2,definition "deep" !deep])).Replay.strategy=Replay.Input_order)

let generated_dags () =
  let random=Random.State.make [|314159;271828|] in
  for trial=1 to 50 do
    let size=20 in
    let dependencies=Array.init size(fun i->
      List.init i Fun.id |> List.filter(fun _->Random.State.int random 4=0)) in
    let rows=Array.init size(fun i->
      let body=List.fold_left(fun body j->Wire.App(body,constant ("g"^string_of_int j))) ty dependencies.(i) in
      i+1,definition ("g"^string_of_int i) body) in
    let verify batches=
      let positions=Array.make size (-1) in
      List.iteri(fun i batch->positions.(Replay.line batch-1)<-i)batches;
      exact_records (Array.to_list rows) batches &&
      Array.for_all Fun.id (Array.mapi(fun i ds->List.for_all(fun j->positions.(j)<positions.(i))ds)dependencies) in
    let sorted,stats=Replay.schedule_with_stats (Array.to_list rows) in
    check ("generated sorted DAG "^string_of_int trial)
      (stats.Replay.strategy=Replay.Input_order && verify sorted && verify (graph (Array.to_list rows)));
    for i=size-1 downto 1 do
      let j=Random.State.int random (i+1) in
      let row=rows.(i) in rows.(i)<-rows.(j);rows.(j)<-row
    done;
    check ("generated shuffled DAG "^string_of_int trial)
      (verify (Replay.schedule (Array.to_list rows)) && verify (graph (Array.to_list rows)))
  done

let ()=
  existing_cases Replay.schedule;
  existing_cases graph;
  extra_cases ();
  generated_dags ();
  Printf.printf "replay transport: %d checks, %d failures\n" !checks !failures;
  if !failures<>0 then exit 1
