let checks = ref 0
let ensure label ok = incr checks; if not ok then failwith label
let n s = Wire.dotted_name [s]
let ty = Wire.Sort (Wire.Succ Wire.Zero)
let atom s e = Wire.Definition {Wire.header={Wire.name=n s;params=[];typ=ty};
  value=e;safety=Wire.Safe;hints=Wire.Abbrev;all=[n s]}
let snapshot schedule unpack rows =
  try Ok(List.map unpack (schedule rows)) with Wire.Error e -> Error e
let old_unpack b = Replay_reference.line b,Replay_reference.count b,
  List.concat_map Replay_reference.names (Replay_reference.declarations b)
let new_unpack b = Replay.line b,Replay.count b,
  List.concat_map Replay.names (Replay.declarations b)
let compare label rows =
  ensure (label ^ " exact schedule/error")
    (snapshot Replay_reference.schedule old_unpack rows = snapshot Replay.schedule new_unpack rows);
  let old_index,old_owner,old_batches=Replay_reference.prepare rows in
  let new_index,new_owner,new_batches=Replay.prepare rows in
  ensure (label ^ " exact summary/statistics")
    (Replay_reference.input_ordered old_index old_owner old_batches =
     Replay.input_ordered new_index new_owner new_batches)

let () =
  let rng=Random.State.make [|91271;81879|] in
  for trial=0 to 999 do
    let count=1+Random.State.int rng 80 in
    let pool=ref [ty;Wire.NatLit Z.zero;Wire.StringLit "a"] in
    let choose ()=List.nth !pool (Random.State.int rng (List.length !pool)) in
    let rows=Array.init count(fun i->
      let name="n" ^ string_of_int i in
      let dep=Wire.Const(n ("n" ^ string_of_int(Random.State.int rng (count+1))),[]) in
      let a=choose() and b=choose() in
      let e=match Random.State.int rng 9 with
        | 0 -> Wire.App(a,dep) | 1 -> Wire.Lam(n "x",a,dep,Wire.Explicit)
        | 2 -> Wire.Pi(n "x",dep,b,Wire.Implicit)
        | 3 -> Wire.Let(n "x",a,dep,b,false)
        | 4 -> Wire.Proj(n "n0",Z.zero,a)
        | 5 -> Wire.MData dep | 6 -> Wire.App(a,b)
        | 7 -> Wire.App(dep,dep) | _ -> a in
      pool:=e:: !pool;
      i+1,atom name e) in
    compare ("generated" ^ string_of_int trial) (Array.to_list rows)
  done;
  let deeply=ref(Wire.Const(n "base",[])) in
  for _=1 to 20000 do deeply:=Wire.MData !deeply done;
  compare "deep early" [1,atom "base" ty;2,atom "deep" !deeply];
  compare "deep forward" [1,atom "deep" !deeply;2,atom "base" ty];
  let shared=ref(Wire.Const(n "base",[])) in
  for _=1 to 1000 do shared:=Wire.App(!shared,!shared) done;
  compare "shared" ((1,atom "base" ty)::List.init 1000(fun i->i+2,atom("d"^string_of_int i) !shared));
  Printf.printf "REPLAY_DIFFERENTIAL_PASS %d\n%!" !checks
