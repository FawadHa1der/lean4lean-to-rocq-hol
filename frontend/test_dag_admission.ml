module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
let nat = A.nat
let key = D.positive
let list xs = A.list (fun x -> x) xs
let rows xs = list (List.map (fun (i,n) -> C.Pair (key i,n)) xs)
let count = ref 0
let equal label a b = incr count; if a <> b then failwith ("admission differential: " ^ label)
let name i = C.NameNum (C.NameAnon,A.binary (Z.of_int i))

let generated () =
  for seed = 0 to 7 do
    let rng = Random.State.make [|seed;2910|] in
    let data = List.init 24 (fun j ->
      let i = j+1 in
      let node = if i = 1 then C.DSort C.LZero else
        let a = key (1+Random.State.int rng (i-1)) in
        let b = key (1+Random.State.int rng (i-1)) in
        match Random.State.int rng 8 with
        | 0 -> C.DSort (C.LSucc C.LZero)
        | 1 -> C.DBVar C.O
        | 2 -> C.DLam (C.NameAnon,C.BDefault,a,b)
        | 3 -> C.DPi (C.NameAnon,C.BImplicit,a,b)
        | 4 -> C.DApp (a,b)
        | 5 -> C.DLet (C.NameAnon,a,b,a,C.False)
        | 6 -> C.DMData a
        | _ -> C.DConst (name 99,C.Nil) in i,node) |> rows in
    let duplicate = {C.decl_hints = C.HintOpaque; decl_name =name 1;decl_params=C.Nil;decl_type=C.ESort C.LZero;
      decl_value=C.None;decl_kind_of=C.DAssumption} in
    List.iter (fun (env,n,ps) -> List.iter (fun fuel ->
      for i = 1 to 24 do
        let tr = key i and br = key (25-i) in
        let expected = C.decode_then_admit_definition C.HintOpaque (nat fuel) env n ps data tr br in
        List.iter (fun budget -> equal "generated"
          (C.admit_dag_definition C.HintOpaque (nat budget) (nat fuel) env n ps data tr br) expected)
          [0;32]
      done) [0;1;16])
      [C.Nil,name 1,C.Nil; list [duplicate],name 1,C.Nil;
       C.Nil,C.core_nat_name,C.Nil; C.Nil,name 1,list [name 2;name 2]]
  done;
  let cases = [rows [1,C.DMData (key 1)]; rows [1,C.DMData (key 2)];
    rows [1,C.DSort C.LZero;1,C.DSort C.LZero]; C.Nil;
    rows [1,C.DSort C.LZero;2,C.DSort (C.LSucc C.LZero)]] in
  List.iter (fun data -> List.iter (fun (tr,br) -> List.iter (fun fuel ->
    equal "malformed/root" (C.admit_dag_definition C.HintOpaque (nat 32) (nat fuel) C.Nil (name 1) C.Nil data (key tr) (key br))
      (C.decode_then_admit_definition C.HintOpaque (nat fuel) C.Nil (name 1) C.Nil data (key tr) (key br))) [0;16])
    [1,1;2,1;1,2;3,1;1,3]) cases

let synthetic_decoders () =
  let n = Wire.Num (Wire.Str (Wire.Anonymous,"A.B"),Z.shift_left Z.one 512) in
  let u = Wire.IMax (Wire.Param n,Wire.Max (Wire.Zero,Wire.Succ Wire.Zero)) in
  let c = Wire.Const (n,[u]) in
  let b = Wire.BVar Z.zero in
  let huge = Wire.NatLit (Z.add (Z.shift_left Z.one 2048) (Z.of_int 37)) in
  let values = [b;Wire.Sort u;c;Wire.App(c,c);
    Wire.Lam(n,c,b,Wire.InstanceImplicit);Wire.Pi(n,c,b,Wire.StrictImplicit);
    Wire.Let(n,c,huge,b,true);Wire.Proj(n,Z.of_int 7,c);huge;
    Wire.StringLit "\000hello\255\194\169";Wire.MData c] in
  let st = A.create () in
  List.iter (fun a -> List.iter (fun b ->
    D.verify_decode st a b (D.encode_pair st a b); incr count) values) values;
  assert (not (D.exact_expr (C.EBVar C.O) (C.EBVar (C.S C.O))));
  assert (not (D.exact_expr (A.expr st (Wire.Lam(n,c,b,Wire.Explicit)))
    (A.expr st (Wire.Lam(n,c,b,Wire.Implicit)))));
  assert (not (D.exact_expr (A.expr st huge) (A.expr st (Wire.NatLit Z.zero))))

let decode_file path =
  let export = Wire.read_file path and st = A.create () in
  let pairs = ref 0 and node_count = ref 0 in
  let pair typ body =
    let encoded = D.encode_pair st typ body in
    D.verify_decode st typ body encoded;
    incr pairs; node_count := !node_count + encoded.D.count in
  List.iter (fun (_,d) -> match d with
    | Wire.Definition d -> pair d.header.typ d.value
    | Wire.Theorem(h,v,_) | Wire.Opaque(h,v,_,_) -> pair h.typ v
    | _ -> ()) export.Wire.declarations;
  Printf.printf "decode-exact path=%s pairs=%d nodes=%d\n%!" path !pairs !node_count

let compare_file path =
  let export = Wire.read_file path and st = A.create () in
  let env = ref C.Nil and stop = ref false and defs = ref 0 and theorems = ref 0 and opaques = ref 0 in
  let batches = try Replay.schedule export.Wire.declarations with
    | Wire.Error error when Wire.error_exit_code error = 1 ->
      Printf.printf "shared-scheduler-reject path=%s (no checker result to compare)\n%!" path;
      [] in
  List.iter (fun batch -> if not !stop then begin
    let original,actual = match batch with
      | Replay.Single(_,d) ->
        (match d with
         | Wire.Definition def when def.Wire.safety = Wire.Safe -> incr defs
         | Wire.Theorem _ -> incr theorems
         | Wire.Opaque (_,_,false,_) -> incr opaques
         | _ -> ());
        A.admit (nat 512) !env st d,D.admit (nat 512) !env st d
      | Replay.Mutual(_,ds) ->
        let result = A.mutual (nat 512) !env st ds in result,result in
    equal path actual original;
    match actual with C.Accept next -> env := next | _ -> stop := true
  end) batches;
  Printf.printf "admission-exact path=%s safe-definitions=%d theorems=%d safe-opaques=%d\n%!"
    path !defs !theorems !opaques

let () =
  match Array.to_list Sys.argv with
  | [_] -> generated (); synthetic_decoders (); Printf.printf "%d synthetic exact comparisons passed\n" !count
  | _::"--decode"::paths -> List.iter decode_file paths
  | _::"--compare"::paths -> List.iter compare_file paths;
    Printf.printf "%d full admission results compared\n" !count
  | _ -> failwith "usage: test-dag-admission [--decode|--compare FILE ...]"
