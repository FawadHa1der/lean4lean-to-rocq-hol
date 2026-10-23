(* Full result comparisons, including declaration kinds and failure payloads. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
let nat = A.nat
let key = D.positive
let list xs = A.list (fun x -> x) xs
let rows xs = list (List.map (fun (i,n) -> C.Pair (key i,n)) xs)
let wname s = Wire.Str (Wire.Anonymous,s)
let cname s = A.name (A.create ()) (wname s)
let p_name = cname "TestP"
let h_name = cname "testProof"
let new_name = cname "dagValue"
let p = C.EConst (p_name,C.Nil)
let h = C.EConst (h_name,C.Nil)
let assumed n ty = {C.decl_hints = C.HintOpaque; decl_name =n;decl_params=C.Nil;decl_type=ty;
  decl_value=C.None;decl_kind_of=C.DAssumption}
let env = list [assumed h_name p;assumed p_name (C.ESort C.LZero)]
let count = ref 0
let outcomes = Hashtbl.create 32
let outcome = function
  | C.Accept _ -> "accept"
  | C.Reject why -> "reject: " ^ A.reject_reason why
  | C.Decline why -> "decline: " ^ A.decline_reason why
let equal label actual expected =
  incr count;
  let category = outcome actual in
  Hashtbl.replace outcomes category (1 + Option.value (Hashtbl.find_opt outcomes category) ~default:0);
  if actual <> expected then failwith ("full result mismatch: " ^ label)

let test_rows = rows [
  1,C.DSort C.LZero;2,C.DSort (C.LSucc C.LZero);
  3,C.DConst(p_name,C.Nil);4,C.DConst(h_name,C.Nil);5,C.DBVar C.O;
  6,C.DMVar C.NameAnon;7,C.DSort(C.LParam C.NameAnon);8,C.DFVar C.NameAnon;
  9,C.DLit(C.LitNat(C.Npos C.XH));10,C.DProj(C.NameAnon,C.O,key 4);
  11,C.DConst(new_name,C.Nil);12,C.DMData(key 4);
  13,C.DLam(C.NameAnon,C.BDefault,key 3,key 5);
  14,C.DPi(C.NameAnon,C.BDefault,key 3,key 3);
  15,C.DLet(C.NameAnon,key 3,key 4,key 5,C.False);
  16,C.DApp(key 13,key 4)]

let paths = ["theorem",C.admit_dag_theorem,C.decode_then_admit_theorem;
             "opaque",C.admit_dag_opaque,C.decode_then_admit_opaque]

let full_differentials () =
  let unsafe_env = list [{(assumed h_name p) with C.decl_kind_of=C.DUnsafe C.DAssumption};
    assumed p_name (C.ESort C.LZero)] in
  let partial_env = list [{(assumed h_name p) with C.decl_kind_of=C.DPartial};
    assumed p_name (C.ESort C.LZero)] in
  let pairs = [3,4;2,1;1,3;3,1;4,4;5,4;3,5;3,6;7,1;3,7;3,8;
    3,9;3,10;3,11;3,12;14,13;3,15;3,16;17,4;3,17] in
  List.iter (fun (label,optimized,reference) ->
    List.iter (fun env -> List.iter (fun name -> List.iter (fun ps ->
      List.iter (fun fuel -> List.iter (fun (tr,br) ->
        let expected = reference (nat fuel) env name ps test_rows (key tr) (key br) in
        List.iter (fun budget -> equal label
          (optimized (nat budget) (nat fuel) env name ps test_rows (key tr) (key br)) expected)
          [0;1;32]) pairs) [0;1;2;16]) [C.Nil;list [C.NameAnon];list [C.NameAnon;C.NameAnon]])
      [new_name;h_name;C.core_nat_name]) [env;C.Nil;unsafe_env;partial_env]) paths;
  let malformed = [C.Nil;rows [1,C.DMData(key 1)];rows [1,C.DMData(key 2)];
    rows [1,C.DSort C.LZero;1,C.DSort C.LZero];
    rows [1,C.DMData(key 2);2,C.DSort C.LZero]] in
  List.iter (fun (label,optimized,reference) -> List.iter (fun rows ->
    List.iter (fun fuel -> List.iter (fun (tr,br) -> equal label
      (optimized (nat 32) (nat fuel) env new_name C.Nil rows (key tr) (key br))
      (reference (nat fuel) env new_name C.Nil rows (key tr) (key br))) [1,1;2,1;1,2])
      [0;16]) malformed) paths

let focused () =
  equal "malicious nonProp theorem"
    (C.admit_dag_theorem (nat 32) (nat 16) C.Nil new_name C.Nil test_rows (key 2) (key 1))
    (C.Reject C.MalformedDeclaration);
  equal "invalid opaque"
    (C.admit_dag_opaque (nat 32) (nat 16) C.Nil new_name C.Nil test_rows (key 1) (key 1))
    (C.Reject C.TypeMismatch);
  List.iter (fun (label,optimized,_,kind) ->
    let result = optimized (nat 32) (nat 16) env new_name C.Nil test_rows (key 3) (key 4) in
    let expected = C.Accept (C.Cons ({C.decl_hints = C.HintOpaque; decl_name =new_name;decl_params=C.Nil;decl_type=p;
      decl_value=C.Some h;decl_kind_of=kind},env)) in
    equal label result expected;
    let admitted = match result with C.Accept next -> next | _ -> failwith label in
    let reduced = C.whnf (nat 16) admitted C.Nil C.empty_context (C.EConst(new_name,C.Nil)) in
    let expected = if kind = C.DTheorem then C.Accept h else C.Accept(C.EConst(new_name,C.Nil)) in
    if reduced <> expected then failwith "theorem/opaque delta policy")
    ["theorem",C.admit_dag_theorem,C.decode_then_admit_theorem,C.DTheorem;
     "opaque",C.admit_dag_opaque,C.decode_then_admit_opaque,C.DOpaque]

let adapter_cases () =
  let header typ : Wire.constant = {name=wname "adapterValue";params=[];typ} in
  let prop = Wire.Sort Wire.Zero and typ = Wire.Sort (Wire.Succ Wire.Zero) in
  let p = Wire.Const(wname "TestP",[]) and h = Wire.Const(wname "testProof",[]) in
  let thm ty value = Wire.Theorem(header ty,value,[]) in
  let opaque ty value unsafe = Wire.Opaque(header ty,value,unsafe,[]) in
  let definition safety = Wire.Definition {header=header typ;value=prop;safety;
    hints=Wire.Abbrev;all=[wname "adapterValue"]} in
  let cases = [thm p h; thm typ prop; thm p prop;opaque typ prop false;
    opaque prop prop false;opaque typ prop true;definition Wire.Safe;
    definition Wire.Unsafe;definition Wire.Partial] in
  List.iter (fun d -> List.iter (fun fuel ->
    equal "adapter dispatch" (D.admit (nat fuel) env (A.create ()) d)
      (A.admit (nat fuel) env (A.create ()) d)) [0;1;16]) cases;
  (* Existing transport resource errors are compared as strings, not collapsed
     into logical rejection or a generic decline. OS resource limits are not
     intentionally triggered or covered by these deterministic tests. *)
  let resource action = try ignore(action ()); None with A.Resource s -> Some s in
  let invalid_indices = [Z.of_int (-1);Z.of_int 1_000_001;Z.shift_left Z.one 128] in
  List.iter (fun index -> List.iter (fun make ->
    let d = make (Wire.BVar index) in
    let old = resource (fun () -> A.admit (nat 16) env (A.create ()) d) in
    let actual = resource (fun () -> D.admit (nat 16) env (A.create ()) d) in
    if actual <> old || actual = None then failwith "adapter resource payload mismatch")
    [thm p; (fun body -> opaque typ body false)]) invalid_indices

let () =
  full_differentials (); focused (); adapter_cases ();
  List.iter (fun category -> if not (Hashtbl.mem outcomes category) then
    failwith ("missing coverage: " ^ category))
    ["accept";"reject: malformed declaration";"reject: type mismatch";
     "reject: duplicate declaration";"reject: duplicate universe parameter";
     "decline: checker fuel exhausted";"decline: unsupported expression: literal/projection"];
  Printf.printf "%d full theorem/opaque result comparisons passed; 6 adapter resource payload comparisons passed\n" !count;
  Hashtbl.to_seq outcomes |> List.of_seq |> List.sort compare |>
    List.iter (fun (category,n) -> Printf.printf "%s: %d\n" category n)
