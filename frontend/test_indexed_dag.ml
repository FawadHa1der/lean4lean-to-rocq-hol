(* Synthetic full-result differentials, never a checker verdict oracle. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
let nat = A.nat
let key = D.positive
let list xs = A.list (fun x -> x) xs
let rows xs = list (List.map (fun (i,n) -> C.Pair (key i,n)) xs)
let name s = A.name (A.create ()) (Wire.Str (Wire.Anonymous,s))
let p_name = name "TestP" and h_name = name "testProof" and new_name = name "dagValue"
let p = C.EConst (p_name,C.Nil) and h = C.EConst (h_name,C.Nil)
let prop = C.ESort C.LZero and typ = C.ESort (C.LSucc C.LZero)
let assumed n ty = {C.decl_hints = C.HintOpaque; decl_name =n;decl_params=C.Nil;decl_type=ty;
  decl_value=C.None;decl_kind_of=C.DAssumption}
let base = [assumed h_name p;assumed p_name prop]
let pad count env =
  let fillers = List.init (max 0 (count-List.length env)) (fun i ->
    let n = C.NameStr (C.NameNum(C.NameAnon,A.binary(Z.of_int i)),A.string "same") in
    assumed n prop) in
  list (env @ fillers)
let data = rows [1,C.DSort C.LZero;2,C.DSort (C.LSucc C.LZero);
  3,C.DConst(p_name,C.Nil);4,C.DConst(h_name,C.Nil);5,C.DBVar C.O;
  6,C.DMVar C.NameAnon;7,C.DSort(C.LParam C.NameAnon);8,C.DFVar C.NameAnon;
  9,C.DLit(C.LitNat(C.Npos C.XH));10,C.DProj(C.NameAnon,C.O,key 4);
  11,C.DConst(new_name,C.Nil);12,C.DMData(key 4);
  13,C.DLam(C.NameAnon,C.BDefault,key 3,key 5);
  14,C.DPi(C.NameAnon,C.BDefault,key 3,key 3);
  15,C.DLet(C.NameAnon,key 3,key 4,key 5,C.False);
  16,C.DApp(key 13,key 4)]
let kinds = [(C.DagDefinition C.HintOpaque);C.DagTheorem;C.DagOpaque]
let hashes = ["fixed-bitfold8",C.suffix_bitfold8;"all-collide",(fun _ -> C.N0)]
let count = ref 0 and accepted = ref 0 and outcomes = Hashtbl.create 32
let outcome = function
  | C.Accept _ -> "accept"
  | C.Reject why -> "reject: " ^ A.reject_reason why
  | C.Decline why -> "decline: " ^ A.decline_reason why
let equal label actual expected =
  incr count;
  if actual <> expected then failwith ("FULL result mismatch: " ^ label);
  let category = outcome actual in
  if category = "accept" then incr accepted;
  Hashtbl.replace outcomes category (1 + Option.value (Hashtbl.find_opt outcomes category) ~default:0)
let compare kind fuel env n ps rows tr br =
  let expected = C.linear_cache_new_admit kind (nat 32) (nat fuel) env n ps rows (key tr) (key br) in
  equal "linear-cache/new-Checker versus new ordinary admit" expected
    (C.new_ordinary_decode_admit kind (nat fuel) env n ps rows (key tr) (key br));
  List.iter (fun budget ->
    equal "hybrid" (C.indexed_dag_admit kind (nat budget) (nat fuel) env n ps rows (key tr) (key br)) expected;
    List.iter (fun (label,hash) -> equal label
      (C.indexed_admit hash kind (nat budget) (nat fuel) env n ps rows (key tr) (key br)) expected) hashes)
    [0;1;32]

let matrix () =
  let mark kind = {(assumed h_name p) with C.decl_kind_of=kind} :: base in
  let envs = [base;mark(C.DUnsafe C.DAssumption);mark C.DPartial;mark C.DUnsupported;
    assumed h_name typ :: base] in
  List.iter (fun env -> List.iter (fun size -> let env = pad size env in
    List.iter (fun kind -> List.iter (fun fuel ->
      List.iter (fun (tr,br) -> compare kind fuel env new_name C.Nil data tr br)
        [3,4;2,1;3,1;3,5;3,6;3,7;3,8;3,9;3,10;3,11;3,12;14,13;3,15;3,16];
      List.iter (fun (n,ps) -> compare kind fuel env n ps data 3 4)
        [h_name,C.Nil;C.core_nat_name,C.Nil;new_name,list [C.NameAnon;C.NameAnon]])
      [0;1;2;16]) kinds) [63;64;96]) envs;
  let malformed = [C.Nil;rows [1,C.DMData(key 1)];rows [1,C.DMData(key 2)];
    rows [1,C.DSort C.LZero;1,C.DSort C.LZero];
    rows [1,C.DMData(key 2);2,C.DSort C.LZero]] in
  List.iter (fun kind -> List.iter (fun rows -> List.iter (fun (tr,br) ->
    compare kind 0 (pad 64 base) new_name C.Nil rows tr br;
    compare kind 16 (pad 64 base) new_name C.Nil rows tr br) [1,1;2,1;1,2]) malformed) kinds

let installed kind ty body env = C.Accept(C.Cons({C.decl_hints = C.HintOpaque; decl_name =new_name;decl_params=C.Nil;
  decl_type=ty;decl_value=C.Some body;decl_kind_of=kind},env))
let focused () =
  List.iter (fun size ->
    let env = pad size base in
    if C.use_index (nat 16) env <> (if size >= 64 then C.True else C.False) then failwith "guard changed";
    List.iter (fun (kind,dk) -> equal "positive baseline"
      (C.indexed_dag_admit kind (nat 32) (nat 16) env new_name C.Nil data (key 3) (key 4))
      (installed dk p h env)) [(C.DagDefinition C.HintOpaque),C.DDefinition;C.DagTheorem,C.DTheorem;C.DagOpaque,C.DOpaque])
    [63;64;96];
  let alias = name "AliasP" in
  let alias_decl kind = {(assumed alias prop) with C.decl_kind_of=kind;decl_value=C.Some p} in
  let alias_rows = rows [1,C.DConst(alias,C.Nil);2,C.DConst(h_name,C.Nil)] in
  List.iter (fun dk ->
    let env = pad 64 (alias_decl dk :: base) in
    List.iter (fun kind -> compare kind 32 env new_name C.Nil alias_rows 1 2) kinds;
    let actual = C.indexed_admit_dag_theorem (nat 32) (nat 32) env new_name C.Nil alias_rows (key 1) (key 2) in
    equal "conversion callback alias" actual
      (if dk = C.DDefinition then installed C.DTheorem (C.EConst(alias,C.Nil)) h env
       else C.Reject C.TypeMismatch)) [C.DDefinition;C.DOpaque];
  (* Proper readiness metadata accepts; a single constructor-field forgery
     must keep declining, even with every hash bucket forced to collide. *)
  let nt = C.EConst(C.core_nat_name,C.Nil) in
  let zero = C.NameStr(C.core_nat_name,A.string "zero") and succ = C.NameStr(C.core_nat_name,A.string "succ") in
  let ind = {C.ind_num_params=C.O;ind_num_indices=C.O;ind_all=list [C.core_nat_name];
    ind_ctors=list [zero;succ];ind_num_nested=C.O;ind_is_rec=C.True;
    ind_is_reflexive=C.False;ind_is_unsafe=C.False} in
  let ctor n index fields ty = {(assumed n ty) with C.decl_kind_of=C.DConstructor
    {C.ctor_induct=C.core_nat_name;ctor_index=nat index;ctor_num_params=C.O;
     ctor_num_fields=nat fields;ctor_is_unsafe=C.False}} in
  let literal = C.ELit(C.LitNat(C.Npos C.XH)) in
  let nat_rows = rows [1,C.DConst(C.core_nat_name,C.Nil);2,C.DLit(C.LitNat(C.Npos C.XH))] in
  List.iter (fun forged ->
    let env = pad 64 [{(assumed C.core_nat_name typ) with C.decl_kind_of=C.DInductive ind};
      ctor zero 0 0 nt;ctor succ 1 (if forged then 2 else 1) (C.EPi(C.NameAnon,C.BDefault,nt,nt))] in
    List.iter (fun kind -> compare kind 32 env new_name C.Nil nat_rows 1 2) kinds;
    equal "Nat metadata gate" (C.indexed_admit_dag_definition C.HintOpaque (nat 32) (nat 32) env new_name C.Nil nat_rows (key 1) (key 2))
      (if forged then C.Decline C.UnsupportedExpression else installed C.DDefinition nt literal env)) [false;true];
  (* Distinct structured names with identical rendered dot notation and hash
     suffixes must never alias; same-name declarations must shadow in order. *)
  let a = name "Parent.child" and b = C.NameStr(name "Parent",A.string "child") in
  let rs = rows [1,C.DConst(p_name,C.Nil);2,C.DConst(a,C.Nil);3,C.DConst(b,C.Nil)] in
  let env = pad 64 (assumed a p :: assumed b typ :: base) in
  List.iter (fun kind -> compare kind 16 env new_name C.Nil rs 1 2;
    compare kind 16 env new_name C.Nil rs 1 3) kinds;
  equal "structured name acceptance"
    (C.indexed_admit_dag_theorem (nat 32) (nat 16) env new_name C.Nil rs (key 1) (key 2))
    (installed C.DTheorem p (C.EConst(a,C.Nil)) env);
  equal "structured name mismatch"
    (C.indexed_admit_dag_theorem (nat 32) (nat 16) env new_name C.Nil rs (key 1) (key 3))
    (C.Reject C.TypeMismatch)

let adapter () =
  let env = pad 64 base in
  let wp = Wire.Const(Wire.Str(Wire.Anonymous,"TestP"),[]) in
  let wh = Wire.Const(Wire.Str(Wire.Anonymous,"testProof"),[]) in
  let header : Wire.constant = {name=Wire.Str(Wire.Anonymous,"dagValue");params=[];typ=wp} in
  let cases = [Wire.Theorem(header,wh,[]);Wire.Opaque(header,wh,false,[]);
    Wire.Definition {header;value=wh;safety=Wire.Safe;hints=Wire.Abbrev;all=[header.name]}] in
  List.iter (fun d -> List.iter (fun fuel ->
    equal "large-env syntax-only adapter" (D.admit (nat fuel) env (A.create ()) d)
      (A.admit (nat fuel) env (A.create ()) d)) [0;1;16]) cases

let () =
  let before = Gc.quick_stat () and start = Sys.time () in
  matrix (); focused (); adapter ();
  if !accepted = 0 then failwith "vacuous negatives";
  let after = Gc.quick_stat () in
  Printf.printf "%d indexed DAG FULL result comparisons passed (%d accept results)\n" !count !accepted;
  Printf.printf "cpu_seconds=%.6f allocated_words=%.0f\n" (Sys.time() -. start)
    (after.Gc.minor_words +. after.Gc.major_words -. after.Gc.promoted_words -.
     before.Gc.minor_words -. before.Gc.major_words +. before.Gc.promoted_words);
  Hashtbl.to_seq outcomes |> List.of_seq |> List.sort Stdlib.compare |>
    List.iter (fun (category,n) -> Printf.printf "%s: %d\n" category n)
