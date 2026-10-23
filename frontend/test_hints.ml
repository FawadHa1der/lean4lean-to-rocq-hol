(* Test-only controls. Expected observations never enter the runtime request. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
module P = Persistent_adapter
module F = Full_result
let assertions = ref 0
let equal label a b = incr assertions; if a <> b then failwith label
let truth label b = equal label b true
let list xs = A.list Fun.id xs
let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x :: elements xs
let nat = A.nat
let fuel = nat 256
let get label = function
  | C.Accept x -> x
  | C.Reject r -> failwith (label ^ ": " ^ A.reject_reason r)
  | C.Decline r -> failwith (label ^ ": " ^ A.decline_reason r)
let wn s = Wire.Str(Wire.Anonymous,s)
let cn s = A.name (A.create ()) (wn s)
let wp = Wire.Sort Wire.Zero
let wt = Wire.Sort (Wire.Succ Wire.Zero)
let cp = C.ESort C.LZero
let ct = C.ESort(C.LSucc C.LZero)
let huge = Z.shift_left Z.one 256
let hints = [Wire.OpaqueHint;Wire.Abbrev;Wire.Regular Z.zero;Wire.Regular Z.one;
             Wire.Regular huge;Wire.Regular(Z.succ huge)]
let definition ?(mode=Wire.Safe) ?(ty=wt) ?(body=wp) name hint =
  Wire.Definition {Wire.header={name=wn name;params=[];typ=ty};value=body;
    safety=mode;hints=hint;all=[wn name]}
let assumed n = {C.decl_name=n;decl_params=C.Nil;decl_type=ct;
  decl_value=C.None;decl_kind_of=C.DAssumption;decl_hints=C.HintOpaque}
let padding n = list (List.init n (fun i -> assumed (cn ("pad" ^ string_of_int i))))
let stored env n = match C.find_decl n env with C.Some d -> d | C.None -> failwith "missing stored declaration"
let projected hash = function
  | C.Accept s -> C.Accept(C.state_environment hash s)
  | C.Reject r -> C.Reject r | C.Decline r -> C.Decline r
let hashes = [C.suffix_bitfold8;(fun _ -> C.N0)]
let full_equal label a b = equal label (F.result a) (F.result b)

let () =
  List.iter (fun z ->
    let json = Yojson.Safe.from_string ("{\"regular\":" ^ Z.to_string z ^ "}") in
    equal "parser preserves exact height" (Wire.hints 1 json) (Wire.Regular z);
    match A.hints (Wire.hints 1 json) with
    | C.HintRegular n -> equal "transport preserves exact height" (F.binary n) (`String (Z.to_string z))
    | _ -> failwith "regular hint lost") [Z.zero;Z.one;huge;Z.succ huge;Z.shift_left Z.one 4096];
  truth "negative height rejected by parser"
    (try ignore(Wire.hints 1 (`Assoc ["regular",`Int (-1)])); false with Wire.Error _ -> true);
  truth "missing hint rejected by parser"
    (try ignore(Wire.hints 1 `Null); false with Wire.Error _ -> true);
  truth "negative direct adapter input not silently wrapped"
    (try ignore(A.hints (Wire.Regular (Z.of_int (-1)))); false with Invalid_argument _ -> true);
  List.iter (fun hint ->
    List.iter (fun count ->
      let env = padding count in
      List.iter (fun f ->
        List.iter (fun body ->
          let st = A.create () in
          let input = definition ~body "tested" hint in
          let ordinary = A.admit (nat f) env st input in
          full_equal "DAG vs new ordinary complete result" (D.admit (nat f) env st input) ordinary;
          List.iter (fun hash ->
            let state = C.seed_state hash env in
            let result = C.state_step hash (nat f) state (P.request st input) in
            full_equal "persistent vs new ordinary complete result" (projected hash result) ordinary;
            equal "original state remains intact" (C.state_environment hash state) env)
            hashes;
          if f = 64 && body = wp then begin
            let result = get "positive admitted baseline" ordinary in
            let d = stored result (cn "tested") in
            equal "accepted hint retained" d.C.decl_hints (A.hints hint);
            equal "accepted effective hint retained" (C.effective_hints d) (A.hints hint)
          end)
          [wp;wt;Wire.BVar Z.zero;Wire.Const(wn "missing",[])])
        [0;1;8;64]) [0;63;64;65]) hints;
  List.iter (fun hint ->
    List.iter (fun mode ->
      let syntax = A.create () in
      let input = definition ~mode "restricted" hint in
      let state = get "restricted positive" (P.State.admit fuel P.State.initial syntax input) in
      let d = stored (P.State.environment state) (cn "restricted") in
      equal "safety admission retains hint" d.C.decl_hints (A.hints hint);
      equal "restricted effective hint remains opaque" (C.effective_hints d) C.HintOpaque;
      equal "unsafe checking view reveals definition hint"
        (C.effective_hints (C.checking_view C.InputUnsafe d)) (A.hints hint))
      [Wire.Unsafe;Wire.Partial];
    let syntax = A.create () in
    let defs = List.map (fun name -> match definition ~mode:Wire.Unsafe name hint with
      | Wire.Definition d -> d | _ -> assert false) ["mutualA";"mutualB"] in
    let state = get "mutual positive" (P.State.mutual fuel P.State.initial syntax defs) in
    List.iter (fun n -> equal "mutual hint retained"
      (stored (P.State.environment state) (cn n)).C.decl_hints (A.hints hint)) ["mutualA";"mutualB"])
    hints

let pi a b = C.EPi(C.NameAnon,C.BDefault,a,b)
let lam a b = C.ELam(C.NameAnon,C.BDefault,a,b)
let ind n ctors = {(assumed n) with C.decl_kind_of=C.DInductive
  {C.ind_num_params=C.O;ind_num_indices=C.O;ind_all=list[n];ind_ctors=list ctors;
   ind_num_nested=C.O;ind_is_rec=C.False;ind_is_reflexive=C.False;ind_is_unsafe=C.False}}
let ctor n index fields ty = {(assumed n) with C.decl_type=ty;decl_kind_of=C.DConstructor
  {C.ctor_induct=C.core_nat_name;ctor_index=nat index;ctor_num_params=C.O;
   ctor_num_fields=nat fields;ctor_is_unsafe=C.False}}
let () =
  let spec = {C.spec_decl=ind C.core_nat_name [C.core_zero_name;C.core_succ_name];
    spec_ctors=list[ctor C.core_zero_name 0 0 C.core_nat;
      ctor C.core_succ_name 1 1 (pi C.core_nat C.core_nat)]} in
  let generated = elements (get "Nat derive baseline" (C.derive_inductive fuel C.Nil C.Nil C.O (list[spec]))) in
  let select p = list(List.filter (fun d -> p d.C.decl_kind_of) generated) in
  let env = get "Nat checked metadata baseline" (C.admit_inductive_extended fuel C.Nil
    (select(function C.DInductive _ -> true | _ -> false))
    (select(function C.DConstructor _ -> true | _ -> false))
    (select(function C.DRecursor _ -> true | _ -> false))) in
  let env = get "Char alias baseline" (C.admit fuel env
    (C.InputDefinition(C.HintOpaque,C.core_char_name,C.Nil,ct,C.core_nat,C.InputSafe))) in
  List.iter (fun hint ->
    let syntax = A.create () in
    let n = Wire.Str(wn "Char","ofNat") in
    let input = Wire.Definition {Wire.header={name=n;params=[];
      typ=Wire.Pi(Wire.Anonymous,Wire.Const(wn "Nat",[]),Wire.Const(wn "Char",[]),Wire.Explicit)};
      value=Wire.Lam(Wire.Anonymous,Wire.Const(wn "Nat",[]),Wire.BVar Z.zero,Wire.Explicit);
      hints=hint;safety=Wire.Safe;all=[n]} in
    let ordinary = A.admit fuel env syntax input in
    let admitted = get "primitive authenticated baseline" ordinary in
    let d = stored admitted C.core_char_of_nat in
    equal "primitive classification retained" d.C.decl_kind_of (C.DPrimitive C.PCharOfNat);
    equal "primitive original hint retained" d.C.decl_hints (A.hints hint);
    equal "primitive effective hint retained" (C.effective_hints d) (A.hints hint);
    full_equal "primitive DAG complete result" (D.admit fuel env syntax input) ordinary;
    List.iter (fun hash ->
      let padded = list (elements (padding 65) @ elements env) in
      let ordinary = A.admit fuel padded syntax input in
      let indexed = projected hash (C.state_step hash fuel (C.seed_state hash padded) (P.request syntax input)) in
      full_equal "primitive forced-index complete result" indexed ordinary) hashes) hints;
  (* Compare accessor/collision paths on complete conversion results. *)
  List.iter (fun left -> List.iter (fun right ->
    let d n hint body = {(assumed (cn n)) with C.decl_value=C.Some body;
      decl_kind_of=C.DDefinition;decl_hints=A.hints hint} in
    let ds = [d "L" left cp;d "R" right (C.EConst(cn "L",C.Nil))] in
    List.iter (fun count ->
      let env = list(ds @ elements (padding count)) in
      let l = C.EConst(cn "L",C.Nil) and r = C.EConst(cn "R",C.Nil) in
      List.iter (fun f ->
        let ordinary = C.defeq (nat f) env C.Nil C.empty_context l r in
        List.iter (fun hash -> equal "prepared conversion full result"
          (C.prepared_defeq (C.prepare_lookup hash env) (nat f) env C.Nil C.empty_context l r)
          ordinary) hashes) [0;1;8;32]) [0;63;64;65]) hints) hints;
  Printf.printf "HINTS_NATIVE_PASS assertions=%d\n%!" !assertions
