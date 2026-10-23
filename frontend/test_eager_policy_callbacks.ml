(* SPDX-License-Identifier: Apache-2.0
   Test-only callback observations of real structural extraction. *)
module C = Eager_policy_native
let rec n = function 0 -> C.O | k -> C.S (n (k - 1))
let rec pos k = if k = 1 then C.XH else if k land 1 = 0 then C.XO (pos (k / 2)) else C.XI (pos (k / 2))
let binary k = if k = 0 then C.N0 else C.Npos (pos k)
let bool b = if b then C.True else C.False
let ascii ch = let k = Char.code ch in let bit i = bool (k land (1 lsl i) <> 0) in
  C.Ascii (bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let string s = let value = ref C.EmptyString in
  for i = String.length s - 1 downto 0 do value := C.String(ascii s.[i],!value) done; !value
let list xs = List.fold_right (fun x tail -> C.Cons(x,tail)) xs C.Nil
let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x :: elements xs
let name s = C.NameStr(C.NameStr(C.NameAnon,string "EagerPolicy"),string s)
let cn s = C.EConst(name s,C.Nil)
let lit k = C.ELit(C.LitNat(binary k))
let b k = C.EBVar(n k)
let pi a body = C.EPi(C.NameAnon,C.BDefault,a,body)
let lam a body = C.ELam(C.NameAnon,C.BDefault,a,body)
let app f a = C.EApp(f,a)
let apps = List.fold_left app
let typ = C.ESort(C.LSucc C.LZero)
let fuel = n 256
let reg = C.HintRegular(binary 7)
let assertions = ref 0
let suites = ref 0
let eq label a b = incr assertions; if a <> b then failwith label
let get label = function C.Accept x -> x | _ -> failwith label
let test label f = (try f () with e -> Printf.eprintf "FAIL %s\n%!" label; raise e);
  incr suites; Printf.printf "PASS %s\n%!" label
let reject label = function C.Reject _ -> incr assertions | _ -> failwith label
let decl nm ty kind = {C.decl_name=nm;decl_params=C.Nil;decl_type=ty;
  decl_value=C.None;decl_kind_of=kind;decl_hints=C.HintOpaque}
let ctor parent nm index fields ty = decl nm ty (C.DConstructor {
  C.ctor_induct=parent;ctor_index=n index;ctor_num_params=C.O;
  ctor_num_fields=n fields;ctor_is_unsafe=C.False})
let admit_type env nm recursive ctors =
  let seed = decl nm typ (C.DInductive {C.ind_num_params=C.O;ind_num_indices=C.O;
    ind_all=list[nm];ind_ctors=list(List.map (fun d -> d.C.decl_name) ctors);
    ind_num_nested=C.O;ind_is_rec=bool recursive;ind_is_reflexive=C.False;ind_is_unsafe=C.False}) in
  let generated = get "derive canonical metadata" (C.derive_inductive fuel env C.Nil C.O
    (list[{C.spec_decl=seed;spec_ctors=list ctors}])) |> elements in
  let select p = list(List.filter (fun d -> p d.C.decl_kind_of) generated) in
  get "admit canonical metadata" (C.admit_inductive_extended fuel env
    (select(function C.DInductive _ -> true | _ -> false))
    (select(function C.DConstructor _ -> true | _ -> false))
    (select(function C.DRecursor _ -> true | _ -> false)))
let nat_env = admit_type C.Nil C.core_nat_name false [
  ctor C.core_nat_name C.core_zero_name 0 0 C.core_nat;
  ctor C.core_nat_name C.core_succ_name 1 1 (pi C.core_nat C.core_nat)]
let bool_type = C.EConst(C.core_bool_name,C.Nil)
let true_term = C.EConst(C.core_true_name,C.Nil)
let false_term = C.EConst(C.core_false_name,C.Nil)
let base_env = admit_type nat_env C.core_bool_name false [
  ctor C.core_bool_name C.core_false_name 0 0 bool_type;
  ctor C.core_bool_name C.core_true_name 1 0 bool_type]
let fold z step major = apps (C.EConst(C.NameStr(C.core_nat_name,string "rec"),
  list[C.LSucc C.LZero])) [lam C.core_nat C.core_nat;z;step;major]
let add_body = lam C.core_nat (lam C.core_nat
  (fold (b 1) (lam C.core_nat(lam C.core_nat(C.primitive_succ(b 0)))) (b 0)))
let add_input body = C.InputDefinition(reg,C.primitive_name C.PNatAdd,C.Nil,
  C.primitive_signature C.PNatAdd,body,C.InputSafe)
let add_env = get "admit authentic Nat.add" (C.admit fuel base_env (add_input add_body))
let eager_ty = pi typ (pi (b 0) (b 1))
let eager_body = lam typ (lam (b 0) (b 0))
let marker = C.EConst(C.eager_reduce_name,C.Nil)
let marked x = apps marker [C.core_nat;x]
let env = get "admit eagerReduce wrapper" (C.admit fuel add_env
  (C.InputDefinition(C.HintAbbrev,C.eager_reduce_name,C.Nil,eager_ty,eager_body,C.InputSafe)))
let env = List.fold_left (fun env (label,ty) -> get "admit fixture axiom"
  (C.admit fuel env (C.InputAxiom(name label,C.Nil,ty,C.False)))) env
  ["L",C.core_nat;"R",C.core_nat;"f",pi C.core_nat C.core_nat]
let add x y = C.primitive_call C.PNatAdd (list[x;y])
let l = cn "L" and r = cn "R"
let t = add l (lit 1) and s = add r (lit 2)
let bound = C.push_binding C.empty_context C.core_nat (C.Some(lit 2))
let free = {C.empty_context with C.free_context=list[C.Pair(name "x",
  {C.binding_type=C.core_nat;binding_value=C.Some(lit 2)})]}
let modes = [C.NormalReduction;C.EagerReduction]
let errors = [C.UnknownConstant;C.UnknownFreeVariable;C.LooseBoundVariable;
  C.UnknownUniverse;C.UniverseArity;C.ExpectedSort;C.ExpectedPi;C.TypeMismatch;
  C.NotDefinitionallyEqual;C.DuplicateDeclaration;C.DuplicateUniverse;
  C.MalformedDeclaration;C.MetaVariable]
let declines = [C.OutOfFuel;C.UnsupportedExpression;C.UnsupportedDeclaration]
let faults () = List.map (fun e -> C.Reject e) errors @ List.map (fun d -> C.Decline d) declines
let cast_fault = function C.Reject e -> C.Reject e | C.Decline d -> C.Decline d | C.Accept _ -> assert false
type event = W of C.expr | Core of C.bool * C.expr | Eq of C.expr * C.expr
  | Eager of C.expr * C.expr | Infer of C.expr | InferType of C.expr
let make_methods mode g whnf defeq events =
  let record actual event = eq "context preserved" actual g; events := !events @ [event] in
  {C.method_mode=mode;
   infer_method=(fun actual e -> record actual (Infer e); C.Reject C.ExpectedSort);
   infer_type_method=(fun actual e -> record actual (InferType e); C.Reject C.ExpectedSort);
   whnf_method=(fun actual e -> record actual (W e); whnf e);
   whnf_core_method=(fun cheap actual e -> record actual (Core(cheap,e)); C.Reject C.ExpectedPi);
   defeq_method=(fun actual a b -> record actual (Eq(a,b)); defeq a b);
   eager_defeq_method=(fun actual a b -> record actual (Eager(a,b)); defeq a b)}
let yes _ _ = C.Accept C.True
let identity e = C.Accept e
let success = C.Accept(C.ConversionDone C.True)
let resolver environment = let lookup = C.prepare_lookup (fun _ -> C.N0) environment in
  fun nm _ -> lookup nm
let lazy_run ?(rounds=2) ?(budget=256) ?(environment=env) mode indexed g whnf defeq left right =
  let events = ref [] in let m = make_methods mode g whnf defeq events in
  let result = if indexed then C.Accessor.core_lazy_delta (resolver environment)
    (n rounds) m (n budget) environment C.Nil g left right
    else C.core_lazy_delta (n rounds) m (n budget) environment C.Nil g left right in
  result,!events
let shortcut_run ?(environment=env) mode indexed g whnf left right =
  let events = ref [] in let m = make_methods mode g whnf yes events in
  let result = if indexed then C.Accessor.core_true_shortcut (resolver environment) m environment g left right
    else C.core_true_shortcut m environment g left right in result,!events
let both f = List.iter f [false;true]
let left_success e = if e=l || e=b 0 || e=C.EFVar(name "x") then C.Accept(lit 2)
  else if e=r then C.Reject C.UnknownFreeVariable else C.Accept e

let () =
  test "real-admission-and-authentication" (fun () ->
    eq "Nat canonical" (C.core_nat_ready env) C.True;
    eq "Bool canonical" (C.core_bool_ready env) C.True;
    eq "actual primitive equations" (C.primitive_authenticated fuel env C.PNatAdd) (C.Accept C.Tt);
    reject "false add body rejected" (C.admit fuel base_env (add_input(lam C.core_nat(lam C.core_nat(b 1)))));
    List.iter (fun mode -> let m = C.checker_mode mode fuel env C.Nil in
      eq "closed add evaluates" (m.C.defeq_method C.empty_context (add (lit 2) (lit 1)) (lit 3)) (C.Accept C.True);
      eq "typed marked expression" (m.C.infer_method C.empty_context (app (cn "f") (marked (lit 2))))
        (C.Accept C.core_nat)) modes);
  test "external-locals-binders-and-malformed-scopes" (fun () ->
    List.iter (fun (e,expected) -> eq "localness" (C.has_external_local e) (bool expected)) [
      b 0,true; C.EFVar(name "x"),true; lam C.core_nat (b 0),false;
      lam C.core_nat (b 1),true;lam (b 0) (b 0),true;
      C.ELet(C.NameAnon,C.core_nat,b 0,b 0,C.False),true;
      C.ELet(C.NameAnon,C.core_nat,lit 2,b 0,C.True),false;
      C.EMData(b 0),true;C.EProj(name "p",C.O,b 0),true;l,false];
    List.iter (fun mode -> let m = C.checker_mode mode fuel env C.Nil in
      eq "malformed scope still rejects" (m.C.infer_method C.empty_context (b 0)) (C.Reject C.LooseBoundVariable);
      eq "missing FVar still rejects" (m.C.infer_method C.empty_context (C.EFVar(name "absent")))
        (C.Reject C.UnknownFreeVariable)) modes);
  test "normal-one-open-and-both-open-skip-both-probes" (fun () -> both (fun indexed ->
    List.iter (fun (g,a,c) -> eq "exact congruence fallback no Nat callbacks"
      (lazy_run C.NormalReduction indexed g (fun _ -> failwith "open Nat probe") yes (add a (lit 1)) (add c (lit 2)))
      (success,[Eq(lit 1,lit 2);Eq(a,c)])) [
        C.empty_context,b 0,r;bound,b 0,r;free,C.EFVar(name "x"),r;
        bound,l,b 0;bound,b 0,b 1;C.empty_context,C.EMData(b 0),r]));
  test "eager-open-left-short-circuit-and-closed-in-nonempty-context" (fun () -> both (fun indexed ->
    List.iter (fun (mode,g,a) -> eq "left success skips right and congruence"
      (lazy_run mode indexed g left_success yes (add a (lit 1)) s)
      (success,[W a;W(lit 1);Eq(lit 3,s)])) [
        C.EagerReduction,bound,b 0;C.EagerReduction,free,C.EFVar(name "x");
        C.NormalReduction,bound,l;C.EagerReduction,bound,l]));
  test "closed-probe-right-success-both-none-and-error-priority" (fun () -> both (fun indexed ->
    List.iter (fun mode ->
      eq "right success" (lazy_run mode indexed C.empty_context
        (fun e -> if e=r then C.Accept(lit 5) else C.Accept e) yes t s)
        (success,[W l;W(lit 1);W r;W(lit 2);Eq(t,lit 7)]);
      eq "both none" (lazy_run mode indexed C.empty_context identity yes t s)
        (success,[W l;W(lit 1);W r;W(lit 2);Eq(lit 1,lit 2);Eq(l,r)]);
      List.iter (fun fault ->
        eq "left first error" (lazy_run mode indexed C.empty_context (fun _ -> fault) yes t s)
          (cast_fault fault,[W l]);
        eq "left second error" (lazy_run mode indexed C.empty_context
          (fun e -> if e=l then C.Accept(lit 2) else fault) yes t s)
          (cast_fault fault,[W l;W(lit 1)]);
        eq "right error after both left callbacks" (lazy_run mode indexed C.empty_context
          (fun e -> if e=r then fault else C.Accept e) yes t s)
          (cast_fault fault,[W l;W(lit 1);W r])) (faults())) modes));
  test "guarded-asymmetric-true-and-canonical-authorization" (fun () -> both (fun indexed ->
    eq "normal open no WHNF" (shortcut_run C.NormalReduction indexed bound (fun _ -> failwith "open true")
      (b 0) true_term) (C.Accept C.False,[]);
    List.iter (fun (mode,g,a) -> eq "eligible left normalizes alone"
      (shortcut_run mode indexed g (fun _ -> C.Accept true_term) a true_term)
      (C.Accept C.True,[W a])) [C.NormalReduction,bound,l;C.EagerReduction,bound,b 0];
    List.iter (fun right -> eq "only exact right true" (shortcut_run C.EagerReduction indexed bound
      (fun _ -> failwith "wrong rhs true") true_term right) (C.Accept C.False,[]))
      [false_term;l;C.EConst(C.core_true_name,list[C.LZero]);C.EMData true_term];
    eq "nontrue normal form" (shortcut_run C.NormalReduction indexed C.empty_context
      (fun _ -> C.Accept false_term) l true_term) (C.Accept C.False,[W l]);
    List.iter (fun bad_env -> eq "unready Bool never authorizes" (shortcut_run ~environment:bad_env
      C.EagerReduction indexed bound (fun _ -> failwith "unauthorized Bool") (b 0) true_term)
      (C.Accept C.False,[])) [C.Nil;C.Cons(decl C.core_bool_name typ C.DAssumption,env);
        C.Cons(decl C.core_true_name bool_type (C.DUnsafe C.DDefinition),env)];
    List.iter (fun fault -> eq "shortcut error retained" (shortcut_run C.EagerReduction indexed bound
      (fun _ -> fault) (b 0) true_term) (cast_fault fault,[W(b 0)])) (faults())));
  test "true-shortcut-error-before-inference-and-nontrue-fallback" (fun () ->
    List.iter (fun mode -> List.iter (fun fault ->
      let events = ref [] in let m = make_methods mode C.empty_context (fun _ -> fault) yes events in
      eq "early WHNF error" (C.defeq_step m fuel env C.Nil C.empty_context l true_term) (cast_fault fault);
      eq "no inference before early error" !events [W l];
      let events = ref [] in let m = make_methods mode C.empty_context (fun _ -> C.Accept false_term) yes events in
      eq "nontrue resumes existing proof-irrel" (C.defeq_step m fuel env C.Nil C.empty_context l true_term)
        (C.Reject C.ExpectedSort);
      eq "uses inference-only callback" !events [W l;InferType l]) (faults())) modes);
  test "exact-marker-scope-orientation-and-argument-error-order" (fun () ->
    let events = ref [] in let m = make_methods C.NormalReduction C.empty_context identity yes events in
    eq "marked uses upstream orientation" (C.application_type_defeq m C.empty_context (marked (lit 2))
      C.core_nat bool_type) (C.Accept C.True);
    eq "marked trace" !events [Eager(C.core_nat,bool_type)];
    let negatives = [marker;app marker C.core_nat;app (marked (lit 2)) (lit 3);
      C.EMData(marked(lit 2));apps (cn "alias") [C.core_nat;lit 2]] in
    List.iter (fun argument -> events := [];
      eq "unmarked result" (C.application_type_defeq m C.empty_context argument C.core_nat bool_type) (C.Accept C.True);
      eq "unmarked uses upstream orientation" !events [Eq(C.core_nat,bool_type)]) negatives;
    events := [];
    eq "checked marked inference" (C.infer_step m fuel env C.Nil C.True C.empty_context (app (cn "f") (marked(lit 2))))
      (C.Accept C.core_nat);
    eq "exactly one override after argument checks" (List.filter (function Eq _ | Eager _ -> true | _ -> false) !events)
      [Eq(typ,typ);Eq(C.core_nat,C.core_nat);Eager(C.core_nat,C.core_nat)];
    events := [];
    eq "argument error before override" (C.infer_step m fuel env C.Nil C.True C.empty_context
      (app (cn "f") (marked(cn "missing")))) (C.Reject C.UnknownConstant);
    eq "no override on bad argument" (List.exists (function Eager _ -> true | _ -> false) !events) false;
    List.iter (fun fault -> let events = ref [] in
      let m = make_methods C.NormalReduction C.empty_context identity yes events in
      let m = {m with C.eager_defeq_method=(fun _ _ _ -> fault)} in
      eq "override errors propagate" (C.infer_step m fuel env C.Nil C.True C.empty_context
        (app (cn "f") (marked(lit 2)))) (cast_fault fault)) (faults());
    let unsafe = C.Cons(decl C.eager_reduce_name eager_ty (C.DUnsafe C.DDefinition),env) in
    eq "unsafe wrapper fails before override" (C.infer_step m fuel unsafe C.Nil C.True C.empty_context
      (app (cn "f") (marked(lit 2)))) (C.Reject C.MalformedDeclaration));
  test "application-upstream-order-full-results-and-callback-selection" (fun () ->
    let outcomes = [C.Accept C.True;C.Accept C.False] @ List.map cast_fault (faults()) in
    List.iter (fun mode -> List.iter (fun g -> List.iter (fun answer ->
      let events = ref [] in
      let ordered a b = eq "domain first" a C.core_nat; eq "argument type second" b bool_type; answer in
      let m = make_methods mode g identity ordered events in
      List.iter (fun (argument,event) -> events := [];
        eq "complete callback result retained" (C.application_type_defeq m g argument C.core_nat bool_type) answer;
        eq "one selected callback in upstream order" !events [event])
        [true_term,Eq(C.core_nat,bool_type);C.EMData(marked(lit 2)),Eq(C.core_nat,bool_type);
         marked(lit 2),Eager(C.core_nat,bool_type)];
      eq "method mode remains unchanged" m.C.method_mode mode) outcomes) [C.empty_context;bound]) modes);
  test "application-ordinary-accessor-error-order-and-unchecked-bypass" (fun () ->
    let function_type = pi C.core_nat C.core_nat in
    let outcomes = [C.Accept C.True;C.Accept C.False] @ List.map cast_fault (faults()) in
    let expected = function C.Accept C.True -> C.Accept C.core_nat
      | C.Accept C.False -> C.Reject C.TypeMismatch | fault -> cast_fault fault in
    List.iter (fun mode -> List.iter (fun g -> both (fun indexed ->
      let run m checking e = if indexed then
        C.Accessor.infer_step (resolver env) m fuel env C.Nil checking g e
        else C.infer_step m fuel env C.Nil checking g e in
      List.iter (fun answer ->
        let events = ref [] in let m = make_methods mode g identity (fun a b ->
          eq "checked domain first" a C.core_nat; eq "checked argument type second" b bool_type; answer) events in
        eq "checked comparison retains full result" (run m C.True (app (cn "f") true_term)) (expected answer);
        eq "WHNF then one regular comparison" !events [W function_type;Eq(C.core_nat,bool_type)]) outcomes;
      let events = ref [] in let m = make_methods mode g identity (fun _ _ -> failwith "unexpected comparison") events in
      List.iter (fun (term,result,trace) -> events := [];
        eq "application precheck result" (run m C.True term) result;
        eq "application precheck ordering" !events trace)
        [app (cn "missing") true_term,C.Reject C.UnknownConstant,[];
         app (cn "f") (cn "missing"),C.Reject C.UnknownConstant,[W function_type];
         app true_term (cn "missing"),C.Reject C.ExpectedPi,[W bool_type];
         app (cn "f") (b 99),C.Reject C.LooseBoundVariable,[W function_type]];
      events := [];
      eq "inference-only still skips bad argument and comparison"
        (run m C.False (app (cn "f") (cn "missing"))) (C.Accept C.core_nat);
      eq "inference-only WHNF remains" !events [W function_type];
      List.iter (fun fault ->
        let events = ref [] in let m = make_methods mode g (fun _ -> fault)
          (fun _ _ -> failwith "comparison before function normalization") events in
        eq "function normalization fault precedes argument fault"
          (run m C.True (app (cn "f") (cn "missing"))) (cast_fault fault);
        eq "first error callback only" !events [W function_type]) (faults()))) [C.empty_context;bound]) modes;
    List.iter (fun mode ->
      let real = C.checker_mode mode fuel env C.Nil in
      eq "actual checker rejects ill-typed unmarked application"
        (real.C.infer_method C.empty_context (app (cn "f") true_term)) (C.Reject C.TypeMismatch);
      let zero = C.checker_mode mode C.O env C.Nil in
      eq "unmarked comparison cannot replenish zero depth"
        (C.application_type_defeq zero C.empty_context true_term C.core_nat bool_type) (C.Decline C.OutOfFuel)) modes);
  test "application-dag-callback-order-and-full-result-refinement" (fun () ->
    let rows = list [C.Pair(pos 1,C.DConst(name "f",C.Nil));
      C.Pair(pos 2,C.DConst(C.core_true_name,C.Nil));C.Pair(pos 3,C.DApp(pos 1,pos 2));
      C.Pair(pos 4,C.DConst(name "missing",C.Nil));C.Pair(pos 5,C.DApp(pos 1,pos 4))] in
    let arena = get "application-order DAG" (C.arena_build C.empty_arena rows) in
    let lookup = C.prepare_lookup (fun _ -> C.N0) env in
    let outcomes = [C.Accept C.True;C.Accept C.False] @ List.map cast_fault (faults()) in
    let function_type = pi C.core_nat C.core_nat in
    List.iter (fun mode -> List.iter (fun g -> List.iter (fun budget ->
      List.iter (fun implementation ->
        let run m checking id = let q = C.Pair(pos id,C.Nil) in
          match implementation with
          | 0 -> C.run_memo_infer m fuel env C.Nil g arena (n budget) checking q
          | 1 -> C.run_memo_infer0 m fuel env C.Nil g arena (n budget) checking q
          | _ -> C.run_memo_infer1 lookup m fuel env C.Nil g arena (n budget) checking q in
        List.iter (fun answer ->
          let events = ref [] in let m = make_methods mode g identity (fun a b ->
            eq "DAG domain first" a C.core_nat; eq "DAG argument type second" b bool_type; answer) events in
          let ordinary = C.infer_step m fuel env C.Nil C.True g (app (cn "f") true_term) in
          events := [];
          eq "DAG complete result equals NEW ordinary" (run m C.True 3) ordinary;
          eq "DAG WHNF then single ordered comparison" !events [W function_type;Eq(C.core_nat,bool_type)]) outcomes;
        let events = ref [] in let m = make_methods mode g identity (fun _ _ -> failwith "bad DAG comparison") events in
        eq "DAG argument fault before comparison" (run m C.True 5) (C.Reject C.UnknownConstant);
        eq "DAG argument fault trace" !events [W function_type];
        events := [];
        eq "DAG unchecked argument bypass" (run m C.False 5) (C.Accept C.core_nat);
        eq "DAG unchecked trace" !events [W function_type]) [0;1;2]) [0;1;16]) [C.empty_context;bound]) modes);
  test "inherited-mode-inference-only-and-no-sibling-leak" (fun () ->
    List.iter (fun mode -> let events = ref [] in let m = make_methods mode C.empty_context identity yes events in
      let io = C.inference_only m in let aio = C.Accessor.inference_only m in
      List.iter (fun view -> eq "view mode inherited" view.C.method_mode mode;
        events := []; ignore(view.C.eager_defeq_method C.empty_context l r);
        eq "view retains override" !events [Eager(l,r)]) [io;aio];
      ignore(m.C.eager_defeq_method C.empty_context l r);
      eq "original mode not mutated" m.C.method_mode mode;
      events := []; ignore(C.application_type_defeq m C.empty_context (lit 2) C.core_nat C.core_nat);
      eq "later unmarked call stays regular" !events [Eq(C.core_nat,C.core_nat)]) modes);
  test "zero-depth-and-no-replenishment-inherited-through-real-methods" (fun () ->
    let cases = [C.empty_context,t,s;bound,add(b 0)(lit 1),lit 3;
      free,add(C.EFVar(name "x"))(lit 1),lit 3;C.empty_context,cn "missing",true_term;
      C.empty_context,lam C.core_nat (b 0),lam C.core_nat (b 1)] in
    List.iter (fun mode -> List.iter (fun budget ->
      let normal = C.checker_mode mode (n budget) env C.Nil in
      let eager = C.checker_mode C.EagerReduction (n budget) env C.Nil in
      List.iter (fun (g,a,c) -> eq "override equals eager at unchanged depth"
        (normal.C.eager_defeq_method g a c) (eager.C.defeq_method g a c)) cases;
      if budget=0 then begin
        eq "zero override cannot quick-accept" (normal.C.eager_defeq_method C.empty_context l l) (C.Decline C.OutOfFuel);
        eq "zero marked branch cannot replenish" (C.application_type_defeq normal C.empty_context (marked(lit 2)) l l)
          (C.Decline C.OutOfFuel)
      end) [0;1;2;8;32]) modes);
  test "full-whnf-nat-remains-ungated-and-contextual" (fun () ->
    List.iter (fun mode -> let m = C.checker_mode mode fuel env C.Nil in
      List.iter (fun (g,x) -> eq "full WHNF open Nat" (m.C.whnf_method g (add x (lit 1))) (C.Accept(lit 3)))
        [bound,b 0;free,C.EFVar(name "x")]) modes);
  test "prepared-collisions-all-methods-and-both-mode-full-results" (fun () ->
    List.iter (fun mode -> List.iter (fun budget ->
      let lookup = C.prepare_lookup (fun _ -> C.N0) env in
      let a = C.checker_mode mode (n budget) env C.Nil in
      let c = C.checker_with_lookup_mode mode (n budget) env lookup C.Nil in
      eq "prepared captures mode" c.C.method_mode mode;
      List.iter (fun (g,e) ->
        eq "checked inference exact" (a.C.infer_method g e) (c.C.infer_method g e);
        eq "inference-only exact" (a.C.infer_type_method g e) (c.C.infer_type_method g e);
        eq "WHNF exact" (a.C.whnf_method g e) (c.C.whnf_method g e);
        List.iter (fun cheap -> eq "core WHNF exact" (a.C.whnf_core_method cheap g e) (c.C.whnf_core_method cheap g e)) [C.True;C.False];
        eq "defeq exact" (a.C.defeq_method g e (lit 3)) (c.C.defeq_method g e (lit 3));
        eq "eager override exact" (a.C.eager_defeq_method g e (lit 3)) (c.C.eager_defeq_method g e (lit 3)))
        [C.empty_context,marked(lit 2);bound,add(b 0)(lit 1);C.empty_context,b 0;
         C.empty_context,C.EMVar(name "bad");C.empty_context,cn "missing"])
      [0;1;2;8;32]) modes);
  test "dag-reference-indexed-cache-budget-zero-and-mode-isolation" (fun () ->
    let rows = list [C.Pair(pos 1,C.DConst(C.core_nat_name,C.Nil));
      C.Pair(pos 2,C.DConst(C.eager_reduce_name,C.Nil)); C.Pair(pos 3,C.DLit(C.LitNat(binary 2)));
      C.Pair(pos 4,C.DApp(pos 2,pos 1));C.Pair(pos 5,C.DApp(pos 4,pos 3));
      C.Pair(pos 6,C.DConst(name "f",C.Nil));C.Pair(pos 7,C.DApp(pos 6,pos 5));
      C.Pair(pos 8,C.DBVar(n 0));C.Pair(pos 9,C.DApp(pos 4,pos 8));
      C.Pair(pos 10,C.DApp(pos 6,pos 9));C.Pair(pos 11,C.DLam(C.NameAnon,C.BDefault,pos 1,pos 10))] in
    let arena = get "build checked DAG" (C.arena_build C.empty_arena rows) in
    List.iter (fun mode -> List.iter (fun depth -> let lookup = C.prepare_lookup (fun _ -> C.N0) env in
      let ordinary = C.checker_mode mode (n depth) env C.Nil in
      let prepared = C.checker_with_lookup_mode mode (n depth) env lookup C.Nil in
      List.iter (fun budget -> List.iter (fun checking -> List.iter (fun id ->
        let q = C.Pair(pos id,C.Nil) in
        let entry = get "decode query" (C.scope_ref arena.C.arena_scope (pos id)) in
        let expected = C.infer_step ordinary (n depth) env C.Nil checking C.empty_context entry.C.scope_expr in
        eq "ordinary DAG full result" (C.run_memo_infer ordinary (n depth) env C.Nil C.empty_context arena (n budget) checking q) expected;
        eq "reference DAG full result" (C.run_memo_infer0 ordinary (n depth) env C.Nil C.empty_context arena (n budget) checking q) expected;
        eq "prepared DAG full result" (C.run_memo_infer1 lookup prepared (n depth) env C.Nil C.empty_context arena (n budget) checking q) expected)
        [7;8;10;11]) [C.True;C.False]) [0;1;16]) [0;1;8;32])
      [C.NormalReduction;C.EagerReduction;C.NormalReduction]);
  Printf.printf "EAGER_POLICY_CALLBACKS_PASS suites=%d assertions=%d\n%!" !suites !assertions
