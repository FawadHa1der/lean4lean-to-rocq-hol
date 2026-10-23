(* SPDX-License-Identifier: Apache-2.0
   Test-only callback instrumentation of actual extraction. No runtime hooks. *)
module C = Lean_arena
module A = Rocq_adapter
let n = A.nat
let list xs = A.list Fun.id xs
let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x :: elements xs
let name s = C.NameStr(C.NameStr(C.NameAnon,A.string "NatProbe"),A.string s)
let cn s = C.EConst(name s,C.Nil)
let lit k = C.ELit(C.LitNat(A.binary(Z.of_int k)))
let pi a b = C.EPi(C.NameAnon,C.BDefault,a,b)
let lam a b = C.ELam(C.NameAnon,C.BDefault,a,b)
let app f a = C.EApp(f,a)
let apps f xs = List.fold_left app f xs
let typ = C.ESort(C.LSucc C.LZero)
let reg = C.HintRegular(A.binary(Z.of_int 7))
let assertions = ref 0
let eq label a b = incr assertions; if a <> b then failwith label
let get label = function C.Accept x -> x | _ -> failwith label
let suites = ref 0
let test label f =
  (try f () with exn -> Printf.eprintf "FAIL %s\n%!" label; raise exn);
  incr suites; Printf.printf "PASS %s\n%!" label
let decl nm ty kind = {C.decl_name=nm;decl_params=C.Nil;decl_type=ty;
  decl_value=C.None;decl_kind_of=kind;decl_hints=C.HintOpaque}

(* Positive metadata is derived and admitted, never inserted as a trusted tag. *)
let fuel = n 256
let seed = decl C.core_nat_name typ (C.DInductive {
  C.ind_num_params=C.O;ind_num_indices=C.O;ind_all=list[C.core_nat_name];
  ind_ctors=list[C.core_zero_name;C.core_succ_name];ind_num_nested=C.O;
  ind_is_rec=C.False;ind_is_reflexive=C.False;ind_is_unsafe=C.False})
let ctor nm index fields ty = decl nm ty (C.DConstructor {
  C.ctor_induct=C.core_nat_name;ctor_index=n index;ctor_num_params=C.O;
  ctor_num_fields=n fields;ctor_is_unsafe=C.False})
let generated = get "derive Nat" (C.derive_inductive fuel C.Nil C.Nil C.O
  (list[{C.spec_decl=seed;spec_ctors=list[
    ctor C.core_zero_name 0 0 C.core_nat;
    ctor C.core_succ_name 1 1 (pi C.core_nat C.core_nat)]}])) |> elements
let select p = list(List.filter (fun d -> p d.C.decl_kind_of) generated)
let nat_env = get "admit Nat" (C.admit_inductive_extended fuel C.Nil
  (select(function C.DInductive _ -> true | _ -> false))
  (select(function C.DConstructor _ -> true | _ -> false))
  (select(function C.DRecursor _ -> true | _ -> false)))
let b i = C.EBVar(n i)
let fold z step major = apps (C.EConst(C.NameStr(C.core_nat_name,A.string "rec"),
  list[C.LSucc C.LZero])) [lam C.core_nat C.core_nat;z;step;major]
let add_body = lam C.core_nat (lam C.core_nat
  (fold (b 1) (lam C.core_nat(lam C.core_nat(C.primitive_succ(b 0)))) (b 0)))
let add_input body = C.InputDefinition(reg,C.primitive_name C.PNatAdd,C.Nil,
  C.primitive_signature C.PNatAdd,body,C.InputSafe)
let add_env = get "admit authenticated Nat.add" (C.admit fuel nat_env (add_input add_body))
let env = List.fold_left (fun e s -> get "admit Nat argument axiom"
  (C.admit fuel e (C.InputAxiom(name s,C.Nil,C.core_nat,C.False)))) add_env ["L";"R"]
let add a b = C.primitive_call C.PNatAdd (list[a;b])
let l = cn "L" and r = cn "R"
let t = add l (lit 1) and s = add r (lit 2)
type event = Whnf of C.expr | Eq of C.expr * C.expr | Core of C.bool * C.expr
let success = C.Accept(C.ConversionDone C.True)
let bool_done = function
  | C.Accept b -> C.Accept(C.ConversionDone b)
  | C.Reject e -> C.Reject e | C.Decline d -> C.Decline d
let errors = [C.UnknownConstant;C.UnknownFreeVariable;C.LooseBoundVariable;
  C.UnknownUniverse;C.UniverseArity;C.ExpectedSort;C.ExpectedPi;C.TypeMismatch;
  C.NotDefinitionallyEqual;C.DuplicateDeclaration;C.DuplicateUniverse;
  C.MalformedDeclaration;C.MetaVariable]
let declines = [C.OutOfFuel;C.UnsupportedExpression;C.UnsupportedDeclaration]
let faults () = List.map (fun e -> C.Reject e) errors @ List.map (fun d -> C.Decline d) declines
let both f = List.iter f [false;true]

let run ?(rounds=2) ?(budget=256) ?(environment=env) ?(g=C.empty_context)
    ?(mode=C.NormalReduction)
    ?(core=(fun _ _ -> C.Reject C.ExpectedPi)) indexed whnf defeq left right =
  let events = ref [] in
  let record callback_g event = eq "callback context changed" callback_g g;
    events := event :: !events in
  let m = {C.infer_method=(fun _ _ -> failwith "unexpected inference");
    infer_type_method=(fun _ _ -> failwith "unexpected type inference");
    whnf_method=(fun g e -> record g (Whnf e); whnf e);
    whnf_core_method=(fun cheap g e -> record g (Core(cheap,e)); core cheap e);
    defeq_method=(fun g a b -> record g (Eq(a,b)); defeq a b);
    method_mode=mode;
    eager_defeq_method=(fun g a b -> record g (Eq(a,b)); defeq a b)} in
  let result = if indexed then
    let lookup = C.prepare_lookup (fun _ -> C.N0) environment in
    C.Accessor.core_lazy_delta (fun nm _ -> lookup nm) (n rounds) m (n budget)
      environment C.Nil g left right
    else C.core_lazy_delta (n rounds) m (n budget) environment C.Nil g left right in
  result,List.rev !events

let left_whnf e = if e=l then C.Accept(lit 2)
  else if e=r then C.Reject C.UnknownFreeVariable else C.Accept e
let right_whnf e = if e=r then C.Accept(lit 5) else C.Accept e
let yes _ _ = C.Accept C.True
let no _ _ = C.Accept C.False
let () =
  test "checked-positive-fixtures" (fun () ->
    eq "Nat readiness" (C.core_nat_ready env) C.True;
    eq "primitive authenticated" (C.primitive_authenticated fuel env C.PNatAdd) (C.Accept C.Tt);
    let d = match C.find_decl (C.primitive_name C.PNatAdd) env with
      | C.Some d -> d | C.None -> failwith "missing add" in
    eq "authenticated tag" d.C.decl_kind_of (C.DPrimitive C.PNatAdd);
    eq "regular hint retained" d.C.decl_hints reg;
    eq "erasing policy fixture" (C.core_erasing_delta env t) C.False;
    eq "ordinary literal evaluation" (C.defeq fuel env C.Nil C.empty_context
      (add (lit 2) (lit 1)) (lit 3)) (C.Accept C.True));
  test "left-success-short-circuits-right-and-congruence" (fun () -> both (fun indexed ->
    List.iter (fun answer -> eq "left result and exact trace"
      (run indexed left_whnf (fun _ _ -> answer) t s)
      (bool_done answer,[Whnf l;Whnf(lit 1);Eq(lit 3,s)]))
      ([C.Accept C.True;C.Accept C.False] @ faults())));
  test "left-none-then-right-success" (fun () -> both (fun indexed ->
    List.iter (fun answer -> eq "right result and exact trace"
      (run indexed right_whnf (fun _ _ -> answer) t s)
      (bool_done answer,[Whnf l;Whnf(lit 1);Whnf r;Whnf(lit 2);Eq(t,lit 7)]))
      ([C.Accept C.True;C.Accept C.False] @ faults())));
  test "probe-error-priority" (fun () -> both (fun indexed ->
    List.iter (fun fault ->
      eq "left first argument error" (run indexed (fun _ -> fault) yes t s)
        (bool_done (match fault with C.Reject e -> C.Reject e | C.Decline d -> C.Decline d
          | C.Accept _ -> assert false),[Whnf l]);
      let result = match fault with C.Reject e -> C.Reject e | C.Decline d -> C.Decline d
        | C.Accept _ -> assert false in
      eq "left second argument error" (run indexed
        (fun e -> if e=l then C.Accept(lit 2) else fault) yes t s)
        (result,[Whnf l;Whnf(lit 1)]);
      eq "right first argument error after left none" (run indexed
        (fun e -> if e=r then fault else C.Accept e) yes t s)
        (result,[Whnf l;Whnf(lit 1);Whnf r]);
      eq "right second argument error after left none" (run indexed
        (fun e -> if e=lit 2 then fault else C.Accept e) yes t s)
        (result,[Whnf l;Whnf(lit 1);Whnf r;Whnf(lit 2)])) (faults())));
  let prefix = [Whnf l;Whnf(lit 1);Whnf r;Whnf(lit 2)] in
  test "both-none-congruence-and-delta-fallback" (fun () -> both (fun indexed ->
    eq "congruence runs only after both none" (run indexed (fun e -> C.Accept e) yes t s)
      (success,prefix @ [Eq(lit 1,lit 2);Eq(l,r)]);
    List.iter (fun fault -> eq "congruence errors retained"
      (run indexed (fun e -> C.Accept e) (fun _ _ -> fault) t s)
      (bool_done fault,prefix @ [Eq(lit 1,lit 2)])) (faults());
    eq "false congruence reaches ordinary delta" (run indexed (fun e -> C.Accept e) no t s)
      (C.Reject C.ExpectedPi,prefix @ [Eq(lit 1,lit 2);
        Core(C.True,apps add_body [l;lit 1])]);
    eq "delta recursion spends one round" (run ~rounds:1
      ~core:(fun _ e -> C.Accept e) indexed (fun e -> C.Accept e) no t s)
      (C.Decline C.OutOfFuel,prefix @ [Eq(lit 1,lit 2);
        Core(C.True,apps add_body [l;lit 1]);Core(C.True,apps add_body [r;lit 2])])));
  test "fuel-quick-and-offset-priority" (fun () -> both (fun indexed ->
    eq "zero rounds no callbacks" (run ~rounds:0 indexed left_whnf yes t s)
      (C.Decline C.OutOfFuel,[]);
    List.iter (fun budget -> eq "Nat before fuel-limited congruence"
      (run ~budget ~rounds:1 indexed left_whnf yes t s)
      (success,[Whnf l;Whnf(lit 1);Eq(lit 3,s)])) [0;1;32;256];
    eq "quick still first" (run indexed (fun _ -> C.Reject C.TypeMismatch) yes t t)
      (success,[]);
    let left = C.primitive_succ l and right = C.primitive_succ r in
    eq "offset still before Nat probes"
      (run indexed (fun _ -> C.Reject C.TypeMismatch) yes left right)
      (success,[Eq(l,r)])));
  test "authorization-and-eligibility-gates" (fun () ->
    begin match C.admit fuel nat_env (add_input(lam C.core_nat(lam C.core_nat(b 1)))) with
      | C.Reject _ -> incr assertions | _ -> failwith "false add body must reject" end;
    let add_decl = match C.find_decl (C.primitive_name C.PNatAdd) env with
      | C.Some d -> d | C.None -> failwith "missing add" in
    (* Raw mutations are negative-only eligibility probes, not admitted environments. *)
    let negative_envs = [C.Nil;
      C.Cons({add_decl with C.decl_kind_of=C.DDefinition},env);
      C.Cons({add_decl with C.decl_kind_of=C.DUnsafe(C.DPrimitive C.PNatAdd)},env);
      C.Cons({add_decl with C.decl_kind_of=C.DPrimitive C.PNatBitwise},env)] in
    let add_head = C.EConst(C.primitive_name C.PNatAdd,C.Nil) in
    let malformed = [add_head;app add_head l;apps add_head [l;lit 1;lit 2];
      apps (C.EConst(C.primitive_name C.PNatAdd,list[C.LZero])) [l;lit 1]] in
    let m = {C.infer_method=(fun _ _ -> failwith "inference eligibility");
      infer_type_method=(fun _ _ -> failwith "type eligibility");
      whnf_method=(fun _ _ -> failwith "ineligible Nat argument evaluated");
      whnf_core_method=(fun _ _ _ -> failwith "core eligibility");
      defeq_method=(fun _ _ _ -> failwith "defeq eligibility");
      method_mode=C.NormalReduction;
      eager_defeq_method=(fun _ _ _ -> failwith "eager defeq eligibility")} in
    let check e term =
      eq "ordinary ineligible" (C.core_reduce_nat m fuel e C.empty_context term) (C.Accept C.None);
      let lookup = C.prepare_lookup (fun _ -> C.N0) e in
      eq "lookup ineligible" (C.Accessor.core_reduce_nat (fun nm _ -> lookup nm)
        m fuel e C.empty_context term) (C.Accept C.None) in
    List.iter (fun e -> check e t) negative_envs; List.iter (check env) malformed);
  let bound = C.push_binding C.empty_context C.core_nat (C.Some(lit 2)) in
  let free = {C.empty_context with C.free_context=list[C.Pair(name "x",
    {C.binding_type=C.core_nat;binding_value=C.Some(lit 2)})]} in
  test "real-local-context-callbacks" (fun () -> both (fun indexed ->
    List.iter (fun (g,value) ->
      let actual = C.checker fuel env C.Nil in
      let left = add value (lit 1) in
      eq "typed local application" (actual.C.infer_method g left) (C.Accept C.core_nat);
      eq "unmodified local normalization and comparison"
        (run ~g ~mode:C.EagerReduction indexed (actual.C.whnf_method g) (actual.C.defeq_method g) left (lit 3))
        (success,[Whnf value;Whnf(lit 1);Eq(lit 3,lit 3)]))
      [bound,b 0;free,C.EFVar(name "x")]));
  test "prepared-complete-result-equivalence-new-order" (fun () ->
    let cases = [C.empty_context,t,s;C.empty_context,add (lit 2) (lit 1),lit 3;
      C.empty_context,add (lit 2) (lit 1),lit 4;
      bound,add (b 0) (lit 1),lit 3;free,add (C.EFVar(name "x")) (lit 1),lit 3;
      C.empty_context,add (C.EFVar(name "missing")) (lit 1),lit 3] in
    List.iter (fun hash -> let lookup = C.prepare_lookup hash env in
      List.iter (fun budget -> List.iter (fun (g,left,right) ->
        eq "full result not verdict-only" (C.prepared_defeq lookup (n budget) env C.Nil g left right)
          (C.defeq (n budget) env C.Nil g left right)) cases) [0;1;2;8;32;256])
      [(fun _ -> C.N0);C.suffix_bitfold8]);
  Printf.printf "NAT_PROBE_CALLBACKS_PASS suites=%d assertions=%d\n%!" !suites !assertions
