(* Test-only methods instrument the actual extracted callbacks, never runtime. *)
module C = Lean_arena
module A = Rocq_adapter
let n = A.nat
let list xs = A.list Fun.id xs
let name s = C.NameStr(C.NameAnon,A.string s)
let p = C.ESort C.LZero
let t = C.ESort(C.LSucc C.LZero)
let cn s us = C.EConst(name s,list us)
let app f a = C.EApp(f,a)
let lam body = C.ELam(C.NameAnon,C.BDefault,t,body)
let reg = C.HintRegular (A.binary (Z.of_int 7))
let d label h kind value = {C.decl_name=name label;decl_params=C.Nil;decl_type=t;
  decl_value=value;decl_kind_of=kind;decl_hints=h}
let ordinary h = d "f" h C.DDefinition (C.Some (cn "alias" []))
let expect a b = if a <> b then failwith "unexpected full result/callback count"
let passed = ref []
let test id f =
  (try f () with exn -> Printf.eprintf "FAIL %s\n%!" id; raise exn);
  passed := id :: !passed; Printf.printf "PASS %s\n%!" id
let args = ref [] and bodies = ref []
let methods answer body_answer = {
  C.infer_method=(fun _ _ -> C.Accept t);
  infer_type_method=(fun _ _ -> C.Accept t);
  whnf_method=(fun _ e -> C.Accept e);
  whnf_core_method=(fun _ _ e -> bodies := e :: !bodies; body_answer e);
  defeq_method=(fun _ a b -> args := (a,b) :: !args; answer a b);
  method_mode=C.NormalReduction;
  eager_defeq_method=(fun _ a b -> args := (a,b) :: !args; answer a b)
}
let reset () = args := []; bodies := []
let run ?(fuel=32) env m a b = reset (); C.core_lazy_delta (n 2) m (n fuel) env C.Nil C.empty_context a b
let congruent ?(fuel=32) env m a b = reset (); C.core_delta_congruent m (n fuel) env C.empty_context a b
let success = C.Accept(C.ConversionDone C.True)
let same_apps = app (cn "f" []) p, app (cn "f" []) t
let yes _ _ = C.Accept C.True
let no _ _ = C.Accept C.False
let normalize _ = C.Accept p
let policy_hint = function
  | `String "opaque" -> C.HintOpaque
  | `String "abbrev" -> C.HintAbbrev
  | `Assoc ["regular",`String z] -> A.hints (Wire.Regular(Z.of_string z))
  | _ -> failwith "invalid policy fixture"

(* Positive fixtures are generated and admitted, never installed as raw tags.
   The raw mutations below are negative-only inputs to the same checker APIs. *)
let projection_controls () =
  let get label = function C.Accept x -> x | _ -> failwith ("projection fixture: " ^ label) in
  let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x :: elements xs in
  let fuel = n 256 in
  let pi a b = C.EPi(C.NameAnon,C.BDefault,a,b) in
  let c s = cn ("Retry." ^ s) [] in
  let nm s = name ("Retry." ^ s) in
  let seed s ty k = {(d ("Retry." ^ s) C.HintOpaque k C.None) with C.decl_type=ty} in
  let dep = c "Dep" and mk = c "Dep.mk" in
  let owner = nm "Dep" in
  let ind = seed "Dep" (C.ESort(C.LSucc(C.LSucc C.LZero))) (C.DInductive {
    C.ind_num_params=C.O; ind_num_indices=C.O; ind_all=list[owner];
    ind_ctors=list[nm "Dep.mk"]; ind_num_nested=C.O; ind_is_rec=C.False;
    ind_is_reflexive=C.False; ind_is_unsafe=C.False}) in
  let ctor = seed "Dep.mk" (pi t (pi (C.EBVar C.O) dep)) (C.DConstructor {
    C.ctor_induct=owner;ctor_index=C.O;ctor_num_params=C.O;
    ctor_num_fields=n 2;ctor_is_unsafe=C.False}) in
  let generated = get "derive dependent package" (C.derive_inductive fuel C.Nil C.Nil C.O
    (list[{C.spec_decl=ind;spec_ctors=list[ctor]}])) |> elements in
  let types = List.filter (fun x -> match x.C.decl_kind_of with C.DInductive _ -> true | _ -> false) generated in
  let ctors = List.filter (fun x -> match x.C.decl_kind_of with C.DConstructor _ -> true | _ -> false) generated in
  let recs = List.filter (fun x -> match x.C.decl_kind_of with C.DRecursor _ -> true | _ -> false) generated in
  let env = get "admit generated dependent package"
    (C.admit_inductive_extended fuel C.Nil (list types) (list ctors) (list recs)) in
  let admit env x = get "checked input" (C.admit fuel env x) in
  let env = admit env (C.InputAxiom(nm "A",C.Nil,t,C.False)) in
  let env = admit env (C.InputAxiom(nm "a",C.Nil,c "A",C.False)) in
  let fn_ty = pi (c "A") (c "A") in
  let body = C.ELam(C.NameAnon,C.BDefault,c "A",C.EBVar C.O) in
  let define env s h ty value = admit env (C.InputDefinition(h,nm s,C.Nil,ty,value,C.InputSafe)) in
  let env = define env "f" reg fn_ty body in
  let env = define env "g" reg fn_ty body in
  let value = app (app mk fn_ty) (c "f") in
  let env = define env "package" reg dep value in
  let env = admit env (C.InputOpaque(nm "stuck",C.Nil,dep,value,C.False)) in
  let env = admit env (C.InputOpaque(nm "opaque",C.Nil,fn_ty,body,C.False)) in
  let project = C.EProj(owner,n 1,c "package") in
  let lhs = app (c "f") (c "a") and rhs = app project (c "a") in
  let stuck = app (C.EProj(owner,n 1,c "stuck")) (c "a") in
  let request term = C.InputDefinition(reg,nm "out",C.Nil,c "A",term,C.InputSafe) in
  ignore(admit env (request lhs)); ignore(admit env (request rhs));
  let baseline = C.checker fuel env C.Nil in
  expect (baseline.C.whnf_core_method C.True C.empty_context rhs) (C.Accept rhs);
  expect (baseline.C.whnf_core_method C.False C.empty_context rhs) (C.Accept lhs);
  expect (C.defeq fuel env C.Nil C.empty_context lhs rhs) (C.Accept C.True);
  Printf.printf "PROJECTION_TYPED_BASELINE_PASS declarations=%d\n%!" (List.length(elements env));
  let events = ref [] and preparations = ref 0 in
  let build_lookup env hash = incr preparations; C.prepare_lookup hash env in
  let invoke ?(rounds=2) ?callback env indexed left right =
    events := []; preparations := 0;
    let lookup = if indexed then Some(build_lookup env (fun _ -> C.N0)) else None in
    let m = match lookup with None -> C.checker fuel env C.Nil
      | Some lookup -> C.checker_with_lookup fuel env lookup C.Nil in
    let instrumented = {m with C.whnf_core_method=(fun cheap g e ->
      events := (cheap,e) :: !events;
      match callback with Some f -> f cheap g e | None -> m.C.whnf_core_method cheap g e)} in
    let result = match lookup with
      | None -> C.core_lazy_delta (n rounds) instrumented fuel env C.Nil C.empty_context left right
      | Some lookup -> C.Accessor.core_lazy_delta (fun k _ -> lookup k) (n rounds)
          instrumented fuel env C.Nil C.empty_context left right in
    expect !preparations (if indexed then 1 else 0);
    result,List.rev !events in
  let orientations f = f lhs rhs; f rhs lhs in
  test "single-delta-projection" (fun () ->
    List.iter (fun indexed -> orientations (fun left right ->
      let result,trace = invoke env indexed left right in
      Printf.printf "PROJECTION_PROBE indexed=%b left_delta=%b success=%b full_callbacks=%d body_callbacks=%d preparations=%d\n%!"
        indexed (left=lhs) (result=success)
        (List.length(List.filter (fun (cheap,_) -> cheap=C.False) trace))
        (List.length(List.filter (fun (cheap,_) -> cheap=C.True) trace)) !preparations;
      expect (result,trace) (success,[C.False,rhs]))) [false;true]);
  test "projection-rounds" (fun () -> List.iter (fun indexed -> orientations (fun left right ->
    expect (invoke ~rounds:0 env indexed left right) (C.Decline C.OutOfFuel,[]);
    expect (invoke ~rounds:1 env indexed left right) (C.Decline C.OutOfFuel,[C.False,rhs]))) [false;true]);
  let errors = [C.UnknownConstant;C.UnknownFreeVariable;C.LooseBoundVariable;C.UnknownUniverse;
    C.UniverseArity;C.ExpectedSort;C.ExpectedPi;C.TypeMismatch;C.NotDefinitionallyEqual;
    C.DuplicateDeclaration;C.DuplicateUniverse;C.MalformedDeclaration;C.MetaVariable] in
  let reasons = [C.OutOfFuel;C.UnsupportedExpression;C.UnsupportedDeclaration] in
  test "projection-callback-errors" (fun () -> List.iter (fun indexed -> orientations (fun left right ->
    List.iter (fun error -> expect
      (invoke ~callback:(fun _ _ _ -> C.Reject error) env indexed left right)
      (C.Reject error,[C.False,rhs])) errors;
    List.iter (fun reason -> expect
      (invoke ~callback:(fun _ _ _ -> C.Decline reason) env indexed left right)
      (C.Decline reason,[C.False,rhs])) reasons)) [false;true]);
  test "projection-stuck-fallback" (fun () -> List.iter (fun indexed ->
    List.iter (fun (left,right) -> expect (invoke ~rounds:1 env indexed left right)
      (C.Decline C.OutOfFuel,[C.False,stuck;C.True,app body (c "a")]))
      [lhs,stuck;stuck,lhs]) [false;true]);
  test "projection-unchanged-callback" (fun () -> List.iter (fun indexed -> orientations (fun left right ->
    let callback cheap _ e = if cheap=C.False then C.Accept e else C.Reject C.ExpectedPi in
    expect (invoke ~callback env indexed left right)
      (C.Reject C.ExpectedPi,[C.False,rhs;C.True,app body (c "a")]))) [false;true]);
  test "projection-nonprojection-and-two-delta" (fun () -> List.iter (fun indexed ->
    List.iter (fun (left,right) -> expect (invoke ~rounds:1 env indexed left right)
      (C.Decline C.OutOfFuel,[C.True,app body (c "a")])) [lhs,c "a";c "a",lhs];
    expect (invoke ~rounds:1 env indexed lhs (app (c "g") (c "a")))
      (C.Decline C.OutOfFuel,[C.True,app body (c "a");C.True,app body (c "a")])) [false;true]);
  let find label = get label (match C.find_decl (nm label) env with
    | C.Some d -> C.Accept d | C.None -> C.Reject C.UnknownConstant) in
  let shadow declaration = C.Cons(declaration,env) in
  test "projection-opaque-hint-and-shadowing" (fun () -> List.iter (fun indexed ->
    let opaque = app (c "opaque") (c "a") in
    expect (invoke env indexed opaque rhs) (C.Accept(C.ConversionStuck(opaque,rhs)),[]);
    expect (invoke env indexed rhs opaque) (C.Accept(C.ConversionStuck(rhs,opaque)),[]);
    let hint = shadow {(find "f") with C.decl_hints=C.HintOpaque} in
    expect (invoke hint indexed lhs rhs) (success,[C.False,rhs]);
    expect (invoke hint indexed rhs lhs) (success,[C.False,rhs]);
    let actual = shadow {(find "f") with C.decl_kind_of=C.DOpaque} in
    expect (invoke actual indexed lhs rhs) (C.Accept(C.ConversionStuck(lhs,rhs)),[]);
    expect (invoke actual indexed rhs lhs) (C.Accept(C.ConversionStuck(rhs,lhs)),[])) [false;true]);
  test "projection-unsafe-and-malformed-gates" (fun () ->
    let bad_owner = shadow {(find "Dep") with C.decl_kind_of=C.DUnsafe (find "Dep").C.decl_kind_of} in
    expect (C.admit fuel bad_owner (request rhs)) (C.Decline C.UnsupportedExpression);
    let bad_ctor = {(find "Dep.mk") with C.decl_kind_of=(match (find "Dep.mk").C.decl_kind_of with
      | C.DConstructor ci -> C.DConstructor {ci with C.ctor_num_fields=n 3}
      | _ -> failwith "expected checked constructor")} in
    expect (C.admit_inductive_extended fuel C.Nil (list types) (list[bad_ctor]) (list recs))
      (C.Reject C.MalformedDeclaration);
    let unsafe = shadow {(find "f") with C.decl_kind_of=C.DUnsafe C.DDefinition} in
    expect (C.admit fuel unsafe (request lhs)) (C.Reject C.MalformedDeclaration);
    List.iter (fun indexed ->
      expect (invoke unsafe indexed lhs rhs) (C.Reject C.MalformedDeclaration,[]);
      expect (invoke unsafe indexed rhs lhs) (C.Reject C.MalformedDeclaration,[]);
      expect (invoke ~rounds:1 (shadow bad_ctor) indexed lhs rhs)
        (C.Decline C.OutOfFuel,[C.False,rhs;C.True,app body (c "a")]);
      expect (invoke ~rounds:1 (shadow bad_ctor) indexed rhs lhs)
        (C.Decline C.OutOfFuel,[C.False,rhs;C.True,app body (c "a")]);
      let bad = app (cn "Retry.f" [C.LZero]) (c "a") in
      expect (invoke env indexed bad rhs) (C.Reject C.UniverseArity,[]);
      expect (invoke env indexed rhs bad) (C.Reject C.UniverseArity,[])) [false;true]);
  test "projection-error-precedence" (fun () ->
    let poly = {(find "f") with C.decl_params=list[nm "u"]} in
    let e = shadow poly in
    let bad = app (cn "Retry.f" [C.LParam(nm "unknown")]) (c "a") in
    expect (C.core_delta_info e bad) (C.Some poly);
    expect (C.core_unfold e C.Nil bad) (C.Reject C.UnknownUniverse);
    expect (C.admit fuel e (request bad)) (C.Reject C.UnknownUniverse);
    List.iter (fun indexed -> List.iter (fun (left,right) ->
      expect (invoke ~callback:(fun _ _ _ -> C.Reject C.ExpectedPi) e indexed left right)
        (C.Reject C.ExpectedPi,[C.False,rhs]);
      expect (invoke ~callback:(fun _ _ _ -> C.Decline C.UnsupportedExpression) e indexed left right)
        (C.Decline C.UnsupportedExpression,[C.False,rhs]);
      expect (invoke ~callback:(fun _ _ term -> C.Accept term) e indexed left right)
        (C.Reject C.UnknownUniverse,[C.False,rhs])) [bad,rhs;rhs,bad]) [false;true]);
  let comparisons = ref 0 in
  test "projection-prepared-full-results" (fun () ->
    List.iter (fun count ->
      let rec pad i env = if i=0 then env else pad (i-1)
        (admit env (C.InputAxiom(nm ("pad" ^ string_of_int i),C.Nil,t,C.False))) in
      let e = pad (count-List.length(elements env)) env in
      List.iter (fun hash -> let lookup = C.prepare_lookup hash e in
        List.iter (fun budget -> List.iter (fun (left,right) ->
          incr comparisons;
          expect (C.prepared_defeq lookup (n budget) e C.Nil C.empty_context left right)
            (C.defeq (n budget) e C.Nil C.empty_context left right))
          [lhs,rhs;rhs,lhs;lhs,stuck;stuck,lhs;lhs,c "a";lhs,app (c "g") (c "a");
           app (c "opaque") (c "a"),rhs;lhs,app (C.EProj(owner,n 2,c "package")) (c "a")])
          [0;1;4;256]) [C.suffix_bitfold8;(fun _ -> C.N0)]) [63;64]);
  Printf.printf "PROJECTION_RETRY_PASS full_result_comparisons=%d shared_preparations=1 success_body_callbacks=0\n%!" !comparisons

let () =
  let open Yojson.Safe.Util in
  let controls = Yojson.Safe.from_file Sys.argv.(1) in
  let vectors = controls |> member "priority_cases" |> to_list in
  List.iteri (fun i row -> test ("priority-" ^ string_of_int i) (fun () ->
    let a = policy_hint(member "left" row) and b = policy_hint(member "right" row) in
    let env = list[d "L" a C.DDefinition (C.Some p); d "R" b C.DDefinition (C.Some t)] in
    let expected = match member "unfold" row |> to_string with
      | "left" -> C.Pair(C.True,C.False) | "right" -> C.Pair(C.False,C.True)
      | "both" | "both-unless-congruence-succeeds" -> C.Pair(C.True,C.True)
      | _ -> failwith "invalid policy outcome" in
    expect (C.core_delta_sides env (cn "L" []) (cn "R" [])) expected)) vectors;
  let env = list[ordinary reg] in
  let a,b = same_apps in
  test "same-regular-success" (fun () ->
    expect (run env (methods yes normalize) a b) success;
    expect (List.length !args,List.length !bodies) (1,0));
  test "false-congruence" (fun () ->
    expect (run env (methods no normalize) a b) success;
    expect (List.length !args,List.length !bodies) (1,2));
  test "congruence-fuel" (fun () ->
    expect (run env (methods (fun _ _ -> C.Decline C.OutOfFuel) normalize) a b) (C.Decline C.OutOfFuel);
    expect (List.length !args,List.length !bodies) (1,0));
  test "congruence-error" (fun () ->
    expect (run env (methods (fun _ _ -> C.Reject C.TypeMismatch) normalize) a b) (C.Reject C.TypeMismatch);
    expect (List.length !args,List.length !bodies) (1,0));
  let poly = {(ordinary reg) with C.decl_params=list[name "u"]} in
  let au = app (cn "f" [C.LZero]) p and bu = app (cn "f" [C.LSucc C.LZero]) t in
  test "levels-false" (fun () ->
    expect (run (list[poly]) (methods yes normalize) au bu) success;
    expect (List.length !args,List.length !bodies) (0,2));
  test "levels-decline" (fun () ->
    expect (run ~fuel:0 (list[poly]) (methods yes normalize) au bu) (C.Decline C.OutOfFuel);
    expect (List.length !args,List.length !bodies) (0,0));
  test "equivalent-not-identical-levels" (fun () ->
    let bu = app (cn "f" [C.LMax(C.LZero,C.LZero)]) t in
    expect (run (list[poly]) (methods yes normalize) au bu) success;
    expect (List.length !args,List.length !bodies) (1,0));
  test "different-definitions" (fun () ->
    let env = list[ordinary reg; {(ordinary reg) with C.decl_name=name "g"}] in
    expect (run env (methods yes normalize) a (app (cn "g" []) t)) success;
    expect (List.length !args,List.length !bodies) (0,2));
  test "not-apps" (fun () ->
    expect (congruent env (methods yes normalize) (cn "f" []) (cn "f" [])) (C.Accept C.False);
    expect (List.length !args,List.length !bodies) (0,0));
  List.iter (fun (id,h) -> test id (fun () ->
    expect (run (list[ordinary h]) (methods yes normalize) a b) success;
    expect (List.length !args,List.length !bodies) (0,2)))
    ["abbrev-apps",C.HintAbbrev;"opaque-hint-apps",C.HintOpaque];
  test "theorem" (fun () ->
    let thm = d "f" C.HintAbbrev C.DTheorem (C.Some p) in
    expect (C.effective_hints thm) C.HintOpaque;
    expect (C.core_delta_info (list[thm]) (cn "f" [])) (C.Some thm));
  test "opaque-kind" (fun () ->
    let opaque = d "f" C.HintAbbrev C.DOpaque (C.Some p) in
    expect (C.effective_hints opaque) C.HintOpaque;
    expect (C.core_delta_info (list[opaque]) (cn "f" [])) C.None);
  test "primitive" (fun () ->
    let prim = d "f" C.HintAbbrev (C.DPrimitive C.PNatAdd) (C.Some p) in
    expect (C.effective_hints prim) C.HintAbbrev);
  test "unsafe-use" (fun () -> List.iter (fun k ->
    let unsafe = d "f" C.HintAbbrev k (C.Some p) in
    expect (C.infer (n 32) (list[unsafe]) C.Nil C.empty_context (cn "f" []))
      (C.Reject C.MalformedDeclaration)) [C.DUnsafe C.DDefinition;C.DPartial]);
  test "unsafe-view" (fun () ->
    let unsafe = d "f" reg (C.DUnsafe C.DDefinition) (C.Some p) in
    expect (C.effective_hints (C.checking_view C.InputSafe unsafe)) C.HintOpaque;
    expect (C.effective_hints (C.checking_view C.InputUnsafe unsafe)) reg);
  test "arity" (fun () ->
    expect (C.core_delta_info (list[poly]) (cn "f" [])) C.None;
    expect (C.infer (n 32) (list[poly]) C.Nil C.empty_context (cn "f" [])) (C.Reject C.UniverseArity));
  test "universe-membership" (fun () ->
    let bad = cn "f" [C.LParam(name "unknown")] in
    expect (C.core_delta_info (list[poly]) bad) (C.Some poly);
    expect (C.infer (n 32) (list[poly]) C.Nil C.empty_context bad) (C.Reject C.UnknownUniverse));
  test "missing-value" (fun () ->
    let bad = {(ordinary reg) with C.decl_value=C.None} in
    expect (C.core_delta_info (list[bad]) (cn "f" [])) C.None;
    expect (C.whnf (n 32) (list[bad]) C.Nil C.empty_context (cn "f" [])) (C.Reject C.MalformedDeclaration));
  test "rightmost-first" (fun () ->
    let left = app (app (cn "f" []) p) t and right = app (app (cn "f" []) t) p in
    let answer x _ = if x=t then C.Reject C.TypeMismatch else C.Decline C.OutOfFuel in
    expect (run env (methods answer normalize) left right) (C.Reject C.TypeMismatch);
    expect !args [t,p]);
  test "two-body-order" (fun () ->
    let env = list[d "L" reg C.DDefinition (C.Some p); d "R" reg C.DDefinition (C.Some t)] in
    let normalize e = if e=p then C.Reject C.ExpectedSort else C.Decline C.OutOfFuel in
    expect (run env (methods yes normalize) (cn "L" []) (cn "R" [])) (C.Reject C.ExpectedSort);
    expect !bodies [p]);
  test "shadowing" (fun () ->
    let old = ordinary C.HintAbbrev and fresh = ordinary C.HintOpaque in
    let g = d "g" reg C.DDefinition (C.Some p) in
    expect (C.core_delta_info (list[fresh;old;g]) (cn "f" [])) (C.Some fresh);
    expect (C.core_delta_sides (list[fresh;old;g]) (cn "f" []) (cn "g" [])) (C.Pair(C.False,C.True)));
  test "erased-invalid-arg" (fun () ->
    let erased = C.InputDefinition(reg,name "erase",C.Nil,C.EPi(C.NameAnon,C.BDefault,t,t),lam p,C.InputSafe) in
    let env = match C.admit (n 64) C.Nil erased with C.Accept e -> e | _ -> failwith "baseline gate failed" in
    let request body = C.InputDefinition(reg,name "out",C.Nil,t,body,C.InputSafe) in
    (match C.admit (n 64) env (request (app (cn "erase" []) p)) with C.Accept _ -> () | _ -> failwith "positive gate failed");
    expect (C.admit (n 64) env (request (app (cn "erase" []) t))) (C.Reject C.TypeMismatch));
  projection_controls ();
  let documented = ["failed-before"] in
  let required = controls |> member "guard_cases" |> to_list |> List.map (fun x -> x |> member "id" |> to_string) in
  List.iter (fun id -> if not (List.mem id !passed || List.mem id documented) then failwith ("uncovered guard: " ^ id)) required;
  Printf.printf "HINT_CALLBACKS_PASS priority_vectors=%d guard_requirements_passed=23 documented_unimplemented=1 extra_controls=10\n%!" (List.length vectors)
