exception Safety_diagnostic_limit;;

(* Test-only reducer mirror. Diagnostics never supply a proof to admission. *)
module Safety_test_diagnostics = struct
  include Lean4hol_safety
  module Original = Lean4hol_safety
  module Raw = Lean4hol_raw_ctor
  module Env = Lean4hol_env
  open Lean4hol
  let equations = Raw.equations @
    [l4_scoped;l4_safety_visible;l4_safety_view;l4_safety_blocked;l4_safety_safe_entries;
     l4_protected_name;l4_primitive_names;l4_nat_name;l4_bool_name;
     l4_mark_safety;l4_mark_entry;l4_mark_hint;l4_mark_all;l4_mark_name;
     l4_safety_refs;l4_safety_rule_refs;l4_safety_role_refs;l4_safety_kind_refs;l4_safety_entry_refs;
     l4_safety_references;l4_safety_fresh;l4_safety_mode;l4_safety_placeholder;l4_safety_fragment;
     l4_safety_definition;l4_safety_shape;l4_safety_step_op;l4_safety_step_raw;
     l4_safety_step_registry;l4_safety_step_env;l4_safety_next_registry;l4_safety_next_env;
     l4_safety_raw_history;l4_safety_safe_history;ITLIST;FILTER;COND_CLAUSES;
     distinctness "l4_safety";distinctness "l4_operation";distinctness "l4_hint";
     injectivity "l4_mark";injectivity "l4_safety_step";injectivity "l4_hint"]
  let quote_mode = function Safe->`L4Safe` | Partial->`L4Partial` | Unsafe->`L4Unsafe`
  let entries mode s = List.filter_map(fun r->
    if mode=Unsafe || r.safety=Safe || (mode=Partial && r.safety=Partial)
    then Some r.entry else None)(registry s)
  let view_term s mode = mk_eq(node "l4_safety_view"
    [quote_mode mode;quote_marks(registry s)],Raw.entries(entries mode s))
  let fresh_term s raw = node "l4_safety_fresh" [quote_marks(registry s);quote_marks raw]
  let bounded_term tm =
    let rec walk left = function []->() | t::rest ->
      if left=0 then raise Safety_diagnostic_limit;
      if is_comb t then let a,b=dest_comb t in walk(left-1)(a::b::rest)
      else if is_abs t then let a,b=dest_abs t in walk(left-1)(a::b::rest)
      else walk(left-1)rest in
    walk 10000 [tm];
    let text=string_of_term tm in
    if String.length text>4096 then String.sub text 0 4096 ^ " [truncated]" else text
  let observe terms result =
    (match result with
    | Error {kind=Proof_failure;message}
      when String.starts_with ~prefix:"undecided safety side condition: " message ->
      let handler=Sys.signal Sys.sigalrm (Sys.Signal_handle(fun _->raise Safety_diagnostic_limit)) in
      let timer=Unix.alarm 2 in
      let restore () =
        ignore(Unix.alarm 0);
        ignore(Sys.signal Sys.sigalrm handler);ignore(Unix.alarm timer) in
      (try
        Printf.printf "SAFETY_DIAGNOSTIC_BEGIN %S seconds=2 passes=8 nodes=10000 chars=4096\n%!" message;
        let pass = computation THENC REWRITE_CONV equations THENC NUM_REDUCE_CONV in
        List.iter(fun(label,tm)->
          let rec loop n t =
            Printf.printf "SAFETY_DIAGNOSTIC_TERM %S pass=%d %S\n%!" label n (bounded_term t);
            if n<8 then let t'=rhs(concl(pass t)) in
              if not(aconv t t') then loop(n+1)t' in
          loop 0 tm)(terms message);
        Printf.printf "SAFETY_DIAGNOSTIC_END original_failure_retained\n%!"
      with
      | Safety_diagnostic_limit -> Printf.printf "SAFETY_DIAGNOSTIC_LIMIT original_failure_retained\n%!"
      | _ -> Printf.printf "SAFETY_DIAGNOSTIC_UNAVAILABLE original_failure_retained\n%!");
      restore()
    | _ -> ());
    result
  let view s mode = observe (fun _->["mode view identity",view_term s mode]) (Original.view s mode)
  let check_fresh s raw = observe (fun _->["full registry freshness",fresh_term s raw])
    (Original.check_fresh s raw)
  let admit_restricted ?fuel s op raw =
    observe (fun message->
      let mode=match op,raw with (Safe_step|Partial_single),_->Safe |_,r::_->r.safety |_,[]->Safe in
      let prior=entries mode s in
      let fragment=if op=Partial_single then prior else
        List.map(fun r->{r.entry with Env.kind=Env.Axiom;value=None})raw @ prior in
      let term=match message with
      | "undecided safety side condition: restricted operation/scope/parameter shape" ->
        node "l4_safety_shape" [quote_operation op;quote_marks raw]
      | "undecided safety side condition: duplicate full-registry declaration name" ->fresh_term s raw
      | "undecided safety side condition: mode view identity" ->view_term s mode
      | "undecided safety side condition: temporary fragment identity" ->mk_eq(
        node "l4_safety_fragment" [quote_operation op;quote_marks(registry s);quote_marks raw],Raw.entries fragment)
      | _ -> failwith "unmapped diagnostic" in
      [message,term]) (Original.admit_restricted ?fuel s op raw)
  let append_safe ?fuel s raw next bridge =
    observe (fun message->
      let count=List.length(Env.declarations next)-List.length(Env.declarations(safe_environment s)) in
      let ds=List.filteri(fun i _->i<count)(Env.declarations next) in
      let canonical=List.map(fun d->{safety=Safe;entry=d;hint=No_hint;all=[]})ds in
      match message with
      | "undecided safety side condition: duplicate full-registry declaration name" ->
        ["raw freshness",fresh_term s raw;"canonical freshness",fresh_term s canonical]
      | "undecided safety side condition: safe prefix identity" ->[message,mk_eq(Env.quote_env next,
        Raw.entries(ds @ Env.declarations(safe_environment s)))]
      | "undecided safety side condition: unsafe entry cannot be a safe step" ->
        [message,list_mk_comb(`ALL:(l4_mark->bool)->l4_mark list->bool`,
          [mk_abs(`r:l4_mark`,mk_eq(node "l4_mark_safety" [`r:l4_mark`],`L4Safe`));quote_marks raw])]
      | "undecided safety side condition: raw/canonical safe metadata mismatch" ->
        [message,node "l4_metadata_matches" [Raw.entries(List.map(fun r->r.entry)raw);Raw.entries ds]]
      | _ -> failwith "unmapped diagnostic") (Original.append_safe ?fuel s raw next bridge)
end;;

let run_safety_group group =
  let module Core=Lean4hol in
  let module Env=Lean4hol_env in
  let module Safety=Safety_test_diagnostics in
  let open Core in
  let count=ref 0 in
  let test label ok =
    incr count;
    Printf.printf "SAFETY_ASSERT %s %d %b %s\n%!" group !count ok label;
    if not ok then failwith("SAFETY FAILURE "^label) in
  let get label = function Ok r->r |Error e->failwith(label^": "^e.message) in
  let bad label = function
    | Error {kind=Resource;message}->failwith(label^": resource is not a negative control: "^message)
    | Error _->test label true |Ok _->test label false in
  let invalid label = function Error {kind=Invalid_input;_}->test label true
    |Error e->failwith(label^": not Invalid_input: "^e.message)|Ok _->test label false in
  let proof_failure label = function Error {kind=Proof_failure;_}->test label true
    |Error e->failwith(label^": wrong failure: "^e.message)|Ok _->test label false in
  let nm s=Str(Anonymous,s) in
  let p=nm "SafetyP" and u=nm "u" in
  let prop=Const(p,[]) in
  let idtype=Pi(Anonymous,prop,prop) and idbody=Lam(Anonymous,prop,Bvar 0) in
  let definition safety n ty value all =
    {Safety.safety=safety;entry={Env.kind=Env.Definition;name=nm n;params=[];typ=ty;value=Some value};
      hint=Safety.Opaque_hint;all=List.map nm all} in
  let loop safety n all=definition safety n prop (Const(nm n,[])) all in
  let as_safe d={d with Safety.safety=Safety.Safe} in
  let closed label s =
    test(label^" closed") (hyp(Safety.certificate s)=[]);
    test(label^" exact") (aconv(concl(Safety.certificate s))(Safety.expected s));
    ignore(get(label^" authenticate")(Safety.authenticate s(Safety.certificate s)));
    test(label^" projection closed") (hyp(Safety.projection_certificate s)=[]) in
  let base () =
    let e0=get "base permissions" (Env.with_axioms[{Env.axiom_name=p;axiom_params=[];axiom_type=Sort Zero}]) in
    let s0=get "start" (Safety.start e0) in
    let d={Env.kind=Env.Axiom;name=p;params=[];typ=Sort Zero;value=None} in
    let e1,_=get "base axiom formation" (Env.admit e0 d) in
    let raw={Safety.safety=Safety.Safe;entry=d;hint=Safety.No_hint;all=[]} in
    let s=get "base marked safe step" (Safety.append_safe s0 [raw] e1 Safety.Exact) in
    closed "base" s;s in
  let add s op raw = get "restricted admission" (Safety.admit_restricted s op raw) in
  let exact_policy label before after =
    test(label^" E unchanged") (Env.declarations(Safety.safe_environment before)=Env.declarations(Safety.safe_environment after));
    test(label^" P unchanged") (Env.permissions(Safety.safe_environment before)=Env.permissions(Safety.safe_environment after));
    test(label^" E proof unchanged") (Env.certificate(Safety.safe_environment before)=Env.certificate(Safety.safe_environment after)) in
  let allowed label s mode raw=match get label(Safety.check_references s mode raw) with
    |Safety.Allowed th->test label(hyp th=[])|Safety.Forbidden _->test label false in
  let forbidden label s mode raw=match get label(Safety.check_references s mode raw) with
    |Safety.Forbidden th->test label(hyp th=[] && is_neg(concl th))|Safety.Allowed _->test label false in
  (match group with
  | "general" ->
    List.iter(fun th->test "closed derived general theorem" (hyp th=[]))
      [l4_safety_full_environment;l4_safety_full_projection;l4_safety_full_inventory;
       l4_safety_restricted_preserves_env;l4_safety_full_safe_only;l4_safety_full_old_safe;
       l4_safety_safe_history_all;l4_safety_visible_safe;l4_safety_visible_partial;l4_safety_visible_unsafe];
    let s=get "empty history" (Safety.start Env.empty) in closed "empty" s;
    List.iter(fun mode->
      let ds,h=get "empty mode view" (Safety.view s mode) in
      test "empty view" (ds=[] && hyp h=[])) [Safety.Safe;Safety.Partial;Safety.Unsafe]
  | "single" ->
    let s=base() in
    let raw=loop Safety.Unsafe "unsafeLoop" ["unsafeLoop"] in
    let next=add s Safety.Unsafe_single [raw] in
    closed "unsafe program only" next;exact_policy "unsafe" s next;
    test "actual marked body retained" (List.hd(Safety.registry next)=raw);
    test "unsafe stays outside safe env" (not(List.exists(fun d->d.Env.name=nm "unsafeLoop")
      (Env.declarations(Safety.safe_environment next))));
    bad "unsafe has no safe typing" (Env.check(Safety.safe_environment next)[] (Const(nm "unsafeLoop",[]))prop);
    let partial=definition Safety.Partial "partialId" idtype idbody ["partialId"] in
    let pnext=add next Safety.Partial_single [partial] in
    closed "direct partial nonrecursive" pnext;exact_policy "partial" next pnext;
    bad "direct partial self loop has no self placeholder"
      (Safety.admit_restricted s Safety.Partial_single [loop Safety.Partial "self" ["self"]]);
    let th={Env.kind=Env.Theorem;name=nm "unrelated";params=[];typ=idtype;value=Some idbody} in
    let env,_=get "unrelated theorem" (Env.admit(Safety.safe_environment pnext)th) in
    let final=get "safe continuation" (Safety.append_safe pnext
      [{Safety.safety=Safety.Safe;entry=th;hint=Safety.No_hint;all=[th.Env.name]}] env Safety.Exact) in
    closed "complete marked then safe history" final;
    test "both marked entries still recorded" (List.mem raw(Safety.registry final) && List.mem partial(Safety.registry final));
    test "safe projection theorem labelled separately"
      (not(aconv(concl(Safety.projection_certificate final))(Safety.expected final)))
  | "mutual" ->
    let s=base() in
    List.iter(fun safety->
      let a=definition safety "mutA" prop (Const(nm "mutB",[])) ["mutA";"mutB"] in
      let b=definition safety "mutB" prop (Const(nm "mutA",[])) ["mutB";"mutA"] in
      let next=add s Safety.Restricted_mutual [a;b] in
      closed "two member mutually recursive block" next;exact_policy "mutual" s next;
      test "both original all orders retained" (List.hd(Safety.registry next)=a && List.nth(Safety.registry next)1=b);
      let view,h=get "mode view includes actual definitions" (Safety.view next safety) in
      test "not persistent axiom placeholders" (List.mem a.Safety.entry view && List.mem b.Safety.entry view && hyp h=[]))
      [Safety.Partial;Safety.Unsafe];
    let raw=loop Safety.Partial "partialLoop" ["partialLoop"] in
    let next=add s Safety.Restricted_mutual [raw] in
    closed "singleton partial mutual" next;exact_policy "singleton mutual" s next;
    let polymorphic={raw with Safety.entry={raw.Safety.entry with Env.name=nm "poly";params=[u];
      typ=Pi(Anonymous,Sort(Param u),Sort(Param u));
      value=Some(Lam(Anonymous,Sort(Param u),Bvar 0))};all=[nm "poly"]} in
    closed "polymorphic partial block" (add s Safety.Restricted_mutual [polymorphic])
  | "references" ->
    let s=base() in
    let us=loop Safety.Unsafe "unsafeLoop" ["unsafeLoop"] in
    let ps=loop Safety.Partial "partialLoop" ["partialLoop"] in
    let next=add(add s Safety.Unsafe_single [us])Safety.Restricted_mutual[ps] in
    List.iter(fun(mode,name,expect)->
      let r=definition Safety.Safe "use" prop (Const(nm name,[])) ["use"] in
      if expect then allowed "visibility matrix" next mode [r]
      else forbidden "visibility matrix" next mode [r])
      [Safety.Safe,"SafetyP",true;Safety.Partial,"SafetyP",true;Safety.Unsafe,"SafetyP",true;
       Safety.Safe,"partialLoop",false;Safety.Partial,"partialLoop",true;Safety.Unsafe,"partialLoop",true;
       Safety.Safe,"unsafeLoop",false;Safety.Partial,"unsafeLoop",false;Safety.Unsafe,"unsafeLoop",true];
    let ignored=definition Safety.Safe "ignored" idtype
      (Let(Anonymous,prop,Const(nm "unsafeLoop",[]),idbody)) ["ignored"] in
    forbidden "unused let value not erased" next Safety.Safe [ignored];
    let app=definition Safety.Safe "ignoredArg" idtype
      (App(Lam(Anonymous,prop,lift {remaining=100000} 1 0 idbody),Const(nm "partialLoop",[]))) ["ignoredArg"] in
    forbidden "ignored application argument not erased" next Safety.Safe [app];
    let ty=definition Safety.Unsafe "unsafeType" (Sort Zero) (Sort Zero) ["unsafeType"] in
    let ty={ty with Safety.entry={ty.Safety.entry with Env.value=Some prop}} in
    let typed=add next Safety.Unsafe_single [ty] in
    let domain=definition Safety.Safe "domain" idtype
      (Lam(Anonymous,Const(nm "unsafeType",[]),Bvar 0)) ["domain"] in
    forbidden "lambda domain safety" typed Safety.Safe [domain];
    let wrong=definition Safety.Partial "wrong" prop (Const(nm "unsafeLoop",[])) ["wrong"] in
    invalid "partial block cannot use unsafe" (Safety.admit_restricted next Safety.Restricted_mutual [wrong]);
    let allowedraw={wrong with Safety.safety=Safety.Unsafe} in
    closed "unsafe may use earlier unsafe" (add next Safety.Unsafe_single [allowedraw]);
    let usepartial=definition Safety.Unsafe "usepartial" prop (Const(nm "partialLoop",[])) ["usepartial"] in
    closed "unsafe may use partial" (add next Safety.Unsafe_single [usepartial])
  | "authentication" ->
    let s=base() in
    let raw=loop Safety.Unsafe "loop" ["loop"] in
    let next=add s Safety.Unsafe_single [raw] in
    proof_failure "assumed full history rejected" (Safety.authenticate next(ASSUME(Safety.expected next)));
    proof_failure "different full registry/history rejected" (Safety.authenticate next(Safety.certificate s));
    proof_failure "safe projection cannot substitute for full input" (Safety.authenticate next(Safety.projection_certificate next));
    let view,_=get "unsafe view" (Safety.view s Safety.Unsafe) in
    let self={raw.Safety.entry with Env.kind=Env.Axiom;value=None} in
    let h=get "actual closed fragment body" (Env.fragment_check(self::view)[] (Const(nm "loop",[]))prop) in
    ignore(get "exact fragment accepted" (Safety.authenticate_body s Safety.Unsafe_single [raw] raw h));test "closed body" (hyp h=[]);
    proof_failure "open body theorem rejected"
      (Safety.authenticate_body s Safety.Unsafe_single [raw] raw (ASSUME(Safety.body_expected s Safety.Unsafe_single [raw] raw)));
    let changed={raw with Safety.entry={raw.Safety.entry with Env.value=Some idbody}} in
    proof_failure "wrong body theorem rejected" (Safety.authenticate_body s Safety.Unsafe_single [changed] changed h);
    let extra=loop Safety.Unsafe "extra" ["extra"] in
    proof_failure "extra placeholder rejected" (Safety.authenticate_body s Safety.Restricted_mutual [raw;extra] raw h);
    proof_failure "wrong fragment mode rejected" (Safety.authenticate_body s Safety.Partial_single [raw] raw h);
    let changed={raw with Safety.entry={raw.Safety.entry with Env.typ=idtype}} in
    proof_failure "wrong body type rejected" (Safety.authenticate_body s Safety.Unsafe_single [changed] changed h);
    let forged=EQ_MP (REFL(Safety.expected next)) (ASSUME(Safety.expected next)) in
    proof_failure "assumptions hidden behind inference rejected" (Safety.authenticate next forged);
    List.iter(fun transformed->
      let fake=ASSUME(transformed(Safety.expected next)) in
      proof_failure "tampered exact full conclusion" (Safety.authenticate next fake)) [(fun t -> mk_neg t); (fun t -> mk_conj(t,t))];
    bad "local placeholder not usable in safe environment" (Env.check(Safety.safe_environment next)[] (Const(nm "loop",[]))prop)
  | "shape" ->
    let s=base() in
    let a=loop Safety.Partial "a" ["a";"b"] and b=loop Safety.Partial "b" ["a";"b"] in
    invalid "empty block" (Safety.admit_restricted s Safety.Restricted_mutual []);
    invalid "safe mutual disallowed" (Safety.admit_restricted s Safety.Restricted_mutual [as_safe a;as_safe b]);
    invalid "mixed safety" (Safety.admit_restricted s Safety.Restricted_mutual [a;{b with Safety.safety=Safety.Unsafe}]);
    invalid "duplicate block name" (Safety.admit_restricted s Safety.Restricted_mutual [a;a]);
    let u1={a with Safety.entry={a.Safety.entry with Env.params=[u;nm "v"]}} in
    let u2={b with Safety.entry={b.Safety.entry with Env.params=[nm "v";u]}} in
    invalid "ordered universe lists must agree" (Safety.admit_restricted s Safety.Restricted_mutual [u1;u2]);
    let dup={a with Safety.entry={a.Safety.entry with Env.params=[u;u]};all=[nm "a"]} in
    invalid "duplicate universe parameters" (Safety.admit_restricted s Safety.Restricted_mutual [dup]);
    let openbody={a with Safety.entry={a.Safety.entry with Env.value=Some(Bvar 0)};all=[nm "a"]} in
    invalid "loose body variable" (Safety.admit_restricted s Safety.Restricted_mutual [openbody]);
    let opentype={a with Safety.entry={a.Safety.entry with Env.typ=Bvar 0};all=[nm "a"]} in
    invalid "loose header variable" (Safety.admit_restricted s Safety.Restricted_mutual [opentype]);
    let undeclared={a with Safety.entry={a.Safety.entry with Env.typ=Sort(Param u)};all=[nm "a"]} in
    invalid "undeclared level parameter" (Safety.admit_restricted s Safety.Restricted_mutual [undeclared]);
    let header={a with Safety.entry={a.Safety.entry with Env.typ=Const(nm "b",[])}} in
    bad "mutual header cannot use sibling placeholder" (Safety.admit_restricted s Safety.Restricted_mutual [header;b]);
    let header={a with Safety.entry={a.Safety.entry with Env.typ=Const(nm "a",[])};all=[nm "a"]} in
    bad "header cannot use self placeholder" (Safety.admit_restricted s Safety.Restricted_mutual [header]);
    let wrong={a with Safety.entry={a.Safety.entry with Env.value=Some(Sort Zero)};all=[nm "a"]} in
    bad "wrong body never accepted" (Safety.admit_restricted s Safety.Restricted_mutual [wrong]);
    let arity={a with Safety.entry={a.Safety.entry with Env.value=Some(Const(p,[Zero]))};all=[nm "a"]} in
    bad "wrong constant universe arity" (Safety.admit_restricted s Safety.Restricted_mutual [arity]);
    let protected={a with Safety.entry={a.Safety.entry with Env.name=Str(nm "Nat","add")};all=[Str(nm "Nat","add")]} in
    invalid "restricted primitive name forbidden" (Safety.admit_restricted s Safety.Restricted_mutual [protected]);
    invalid "mutual all missing member" (Safety.admit_restricted s Safety.Restricted_mutual [{a with Safety.all=[nm "a"]};b])
  | "atomicity" ->
    let s=base() in
    let a=definition Safety.Partial "a" idtype idbody ["a";"b"] in
    let b=definition Safety.Partial "b" prop (Sort Zero) ["a";"b"] in
    let before=Safety.certificate s and before_h=Safety.history_term s and before_r=Safety.registry s in
    bad "last body failure" (Safety.admit_restricted s Safety.Restricted_mutual [a;b]);
    test "rollback proof/history/registry" (Safety.certificate s=before && Safety.history_term s=before_h && Safety.registry s=before_r);
    let hidden=loop Safety.Unsafe "hidden" ["hidden"] in
    let next=add s Safety.Unsafe_single [hidden] in
    invalid "hidden duplicate unsafe" (Safety.admit_restricted next Safety.Unsafe_single [hidden]);
    invalid "safe name collides with hidden" (Safety.check_fresh next [{hidden with Safety.safety=Safety.Safe}]);
    let ind=nm "FreshType" in
    let recname=Str(ind,"rec") in
    let recslot={hidden with Safety.entry={hidden.Safety.entry with Env.name=recname;value=Some(Const(recname,[]))};all=[recname]} in
    let with_rec=add next Safety.Unsafe_single [recslot] in
    let block={Env.inductive_name=ind;inductive_level=Succ Zero;constructors=[];claims=[]} in
    let claims=Env.generate {remaining=100000} block in
    let block={block with Env.claims=claims} in
    let env,_=get "genuine generated candidate" (Env.admit_inductive(Safety.safe_environment with_rec)block) in
    let marks=List.map(fun d->{Safety.safety=Safety.Safe;entry=d;hint=Safety.No_hint;all=[]})claims in
    invalid "raw generated names include hidden collision" (Safety.check_fresh with_rec marks);
    invalid "generated commit independently checks full registry" (Safety.append_safe with_rec marks env Safety.Exact);
    test "failed generated commit keeps full certificate" (hyp(Safety.certificate with_rec)=[]);
    let allowedenv,_=get "positive generated admission" (Env.admit_inductive(Safety.safe_environment s)block) in
    closed "positive generated full history" (get "positive generated commit" (Safety.append_safe s marks allowedenv Safety.Exact))
  | "wrappers" ->
    let s=base() in
    let ty=definition Safety.Unsafe "unsafeType" (Sort Zero) prop ["unsafeType"] in
    let next=add s Safety.Unsafe_single [ty] in
    let converted=definition Safety.Unsafe "convertedId" idtype
      (Lam(Anonymous,Const(nm "unsafeType",[]),Bvar 0)) ["convertedId"] in
    closed "conversion unfolds actual unsafe definition" (add next Safety.Unsafe_single [converted]);
    let partial=definition Safety.Partial "partialId" idtype idbody ["partialId"] in
    let next=add s Safety.Restricted_mutual [partial] in
    let use=definition Safety.Partial "partialUse" idtype (Const(nm "partialId",[])) ["partialUse"] in
    closed "partial view includes earlier partial" (add next Safety.Restricted_mutual [use]);
    invalid "standalone partial uses safe prior mode" (Safety.admit_restricted next Safety.Partial_single [use]);
    bad "cannot bootstrap a nonempty environment without history" (Safety.start(Safety.safe_environment s));
    List.iter(fun kind->
      let d=loop Safety.Unsafe "excluded" ["excluded"] in
      let result=Safety.admit_restricted s Safety.Unsafe_single [{d with Safety.entry={d.Safety.entry with Env.kind=kind}}] in
      test "excluded kinds explicitly decline" (match result with Error{kind=Unsupported;_}->true|_->false))
      [Env.Axiom;Env.Opaque;Env.Generated(Env.Inductive_role{Env.num_params=0;num_indices=0;all=[];ctors=[];
         num_nested=0;is_rec=false;is_reflexive=false;is_unsafe=true})];
    test "fuel refusal is resource decline" (match Safety.admit_restricted ~fuel:0 s Safety.Unsafe_single
      [loop Safety.Unsafe "limited" ["limited"]] with Error{kind=Resource;_}->true|_->false);
    let safe=definition Safety.Safe "safeId" idtype idbody ["safeId"] in
    let env,_=get "legacy safe definition" (Env.admit(Safety.safe_environment s)safe.Safety.entry) in
    closed "legacy safe-only continuation" (get "safe-only full certificate" (Safety.append_safe s [safe] env Safety.Exact))
  | _ -> failwith("unknown safety group "^group));
  test "unchanged HOL axiom inventory" (axioms()=private_axioms);
  test "unchanged typing rule count" (List.length(CONJUNCTS l4_edef_RULES)=private_native_rule_count);
  test "unchanged environment rule count" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=private_admission_rule_count);
  test "old safe input trace rules unchanged" (List.length(CONJUNCTS l4_input_trace_RULES)=3);
  Printf.printf "SAFETY_DEFINITIONS_PASSED %s %d closed_exact unchanged_axioms rules%d_%d\n%!"
    group !count private_native_rule_count private_admission_rule_count;;
run_safety_group(Sys.getenv "SAFETY_GROUP");;
