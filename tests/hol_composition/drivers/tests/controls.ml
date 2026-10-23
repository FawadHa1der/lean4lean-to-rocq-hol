needs "tests/common.ml";;
let run_early_controls group =
  let open Lean4hol in
  let open Early_test in
  let module Env=Lean4hol_env in
  (match group with
   | "context" ->
     let g=[Bvar 1;Bvar 0;prop] in
     exact "dependent proof context" g (Bvar 0) (Bvar 1) (Bvar 2)
       (get "dependent proof conversion" (convert g (Bvar 0) (Bvar 1) (Bvar 2)));
     refusal "different nonproof context" (convert [prop;prop;prop] (Bvar 0) (Bvar 1) prop);
     refusal "open context" (convert [Bvar 0] (Bvar 0) (Bvar 0) (Bvar 0));
     test "negative index invalid" (match convert g (Bvar(-1)) (Bvar 1) (Bvar 2) with
       | Error {kind=Invalid_input;_}->true | _->false);
     let budget={remaining=100000} in
     let ty,h=equal_i budget g (Bvar 0) (Bvar 1) in
     exact "cached context original" g (Bvar 0) (Bvar 1) ty h;
     let _,again=equal_i budget g (Bvar 0) (Bvar 1) in
     exact "same-budget cache hit" g (Bvar 0) (Bvar 1) ty again;
     test "different context is not a cache hit"
       (try ignore(equal_i budget [prop;prop;prop] (Bvar 0) (Bvar 1));false
        with Stop {kind=Proof_failure;_} | Failure _->true);
     test "fresh empty budget cannot reuse cache"
       (try ignore(equal_i {remaining=0} g (Bvar 0) (Bvar 1));false
        with Stop {kind=Resource;_}->true)
   | "nonprop" ->
     let value=Sort Zero and typ=Sort(Succ Zero) in
     let other=beta typ value in
     exact "nonProp beta fallback" [] other value typ
       (get "nonProp ordinary conversion" (convert [] other value typ));
     refusal "unequal sorts" (run 10000 [] [prop;Sort(Succ Zero)]
       (fun st->equal_i st [] prop (Sort(Succ Zero))));
     refusal "distinct type variables are not proof-irrelevant"
       (convert [prop;prop] (Bvar 0) (Bvar 1) prop)
   | "forged" ->
     let bad=Lam(n,prop,Lam(n,Bvar 0,prop)) in
     refusal "forged proof body" (convert [] bad hp p);
     let hp_type=get "Prop premise" (check [] p prop) in
     let left=get "left proof premise" (check [] hp p)
     and right=get "right proof premise" (check [] (beta p hp) p) in
     let args=[quote_context [];quote_expr p;quote_expr hp;quote_expr(beta p hp)] in
     List.iteri(fun i _->
       let premises=List.filteri(fun j _->j<>i)[hp_type;left;right] in
       test "missing rule10 premise fails"
         (try ignore(rule {remaining=10000} 10 args premises);false
          with Stop {kind=Proof_failure;_} | Failure _->true)) [hp_type;left;right];
     List.iter(fun forged->test "guard refuses forged/open theorem"
       (try ignore(guard [] hp hp p forged);false
        with Stop {kind=Proof_failure;_}->true))
       [TRUTH;ASSUME(judgment [] hp hp p);ADD_ASSUM `P:bool` left];
     let budget={remaining=100000} in
     let _,valid=equal_i budget [] (beta p hp) hp in
     Hashtbl.replace equality_cache ([],beta p hp,hp) (p,TRUTH);
     test "mutated cached conclusion refused"
       (try ignore(equal_i budget [] (beta p hp) hp);false
        with Stop {kind=Proof_failure;_}->true);
     Hashtbl.replace equality_cache ([],beta p hp,hp) (p,ADD_ASSUM `P:bool` valid);
     test "mutated cached assumptions refused"
       (try ignore(equal_i budget [] (beta p hp) hp);false
        with Stop {kind=Proof_failure;_}->true)
   | "fuel-baseline" | "fuel-candidate" ->
     let label=function Ok _->"pass" | Error {kind=Resource;_}->"resource"
       | Error {kind=Invalid_input;_}->"invalid" | Error {kind=Unsupported;_}->"unsupported"
       | Error {kind=Proof_failure;_}->"proof-failure" in
     List.iter(fun fuel->
       let result=convert ~fuel [] (beta p hp) hp p in
       (match result with
        | Ok th->exact "fuel success remains exact" [] (beta p hp) hp p th
        | Error {kind=Resource;_}->test "bounded fuel resource" true
        | Error e->failwith("unexpected fuel result: "^e.message));
       if fuel=0 then test "zero fuel remains resource" (label result="resource");
       Printf.printf "EARLY_FUEL %s fuel=%d result=%s\n%!" group fuel (label result))
       [0;1;16;64;256;1024;100000];
     let budget={remaining=100000} in
     ignore(equal_i budget [] (beta p hp) hp);
     let first=budget.remaining in
     ignore(equal_i budget [] (beta p hp) hp);
     test "cache hit still consumes supplied fuel" (budget.remaining<first);
     Printf.printf "EARLY_FUEL_USED %s first=%d cache=%d\n%!" group (100000-first) (first-budget.remaining)
   | "crossbackend" ->
     let name=Str(Anonymous,"EarlyProof") in
     let admit typ value=fst(get "certified proof admission" (Env.admit Env.empty
       {Env.kind=Env.Definition;name;params=[];typ;value=Some value})) in
     let first=admit p hp and second=admit q hq in
     let term=Const(name,[]) in
     let h=get "first backend" (Env.convert first [] term (beta p hp) p) in
     checked first [] term (beta p hp) p h;
     refusal "same name in different backend" (Env.convert second [] term (beta p hp) p);
     checked second [] term (beta q hq) q
       (get "second backend exact proof" (Env.convert second [] term (beta q hq) q));
     checked first [] term (beta p hp) p
       (get "first backend again" (Env.convert first [] term (beta p hp) p));
     refusal "unadmitted name" (Env.convert Env.empty [] term hp p);
     refusal "illtyped declaration not trusted" (Env.admit Env.empty
       {Env.kind=Env.Theorem;name;params=[];typ=p;value=Some hq})
   | _ -> failwith "unknown early control group");
  finish group;;
