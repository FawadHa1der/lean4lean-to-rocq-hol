let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/derived_bool.ml";;

let run_bool_cases suffix group =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Bool=Lean4hol_derived_bool in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let refusal label = function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_}->test label true
    | Error e->failwith(label^": unexpected error class: "^e.message)
    | Ok _->failwith(label^": accepted") in
  let nn=Str(Anonymous,"Nat") and bn=Str(Anonymous,"Bool") in
  let nat=Const(nn,[]) and bool=Const(bn,[])
  and zero=Const(Str(nn,"zero"),[]) and successor=Const(Str(nn,"succ"),[])
  and tru=Const(Str(bn,"true"),[]) and fal=Const(Str(bn,"false"),[]) in
  let lam a b=Lam(Anonymous,a,b) and pi a b=Pi(Anonymous,a,b) in
  let unary=pi nat bool in
  let signature=pi nat unary in
  let app2 f x y=App(App(f,x),y) and succ x=App(successor,x) in
  let recnat ty base step n=Env.apps (Const(Str(nn,"rec"),[Succ Zero]))
    [lam nat ty;base;step;n] in
  let build b00 b0s bs0 diagonal =
    let base=lam nat(recnat bool b00 (lam nat(lam bool b0s)) (Bvar 0)) in
    let step=lam nat(lam unary(lam nat
      (recnat bool bs0 (lam nat(lam bool diagonal)) (Bvar 0)))) in
    lam nat(recnat unary base step (Bvar 0)) in
  let op,b0s,opposite=match suffix with
    | "beq"->Bool.Beq,fal,tru | "ble"->Bool.Ble,tru,fal
    | _->failwith "unknown comparison operation" in
  let diagonal=App(Bvar 3,Bvar 1) in
  let body=build tru b0s fal diagonal in
  let block n cs={Env.inductive_name=n;inductive_level=Succ Zero;constructors=cs;claims=[]} in
  let nat_block=block nn [Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]]
  and bool_block=block bn [Str(bn,"false"),[];Str(bn,"true"),[]] in
  let admit env b =
    let b={b with Env.claims=Env.generate {remaining=100000} b} in
    fst(get "ordinary inductive admission" (Env.admit_inductive env b)) in
  let nat_env=admit Env.empty nat_block in
  let env=admit nat_env bool_block in
  let qe0=Env.quote_env env and qp0=Env.quote_policy env in
  let certify env g b=get "ordinary four-case contract and evaluation theorem" (Bool.prepare env g op b) in
  let checked env g b answer left right =node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;
     quote_expr(app2 b (Natlit left) (Natlit right));quote_expr answer;quote_expr bool] in
  let cases env g b c =
    test "opaque certificate retains original source" (Bool.body c=b);
    test "opaque certificate retains exact context" (Bool.context c=g);
    List.iter(fun h->test "universal theorem and contract are closed"
      (hyp h=[] && frees(concl h)=[])) [Bool.theorem c;Bool.contract c];
    let pairs=["0","0",true,true;"0","1",false,true;"1","0",false,false;
      "1","1",true,true;"1","2",false,true;"2","1",false,false;
      "7","13",false,true;"13","7",false,false;"29","29",true,true;
      "9876543210987654321098765432109876543210","9876543210987654321098765432109876543210",true,true;
      "9876543210987654321098765432109876543210","9876543210987654321098765432109876543211",false,true;
      "9876543210987654321098765432109876543211","9876543210987654321098765432109876543210",false,false;
      "0",("1"^String.make 120 '0'),false,true;
      ("1"^String.make 120 '0'),"0",false,false;
      (String.make 120 '9'),("1"^String.make 120 '0'),false,true;
      ("1"^String.make 120 '0'),(String.make 120 '9'),false,false] in
    List.iter(fun (left,right,equal,le)->
      let expected=if (if suffix="beq" then equal else le) then tru else fal in
      let answer,h=get "derived numeral comparison" (Bool.evaluate c left right) in
      test "exact numeral result" (answer=expected);
      test "exact typed equality with original source" (hyp h=[] && frees(concl h)=[] &&
        aconv(concl h)(checked env g b expected left right))) pairs in
  let positive env g b =let c=certify env g b in cases env g b c;c in
  (match group with
   | "empty" ->
      ignore(positive env [] body);
      List.iter(fun(left,right,answer)->
        let h=get "independent ordinary small comparison" (Env.convert env []
          (app2 body (Natlit left) (Natlit right)) answer bool) in
        test "ordinary small judgment is exact and closed"
          (hyp h=[] && aconv(concl h)(checked env [] body answer left right)))
        ["0","0",tru;"0","1",b0s;"1","0",fal;"1","1",tru]
   | "nat-context" -> ignore(positive env [nat] body)
   | "dependent" -> ignore(positive env [Bvar 0;Sort(Succ Zero)] body)
   | "beta" -> ignore(positive env [] (App(lam signature(Bvar 0),body)))
   | "let" -> ignore(positive env [] (Let(Anonymous,signature,body,Bvar 0)))
   | "named" ->
      let name=Str(Anonymous,"LocalDerived"^suffix) in
      let env',_=get "ordinary named definition admission" (Env.admit env
        {Env.kind=Env.Definition;name;params=[];typ=signature;value=Some body}) in
      ignore(positive env' [Bvar 0;Sort(Succ Zero)] (Const(name,[])))
   | "guards" ->
      let c=positive env [] body in
      let law=Bool.contract c in
      let use env gamma operation source proof=Bool.of_contract env gamma operation source proof in
      refusal "wrong environment" (use nat_env [] op body law);
      refusal "wrong context" (use env [nat] op body law);
      refusal "wrong body" (use env [] op (lam nat(lam nat tru)) law);
      refusal "wrong operation" (use env [] (if suffix="beq" then Bool.Ble else Bool.Beq) body law);
      refusal "unproved contract" (use env [] op body (ASSUME(concl law)));
      refusal "unrelated true theorem" (use env [] op body TRUTH);
      refusal "extra open assumption" (use env [] op body (ADD_ASSUM `P:bool` law));
      let expanded=REWRITE_RULE [l4_prim_beq_contract;l4_prim_ble_contract;l4_prim_bool_cases_contract] law in
      let parts=CONJUNCTS expanded in
      List.iteri(fun i _->refusal "missing symbolic contract premise"
        (use env [] op body (end_itlist CONJ(List.filteri(fun k _->i<>k) parts)))) parts;
      let policy=get "unused policy" (Env.with_axioms
        [{Env.axiom_name=Str(Anonymous,"UnusedBooleanPermission");axiom_params=[];axiom_type=nat}]) in
      let policy_env=admit(admit policy nat_block) bool_block in
      test "policy poison has identical entries" (aconv(Env.quote_env policy_env)(Env.quote_env env));
      refusal "policy replay" (use policy_env [] op body law);
      List.iter(fun(s,t)->test "malformed numeric input"
        (match Bool.evaluate c s t with Error {kind=Invalid_input;_}->true | _->false))
        ["","0";"01","0";"-1","0";"0","+1";"0","1x"];
      test "evaluation zero fuel is resource" (match Bool.evaluate ~fuel:0 c "0" "0" with
        | Error {kind=Resource;_}->true | _->false);
      test "preparation zero fuel is resource" (match Bool.prepare ~fuel:0 env [] op body with
        | Error {kind=Resource;_}->true | _->false)
   | "missing" ->
      ignore(positive env [] body);
      refusal "missing Bool" (Bool.prepare nat_env [] op body);
      refusal "missing Nat and Bool" (Bool.prepare Env.empty [] op body);
      refusal "incorrect result signature" (Bool.prepare env [] op (lam nat(lam nat zero)));
      refusal "open candidate" (Bool.prepare env [signature] op (Bvar 0));
      refusal "ill-formed dependent context" (Bool.prepare env [Bvar 0] op body)
   | "impostor-zz" | "impostor-zs" | "impostor-sz" | "impostor-ss" | "finite" ->
      ignore(positive env [] body);
      let mutant=match group with
        | "impostor-zz"->build fal b0s fal diagonal
        | "impostor-zs"->build tru opposite fal diagonal
        | "impostor-sz"->build tru b0s tru diagonal
        | "impostor-ss"->build tru b0s fal (App(Bvar 3,succ(Bvar 1)))
        | _->build tru b0s fal tru in
      let h=get "impostor independently well typed" (Env.check env [] mutant signature) in
      test "typed impostor positive gate" (hyp h=[]);
      if group="finite" then List.iter(fun n->
        let h=get "finite diagonal examples pass" (Env.convert env [] (app2 mutant n n) tru bool) in
        test "finite sample not a universal contract" (hyp h=[])) [zero;succ zero];
      refusal "typed impostor fails full symbolic contract" (Bool.prepare env [] op mutant)
   | _->failwith "unknown comparison test group");
  test "original environment unmodified" (aconv(Env.quote_env env)qe0);
  test "original policy unmodified" (aconv(Env.quote_policy env)qp0);
  test "native clauses unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission clauses unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "\nCOMPOSED_WORK_PASS bool-%s-%s %d\n%!" suffix group !count;;
