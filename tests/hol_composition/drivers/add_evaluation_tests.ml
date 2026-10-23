let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/add_evaluation.ml";;
needs "hol/primitive_validation.ml";;
let run_add_evaluation_cases () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let module Prim=Lean4hol_primitive in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2 in
  let nn=Str(Anonymous,"Nat") in
  let nat=Const(nn,[]) and zero=Const(Str(nn,"zero"),[])
  and successor=Const(Str(nn,"succ"),[]) in
  let lam x=Lam(Anonymous,nat,x) in
  let recursor=Const(Str(nn,"rec"),[Succ Zero]) in
  let body=lam(lam(Env.apps recursor [lam nat;Bvar 1;
    lam(lam(App(successor,Bvar 0)));Bvar 0])) in
  let block={Env.inductive_name=nn;inductive_level=Succ Zero;
    constructors=[Str(nn,"zero"),[];Str(nn,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,valid=get "actual Nat admission" (Env.admit_inductive Env.empty block) in
  let qe=Env.quote_env env and qp=Env.quote_policy env and qb=quote_expr body in
  let jchecked=node "l4_checked" [qp;qe] and jraw=node "l4_edef" [qe] in
  let certificate=get "original symbolic add contract" (Prim.check_add env body) in
  let checked_law=Prim.add_theorem certificate in
  test "actual symbolic contract closed" (hyp checked_law=[] && frees(concl checked_law)=[]);
  let bridge=prove(list_mk_forall([`g:l4_expr list`;`x:l4_expr`;`y:l4_expr`;`a:l4_expr`],
      mk_imp(list_mk_comb(jchecked,[`g:l4_expr list`;`x:l4_expr`;`y:l4_expr`;`a:l4_expr`]),
             list_mk_comb(jraw,[`g:l4_expr list`;`x:l4_expr`;`y:l4_expr`;`a:l4_expr`]))),
    REWRITE_TAC [l4_checked] THEN MESON_TAC []) in
  let law=MP(MP(SPECL [jchecked;jraw;qb] l4_prim_add_mono) bridge) checked_law in
  let scope=prove(node "l4_scoped" [qb;`0`],
    REWRITE_TAC [l4_scoped] THEN CONV_TAC NUM_REDUCE_CONV) in
  let hnat0=get "Nat typed in empty context" (Env.check env [] nat (Sort(Succ Zero))) in
  let hnat1=get "Nat typed under Nat binder" (Env.check env [nat] nat (Sort(Succ Zero))) in
  let hz=get "zero typing" (Env.check env [] zero nat) in
  let hs=get "successor typing" (Env.check env [] successor (Pi(Anonymous,nat,nat))) in
  let premises=[scope;law;raw hnat0;raw hnat1;raw hz;raw hs] in
  let theorem=REWRITE_RULE [l4_nat_name](SPECL [qe;qb] l4_edef_add_evaluation) in
  let all=MP theorem(end_itlist CONJ premises) in
  test "all natural pairs proved without hypotheses" (hyp all=[] && frees(concl all)=[]);
  let _,context=match CONJUNCTS(REWRITE_RULE [l4_checked] hnat0) with
    | [a;b;_]->a,b | _->failwith "checked premise arity" in
  let cases=["0","0";"0","37";"37","0";"2","3";"255","256";
    "12345678901234567890123456789012345678901234567890","98765432109876543210987654321098765432109876543210"] in
  List.iter(fun (left,right)->
    let m=natural left and n=natural right in
    let sum=rhs(concl(NUM_REDUCE_CONV(node "+" [m;n]))) in
    let call=node "L4App" [node "L4App" [qb;node "L4NatLit" [m]];node "L4NatLit" [n]] in
    let output=node "L4NatLit" [sum] and ty=quote_expr nat in
    let expected=list_mk_comb(jraw,[`[]:l4_expr list`;call;output;ty]) in
    let proof=CONV_RULE NUM_REDUCE_CONV(SPECL [m;n] all) in
    test "exact raw addition result" (aconv(concl proof) expected && hyp proof=[]);
    let expected_checked=list_mk_comb(jchecked,[`[]:l4_expr list`;call;output;ty]) in
    let checked_proof=EQ_MP(SYM(REWRITE_CONV [l4_checked] expected_checked))
      (CONJ valid(CONJ context proof)) in
    test "exact checked addition result" (aconv(concl checked_proof) expected_checked && hyp checked_proof=[]);
    let wrong=rhs(concl(NUM_REDUCE_CONV(mk_comb(`SUC`,sum)))) in
    test "wrong result does not match certificate" (not(aconv(concl proof)
      (list_mk_comb(jraw,[`[]:l4_expr list`;call;node "L4NatLit" [wrong];ty]))))
  ) cases;
  let refuses th hs=try ignore(MP th(end_itlist CONJ hs));false with Failure _->true in
  List.iteri(fun omitted _->
    test "each premise required" (refuses theorem(List.filteri(fun i _->i<>omitted) premises))
  ) premises;
  let wrong_body=REWRITE_RULE [l4_nat_name]
    (SPECL [qe;quote_expr(lam(Bvar 0))] l4_edef_add_evaluation) in
  test "wrong body cannot reuse contract" (refuses wrong_body premises);
  let wrong_env=REWRITE_RULE [l4_nat_name]
    (SPECL [`[]:l4_entry list`;qb] l4_edef_add_evaluation) in
  test "wrong environment cannot reuse contract" (refuses wrong_env premises);
  let assumed=MP theorem(ASSUME(fst(dest_imp(concl theorem)))) in
  test "assumed contract retains hypotheses" (hyp assumed<>[]);
  test "no added rules" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "no added admission clauses" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "PRIVATE_NAT_EVALUATION_DONE %d_add_concrete_assertions unchanged_axioms\n%!" !count;;
run_add_evaluation_cases ();;
exit 0;;
