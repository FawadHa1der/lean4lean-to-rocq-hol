let before_axioms = axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/core.ml";;

let run_closed_computation_tests () =
  let open Lean4hol in
  let checks = ref 0 in
  let test label b = incr checks; if not b then failwith label in
  let fails f = try ignore(f()); false with Failure _ -> true in
  let guard label tm th =
    test (label^" no hypotheses") (hyp th=[]);
    test (label^" exact original input") (lhs(concl th)=tm) in
  let compare label tm =
    let ordinary=compute_object_ordinary tm in
    let fast=compute_object tm in
    guard (label^" ordinary") tm ordinary;
    guard (label^" optimized") tm fast;
    test (label^" equal full conclusions") (concl fast=concl ordinary) in
  let failed_guard_fallback label tm attempt =
    let called=ref false in
    let injected input = called:=true; attempt input in
    let ordinary=compute_object_ordinary tm in
    let fallback=(TRY_CONV injected THENC compute_object_ordinary) tm in
    test (label^" guard exercised") !called;
    guard (label^" guarded fallback") tm fallback;
    test (label^" exact ordinary fallback") (concl fallback=concl ordinary) in
  let group=try Sys.getenv "CLOSED_GROUP" with Not_found->"differential" in
  let zero=quote_expr(Sort Zero) in
  let an=`L4Anonymous` in
  let closed=[
    zero; `L4Sort (L4IMax (L4Param L4Anonymous) (L4Succ L4Zero))`;
    `L4Sort (u:l4_level)`;
    `L4Const L4Anonymous [u:l4_level; L4Zero]`;
    `L4App (L4Const L4Anonymous []) (L4Sort L4Zero)`;
    `L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0)`;
    `L4Pi L4Anonymous (L4Sort L4Zero) (L4BVar 0)`;
    `L4Lam L4Anonymous (L4Sort L4Zero)
       (L4Pi L4Anonymous (L4BVar 0) (L4BVar 1))`;
    `L4Let L4Anonymous (L4Sort L4Zero) (L4Sort L4Zero) (L4BVar 0)`;
    `L4NatLit 0`; `L4NatLit 42`;
    `L4Proj L4Anonymous 19 (L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0))`;
    `L4StrLit []`; `L4StrLit [65]`;
    `L4StrLit [1114112]`] in
  let open_terms=[
    `L4BVar 0`; `L4BVar 1`; `L4BVar 90000000000000000000000`;
    `L4App (L4BVar 0) (L4Sort L4Zero)`;
    `L4Lam L4Anonymous (L4BVar 0) (L4BVar 0)`;
    `L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 1)`;
    `L4Pi L4Anonymous (L4BVar 0) (L4BVar 0)`;
    `L4Pi L4Anonymous (L4Sort L4Zero) (L4BVar 1)`;
    `L4Let L4Anonymous (L4BVar 0) (L4Sort L4Zero) (L4BVar 0)`;
    `L4Let L4Anonymous (L4Sort L4Zero) (L4BVar 0) (L4BVar 0)`;
    `L4Let L4Anonymous (L4Sort L4Zero) (L4Sort L4Zero) (L4BVar 1)`;
    `L4Proj L4Anonymous 0 (L4BVar 0)`] in
  if group="differential" then (
    L4_closed_computation.clear();
    List.iter(fun e->
      test "closed scope obtained" (L4_closed_computation.scope e<>None);
      List.iter(fun d->List.iter(fun k->
        let tm=node "l4_lift" [e;number d;number k] in
        let th=L4_closed_computation.convert tm in
        guard "direct fast lift" tm th;
        test "direct fast lift result" (rhs(concl th)=e);
        compare "lift" tm) [0;1;9;31]) [0;1;7;99];
      List.iter(fun s->
        List.iter(fun k->
          let tm=node "l4_subst" [e;number k;s] in
          let h=L4_closed_computation.convert tm in
          guard "direct fast subst" tm h;
          test "direct fast subst result" (rhs(concl h)=e);
          compare "subst" tm) [0;1;9;31];
        let tm=node "l4_inst" [s;e] in
        let h=L4_closed_computation.convert tm in
        guard "direct fast inst" tm h;
        test "direct fast inst result" (rhs(concl h)=e);
        compare "inst" tm)
        [`L4BVar 0`;`L4BVar 3`;zero;`L4Lam L4Anonymous (L4BVar 0) (L4BVar 1)`]
    ) closed;
    List.iter(fun e->
      test "open scope not certified" (L4_closed_computation.scope e=None);
      List.iter(fun k->
        let tm=node "l4_lift" [e;`2`;number k] in
        test "open direct conversion declines" (fails(fun()->L4_closed_computation.convert tm));
        compare "open lift fallback" tm;
        compare "open subst fallback" (node "l4_subst" [e;number k;zero])) [0;1;9];
      compare "open inst fallback" (node "l4_inst" [zero;e])) open_terms;
    List.iter(compare "non-target fallback")
      [`EL 1 [L4Sort L4Zero; L4BVar 0]`;
       `LENGTH [L4BVar 0;L4BVar 1]`; `L4Sort L4Zero`;
       `l4_lift (l4_inst (L4Sort L4Zero) (L4BVar 0)) 2 0`;
       `l4_subst (L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0)) 0
          (l4_lift (L4BVar 0) 2 0)`;
       `l4_lift (L4NatLit 100000000000000000000000000000000000000000000) 2 0`;
       `l4_subst (L4StrLit [76;101;97;110;128512]) 3 (L4BVar 2)`];
    let a=L4_closed_computation.stats() in
    test "cache actually exercised" (a.hits>0 && a.count>0)
  ) else if group="guards" then (
    L4_closed_computation.clear();
    let e=`L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0)` in
    let good=match L4_closed_computation.scope e with Some h->h | None->failwith "scope" in
    test "valid exact guard" (L4_closed_computation.guard_scope e good=good);
    test "hypothetical scope denied" (fails(fun()->L4_closed_computation.guard_scope e
      (ASSUME(node "l4_scoped" [e;`0`]))));
    test "wrong scope denied" (fails(fun()->L4_closed_computation.guard_scope zero good));
    let tm=node "l4_lift" [e;`2`;`0`] in
    let h=L4_closed_computation.convert tm in
    test "valid conversion guard" (L4_closed_computation.guard_conversion tm e h=h);
    test "hypothetical conversion denied" (fails(fun()->L4_closed_computation.guard_conversion tm e
      (ASSUME(mk_eq(tm,e)))));
    test "wrong left denied" (fails(fun()->L4_closed_computation.guard_conversion
      (node "l4_lift" [e;`3`;`0`]) e h));
    test "wrong right denied" (fails(fun()->L4_closed_computation.guard_conversion tm zero h));
    List.iter(fun(label,bad)->
      test (label^" fails before wrapper") (fails(fun()->bad tm));
      failed_guard_fallback label tm bad)
      ["hypothetical scope",(fun _->L4_closed_computation.guard_scope e
         (ASSUME(node "l4_scoped" [e;`0`])));
       "wrong scope",(fun _->L4_closed_computation.guard_scope zero good);
       "hypothetical conversion",(fun input->L4_closed_computation.guard_conversion input e
         (ASSUME(mk_eq(input,e))));
       "wrong left",(fun _->L4_closed_computation.guard_conversion
         (node "l4_lift" [e;`3`;`0`]) e h);
       "wrong right",(fun input->L4_closed_computation.guard_conversion input zero h)];
    let spoof=mk_comb(mk_var("L4Sort",`:l4_level->l4_expr`),`L4Zero`) in
    let unknowns=[`e:l4_expr`;spoof;`L4BVar (i:num)`;
      `L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar (i:num))`;
      `(f:l4_expr->l4_expr) (L4Sort L4Zero)`;
      `l4_lift (L4Sort L4Zero) 1 0`] in
    List.iter(fun x->
      L4_closed_computation.clear();
      test "unknown scope unavailable" (L4_closed_computation.scope x=None);
      test "unknown not retained" ((L4_closed_computation.stats()).count=0);
      compare "unknown lift fallback" (node "l4_lift" [x;`1`;`0`]);
      compare "unknown subst fallback" (node "l4_subst" [x;`0`;zero]);
      compare "unknown inst fallback" (node "l4_inst" [zero;x])) unknowns;
    List.iter(fun x->test "wrong operation head or arity" (fails(fun()->
      L4_closed_computation.convert x)))
      [mk_comb(mk_var("l4_inst",`:l4_expr->l4_expr->l4_expr`),zero);
       mk_comb(mk_comb(mk_var("l4_inst",`:l4_expr->l4_expr->l4_expr`),zero),e);
       node "l4_lift" [e;`1`];node "l4_subst" [e];node "L4Sort" [`L4Zero`]];
    test "symbolic universe really supported"
      (L4_closed_computation.scope `L4Sort (u:l4_level)`<>None);
    let symbolic=match L4_closed_computation.scope `L4Sort (u:l4_level)` with
      | Some h->h | None->failwith "symbolic universe scope" in
    test "symbolic scope has no hypotheses but has HOL free variables"
      (hyp symbolic=[] && frees(concl symbolic)<>[]);
    test "symbolic scope exact conclusion"
      (concl symbolic=`l4_scoped (L4Sort (u:l4_level)) 0`);
    test "scope is not typing" (L4_closed_computation.scope `L4StrLit [1114112]`<>None);
    L4_closed_computation.clear();
    let deep=ref zero in
    for _=1 to 10000 do deep:=node "L4App" [!deep;zero] done;
    test "deep syntax refused without recursive equality" (L4_closed_computation.scope !deep=None);
    test "deep key never retained" ((L4_closed_computation.stats()).count=0);
    let huge_label=mk_var(String.make 10000 'x',`:l4_level`) in
    test "oversized symbolic universe key refused"
      (L4_closed_computation.scope(node "L4Sort" [huge_label])=None);
    test "oversized label not retained" ((L4_closed_computation.stats()).count=0);
    (* Exercise an actual production guard failure: the expression and scope
       fit but the larger conversion certificate exceeds the local guard cap.
       The injected tests above cover wrong/hypothetical proof guards without
       adding an injection hook to production. *)
    let body=ref `L4BVar 0` and bounded_guard_case=ref None in
    for _=1 to 32 do
      body:=node "L4Lam" [an;zero;!body];
      match !bounded_guard_case,L4_closed_computation.scope !body with
      | None,Some scope ->
        let input=node "l4_lift" [!body;`1`;`0`] in
        let certificate=SPECL [`1`;`0`] (MP (SPEC !body l4_lift_closed) scope) in
        if fails(fun()->L4_closed_computation.guard_conversion input !body certificate)
        then bounded_guard_case:=Some input
      | _ -> ()
    done;
    (match !bounded_guard_case with
     | None->failwith "no natural conversion guard-bound witness"
     | Some input->
       test "production guard failure declines fast conversion"
         (fails(fun()->L4_closed_computation.convert input));
       compare "production guard-bound fallback" input);
    for i=0 to 511 do
      ignore(L4_closed_computation.scope(node "L4NatLit" [number i]));
      ignore(L4_closed_computation.scope(node "L4BVar" [number i]));
      let s=L4_closed_computation.stats() in
      test "native count bound" (s.count<=64);
      test "native weighted bound" (s.weight<=65536)
    done;
    test "native eviction exercised" ((L4_closed_computation.stats()).evictions>0);
    L4_closed_computation.clear();
    let s=L4_closed_computation.stats() in
    test "native reset observable" (s.count=0 && s.weight=0 && s.hits=0 && s.misses=0);
    test "post-clear theorem independently replayed" (L4_closed_computation.scope e<>None)
  ) else if group="benchmark" then (
    let body=ref `L4BVar 0` in
    for _=1 to 3 do body:=node "L4Lam" [an;zero;!body] done;
    let inputs=List.init 64(fun i->node "l4_lift" [!body;number(i+1);`0`]) @
      List.init 64(fun i->node "l4_subst" [!body;number i;zero]) in
    let measure f = let start=Sys.time() in
      let proofs=List.map f inputs in Sys.time()-.start,proofs in
    L4_closed_computation.clear();
    test "benchmark fast path eligible" (not(fails(fun()->L4_closed_computation.convert(List.hd inputs))));
    L4_closed_computation.clear();
    let ordinary,old=measure compute_object_ordinary in
    let optimized,fresh=measure compute_object in
    List.iter2(fun x y->test "benchmark exact conclusions" (concl x=concl y && hyp x=[] && hyp y=[])) old fresh;
    Printf.printf "CLOSED_COMPUTATION_TIMING ordinary_cpu=%.6f optimized_cpu=%.6f cases=128\n%!" ordinary optimized
  ) else failwith "unknown closed computation group";
  test "no logical rule extension" (List.length(CONJUNCTS l4_defeq_RULES)=13);
  test "unchanged axioms" (axioms()=before_axioms);
  Printf.printf "CLOSED_COMPUTATION_NATIVE_PASS %s %d\n%!" group !checks;;
run_closed_computation_tests ();;
exit 0;;
