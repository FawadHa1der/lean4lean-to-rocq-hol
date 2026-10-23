let before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/nat_evaluation_checked.ml";;
needs "hol/environment.ml";;
let run_nat_evaluation_cases () =
  let open Lean4hol in
  let module Env=Lean4hol_env in
  let count=ref 0 in
  let test label ok=incr count;if not ok then failwith label in
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message) in
  let raw th=List.nth(CONJUNCTS(REWRITE_RULE [l4_checked] th)) 2 in
  let name=Str(Anonymous,"Nat") in
  let succ=Const(Str(name,"succ"),[]) and nat=Const(name,[]) in
  let block={Env.inductive_name=name;inductive_level=Succ Zero;
    constructors=[Str(name,"zero"),[];Str(name,"succ"),[Env.Recursive]];claims=[]} in
  let block={block with Env.claims=Env.generate {remaining=100000} block} in
  let env,valid=get "genuine canonical Nat admission" (Env.admit_inductive Env.empty block) in
  test "valid canonical environment" (hyp valid=[] && frees(concl valid)=[]);
  let qe=Env.quote_env env and qp=Env.quote_policy env in
  let qnat=quote_expr nat and qs=quote_expr succ in
  let n=`n:num` in
  let lit k=node "L4NatLit" [k] and app f x=node "L4App" [f;x] in
  let unary=Pi(Anonymous,nat,nat) in
  let rules=Array.of_list(CONJUNCTS l4_edef_RULES) in
  let simplify=REWRITE_CONV [l4_nat_name;l4_inst;l4_subst;l4_lift;EL;HD;TL;LENGTH]
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV [] in
  List.iter(fun g->
    let qg=quote_context g in
    let j a b ty=node "l4_edef" [qe;qg;a;b;ty] in
    let checked a b ty=node "l4_checked" [qp;qe;qg;a;b;ty] in
    let use i args ps =
      let h=CONV_RULE simplify(SPECL(qe::qg::args)rules.(i)) in
      MP h(if List.length ps=1 then List.hd ps else end_itlist CONJ ps) in
    let hs=get "successor typing" (Env.check env g succ unary) in
    let hn=raw(get "Nat typing" (Env.check env g nat (Sort(Succ Zero)))) in
    let lit_type k=use 16 [k] [hn] in
    let sym a b h=use 6 [a;b;qnat] [h] in
    let trans a b c h k=use 7 [a;b;c;qnat] [h;k] in
    let congr f a b hf hab=use 2 [f;f;a;b;`L4Anonymous`;qnat;qnat] [hf;hab] in
    List.iter(fun (f,m)->
      let qf=quote_expr f in
      let hf=get "function typing" (Env.check env g f unary) in
      let hb=get "function zero equation" (Env.convert env g
        (App(f,Natlit "0")) (Natlit(string_of_int m)) nat) in
      let ln=lit n in
      let sln=app qs ln in
      let hln=lit_type n in
      let hsln=congr qs ln ln (raw hs) hln in
      let recurrence=if m=1 then congr qs sln sln (raw hs) hsln else
        let hv=raw(get "identity binder typing" (Env.check env (nat::g) (Bvar 0) nat)) in
        let beta v ht=use 8 [`L4Anonymous`;qnat;`L4BVar 0`;qnat;v] [hv;ht] in
        let left=beta sln hsln in
        let right=congr qs (app qf ln) ln (raw hs) (beta ln hln) in
        trans (app qf sln) sln (app qs(app qf ln)) left
          (sym (app qs(app qf ln)) sln right) in
      test "original recurrence exact" (aconv(concl recurrence)
        (j (app qf sln) (app qs(app qf ln)) qnat));
      let hrec=GEN n recurrence in
      let premises=[raw hf;raw hs;raw hb;hrec] in
      let law=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;qg;qf;number m] l4_edef_nat_recurrence) in
      let hall=MP law(end_itlist CONJ premises) in
      test "general result has no assumptions" (hyp hall=[] && frees(concl hall)=[]);
      let hvalid,hctx=match CONJUNCTS(REWRITE_RULE [l4_checked] hf) with
        | [a;b;_]->a,b | _->failwith "checked premise arity" in
      let checked_rec=GEN n(EQ_MP (SYM(REWRITE_CONV [l4_checked]
        (checked (app qf sln) (app qs(app qf ln)) qnat)))
        (CONJ hvalid(CONJ hctx recurrence))) in
      let checked_law=REWRITE_RULE [l4_prim_unary;l4_prim_nat;l4_prim_succ;l4_nat_name]
        (SPECL [qp;qe;qg;qf;number m] l4_checked_nat_recurrence) in
      let checked_all=MP checked_law(end_itlist CONJ [hf;hs;hb;checked_rec]) in
      test "checked general result closed" (hyp checked_all=[] && frees(concl checked_all)=[]);
      List.iter(fun text->
        let k=natural text in
        let output=rhs(concl(NUM_REDUCE_CONV(mk_comb(mk_comb(`(+):num->num->num`,number m),k)))) in
        let expected=j (app qf(lit k)) (lit output) qnat in
        let actual=CONV_RULE NUM_REDUCE_CONV(SPEC k hall) in
        test "exact evaluated native result" (aconv(concl actual) expected && hyp actual=[]);
        let actual_checked=CONV_RULE NUM_REDUCE_CONV(SPEC k checked_all) in
        test "exact evaluated checked result" (aconv(concl actual_checked)
          (checked (app qf(lit k)) (lit output) qnat) && hyp actual_checked=[])
      )["0";"1";"2";"17";"12345678901234567890123456789012345678901234567890"];
      let refuses rule ps=try ignore(MP rule(end_itlist CONJ ps));false with Failure _->true in
      test "missing recurrence refused" (refuses law(List.tl premises));
      let wrong_m=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;qg;qf;number(m+1)] l4_edef_nat_recurrence) in
      test "wrong base value refused" (refuses wrong_m premises);
      let wrong_g=REWRITE_RULE [l4_nat_name]
        (SPECL [qe;quote_context(nat::g);qf;number m] l4_edef_nat_recurrence) in
      test "wrong context refused" (refuses wrong_g premises);
      let wrong_env=REWRITE_RULE [l4_nat_name]
        (SPECL [`[]:l4_entry list`;qg;qf;number m] l4_edef_nat_recurrence) in
      test "wrong environment refused" (refuses wrong_env premises);
      let conditional=MP law(ASSUME(fst(dest_imp(concl law)))) in
      test "assumed premises remain hypotheses" (hyp conditional<>[])
    )[Lam(Anonymous,nat,Bvar 0),0;succ,1]
  )[[];[nat]];
  test "native rule count unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
  test "admission rule count unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
  test "axioms unchanged" (axioms()=before_axioms);
  Printf.printf "PRIVATE_NAT_EVALUATION_DONE %d_concrete_assertions unchanged_axioms\n%!" !count;;
run_nat_evaluation_cases ();;
exit 0;;
