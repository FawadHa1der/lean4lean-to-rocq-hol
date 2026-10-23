(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Quotations are generated from a hash-pinned Arena export. These tests
   authenticate signature syntax only, not quotient admission or reduction. *)
let l4_quotient_syntax_axioms_before = axioms ();;
needs "hol/core.ml";;
needs "hol/quotient_syntax.ml";;
needs "hol/quotient_model.ml";;
needs "build/hol-quotient-inputs.ml";;

let l4_quotient_syntax_tests () =
  let open Lean4hol in
  let module Qmodel = Lean4hol_quotient_model in
  let count=ref 0 in
  let check label ok =
    if not ok then failwith("quotient syntax regression: " ^ label);
    incr count in
  let compute = REPEATC (CHANGED_CONV
    (REWRITE_CONV [l4_quot_signature;l4_quot_name;l4_quot_base;l4_quot_eq;
      l4_quot_arity;l4_quot_pi;l4_quot_arrow;l4_quot_relation;l4_quot_app;
      l4_quot_eq_type;l4_quot_refl_type;l4_apps;l4_lift] THENC NUM_REDUCE_CONV)) in
  let certify label left right =
    let target=mk_eq(left,right) in
    let th=prove(target,CONV_TAC compute) in
    check (label ^ " exact") (aconv (concl th) target);
    check (label ^ " closed") (hyp th=[] && frees(concl th)=[]) in
  let rec unquote_name t = match strip_comb t with
    | h,[] when h=`L4Anonymous` -> Anonymous
    | h,[n;s] when fst(dest_const h)="L4String" ->
      let bytes=List.map (fun c->Char.chr(int_of_string(string_of_num(dest_numeral c)))) (dest_list s) in
      Str(unquote_name n,String.of_seq(List.to_seq bytes))
    | h,[n;i] when fst(dest_const h)="L4Numeric" ->
      Num(unquote_name n,string_of_num(dest_numeral i))
    | _ -> failwith "unexpected fixture name" in
  let rec unquote_level t = match strip_comb t with
    | h,[] when h=`L4Zero` -> Zero
    | h,[u] when fst(dest_const h)="L4Succ" -> Succ(unquote_level u)
    | h,[u;v] when fst(dest_const h)="L4Max" -> Max(unquote_level u,unquote_level v)
    | h,[u;v] when fst(dest_const h)="L4IMax" -> Imax(unquote_level u,unquote_level v)
    | h,[n] when fst(dest_const h)="L4Param" -> Param(unquote_name n)
    | _ -> failwith "unexpected fixture universe" in
  let model_kind k = match fst(dest_const k) with
    | "L4QuotType" -> Qmodel.Qtype | "L4QuotCtor" -> Qmodel.Qctor
    | "L4QuotLift" -> Qmodel.Qlift | "L4QuotInd" -> Qmodel.Qind
    | _ -> failwith "unexpected fixture quotient kind" in
  List.iter (fun (k,n,a,u,v,arity) ->
    certify "Arena quotient name" (node "l4_quot_name" [k]) n;
    certify "Arena quotient universe count" (node "l4_quot_arity" [k]) (number arity);
    certify "Arena quotient signature" (node "l4_quot_signature" [k;u;v]) a;
    let kind=model_kind k in
    certify "ML quotient name" (quote_name(Qmodel.name kind)) n;
    certify "ML quotient signature"
      (quote_expr(Qmodel.signature {remaining=100000} kind (unquote_level u) (unquote_level v))) a;
    check "ML universe arity" (Qmodel.arity kind=arity);
    check "ML kind quotation" (aconv(Qmodel.quote_kind kind)k))
    l4_quotient_signature_inputs;
  List.iter (fun (u,a,c) ->
    certify "Arena equality type prerequisite" (node "l4_quot_eq_type" [u]) a;
    certify "Arena reflexivity prerequisite" (node "l4_quot_refl_type" [u]) c;
    certify "ML equality prerequisite"
      (quote_expr(Qmodel.equality_type {remaining=100000} (unquote_level u))) a;
    certify "ML reflexivity prerequisite"
      (quote_expr(Qmodel.reflexivity_type {remaining=100000} (unquote_level u))) c)
    l4_quotient_eq_inputs;
  check "all four quotient constructors tested" (List.length l4_quotient_signature_inputs=4);
  check "one equality prerequisite tested" (List.length l4_quotient_eq_inputs=1);
  check "no new HOL axioms" (axioms()=l4_quotient_syntax_axioms_before);
  print_endline("HOL_QUOTIENT_SYNTAX_TESTS_PASSED " ^ string_of_int !count);;

l4_quotient_syntax_tests ();;
