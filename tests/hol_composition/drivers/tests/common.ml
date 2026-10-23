let early_before_axioms=axioms();;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/environment.ml";;

module Early_test = struct
  open Lean4hol
  let count=ref 0
  let test label ok=incr count;if not ok then failwith label
  let get label=function Ok x->x | Error e->failwith(label^": "^e.message)
  let refusal label=function
    | Error {kind=Proof_failure;_} | Error {kind=Unsupported;_}->test label true
    | Error e->failwith(label^": wrong error: "^e.message)
    | Ok _->failwith(label^": accepted")
  let n=Anonymous
  let prop=Sort Zero
  let p=Pi(n,prop,Pi(n,Bvar 0,Bvar 1))
  let hp=Lam(n,prop,Lam(n,Bvar 0,Bvar 0))
  let q=Pi(n,prop,Pi(n,prop,Pi(n,Bvar 1,Pi(n,Bvar 1,Bvar 3))))
  let hq=Lam(n,prop,Lam(n,prop,Lam(n,Bvar 1,Lam(n,Bvar 1,Bvar 1))))
  let beta typ proof=App(Lam(n,typ,Bvar 0),proof)
  let zeta typ proof=Let(n,typ,proof,Bvar 0)
  let exact label g e e' typ th =
    test label (hyp th=[] && frees(concl th)=[] && aconv(concl th)(judgment g e e' typ))
  let checked env g e e' typ th =
    let expected=node "l4_checked" [Lean4hol_env.quote_policy env;Lean4hol_env.quote_env env;
      quote_context g;quote_expr e;quote_expr e';quote_expr typ] in
    test "exact closed checked judgment" (hyp th=[] && frees(concl th)=[] && aconv(concl th)expected)
  let finish tag =
    test "core clauses unchanged" (Array.length rules=13);
    test "environment clauses unchanged" (List.length(CONJUNCTS l4_edef_RULES)=29);
    test "admission clauses unchanged" (List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES))=11);
    test "axioms unchanged" (axioms()=early_before_axioms);
    Printf.printf "\nEARLY_PASS %s %d\n%!" tag !count
end;;
