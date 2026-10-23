(* Proof-bearing conditional capability checks; no admission hook. *)
needs "hol/condition_contracts.ml";;
needs "hol/environment.ml";;

let l4_bool_condition_ite_checked_raw = prove
 (`!policy env p d dt.
    l4_bool_condition_ite_contract (l4_checked policy env) p d dt ==>
    l4_bool_condition_ite_contract (l4_edef env) p d dt`,
  MESON_TAC [l4_bool_condition_ite_mono;l4_checked_typing]);;

module Lean4hol_condition : sig
  type bool_ite_certificate
  val check_bool_ite : ?fuel:int -> Lean4hol_env.environment ->
    Lean4hol.expr -> Lean4hol.expr ->
    (bool_ite_certificate,Lean4hol.error) result
  val bool_ite_inputs : bool_ite_certificate ->
    Lean4hol.expr * Lean4hol.expr * Lean4hol.expr
  val bool_ite_theorem : bool_ite_certificate -> thm
  val bool_ite_raw_theorem : bool_ite_certificate -> thm
end = struct
  open Lean4hol
  module Env = Lean4hol_env
  type bool_ite_certificate = {
    prop:expr; dec:expr; dec_type:expr; checked:thm; raw:thm
  }
  let bool_ite_inputs c = c.prop,c.dec,c.dec_type
  let bool_ite_theorem c = c.checked
  let bool_ite_raw_theorem c = c.raw
  let guard target h =
    if hyp h<>[] || frees(concl h)<>[] || not(aconv target (concl h)) then
      stop Proof_failure "condition certificate conclusion or hypotheses mismatch";
    h
  let get = function Ok x -> x | Error e -> raise(Stop e)
  let equations = [l4_bool_condition_ite_contract;l4_condition_prop_type;
    l4_condition_nat_selector;l4_condition_nat_ite;l4_condition_select_true;
    l4_condition_select_false;l4_prim_binary;l4_prim_unary;l4_prim_nat;
    l4_prim_bool;l4_prim_true;l4_prim_false;l4_nat_name;l4_bool_name;l4_lift]
  let calc = REWRITE_CONV equations THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let check_bool_ite ?(fuel=100000) env prop dec = run fuel [] [prop;dec] (fun st ->
    let name s=Str(Anonymous,s) in
    let nt=Const(name "Nat",[]) and bt=Const(name "Bool",[]) in
    let tru=Const(Str(name "Bool","true"),[]) in
    let fal=Const(Str(name "Bool","false"),[]) in
    let binary=Pi(Anonymous,nt,Pi(Anonymous,nt,nt)) in
    let prop_type=Pi(Anonymous,bt,Sort Zero) in
    let selector_type=Pi(Anonymous,bt,binary) in
    (* prop and dec must be closed. Quoted HOL syntax independently checks
       lifting; the host term cannot choose a different certificate target. *)
    let it=Lam(Anonymous,bt,Env.apps (Const(name "ite",[Succ Zero]))
      [nt;App(prop,Bvar 0);App(dec,Bvar 0)]) in
    let yes=Lam(Anonymous,nt,Lam(Anonymous,nt,Bvar 1)) in
    let no=Lam(Anonymous,nt,Lam(Anonymous,nt,Bvar 0)) in
    let j=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
    let typed a b ty h=guard (list_mk_comb(j,
      [quote_context [];quote_expr a;quote_expr b;quote_expr ty])) h in
    let dt,hd=get(Env.infer ~fuel env [] dec) in
    let hd=typed dec dec dt hd in
    let hp=typed prop prop prop_type (get(Env.check ~fuel env [] prop prop_type)) in
    let hi=typed it it selector_type (get(Env.check ~fuel env [] it selector_type)) in
    let ht=typed (App(it,tru)) yes binary (get(Env.convert ~fuel env [] (App(it,tru)) yes binary)) in
    let hf=typed (App(it,fal)) no binary (get(Env.convert ~fuel env [] (App(it,fal)) no binary)) in
    let args=[quote_expr prop;quote_expr dec;quote_expr dt] in
    let target=node "l4_bool_condition_ite_contract" (j::args) in
    tick st;
    (* The environment is opaque to every rewrite here. Instantiate the
       kernel-proved schematic expansion instead of traversing its syntax. *)
    let jvar=genvar(type_of j) in
    let expansion=INST [j,jvar] (calc(node "l4_bool_condition_ite_contract" (jvar::args))) in
    let checked=guard target (EQ_MP(SYM expansion)(end_itlist CONJ[hd;hp;hi;ht;hf])) in
    let raw_target=node "l4_bool_condition_ite_contract"
      (node "l4_edef" [Env.quote_env env]::args) in
    let raw=guard raw_target (MATCH_MP l4_bool_condition_ite_checked_raw checked) in
    {prop;dec;dec_type=dt;checked;raw})
end;;
