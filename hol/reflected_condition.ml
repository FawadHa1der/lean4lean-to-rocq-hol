(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Condition.check dispatch and construction helpers, Primitive.lean:122-177
   at 8223d223ed98661882e95d9d6a7126df7097cd76.
   Branch bodies passed to apply_dite are already under their proof binder,
   exactly as in the upstream raw-Expr interface. *)
needs "hol/reflection_validation.ml";;

let l4_condition_apps = new_definition
 `l4_condition_apps f xs = ITLIST (\a g. L4App g a) (REVERSE xs) f`;;
let l4_condition_apply_ite = new_definition
 `l4_condition_apply_ite cp cd a args t e = l4_condition_apps (l4_r_run l4_r_ite)
   [a;l4_condition_apps cp args;l4_condition_apps cd args;t;e]`;;
let l4_condition_apply_dite = new_definition
 `l4_condition_apply_dite cp cd args t e = l4_condition_apps (l4_r_run l4_r_dite)
   [l4_r_run l4_r_nat;l4_condition_apps cp args;l4_condition_apps cd args;
    L4Lam L4Anonymous (l4_condition_apps cp args) t;
    L4Lam L4Anonymous (L4App (l4_r_run l4_r_not) (l4_condition_apps cp args)) e]`;;
let l4_condition_apply_decide = new_definition
 `l4_condition_apply_decide cp cd args = l4_condition_apply_ite cp cd
    (l4_r_run l4_r_bool) args (l4_r_run l4_r_true) (l4_r_run l4_r_false)`;;
let l4_bool_condition_base_contract = new_definition
 `l4_bool_condition_base_contract J cp cd dt <=>
    J ([]:l4_expr list) (cd:l4_expr) cd dt /\ J [] cp cp l4_condition_prop_type`;;
let l4_bool_condition_base_checked_raw = prove
 (`!policy env cp cd dt.
   l4_bool_condition_base_contract (l4_checked policy env) cp cd dt ==>
   l4_bool_condition_base_contract (l4_edef env) cp cd dt`,
  REWRITE_TAC [l4_bool_condition_base_contract] THEN MESON_TAC [l4_checked_typing]);;

let l4_bool_condition_ite_implies_base = prove
 (`!J cp cd dt. l4_bool_condition_ite_contract J cp cd dt ==>
    l4_bool_condition_base_contract J cp cd dt`,
  REWRITE_TAC [l4_bool_condition_ite_contract;l4_bool_condition_base_contract] THEN MESON_TAC []);;

module Lean4hol_reflected_condition : sig
  type condition = Boolean of Lean4hol.expr * Lean4hol.expr
    | Reflected_nat of Lean4hol_reflection_syntax.nat_condition
  type certificate
  val theorems : certificate -> thm list
  val raw_theorems : certificate -> thm list
  val check : ?fuel:int -> ?ite:bool -> ?dite:bool -> Lean4hol_env.environment ->
    condition -> (certificate,Lean4hol.error) result
  val check_prepared : ?fuel:int -> ?ite:bool -> ?dite:bool ->
    ?ite_proof:thm -> ?dite_proof:thm -> Lean4hol_env.environment ->
    condition -> thm -> (certificate,Lean4hol.error) result
end = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Ref=Lean4hol_reflection
  module Syn=Lean4hol_reflection_syntax
  type condition = Boolean of expr * expr | Reflected_nat of Syn.nat_condition
  type certificate = (thm * thm) list
  let theorems c=List.map fst c
  let raw_theorems c=List.map snd c
  let get = function Ok x -> x | Error e -> raise(Stop e)
  let guard tm h =
    if hyp h<>[] || frees(concl h)<>[] || not(aconv tm (concl h)) then
      stop Proof_failure "condition source/policy mismatch";h
  let check ?(fuel=100000) ?(ite=false) ?(dite=false) env condition =
    let inputs=match condition with Boolean(p,d) -> [p;d]
      | Reflected_nat c -> [c.Syn.prop;c.Syn.dec;c.Syn.as_bool;c.Syn.proof;
          c.Syn.reflect.Syn.typ;c.Syn.reflect.Syn.to_dec] in
    run fuel [] inputs (fun _ ->
      match condition with
      | Boolean(p,d) when ite ->
        let c=get(Lean4hol_condition.check_bool_ite ~fuel env p d) in
        let _,_,dt=Lean4hol_condition.bool_ite_inputs c in
        let args=List.map quote_expr [p;d;dt] in
        let checked=Lean4hol_condition.bool_ite_theorem c in
        let raw=Lean4hol_condition.bool_ite_raw_theorem c in
        let base judgment h=guard (node "l4_bool_condition_base_contract" (judgment::args))
          (MATCH_MP l4_bool_condition_ite_implies_base h) in
        let base_checked=base (node "l4_checked" [Env.quote_policy env;Env.quote_env env]) checked in
        let base_raw=base (node "l4_edef" [Env.quote_env env]) raw in
        if dite then stop Unsupported "Condition.bool dependent ite is unsupported upstream";
        [base_checked,base_raw;checked,raw]
      | Boolean(p,d) ->
        let dt,hd=get(Env.infer ~fuel env [] d) in
        let pty=Pi(Anonymous,Const(Str(Anonymous,"Bool"),[]),Sort Zero) in
        let hp=get(Env.check ~fuel env [] p pty) in
        let j=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
        let args=List.map quote_expr [p;d;dt] in
        let target=node "l4_bool_condition_base_contract" (j::args) in
        let jvar=genvar(type_of j) in
        let expansion=INST [j,jvar] ((REWRITE_CONV [l4_bool_condition_base_contract;l4_condition_prop_type;
          l4_prim_bool;l4_bool_name]) (node "l4_bool_condition_base_contract" (jvar::args))) in
        let checked=guard target (EQ_MP(SYM expansion)(CONJ hd hp)) in
        let raw_target=node "l4_bool_condition_base_contract"
          (node "l4_edef" [Env.quote_env env]::args) in
        let raw=guard raw_target (MATCH_MP l4_bool_condition_base_checked_raw checked) in
        if dite then stop Unsupported "Condition.bool dependent ite is unsupported upstream";
        [checked,raw]
      | Reflected_nat c ->
        let pair c=Ref.theorem c,Ref.raw_theorem c in
        let base=pair(get(Ref.check_nat_condition ~fuel env c)) in
        let is=if ite then [pair(get(Ref.check_ite ~fuel env c.Syn.reflect))] else [] in
        let ds=if dite then [pair(get(Ref.check_nat_dite ~fuel env c.Syn.reflect))] else [] in
        base::is@ds)
  (* Whole prepared contracts are an explicit alternative to search. Their
     type witnesses come from closed kernel theorems, not trusted annotations.
     Supplied proofs for supported capabilities are checked even when their
     flags are false. Boolean DITE is always Unsupported, also with a proof. *)
  let check_prepared ?(fuel=100000) ?(ite=false) ?(dite=false)
      ?ite_proof ?dite_proof env condition base =
    let inputs=match condition with Boolean(p,d) -> [p;d]
      | Reflected_nat c -> [c.Syn.prop;c.Syn.dec;c.Syn.as_bool;c.Syn.proof;
          c.Syn.reflect.Syn.typ;c.Syn.reflect.Syn.to_dec;
          c.Syn.reflect.Syn.of_true;c.Syn.reflect.Syn.of_false] in
    run fuel [] inputs (fun st ->
      let j=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
      let raw=node "l4_edef" [Env.quote_env env] in
      let pair id args bridge h =
        tick st;
        let h=guard (node id (j::args)) h in
        h,guard (node id (raw::args)) (MATCH_MP bridge h) in
      let witnesses id prefix count =
        tick st;
        let head,args=strip_comb(concl base) in
        if not(is_const head) || fst(dest_const head)<>id ||
           List.length args<>1+List.length prefix+count then
          stop Proof_failure "prepared condition base has wrong contract shape";
        let rec drop n xs=if n=0 then xs else drop (n-1) (List.tl xs) in
        prefix @ drop (1+List.length prefix) args in
      let optional flag id args bridge proof =
        match proof with
        | Some h -> let p=pair id args bridge h in if flag then [p] else []
        | None when flag -> stop Proof_failure "missing prepared condition capability"
        | None -> [] in
      match condition with
      | Boolean(p,d) ->
        let args=witnesses "l4_bool_condition_base_contract"
          (List.map quote_expr [p;d]) 1 in
        let b=pair "l4_bool_condition_base_contract" args
          l4_bool_condition_base_checked_raw base in
        let is=optional ite "l4_bool_condition_ite_contract" args
          l4_bool_condition_ite_checked_raw ite_proof in
        if dite || dite_proof<>None then
          stop Unsupported "Condition.bool dependent ite is unsupported upstream";
        b::is
      | Reflected_nat c ->
        let r=c.Syn.reflect in
        let args=witnesses "l4_reflected_nat_contract"
          (List.map quote_expr [r.Syn.typ;r.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;
            c.Syn.proof;c.Syn.dec]) 2 in
        let b=pair "l4_reflected_nat_contract" args l4_reflected_nat_checked_raw base in
        let is=optional ite "l4_reflection_ite_contract"
          (List.map quote_expr [r.Syn.typ;r.Syn.to_dec])
          l4_reflection_ite_checked_raw ite_proof in
        let ds=optional dite "l4_reflection_dite_contract"
          (List.map quote_expr [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec])
          l4_reflection_dite_checked_raw dite_proof in
        b::is@ds)
end;;
