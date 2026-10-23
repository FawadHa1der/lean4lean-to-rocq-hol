(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Primitive.lean helpers at 8223d223ed98661882e95d9d6a7126df7097cd76.
   Capability certification only. No admission or native reduction hook. *)
needs "hol/reflection_contracts.ml";;
needs "hol/condition_validation.ml";;

let l4_reflection_type_checked_raw = prove
 (`!policy env rt. l4_reflection_type_contract (l4_checked policy env) rt ==>
    l4_reflection_type_contract (l4_edef env) rt`,
  MESON_TAC [l4_reflection_type_mono;l4_checked_typing]);;
let l4_reflection_ite_checked_raw = prove
 (`!policy env rt rd. l4_reflection_ite_contract (l4_checked policy env) rt rd ==>
    l4_reflection_ite_contract (l4_edef env) rt rd`,
  MESON_TAC [l4_reflection_ite_mono;l4_checked_typing]);;
let l4_reflection_dite_checked_raw = prove
 (`!policy env rt ry rn rd. l4_reflection_dite_contract (l4_checked policy env) rt ry rn rd ==>
    l4_reflection_dite_contract (l4_edef env) rt ry rn rd`,
  MESON_TAC [l4_reflection_dite_mono;l4_checked_typing]);;
let l4_reflected_nat_checked_raw = prove
 (`!policy env rt rd cp cb ch cd dt gt.
    l4_reflected_nat_contract (l4_checked policy env) rt rd cp cb ch cd dt gt ==>
    l4_reflected_nat_contract (l4_edef env) rt rd cp cb ch cd dt gt`,
  MESON_TAC [l4_reflected_nat_mono;l4_checked_typing]);;

module Lean4hol_reflection_syntax = struct
  open Lean4hol
  let calc = REWRITE_CONV (l4_reflection_contract_equations @
    l4_reflection_syntax_equations @ [l4_lift;ITLIST;REVERSE;APPEND])
    THENC NUM_REDUCE_CONV THENC REWRITE_CONV []
  let tag tm = let h,xs=strip_comb tm in fst(dest_const h),xs
  let bounded tm = let n=dest_numeral tm in
    if n </ num 0 || n >/ num max_int then
      stop Resource "quotation index exceeds host syntax range";
    int_of_string(string_of_num n)
  let rec name tm = match tag tm with
    | "L4Anonymous",[] -> Anonymous
    | "L4String",[n;cs] -> Str(name n,String.of_seq(List.to_seq
        (List.map (fun c -> Char.chr(bounded c)) (dest_list cs))))
    | "L4Numeric",[n;k] -> Num(name n,string_of_num(dest_numeral k))
    | _ -> stop Proof_failure "nonliteral quoted name"
  let rec level tm = match tag tm with
    | "L4Zero",[] -> Zero
    | "L4Succ",[u] -> Succ(level u)
    | "L4Max",[u;v] -> Max(level u,level v)
    | "L4IMax",[u;v] -> Imax(level u,level v)
    | "L4Param",[n] -> Param(name n)
    | _ -> stop Proof_failure "nonliteral quoted level"
  let rec expr tm = match tag tm with
    | "L4BVar",[i] -> Bvar(bounded i)
    | "L4Sort",[u] -> Sort(level u)
    | "L4Const",[n;us] -> Const(name n,List.map level (dest_list us))
    | "L4App",[f;a] -> App(expr f,expr a)
    | "L4Lam",[n;a;b] -> Lam(name n,expr a,expr b)
    | "L4Pi",[n;a;b] -> Pi(name n,expr a,expr b)
    | "L4Let",[n;a;v;b] -> Let(name n,expr a,expr v,expr b)
    | "L4NatLit",[n] -> Natlit(string_of_num(dest_numeral n))
    | "L4StrLit",[cs] ->
      let b=Buffer.create 32 in
      List.iter (fun tm -> let scalar=bounded tm in
        if not(Uchar.is_valid scalar) then stop Invalid_input "invalid quoted Unicode scalar";
        Buffer.add_utf_8_uchar b (Uchar.of_int scalar)) (dest_list cs);
      Strlit(Buffer.contents b)
    | "L4Proj",[n;i;e] -> Proj(name n,bounded i,expr e)
    | _ -> stop Unsupported "quotation decoder does not support this syntax"
  let decode tm = let e=expr tm in
    if not(aconv (quote_expr e) tm) then stop Proof_failure "quotation roundtrip mismatch";
    e
  let make tm =
    let h=calc tm in
    if hyp h<>[] || frees(concl h)<>[] then stop Proof_failure "open quotation theorem";
    decode(rhs(concl h)),h
  let template id args = fst(make(node id args))
  type reflection = {typ:expr;of_true:expr;of_false:expr;to_dec:expr}
  let reflection second =
    let b=if second then `T` else `F` in
    {typ=template "l4_reflection_type" [b];
     of_true=template "l4_reflection_true" [b];
     of_false=template "l4_reflection_false" [b];
     to_dec=template "l4_reflection_dec" [b]}
  type nat_condition = {prop:expr;as_bool:expr;proof:expr;dec:expr;reflect:reflection}
  let nat_condition second =
    let b=if second then `T` else `F` in
    {prop=template "l4_condition_nat_prop" [b];
     as_bool=template "l4_condition_nat_bool" [b];
     proof=template "l4_condition_nat_proof" [b];
     dec=template "l4_condition_nat_dec" [b];reflect=reflection second}
  let bool_condition () = template "l4_condition_bool_prop" [],
    template "l4_condition_bool_dec" []
end;;

module Lean4hol_reflection : sig
  type certificate
  val theorem : certificate -> thm
  val raw_theorem : certificate -> thm
  val check_type : ?fuel:int -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.reflection -> (certificate,Lean4hol.error) result
  val check_ite : ?fuel:int -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.reflection -> (certificate,Lean4hol.error) result
  val check_nat_dite : ?fuel:int -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.reflection -> (certificate,Lean4hol.error) result
  val check_ite_using : ?fuel:int -> thm list -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.reflection -> (certificate,Lean4hol.error) result
  val check_nat_dite_using : ?fuel:int -> thm list -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.reflection -> (certificate,Lean4hol.error) result
  val check_nat_condition : ?fuel:int -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.nat_condition -> (certificate,Lean4hol.error) result
  val check_nat_condition_using : ?fuel:int -> thm list -> Lean4hol_env.environment ->
    Lean4hol_reflection_syntax.nat_condition -> dec_type:Lean4hol.expr ->
    gadget_type:Lean4hol.expr -> (certificate,Lean4hol.error) result
end = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Syn=Lean4hol_reflection_syntax
  type certificate = {checked:thm;raw:thm}
  let theorem c=c.checked
  let raw_theorem c=c.raw
  let get = function Ok x -> x | Error e -> raise(Stop e)
  let guard tm h =
    if hyp h<>[] || frees(concl h)<>[] || not(aconv tm (concl h)) then
      stop Proof_failure "reflection certificate source/policy/conclusion mismatch";
    h
  let certify ?(proofs=[]) fuel st env id bridge args =
    let j=node "l4_checked" [Env.quote_policy env;Env.quote_env env] in
    let target=node id (j::args) in
    let trace label f =
      let verbose=try Sys.getenv "HOL_HELPER_TRACE"="1" with Not_found -> false in
      let start=Sys.time() in
      if verbose then Printf.printf "HELPER_START %s %s\n%!" id label;
      let x=f() in
      if verbose then Printf.printf "HELPER_END %s %s %.6f\n%!" id label (Sys.time()-.start);
      x in
    let expansion=trace "expansion" (fun () ->
      let jvar=genvar(type_of j) in
      INST [j,jvar] (Syn.calc(node id (jvar::args)))) in
    let obligations=conjuncts(rhs(concl expansion)) in
    (* Proof objects are reusable only as closed proofs of one exact requested
       judgment, including its environment, policy, context, type and source. *)
    List.iter (fun h ->
      tick st;
      if hyp h<>[] || frees(concl h)<>[] || not(List.exists (fun tm ->
        tick st; aconv tm (concl h)) obligations) then
        stop Proof_failure "supplied reflection proof is not a closed exact obligation") proofs;
    let index=ref 0 in
    let prove_obligation tm =
      tick st;
      match List.find_opt (fun h -> tick st; aconv tm (concl h)) proofs with
      | Some h -> guard tm h
      | None ->
      let head,xs=strip_comb tm in
      match fst(dest_const head),xs with
      | "l4_checked",[policy;entries;g;e;e';a] when
          aconv policy (Env.quote_policy env) && aconv entries (Env.quote_env env) &&
          aconv g (quote_context []) ->
        let e=Syn.decode e and e'=Syn.decode e' and a=Syn.decode a in
        incr index;
        let h=trace ("obligation-"^string_of_int !index) (fun () ->
          if e=e' then get(Env.check ~fuel env [] e a)
          else get(Env.convert ~fuel env [] e e' a)) in
        guard tm h
      | _ -> stop Proof_failure "unexpected reflection obligation" in
    let hs=List.map prove_obligation obligations in
    let checked=guard target (EQ_MP(SYM expansion)(end_itlist CONJ hs)) in
    let raw_target=node id (node "l4_edef" [Env.quote_env env]::args) in
    {checked;raw=guard raw_target (MATCH_MP bridge checked)}
  let check_type ?(fuel=100000) env r =
    run fuel [] [r.Syn.typ] (fun st ->
      certify fuel st env "l4_reflection_type_contract" l4_reflection_type_checked_raw
        [quote_expr r.Syn.typ])
  let check_ite_using ?(fuel=100000) proofs env r =
    run fuel [] [r.Syn.typ;r.Syn.to_dec] (fun st ->
      certify ~proofs fuel st env "l4_reflection_ite_contract" l4_reflection_ite_checked_raw
        [quote_expr r.Syn.typ;quote_expr r.Syn.to_dec])
  let check_ite ?fuel env r = check_ite_using ?fuel [] env r
  let check_nat_dite_using ?(fuel=100000) proofs env r =
    run fuel [] [r.Syn.typ;r.Syn.of_true;r.Syn.of_false;r.Syn.to_dec] (fun st ->
      certify ~proofs fuel st env "l4_reflection_dite_contract" l4_reflection_dite_checked_raw
        [quote_expr r.Syn.typ;quote_expr r.Syn.of_true;quote_expr r.Syn.of_false;quote_expr r.Syn.to_dec])
  let check_nat_dite ?fuel env r = check_nat_dite_using ?fuel [] env r
  (* Candidate types are not trusted: they occur in the complete checked
     obligations, and every supplied proof passes the same exact guard. *)
  let check_nat_condition_using ?(fuel=100000) proofs env c ~dec_type ~gadget_type =
    let r=c.Syn.reflect in
    run fuel [] [r.Syn.typ;r.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;c.Syn.proof;c.Syn.dec;
      dec_type;gadget_type] (fun st ->
      certify ~proofs fuel st env "l4_reflected_nat_contract" l4_reflected_nat_checked_raw
        (List.map quote_expr [r.Syn.typ;r.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;c.Syn.proof;
          c.Syn.dec;dec_type;gadget_type]))
  let check_nat_condition ?(fuel=100000) env c =
    let r=c.Syn.reflect in
    run fuel [] [r.Syn.typ;r.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;c.Syn.proof;c.Syn.dec] (fun st ->
      let args=List.map quote_expr [r.Syn.typ;r.Syn.to_dec;c.Syn.prop;c.Syn.as_bool;c.Syn.proof] in
      let gadget=Syn.template "l4_reflected_nat_gadget" args in
      let dt,_=get(Env.infer ~fuel env [] c.Syn.dec) in
      ignore(get(check_type ~fuel env r));
      let gt,_=get(Env.infer ~fuel env [] gadget) in
      certify fuel st env "l4_reflected_nat_contract" l4_reflected_nat_checked_raw
        (args@[quote_expr c.Syn.dec;quote_expr dt;quote_expr gt]))
end;;
