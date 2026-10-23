(* Separate opt-in checker; Hol_check and the default server dispatch are unchanged. *)
(* Preload these roots in distinct top-level phases: proofs in JRH mode,
   Hol_check in ordinary mode, and this adapter in JRH mode. *)
needs "hol/safety_admission.ml";;
needs "frontend/hol_check.ml";;
module Hol_safety_check = struct
  module Core = Lean4hol
  module Env = Lean4hol_env
  module Safety = Lean4hol_safety
  module Input = Hol_input
  module Transport = Hol_safety_input
  module Old = Hol_check
  type outcome = {code:int; message:string; line:int; checked:int;
    prefix:Safety.state option; forbidden:thm option}
  let safety = function Transport.Safe->Safety.Safe | Transport.Partial->Safety.Partial | Transport.Unsafe->Safety.Unsafe
  let hint = function Transport.No_hint->Safety.No_hint | Transport.Opaque_hint->Safety.Opaque_hint
    | Transport.Abbrev_hint->Safety.Abbrev_hint | Transport.Regular_hint n->Safety.Regular_hint n
  let operation = function Transport.Unsafe_single->Safety.Unsafe_single | Transport.Partial_single->Safety.Partial_single
    | Transport.Restricted_mutual->Safety.Restricted_mutual
  let entry kind (h:Input.constant) value =
    {Env.kind=kind;name=Old.name h.Input.name;params=List.map Old.name h.Input.params;
      typ=Old.expr h.Input.typ;value}
  let restricted (d:Transport.definition) =
    {Safety.safety=safety d.Transport.safety;entry=entry Env.Definition d.Transport.header (Some(Old.expr d.Transport.value));
      hint=hint d.Transport.hint;all=List.map Old.name d.Transport.all}
  let raw = function
    | Input.Inductive claims -> List.map Old.claim claims
    | Input.Quotient(h,k) ->
      let k=match k with Input.Qtype->Lean4hol_quotient_model.Qtype | Input.Qctor->Lean4hol_quotient_model.Qctor
        | Input.Qlift->Lean4hol_quotient_model.Qlift | Input.Qind->Lean4hol_quotient_model.Qind in
      [entry (Env.Quotient k) h None]
    | Input.Definition(h,v) | Input.Primitive_definition(h,v) | Input.Text_primitive_definition(h,v) ->
      [entry Env.Definition h (Some(Old.expr v))]
    | Input.Theorem(h,v) -> [entry Env.Theorem h (Some(Old.expr v))]
    | Input.Opaque(h,v) -> [entry Env.Opaque h (Some(Old.expr v))]
    | Input.Axiom h -> [entry Env.Axiom h None]
    | Input.Unsupported m -> raise(Old.Verdict(2,m))
  let safe_marks metadata entries = List.map(fun d->
    {Safety.safety=Safety.Safe;entry=d;hint=hint metadata.Transport.hint;all=List.map Old.name metadata.Transport.all})entries
  let get = function Ok v->v | Error e->raise(Old.Verdict(
    (match e.Core.kind with Core.Invalid_input->1 | _->2),e.Core.message))
  let safe_admit env input entries =
    match input with
    | Input.Inductive claims ->
      let ordinary=try Old.admit_generated env claims with
        Old.Verdict(2,message)->Error{Core.kind=Core.Unsupported;message} in
      (match ordinary with
       | Ok(next,_)->next,Safety.Exact
       | Error {Core.kind=(Core.Invalid_input|Core.Resource);_} as bad->ignore(get bad);assert false
       | Error _ ->
         let family=match Reducible_candidate.family env entries with
           | Error e->Error e
           | Ok b->match Env.admit_inductive_family env b with
             | Error e->Error e
             | Ok(next,_)->match Lean4hol_raw_ctor.certify env next entries b with
               | Error e->Error e
               | Ok h->
                 let args=[Env.quote_policy env;Env.quote_env env;Lean4hol_raw_ctor.entries entries;
                   Lean4hol_raw_ctor.entries b.Env.family_claims;Env.quote_env next] in
                 Ok(next,Safety.Generated(MP(SPECL args l4_raw_family_generated)h)) in
         match family with
         | Ok r->r
         | Error {Core.kind=(Core.Invalid_input|Core.Resource);_} as bad->get bad
         | Error _ ->
           let b=get(Reducible_candidate.indexed env entries) in
           let next,_=get(Env.admit_indexed_inductive env b) in
           let h=get(Lean4hol_raw_indexed.certify env next entries b) in
           let args=[Env.quote_policy env;Env.quote_env env;Lean4hol_raw_ctor.entries entries;
             Lean4hol_raw_ctor.entries b.Env.indexed_claims;Env.quote_env next] in
           next,Safety.Generated(MP(SPECL args l4_raw_indexed_generated)h))
    | _ ->
      let d=match entries with [d]->d | _->raise(Old.Verdict(3,"safe ordinary entry count")) in
      let next,_=get(match input with
        | Input.Quotient _ -> Env.admit_quotient env d
        | Input.Primitive_definition _ ->
          let c=get(Lean4hol_primitive.check_definition env d) in
          Env.admit_primitive env d (Lean4hol_primitive.definition_raw_theorem c)
        | Input.Text_primitive_definition _ ->
          let c=get(Lean4hol_text.check_definition env d) in
          Env.admit_text_primitive env d (Lean4hol_text.raw_theorem c)
        | _ -> Env.admit env d) in
      next,Safety.Exact
  let check_file path =
    Old.reset_syntax();
    let line=ref 0 and checked=ref 0 and prefix=ref None and forbidden=ref None in
    let finish code message={code;message=Printf.sprintf "line=%d checked=%d %s" !line !checked message;
      line= !line;checked= !checked;prefix= !prefix;forbidden= !forbidden} in
    try
      let rows=Transport.read_file path in
      let grants=List.filter_map(fun(_,d)->match d with
        | Transport.Safe_input(Input.Axiom h,_) -> Some{Env.axiom_name=Old.name h.Input.name;
            axiom_params=List.map Old.name h.Input.params;axiom_type=Old.expr h.Input.typ}
        | _->None)rows in
      let state=ref(get(Safety.start(get(Env.with_axioms grants)))) in
      prefix:=Some !state;
      let references mode marked=match get(Safety.check_references !state mode marked) with
        | Safety.Allowed _->()
        | Safety.Forbidden th->forbidden:=Some th;
          raise(Old.Verdict(1,"closed forbidden-reference certificate; accepted prefix retained")) in
      List.iter(fun(n,d)->
        line:=n;
        let next,count=match d with
        | Transport.Unsupported m->raise(Old.Verdict(2,m))
        | Transport.Restricted(op,ds)->
          let op=operation op and marked=List.map restricted ds in
          let mode=match op,marked with Safety.Partial_single,_->Safety.Safe
            | _,r::_->r.Safety.safety | _,[]->Safety.Safe in
          references mode marked;
          get(Safety.admit_restricted !state op marked),List.length ds
        | Transport.Safe_input(input,metadata)->
          let entries=raw input in
          let marked=safe_marks metadata entries in
          ignore(get(Safety.check_fresh !state marked));
          references Safety.Safe marked;
          let next,bridge=safe_admit(Safety.safe_environment !state)input entries in
          get(Safety.append_safe !state marked next bridge),1 in
        state:=next;prefix:=Some next;checked:= !checked+count)rows;
      ignore(get(Safety.authenticate !state (Safety.certificate !state)));
      finish 0 "accept: closed full marked-history and safe-projection certificates"
    with
    | Old.Verdict(code,m)->finish code m
    | Wire.Error e->line:=e.Wire.line;finish(Wire.error_exit_code e)e.Wire.message
    | Core.Stop e->finish(match e.Core.kind with Core.Invalid_input->1|_->2)e.Core.message
    | Stack_overflow->finish 2 "stack resource exhausted"
    | Out_of_memory->finish 2 "memory resource exhausted"
    | Sys_error m->finish 3 m
    | exn->finish 3 (Printexc.to_string exn)
end;;
