(* Same policy controls; HOL invariant application is defined before lexer reset. *)
let compose_policy_axioms=axioms();;
let () =
  let open Lean4hol in
  let module A=Lean4hol_env in
  let module C=Lean4hol_input_certificate in
  let get=function Ok x->x|Error e->failwith e.message in
  let n s=Str(Anonymous,s) in
  let prop={A.kind=A.Axiom;name=n "ComposePolicyP";params=[];typ=Sort Zero;value=None} in
  let witness={prop with A.name=n "ComposePolicyWitness";typ=Const(prop.A.name,[])} in
  let permission d={A.axiom_name=d.A.name;axiom_params=d.A.params;axiom_type=d.A.typ} in
  let grants=List.map permission [prop;witness] in
  let prior=get(A.with_axioms grants) in
  let first,_=get(A.admit prior prop) in
  let hfirst=get(C.append_exact prior first [] [prop] (C.start prior)) in
  let next,_=get(A.admit first witness) in
  let hnext=get(C.append_exact first next [[prop]] [witness] hfirst) in
  let blocks=[[witness];[prop]] in
  let final=get(C.finish next blocks hnext) in
  ignore(Lean4hol_raw_ctor.exact(C.expected next blocks)final);
  if frees(concl final)<>[] || A.permissions next<>grants then failwith "policy was not retained";
  compose_policy_invariants [A.quote_policy next;A.quote_env next;C.history blocks] final;
  let declines=ref 0 in
  let decline label=function
    | Error {kind=(Unsupported|Proof_failure);_}->
      incr declines;print_endline("POLICY_DECLINE "^label)
    | Error e->failwith(label^": unexpected error: "^e.message)
    | Ok _->failwith("policy control accepted: "^label) in
  decline "trace_replayed_under_different_policy"
    (C.append_exact prior first [] [prop] (C.start A.empty));
  decline "raw_axiom_signature_tamper"
    (C.finish next [[{witness with A.typ=Sort Zero}];[prop]] hnext);
  decline "raw_axiom_relabelled_definition"
    (C.append_exact first next [[prop]] [{witness with A.kind=A.Definition;value=Some(Sort Zero)}] hfirst);
  decline "ungranted_object_axiom" (A.admit A.empty prop);
  let wrong=get(A.with_axioms [{(permission prop) with A.axiom_type=Sort(Succ Zero)}]) in
  decline "permission_signature_mismatch" (A.admit wrong prop);
  if axioms()<>compose_policy_axioms then failwith "axiom change";
  Printf.printf "PRIVATE_COMPOSE_POLICY_DONE nonempty_exact_policy closed_history three_invariants %d_declines unchanged_axioms\n%!" !declines;;
