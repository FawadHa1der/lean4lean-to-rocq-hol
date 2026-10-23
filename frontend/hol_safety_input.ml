(* Opt-in syntax transport only. No type checking or verdict oracle. *)
type safety = Safe | Partial | Unsafe
type hint = No_hint | Opaque_hint | Abbrev_hint | Regular_hint of string
type operation = Unsafe_single | Partial_single | Restricted_mutual
type definition = {header:Hol_input.constant; value:Hol_input.expr;
  safety:safety; hint:hint; all:Hol_input.name list}
type metadata = {hint:hint; all:Hol_input.name list}
type declaration = Safe_input of Hol_input.declaration * metadata
                 | Restricted of operation * definition list
                 | Unsupported of string
let safety = function Wire.Safe->Safe | Wire.Partial->Partial | Wire.Unsafe->Unsafe
let hint = function Wire.OpaqueHint->Opaque_hint | Wire.Abbrev->Abbrev_hint
  | Wire.Regular n->Regular_hint(Z.to_string n)
let definition memo (d:Wire.definition) =
  {header=Hol_input.constant memo d.Wire.header;value=Hol_input.expr memo d.Wire.value;
   safety=safety d.Wire.safety;hint=hint d.Wire.hints;all=List.map Hol_input.name d.Wire.all}
let translate_batch memo = function
  | Replay.Mutual(line,ds) -> line,Restricted(Restricted_mutual,List.map(definition memo)ds)
  | Replay.Single(line,Wire.Definition d) when d.Wire.safety<>Wire.Safe ->
    line,Restricted((if d.Wire.safety=Wire.Unsafe then Unsafe_single else Partial_single),
      [definition memo d])
  | Replay.Single(line,(Wire.Axiom(_,true) | Wire.Opaque(_,_,true,_))) ->
    line,Unsupported "unsafe axiom/opaque admission remains outside restricted-definition slice"
  | Replay.Single(line,Wire.Inductive(ts,cs,rs)) when
      List.exists(fun (t:Wire.inductive)->t.Wire.ind_unsafe)ts ||
      List.exists(fun (c:Wire.constructor)->c.Wire.ctor_unsafe)cs ||
      List.exists(fun (r:Wire.recursor)->r.Wire.rec_unsafe)rs ->
    line,Unsupported "unsafe inductive admission remains outside restricted-definition slice"
  | Replay.Single(line,d) ->
    let metadata=match d with
      | Wire.Definition d -> {hint=hint d.Wire.hints;all=List.map Hol_input.name d.Wire.all}
      | Wire.Theorem(_,_,ns) | Wire.Opaque(_,_,_,ns) ->
        {hint=No_hint;all=List.map Hol_input.name ns}
      | _ -> {hint=No_hint;all=[]} in
    line,Safe_input(Hol_input.declaration memo d,metadata)
let translate_export export =
  let memo=Hol_input.Exprs.create export.Wire.expr_count in
  List.map(translate_batch memo)(Replay.schedule export.Wire.declarations)
let read_file path = translate_export(Wire.read_file path)
