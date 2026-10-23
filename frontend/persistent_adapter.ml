(* Only syntactic batch translation. The abstract state can only come from
   extracted initialization or a successful extracted admission. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter

let request st = function
  | Wire.Definition d when d.Wire.safety = Wire.Safe ->
    let encoded = D.encode_pair st d.header.typ d.value in
    C.BatchDag (C.DagDefinition (A.hints d.hints),D.budget encoded,A.name st d.header.name,
      A.list (A.name st) d.header.params,encoded.rows,encoded.type_root,encoded.body_root)
  | Wire.Theorem (h,value,_) ->
    let encoded = D.encode_pair st h.typ value in
    C.BatchDag (C.DagTheorem,D.budget encoded,A.name st h.name,
      A.list (A.name st) h.params,encoded.rows,encoded.type_root,encoded.body_root)
  | Wire.Opaque (h,value,false,_) ->
    let encoded = D.encode_pair st h.typ value in
    C.BatchDag (C.DagOpaque,D.budget encoded,A.name st h.name,
      A.list (A.name st) h.params,encoded.rows,encoded.type_root,encoded.body_root)
  | Wire.Inductive (types,ctors,recs) -> C.BatchInductive
      (A.list (A.inductive st) types,A.list (A.constructor st) ctors,A.list (A.recursor st) recs)
  | Wire.Quotient (h,k) ->
    let kind = match k with Wire.QuotType -> C.QType | Wire.QuotCtor -> C.QCtor
      | Wire.QuotLift -> C.QLift | Wire.QuotInd -> C.QInd in
    C.BatchQuotient (A.name st h.name,A.list (A.name st) h.params,A.expr st h.typ,kind)
  | other -> C.BatchOrdinary (A.declaration st other)

module State : sig
  type t
  val initial : t
  val environment : t -> C.environment
  val admit : C.nat -> t -> A.state -> Wire.declaration -> t C.result
  val mutual : C.nat -> t -> A.state -> Wire.definition list -> t C.result
end = struct
  type t = C.runtime_state
  let initial = C.initial_state
  let environment = C.state_environment C.suffix_bitfold8
  let admit fuel state syntax input = C.admit_batch fuel state (request syntax input)
  let mutual fuel state syntax inputs =
    C.admit_batch fuel state (C.BatchMutual (A.list (A.definition syntax) inputs))
end
