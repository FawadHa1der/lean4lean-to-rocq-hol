(* Private syntax-only DAG numbering. IDs convey sharing, never a judgment.
   Gallina independently rejects duplicate/missing/forward/cyclic references. *)
module C = Lean_arena
module A = Rocq_adapter

module Seen = Hashtbl.Make(struct
  type t = Wire.expr
  let equal a b = a == b
  let hash = Hashtbl.hash
end)

type encoded = {
  rows : (C.positive,C.dag_node) C.prod C.list;
  type_root : C.positive;
  body_root : C.positive;
  count : int;
}

let positive i = match A.binary (Z.of_int i) with
  | C.Npos p -> p | C.N0 -> invalid_arg "positive syntax identifier"

let encode_pair st typ body =
  let seen = Seen.create 1024 and rows = ref [] and next = ref 0 in
  let rec visit e = match Seen.find_opt seen e with
    | Some id -> id
    | None ->
      let node = match e with
        | Wire.BVar i -> C.DBVar (A.index i)
        | Wire.Sort u -> C.DSort (A.level st u)
        | Wire.Const (n,us) -> C.DConst (A.name st n,A.list (A.level st) us)
        | Wire.App (f,a) -> C.DApp (visit f,visit a)
        | Wire.Lam (n,a,b,bi) -> C.DLam (A.name st n,A.binder bi,visit a,visit b)
        | Wire.Pi (n,a,b,bi) -> C.DPi (A.name st n,A.binder bi,visit a,visit b)
        | Wire.Let (n,a,v,b,nd) -> C.DLet (A.name st n,visit a,visit v,visit b,A.bool nd)
        | Wire.Proj (n,i,a) -> C.DProj (A.name st n,A.index i,visit a)
        | Wire.NatLit n -> C.DLit (C.LitNat (A.binary n))
        | Wire.StringLit s -> C.DLit (C.LitString (A.string s))
        | Wire.MData a -> C.DMData (visit a) in
      if !next = max_int then raise (A.Resource "syntax table address range");
      incr next;
      let id = positive !next in
      Seen.add seen e id;
      rows := C.Pair (id,node) :: !rows;
      id in
  let type_root = visit typ in
  let body_root = visit body in
  let rows = List.fold_left (fun tail row -> C.Cons (row,tail)) C.Nil !rows in
  {rows;type_root;body_root;count= !next}

let budget encoded = A.nat (min 1_000_000 encoded.count)

(* Test-only structural comparison with pair memoization. Every constructor and
   payload is compared; pointer pairs merely prevent revisiting shared children.
   This is never called to produce a logical admission result. *)
module ExprPairs = Hashtbl.Make(struct
  type t = C.expr * C.expr
  let equal (a,b) (c,d) = a == c && b == d
  let hash = Hashtbl.hash
end)

let exact_expr a b =
  let seen = ExprPairs.create 1024 and pending = ref [a,b] and ok = ref true in
  let push a b = pending := (a,b) :: !pending in
  while !ok && !pending <> [] do
    let a,b = List.hd !pending in
    pending := List.tl !pending;
    if not (ExprPairs.mem seen (a,b)) then begin
      ExprPairs.add seen (a,b) ();
      match a,b with
      | C.EBVar i,C.EBVar j -> ok := i = j
      | C.EFVar n,C.EFVar m | C.EMVar n,C.EMVar m -> ok := n = m
      | C.ESort u,C.ESort v -> ok := u = v
      | C.EConst (n,us),C.EConst (m,vs) -> ok := n = m && us = vs
      | C.EApp (f,a),C.EApp (g,b) -> push f g; push a b
      | C.ELam (n,bi,a,b),C.ELam (m,bj,c,d)
      | C.EPi (n,bi,a,b),C.EPi (m,bj,c,d) ->
        ok := n = m && bi = bj; push a c; push b d
      | C.ELet (n,a,v,b,nd),C.ELet (m,c,w,d,md) ->
        ok := n = m && nd = md; push a c; push v w; push b d
      | C.ELit l,C.ELit k -> ok := l = k
      | C.EProj (n,i,a),C.EProj (m,j,b) -> ok := n = m && i = j; push a b
      | C.EMData a,C.EMData b -> push a b
      | _ -> ok := false
    end
  done;
  !ok

let decoded encoded =
  let get = function C.Accept x -> x | _ -> failwith "syntax-only DAG encoding rejected" in
  let arena = get (C.arena_build C.empty_arena encoded.rows) in
  let typ = get (C.scope_ref arena.C.arena_scope encoded.type_root) in
  let body = get (C.scope_ref arena.C.arena_scope encoded.body_root) in
  typ.C.scope_expr,body.C.scope_expr

let verify_decode st typ body encoded =
  let actual_type,actual_body = decoded encoded in
  if not (exact_expr actual_type (A.expr st typ) && exact_expr actual_body (A.expr st body))
  then failwith "new DAG decoder differs from original expression adapter"

let admit fuel env st = function
  | Wire.Definition d when d.Wire.safety = Wire.Safe ->
    let encoded = encode_pair st d.header.typ d.value in
    C.indexed_admit_dag_definition (A.hints d.hints) (budget encoded) fuel env (A.name st d.header.name)
      (A.list (A.name st) d.header.params) encoded.rows encoded.type_root encoded.body_root
  | Wire.Theorem (h,value,_) ->
    let encoded = encode_pair st h.typ value in
    C.indexed_admit_dag_theorem (budget encoded) fuel env (A.name st h.name)
      (A.list (A.name st) h.params) encoded.rows encoded.type_root encoded.body_root
  | Wire.Opaque (h,value,false,_) ->
    let encoded = encode_pair st h.typ value in
    C.indexed_admit_dag_opaque (budget encoded) fuel env (A.name st h.name)
      (A.list (A.name st) h.params) encoded.rows encoded.type_root encoded.body_root
  | other -> A.admit fuel env st other
