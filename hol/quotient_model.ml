(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Candidate syntax only. Admission must prove agreement with quotient_syntax. *)
needs "hol/core.ml";;
needs "hol/quotient_syntax.ml";;

module Lean4hol_quotient_model = struct
  open Lean4hol
  type quotient_kind = Qtype | Qctor | Qlift | Qind
  let quote_kind = function
    | Qtype -> `L4QuotType` | Qctor -> `L4QuotCtor`
    | Qlift -> `L4QuotLift` | Qind -> `L4QuotInd`
  let base = Str(Anonymous,"Quot")
  let eq = Str(Anonymous,"Eq")
  let name = function
    | Qtype -> base | Qctor -> Str(base,"mk")
    | Qlift -> Str(base,"lift") | Qind -> Str(base,"ind")
  let arity = function Qlift -> 2 | _ -> 1
  let pi a b = Pi(Anonymous,a,b)
  let app f xs = List.fold_left (fun f a -> App(f,a)) f xs
  let arrow st a b = pi a (lift st 1 0 b)
  let relation st a = arrow st a (arrow st a (Sort Zero))
  let qapp kind u args = app (Const(name kind,[u])) args
  let equality_type st u = pi (Sort u) (relation st (Bvar 0))
  let reflexivity_type st u =
    tick st;
    pi (Sort u) (pi (Bvar 0) (app (Const(eq,[u])) [Bvar 1;Bvar 0;Bvar 0]))
  let signature st kind u v =
    tick st;
    let rel=relation st (Bvar 0) in
    let body=match kind with
      | Qtype -> Sort u
      | Qctor -> pi (Bvar 1) (qapp Qtype u [Bvar 2;Bvar 1])
      | Qlift ->
        let sanity=pi (Bvar 3) (pi (Bvar 4)
          (arrow st (app (Bvar 4) [Bvar 1;Bvar 0])
            (app (Const(eq,[v])) [Bvar 3;App(Bvar 2,Bvar 1);App(Bvar 2,Bvar 0)]))) in
        pi (Sort v) (pi (arrow st (Bvar 2) (Bvar 0))
          (arrow st sanity (arrow st (qapp Qtype u [Bvar 3;Bvar 2]) (Bvar 1))))
      | Qind ->
        let motive=arrow st (qapp Qtype u [Bvar 1;Bvar 0]) (Sort Zero) in
        let branch=pi (Bvar 2) (App(Bvar 1,qapp Qctor u [Bvar 3;Bvar 2;Bvar 0])) in
        let result=pi (qapp Qtype u [Bvar 2;Bvar 1]) (App(Bvar 1,Bvar 0)) in
        pi motive (arrow st branch result) in
    pi (Sort u) (pi rel body)
end;;
