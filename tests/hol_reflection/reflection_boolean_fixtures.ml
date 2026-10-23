(* Canonical dependency fixtures, independently admitted from generated Bool
   and Eq recursors. No Bool theorem is admitted as an axiom or policy grant.
   noConfusionType has P -> P on equal nullary constructors, P otherwise. *)
needs "tests/hol_reflection/reflection_fixtures.ml";;

module Lean4hol_reflection_boolean_fixture = struct
  open Lean4hol
  module Fix=Lean4hol_reflection_fixture
  module Env=Lean4hol_env
  open Fix.Quote
  let add env =
    let u=Fix.name ["u"] in
    let uu=Param u and sortu=embed(Sort(Param u)) in
    let nc p a b=apps (con ["Bool";"noConfusionType"] [uu]) [p;a;b] in
    let nct=run(pi sortu (fun _ -> arrow bb (arrow bb sortu))) in
    let ncb=run(lam sortu (fun p -> lam bb (fun a -> lam bb (fun b ->
      app (apps (con ["Bool";"rec"] [Succ uu])
        [lam bb (fun _ -> arrow bb sortu);
         lam bb (fun b -> apps (con ["Bool";"rec"] [Succ uu])
           [lam bb (fun _ -> sortu);arrow p p;p;b]);
         lam bb (fun b -> apps (con ["Bool";"rec"] [Succ uu])
           [lam bb (fun _ -> sortu);p;arrow p p;b]);a]) b)))) in
    let env=Fix.def env ["Bool";"noConfusionType"] [u] nct ncb in
    let npt=run(pi sortu (fun p -> pi bb (fun a -> pi bb (fun b ->
      arrow (eq bb a b) (nc p a b))))) in
    let npb=run(lam sortu (fun p -> lam bb (fun a -> lam bb (fun b ->
      lam (eq bb a b) (fun h ->
       apps (con ["Eq";"rec"] [uu;Fix.one])
        [bb;a;lam bb (fun b -> lam (eq bb a b) (fun _ -> nc p a b));
         apps (con ["Bool";"rec"] [uu])
          [lam bb (fun a -> nc p a a);lam p (fun x -> x);lam p (fun x -> x);a];b;h]))))) in
    let env=Fix.def env ["Bool";"noConfusion"] [u] npt npb in
    let yes b=apps (con ["Decidable";"isTrue"] []) [eq bb b b;refl bb b] in
    let no a b=apps (con ["Decidable";"isFalse"] [])
      [eq bb a b;lam (eq bb a b) (fun h ->
        apps (con ["Bool";"noConfusion"] [Zero]) [con ["False"] [];a;b;h])] in
    let dt=run(pi bb (fun a -> pi bb (fun b -> dec(eq bb a b)))) in
    let db=run(lam bb (fun a -> lam bb (fun b ->
      app (apps (con ["Bool";"rec"] [Fix.one])
       [lam bb (fun a -> pi bb (fun b -> dec(eq bb a b)));
        lam bb (fun b -> apps (con ["Bool";"rec"] [Fix.one])
          [lam bb (fun b -> dec(eq bb ff b));yes ff;no ff tt;b]);
        lam bb (fun b -> apps (con ["Bool";"rec"] [Fix.one])
          [lam bb (fun b -> dec(eq bb tt b));no tt ff;yes tt;b]);a]) b))) in
    Fix.def env ["Bool";"decEq"] [] dt db
end;;
