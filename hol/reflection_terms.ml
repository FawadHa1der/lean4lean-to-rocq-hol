(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Candidate syntax construction for Primitive.lean reflection helpers at
   8223d223ed98661882e95d9d6a7126df7097cd76. No environment is constructed or
   admitted here. Constructed terms must pass the checked proof interfaces. *)
needs "hol/reflection_validation.ml";;

module Lean4hol_reflection_terms = struct
  open Lean4hol
  module Env=Lean4hol_env
  let get label = function Ok x -> x | Error e -> raise(Stop {e with message=label^": "^e.message})
  let name xs=List.fold_left (fun n s -> Str(n,s)) Anonymous xs
  let c xs us=Const(name xs,us)
  let prop=Sort Zero and one=Succ Zero
  let nt=c ["Nat"] [] and bt=c ["Bool"] []
  let tru=c ["Bool";"true"] [] and fal=c ["Bool";"false"] []
  module Quote = struct
    let embed e d=lift {remaining=1000000} d 0 e
    let app f a d=App(f d,a d)
    let apps f xs d=Env.apps (f d) (List.map (fun x -> x d) xs)
    let lam a b d=Lam(Anonymous,a d,b (fun k -> Bvar(k-d-1)) (d+1))
    let pi a b d=Pi(Anonymous,a d,b (fun k -> Bvar(k-d-1)) (d+1))
    let arrow a b=pi a (fun _ -> b)
    let run e=e 0
    let con xs us=embed(c xs us)
    let pp=embed prop and nn=embed nt and bb=embed bt
    let tt=embed tru and ff=embed fal
    let nott p=app (con ["Not"] []) p
    let dec p=app (con ["Decidable"] []) p
    let eq a x y=apps (con ["Eq"] [one]) [a;x;y]
    let refl a x=apps (con ["Eq";"refl"] [one]) [a;x]
  end
end;;
