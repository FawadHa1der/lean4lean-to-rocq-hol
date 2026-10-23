(* Test-only candidates. Every environment entry passes existing admission;
   no policy grants or conversion axioms are used. *)
needs "hol/reflection_validation.ml";;

module Lean4hol_reflection_fixture = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Syn=Lean4hol_reflection_syntax
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message)
  let name xs=List.fold_left (fun n s -> Str(n,s)) Anonymous xs
  let c xs us=Const(name xs,us)
  let prop=Sort Zero and one=Succ Zero
  let nt=c ["Nat"] [] and bt=c ["Bool"] []
  let tru=c ["Bool";"true"] [] and fal=c ["Bool";"false"] []
  let progress label = Printf.printf "REFLECTION_FIXTURE %s\n%!" label
  let admissions=ref 0
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
  let admitted label result =
    let env,h=get label result in
    let expected=node "l4_evalid" [Env.quote_policy env;Env.quote_env env] in
    if hyp h<>[] || frees(concl h)<>[] || not(aconv expected (concl h)) then
      failwith(label^": environment certificate mismatch");
    incr admissions;progress label;env
  let block env parts level cs =
    let b={Env.family_name=name parts;level_params=[];parameters=[];
      result_level=level;family_constructors=cs;family_claims=[]} in
    let b={b with Env.family_claims=Env.generate_family {remaining=100000} b
      ~large:true ~k:(level=Zero && List.length cs=1)} in
    admitted (String.concat "." parts) (Env.admit_inductive_family env b)
  let def env parts ps ty body = admitted (String.concat "." parts)
    (Env.admit env {Env.kind=Env.Definition;name=name parts;params=ps;typ=ty;value=Some body})
  let base () =
    let env=block Env.empty ["Nat"] one
      [name ["Nat";"zero"],[];name ["Nat";"succ"],[Env.Recursive]] in
    let env=block env ["Bool"] one [name ["Bool";"false"],[];name ["Bool";"true"],[]] in
    let env=block env ["False"] Zero [] in
    let env=block env ["True"] Zero [name ["True";"intro"],[]] in
    let open Quote in
    let env=def env ["Not"] [] (run(arrow pp pp))
      (run(lam pp (fun p -> arrow p (con ["False"] [])))) in
    let db={Env.family_name=name ["Decidable"];level_params=[];
      parameters=[name ["p"],prop];result_level=one;
      family_constructors=[name ["Decidable";"isFalse"],[Env.Data(App(c ["Not"] [],Bvar 0))];
        name ["Decidable";"isTrue"],[Env.Data(Bvar 0)]];family_claims=[]} in
    let db={db with Env.family_claims=Env.generate_family {remaining=100000} db ~large:true ~k:false} in
    let env=admitted "Decidable" (Env.admit_inductive_family env db) in
    let u=name ["u"] in
    let eq={Env.indexed_name=name ["Eq"];indexed_level_params=[u];
      indexed_parameters=[name ["A"],Sort(Param u);name ["a"],Bvar 0];
      indices=[name ["b"],Bvar 1];indexed_result_level=Zero;
      indexed_constructors=[{Env.indexed_ctor_name=name ["Eq";"refl"];
        indexed_fields=[];result_indices=[Bvar 0]}];indexed_claims=[]} in
    let eq={eq with Env.indexed_claims=Env.generate_indexed {remaining=100000} eq ~large:true ~k:true} in
    let env=admitted "Eq" (Env.admit_indexed_inductive env eq) in
    let sortu=embed(Sort(Param u)) in
    let bct=run(pi (arrow bb sortu) (fun motive -> pi bb (fun b ->
      arrow (app motive ff) (arrow (app motive tt) (app motive b))))) in
    let bcb=run(lam (arrow bb sortu) (fun motive -> lam bb (fun b ->
      lam (app motive ff) (fun f -> lam (app motive tt) (fun t ->
       apps (con ["Bool";"rec"] [Param u]) [motive;f;t;b]))))) in
    let env=def env ["Bool";"casesOn"] [u] bct bcb in
    let itetype=run(pi sortu (fun a -> pi pp (fun p ->
      arrow (dec p) (arrow a (arrow a a))))) in
    let ite=run(lam sortu (fun a -> lam pp (fun p -> lam (dec p) (fun d ->
      lam a (fun yes -> lam a (fun no ->
       apps (con ["Decidable";"rec"] [Param u])
        [p;lam (dec p) (fun _ -> a);lam (nott p) (fun _ -> no);lam p (fun _ -> yes);d])))))) in
    let env=def env ["ite"] [u] itetype ite in
    let ditype=run(pi sortu (fun a -> pi pp (fun p ->
      arrow (dec p) (arrow (arrow p a) (arrow (arrow (nott p) a) a))))) in
    let dite=run(lam sortu (fun a -> lam pp (fun p -> lam (dec p) (fun d ->
      lam (arrow p a) (fun yes -> lam (arrow (nott p) a) (fun no ->
       apps (con ["Decidable";"rec"] [Param u])
        [p;lam (dec p) (fun _ -> a);no;yes;d])))))) in
    def env ["dite"] [u] ditype dite

  (* Generic reflection with an uninhabited Church-pair premise. These probes
     are genuinely typed and symbolic, but are NOT Reflection.defn1/defn2. *)
  let generic () =
    let open Quote in
    let rt=run(lam pp (fun p -> lam bb (fun _ ->
      pi pp (fun q -> arrow (arrow p (arrow (nott p) q)) q)))) in
    let rel p b=apps (embed rt) [p;b] in
    let yes p h=apps h [p;lam p (fun hp -> lam (nott p) (fun _ -> hp))] in
    let no p h=apps h [nott p;lam p (fun _ -> lam (nott p) (fun hn -> hn))] in
    {Syn.typ=rt;
     of_true=run(lam pp (fun p -> lam (rel p tt) (yes p)));
     of_false=run(lam pp (fun p -> lam (rel p ff) (no p)));
     to_dec=run(lam pp (fun p -> lam bb (fun b -> lam (rel p b) (fun h ->
       apps (con ["Bool";"rec"] [one]) [lam bb (fun _ -> dec p);
        apps (con ["Decidable";"isFalse"] []) [p;no p h];
        apps (con ["Decidable";"isTrue"] []) [p;yes p h];b]))))}
  let generic_condition () =
    let open Quote in
    let rt=run(lam pp (fun p -> lam bb (fun _ -> p))) in
    let rd=run(lam pp (fun p -> lam bb (fun _ -> lam p (fun h ->
      apps (con ["Decidable";"isTrue"] []) [p;h])))) in
    let cp=run(lam nn (fun _ -> lam nn (fun _ -> con ["True"] []))) in
    let cb=run(lam nn (fun _ -> lam nn (fun _ -> tt))) in
    let ch=run(lam nn (fun _ -> lam nn (fun _ -> con ["True";"intro"] []))) in
    let cd=run(lam nn (fun _ -> lam nn (fun _ ->
      apps (con ["Decidable";"isTrue"] []) [con ["True"] [];con ["True";"intro"] []]))) in
    {Syn.prop=cp;as_bool=cb;proof=ch;dec=cd;
     reflect={Syn.typ=rt;of_true=Sort Zero;of_false=Sort Zero;to_dec=rd}}
end;;
