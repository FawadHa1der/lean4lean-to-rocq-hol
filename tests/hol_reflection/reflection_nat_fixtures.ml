(* Test-only arithmetic dependencies for pinned Primitive.Condition.
   Candidate bodies use only admitted recursors; every entry is checked by
   the unchanged environment admission API, with an empty axiom policy. *)
needs "tests/hol_reflection/reflection_boolean_fixtures.ml";;
needs "hol/primitive_validation.ml";;

module Lean4hol_reflection_nat_fixture = struct
  open Lean4hol
  module Fix=Lean4hol_reflection_fixture
  module Env=Lean4hol_env
  open Fix.Quote
  let zero=con ["Nat";"zero"] []
  let suc n=app (con ["Nat";"succ"] []) n
  let falsep=con ["False"] []
  let natrec u motive z s n=apps (con ["Nat";"rec"] [u]) [motive;z;s;n]
  let eqrec u a x motive r y h=apps (con ["Eq";"rec"] [u;Fix.one]) [a;x;motive;r;y;h]
  let abort p h=apps (con ["False";"rec"] [Zero]) [lam falsep (fun _ -> p);h]
  let absurd_bool p a b h=apps (con ["Bool";"noConfusion"] [Zero]) [p;a;b;h]
  let beq n m=apps (con ["Nat";"beq"] []) [n;m]
  let ble n m=apps (con ["Nat";"ble"] []) [n;m]
  let le n m=apps (con ["Nat";"le"] []) [n;m]
  let refl_le n=app (con ["Nat";"le";"refl"] []) n
  let step_le n m h=apps (con ["Nat";"le";"step"] []) [n;m;h]
  let lerec n motive z s m h=apps (con ["Nat";"le";"rec"] []) [n;motive;z;s;m;h]
  let nat2ty b=run(arrow nn (arrow nn b))
  let primitive env parts body =
    let d={Env.kind=Env.Definition;name=Fix.name parts;params=[];typ=nat2ty bb;value=Some body} in
    let cert=Fix.get "authenticated Boolean arithmetic definition"
      (Lean4hol_primitive.check_definition ~fuel:200000 env d) in
    Fix.admitted (String.concat "." parts) (Env.admit_primitive env d
      (Lean4hol_primitive.definition_raw_theorem cert))
  let beq_body ()=lam nn (fun n -> lam nn (fun m ->
      app (natrec Fix.one (lam nn (fun _ -> arrow nn bb))
        (lam nn (fun m -> natrec Fix.one (lam nn (fun _ -> bb)) tt
          (lam nn (fun _ -> lam bb (fun _ -> ff))) m))
        (lam nn (fun _ -> lam (arrow nn bb) (fun ih -> lam nn (fun m ->
          natrec Fix.one (lam nn (fun _ -> bb)) ff
            (lam nn (fun k -> lam bb (fun _ -> app ih k))) m)))) n) m))
  let add_beq env = primitive env ["Nat";"beq"] (run(beq_body()))
  let add_ble env =
    let body=lam nn (fun n -> lam nn (fun m ->
      app (natrec Fix.one (lam nn (fun _ -> arrow nn bb)) (lam nn (fun _ -> tt))
        (lam nn (fun _ -> lam (arrow nn bb) (fun ih -> lam nn (fun m ->
          natrec Fix.one (lam nn (fun _ -> bb)) ff
            (lam nn (fun k -> lam bb (fun _ -> app ih k))) m)))) n) m)) in
    primitive env ["Nat";"ble"] (run body)
  let add_diag env is_le =
    let f=if is_le then ble else beq in
    let motive=lam nn (fun n -> eq bb (f n n) tt) in
    let body=lam nn (fun n -> natrec Zero motive (refl bb tt)
      (lam nn (fun k -> lam (app motive k) (fun ih -> ih))) n) in
    Fix.def env ["Nat";(if is_le then "ble_refl_checked" else "beq_refl_checked")]
      [] (run(pi nn (fun n -> app motive n))) (run body)
  let add_eq_true env =
    let goal n m=arrow (eq bb (beq n m) tt) (eq nn n m) in
    let motive=lam nn (fun n -> pi nn (goal n)) in
    let z=lam nn (fun m -> natrec Zero (lam nn (goal zero))
      (lam (eq bb tt tt) (fun _ -> refl nn zero))
      (lam nn (fun k -> lam (goal zero k) (fun _ ->
        lam (eq bb ff tt) (fun h -> absurd_bool (eq nn zero (suc k)) ff tt h)))) m) in
    let s=lam nn (fun n -> lam (app motive n) (fun ih -> lam nn (fun m ->
      natrec Zero (lam nn (goal (suc n)))
        (lam (eq bb ff tt) (fun h -> absurd_bool (eq nn (suc n) zero) ff tt h))
        (lam nn (fun k -> lam (goal (suc n) k) (fun _ ->
          lam (eq bb (beq n k) tt) (fun h ->
            eqrec Zero nn n (lam nn (fun y -> lam (eq nn n y) (fun _ -> eq nn (suc n) (suc y))))
              (refl nn (suc n)) k (apps ih [k;h]))))) m))) in
    Fix.def env ["Nat";"eq_of_beq_eq_true"] [] (run(pi nn (fun n -> pi nn (goal n))))
      (run(lam nn (fun n -> natrec Zero motive z s n)))
  let add_eq_false env =
    let goal n m=arrow (eq bb (beq n m) ff) (nott(eq nn n m)) in
    let body=lam nn (fun n -> lam nn (fun m -> lam (eq bb (beq n m) ff) (fun hb ->
      lam (eq nn n m) (fun he ->
        let motive=lam nn (fun y -> lam (eq nn n y) (fun _ -> arrow (eq bb (beq n y) ff) falsep)) in
        let base=lam (eq bb (beq n n) ff) (fun hf ->
          let htrue=app (con ["Nat";"beq_refl_checked"] []) n in
          let transported=eqrec Zero bb (beq n n)
            (lam bb (fun b -> lam (eq bb (beq n n) b) (fun _ -> eq bb b ff))) hf tt htrue in
          absurd_bool falsep tt ff transported) in
        app (eqrec Zero nn n motive base m he) hb)))) in
    Fix.def env ["Nat";"ne_of_beq_eq_false"] [] (run(pi nn (fun n -> pi nn (goal n)))) (run body)
  let add_dec_eq env =
    let body=lam nn (fun n -> lam nn (fun m ->
      let p=eq nn n m and b=beq n m in
      let motive=lam bb (fun b' -> arrow (eq bb b b') (dec p)) in
      apps (con ["Bool";"casesOn"] [Fix.one])
        [motive;b;
         lam (eq bb b ff) (fun h -> apps (con ["Decidable";"isFalse"] [])
           [p;apps (con ["Nat";"ne_of_beq_eq_false"] []) [n;m;h]]);
         lam (eq bb b tt) (fun h -> apps (con ["Decidable";"isTrue"] [])
           [p;apps (con ["Nat";"eq_of_beq_eq_true"] []) [n;m;h]]);
         refl bb b])) in
    Fix.def env ["Nat";"decEq"] [] (run(pi nn (fun n -> pi nn (fun m -> dec(eq nn n m))))) (run body)
  let add_le env =
    let b={Env.indexed_name=Fix.name ["Nat";"le"];indexed_level_params=[];
      indexed_parameters=[Fix.name ["n"],Fix.nt];indices=[Fix.name ["m"],Fix.nt];
      indexed_result_level=Zero;
      indexed_constructors=[
        {Env.indexed_ctor_name=Fix.name ["Nat";"le";"refl"];indexed_fields=[];result_indices=[Bvar 0]};
        {Env.indexed_ctor_name=Fix.name ["Nat";"le";"step"];
         indexed_fields=[Env.Index_data Fix.nt;Env.Index_recursive [Bvar 0]];
         result_indices=[App(Fix.c ["Nat";"succ"] [],Bvar 1)]}];indexed_claims=[]} in
    let b={b with Env.indexed_claims=Env.generate_indexed {remaining=100000} b ~large:false ~k:false} in
    Fix.admitted "Nat.le" (Env.admit_indexed_inductive env b)
  let add_le_class env =
    let u=Fix.name ["u"] in
    let b={Env.family_name=Fix.name ["LE"];level_params=[u];
      parameters=[Fix.name ["A"],Sort(Succ(Param u))];result_level=Succ(Param u);
      family_constructors=[Fix.name ["LE";"mk"],[Env.Data(run(arrow (embed(Bvar 0))
        (arrow (embed(Bvar 0)) pp)))]];family_claims=[]} in
    let b={b with Env.family_claims=Env.generate_family {remaining=100000} b ~large:true ~k:false} in
    Fix.admitted "LE" (Env.admit_inductive_family env b)
  let add_le_projection env =
    let u=Fix.name ["u"] in
    let a=embed(Sort(Succ(Param u))) in
    let instance ty=app (con ["LE"] [Param u]) ty in
    let body=run(lam a (fun ty -> lam (instance ty) (fun inst d -> Proj(Fix.name ["LE"],0,inst d)))) in
    Fix.def env ["LE";"le"] [u] (run(pi a (fun ty -> arrow (instance ty) (arrow ty (arrow ty pp))))) body
  let add_le_instance env = Fix.def env ["instLENat"] []
    (run(app (con ["LE"] [Zero]) nn)) (run(apps (con ["LE";"mk"] [Zero]) [nn;con ["Nat";"le"] []]))
  let add_zero_le env =
    let motive=lam nn (le zero) in
    Fix.def env ["Nat";"zero_le_checked"] [] (run(pi nn (le zero)))
      (run(lam nn (fun m -> natrec Zero motive (refl_le zero)
        (lam nn (fun k -> lam (le zero k) (step_le zero k))) m)))
  let add_succ_le env =
    let body=lam nn (fun n -> lam nn (fun m -> lam (le n m) (fun h ->
      lerec n (lam nn (fun m -> lam (le n m) (fun _ -> le (suc n) (suc m)))) (refl_le (suc n))
        (lam nn (fun k -> lam (le n k) (fun _ -> lam (le (suc n) (suc k))
          (step_le (suc n) (suc k))))) m h))) in
    Fix.def env ["Nat";"succ_le_succ_checked"] []
      (run(pi nn (fun n -> pi nn (fun m -> arrow (le n m) (le (suc n) (suc m)))))) (run body)
  let add_le_true env =
    let goal n m=arrow (eq bb (ble n m) tt) (le n m) in
    let motive=lam nn (fun n -> pi nn (goal n)) in
    let z=lam nn (fun m -> lam (eq bb tt tt) (fun _ -> app (con ["Nat";"zero_le_checked"] []) m)) in
    let s=lam nn (fun n -> lam (app motive n) (fun ih -> lam nn (fun m ->
      natrec Zero (lam nn (goal (suc n)))
        (lam (eq bb ff tt) (fun h -> absurd_bool (le (suc n) zero) ff tt h))
        (lam nn (fun k -> lam (goal (suc n) k) (fun _ -> lam (eq bb (ble n k) tt)
          (fun h -> apps (con ["Nat";"succ_le_succ_checked"] []) [n;k;apps ih [k;h]])))) m))) in
    Fix.def env ["Nat";"le_of_ble_eq_true"] [] (run(pi nn (fun n -> pi nn (goal n))))
      (run(lam nn (fun n -> natrec Zero motive z s n)))
  let add_ble_step env =
    let goal n m=arrow (eq bb (ble n m) tt) (eq bb (ble n (suc m)) tt) in
    let motive=lam nn (fun n -> pi nn (goal n)) in
    let z=lam nn (fun _ -> lam (eq bb tt tt) (fun h -> h)) in
    let s=lam nn (fun n -> lam (app motive n) (fun ih -> lam nn (fun m ->
      natrec Zero (lam nn (goal (suc n)))
        (lam (eq bb ff tt) (fun h -> absurd_bool (eq bb (ble n zero) tt) ff tt h))
        (lam nn (fun k -> lam (goal (suc n) k) (fun _ ->
          lam (eq bb (ble n k) tt) (fun h -> apps ih [k;h])))) m))) in
    Fix.def env ["Nat";"ble_step_checked"] [] (run(pi nn (fun n -> pi nn (goal n))))
      (run(lam nn (fun n -> natrec Zero motive z s n)))
  let add_ble_of_le env =
    let body=lam nn (fun n -> lam nn (fun m -> lam (le n m) (fun h ->
      lerec n (lam nn (fun m -> lam (le n m) (fun _ -> eq bb (ble n m) tt)))
        (app (con ["Nat";"ble_refl_checked"] []) n)
        (lam nn (fun k -> lam (le n k) (fun _ -> lam (eq bb (ble n k) tt)
          (fun ih -> apps (con ["Nat";"ble_step_checked"] []) [n;k;ih])))) m h))) in
    Fix.def env ["Nat";"ble_eq_true_of_le_checked"] []
      (run(pi nn (fun n -> pi nn (fun m -> arrow (le n m) (eq bb (ble n m) tt))))) (run body)
  let add_le_false env =
    let body=lam nn (fun n -> lam nn (fun m -> lam (nott(eq bb (ble n m) tt)) (fun hn ->
      lam (le n m) (fun hl -> app hn (apps (con ["Nat";"ble_eq_true_of_le_checked"] []) [n;m;hl]))))) in
    Fix.def env ["Nat";"not_le_of_not_ble_eq_true"] []
      (run(pi nn (fun n -> pi nn (fun m -> arrow (nott(eq bb (ble n m) tt)) (nott(le n m)))))) (run body)
  let add_dec_le env =
    let body=lam nn (fun n -> lam nn (fun m ->
      let p=le n m and q=eq bb (ble n m) tt in
      apps (con ["dite"] [Fix.one]) [dec p;q;apps (con ["Bool";"decEq"] []) [ble n m;tt];
        lam q (fun h -> apps (con ["Decidable";"isTrue"] [])
          [p;apps (con ["Nat";"le_of_ble_eq_true"] []) [n;m;h]]);
        lam (nott q) (fun h -> apps (con ["Decidable";"isFalse"] [])
          [p;apps (con ["Nat";"not_le_of_not_ble_eq_true"] []) [n;m;h]])])) in
    Fix.def env ["Nat";"decLe"] [] (run(pi nn (fun n -> pi nn (fun m -> dec(le n m))))) (run body)
  let stages=["beq",add_beq;"beq-diag",(fun e -> add_diag e false);
    "eq-true",add_eq_true;"eq-false",add_eq_false;"dec-eq",add_dec_eq;
    "ble",add_ble;"ble-diag",(fun e -> add_diag e true);"nat-le",add_le;
    "le-class",add_le_class;"le-projection",add_le_projection;"le-instance",add_le_instance;
    "zero-le",add_zero_le;"succ-le",add_succ_le;"le-true",add_le_true;
    "ble-step",add_ble_step;"ble-of-le",add_ble_of_le;"le-false",add_le_false;"dec-le",add_dec_le]
end;;
