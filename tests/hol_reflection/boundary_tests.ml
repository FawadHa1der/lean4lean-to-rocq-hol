(* Focused fixture-free boundary controls. No admission, policy grants or axioms. *)
needs "hol/reflection.ml";;

module Lean4hol_reflection_boundary_tests = struct
  open Lean4hol
  module Ni=Lean4hol_nat_instantiation
  module Env=Lean4hol_env
  let initial_axioms=axioms()
  let count=ref 0
  let test label value =
    if not value then failwith ("reflection boundary: "^label);
    incr count;
    Printf.printf "REFLECTION_BOUNDARY_CHECK %d %s\n%!" !count label
  let rejected label f =
    let okay=try ignore(f());false with
      | Stop {kind=Proof_failure;_} -> true in
    test label okay
  let same j k=aconv (concl j.Ni.h) (concl k.Ni.h) && hyp k.Ni.h=[]
  let run () =
    let j=Ni.infer Env.empty [] (Sort Zero) in
    test "genuine closed sort inference" (hyp j.Ni.h=[] && frees(concl j.Ni.h)=[]);
    test "genuine identity cast" (same j (Ni.cast j j.Ni.ty));
    test "genuine checked sort" (Ni.sort j=Succ Zero);
    let bad={j with Ni.h=TRUTH} in
    rejected "identity cast unrelated theorem" (fun () -> Ni.cast bad bad.Ni.ty);
    rejected "sort unrelated theorem" (fun () -> Ni.sort bad);
    rejected "existing downstream sym theorem guard" (fun () -> Ni.sym bad);
    let ctx={j with Ni.g=[Sort Zero]} in
    rejected "identity cast context mismatch" (fun () -> Ni.cast ctx ctx.Ni.ty);
    rejected "sort context mismatch" (fun () -> Ni.sort ctx);
    let assumed={j with Ni.h=ASSUME(concl j.Ni.h)} in
    rejected "identity cast hypothesis" (fun () -> Ni.cast assumed assumed.Ni.ty);
    rejected "sort hypothesis" (fun () -> Ni.sort assumed);
    let endpoints={j with Ni.left=Sort(Succ Zero)} in
    rejected "identity cast endpoints" (fun () -> Ni.cast endpoints endpoints.Ni.ty);
    let f=Ni.infer Env.empty [] (Lam(Anonymous,Sort Zero,Bvar 0)) in
    let f',_,a,b=Ni.pi f in
    test "genuine already-Pi" (same f f' && a=Sort Zero && b=Sort Zero);
    rejected "already-Pi unrelated theorem" (fun () -> Ni.pi {f with Ni.h=TRUTH});
    rejected "already-Pi context mismatch" (fun () -> Ni.pi {f with Ni.g=[Sort Zero]});
    rejected "already-Pi hypothesis" (fun () -> Ni.pi {f with Ni.h=ASSUME(concl f.Ni.h)});
    test "get success is preserved" (Ni.get "positive" (Ok 7)=7);
    List.iter (fun (kind,label) ->
      let error={kind;message="original"} in
      let direct=try ignore(Ni.get "boundary" (Error error));false with
        | Stop e -> e.kind=kind && e.message="boundary: original" in
      test (label^" direct Stop preserved") direct;
      let wrapped=Lean4hol.run 100000 [] [Sort Zero] (fun _ -> Ni.get "boundary" (Error error)) in
      test (label^" through run preserved") (match wrapped with
        | Error e -> e.kind=kind && e.message="boundary: original" | Ok _ -> false))
      [Resource,"Resource";Unsupported,"Unsupported";Invalid_input,"Invalid_input";Proof_failure,"Proof_failure"];
    test "no new HOL axioms" (axioms()=initial_axioms)
end;;
Lean4hol_reflection_boundary_tests.run();;
