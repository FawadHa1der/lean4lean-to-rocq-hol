(* Prepared only: use an instrumented private snapshot, never production core. *)
needs "tests/common.ml";;
let run_scheduler_probe_controls variant =
  let open Lean4hol in
  let open Early_test in
  let shape = function
    | Sort _ -> "Sort" | Pi _ -> "Pi" | Lam _ -> "Lam" | App _ -> "App"
    | Let _ -> "Let" | Bvar _ -> "Bvar" | Const _ -> "Const"
    | Natlit _ -> "Natlit" | Strlit _ -> "Strlit" | Proj _ -> "Proj" in
  let level_shape = function
    | Zero -> "Zero" | Succ _ -> "Succ" | Max _ -> "Max"
    | Imax _ -> "Imax" | Param _ -> "Param" in
  let run label g left right typ =
    let counts=Hashtbl.create 31 in
    let count key=Hashtbl.replace counts key
      (1+(try Hashtbl.find counts key with Not_found -> 0)) in
    test_schedule_mark := count;
    test_schedule_expr := (fun tag a b ->
      count(tag^":"^shape a^":"^shape b);
      if tag="early.type" then (match b with
        | Sort _ -> count "would.skip.inferred-sort" | _ -> ());
      if tag="early.enter" then (match a with
        | Sort _ | Pi _ -> count "would.skip.expression" | _ -> ());
      if tag="whnf.enter" && (a=left || a=right) then count "target.whnf";
      if tag="equal.enter" && a=left && b=right then count "target.equal");
    test_schedule_level := (fun tag u v ->
      count(tag^":"^level_shape u^":"^level_shape v));
    let started=Sys.time() in
    let result=convert ~fuel:100000 g left right typ in
    let seconds=Sys.time()-.started in
    test_schedule_expr := (fun _ _ _ -> ());
    test_schedule_level := (fun _ _ _ -> ());
    test_schedule_mark := (fun _ -> ());
    exact label g left right typ (get label result);
    test "target equality reached" (Hashtbl.mem counts "target.equal");
    if variant="guarded" then (
      test "no impossible successor-zero search in focused positive controls"
        (not(Hashtbl.mem counts "level.request:Succ:Zero"));
      let expected=match label with
        | "sort-equivalent" | "pi-alpha" -> "skip.expression"
        | "beta-nonproof" -> "skip.inferred-sort"
        | "nonproof-successor" -> "skip.successor"
        | _ -> "early.success" in
      test "expected guard or typed success observed" (Hashtbl.mem counts expected));
    Hashtbl.fold (fun key value acc -> (key,value)::acc) counts []
    |> List.sort compare
    |> List.iter (fun(key,value)->
      Printf.printf "SCHEDULE_COUNT %s %s %s %d\n%!" variant label key value);
    Printf.printf "SCHEDULE_CPU %s %s %.6f\n%!" variant label seconds in
  run "sort-equivalent" [] (Sort Zero) (Sort(Max(Zero,Zero))) (Sort(Succ Zero));
  run "pi-alpha" [] p (Pi(Str(Anonymous,"renamed"),prop,Pi(n,Bvar 0,Bvar 1))) prop;
  run "beta-nonproof" [] (beta (Sort(Succ Zero)) prop) prop (Sort(Succ Zero));
  run "beta-proof" [] (beta p hp) hp p;
  run "let-proof" [] (zeta q hq) hq q;
  run "dependent-proof" [Bvar 1;Bvar 0;prop] (Bvar 0) (Bvar 1) (Bvar 2);
  run "nonproof-successor" [Bvar 0;Sort(Succ Zero)]
    (Let(n,Bvar 1,Bvar 0,Bvar 0)) (Bvar 0) (Bvar 1);
  finish ("schedule-"^variant);;
