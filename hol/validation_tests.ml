needs "hol/core.ml";;

module Lean4hol_validation_tests = struct
  open Lean4hol
  let count = ref 0
  let test label value = incr count; if not value then failwith ("validation: " ^ label)
  let original st g expressions =
    let depth d = tick st; if d > 512 then stop Resource "input nesting limit exceeded" in
    let bytes s = String.iter (fun _ -> tick st) s in
    let rec name d = function
      | Anonymous -> depth d
      | Str(n,s) -> depth d; bytes s; name (d+1) n
      | Num(n,s) -> depth d; bytes s; ignore(natural s); name (d+1) n in
    let rec level d = function
      | Zero -> depth d
      | Succ u -> depth d; level (d+1) u
      | Max(u,v) | Imax(u,v) -> depth d; level (d+1) u; level (d+1) v
      | Param n -> depth d; name (d+1) n in
    let rec expr d = function
      | Bvar i -> depth d; if i < 0 then stop Invalid_input "negative de Bruijn index"
      | Sort u -> depth d; level (d+1) u
      | Const(n,us) -> depth d; name (d+1) n; List.iter (level (d+1)) us
      | Natlit n -> depth d; bytes n; ignore(natural n)
      | Strlit s -> depth d; bytes s; ignore(string_scalars s)
      | Proj(n,i,e) -> depth d; name (d+1) n;
        if i < 0 then stop Invalid_input "negative projection index"; expr (d+1) e
      | App(f,a) -> depth d; expr (d+1) f; expr (d+1) a
      | Lam(n,a,b) | Pi(n,a,b) -> depth d; name (d+1) n; expr (d+1) a; expr (d+1) b
      | Let(n,a,v,b) -> depth d; name (d+1) n; expr (d+1) a; expr (d+1) v; expr (d+1) b in
    List.iter (expr 0) g; List.iter (expr 0) expressions
  let outcome validation fuel g es =
    try validation {remaining=fuel} g es; None with Stop e -> Some e
  let eq g es =
    test "old/new finite syntax checks and first-error order"
      (outcome original 1000000 g es = outcome validate 1000000 g es)
  let invalid es = match outcome validate 1000000 [] es with
    | Some {kind=Invalid_input;_} -> true | _ -> false
  let resource fuel es = match outcome validate fuel [] es with
    | Some {kind=Resource;_} -> true | _ -> false
  let prop = Sort Zero
  let deep count wrap leaf =
    let result = ref leaf in for _ = 1 to count do result := wrap !result done; !result
  let rng = Random.State.make [|1977;6841|]
  let pick n = Random.State.int rng n
  let leaves = [|Bvar 0;Bvar (-1);Sort Zero;Sort(Succ Zero);
    Const(Anonymous,[]);Const(Num(Anonymous,"01"),[]);
    Natlit "0";Natlit "12345678901234567890";Natlit "01";Natlit "";
    Strlit "hello";Strlit "\240\159\152\128";Strlit "\192\128";
    Proj(Anonymous,-1,prop)|]
  let rec generated depth =
    if depth=0 then leaves.(pick(Array.length leaves)) else
    let sub () = generated (depth-1) in
    match pick 10 with
    | 0 -> let a=sub() in App(a,a)
    | 1 -> App(sub(),sub())
    | 2 -> Lam(Anonymous,sub(),sub())
    | 3 -> Pi(Num(Anonymous,"3"),sub(),sub())
    | 4 -> Let(Str(Anonymous,"x"),sub(),sub(),sub())
    | 5 -> Proj(Num(Anonymous,"01"),-1,sub())
    | 6 -> Proj(Str(Anonymous,"x"),pick 3,sub())
    | 7 -> Sort(Imax(Max(Zero,Succ Zero),Param(Num(Anonymous,"01"))))
    | _ -> sub()
  let () =
    for _ = 1 to 2000 do
      let a=generated 5 and b=generated 4 in eq [] [a;b]; eq [a] [b]
    done;
    Array.iter (fun bad ->
      List.iter (fun e -> eq [] [e])
        [bad;App(bad,prop);App(prop,bad);Lam(Anonymous,bad,prop);
         Lam(Anonymous,prop,bad);Pi(Anonymous,bad,prop);Pi(Anonymous,prop,bad);
         Let(Anonymous,bad,prop,prop);Let(Anonymous,prop,bad,prop);
         Let(Anonymous,prop,prop,bad);Proj(Anonymous,0,bad)]) leaves;
    let tall = deep 20000 (fun e -> App(e,prop)) prop in
    test "twenty-thousand expression levels validate" (outcome validate 100000 [] [tall]=None);
    test "historical depth cap declines same syntax"
      (match outcome original 100000 [] [tall] with Some {kind=Resource;_}->true|_->false);
    test "finite work budget still declines" (resource 100 [tall]);
    let tall_name=deep 20000 (fun n -> Str(n,"x")) Anonymous in
    test "twenty-thousand name levels" (outcome validate 100000 [] [Const(tall_name,[])]=None);
    let tall_level=deep 20000 (fun u -> Succ u) Zero in
    test "twenty-thousand universe levels" (outcome validate 100000 [] [Sort tall_level]=None);
    let shared=deep 10000 (fun e -> App(e,e)) prop in
    test "shared DAG does not expand exponentially" (outcome validate 100000 [] [shared]=None);
    let shared_bad=deep 10000 (fun e -> App(e,e)) (Natlit "01") in
    test "invalid shared leaf is not skipped" (invalid [shared_bad]);
    test "deep invalid projection index" (invalid [deep 10000 (fun e -> App(e,prop)) (Proj(Anonymous,-1,prop))]);
    test "deep invalid UTF-8" (invalid [deep 10000 (fun e -> App(e,prop)) (Strlit "\237\160\128")]);
    let rec cyclic_expr=App(prop,cyclic_expr) in
    let rec cyclic_name=Str(cyclic_name,"x") in
    let rec cyclic_level=Succ cyclic_level in
    test "cyclic expression rejected" (invalid [cyclic_expr]);
    test "cyclic name rejected" (invalid [Const(cyclic_name,[])]);
    test "cyclic universe rejected" (invalid [Sort cyclic_level]);
    test "invalid syntax is never cached between calls" (invalid [Natlit "01"]);
    test "resource state is local" (resource 0 [prop] && outcome validate 10 [] [prop]=None);
    let ty,h = match infer [] prop with Ok result -> result | Error _ -> failwith "positive typing gate" in
    test "ordinary positive typing certificate remains closed" (hyp h=[] && ty=Sort(Succ Zero));
    test "ill-typed application does not become accepted"
      (match infer [] (App(prop,prop)) with Error _ -> true | Ok _ -> false);
    Printf.printf "HOL_ITERATIVE_VALIDATION_TESTS_PASSED %d\n%!" !count
end;;
