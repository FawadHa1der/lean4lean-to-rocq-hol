module Bridge_reference = struct
  module H = Lean4hol
  module W = Hol_input
  let rec name = function
    | W.Anonymous -> H.Anonymous | W.Str(n,s) -> H.Str(name n,s)
    | W.Num(n,s) -> H.Num(name n,s)
  let rec level = function
    | W.Zero -> H.Zero | W.Succ u -> H.Succ(level u)
    | W.Max(u,v) -> H.Max(level u,level v)
    | W.Imax(u,v) -> H.Imax(level u,level v) | W.Param n -> H.Param(name n)
  let rec expr = function
    | W.Bvar i -> H.Bvar i | W.Sort u -> H.Sort(level u)
    | W.Const(n,us) -> H.Const(name n,List.map level us)
    | W.App(f,a) -> H.App(expr f,expr a)
    | W.Lam(n,a,b) -> H.Lam(name n,expr a,expr b)
    | W.Pi(n,a,b) -> H.Pi(name n,expr a,expr b)
    | W.Let(n,a,v,b) -> H.Let(name n,expr a,expr v,expr b)
    | W.Natlit n -> H.Natlit n
    | W.Proj(n,i,e) -> H.Proj(name n,i,expr e)
end;;

module Bridge_cache_test = struct
  open Hol_input
  let count = ref 0
  let check label predicate = if predicate then incr count else failwith label
  let name i = Str(Num(Anonymous,string_of_int(i mod 31)),"x" ^ string_of_int i)
  let level i = match i mod 5 with
    | 0 -> Zero | 1 -> Succ Zero | 2 -> Max(Param(name i),Zero)
    | 3 -> Imax(Succ Zero,Param(name i)) | _ -> Param(name i)
  let rec expr d i = if d=0 then match i mod 4 with
      | 0 -> Bvar(i mod 7) | 1 -> Sort(level i)
      | 2 -> Const(name i,[level i;level(i+1)])
      | _ -> Natlit(string_of_int(i*13))
    else let a = expr (d-1) (i+1) and b = expr (d-1) (i+2) in
      match i mod 5 with
      | 0 -> App(a,b) | 1 -> Lam(name i,a,b) | 2 -> Pi(name i,a,b)
      | 3 -> Let(name i,a,b,a) | _ -> Proj(name i,i mod 4,a)
  let rec shared depth e = if depth=0 then e else shared (depth-1) (App(e,e))
  let run () =
    for i=0 to 4500 do
      let n = name i and u = level i and e = expr (i mod 4) i in
      check "name translation" (Bridge_reference.name n = Hol_check.name n);
      check "level translation" (Bridge_reference.level u = Hol_check.level u);
      check "expression translation" (Bridge_reference.expr e = Hol_check.expr e)
    done;
    List.iter (fun e -> check "malformed syntax remains unchanged for validation"
      (Bridge_reference.expr e = Hol_check.expr e))
      [Bvar(-1);Natlit "01";Natlit "-1";Natlit "";
       Const(Num(Anonymous,"01"),[]);Proj(Anonymous,-1,Sort Zero)];
    for depth=0 to 13 do
      let e = shared depth (Sort Zero) in
      check "shared expression translation" (Bridge_reference.expr e = Hol_check.expr e)
    done;
    Printf.printf "HOL_BRIDGE_CACHE_TESTS_PASSED %d\n%!" !count;
    for depth=12 to 18 do
      let e = shared depth (Sort(Succ Zero)) in
      let before = Gc.allocated_bytes() and started = Sys.time() in
      let h = Hol_check.expr e in
      let seconds = Sys.time() -. started and allocated = Gc.allocated_bytes() -. before in
      let shares = match h with Lean4hol.App(a,b) -> a==b | _ -> false in
      Printf.printf "HOL_BRIDGE_BENCH depth=%d seconds=%.9f allocated=%.0f shares=%b\n%!"
        depth seconds allocated shares
    done
end;;
Bridge_cache_test.run();;
