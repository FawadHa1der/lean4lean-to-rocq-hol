let quote_cache_axioms_before = axioms();;
needs "hol/core.ml";;

module Quote_reference = struct
  open Lean4hol
  let rec name = function
    | Anonymous -> `L4Anonymous`
    | Str(n,s) -> node "L4String" [name n;
        mk_list(List.init (String.length s) (fun i -> number(Char.code s.[i])),`:num`)]
    | Num(n,s) -> node "L4Numeric" [name n;natural s]
  let rec level = function
    | Zero -> `L4Zero`
    | Succ u -> node "L4Succ" [level u]
    | Max(u,v) -> node "L4Max" [level u;level v]
    | Imax(u,v) -> node "L4IMax" [level u;level v]
    | Param n -> node "L4Param" [name n]
  let rec expr = function
    | Bvar i -> node "L4BVar" [number i]
    | Sort u -> node "L4Sort" [level u]
    | Const(n,us) -> node "L4Const" [name n;mk_list(List.map level us,`:l4_level`)]
    | App(f,a) -> node "L4App" [expr f;expr a]
    | Lam(n,a,b) -> node "L4Lam" [name n;expr a;expr b]
    | Pi(n,a,b) -> node "L4Pi" [name n;expr a;expr b]
    | Let(n,a,v,b) -> node "L4Let" [name n;expr a;expr v;expr b]
    | Natlit n -> node "L4NatLit" [natural n]
    | Proj(n,i,e) -> node "L4Proj" [name n;number i;expr e]
end;;

let quote_cache_tests = ref 0;;
let quote_expect message predicate =
  if not predicate then failwith message else incr quote_cache_tests;;
let quote_compare label reference cached input =
  let a = reference input and b = cached input in
  quote_expect label (aconv a b);
  let th = TRANS (REFL a) (REFL b) in
  quote_expect (label ^ " exact closed theorem")
    (hyp th = [] && aconv (concl th) (mk_eq(a,b)));;
let quote_outcome f x = try let _ = f x in None with
  Lean4hol.Stop e -> Some(e.Lean4hol.kind,e.Lean4hol.message);;

module Quote_cache_test = struct
  open Lean4hol
  let name i = Str(Num(Anonymous,string_of_int (i mod 31)),"n" ^ string_of_int i)
  let level i = match i mod 5 with
    | 0 -> Zero | 1 -> Succ Zero | 2 -> Max(Param(name i),Zero)
    | 3 -> Imax(Succ Zero,Param(name i)) | _ -> Param(name i)
  let rec expr d i = if d = 0 then match i mod 4 with
      | 0 -> Bvar (i mod 7) | 1 -> Sort(level i)
      | 2 -> Const(name i,[level i;level(i+1)])
      | _ -> Natlit(string_of_int(i*17))
    else let a = expr (d-1) (i+1) and b = expr (d-1) (i+2) in
      match i mod 5 with
      | 0 -> App(a,b) | 1 -> Lam(name i,a,b) | 2 -> Pi(name i,a,b)
      | 3 -> Let(name i,a,b,a) | _ -> Proj(name i,i mod 4,a)
  let rec shared depth e = if depth = 0 then e else
    let e' = App(e,e) in shared (depth-1) e'
  let run () =
    for i = 0 to 4500 do
      quote_compare "name quotation" Quote_reference.name quote_name (name i);
      quote_compare "level quotation" Quote_reference.level quote_level (level i);
      quote_compare "expr quotation" Quote_reference.expr quote_expr (expr (i mod 4) i)
    done;
    List.iter (fun n -> quote_compare "name post-eviction" Quote_reference.name quote_name n)
      [Anonymous;Str(Anonymous,"");Str(Anonymous,"\000\255");Num(Anonymous,"123456789012345678901234567890")];
    List.iter (fun e -> quote_expect "invalid syntax error preserved"
      (quote_outcome Quote_reference.expr e = quote_outcome quote_expr e))
      [Bvar(-1);Natlit "";Natlit "-1";Natlit "01";Natlit "x";
       Const(Num(Anonymous,"01"),[]);Proj(Anonymous,-1,Sort Zero);
       Let(Anonymous,Sort Zero,Natlit "2",Natlit "-3")];
    for depth = 0 to 13 do
      quote_compare "shared DAG quotation" Quote_reference.expr quote_expr
        (shared depth (Sort Zero))
    done;
    quote_expect "axioms unchanged" (axioms() = quote_cache_axioms_before);
    Printf.printf "HOL_QUOTE_CACHE_TESTS_PASSED %d\n%!" !quote_cache_tests;
    for depth = 12 to 18 do
      let e = shared depth (Sort(Succ Zero)) in
      let before = Gc.allocated_bytes() and started = Sys.time() in
      let quoted = quote_expr e in
      let seconds = Sys.time() -. started and allocated = Gc.allocated_bytes() -. before in
      quote_expect "benchmark has expression type" (type_of quoted = `:l4_expr`);
      Printf.printf "HOL_QUOTE_BENCH depth=%d seconds=%.9f allocated=%.0f\n%!"
        depth seconds allocated
    done
end;;
Quote_cache_test.run();;
