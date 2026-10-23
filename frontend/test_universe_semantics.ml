(* Finite extracted-code controls complement, not replace, universal proofs. *)
module U = Universe_native
let assertions = ref 0
let check label value = incr assertions; if not value then failwith label
let rec nat = function 0 -> U.O | n -> U.S (nat (n-1))
let rec integer = function U.O -> 0 | U.S n -> 1 + integer n
let rec list = function [] -> U.Nil | x::xs -> U.Cons(x,list xs)
let p = U.NameAnon
let q = U.NameNum (U.NameAnon,U.N0)
let meta = U.NameNum(q,U.N0)
let rec eval rho = function
  | U.LZero -> 0 | U.LSucc u -> 1 + eval rho u
  | U.LMax(u,v) -> max (eval rho u) (eval rho v)
  | U.LIMax(u,v) -> let r=eval rho v in if r=0 then 0 else max (eval rho u) r
  | U.LParam n -> rho n | U.LMVar _ -> 0
let rec has_meta = function
  | U.LMVar _ -> true | U.LSucc u -> has_meta u
  | U.LMax(u,v) | U.LIMax(u,v) -> has_meta u || has_meta v
  | _ -> false
let rec nodes = function
  | U.LSucc u -> 1 + nodes u
  | U.LMax(u,v) | U.LIMax(u,v) -> 1 + nodes u + nodes v
  | _ -> 1
let rec guarded rho = function
  | U.Nil -> true | U.Cons(n,ns) -> rho n > 0 && guarded rho ns
let atom rho = function
  | U.SubConst(ns,k) -> if guarded rho ns then integer k else 0
  | U.SubVar(ns,n,k) -> if guarded rho ns then rho n + integer k else 0
let rec atoms rho = function
  | U.Nil -> 0 | U.Cons(x,xs) -> max (atom rho x) (atoms rho xs)
let zero = U.LZero
let one = U.LSucc zero
let bases = [zero;one;U.LParam p;U.LParam q;U.LMVar meta]
let pairs f xs = List.concat_map(fun a -> List.map(fun b -> f(a,b)) xs) xs
let first = bases @ List.map(fun u -> U.LSucc u) bases @
  pairs (fun (a,b) -> U.LMax(a,b)) bases @ pairs (fun (a,b) -> U.LIMax(a,b)) bases
let levels = first @ List.concat_map(fun a -> List.concat_map(fun b ->
  [U.LIMax(a,U.LMax(b,U.LParam p)); U.LIMax(a,U.LIMax(b,U.LParam q));
   U.LSucc(U.LIMax(a,b)); U.LMax(a,U.LIMax(b,zero))]) bases) first
let valuations = List.concat_map(fun a -> List.map(fun b ->
  fun n -> if n=p then a else if n=q then b else 0) [0;1;2;4]) [0;1;2;4]
let paths = List.map list [[];[p];[q];[p;q];[p;p];[q;p;q]]
let accepts = ref 0 and rejects = ref 0 and declines = ref 0
let () =
  List.iter(fun u ->
    check "syntax-size count" (integer(U.level_nodes u)=nodes u);
    let bounded=U.normalize_level(nat(nodes u)) u in
    check "syntax-size fuel suffices" (match bounded with
      | U.Accept _ -> not(has_meta u)
      | U.Reject U.MetaVariable -> has_meta u | _ -> false);
    check "normalization fuel extension control"
      (bounded=U.normalize_level(nat(nodes u+1)) u);
    List.iter(fun fuel ->
      let result=U.normalize_level (nat fuel) u in
      if has_meta u then check "outer metadata rejection precedes fuel"
        (result=U.Reject U.MetaVariable);
      if fuel=0 && not(has_meta u) then check "outer zero fuel"
        (result=U.Decline U.OutOfFuel);
      match result with
      | U.Accept xs -> incr accepts; List.iter(fun rho ->
          let expected=eval rho u in
          check "normalization semantic oracle" (atoms rho xs=expected);
          check "extracted level evaluator" (integer(U.level_eval(fun n->nat(rho n)) u)=expected);
          check "extracted atom evaluator" (integer(U.sublevels_eval(fun n->nat(rho n)) xs)=expected)) valuations
      | U.Reject U.MetaVariable -> incr rejects
      | U.Decline U.OutOfFuel -> incr declines
      | _ -> failwith "unexpected normalization outcome") [0;1;2;4;16]) levels;
  List.iter(fun u -> List.iter(fun path -> for k=0 to 3 do
    match U.normalize_aux (nat 16) u path (nat k) with
    | U.Accept xs -> List.iter(fun rho ->
        check "guarded-offset normalization oracle"
          (atoms rho xs=(if guarded rho path then eval rho u+k else 0))) valuations
    | U.Reject U.MetaVariable -> ()
    | _ -> failwith "unexpected full-fuel auxiliary outcome"
  done) paths) levels;
  List.iter(fun u -> List.iter(fun v ->
    let budget=nat(max(nodes u)(nodes v)) in
    let complete = function U.Accept _ -> not(has_meta u || has_meta v)
      | U.Reject U.MetaVariable -> has_meta u || has_meta v | _ -> false in
    check "syntax-size comparison fuel" (complete(U.level_le budget u v));
    check "syntax-size equivalence fuel" (complete(U.level_equiv budget u v));
    let le=U.level_le(nat 16) u v and eq=U.level_equiv(nat 16) u v in
    List.iter(fun rho ->
      check "accepted comparison soundness" (le<>U.Accept U.True || eval rho u<=eval rho v);
      check "accepted equivalence soundness" (eq<>U.Accept U.True || eval rho u=eval rho v)) valuations;
    check "equivalence symmetry" (eq=U.level_equiv(nat 16) v u)) first) first;
  let nested = List.init 64 (fun i -> List.nth levels (60+17*i)) in
  List.iter(fun u -> List.iter(fun v ->
    let le=U.level_le(nat 16) u v and eq=U.level_equiv(nat 16) u v in
    List.iter(fun rho ->
      check "nested accepted comparison" (le<>U.Accept U.True || eval rho u<=eval rho v);
      check "nested accepted equivalence" (eq<>U.Accept U.True || eval rho u=eval rho v)) valuations;
    check "nested equivalence symmetry" (eq=U.level_equiv(nat 16) v u)) nested) nested;
  List.iter(fun u ->
    let expected value = if has_meta u then U.Reject U.MetaVariable else U.Accept value in
    check "three-element equivalent list"
      (U.levels_equiv(nat 16) (list[u;U.LSucc u;U.LMax(u,zero)])
        (list[U.LMax(u,zero);U.LSucc(U.LMax(u,zero));u])=expected U.True);
    check "second list element disagrees"
      (U.levels_equiv(nat 16) (list[u;U.LSucc u]) (list[u;u])=expected U.False)) levels;
  check "empty lists need no recursive fuel" (U.levels_equiv U.O U.Nil U.Nil=U.Accept U.True);
  check "list mismatch short circuits later meta"
    (U.levels_equiv(nat 16) (list[zero;U.LMVar meta]) (list[one;zero])=U.Accept U.False);
  check "list positive prefix preserves later meta rejection"
    (U.levels_equiv(nat 16) (list[zero;U.LMVar meta]) (list[zero;zero])=U.Reject U.MetaVariable);
  check "hidden metadata rejected" (U.normalize_level(nat 16)(U.LIMax(U.LMVar meta,zero))=U.Reject U.MetaVariable);
  check "list length mismatch" (U.levels_equiv(nat 16)(list[zero]) U.Nil=U.Accept U.False);
  check "list semantic equality" (U.levels_equiv(nat 16)
    (list[U.LMax(U.LParam p,zero);U.LIMax(one,zero)])
    (list[U.LParam p;zero])=U.Accept U.True);
  check "not all results are vacuous" (!accepts>0 && !rejects>0 && !declines>0);
  Printf.printf "UNIVERSE_SEMANTICS_PASS assertions=%d levels=%d valuations=%d accepted=%d rejected=%d declined=%d\n%!"
    !assertions (List.length levels) (List.length valuations) !accepts !rejects !declines
