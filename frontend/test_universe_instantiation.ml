(* Independent finite semantic controls, separate from the universal theorems. *)
module U = Universe_instantiation_native
let assertions = ref 0 and positive_le = ref 0 and positive_eq = ref 0
let check label ok = incr assertions; if not ok then failwith label
let rec nat = function 0 -> U.O | n -> U.S(nat(n-1))
let rec integer = function U.O -> 0 | U.S n -> 1 + integer n
let rec list = function [] -> U.Nil | x::xs -> U.Cons(x,list xs)
let p=U.NameAnon
let q=U.NameNum(p,U.N0)
let r=U.NameNum(q,U.N0)
let zero=U.LZero
let one=U.LSucc zero
let rec lookup ps us n = match ps,us with
  | p::ps,u::us -> if p=n then u else lookup ps us n
  | _ -> U.LParam n
let rec subst ps us = function
  | U.LZero -> U.LZero | U.LSucc u -> U.LSucc(subst ps us u)
  | U.LMax(u,v) -> U.LMax(subst ps us u,subst ps us v)
  | U.LIMax(u,v) -> U.LIMax(subst ps us u,subst ps us v)
  | U.LParam n -> lookup ps us n | U.LMVar n -> U.LMVar n
let rec eval rho = function
  | U.LZero -> 0 | U.LSucc u -> 1+eval rho u
  | U.LMax(u,v) -> max (eval rho u) (eval rho v)
  | U.LIMax(u,v) -> let b=eval rho v in if b=0 then 0 else max (eval rho u) b
  | U.LParam n -> rho n | U.LMVar _ -> 0
let rec has_meta = function
  | U.LMVar _ -> true | U.LSucc u -> has_meta u
  | U.LMax(u,v) | U.LIMax(u,v) -> has_meta u || has_meta v | _ -> false
let rec wf ns = function
  | U.LZero -> true | U.LSucc u -> wf ns u
  | U.LMax(u,v) | U.LIMax(u,v) -> wf ns u && wf ns v
  | U.LParam n -> List.mem n ns | U.LMVar _ -> false
let rec nodes = function
  | U.LSucc u -> 1+nodes u
  | U.LMax(u,v) | U.LIMax(u,v) -> 1+nodes u+nodes v | _ -> 1
let bases=[zero;one;U.LParam p;U.LParam q;U.LParam r;U.LMVar p]
let pairs f xs=List.concat_map(fun a->List.map(fun b->f(a,b)) xs) xs
let first=bases @ List.map(fun u->U.LSucc u) bases @
  pairs(fun(a,b)->U.LMax(a,b)) bases @ pairs(fun(a,b)->U.LIMax(a,b)) bases
let levels=first @ List.concat_map(fun u->[
  U.LIMax(u,U.LMax(U.LParam p,U.LParam q));
  U.LIMax(u,U.LIMax(U.LParam q,U.LParam r));
  U.LSucc(U.LIMax(u,U.LParam r))]) first
let parameter_lists=[[];[p];[q];[p;q];[q;p];[p;p];[p;q;r]]
let replacement_lists=[[];[zero];[one];[U.LParam q];[U.LMVar r];
  [U.LParam q;zero];[U.LParam q;U.LParam p];[U.LMax(U.LParam r,one);U.LIMax(U.LParam p,U.LParam r)];
  [zero;U.LMVar p];[zero;one;U.LParam r]]
let targets=[[];[p];[q];[p;q];[p;q;r]]
let valuations=List.concat_map(fun a->List.concat_map(fun b->List.map(fun c->
  fun n->if n=p then a else if n=q then b else if n=r then c else 0)
  [0;1;4]) [0;1;4]) [0;1;4]
let () =
  List.iter(fun ps->List.iter(fun us->
    List.iter(fun n->check "lookup including duplicate/short lists"
      (U.lookup_level(list ps)(list us)n=lookup ps us n)) [p;q;r;U.NameNum(r,U.N0)];
    List.iter(fun u->
      let got=U.subst_level(list ps)(list us)u in
      check "simultaneous structural oracle" (got=subst ps us u);
      check "metadata oracle" ((U.level_has_meta got=U.True)=has_meta got);
      if not(has_meta u) && List.for_all(fun x->not(has_meta x)) us then
        check "meta-free instantiation" (not(has_meta got));
      List.iter(fun qs->
        check "scope oracle" ((U.level_wf(list qs)got=U.True)=wf qs got);
        if List.length ps=List.length us && wf ps u && List.for_all(wf qs)us then
          check "scope preservation at correct arity" (wf qs got)) targets;
      List.iter(fun rho->
        let extended n=eval rho (lookup ps us n) in
        check "universe substitution semantic oracle" (eval rho got=eval extended u);
        check "extracted interpretation" (integer(U.level_eval(fun n->nat(rho n)) got)=eval rho got);
        List.iter(fun n->check "instantiated assignment agrees with oracle"
          (integer(U.instantiated_assignment(fun n->nat(rho n))(list ps)(list us)n)=extended n))
          [p;q;r]) valuations) levels) replacement_lists) parameter_lists;
  let small=List.filter(fun u->not(has_meta u)) first in
  let replacements=List.filter(List.for_all(fun u->not(has_meta u)))replacement_lists in
  List.iter(fun us->List.iter(fun u->List.iter(fun v->
    let a=U.subst_level(list[p;q])(list us)u and b=U.subst_level(list[p;q])(list us)v in
    let initial=nat(max(nodes u)(nodes v)) and enough=nat(max(nodes a)(nodes b)) in
    if U.level_le initial u v=U.Accept U.True then begin
      incr positive_le; check "accepted inequality preserved at substituted-size fuel"
        (U.level_le enough a b=U.Accept U.True)
    end;
    if U.level_equiv initial u v=U.Accept U.True then begin
      incr positive_eq; check "accepted equivalence preserved at substituted-size fuel"
        (U.level_equiv enough a b=U.Accept U.True)
    end)small)small)replacements;
  List.iter(fun ps->List.iter(fun us->
    let u=U.LParam p and v=U.LMax(U.LParam p,U.LParam q) in
    let w=U.LMax(U.LParam q,U.LParam p) in
    let instantiate=U.subst_level(list ps)(list us) in
    let a=instantiate u and b=instantiate v and c=instantiate w in
    check "parameter-list matrix original inequality" (U.level_le(nat 3)u v=U.Accept U.True);
    incr positive_le;
    check "parameter-list matrix instantiated inequality"
      (U.level_le(nat(max(nodes a)(nodes b)))a b=U.Accept U.True);
    check "parameter-list matrix original equality" (U.level_equiv(nat 3)v w=U.Accept U.True);
    incr positive_eq;
    check "parameter-list matrix instantiated equality"
      (U.level_equiv(nat(max(nodes b)(nodes c)))b c=U.Accept U.True)
  )replacements)parameter_lists;
  check "replacement is simultaneous, not recursive"
    (U.subst_level(list[p;q])(list[U.LParam q;zero])(U.LParam p)=U.LParam q);
  check "duplicate parameter first match"
    (U.subst_level(list[p;p])(list[one;zero])(U.LParam p)=one);
  check "short replacement preserves unmatched parameter"
    (U.subst_level(list[p;q])(list[zero])(U.LParam q)=U.LParam q);
  check "extra unused meta replacement is not traversed"
    (U.subst_level(list[p])(list[one;U.LMVar r])(U.LParam p)=one);
  check "missing arity premise can break target scope"
    (U.level_wf U.Nil (U.subst_level(list[p;q])(list[zero])(U.LParam q))=U.False);
  check "distinct parameters not universally equal"
    (U.level_equiv(nat 2)(U.LParam p)(U.LParam q)=U.Accept U.False);
  check "negative equality need not survive instantiation"
    (U.level_equiv(nat 2)(U.subst_level(list[p;q])(list[zero;zero])(U.LParam p))
      (U.subst_level(list[p;q])(list[zero;zero])(U.LParam q))=U.Accept U.True);
  check "original comparison fits one unit of fuel"
    (U.level_equiv(nat 1)(U.LParam p)(U.LParam p)=U.Accept U.True);
  let grown=U.subst_level(list[p])(list[U.LSucc zero])(U.LParam p) in
  check "positive preservation is not same-fuel preservation"
    (U.level_equiv(nat 1)grown grown=U.Decline U.OutOfFuel);
  check "expanded comparison succeeds at its new syntax-size bound"
    (U.level_equiv(nat(nodes grown))grown grown=U.Accept U.True);
  check "meta replacements excluded from accepted-comparison theorem"
    (U.level_equiv(nat 8)(U.subst_level(list[p])(list[U.LMVar r])(U.LParam p))zero=U.Reject U.MetaVariable);
  Printf.printf "UNIVERSE_INSTANTIATION_PASS assertions=%d levels=%d parameter_lists=%d replacement_lists=%d valuations=%d positive_le=%d positive_eq=%d\n%!"
    !assertions (List.length levels) (List.length parameter_lists) (List.length replacement_lists)
    (List.length valuations) !positive_le !positive_eq
