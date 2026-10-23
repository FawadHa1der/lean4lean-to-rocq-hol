(* Independent finite controls; the universal guarantees are Rocq theorems. *)
module U = Universe_complete_native
let assertions = ref 0 and witnesses = ref 0
let check label ok = incr assertions; if not ok then failwith label
let rec nat = function 0 -> U.O | n -> U.S(nat(n-1))
let rec integer = function U.O -> 0 | U.S n -> 1 + integer n
let rec list = function [] -> U.Nil | x::xs -> U.Cons(x,list xs)
let rec host = function U.Nil -> [] | U.Cons(x,xs) -> x::host xs
let p = U.NameAnon
let q = U.NameNum(p,U.N0)
let r = U.NameNum(q,U.N0)
let names = [p;q;r]
let rec powerset = function [] -> [[]] | n::ns ->
  let rest=powerset ns in rest @ List.map(fun xs->n::xs) rest
let guards = powerset names
let atom_wf = function
  | U.SubConst(_,k) -> integer k>0
  | U.SubVar(ns,n,_) -> List.mem n (host ns)
let guard rho ns = List.for_all(fun n->rho n>0) (host ns)
let eval_atom rho = function
  | U.SubConst(ns,k) -> if guard rho ns then integer k else 0
  | U.SubVar(ns,n,k) -> if guard rho ns then rho n+integer k else 0
let eval_atoms rho xs = List.fold_left(fun a x->max a (eval_atom rho x)) 0 (host xs)
let rec eval rho = function
  | U.LZero -> 0 | U.LSucc u -> 1+eval rho u
  | U.LMax(u,v) -> max (eval rho u) (eval rho v)
  | U.LIMax(u,v) -> let b=eval rho v in if b=0 then 0 else max (eval rho u) b
  | U.LParam n -> rho n | U.LMVar _ -> 0
let rec nodes = function
  | U.LSucc u -> 1+nodes u
  | U.LMax(u,v) | U.LIMax(u,v) -> 1+nodes u+nodes v
  | _ -> 1
let atoms = List.concat_map(fun ns ->
  List.init 4 (fun k->U.SubConst(list ns,nat(k+1))) @
  List.concat_map(fun n->List.init 5(fun k->U.SubVar(list ns,n,nat k))) ns) guards
let arrays =
  let a=Array.of_list atoms in let n=Array.length a in
  U.Nil :: List.map(fun x->list[x]) atoms @
  List.init n (fun i->list[a.(i);a.((i*7+3) mod n)]) @
  List.init n (fun i->list[a.(i);a.((i*3+1) mod n);a.((i*11+8) mod n)])
let valuations = List.concat_map(fun a->List.concat_map(fun b->List.map(fun c->
  fun n->if n=p then a else if n=q then b else if n=r then c else 0)
  [0;1;3]) [0;1;3]) [0;1;3]
let witness xs ys =
  let x=List.find(fun x->not(List.exists(fun y->U.sublevel_le x y=U.True) (host ys))) (host xs) in
  let rho n=integer(U.atom_countervaluation x ys n) in
  incr witnesses;
  check "countervaluation beats entire right list" (eval_atoms rho ys < eval_atoms rho xs);
  check "countervaluation beats right list at chosen atom" (eval_atoms rho ys < eval_atom rho x);
  rho
let normalized u = match U.normalize_level(nat(nodes u)) u with
  | U.Accept xs -> check "normalized atom wellformedness" (List.for_all atom_wf (host xs)); xs
  | _ -> failwith "meta-free sufficient-fuel normalization failed"
let zero=U.LZero and param n=U.LParam n
let basics=[U.LZero;U.LSucc U.LZero;U.LSucc(U.LSucc U.LZero);U.LParam p;U.LParam q;U.LParam r]
let pairs f xs=List.concat_map(fun a->List.map(fun b->f(a,b)) xs) xs
let first=basics @ List.map(fun u->U.LSucc u) basics @ pairs(fun(a,b)->U.LMax(a,b)) basics @
  pairs(fun(a,b)->U.LIMax(a,b)) basics
let nested=List.concat_map(fun u->[
  U.LIMax(u,U.LMax(param p,param q)); U.LIMax(u,U.LIMax(param q,param r));
  U.LSucc(U.LIMax(u,param r)); U.LMax(U.LIMax(u,param p),U.LIMax(param q,param r))]) first
let levels=first @ List.init 96 (fun i->List.nth nested ((i*17) mod List.length nested))
let () =
  check "arbitrary atom inventory" (List.length atoms=92);
  List.iter(fun x->check "arbitrary atom precondition" (atom_wf x)) atoms;
  List.iter(fun xs->List.iter(fun ys->
    match U.sublevels_le xs ys with
    | U.False -> ignore(witness xs ys)
    | U.True -> List.iter(fun rho->check "positive atoms semantic control"
        (eval_atoms rho xs<=eval_atoms rho ys)) valuations) arrays) arrays;
  let prepared=List.map(fun u->u,normalized u) levels in
  List.iter(fun(u,xs)->List.iter(fun(v,ys)->
    let fuel=nat(max(nodes u)(nodes v)) in
    let le=U.level_le fuel u v and eq=U.level_equiv fuel u v in
    (match le with
    | U.Accept U.False -> let rho=witness xs ys in
        check "negative level semantic counterexample" (eval rho v<eval rho u)
    | U.Accept U.True -> List.iter(fun rho->check "positive level semantic control" (eval rho u<=eval rho v)) valuations
    | _ -> failwith "full-fuel inequality did not decide");
    (match eq with
    | U.Accept U.False -> let rho=if U.sublevels_le xs ys=U.False then witness xs ys else witness ys xs in
        check "negative equality semantic counterexample" (eval rho u<>eval rho v)
    | U.Accept U.True -> List.iter(fun rho->check "positive equality semantic control" (eval rho u=eval rho v)) valuations
    | _ -> failwith "full-fuel equivalence did not decide");
    check "equivalence equals two accepted inequalities"
      (eq=U.Accept(if le=U.Accept U.True && U.level_le fuel v u=U.Accept U.True then U.True else U.False));
    check "list equality agrees with scalar"
      (U.levels_equiv fuel (list[zero;u;zero]) (list[zero;v;zero])=eq)) prepared) prepared;
  let large=list[U.SubVar(list[p],p,nat 512);U.SubConst(list[q],nat 1024)] in
  let high=U.SubVar(list[p;q;r],r,nat 1025) in
  check "large-offset witness preconditions" (atom_wf high && List.for_all atom_wf (host large));
  ignore(witness (list[high]) large);
  let rho=witness (list[U.SubVar(list[p;q;r],r,nat 0)]) large in
  check "large right offsets force a large spike" (rho r>1024);
  check "spike leaves other guarded variables at one" (rho p=1 && rho q=1);
  check "spike leaves outside variables at zero" (rho (U.NameNum(r,U.N0))=0);
  (* Preconditions matter: a zero constant is semantic zero, but has no
     dominating atom in the empty list. Such an atom is never normalized. *)
  let malformed=list[U.SubConst(U.Nil,U.O)] in
  check "wellformedness cannot be omitted" (U.sublevels_le malformed U.Nil=U.False);
  List.iter(fun rho->check "malformed zero countermodel boundary" (eval_atoms rho malformed=0)) valuations;
  let unguarded=U.SubVar(U.Nil,p,U.O) and selfguarded=U.SubVar(list[p],p,U.O) in
  check "self-guard precondition cannot be omitted" (not(atom_wf unguarded));
  check "unguarded variable syntactic nondomination" (U.sublevel_le unguarded selfguarded=U.False);
  List.iter(fun rho->check "unguarded variable semantic equality boundary"
    (eval_atom rho unguarded=eval_atom rho selfguarded)) valuations;
  check "fuel decline not negative witness" (U.level_le U.O zero zero=U.Decline U.OutOfFuel);
  check "metadata rejection not comparison false"
    (U.level_equiv(nat 16)(U.LMVar p)zero=U.Reject U.MetaVariable);
  check "list length mismatch" (U.levels_equiv U.O (list[zero]) U.Nil=U.Accept U.False);
  check "list mismatch before later metadata"
    (U.levels_equiv(nat 16)(list[zero;U.LMVar p])(list[U.LSucc zero;zero])=U.Accept U.False);
  check "empty list mismatch before metadata and fuel"
    (U.levels_equiv U.O U.Nil (list[U.LMVar p])=U.Accept U.False);
  check "head fuel exhaustion before later length mismatch"
    (U.levels_equiv U.O (list[zero]) (list[zero;U.LMVar p])=U.Decline U.OutOfFuel);
  check "matching prefix reaches later metadata"
    (U.levels_equiv(nat 16)(list[zero;U.LMVar p])(list[zero;zero])=U.Reject U.MetaVariable);
  check "head metadata precedes later length mismatch"
    (U.levels_equiv(nat 16)(list[U.LMVar p])(list[zero;zero])=U.Reject U.MetaVariable);
  Printf.printf "UNIVERSE_COMPLETENESS_PASS assertions=%d witnesses=%d atoms=%d lists=%d levels=%d valuations=%d\n%!"
    !assertions !witnesses (List.length atoms) (List.length arrays) (List.length levels) (List.length valuations)
