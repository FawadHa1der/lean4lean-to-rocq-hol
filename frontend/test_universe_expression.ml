module U = Universe_expression_native
let assertions = ref 0
let check label ok = incr assertions; if not ok then failwith label
let rec nat = function 0 -> U.O | n -> U.S(nat(n-1))
let rec integer = function U.O -> 0 | U.S n -> 1+integer n
let rec list = function [] -> U.Nil | a::rest -> U.Cons(a,list rest)
let rec host_list = function U.Nil -> [] | U.Cons(a,rest) -> a::host_list rest
let p=U.NameAnon and q=U.NameNum(U.NameAnon,U.N0)
let bvar n=U.EBVar(nat n)
let zero=U.LZero and up=U.LParam p and uq=U.LParam q
let sortp=U.ESort up and sortq=U.ESort uq
let rec lookup ps us n = match ps,us with
  | p::ps,u::us -> if p=n then u else lookup ps us n
  | _ -> U.LParam n
let rec level ps us = function
  | U.LZero -> U.LZero | U.LSucc v -> U.LSucc(level ps us v)
  | U.LMax(a,b) -> U.LMax(level ps us a,level ps us b)
  | U.LIMax(a,b) -> U.LIMax(level ps us a,level ps us b)
  | U.LParam n -> lookup ps us n | U.LMVar n -> U.LMVar n
let rec levels ps us = function
  | U.ESort u -> U.ESort(level ps us u)
  | U.EConst(n,vs) -> U.EConst(n,list(List.map(level ps us)(host_list vs)))
  | U.EApp(f,a) -> U.EApp(levels ps us f,levels ps us a)
  | U.ELam(n,bi,a,b) -> U.ELam(n,bi,levels ps us a,levels ps us b)
  | U.EPi(n,bi,a,b) -> U.EPi(n,bi,levels ps us a,levels ps us b)
  | U.ELet(n,a,v,b,nd) -> U.ELet(n,levels ps us a,levels ps us v,levels ps us b,nd)
  | U.EProj(n,i,a) -> U.EProj(n,i,levels ps us a)
  | U.EMData a -> U.EMData(levels ps us a)
  | e -> e
let rec lift amount cutoff = function
  | U.EBVar i -> bvar(if integer i >= cutoff then amount+integer i else integer i)
  | U.EApp(f,a) -> U.EApp(lift amount cutoff f,lift amount cutoff a)
  | U.ELam(n,bi,a,b) -> U.ELam(n,bi,lift amount cutoff a,lift amount (cutoff+1) b)
  | U.EPi(n,bi,a,b) -> U.EPi(n,bi,lift amount cutoff a,lift amount (cutoff+1) b)
  | U.ELet(n,a,v,b,nd) -> U.ELet(n,lift amount cutoff a,lift amount cutoff v,lift amount (cutoff+1) b,nd)
  | U.EProj(n,i,a) -> U.EProj(n,i,lift amount cutoff a)
  | U.EMData a -> U.EMData(lift amount cutoff a)
  | e -> e
let rec subst_many index values = function
  | U.EBVar i as e ->
      let i=integer i in if i<index then e else
      (match List.nth_opt values (i-index) with
       | Some v -> lift index 0 v | None -> bvar(max 0 (i-List.length values)))
  | U.EApp(f,a) -> U.EApp(subst_many index values f,subst_many index values a)
  | U.ELam(n,bi,a,b) -> U.ELam(n,bi,subst_many index values a,subst_many (index+1) values b)
  | U.EPi(n,bi,a,b) -> U.EPi(n,bi,subst_many index values a,subst_many (index+1) values b)
  | U.ELet(n,a,v,b,nd) -> U.ELet(n,subst_many index values a,subst_many index values v,
      subst_many (index+1) values b,nd)
  | U.EProj(n,i,a) -> U.EProj(n,i,subst_many index values a)
  | U.EMData a -> U.EMData(subst_many index values a)
  | e -> e
let rec scoped depth = function
  | U.EBVar i -> integer i < depth
  | U.EApp(a,b) -> scoped depth a && scoped depth b
  | U.ELam(_,_,a,b) | U.EPi(_,_,a,b) -> scoped depth a && scoped (depth+1) b
  | U.ELet(_,a,v,b,_) -> scoped depth a && scoped depth v && scoped (depth+1) b
  | U.EProj(_,_,a) | U.EMData a -> scoped depth a
  | _ -> true
let bases=[bvar 0;bvar 1;bvar 3;U.EFVar p;U.EMVar q;U.ESort zero;sortp;
  U.ESort(U.LIMax(up,uq));U.ESort(U.LMVar q);U.EConst(p,U.Nil);
  U.EConst(q,list[up;U.LIMax(up,uq)]);U.ELit(U.LitNat U.N0);
  U.ELit(U.LitNat(U.Npos U.XH));U.ELit(U.LitString U.EmptyString)]
let pairs f=List.concat_map(fun a->List.map(fun b->f(a,b))bases)bases
let first=bases @ pairs(fun(a,b)->U.EApp(a,b)) @
  pairs(fun(a,b)->U.ELam(p,U.BImplicit,a,b)) @ pairs(fun(a,b)->U.EPi(q,U.BInstImplicit,a,b)) @
  List.concat_map(fun a->[U.ELet(p,sortp,a,U.EApp(bvar 0,bvar 1),U.True);
    U.ELet(q,sortq,bvar 0,a,U.False);U.EProj(p,nat 2,a);U.EMData a])bases
let terms=first @ List.concat_map(fun a->[
  U.ELam(q,U.BStrictImplicit,sortp,U.ELam(p,U.BDefault,a,bvar 2));
  U.ELet(p,sortq,a,U.ELam(q,U.BDefault,sortp,U.EApp(bvar 2,a)),U.False);
  U.EProj(q,nat 1,U.EApp(a,bvar 3));U.EMData(U.EPi(p,U.BDefault,a,U.EApp(a,bvar 1)))])first
let ps_lists=[[];[p];[p;q];[p;p]]
let us_lists=[[];[zero];[uq;zero];[U.LMax(up,uq);up];[U.LMVar p];[U.LSucc zero;zero;U.LIMax(up,uq)]]
let values=[bvar 0;sortp;U.EConst(q,list[up;uq]);U.ELam(p,U.BDefault,sortq,bvar 1)]
let batches=[[];[bvar 0];[sortp;sortq];[bvar 1;bvar 0];values]
let () =
  List.iter(fun ps->List.iter(fun us->
    let map=U.subst_levels(list ps)(list us) in
    List.iter(fun e->
      let mapped=map e in
      check "independent universe substitution oracle" (mapped=levels ps us e);
      List.iter(fun depth->
        check "scope preserved exactly" (U.scoped(nat depth)mapped=U.scoped(nat depth)e);
        check "scope host oracle" ((U.scoped(nat depth)mapped=U.True)=scoped depth mapped)) [0;1;2;3;4];
      List.iter(fun amount->List.iter(fun cutoff->
        let lifted=U.lift(nat amount)(nat cutoff)e in
        check "lift host oracle" (lifted=lift amount cutoff e);
        check "lift commutes with universe substitution"
          (map lifted=U.lift(nat amount)(nat cutoff)mapped)) [0;1;2]) [0;1;3];
      List.iter(fun index->
        List.iter(fun value->
          let got=U.subst(nat index)value e in
          check "single substitution via independent simultaneous oracle" (got=subst_many index [value] e);
          check "single substitution commutes" (map got=U.subst(nat index)(map value)mapped))values;
        List.iter(fun batch->
          let got=U.subst_many(nat index)(list batch)e in
          check "batch host oracle" (got=subst_many index batch e);
          check "batch substitution commutes"
            (map got=U.subst_many(nat index)(list(List.map map batch))mapped))batches) [0;1;2];
      List.iter(fun value->check "instantiate commutes"
        (map(U.instantiate e value)=U.instantiate mapped (map value)))values;
      List.iter(fun batch->check "instantiate_many commutes including empty list"
        (map(U.instantiate_many e (list batch))=U.instantiate_many mapped (list(List.map map batch))))batches
    )terms)us_lists)ps_lists;
  check "all constructor samples retained" (List.length terms=3290);
  check "open replacement lifted under binder"
    (U.instantiate(U.ELam(p,U.BDefault,sortp,bvar 1))(bvar 0)=U.ELam(p,U.BDefault,sortp,bvar 1));
  check "inner binder protected"
    (U.instantiate(U.ELam(p,U.BDefault,sortp,bvar 0))(bvar 3)=U.ELam(p,U.BDefault,sortp,bvar 0));
  check "batch is innermost-first"
    (U.instantiate_many(U.EApp(bvar 0,bvar 1))(list[sortp;sortq])=U.EApp(sortp,sortq));
  check "duplicate universe parameter first match"
    (U.subst_levels(list[p;p])(list[zero;uq])sortp=U.ESort zero);
  let digit_zero=U.Ascii(U.False,U.False,U.False,U.False,U.True,U.True,U.False,U.False) in
  let r=U.NameStr(p,U.String(digit_zero,U.EmptyString)) in
  let ur=U.LParam r in
  check "string-tagged universe name substituted"
    (U.subst_levels(list[r])(list[zero])(U.ESort ur)=U.ESort zero);
  check "numeric name zero differs from string name zero"
    (U.subst_levels(list[r])(list[zero])(U.ESort uq)=U.ESort uq);
  List.iter(fun u->
    let ps=[r;p;q] and us=[zero;uq;U.LSucc zero] in
    let map=U.subst_levels(list ps)(list us) in
    let e=U.ELam(r,U.BInstImplicit,U.ESort u,U.EApp(bvar 1,U.EConst(r,list[u]))) in
    let v=U.EConst(q,list[u]) in
    check "source successor/max/imax and string names oracle" (map e=levels ps us e);
    check "source level traversal lift commutation"
      (map(U.lift(nat 2)(nat 1)e)=U.lift(nat 2)(nat 1)(map e));
    check "source level traversal substitution commutation"
      (map(U.subst(nat 0)v e)=U.subst(nat 0)(map v)(map e));
    check "source level traversal batch commutation"
      (map(U.subst_many(nat 0)(list[v;bvar 0])e)=
       U.subst_many(nat 0)(list[map v;bvar 0])(map e));
    check "source level traversal scope unchanged"
      (U.scoped(nat 1)(map e)=U.scoped(nat 1)e)
  )[U.LSucc ur;U.LMax(ur,U.LSucc up);U.LIMax(U.LMax(up,uq),U.LSucc ur)];
  if !assertions <> 7264342 then failwith "assertion inventory changed";
  Printf.printf "UNIVERSE_EXPRESSION_PASS assertions=%d expressions=%d configurations=24\n%!"
    !assertions (List.length terms)
