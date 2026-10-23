(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Additive proof composition only. No new object-language rule or axiom.
   The audited instantiation helper is imported byte-for-byte. *)
needs "hol/reflection_terms.ml";;
needs "hol/instantiation_certificates.ml";;

let nat_checked_rules =
  let all=CONJUNCTS l4_edef_RULES in
  List.map (fun i ->
    let rule=List.nth all i in
    let vs,body=strip_forall(concl rule) in
    let env=List.hd vs and policy=`policy:l4_entry list` in
    let raw=mk_comb(`l4_edef`,env) in
    let checked=list_mk_comb(`l4_checked`,[policy;env]) in
    let target=list_mk_forall(policy::vs,subst [checked,raw] body) in
    let h=prove(target,REWRITE_TAC [l4_checked] THEN MESON_TAC [rule]) in
    if hyp h<>[] || frees(concl h)<>[] then failwith "open checked rule";
    i,h) [2;3;5;6;7;8;10];;

module Lean4hol_nat_instantiation = struct
  open Lean4hol
  module Env=Lean4hol_env
  module Fix=Lean4hol_reflection_terms
  module Syn=Lean4hol_reflection_syntax
  type judgment={env:Env.environment;g:expr list;left:expr;right:expr;ty:expr;h:thm}
  let get=Fix.get
  let fuel=200000
  let budget ()={remaining=fuel}
  let expected env g e f t=node "l4_checked" [Env.quote_policy env;Env.quote_env env;
    quote_context g;quote_expr e;quote_expr f;quote_expr t]
  let pack env g left right ty h =
    if hyp h<>[] || frees(concl h)<>[] || not(aconv (expected env g left right ty) (concl h)) then
      stop Proof_failure "composed judgment is not closed/exact for source/context/environment/policy";
    {env;g;left;right;ty;h}
  let unpack env h =
    let head,args=strip_comb(concl h) in
    match fst(dest_const head),args with
    | "l4_checked",[p;e;g;l;r;t] when aconv p (Env.quote_policy env) && aconv e (Env.quote_env env) ->
      pack env (List.map Syn.decode (dest_list g)) (Syn.decode l) (Syn.decode r) (Syn.decode t) h
    | _ -> stop Proof_failure "wrong checked environment/policy/shape"
  let same env j=ignore(pack env j.g j.left j.right j.ty j.h)
  let specialize env theorem args =
    let p=genvar(type_of(Env.quote_policy env)) and e=genvar(type_of(Env.quote_env env)) in
    INST [Env.quote_policy env,p;Env.quote_env env,e]
      (CONV_RULE computation (SPECL (p::e::args) theorem))
  let use env i args js =
    List.iter (same env) js;
    let th=specialize env (List.assoc i nat_checked_rules) args in
    unpack env (MP th (if List.length js=1 then (List.hd js).h else
      end_itlist CONJ (List.map (fun j -> j.h) js)))
  let infer env g e = let t,h=get "composition inference" (Env.infer ~fuel env g e) in pack env g e e t h
  let check env g e t=pack env g e e t (get "composition checking" (Env.check ~fuel env g e t))
  let convert env g e f t=pack env g e f t (get "composition type/argument conversion" (Env.convert ~fuel env g e f t))
  let sort j=same j.env j; match j.ty with Sort u -> u | _ -> stop Proof_failure "expected checked sort"
  let cast j ty =
    same j.env j;
    if j.ty=ty then j else
    let ht=infer j.env j.g j.ty in
    let u=sort ht in
    let he=convert j.env j.g j.ty ty (Sort u) in
    use j.env 5 [quote_context j.g;quote_expr j.ty;quote_expr ty;quote_expr j.left;
      quote_expr j.right;quote_level u] [he;j]
  let sym j=use j.env 6 [quote_context j.g;quote_expr j.left;quote_expr j.right;quote_expr j.ty] [j]
  let trans j k =
    same j.env k;
    if j.g<>k.g || j.right<>k.left then stop Proof_failure "transitivity endpoints/context differ";
    let k=cast k j.ty in
    use j.env 7 [quote_context j.g;quote_expr j.left;quote_expr j.right;quote_expr k.right;quote_expr j.ty] [j;k]
  let pi j=same j.env j; match j.ty with
    | Pi(n,a,b) -> j,n,a,b
    | _ ->
      let norm,_,h=get "function type normalization" (Env.normalize ~fuel j.env j.g j.ty) in
      let he=unpack j.env h in
      let j=use j.env 5 [quote_context j.g;quote_expr j.ty;quote_expr norm;
        quote_expr j.left;quote_expr j.right;quote_level(sort he)] [he;j] in
      match norm with Pi(n,a,b)->j,n,a,b | _ -> stop Proof_failure "function type is not Pi"
  let app f a =
    same f.env a;
    if f.g<>a.g then stop Proof_failure "application contexts differ";
    let f,n,d,b=pi f in let a=cast a d in
    use f.env 2 [quote_context f.g;quote_expr f.left;quote_expr f.right;quote_expr a.left;
      quote_expr a.right;quote_name n;quote_expr d;quote_expr b] [f;a]
  let close j = match j.g with
    | [] -> stop Invalid_input "no binder to close"
    | a::g ->
      let ha=infer j.env g a in
      use j.env 3 [quote_context g;quote_name Anonymous;quote_name Anonymous;quote_expr a;quote_expr a;
        quote_expr j.left;quote_expr j.right;quote_expr j.ty;quote_level(sort ha)] [ha;j]
  let instantiated_typing ha hb hv =
    same ha.env ha;same ha.env hb;same ha.env hv;
    if hb.g<>ha.left::ha.g || hv.g<>ha.g || hb.left<>hb.right ||
      ha.left<>ha.right || hv.left<>hv.right || hv.ty<>ha.left then
      stop Proof_failure "typed instantiation context/type/endpoints differ";
    let th=specialize ha.env l4_checked_instantiation
      [quote_context ha.g;quote_expr ha.left;quote_level(sort ha);quote_expr hb.left;
       quote_expr hb.right;quote_expr hb.ty;quote_expr hv.left] in
    unpack ha.env (MP th (CONJ ha.h (CONJ hb.h hv.h)))
  let beta env g n a b t hv hb =
    use env 8 [quote_context g;quote_name n;quote_expr a;quote_expr b;quote_expr t;quote_expr hv.left] [hb;hv]
  (* An equality between two lambdas is applied to a typed argument. The
     audited lemma certifies each substituted body; existing beta/application
     rules propagate the cross-body equality without new conversion search. *)
  let apply_symbolic j v =
    let j,_,a,t=pi j in
    match j.left,j.right with
    | Lam(n,d,b),Lam(n',d',b') when d=a && d'=a ->
      let ha=infer j.env j.g a and hv=check j.env j.g v a in
      let hb=check j.env (a::j.g) b t and hb'=check j.env (a::j.g) b' t in
      let il=instantiated_typing ha hb hv and ir=instantiated_typing ha hb' hv in
      let bl=beta j.env j.g n a b t hv hb and br=beta j.env j.g n' a b' t hv hb' in
      trans il (trans (trans (trans (sym bl) (app j hv)) br) ir)
    | _ -> stop Proof_failure "symbolic application requires aligned lambda domains"
  (* One completed application of a known wrapper. No constant is unfolded. *)
  let apply_wrapper prefix arg =
    let prefix=cast prefix (infer prefix.env prefix.g prefix.right).ty in
    let prefix,_,a,t=pi prefix in
    match prefix.right with
    | Lam(n,d,b) when d=a ->
      let arg=cast arg a in
      let hb=check prefix.env (a::prefix.g) b t in
      let hv=check prefix.env prefix.g arg.right a in
      let head=app prefix arg in
      trans head (beta prefix.env prefix.g n a b t hv hb)
    | _ -> stop Proof_failure "wrapper head is not a lambda"
  let proof_irrelevance env g p l r =
    let hp=check env g p (Sort Zero) and hl=check env g l p and hr=check env g r p in
    use env 10 [quote_context g;quote_expr p;quote_expr l;quote_expr r] [hp;hl;hr]
  let generic second =
    let r=Syn.reflection second in let open Fix.Quote in
    let fw p b=arrow (eq bb b tt) p in
    let bw p b=arrow (if second then eq bb b ff else nott(eq bb b tt)) (nott p) in
    let bind k=lam pp (fun p -> lam bb (fun b -> lam (fw p b) (fun yes ->
      lam (bw p b) (fun no -> k p b yes no)))) in
    let left=run(bind (fun p b yes no ->
      apps (embed r.Syn.to_dec) [p;b;lam pp (fun q ->
        lam (arrow (fw p b) (arrow (bw p b) q)) (fun use -> apps use [yes;no]))])) in
    let right=run(bind (fun p b yes no ->
      let pos h=apps (con ["Decidable";"isTrue"] []) [p;app yes h] in
      let neg h=apps (con ["Decidable";"isFalse"] []) [p;app no h] in
      if second then apps (con ["Bool";"casesOn"] [Fix.one])
        [lam bb (fun b' -> arrow (eq bb b b') (dec p));b;
         lam (eq bb b ff) neg;lam (eq bb b tt) pos;refl bb b]
      else apps (con ["dite"] [Fix.one])
        [dec p;eq bb b tt;apps (con ["Bool";"decEq"] []) [b;tt];
         lam (eq bb b tt) pos;lam (nott(eq bb b tt)) neg])) in
    let ty=run(pi pp (fun p -> pi bb (fun b -> pi (fw p b) (fun _ -> pi (bw p b) (fun _ -> dec p))))) in
    let rec peel lam g e=match e with
      | Lam(_,a,b) when lam -> peel lam (a::g) b
      | Pi(_,a,b) when not lam -> peel lam (a::g) b
      | _ -> g,e in
    let g,l=peel true [] left and g',r=peel true [] right and gt,t=peel false [] ty in
    if g<>g' || g<>gt || List.length g<>4 then stop Proof_failure "generic telescope differs";
    g@[Fix.nt;Fix.nt],l,r,t
  let seed env second = let g,l,r,t=generic second in convert env g l r t
  let arguments second =
    let c=Syn.nat_condition second in
    let n=Bvar 1 and m=Bvar 0 in
    let app2 f=Env.apps f [n;m] in
    let p=if second then app2 c.Syn.prop else app2(Fix.c ["Nat";"le"] []) in
    [p;app2 c.Syn.as_bool;
     app2(Fix.c ["Nat";(if second then "eq_of_beq_eq_true" else "le_of_ble_eq_true")] []);
     app2(Fix.c ["Nat";(if second then "ne_of_beq_eq_false" else "not_le_of_not_ble_eq_true")] [])]
end;;
