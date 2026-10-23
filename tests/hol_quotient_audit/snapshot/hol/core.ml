(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/judgments.ml";;

module Lean4hol = struct
  type name = Anonymous | Str of name * string | Num of name * string
  type level = Zero | Succ of level | Max of level * level
             | Imax of level * level | Param of name
  type expr = Bvar of int | Sort of level | Const of name * level list
            | App of expr * expr | Lam of name * expr * expr
            | Pi of name * expr * expr | Let of name * expr * expr * expr
            | Natlit of string | Proj of name * int * expr
  type error_kind = Invalid_input | Unsupported | Resource | Proof_failure
  type error = { kind : error_kind; message : string }
  exception Stop of error
  type budget = { mutable remaining : int }

  let stop kind message = raise (Stop {kind;message})
  let tick st =
    if st.remaining <= 0 then stop Resource "core proof-search fuel exhausted";
    st.remaining <- st.remaining - 1

  let natural s =
    let n = String.length s in
    if n = 0 || (n > 1 && s.[0] = '0') then
      stop Invalid_input "natural numeral must be canonical decimal";
    String.iter (fun c -> if c < '0' || c > '9' then
      stop Invalid_input "natural numeral must be nonnegative decimal") s;
    mk_numeral (num_of_string s)

  let number n =
    if n < 0 then stop Invalid_input "negative de Bruijn index";
    mk_small_numeral n
  let node s xs = list_mk_comb (mk_const(s,[]),xs)
  let rec quote_name = function
    | Anonymous -> `L4Anonymous`
    | Str(n,s) -> node "L4String" [quote_name n;
        mk_list (List.init (String.length s) (fun i -> number (Char.code s.[i])),`:num`)]
    | Num(n,s) -> node "L4Numeric" [quote_name n;natural s]
  let rec quote_level = function
    | Zero -> `L4Zero`
    | Succ u -> node "L4Succ" [quote_level u]
    | Max(u,v) -> node "L4Max" [quote_level u;quote_level v]
    | Imax(u,v) -> node "L4IMax" [quote_level u;quote_level v]
    | Param n -> node "L4Param" [quote_name n]
  let rec quote_expr = function
    | Bvar i -> node "L4BVar" [number i]
    | Sort u -> node "L4Sort" [quote_level u]
    | Const(n,us) -> node "L4Const" [quote_name n;mk_list(List.map quote_level us,`:l4_level`)]
    | App(f,a) -> node "L4App" [quote_expr f;quote_expr a]
    | Lam(n,a,b) -> node "L4Lam" [quote_name n;quote_expr a;quote_expr b]
    | Pi(n,a,b) -> node "L4Pi" [quote_name n;quote_expr a;quote_expr b]
    | Let(n,a,v,b) -> node "L4Let" [quote_name n;quote_expr a;quote_expr v;quote_expr b]
    | Natlit n -> node "L4NatLit" [natural n]
    | Proj(n,i,e) -> node "L4Proj" [quote_name n;number i;quote_expr e]
  let quote_context g = mk_list(List.map quote_expr g,`:l4_expr`)

  let add n d =
    if n > max_int - d then stop Resource "de Bruijn index overflow" else n+d
  let rec lift st d k e =
    tick st;
    match e with
    | Bvar i -> Bvar(if i < k then i else add i d)
    | Sort _ | Const _ | Natlit _ -> e
    | Proj(n,i,e) -> Proj(n,i,lift st d k e)
    | App(f,a) -> App(lift st d k f,lift st d k a)
    | Lam(n,a,b) -> Lam(n,lift st d k a,lift st d (add k 1) b)
    | Pi(n,a,b) -> Pi(n,lift st d k a,lift st d (add k 1) b)
    | Let(n,a,v,b) -> Let(n,lift st d k a,lift st d k v,lift st d (add k 1) b)
  let rec subst st k s e =
    tick st;
    match e with
    | Bvar i -> if i < k then e else if i = k then lift st k 0 s else Bvar(i-1)
    | Sort _ | Const _ | Natlit _ -> e
    | Proj(n,i,e) -> Proj(n,i,subst st k s e)
    | App(f,a) -> App(subst st k s f,subst st k s a)
    | Lam(n,a,b) -> Lam(n,subst st k s a,subst st (add k 1) s b)
    | Pi(n,a,b) -> Pi(n,subst st k s a,subst st (add k 1) s b)
    | Let(n,a,v,b) -> Let(n,subst st k s a,subst st k s v,subst st (add k 1) s b)

  let instantiate_levels st ps us e =
    let substitutions = List.combine ps us in
    let rec level = function
      | Zero -> tick st; Zero
      | Succ u -> tick st; Succ(level u)
      | Max(u,v) -> tick st; Max(level u,level v)
      | Imax(u,v) -> tick st; Imax(level u,level v)
      | Param n -> tick st; (try List.assoc n substitutions with Not_found -> Param n) in
    let rec expr = function
      | Bvar i -> tick st; Bvar i
      | Sort u -> tick st; Sort(level u)
      | Const(n,ls) -> tick st; Const(n,List.map level ls)
      | App(f,a) -> tick st; App(expr f,expr a)
      | Lam(n,a,b) -> tick st; Lam(n,expr a,expr b)
      | Pi(n,a,b) -> tick st; Pi(n,expr a,expr b)
      | Let(n,a,v,b) -> tick st; Let(n,expr a,expr v,expr b)
      | Natlit n -> tick st; Natlit n
      | Proj(n,i,e) -> tick st; Proj(n,i,expr e) in
    expr e

  let compute_object =
    DEPTH_CONV EL_CONV THENC
    REWRITE_CONV [l4_inst;l4_subst;l4_lift;EL;HD;TL;LENGTH] THENC
    NUM_REDUCE_CONV THENC REWRITE_CONV []
  let computation = DEPTH_CONV (fun tm ->
    let head,_ = strip_comb tm in
    if is_const head && mem (fst(dest_const head))
      ["l4_inst";"l4_subst";"l4_lift";"EL";"LENGTH"]
    then CHANGED_CONV compute_object tm else failwith "not an object computation")
  let rules = Array.of_list (CONJUNCTS l4_defeq_RULES)
  let rule st i args premises =
    tick st;
    try
      let th = CONV_RULE computation (SPECL args rules.(i)) in
      match premises with [] -> th | _ -> MP th (end_itlist CONJ premises)
    with Failure s -> stop Proof_failure
      ("HOL rule " ^ string_of_int i ^ ": " ^ s)
  let level_proofs = Hashtbl.create 127
  let level_proof st u v =
    tick st;
    let expected = node "l4_level_equiv" [quote_level u;quote_level v] in
    let th = if u = v then SPEC (quote_level u) l4_level_equiv_refl else
      match Hashtbl.find_opt level_proofs (u,v) with
      | Some th -> th
      | None ->
        let th = prove (expected,
          REWRITE_TAC [l4_level_equiv;l4_eval_level;MAX] THEN
          REPEAT GEN_TAC THEN
          REPEAT (fun goal -> tick st; COND_CASES_TAC goal) THEN
          (fun goal -> tick st; ASM_ARITH_TAC goal)) in
        (* These theorems quantify over every valuation and have no environment
           dependency. Bound retention; failed searches are never cached. *)
        if Hashtbl.length level_proofs >= 256 then Hashtbl.clear level_proofs;
        Hashtbl.replace level_proofs (u,v) th; th in
    if hyp th <> [] || not (aconv (concl th) expected) then
      stop Proof_failure "universe equivalence certificate mismatch";
    th
  let judgment g a b ty = node "l4_defeq"
    [quote_context g;quote_expr a;quote_expr b;quote_expr ty]
  type projection_services = {
    project_infer : expr -> expr * thm;
    project_sort : expr -> level * thm;
    project_check : expr -> expr -> thm;
    project_reduce : expr -> expr * expr * thm;
    project_convert : expr -> expr -> expr -> thm
  }
  module Engine (Logic : sig
    val rule : budget -> int -> term list -> thm list -> thm
    val judgment : expr list -> expr -> expr -> expr -> term
    val constant : budget -> expr list -> name -> level list -> level list -> expr * thm
    val delta : budget -> expr list -> name -> level list -> (expr * expr * thm) option
    val nat_literal : budget -> expr list -> string -> expr * thm
    val nat_literal_step : budget -> expr list -> string -> expr * expr * thm
    val iota : budget -> expr list -> expr ->
      (expr * (expr -> thm -> thm -> thm)) option
    val major : expr -> (expr * (expr -> expr) * expr option) option
    val project_type : budget -> expr list -> name -> int -> expr ->
      projection_services -> expr * thm
    val project_step : budget -> expr list -> name -> int -> expr ->
      projection_services -> (expr * expr * thm) option
    val project_congr : budget -> expr list -> name -> int -> expr -> expr ->
      projection_services -> expr * thm
    val structure_equal : budget -> expr list -> expr -> expr ->
      projection_services -> (expr * thm) option
    val context_empty : thm
    val context_extend : thm
  end) = struct
  let rule = Logic.rule
  let judgment = Logic.judgment
  let guard g a b ty th =
    if hyp th <> [] || not (aconv (concl th) (judgment g a b ty)) then
      stop Proof_failure "internal theorem conclusion or hypotheses mismatch";
    th

  (* Caches are confined to one fuel budget and one instantiated backend.
     Hits retain ordinary theorem objects, not trusted Boolean verdicts. *)
  let cache_budget = ref None
  let inference_cache = Hashtbl.create 127
  let reduction_cache = Hashtbl.create 127
  let equality_cache = Hashtbl.create 127
  let reset_caches st = match !cache_budget with
    | Some old when old == st -> ()
    | _ ->
      Hashtbl.clear inference_cache; Hashtbl.clear reduction_cache;
      Hashtbl.clear equality_cache; cache_budget := Some st

  let rec infer_i st g e =
    tick st; reset_caches st;
    match Hashtbl.find_opt inference_cache (g,e) with
    | Some(ty,th) -> ty,guard g e e ty th
    | None ->
    let ty,th = match e with
    | Bvar i ->
      if i < 0 then stop Invalid_input "negative de Bruijn index";
      if i >= List.length g then stop Proof_failure "bound variable outside context";
      let ty = lift st (add i 1) 0 (List.nth g i) in
      let bound = prove (mk_comb(mk_comb(`(<):num->num->bool`,number i),
          number (List.length g)), CONV_TAC NUM_REDUCE_CONV) in
      ty,rule st 0 [quote_context g;number i] [bound]
    | Sort u ->
      Sort(Succ u),rule st 1 [quote_context g;quote_level u;quote_level u]
        [level_proof st u u]
    | Const(n,us) -> Logic.constant st g n us us
    | Natlit n -> Logic.nat_literal st g n
    | Proj(n,i,e) -> Logic.project_type st g n i e (projection_services st g)
    | Pi(n,a,b) ->
      let u,ha = infer_sort st g a in
      let v,hb = infer_sort st (a::g) b in
      Sort(Imax(u,v)),rule st 4
        [quote_context g;quote_name n;quote_name n;quote_expr a;quote_expr a;
         quote_expr b;quote_expr b;quote_level u;quote_level v] [ha;hb]
    | Lam(n,a,b) ->
      let u,ha = infer_sort st g a in
      let ty,hb = infer_i st (a::g) b in
      Pi(n,a,ty),rule st 3
        [quote_context g;quote_name n;quote_name n;quote_expr a;quote_expr a;
         quote_expr b;quote_expr b;quote_expr ty;quote_level u] [ha;hb]
    | App(f,a) ->
      let n,d,b,hf = pi_judgment st g (infer_i st g f) in
      let ha = check_i st g a d in
      let ty = subst st 0 a b in
      ty,rule st 2
        [quote_context g;quote_expr f;quote_expr f;quote_expr a;quote_expr a;
         quote_name n;quote_expr d;quote_expr b] [hf;ha]
    | Let(n,a,v,b) ->
      let u,ha = infer_sort st g a in
      let hv = check_i st g v a in
      let ty,hb = infer_i st (a::g) b in
      subst st 0 v ty,rule st 11
        [quote_context g;quote_name n;quote_expr a;quote_expr v;
         quote_expr b;quote_expr ty;quote_level u] [ha;hv;hb] in
    let result = ty,guard g e e ty th in
    Hashtbl.add inference_cache (g,e) result; result

  and projection_services st g = {
    project_infer = infer_i st g;
    project_sort = infer_sort st g;
    project_check = check_i st g;
    project_reduce = whnf st g;
    project_convert = (fun a b ty ->
      guard g a b ty (cast st g (equal_i st g a b) ty))
  }

  and infer_sort st g e = sort_judgment st g (infer_i st g e)

  and sort_judgment st g (ty,th) =
    tick st;
    match ty with
    | Sort u -> u,th
    | _ ->
      let ty',uty,eq = whnf st g ty in
      (match ty' with
       | Sort u -> u,convert_with st g ty ty' (uty,eq) th
       | _ -> stop Proof_failure "a sort was required")

  and pi_judgment st g (ty,th) =
    tick st;
    match ty with
    | Pi(n,a,b) -> n,a,b,th
    | _ ->
      let ty',uty,eq = whnf st g ty in
      (match ty' with
       | Pi(n,a,b) -> n,a,b,convert_with st g ty ty' (uty,eq) th
       | _ -> stop Proof_failure "a dependent function type was required")

  and convert_with st g a b eq th =
    let u,heq = sort_judgment st g eq in
    let _,args = strip_comb (concl th) in
    match List.rev args with
    | _::e'::e::_ -> rule st 5
        [quote_context g;quote_expr a;quote_expr b;e;e';quote_level u] [heq;th]
    | _ -> stop Proof_failure "malformed internal judgment"

  and cast st g (ty,th) target =
    tick st;
    if ty = target then th
    else convert_with st g ty target (equal_i st g ty target) th

  and check_i st g e ty =
    let inferred = infer_i st g e in
    guard g e e ty (cast st g inferred ty)

  and sym st g a b ty th =
    rule st 6 [quote_context g;quote_expr a;quote_expr b;quote_expr ty] [th]

  and trans st g a b c ty h h' =
    rule st 7 [quote_context g;quote_expr a;quote_expr b;quote_expr c;quote_expr ty] [h;h']

  and whnf st g e =
    tick st; reset_caches st;
    match Hashtbl.find_opt reduction_cache (g,e) with
    | Some(r,ty,th) -> r,ty,guard g e r ty th
    | None ->
    let r,ty,th = match e with
    | Natlit n -> Logic.nat_literal_step st g n
    | Proj(n,i,major) ->
      (match Logic.project_step st g n i major (projection_services st g) with
       | None -> let ty,h = infer_i st g e in e,ty,h
       | Some(r,ty,h) ->
         let h = guard g e r ty h in
         let r',rty,hr = whnf st g r in
         r',ty,trans st g e r r' ty h (cast st g (rty,hr) ty))
    | Const(n,us) ->
      (match Logic.delta st g n us with
       | None -> let ty,h = infer_i st g e in e,ty,h
       | Some(r,ty,h) ->
         let r',rty,hr = whnf st g r in
         r',ty,trans st g e r r' ty h (cast st g (rty,hr) ty))
    | Let(n,a,v,b) ->
      let u,ha = infer_sort st g a in
      let hv = check_i st g v a in
      let bty,hb = infer_i st (a::g) b in
      let r = subst st 0 v b and ty = subst st 0 v bty in
      let h = rule st 12
        [quote_context g;quote_name n;quote_expr a;quote_expr v;
         quote_expr b;quote_expr bty;quote_level u] [ha;hv;hb] in
      let r',rty,hr = whnf st g r in
      r',ty,trans st g e r r' ty h (cast st g (rty,hr) ty)
    | App(f,a) ->
      let f',fty,hf = whnf st g f in
      let n,d,b,hf = pi_judgment st g (fty,hf) in
      let ha = check_i st g a d in
      let ty = subst st 0 a b in
      let mid = App(f',a) in
      let h = rule st 2
        [quote_context g;quote_expr f;quote_expr f';quote_expr a;quote_expr a;
         quote_name n;quote_expr d;quote_expr b] [hf;ha] in
      (match f' with
       | Lam(m,dom,body) ->
         let bty,hbody = infer_i st (dom::g) body in
         let hv = check_i st g a dom in
         let r = subst st 0 a body and rty = subst st 0 a bty in
         let beta = rule st 8
           [quote_context g;quote_name m;quote_expr dom;quote_expr body;
            quote_expr bty;quote_expr a] [hbody;hv] in
         let h = trans st g e mid r ty h (cast st g (rty,beta) ty) in
         let r',rty,hr = whnf st g r in
         r',ty,trans st g e r r' ty h (cast st g (rty,hr) ty)
       | _ ->
         let mid,h = match Logic.major mid with
           | None -> mid,h
           | Some(major,rebuild,candidate) ->
             let major',_,_ = whnf st g major in
             let replace current proof target =
               let next = rebuild target in
               if next=current then current,proof else
               let hm = cast st g (equal_heads st g current next) ty in
               next,trans st g e current next ty proof hm in
             let mid,h = replace mid h major' in
             (match candidate with
              | None -> mid,h
              | Some ctor ->
                (* The candidate is not a rewrite rule. Typed congruence must
                   establish its equality, including all dependent indices. *)
                try replace mid h ctor with
                | Failure _ | Stop {kind=Proof_failure;_} -> mid,h) in
         (match Logic.iota st g mid with
          | None -> mid,ty,h
          | Some(r,prove_step) ->
            let hl = check_i st g mid ty and hr = check_i st g r ty in
            let step = guard g mid r ty (prove_step ty hl hr) in
            let h = trans st g e mid r ty h step in
            let r',rty,hr = whnf st g r in
            r',ty,trans st g e r r' ty h (cast st g (rty,hr) ty)))
    | _ -> let ty,h = infer_i st g e in e,ty,h in
    let result = r,ty,guard g e r ty th in
    Hashtbl.add reduction_cache (g,e) result; result

  and equal_i st g e e' =
    tick st; reset_caches st;
    match Hashtbl.find_opt equality_cache (g,e,e') with
    | Some(ty,th) -> ty,guard g e e' ty th
    | None ->
    let ty,th =
      if e = e' then infer_i st g e else
      if (match e,e' with Natlit _,Natlit _ -> true | _ -> false) then
        stop Proof_failure "distinct natural literals: no conversion certificate"
      else
      let en,ty,h = whnf st g e in
      let en',ty',h' = whnf st g e' in
      if en <> e || en' <> e' then
        let eqty,heq = equal_i st g en en' in
        let heq = cast st g (eqty,heq) ty in
        let h' = cast st g (ty',h') ty in
        ty,trans st g e en' e' ty
          (trans st g e en en' ty h heq) (sym st g e' en' ty h')
      else if (match e,e' with Sort _,Sort _ -> true | _ -> false) then
        equal_heads st g e e'
      else
        try equal_heads st g e e' with
        | Failure _ | Stop {kind=Proof_failure;_} -> special_equal st g e e' in
    let result = ty,guard g e e' ty th in
    Hashtbl.add equality_cache (g,e,e') result; result

  and equal_heads st g e e' =
    match e,e' with
    | Proj(n,i,a),Proj(m,j,b) when n=m && i=j ->
      Logic.project_congr st g n i a b (projection_services st g)
    | Const(n,us),Const(m,vs) when n=m -> Logic.constant st g n us vs
    | Sort u,Sort v ->
      Sort(Succ u),rule st 1 [quote_context g;quote_level u;quote_level v]
        [level_proof st u v]
    | Lam(n,a,b),Lam(n',a',b') ->
      let u,ha = sort_judgment st g (equal_i st g a a') in
      let ty,hb = equal_i st (a::g) b b' in
      Pi(n,a,ty),rule st 3
        [quote_context g;quote_name n;quote_name n';quote_expr a;quote_expr a';
         quote_expr b;quote_expr b';quote_expr ty;quote_level u] [ha;hb]
    | Pi(n,a,b),Pi(n',a',b') ->
      let u,ha = sort_judgment st g (equal_i st g a a') in
      let v,hb = sort_judgment st (a::g) (equal_i st (a::g) b b') in
      Sort(Imax(u,v)),rule st 4
        [quote_context g;quote_name n;quote_name n';quote_expr a;quote_expr a';
         quote_expr b;quote_expr b';quote_level u;quote_level v] [ha;hb]
    | App(f,a),App(f',a') ->
      let n,d,b,hf = pi_judgment st g (equal_i st g f f') in
      let ha = cast st g (equal_i st g a a') d in
      subst st 0 a b,rule st 2
        [quote_context g;quote_expr f;quote_expr f';quote_expr a;quote_expr a';
         quote_name n;quote_expr d;quote_expr b] [hf;ha]
    | _ -> stop Proof_failure "no structural conversion rule applies"

  and special_equal st g e e' =
    (* Failed proof search is not a refutation. These alternatives still have
       to discharge every typed premise through the HOL inference rules. *)
    try
      let p,h = infer_i st g e in
      let hp = check_i st g p (Sort Zero) in
      let h' = check_i st g e' p in
      p,rule st 10 [quote_context g;quote_expr p;quote_expr e;quote_expr e'] [hp;h;h']
    with Failure _ | Stop {kind=Proof_failure;_} ->
      let structure = try Logic.structure_equal st g e e' (projection_services st g)
        with Failure _ | Stop {kind=Proof_failure;_} -> None in
      match structure with
      | Some result -> result
      | None ->
        match e,e' with
        | Lam _,(Lam _) -> stop Proof_failure "lambda conversion not established"
        | Lam _,_ -> eta_equal st g e e'
        | _,Lam _ ->
          let ty,h = eta_equal st g e' e in ty,sym st g e' e ty h
        | _ -> stop Proof_failure "typed conversion not established"

  and eta_equal st g lam f =
    let n,a,b,hf = pi_judgment st g (infer_i st g f) in
    let ty = Pi(n,a,b) in
    let expanded = Lam(n,a,App(lift st 1 0 f,Bvar 0)) in
    let heta = rule st 9
      [quote_context g;quote_name n;quote_expr a;quote_expr b;quote_expr f] [hf] in
    let heq = cast st g (equal_i st g lam expanded) ty in
    ty,trans st g lam expanded f ty heq heta

  let rec context st = function
    | [] -> Logic.context_empty
    | a::g ->
      tick st;
      let hg = context st g in
      let u,ha = infer_sort st g a in
      MP (SPECL [quote_context g;quote_expr a;quote_level u]
           Logic.context_extend) (CONJ hg ha)

  end

  module Pure = Engine(struct
    let rule = rule
    let judgment = judgment
    let constant _ _ _ _ _ =
      stop Unsupported "constant admission is outside the HOL core slice"
    let delta _ _ _ _ = None
    let nat_literal _ _ _ =
      stop Unsupported "natural literals require a certified Nat environment"
    let nat_literal_step _ _ _ =
      stop Unsupported "natural literal reduction requires a certified Nat environment"
    let iota _ _ _ = None
    let major _ = None
    let project_type _ _ _ _ _ _ =
      stop Unsupported "projections require certified structure metadata"
    let project_step _ _ _ _ _ _ = None
    let project_congr _ _ _ _ _ _ _ =
      stop Unsupported "projection congruence requires certified structure metadata"
    let structure_equal _ _ _ _ _ = None
    let context_empty = CONJUNCT1 l4_context_RULES
    let context_extend = CONJUNCT2 l4_context_RULES
  end)
  include Pure

  let validate st g expressions =
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
      | Proj(n,i,e) ->
        depth d; name (d+1) n;
        if i < 0 then stop Invalid_input "negative projection index";
        expr (d+1) e
      | App(f,a) -> depth d; expr (d+1) f; expr (d+1) a
      | Lam(n,a,b) | Pi(n,a,b) -> depth d; name (d+1) n; expr (d+1) a; expr (d+1) b
      | Let(n,a,v,b) -> depth d; name (d+1) n; expr (d+1) a; expr (d+1) v; expr (d+1) b in
    List.iter (expr 0) g; List.iter (expr 0) expressions

  let run fuel g expressions f =
    let st = {remaining=fuel} in
    try
      validate st g expressions;
      let hg = context st g in
      if hyp hg <> [] || not (aconv (concl hg) (node "l4_context" [quote_context g])) then
        stop Proof_failure "context certificate mismatch";
      Ok(f st)
    with
    | Stop e -> Error e
    | Stack_overflow -> Error {kind=Resource;message="OCaml stack resource exhausted"}
    | Out_of_memory -> Error {kind=Resource;message="memory resource exhausted"}
    | Failure s -> Error {kind=Proof_failure;message="HOL proof construction: " ^ s}
    | Invalid_argument s -> Error {kind=Proof_failure;message="HOL construction argument: " ^ s}

  let infer ?(fuel=100000) g e = run fuel g [e] (fun st -> infer_i st g e)
  let check ?(fuel=100000) g e a = run fuel g [e;a] (fun st -> check_i st g e a)
  let convert ?(fuel=100000) g e e' a = run fuel g [e;e';a] (fun st ->
    ignore(check_i st g e a); ignore(check_i st g e' a);
    guard g e e' a (cast st g (equal_i st g e e') a))
end;;
