(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment.ml";;

let l4_inductive_tests () =
  let open Lean4hol in
  let module Env = Lean4hol_env in
  let count = ref 0 and n = Anonymous in
  let test label ok = if not ok then failwith("inductive regression: "^label); incr count;
    print_endline("inductive check "^string_of_int !count^": "^label) in
  let get label = function Ok x -> x | Error e -> failwith(label^": "^e.message) in
  let decline label = function Error _ -> test label true | Ok _ -> failwith("accepted: "^label) in
  let nm s = Str(Anonymous,s) in
  let child i s = Str(i,s) in
  let cn i = Const(i,[]) in
  let pi a b = Pi(n,a,b) and lam a b = Lam(n,a,b) in
  let app f xs = List.fold_left (fun f a -> App(f,a)) f xs in
  let stmt env g a b ty = node "l4_checked"
    [Env.quote_policy env;Env.quote_env env;quote_context g;quote_expr a;quote_expr b;quote_expr ty] in
  let eq env g a b ty =
    let th = get "iota/conversion" (Env.convert env g a b ty) in
    test "closed conversion" (hyp th=[]);
    test "exact conversion" (aconv (concl th) (stmt env g a b ty)) in
  let chk env g a ty =
    let th = get "typing" (Env.check env g a ty) in
    test "closed typing" (hyp th=[]);
    test "exact typing" (aconv (concl th) (stmt env g a a ty)) in
  let admit env b =
    let env',th = get "inductive admission" (Env.admit_inductive env b) in
    test "closed admission" (hyp th=[]);
    test "exact admission" (aconv (concl th)
      (node "l4_evalid" [Env.quote_policy env';Env.quote_env env']));
    let qi=quote_name b.Env.inductive_name and qu=quote_level b.Env.inductive_level in
    let qcs=mk_list(List.map (fun (c,fs) -> node "L4CtorSpec" [quote_name c;
      mk_list(List.map (function Env.Data a -> node "L4Data" [quote_expr a]
        | Env.Recursive -> `L4Recursive`) fs,`:l4_field`)]) b.Env.constructors,`:l4_ctor_spec`) in
    let qc=mk_list(List.map Env.quote_decl b.Env.claims,`:l4_entry`) in
    let args=[Env.quote_policy env;Env.quote_env env;qi;qu;qcs;qc] in
    let detail=get "admission detail" (Env.inductive_certificate env' b.Env.inductive_name) in
    test "closed admission detail" (hyp detail=[]);
    test "exact admission detail" (aconv (concl detail) (node "l4_inductive_checked" args));
    let meta=MATCH_MP (SPECL args l4_inductive_checked_metadata) detail in
    test "closed metadata authentication" (hyp meta=[]);
    test "exact metadata authentication" (aconv (concl meta)
      (node "l4_metadata_matches" [qc;node "l4_generated" [qi;qu;qcs]])); env' in
  let mk kind name params typ = {Env.kind;name;params;typ;value=None} in
  let level = Succ Zero and u = nm "u" in
  let i = nm "Flag" in
  let off = child i "off" and on = child i "on" and recn = child i "rec" in
  let it = cn i in
  (* Independent expected enum types and RHSs, not the candidate generator. *)
  let motive = pi it (Sort(Param u)) in
  let minor0 = App(Bvar 0,cn off) and minor1 = App(Bvar 1,cn on) in
  let rty = pi motive (pi minor0 (pi minor1 (pi it (App(Bvar 3,Bvar 0))))) in
  let rhs j = lam motive (lam minor0 (lam minor1 (Bvar j))) in
  let rules = [{Env.ctor=off;num_fields=0;rhs=rhs 1};{Env.ctor=on;num_fields=0;rhs=rhs 0}] in
  let info = {Env.num_params=0;num_indices=0;all=[i];ctors=[off;on];num_nested=0;
    is_rec=false;is_reflexive=false;is_unsafe=false} in
  let rinfo = {Env.all=[i];num_params=0;num_indices=0;num_motives=1;num_minors=2;
    rules;k=false;is_unsafe=false} in
  let claims = [mk (Env.Generated(Env.Inductive_role info)) i [] (Sort level);
    mk (Env.Generated(Env.Constructor_role {induct=i;index=0;num_params=0;num_fields=0;is_unsafe=false})) off [] it;
    mk (Env.Generated(Env.Constructor_role {induct=i;index=1;num_params=0;num_fields=0;is_unsafe=false})) on [] it;
    mk (Env.Generated(Env.Recursor_role rinfo)) recn [u] rty] in
  let block = {Env.inductive_name=i;inductive_level=level;constructors=[off,[];on,[]];claims} in
  let env = admit Env.empty block in
  ignore(admit Env.empty {block with Env.claims=List.rev claims});
  chk env [] (cn off) it;
  chk env [] (Const(recn,[level])) (Env.rec_type i block.Env.constructors |> instantiate_levels {remaining=10000} [u] [level]);
  let motive_id = lam it it in
  let elim major = app (Const(recn,[level])) [motive_id;cn on;cn off;major] in
  eq env [] (elim(cn off)) (cn on) it;
  eq env [] (elim(cn on)) (cn off) it;
  eq env [] (elim(elim(cn off))) (cn off) it;
  let dependent_ctx = [App(Bvar 1,cn on);App(Bvar 0,cn off);pi it (Sort level)] in
  eq env dependent_ctx (app (Const(recn,[level])) [Bvar 2;Bvar 1;Bvar 0;cn off])
    (Bvar 1) (App(Bvar 2,cn off));
  eq env [] (App(app (Const(recn,[level]))
    [lam it (pi it it);lam it (cn on);lam it (Bvar 0);cn on],cn off)) (cn off) it;
  decline "distinct enum constructors" (Env.convert env [] (cn off) (cn on) it);
  decline "neutral major does not reduce" (Env.convert env [it] (elim(Bvar 0)) (cn off) it);
  let change_at k f xs = List.mapi (fun j x -> if j=k then f x else x) xs in
  let bad label f = decline label (Env.admit_inductive Env.empty {block with Env.claims=f claims}) in
  let badind label inf = bad label (change_at 0 (fun d -> {d with Env.kind=Env.Generated(Env.Inductive_role inf)})) in
  badind "ind params" {info with Env.num_params=1};
  badind "ind indices" {info with Env.num_indices=1};
  badind "mutual owner list" {info with Env.all=[i;nm "Other"]};
  badind "constructor order" {info with Env.ctors=[on;off]};
  badind "nested metadata" {info with Env.num_nested=1};
  badind "recursive metadata" {info with Env.is_rec=true};
  badind "reflexive metadata" {info with Env.is_reflexive=true};
  badind "unsafe metadata" {info with Env.is_unsafe=true};
  let badrec label inf = bad label (change_at 3 (fun d -> {d with Env.kind=Env.Generated(Env.Recursor_role inf)})) in
  badrec "recursor params" {rinfo with Env.num_params=1};
  badrec "recursor indices" {rinfo with Env.num_indices=1};
  badrec "recursor motives" {rinfo with Env.num_motives=2};
  badrec "recursor minors" {rinfo with Env.num_minors=1};
  badrec "K metadata" {rinfo with Env.k=true};
  badrec "unsafe recursor" {rinfo with Env.is_unsafe=true};
  badrec "arbitrary recursor RHS" {rinfo with Env.rules=change_at 0 (fun r -> {r with Env.rhs=rhs 0}) rules};
  badrec "recursor field count" {rinfo with Env.rules=change_at 0 (fun (r:Env.rec_rule) -> {r with Env.num_fields=1}) rules};
  badrec "missing recursor rule" {rinfo with Env.rules=List.tl rules};
  badrec "recursor rule order is semantic" {rinfo with Env.rules=List.rev rules};
  bad "recursor universe list" (change_at 3 (fun d -> {d with Env.params=[]}));
  bad "wrong constructor type" (change_at 1 (fun d -> {d with Env.typ=Sort level}));
  bad "extra declaration" (fun ds -> ds@[List.hd ds]);
  bad "missing recursor" (fun ds -> List.rev(List.tl(List.rev ds)));
  bad "same-length duplicate claim substitution" (change_at 2 (fun _ -> List.nth claims 1));
  bad "claimed body" (change_at 0 (fun d -> {d with Env.value=Some(Sort Zero)}));
  decline "ordinary admission cannot inject role" (Env.admit Env.empty (List.hd claims));
  decline "unknown admission detail" (Env.inductive_certificate env (nm "Unknown"));
  decline "duplicate environment name" (Env.admit_inductive env block);
  decline "fuel decline" (Env.admit_inductive ~fuel:0 Env.empty block);
  let candidate name lev cs =
    let b={Env.inductive_name=name;inductive_level=lev;constructors=cs;claims=[]} in
    {b with Env.claims=Env.generate {remaining=100000} b} in
  decline "Prop elimination unsupported" (Env.admit_inductive Env.empty (candidate i Zero [off,[];on,[]]));
  decline "undeclared datatype universe" (Env.admit_inductive Env.empty (candidate i (Param u) [off,[]]));
  decline "negative recursive field" (Env.admit_inductive Env.empty
    (candidate i level [off,[Env.Data(pi it (Sort Zero))]]));
  decline "hidden positive occurrence not trusted" (Env.admit_inductive Env.empty
    (candidate i level [off,[Env.Data it]]));
  decline "field universe too large" (Env.admit_inductive Env.empty
    (candidate i level [off,[Env.Data(Sort level)]]));
  decline "open field" (Env.admit_inductive Env.empty (candidate i level [off,[Env.Data(Bvar 0)]]));
  decline "duplicate ctor names" (Env.admit_inductive Env.empty (candidate i level [off,[];off,[]]));
  decline "constructor recursor collision" (Env.admit_inductive Env.empty (candidate i level [recn,[]]));
  let nat = nm "Unary" in
  let z = child nat "zero" and s = child nat "succ" and nr = child nat "rec" in
  let nt = cn nat in
  let nb = candidate nat level [z,[];s,[Env.Recursive]] in
  let nmotive = pi nt (Sort(Param u)) in
  let nminor0 = App(Bvar 0,cn z) in
  let nminor1 = pi nt (pi (App(Bvar 2,Bvar 0)) (App(Bvar 3,App(cn s,Bvar 1)))) in
  let expected_type = pi nmotive (pi nminor0 (pi nminor1 (pi nt (App(Bvar 3,Bvar 0))))) in
  let expected_rhs = lam nmotive (lam nminor0 (lam nminor1 (lam nt
    (app (Bvar 1) [Bvar 0;app (Const(nr,[Param u])) [Bvar 3;Bvar 2;Bvar 1;Bvar 0]])))) in
  let rd = List.nth nb.Env.claims 3 in
  test "independent recursive recursor type" (rd.Env.typ=expected_type);
  (match rd.Env.kind with Env.Generated(Env.Recursor_role r) ->
    test "independent recursive recursor RHS" ((List.nth r.Env.rules 1).Env.rhs=expected_rhs)
   | _ -> failwith "missing recursor role");
  let nenv = admit Env.empty nb in
  let rec rename = function
    | Lam(_,a,b) -> Lam(nm "named",rename a,rename b)
    | Pi(_,a,b) -> Pi(nm "named",rename a,rename b)
    | Let(_,a,v,b) -> Let(nm "named",rename a,rename v,rename b)
    | App(f,a) -> App(rename f,rename a)
    | e -> e in
  let alpha = List.map (fun d ->
    let kind = match d.Env.kind with
      | Env.Generated(Env.Recursor_role r) -> Env.Generated(Env.Recursor_role
          {r with Env.rules=List.map (fun rr -> {rr with Env.rhs=rename rr.Env.rhs}) r.Env.rules})
      | k -> k in
    {d with Env.kind=kind;typ=rename d.Env.typ}) nb.Env.claims in
  let alphaenv = admit Env.empty {nb with Env.claims=alpha} in
  test "alpha names canonical certificate" (aconv (Env.quote_env nenv) (Env.quote_env alphaenv));
  let zero=cn z and succ a=App(cn s,a) in
  let identity a = app (Const(nr,[level]))
    [lam nt nt;zero;lam nt (lam nt (succ(Bvar 0)));a] in
  eq nenv [] (identity zero) zero nt;
  eq nenv [] (identity(succ zero)) (succ zero) nt;
  eq nenv [] (identity(succ(succ zero))) (succ(succ zero)) nt;
  eq nenv [nt] (identity(succ(Bvar 0))) (succ(identity(Bvar 0))) nt;
  let tree=nm "Tree" in
  let leaf=child tree "leaf" and branch=child tree "branch" in
  let tb=candidate tree level [leaf,[Env.Data it];branch,[Env.Recursive;Env.Recursive]] in
  let tenv=admit env tb in
  ignore(admit env {tb with Env.claims=List.rev tb.Env.claims});
  chk tenv [] (app (cn branch) [App(cn leaf,cn off);App(cn leaf,cn on)]) (cn tree);
  let treevalue = app (cn branch) [App(cn leaf,cn on);App(cn leaf,cn off)] in
  let treefold = app (Const(child tree "rec",[level]))
    [lam (cn tree) it;lam it (Bvar 0);
     lam (cn tree) (lam (cn tree) (lam it (lam it (Bvar 1))));treevalue] in
  eq tenv [] treefold (cn on) it;
  let empty=nm "EmptyType" in
  let eenv=admit Env.empty (candidate empty level []) in
  chk eenv [] (cn empty) (Sort level);
  let natname=nm "Nat" and boolname=nm "Bool" in
  let natctors=[child natname "zero",[];child natname "succ",[Env.Recursive]] in
  let boolctors=[child boolname "false",[];child boolname "true",[]] in
  let canonical_nat=candidate natname level natctors in
  let penv=admit Env.empty canonical_nat in
  ignore(admit Env.empty {canonical_nat with Env.claims=List.rev canonical_nat.Env.claims});
  let canonical_bool=candidate boolname level boolctors in
  let penv=admit penv canonical_bool in
  ignore(admit Env.empty {canonical_bool with Env.claims=List.rev canonical_bool.Env.claims});
  chk penv [] (App(cn(child natname "succ"),cn(child natname "zero"))) (cn natname);
  chk penv [] (cn(child boolname "true")) (cn boolname);
  decline "noncanonical Nat universe" (Env.admit_inductive Env.empty (candidate natname (Succ level) natctors));
  decline "empty Nat" (Env.admit_inductive Env.empty (candidate natname level []));
  decline "empty Bool" (Env.admit_inductive Env.empty (candidate boolname level []));
  decline "noncanonical Nat constructor arity" (Env.admit_inductive Env.empty
    (candidate natname level [child natname "zero",[];child natname "succ",[]]));
  decline "noncanonical Bool constructor order" (Env.admit_inductive Env.empty
    (candidate boolname level (List.rev boolctors)));
  decline "protected unrelated constructor" (Env.admit_inductive Env.empty
    (candidate (nm "Impostor") level [child natname "zero",[]]));
  decline "protected unrelated block name" (Env.admit_inductive Env.empty
    (candidate (child natname "add") level []));
  let ax={Env.kind=Env.Axiom;name=natname;params=[];typ=Sort level;value=None} in
  let permitted=get "primitive permission policy" (Env.with_axioms
    [{Env.axiom_name=natname;axiom_params=[];axiom_type=Sort level}]) in
  decline "permission cannot impersonate primitive" (Env.admit permitted ax);
  decline "definition cannot impersonate primitive" (Env.admit Env.empty
    {ax with Env.kind=Env.Definition;name=child natname "add";value=Some(Sort Zero)});
  ignore(admit Env.empty (candidate (nm "Nat.zero") level []));
  let nested=nm "_nested" in
  let nested_type=child nested "T" in
  let nested_block=candidate nested_type level [] in
  let nested_env=admit Env.empty nested_block in
  let nested_detail=get "nested-free admission detail"
    (Env.inductive_certificate nested_env nested_type) in
  let nested_guard=MATCH_MP (SPECL
    [Env.quote_policy Env.empty;Env.quote_env Env.empty;quote_name nested_type;
     quote_level level;`[]:l4_ctor_spec list`;
     mk_list(List.map Env.quote_decl nested_block.Env.claims,`:l4_entry`)]
    l4_inductive_checked_no_nested) nested_detail in
  test "closed nested-reference authentication" (hyp nested_guard=[]);
  test "exact nested-reference authentication" (aconv (concl nested_guard)
    (mk_conj(node "l4_no_nested_block" [quote_name nested_type;`[]:l4_ctor_spec list`],
      node "l4_no_nested_claims"
        [mk_list(List.map Env.quote_decl nested_block.Env.claims,`:l4_entry`)])));
  decline "nested namespace constructor return" (Env.admit_inductive Env.empty
    (candidate nested_type level [child nested_type "mk",[]]));
  let holder=nm "NestedHolder" in
  decline "prior nested namespace field" (Env.admit_inductive nested_env
    (candidate holder level [child holder "mk",[Env.Data(cn nested_type)]]));
  decline "prior nested namespace function field" (Env.admit_inductive nested_env
    (candidate holder level [child holder "mk",[Env.Data(pi (cn nested_type) (cn nested_type))]]));
  ignore(admit Env.empty (candidate (nm "_nested.T") level [nm "PlainCtor",[]]));
  ignore(admit Env.empty (candidate holder level [child nested "CtorNameOnly",[]]));
  let traversal label e expected =
    let tm=mk_eq(node "l4_no_nested_aux" [quote_expr e],if expected then `T` else `F`) in
    let th=prove(tm,REWRITE_TAC [l4_no_nested_aux;l4_nested_name;
      distinctness "l4_name";injectivity "l4_name";distinctness "list";injectivity "list"]
      THEN CONV_TAC NUM_REDUCE_CONV) in
    test label (hyp th=[] && aconv (concl th) tm) in
  traversal "nested root reference" (cn nested) false;
  traversal "nested numeric descendant" (cn(Num(nested,"37"))) false;
  traversal "nested-looking string is distinct" (cn(nm "_nested.T")) true;
  traversal "nonroot nested segment is distinct" (cn(child (nm "Local") "_nested")) true;
  traversal "nested binder name is not a reference" (Pi(nested,Sort level,Bvar 0)) true;
  traversal "nested universe name is not a reference" (Sort(Param nested_type)) true;
  traversal "nested application function" (App(cn nested_type,Sort Zero)) false;
  traversal "nested application argument" (App(cn holder,cn nested_type)) false;
  traversal "nested lambda domain" (lam (cn nested_type) (Bvar 0)) false;
  traversal "nested lambda body" (lam (Sort level) (cn nested_type)) false;
  traversal "nested Pi domain" (pi (cn nested_type) (Sort level)) false;
  traversal "nested Pi body" (pi (Sort level) (cn nested_type)) false;
  traversal "nested let type" (Let(n,cn nested_type,Sort Zero,Bvar 0)) false;
  traversal "nested let value" (Let(n,Sort level,cn nested_type,Bvar 0)) false;
  traversal "nested let body" (Let(n,Sort level,Sort Zero,cn nested_type)) false;
  let permission = MATCH_MP (SPECL [Env.quote_policy tenv;Env.quote_env tenv] l4_evalid_permissions) (Env.certificate tenv) in
  test "inductive permission invariant" (hyp permission=[]);
  test "no new HOL axioms" (axioms()=l4_axioms_before);
  print_endline("HOL_INDUCTIVE_TESTS_PASSED "^string_of_int !count);;

l4_inductive_tests ();;
