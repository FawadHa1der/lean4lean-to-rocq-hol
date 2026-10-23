(* Same test-only factory linked separately to byte-exact old extraction and
   new extraction. Bodies and metadata pass the real admission APIs first. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
let nat = A.nat
let list xs = A.list (fun x -> x) xs
let rec elements = function C.Nil -> [] | C.Cons (x,xs) -> x :: elements xs
let name s = C.NameStr(C.NameAnon,A.string s)
let child n s = C.NameStr(n,A.string s)
let const n us = C.EConst(n,list us)
let app f a = C.EApp(f,a)
let apps = List.fold_left app
let pi a b = C.EPi(C.NameAnon,C.BDefault,a,b)
let lam a b = C.ELam(C.NameAnon,C.BDefault,a,b)
let bvar i = C.EBVar(nat i)
let typ = C.ESort(C.LSucc C.LZero)
let lit s = C.ELit(C.LitString(A.string s))
let nlit n = C.ELit(C.LitNat(A.binary(Z.of_int n)))
let fuel = nat 256
let get label = function
  | C.Accept x -> x
  | C.Reject r -> failwith (label ^ ": reject " ^ A.reject_reason r)
  | C.Decline r -> failwith (label ^ ": decline " ^ A.decline_reason r)
let unit_result = function
  | C.Accept _ -> C.Accept C.Tt | C.Reject r -> C.Reject r | C.Decline r -> C.Decline r
let declaration n ps ty k = {C.decl_hints = C.HintOpaque; decl_name =n;decl_params=list ps;decl_type=ty;
  decl_value=C.None;decl_kind_of=k}
let ind n ps np ty ctors = declaration n ps ty (C.DInductive
  {C.ind_num_params=nat np;ind_num_indices=C.O;ind_all=list[n];ind_ctors=list ctors;
   ind_num_nested=C.O;ind_is_rec=C.False;ind_is_reflexive=C.False;ind_is_unsafe=C.False})
let ctor n owner ps np index fields ty = declaration n ps ty (C.DConstructor
  {C.ctor_induct=owner;ctor_index=nat index;ctor_num_params=nat np;
   ctor_num_fields=nat fields;ctor_is_unsafe=C.False})
let install env ps np spec =
  let ds = elements (get "derive inductive" (C.derive_inductive fuel env (list ps) (nat np) (list[spec]))) in
  let select pred = list (List.filter (fun d -> pred d.C.decl_kind_of) ds) in
  get "checked inductive admission" (C.admit_inductive_extended fuel env
    (select (function C.DInductive _ -> true | _ -> false))
    (select (function C.DConstructor _ -> true | _ -> false))
    (select (function C.DRecursor _ -> true | _ -> false)))
let define env n ps ty body = get "checked safe definition" (C.admit fuel env
  (C.InputDefinition (C.HintOpaque,n,list ps,ty,body,C.InputSafe)))
let nat_env () = install C.Nil [] 0
  {C.spec_decl=ind C.core_nat_name [] 0 typ [C.core_zero_name;C.core_succ_name];
   spec_ctors=list[ctor C.core_zero_name C.core_nat_name [] 0 0 0 C.core_nat;
     ctor C.core_succ_name C.core_nat_name [] 0 1 1 (pi C.core_nat C.core_nat)]}
let u = name "u"
let level = C.LParam u
let list_a a = app (const C.core_list_name [level]) a
let base_env () =
  let n = C.core_list_name in
  let nil = child n "nil" and cons = child n "cons" in
  let univ = C.ESort(C.LSucc level) in
  let env = install (nat_env ()) [u] 1
    {C.spec_decl=ind n [u] 1 (pi univ univ) [nil;cons];
     spec_ctors=list[ctor nil n [u] 1 0 0 (pi univ (list_a (bvar 0)));
       ctor cons n [u] 1 1 2 (pi univ (pi (bvar 0) (pi (list_a (bvar 1)) (list_a (bvar 2)))))]} in
  define env C.core_char_name [] typ C.core_nat
let nil = app (const (child C.core_list_name "nil") [C.LZero]) C.primitive_char
let mk = child C.core_string_name "mk"
let text_env structure cc cs =
  let env = base_env () in
  let env = if structure then install env [] 0
    {C.spec_decl=ind C.core_string_name [] 0 typ [mk];
     spec_ctors=list[ctor mk C.core_string_name [] 0 0 1 (pi C.primitive_list_char C.primitive_string)]}
    else define env C.core_string_name [] typ C.primitive_list_char in
  let env = define env C.core_char_of_nat [] (C.primitive_signature C.PCharOfNat)
    (lam C.core_nat (if cc then nlit 0 else bvar 0)) in
  let value = if cs then nil else bvar 0 in
  define env C.core_string_of_list [] (C.primitive_signature C.PStringOfList)
    (lam C.primitive_list_char (if structure then app (const mk []) value else value))
let checked env value ty = get "positive typing gate" (C.check fuel env C.Nil C.empty_context value ty)
let expansion s = get "UTF8 expansion" (C.core_expand_string (A.string s))
let pair_gate env a b =
  ignore (checked env a C.primitive_string); ignore (checked env b C.primitive_string)
let conversion_comparisons = ref 0
let compare env a b =
  let ordinary = C.defeq fuel env C.Nil C.empty_context a b in
  List.iter (fun hash ->
    let lookup = C.prepare_lookup hash env in
    let indexed = C.prepared_defeq lookup fuel env C.Nil C.empty_context a b in
    if indexed <> ordinary then failwith "FULL prepared conversion differs from own ordinary semantics";
    incr conversion_comparisons) [C.suffix_bitfold8;(fun _ -> C.N0)];
  C.check_defeq fuel env C.Nil C.empty_context a b
let mixed structure cc cs reverse text =
  let env = text_env structure cc cs and a = lit text and b = expansion text in
  pair_gate env a b;
  if reverse then compare env b a else compare env a b
let mixed_normal () =
  let env = text_env false false false in
  let a = lit "A" and b = get "expanded WHNF" (C.whnf fuel env C.Nil C.empty_context (expansion "A")) in
  pair_gate env a b; compare env a b
let distinct structure cc cs =
  let env = text_env structure cc cs and a = lit "A" and b = lit "B" in
  pair_gate env a b; compare env a b
let list_value text =
  let chars = match C.core_utf8 (A.string text) with C.Some cs -> cs | C.None -> failwith "fixture UTF8" in
  C.core_char_list chars
let projection text =
  let env = text_env true false false in
  let value = C.EProj(C.core_string_name,C.O,lit text) in
  ignore (checked env value C.primitive_list_char);
  compare env value (list_value text)
let recursor text =
  let env = text_env true false false in
  let value = apps (const (C.rec_name C.core_string_name) [C.LSucc C.LZero])
    [lam C.primitive_string C.primitive_list_char;lam C.primitive_list_char (bvar 0);lit text] in
  ignore (checked env value C.primitive_list_char);
  compare env value (list_value text)
let eq = name "Eq"
let eq_at u a x y = apps (const eq [u]) [a;x;y]
let eq_env structure = install (text_env structure true false) [u] 2
  {C.spec_decl=ind eq [u] 2
     (pi (C.ESort level) (pi (bvar 0) (pi (bvar 1) (C.ESort C.LZero)))) [child eq "refl"];
   spec_ctors=list[ctor (child eq "refl") eq [u] 2 0 0
     (pi (C.ESort level) (pi (bvar 0) (eq_at level (bvar 1) (bvar 0) (bvar 0))))]}
let refl value = apps (const (child eq "refl") [C.LSucc C.LZero]) [C.primitive_string;value]
let equality = eq_at (C.LSucc C.LZero) C.primitive_string (lit "A") (lit "B")
let proof_gate structure =
  let env = eq_env structure and value = expansion "A" in
  checked env (refl value) (eq_at (C.LSucc C.LZero) C.primitive_string value value)
let theorem structure expanded =
  let env = eq_env structure in
  if expanded then ignore (proof_gate structure);
  unit_result (C.admit fuel env (C.InputTheorem(name "StringEquality",C.Nil,equality,
    refl (if expanded then expansion "A" else lit "A"))))

(* Test-only exact syntax encoding. It does not infer a type or select a verdict. *)
let quote_pair ty body =
  let next = ref 0 and rows = ref [] in
  let rec visit = function
    | C.EBVar n -> emit (C.DBVar n)
    | C.EFVar n -> emit (C.DFVar n)
    | C.EMVar n -> emit (C.DMVar n)
    | C.ESort u -> emit (C.DSort u)
    | C.EConst(n,us) -> emit (C.DConst(n,us))
    | C.ELit l -> emit (C.DLit l)
    | C.EApp(f,a) -> let fi=visit f in let ai=visit a in emit (C.DApp(fi,ai))
    | C.ELam(n,bi,a,b) -> let ai=visit a in let bj=visit b in emit (C.DLam(n,bi,ai,bj))
    | C.EPi(n,bi,a,b) -> let ai=visit a in let bj=visit b in emit (C.DPi(n,bi,ai,bj))
    | C.ELet(n,a,v,b,nd) -> let ai=visit a in let vi=visit v in let bj=visit b in emit (C.DLet(n,ai,vi,bj,nd))
    | C.EProj(n,i,a) -> let ai=visit a in emit (C.DProj(n,i,ai))
    | C.EMData a -> let ai=visit a in emit (C.DMData ai)
  and emit node = incr next; let id=D.positive !next in rows := C.Pair(id,node) :: !rows; id in
  let tr=visit ty in let br=visit body in tr,br,list (List.rev !rows)
let pad env =
  let rec loop i env = if List.length (elements env) >= 64 then env else
    loop (i+1) (define env (child (name "StringParityPadding") (string_of_int i)) [] typ (C.ESort C.LZero)) in
  loop 0 env
let dag_comparisons = ref 0
let dag_theorems () =
  List.iter (fun structure ->
    let env = pad (eq_env structure) in
    if C.use_index fuel env <> C.True then failwith "index positive gate";
    List.iter (fun expanded ->
      let body = refl (if expanded then expansion "A" else lit "A") in
      let n = name "IndexedStringEquality" in
      let expected = C.admit fuel env (C.InputTheorem(n,C.Nil,equality,body)) in
      let tr,br,rows = quote_pair equality body in
      let arena = get "DAG syntax gate" (C.arena_build C.empty_arena rows) in
      let actual_t = get "DAG type root" (C.scope_ref arena.C.arena_scope tr) in
      let actual_b = get "DAG body root" (C.scope_ref arena.C.arena_scope br) in
      if actual_t.C.scope_expr <> equality || actual_b.C.scope_expr <> body then failwith "DAG input changed";
      List.iter (fun budget ->
        List.iter (fun actual ->
          if actual <> expected then failwith "FULL optimized theorem result differs from own ordinary semantics";
          incr dag_comparisons)
          [C.indexed_dag_admit C.DagTheorem (nat budget) fuel env n C.Nil rows tr br;
           C.indexed_admit (fun _ -> C.N0) C.DagTheorem (nat budget) fuel env n C.Nil rows tr br]) [0;1;32])
      [false;true]) [false;true]
let tag = function
  | C.Accept C.Tt -> "accept"
  | C.Reject C.NotDefinitionallyEqual -> "not-defeq"
  | C.Reject C.TypeMismatch -> "type-mismatch"
  | C.Reject r -> failwith ("unexpected reject: " ^ A.reject_reason r)
  | C.Decline r -> failwith ("uncovered decline: " ^ A.decline_reason r)
let () =
  let mode = Sys.argv.(1) in
  let gates = ref 0 in
  let gate run = run (); incr gates in
  gate (fun () -> ignore (nat_env ()));
  gate (fun () -> ignore (base_env ()));
  List.iter (fun (s,c,d) -> gate (fun () -> ignore (text_env s c d)))
    [false,false,false;false,true,false;false,false,true;true,false,false;true,true,false;true,false,true];
  List.iter (fun s -> gate (fun () -> pair_gate (text_env s false false) (lit "A") (expansion "A"))) [false;true];
  List.iter (fun s -> gate (fun () -> ignore (eq_env s))) [false;true];
  List.iter (fun s -> gate (fun () -> ignore (proof_gate s))) [false;true];
  if !gates <> 14 then failwith "gate count";
  let observed = List.map (fun f -> tag (f ()))
    [ (fun () -> mixed false false false false "A"); (fun () -> mixed false false false true "A");
      (fun () -> mixed false true false false "A"); (fun () -> mixed false false true false "A");
      (fun () -> mixed false false false false ""); mixed_normal;
      (fun () -> mixed true false false false "A"); (fun () -> mixed true false false true "A");
      (fun () -> mixed true true false false "A"); (fun () -> mixed true false true false "A");
      (fun () -> projection "A"); (fun () -> projection ""); (fun () -> recursor "A"); (fun () -> recursor "");
      (fun () -> distinct false true false); (fun () -> distinct false false true);
      (fun () -> distinct true true false); (fun () -> distinct true false true);
      (fun () -> theorem false true); (fun () -> theorem true true);
      (fun () -> theorem false false); (fun () -> theorem true false)] in
  let first = match mode with
    | "old" -> List.init 14 (fun _ -> "accept")
    | "new" -> List.init 6 (fun _ -> "not-defeq") @ List.init 8 (fun _ -> "accept")
    | _ -> invalid_arg "test mode old/new" in
  let expected = first @ List.init 4 (fun _ -> "not-defeq") @
    [(if mode="old" then "accept" else "type-mismatch");"accept";"type-mismatch";"type-mismatch"] in
  if observed <> expected then failwith "string semantic observation mismatch";
  List.iteri (fun i value -> print_endline (Yojson.Safe.to_string (`List [`Int i;`String value]))) observed;
  dag_theorems ();
  Printf.eprintf "PASS %s: %d admitted gates; %d observations; %d prepared conversion full comparisons; %d indexed theorem full comparisons\n"
    mode !gates (List.length observed) !conversion_comparisons !dag_comparisons
