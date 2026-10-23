(* Test-only full-result comparisons and hash-call instrumentation. *)
module C = Persistent_tests_native
module M = C.Metadata
module T = C.MetadataCases
let rec nat = function 0 -> C.O | n -> C.S (nat (n-1))
let rec pos n = if n=1 then C.XH else if n mod 2=0 then C.XO(pos(n/2)) else C.XI(pos(n/2))
let number n = if n=0 then C.N0 else C.Npos(pos n)
let name n = C.NameNum(C.NameAnon,number n)
let rec list = function [] -> C.Nil | x::xs -> C.Cons(x,list xs)
let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x::elements xs
let prop = C.ESort C.LZero
let con n = C.EConst(n,C.Nil)
let fail label = failwith label
let get label = function C.Accept x -> x | C.Reject _ -> fail (label^": reject")
  | C.Decline _ -> fail(label^": decline")
let assertions = ref 0 and comparisons = ref 0 and lookup_checks = ref 0
let accepted = ref 0 and rejected = ref 0 and declined = ref 0
let eq label a b = incr assertions; if a<>b then fail label
let check label b = eq label b true
let full label a b = incr comparisons; eq label a b
let env hash s = C.state_environment hash s
let verify_lookup hash s =
  let e = env hash s in
  List.iter (fun n -> incr lookup_checks;
    eq "complete indexed declaration" (C.state_lookup hash s n) (C.find_decl n e))
    (name 99999 :: List.map (fun d -> d.C.decl_name) (elements e))
let step label hash fuel s request =
  let before = env hash s in
  let got = C.state_step hash fuel s request in
  full (label^" full result") (C.project_result hash got) (C.reference_batch fuel before request);
  verify_lookup hash s;
  (match got with C.Accept next -> incr accepted; verify_lookup hash next
    | C.Reject _ -> incr rejected | C.Decline _ -> incr declined);
  got
let success label hash s request = get label (step label hash M.fuel s request)
let ax n ty unsafe = C.BatchOrdinary(C.InputAxiom(n,C.Nil,ty,unsafe))
let quoted kind budget n ps ty body =
  let C.Pair(C.Pair(tr,br),rows) = T.quote_pair ty body in
  C.BatchDag(kind,nat budget,n,ps,rows,tr,br)
let ordinary_of_case c = C.BatchOrdinary(match c.T.case_kind with
  | C.DagDefinition hints -> C.InputDefinition (hints,c.case_name,C.Nil,c.case_type,c.case_body,C.InputSafe)
  | C.DagTheorem -> C.InputTheorem(c.case_name,C.Nil,c.case_type,c.case_body)
  | C.DagOpaque -> C.InputOpaque(c.case_name,C.Nil,c.case_type,c.case_body,C.False))
let rollback label hash s request expected =
  let got = step label hash M.fuel s request in
  let C.Pair(after,status) = C.transaction hash M.fuel s request in
  eq (label^" reason") status expected;
  check (label^" same state") (after == s);
  verify_lookup hash after;
  check (label^" not accepted") (match got with C.Accept _ -> false | _ -> true)

let index_units hash =
  (* Arbitrary records here test the index, not admitted logical validity. *)
  let d n kind = {C.decl_hints = C.HintOpaque; decl_name =n;decl_params=C.Nil;decl_type=prop;
    decl_value=C.None;decl_kind_of=kind} in
  let old = list(List.init 96 (fun i -> d (name i) C.DAssumption)) in
  let calls = ref 0 in
  let counted n = incr calls; hash n in
  let state = C.seed_state counted old in
  eq "seed hashes every old declaration once" !calls 96;
  let newest = d (name 1) (C.DUnsafe C.DAssumption) in
  let prefix = list [newest;d (name 1) C.DOpaque;d (name 1000) C.DAssumption] in
  calls := 0;
  let extended = C.extend_state counted state prefix in
  eq "only additions hashed" !calls 3;
  eq "old state immutable" (env hash state) old;
  eq "newest duplicate shadows old and same-batch duplicate"
    (C.state_lookup hash extended (name 1)) (C.Some newest);
  verify_lookup hash extended;
  verify_lookup hash state;
  calls := 0;
  let unchanged = C.extend_state counted extended C.Nil in
  eq "empty commit no hashes" !calls 0;
  check "empty commit shares old index" (unchanged.C.state_index == extended.C.state_index)

let checked_padding hash =
  List.fold_left (fun s d -> success "padding admission" hash s
    (C.BatchOrdinary(C.InputAxiom(d.C.decl_name,d.decl_params,d.decl_type,C.False))))
    (C.seed_state hash C.Nil) (List.rev (elements(get "padded fixture" M.padded_env)))

let incremental_hash_work hash =
  let seen=ref [] in
  let counted n = seen:=n::!seen; hash n in
  let s=C.seed_state counted (get "checked hash-work padding" M.padded_env) in
  let n=name 7000 in
  seen:=[];
  let next=get "ordinary hash-work positive" (C.state_step counted M.fuel s (ax n prop C.False)) in
  eq "ordinary commit hashes new declaration only" !seen [n];
  seen:=[];
  eq "ordinary duplicate fails" (C.project_result counted
    (C.state_step counted M.fuel next (ax n prop C.False))) (C.Reject C.DuplicateDeclaration);
  eq "ordinary rejection hashes nothing" !seen [];
  seen:=[];
  eq "unsupported decline exact" (C.project_result counted
    (C.state_step counted M.fuel next (C.BatchOrdinary C.InputUnsupported)))
    (C.Decline C.UnsupportedDeclaration);
  eq "decline hashes nothing" !seen [];
  let n=name 7001 in
  seen:=[];
  let got=C.state_step counted M.fuel next (quoted (C.DagDefinition C.HintOpaque) 32 n C.Nil M.type0 prop) in
  ignore(get "DAG hash-work positive" got);
  let names= !seen in
  check "DAG performed index insertion" (names<>[]);
  check "DAG did not rehash any old declarations" (List.for_all ((=) n) names);
  verify_lookup hash (get "hash-work next" got)
let build_metadata hash =
  let s = checked_padding hash in
  eq "padding exact ordering" (env hash s) (get "padding" M.padded_env);
  let induct label ps np specs s =
    let request = get (label^" derive checked inputs") (C.generated_batch (env hash s) ps (nat np) (list specs)) in
    success label hash s request in
  let s = induct "Nat incremental" C.Nil 0 [M.nat_spec] s in
  eq "Nat batch ordering" (env hash s) (get "Nat" M.nat_env);
  eq "Nat cached readiness" (C.lookup_nat_ready (C.state_lookup hash s)) C.True;
  let s = induct "Eq incremental" (list[M.u_name]) 2 [M.eq_spec] s in
  eq "Eq batch ordering" (env hash s) (get "Eq" M.eq_env);
  let s = induct "Box incremental" C.Nil 0 [M.box_spec] s in
  let s = induct "dependent structure incremental" C.Nil 0 [M.dep_spec] s in
  let structure = s in
  let s = List.fold_left (fun s k -> let d=C.canonical_quotient k in
    success "quotient incremental" hash s
      (C.BatchQuotient(d.C.decl_name,d.decl_params,d.decl_type,k))) s
    [C.QType;C.QCtor;C.QLift;C.QInd] in
  eq "full checked metadata environment" (env hash s) (get "base" M.base_env);
  s,structure

let metadata hash =
  let base,structure = build_metadata hash in
  let add_case = List.hd(elements T.cases) in
  let added = success "install authenticated primitive incrementally" hash base
    (quoted add_case.case_kind 128 add_case.case_name C.Nil add_case.case_type add_case.case_body) in
  eq "primitive updated full record" (env hash added) (get "add fixture" M.with_add);
  eq "primitive tag authentication" (C.primitive_authenticated M.fuel (env hash added) C.PNatAdd) (C.Accept C.Tt);
  List.iteri (fun i c ->
    let source = get "case env" c.T.case_env in
    let s = if source=env hash base then base else if source=env hash added then added
      else C.seed_state hash source in
    eq "metadata forced indexed size" (C.use_index M.fuel (env hash s)) C.True;
    List.iter (fun budget ->
      let r = step (Printf.sprintf "metadata %d budget%d" i budget) hash M.fuel s
        (quoted c.case_kind budget c.case_name C.Nil c.case_type c.case_body) in
      let projected=C.project_result hash r in
      full "metadata vs ordinary admission" projected (C.reference_batch M.fuel source (ordinary_of_case c));
      if c.case_positive=C.True then eq "nonvacuous positive" projected (T.expected source c)
      else check "negative control" (match r with C.Accept _ -> false | _ -> true)
    ) [0;1;128]) (elements T.cases);
  List.iter (fun (C.Pair(C.Pair(_,term),expected)) ->
    full "incremental metadata reduction vs linear"
      (C.prepared_whnf (C.state_lookup hash base) M.fuel (env hash base) C.Nil C.empty_context term)
      (C.whnf M.fuel (env hash base) C.Nil C.empty_context term);
    eq "metadata expected reduction"
      (C.prepared_whnf (C.state_lookup hash base) M.fuel (env hash base) C.Nil C.empty_context term)
      (C.Accept expected)) (elements T.reductions);
  eq "incremental primitive reduction"
    (C.prepared_whnf (C.state_lookup hash added) M.fuel (env hash added) C.Nil C.empty_context M.add_value)
    (C.Accept (C.ELit(C.LitNat(number 2))));
  let padded = checked_padding hash in
  let generated = get "derive Nat for mutation" (C.generated_batch (env hash padded) C.Nil C.O (list[M.nat_spec])) in
  (match generated with
  | C.BatchInductive(types,ctors,recs) ->
    rollback "forged constructor metadata" hash padded
      (C.BatchInductive(types,list(List.map M.corrupt_fields(elements ctors)),recs))
      (C.Reject C.MalformedDeclaration);
    rollback "forged recursor metadata" hash padded
      (C.BatchInductive(types,ctors,list(List.map M.corrupt_rule(elements recs))))
      (C.Reject C.MalformedDeclaration);
    rollback "missing recursor metadata" hash padded
      (C.BatchInductive(types,ctors,C.Nil)) (C.Reject C.MalformedDeclaration)
  | _ -> fail "wrong generated batch");
  let d = C.canonical_quotient C.QType in
  rollback "forged quotient type" hash structure
    (C.BatchQuotient(d.C.decl_name,d.decl_params,M.type0,C.QType)) (C.Reject C.MalformedDeclaration);
  rollback "quotient missing prerequisite" hash padded
    (C.BatchQuotient(d.C.decl_name,d.decl_params,d.decl_type,C.QType)) (C.Reject C.UnknownConstant);
  let quotient k = let d=C.canonical_quotient k in
    C.BatchQuotient(d.C.decl_name,d.decl_params,d.decl_type,k) in
  let ordinary_quotient k = let d=C.canonical_quotient k in
    C.BatchOrdinary(C.InputAxiom(d.C.decl_name,d.decl_params,d.decl_type,C.False)) in
  let axiom_type = success "ordinary Quot header is well typed" hash structure
    (ordinary_quotient C.QType) in
  rollback "ordinary Quot cannot authorize constructor" hash axiom_type
    (quotient C.QCtor) (C.Reject C.MalformedDeclaration);
  rollback "ordinary Quot cannot authorize lift" hash axiom_type
    (quotient C.QLift) (C.Reject C.MalformedDeclaration);
  let genuine_type = success "genuine Quot dependency gate" hash structure
    (quotient C.QType) in
  ignore(success "lift requires Quot but not Quot.mk" hash genuine_type (quotient C.QLift));
  let axiom_ctor = success "ordinary Quot.mk header is well typed" hash genuine_type
    (ordinary_quotient C.QCtor) in
  rollback "ordinary Quot.mk cannot authorize induction" hash axiom_ctor
    (quotient C.QInd) (C.Reject C.MalformedDeclaration)

let safety hash =
  let s = checked_padding hash in
  let u=name 3000 in
  let s = success "unsafe axiom" hash s (ax u prop C.True) in
  eq "cached unsafe marker" (C.lookup_get_constant (C.state_lookup hash s) C.Nil u C.Nil)
    (C.Reject C.MalformedDeclaration);
  rollback "safe use of unsafe axiom" hash s (ax (name 3001) (con u) C.False)
    (C.Reject C.MalformedDeclaration);
  List.iter (fun mode ->
    let p=name 3100 and q=name 3101 in
    let definition n body=C.InputDefinition (C.HintOpaque,n,C.Nil,prop,body,mode) in
    let good=C.BatchMutual(list[definition p (con q);definition q (con p)]) in
    let next=success "checked mutual recursive batch" hash s good in
    eq "mutual appended two only" (List.length(elements(env hash next)))
      (2+List.length(elements(env hash s)));
    List.iter (fun n -> match C.state_lookup hash next n with
      | C.Some d -> eq "mutual committed marker not placeholder" d.C.decl_kind_of
          (match mode with C.InputUnsafe -> C.DUnsafe C.DDefinition | _ -> C.DPartial)
      | C.None -> fail "missing mutual addition") [p;q];
    rollback "mutual malformed second value atomic" hash s
      (C.BatchMutual(list[definition p (con q);definition q (C.EBVar C.O)]))
      (C.Reject C.MalformedDeclaration);
    rollback "mutual duplicate names" hash s
      (C.BatchMutual(list[definition p (con q);definition p (con p)]))
      (C.Reject C.DuplicateDeclaration)
  ) [C.InputUnsafe;C.InputPartial];
  rollback "empty mutual malformed" hash s (C.BatchMutual C.Nil) (C.Reject C.MalformedDeclaration);
  rollback "unsupported rollback" hash s (C.BatchOrdinary C.InputUnsupported)
    (C.Decline C.UnsupportedDeclaration);
  ignore(success "post rollback positive" hash s (ax (name 3900) prop C.False));
  let ind=M.seed_ind (name 3950) C.Nil M.type0 C.O C.Nil in
  let ind = match ind.C.decl_kind_of with
    | C.DInductive info -> {ind with C.decl_kind_of=C.DInductive {info with C.ind_is_unsafe=C.True}}
    | _ -> fail "inductive seed" in
  let request=get "derive unsafe Empty" (C.generated_batch (env hash s) C.Nil C.O
    (list[{C.spec_decl=ind;spec_ctors=C.Nil}])) in
  let next=success "unsafe Empty batch" hash s request in
  eq "unsafe type marker retained" (C.lookup_get_constant (C.state_lookup hash next) C.Nil (name 3950) C.Nil)
    (C.Reject C.MalformedDeclaration)

let matrix hash =
  let p=name 6000 and h=name 6001 in
  let s0=C.seed_state hash C.Nil in
  let s1=success "matrix P" hash s0 (ax p prop C.False) in
  let s2=success "matrix h" hash s1 (ax h (con p) C.False) in
  let padded=checked_padding hash in
  let env64=env hash padded in
  let env63=match env64 with C.Cons(_,rest) -> rest | _ -> fail "padding" in
  List.iter (fun source -> let s=C.seed_state hash source in
    List.iter (fun f -> let fuel=nat f in
      List.iter (fun budget ->
        List.iter (fun kind ->
          let good=quoted kind budget (name 6100) C.Nil (con p) (con h) in
          let requests=[good;
            quoted kind budget p C.Nil (con p) (con h);
            quoted kind budget (name 6100) (list[p;p]) prop prop;
            quoted kind budget (name 6100) C.Nil (C.EBVar C.O) (C.EMVar p);
            C.BatchDag(kind,nat budget,p,C.Nil,C.Nil,C.XH,C.XH);
            C.BatchDag(kind,nat budget,p,C.Nil,list[C.Pair(C.XH,C.DSort C.LZero)],C.XH,C.XO C.XH);
            C.BatchDag(kind,nat budget,p,C.Nil,list[C.Pair(C.XH,C.DSort C.LZero);C.Pair(C.XH,C.DSort C.LZero)],C.XH,C.XH)] in
          List.iter (fun r -> ignore(step "boundary matrix" hash fuel s r)) requests
        ) [(C.DagDefinition C.HintOpaque);C.DagTheorem;C.DagOpaque]
      ) [0;1;32];
      List.iter (fun requests -> full "complete streaming result"
        (C.project_result hash(C.state_stream hash fuel s (list requests)))
        (C.reference_stream fuel source (list requests)))
        [[];[ax p prop C.False;ax h (con p) C.False];
         [ax p prop C.False;ax p prop C.False;ax h (con p) C.False];
         [C.BatchOrdinary C.InputUnsupported;ax h prop C.False]]
    ) [0;1;2;16]
  ) [C.Nil;env hash s2;env63;env64];
  let s=C.seed_state hash env63 in
  eq "63 gate" (C.use_index M.fuel(env hash s)) C.False;
  let s=success "cross guard boundary" hash s (ax p prop C.False) in
  eq "64 gate" (C.use_index M.fuel(env hash s)) C.True;
  let s=success "above guard admission" hash s (ax h (con p) C.False) in
  ignore(success "above guard DAG uses newly admitted type and proof" hash s
    (quoted C.DagTheorem 32 (name 6200) C.Nil (con p) (con h)))

let () =
  List.iter (fun (label,hash) ->
    Printf.printf "hash=%s\n%!" label;
    index_units hash; incremental_hash_work hash; matrix hash; metadata hash; safety hash
  ) ["bitfold8",C.suffix_bitfold8;"all-colliding",(fun _ -> C.N0)];
  Printf.printf "assertions=%d full_result_comparisons=%d lookup_comparisons=%d step_accept=%d step_reject=%d step_decline=%d\n%!"
    !assertions !comparisons !lookup_checks !accepted !rejected !declined
