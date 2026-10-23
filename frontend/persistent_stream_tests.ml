(* Checked incremental String/nested environments. All expectations are tests. *)
module C = Persistent_tests_native
module M = C.Metadata
module T = C.MetadataCases
module NR = C.NestedRegression
let rec nat = function 0 -> C.O | i -> C.S(nat(i-1))
let rec pos i = if i=1 then C.XH else if i mod 2=0 then C.XO(pos(i/2)) else C.XI(pos(i/2))
let num i = if i=0 then C.N0 else C.Npos(pos i)
let rec list = function [] -> C.Nil | x::xs -> C.Cons(x,list xs)
let rec elements = function C.Nil -> [] | C.Cons(x,xs) -> x::elements xs
let ascii c = let i=Char.code c in
  let bit n=if i land (1 lsl n)=0 then C.False else C.True in
  C.Ascii(bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let str s = let v=ref C.EmptyString in for i=String.length s-1 downto 0 do
  v:=C.String(ascii s.[i],!v) done; !v
let name s=C.NameStr(C.NameAnon,str s)
let cbool b=if b then C.True else C.False
let get label = function C.Accept x -> x | C.Reject _ -> failwith(label^": reject")
  | C.Decline _ -> failwith(label^": decline")
let prop=C.ESort C.LZero
let typ=C.ESort(C.LSucc C.LZero)
let lam a b=C.ELam(C.NameAnon,C.BDefault,a,b)
let con n us=C.EConst(n,list us)
let lit s=C.ELit(C.LitString(str s))
let nlit i=C.ELit(C.LitNat(num i))
let bvar i=C.EBVar(nat i)
let apps=List.fold_left(fun f a->C.EApp(f,a))
let fuel=nat 256
let assertions=ref 0 and full_results=ref 0 and checked_steps=ref 0
let lookup_checks=ref 0 and rollbacks=ref 0 and observations=ref 0
let eq label a b=incr assertions; if a<>b then failwith label
let full label a b=incr full_results; eq label a b
let env hash s=C.state_environment hash s
let verify hash s =
  List.iter(fun n->incr lookup_checks;
    eq "whole declaration lookup" (C.state_lookup hash s n) (C.find_decl n (env hash s)))
    (name "never-declared" :: List.map(fun d->d.C.decl_name)(elements(env hash s)))
let request kind budget n ps ty value =
  let C.Pair(C.Pair(tr,br),rows)=T.quote_pair ty value in
  C.BatchDag(kind,nat budget,n,list ps,rows,tr,br)
let step hash s input =
  incr checked_steps;
  let actual=C.state_step hash fuel s input in
  full "stream step equals NEW ordinary/reference batch"
    (C.project_result hash actual) (C.reference_batch fuel (env hash s) input);
  (match actual with C.Accept next->verify hash next|_->verify hash s);
  actual
let install hash s ps np spec =
  let input=get "derive untrusted inductive input"
    (C.generated_batch (env hash s) (list ps) (nat np) (list[spec])) in
  get "real inductive admission" (step hash s input)
let define hash s n ps ty value =
  get "real DAG definition admission" (step hash s (request (C.DagDefinition C.HintOpaque) 128 n ps ty value))
let padded hash =
  let s=C.seed_state hash C.Nil in
  List.fold_left(fun s d->get "checked padding" (step hash s
    (C.BatchOrdinary(C.InputAxiom(d.C.decl_name,d.decl_params,d.decl_type,C.False)))))
    s (List.rev(elements(get "padding inputs" M.padded_env)))
let base hash () =
  let s=install hash (padded hash) [] 0 M.nat_spec in
  let s=install hash s [C.sp_u] 1 C.sp_list_spec in
  define hash s C.core_char_name [] typ C.core_nat
let text_state hash structure cc cs =
  let s=base hash () in
  let s=if structure then install hash s [] 0 C.sp_string_spec
    else define hash s C.core_string_name [] typ C.primitive_list_char in
  let s=define hash s C.core_char_of_nat [] (C.primitive_signature C.PCharOfNat)
    (lam C.core_nat (if cc then nlit 0 else bvar 0)) in
  let value=if cs then C.sp_nil else bvar 0 in
  let s=define hash s C.core_string_of_list [] (C.primitive_signature C.PStringOfList)
    (lam C.primitive_list_char (if structure then C.EApp(con (C.NameStr(C.core_string_name,str "mk")) [],value) else value)) in
  eq "persistent String state uses index" (C.use_index fuel (env hash s)) C.True;
  s
let unit_result = function C.Accept _->C.Accept C.Tt|C.Reject r->C.Reject r|C.Decline r->C.Decline r
let check hash s value ty = get "positive typing gate"
  (C.check fuel (env hash s) C.Nil C.empty_context value ty)
let expand s=get "UTF8 expansion" (C.core_expand_string(str s))
let pair hash s a b=ignore(check hash s a C.primitive_string);ignore(check hash s b C.primitive_string)
let compare hash s a b =
  let actual=C.prepared_defeq (C.state_lookup hash s) fuel (env hash s) C.Nil C.empty_context a b in
  full "prepared conversion equals NEW ordinary"
    actual (C.defeq fuel (env hash s) C.Nil C.empty_context a b);
  let checked=match actual with
    | C.Accept C.True -> C.Accept C.Tt | C.Accept C.False -> C.Reject C.NotDefinitionallyEqual
    | C.Reject r->C.Reject r|C.Decline r->C.Decline r in
  full "complete check_defeq result" checked (C.check_defeq fuel (env hash s) C.Nil C.empty_context a b);
  checked
let run_string hash label =
  let table=Hashtbl.create 8 in
  let text a b c=match Hashtbl.find_opt table (a,b,c) with
    | Some s->s|None->let s=text_state hash a b c in Hashtbl.add table (a,b,c) s;s in
  let eq_states=Hashtbl.create 2 in
  let equality_state structure=match Hashtbl.find_opt eq_states structure with
    | Some s->s|None->let s=install hash (text structure true false) [C.sp_u] 2 C.sp_eq_spec in
      Hashtbl.add eq_states structure s;s in
  let gate_count=ref 0 in
  let gate f=f();incr gate_count in
  gate(fun()->ignore(install hash (padded hash) [] 0 M.nat_spec));
  gate(fun()->ignore(base hash ()));
  List.iter(fun(a,b,c)->gate(fun()->ignore(text a b c)))
    [false,false,false;false,true,false;false,false,true;true,false,false;true,true,false;true,false,true];
  List.iter(fun structure->gate(fun()->pair hash (text structure false false) (lit "A") (expand "A"))) [false;true];
  List.iter(fun structure->gate(fun()->ignore(equality_state structure))) [false;true];
  List.iter(fun structure->gate(fun()->let s=equality_state structure and e=expand "A" in
    let ty=apps(con C.sp_eq_name [C.LSucc C.LZero]) [C.primitive_string;e;e] in
    ignore(check hash s (C.sp_refl e) ty))) [false;true];
  eq "14 persistent admitted gates" !gate_count 14;
  let mixed structure cc cs reverse txt=
    let s=text structure cc cs and a=lit txt and b=expand txt in
    pair hash s a b;if reverse then compare hash s b a else compare hash s a b in
  let normal ()=let s=text false false false in
    let a=lit "A" and b=get "WHNF expansion" (C.whnf fuel (env hash s) C.Nil C.empty_context (expand "A")) in
    pair hash s a b;compare hash s a b in
  let chars txt=match C.core_utf8(str txt) with C.Some cs->C.core_char_list cs|C.None->failwith "UTF8 fixture" in
  let proj txt=let s=text true false false in
    let value=C.EProj(C.core_string_name,C.O,lit txt) in
    ignore(check hash s value C.primitive_list_char);compare hash s value (chars txt) in
  let recursor txt=let s=text true false false in
    let value=apps(con (C.rec_name C.core_string_name) [C.LSucc C.LZero])
      [lam C.primitive_string C.primitive_list_char;lam C.primitive_list_char (bvar 0);lit txt] in
    ignore(check hash s value C.primitive_list_char);compare hash s value (chars txt) in
  let distinct structure cc cs=let s=text structure cc cs in
    pair hash s (lit "A") (lit "B");compare hash s (lit "A") (lit "B") in
  let theorem structure expanded=
    let s=equality_state structure in
    let body=C.sp_refl(if expanded then expand "A" else lit "A") in
    let n=name "PersistentStringEquality" in
    let expected=C.admit fuel (env hash s) (C.InputTheorem(n,C.Nil,C.sp_literal_equality,body)) in
    let statuses=List.map(fun budget->
      let input=request C.DagTheorem budget n [] C.sp_literal_equality body in
      let actual=step hash s input in
      full "persistent String theorem vs NEW ordinary admit" (C.project_result hash actual) expected;
      (match actual with
      | C.Accept next->
        eq "accepted theorem now indexed" (C.state_lookup hash next n) (C.find_decl n (env hash next));
        let use=get "post String theorem use" (step hash next
          (request C.DagTheorem 32 (name "PersistentStringEqualityUse") [] C.sp_literal_equality (con n []))) in
        verify hash use
      | C.Reject r->
        let C.Pair(after,status)=C.transaction hash fuel s input in
        eq "String rollback reason" status (C.Reject r);eq "String rollback same pointer" (after==s) true;
        incr rollbacks;
        ignore(define hash after (name "AfterStringRejection") [] typ prop)
      | C.Decline _->failwith "String theorem unexpectedly declined");
      unit_result actual) [0;1;32] in
    List.iter(fun actual->eq "budget independent observation" actual (List.hd statuses)) statuses;
    List.hd statuses in
  let actual=[mixed false false false false "A";mixed false false false true "A";
    mixed false true false false "A";mixed false false true false "A";
    mixed false false false false "";normal();mixed true false false false "A";
    mixed true false false true "A";mixed true true false false "A";
    mixed true false true false "A";proj "A";proj "";recursor "A";recursor "";
    distinct false true false;distinct false false true;distinct true true false;distinct true false true;
    theorem false true;theorem true true;theorem false false;theorem true false] in
  let expected=List.init 6(fun _->C.Reject C.NotDefinitionallyEqual) @
    List.init 8(fun _->C.Accept C.Tt) @ List.init 4(fun _->C.Reject C.NotDefinitionallyEqual) @
    [C.Reject C.TypeMismatch;C.Accept C.Tt;C.Reject C.TypeMismatch;C.Reject C.TypeMismatch] in
  eq "all repaired observations" actual expected;
  eq "matches independently checked fixture observations" actual (elements(C.sp_observations C.Tt));
  eq "fixture positive gates" (elements(C.sp_gate_results C.Tt)) (List.init 14(fun _->C.True));
  List.iter(fun i->eq "historically changed observation remains rejected"
    (List.nth actual i) (if i=18 then C.Reject C.TypeMismatch else C.Reject C.NotDefinitionallyEqual)) [0;1;2;3;4;5;18];
  observations:= !observations+List.length actual;
  List.iteri(fun i r->let tag=match r with C.Accept _->"accept"|C.Reject C.NotDefinitionallyEqual->"not-defeq"
    |C.Reject C.TypeMismatch->"type-mismatch"|_->"unexpected" in
    Printf.printf "string hash=%s index=%d result=%s\n%!" label i tag) actual

let nested hash label =
  List.iter(fun padded_env->
    let initial=if padded_env then padded hash else C.seed_state hash C.Nil in
    let box=get "nested Box baseline" (step hash initial C.nested_box_batch) in
    let tree=get "true nested baseline" (step hash box C.nested_tree_batch) in
    if not padded_env then eq "literal independent full nested environment"
      (C.Accept(env hash tree)) NR.tree_admission;
    let transformed=get "true nested transformation" (C.eliminate_nested fuel (env hash box) C.Nil C.O
      (list[{C.spec_decl=NR.tree_decl(C.S C.O);spec_ctors=list[NR.leaf_ctor;NR.node_ctor]}])) in
    eq "exactly one real auxiliary" transformed.C.nested_aux_count (C.S C.O);
    eq "nested map actually contains Box Tree" (List.map(fun(C.Pair(e,_))->e)(elements transformed.nested_mapping))
      [NR.box_at NR.tree_ty];
    eq "fresh auxiliary type not committed" (C.state_lookup hash tree NR.aux) C.None;
    eq "fresh auxiliary recursor not committed" (C.state_lookup hash tree(C.rec_name NR.aux)) C.None;
    (match C.state_lookup hash tree NR.nested_rec with C.Some d->
      eq "restored recursor cached whole" (C.Some d) (C.find_decl NR.nested_rec (env hash tree))
      |_->failwith "missing restored rec_1");
    List.iter(fun input->
      eq "nested mutation rejects exact reason" (C.project_result hash(step hash box input))
        (C.Reject C.MalformedDeclaration);
      let C.Pair(after,status)=C.transaction hash fuel box input in
      eq "nested transaction rejected" status (C.Reject C.MalformedDeclaration);
      eq "nested rollback identical state" (after==box) true;
      eq "no partial tree leaked" (C.state_lookup hash after NR.tree) C.None;
      incr rollbacks;
      full "good tree still accepted after failed batch" (C.project_result hash(step hash after C.nested_tree_batch))
        (C.Accept(env hash tree))) (elements C.nested_mutations);
    Printf.printf "nested hash=%s padded=%b accepted=true aux=1 mutations=5 rollback=true\n%!" label padded_env
  ) [false;true]
let ()=
  List.iter(fun(label,hash)->run_string hash label;nested hash label)
    ["bitfold8",C.suffix_bitfold8;"constant-collision",(fun _->C.N0)];
  Printf.printf "PASS persistent_stream: assertions=%d full_results=%d checked_steps=%d lookups=%d observations=%d changed_per_hash=7 nested_positives=4 rollbacks=%d\n%!"
    !assertions !full_results !checked_steps !lookup_checks !observations !rollbacks
