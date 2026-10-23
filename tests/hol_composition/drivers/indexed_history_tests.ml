(* Independent test-only Wire decoder. It does not use Hol_input or Hol_check
   syntax conversion to construct the expected raw history. *)
module Compose_history = struct
  module W = Wire
  module H = Lean4hol
  module A = Lean4hol_env
  module C = Lean4hol_input_certificate
  module R = Lean4hol_raw_ctor
  module Q = Lean4hol_quotient_model
  let count = ref 0
  let ensure label b =
    if not b then failwith ("history assertion: " ^ label);
    incr count; Printf.printf "history check %d: %s\n%!" !count label
  let integer n =
    if Z.sign n < 0 || not (Z.fits_int n) then failwith "test integer out of range";
    Z.to_int n
  let rec name = function
    | W.Anonymous -> H.Anonymous
    | W.Str(n,s) -> H.Str(name n,s)
    | W.Num(n,i) -> H.Num(name n,Z.to_string i)
  let rec level = function
    | W.Zero -> H.Zero | W.Succ u -> H.Succ(level u)
    | W.Max(u,v) -> H.Max(level u,level v)
    | W.IMax(u,v) -> H.Imax(level u,level v)
    | W.Param n -> H.Param(name n)
  let rec expr = function
    | W.BVar i -> H.Bvar(integer i)
    | W.Sort u -> H.Sort(level u)
    | W.Const(n,us) -> H.Const(name n,List.map level us)
    | W.App(f,a) -> H.App(expr f,expr a)
    | W.Lam(n,a,b,_) -> H.Lam(name n,expr a,expr b)
    | W.Pi(n,a,b,_) -> H.Pi(name n,expr a,expr b)
    | W.Let(n,a,v,b,_) -> H.Let(name n,expr a,expr v,expr b)
    | W.Proj(n,i,e) -> H.Proj(name n,integer i,expr e)
    | W.NatLit i -> H.Natlit(Z.to_string i)
    | W.StringLit s -> H.Strlit s
    | W.MData e -> expr e
  let declaration kind (h:W.constant) value : A.declaration =
    {A.kind;name=name h.W.name;params=List.map name h.W.params;
     typ=expr h.W.typ;value=Option.map expr value}
  let rule (r:W.rule) : A.rec_rule =
    {A.ctor=name r.W.ctor;num_fields=integer r.W.nfields;rhs=expr r.W.rhs}
  let ind (i:W.inductive) = declaration (A.Generated(A.Inductive_role {
    A.num_params=integer i.W.ind_num_params;num_indices=integer i.W.num_indices;
    all=List.map name i.W.ind_all;ctors=List.map name i.W.constructors;
    num_nested=integer i.W.num_nested;is_rec=i.W.is_rec;
    is_reflexive=i.W.is_reflexive;is_unsafe=i.W.ind_unsafe})) i.W.ind_header None
  let ctor (c:W.constructor) = declaration (A.Generated(A.Constructor_role {
    A.induct=name c.W.induct;index=integer c.W.cidx;
    num_params=integer c.W.ctor_num_params;num_fields=integer c.W.num_fields;
    is_unsafe=c.W.ctor_unsafe})) c.W.ctor_header None
  let recursor (r:W.recursor) = declaration (A.Generated(A.Recursor_role {
    A.all=List.map name r.W.rec_all;num_params=integer r.W.rec_num_params;
    num_indices=integer r.W.rec_num_indices;num_motives=integer r.W.num_motives;
    num_minors=integer r.W.num_minors;rules=List.map rule r.W.rules;
    k=r.W.k;is_unsafe=r.W.rec_unsafe})) r.W.rec_header None
  let block = function
    | W.Inductive(is,cs,rs) -> List.map ind is @ List.map ctor cs @ List.map recursor rs
    | W.Axiom(h,false) -> [declaration A.Axiom h None]
    | W.Definition d when d.W.safety=W.Safe ->
        [declaration A.Definition d.W.header (Some d.W.value)]
    | W.Theorem(h,v,_) -> [declaration A.Theorem h (Some v)]
    | W.Opaque(h,v,false,_) -> [declaration A.Opaque h (Some v)]
    | W.Quotient(h,k) ->
        let k=match k with W.QuotType->Q.Qtype | W.QuotCtor->Q.Qctor
          | W.QuotLift->Q.Qlift | W.QuotInd->Q.Qind in
        [declaration (A.Quotient k) h None]
    | _ -> failwith "unsupported test decoder safety case"
  let decode path =
    let input=W.read_file path in
    let batches=Replay.schedule input.W.declarations in
    let blocks=List.map(function Replay.Single(_,d)->block d
      | Replay.Mutual _ -> failwith "mutual definition batch in history fixture") batches in
    let policy=List.concat_map(fun(_,d)->match d with
      | W.Axiom(h,false)->[declaration A.Axiom h None] | _->[])input.W.declarations in
    List.rev blocks,policy
  let closed label th =
    ensure (label ^ " no hypotheses") (hyp th=[]);
    ensure (label ^ " no free variables") (frees(concl th)=[])
  let exact label expected th =
    closed label th; ensure (label ^ " exact conclusion") (aconv expected (concl th))
  let accepted path blocks_expected =
    let expected_history,policy=decode path in
    let code,message,result=Hol_check.check_file_with_certificate path in
    Printf.printf "general frontend: %s\n%!" message;
    ensure "general frontend accepted" (code=0);
    let c=match result with Some c->c | None->failwith "accepted without certificate" in
    ensure "all whole input blocks retained" (List.length expected_history=blocks_expected);
    ensure "independent decoded input equals returned raw history"
      (c.Hol_check.raw_history=expected_history);
    let qpolicy=R.entries policy and qenv=A.quote_env c.Hol_check.environment
      and qhistory=C.history expected_history in
    ensure "independent input permission policy"
      (aconv qpolicy (A.quote_policy c.Hol_check.environment));
    let expected=H.node "l4_input_valid" [qpolicy;qenv;qhistory] in
    exact "raw history certificate" expected c.Hol_check.theorem;
    let head,args=strip_comb(concl c.Hol_check.theorem) in
    ensure "object predicate l4_input_valid" (fst(dest_const head)="l4_input_valid");
    ensure "exact independently decoded third argument"
      (List.length args=3 && aconv (List.nth args 2) qhistory);
    let derive lemma=compose_mp(compose_specl[qpolicy;qenv;qhistory]lemma)c.Hol_check.theorem in
    exact "derived environment" (H.node "l4_evalid" [qpolicy;qenv])
      (derive l4_input_valid_environment);
    closed "derived unique raw names" (derive l4_input_valid_unique);
    closed "derived input and environment permissions" (derive l4_input_valid_permissions);
    let expanded=compose_eq_mp(compose_specl[qpolicy;qenv;qhistory]l4_input_valid)c.Hol_check.theorem in
    let trace=compose_conjunct1 expanded in
    exact "derived exact history trace" (H.node "l4_input_trace" [qpolicy;qenv;qhistory]) trace;
    let tampered=List.rev expected_history in
    ensure "history-order mutation is nontrivial" (tampered<>expected_history);
    ensure "certificate cannot authenticate reversed raw history"
      (match C.finish c.Hol_check.environment tampered trace with
       | Error {H.kind=H.Proof_failure;_}->true | _->false);
    Printf.printf "HISTORY_THEOREM_BEGIN\n%s\nHISTORY_THEOREM_END\n%!"
      (string_of_thm c.Hol_check.theorem);
    c,expected_history
  let first_rec f ds =
    let rec loop = function
      | [] -> failwith "no recursor to mutate"
      | ({A.kind=A.Generated(A.Recursor_role r);_} as d)::rest ->
          {d with A.kind=A.Generated(A.Recursor_role(f r))}::rest
      | d::rest -> d::loop rest in loop ds
  let run group =
    let rs="fixtures/indexed/rs-slice.ndjson" in
    (match group with
    | "rs" ->
        let c,history=accepted rs 2 in
        let raw_names=List.map(fun d->d.A.name)(List.concat history) in
        let env_names=List.map(fun d->d.A.name)(A.declarations c.Hol_check.environment) in
        ensure "nonordered recursor table exercises name inventory" (raw_names<>env_names)
    | "mamb" -> ignore(accepted "fixtures/indexed/ma-mb-slice.ndjson" 8)
    | "joint" | "joint_forged" ->
        let raw="arena/corpus/tutorial/119_reduceCtorParamRefl.mk.ndjson" in
        let rh,rp=decode raw and ih,ip=decode rs in
        let combined="fixtures/indexed/joint-rs-119.ndjson" in
        let ch,cp=decode combined in
        ensure "table remapping preserves every independent decoded block"
          (ch=ih@rh && cp=rp@ip);
        if group="joint" then ignore(accepted combined 5) else begin
        let forged="fixtures/indexed/joint-forged-motive-119.ndjson" in
        let fh,fp=decode forged in
        let fi,_=decode "fixtures/indexed/rs-forged-motive.ndjson" in
        ensure "mixed history forgery changes only the indexed source count"
          (fh=fi@rh && fp=cp && fh<>ch);
        let code,_,certificate=Hol_check.check_file_with_certificate forged in
        ensure "mixed history forged motive declines without certificate"
          (code=2 && certificate=None)
        end
    | "forged_index" | "forged_motive" ->
        let _,baseline=accepted rs 2 in
        let path=if group="forged_index" then "fixtures/indexed/rs-forged-index.ndjson"
          else "fixtures/indexed/rs-forged-motive.ndjson" in
        let mutant,_=decode path in
        let original_block=List.hd(List.rev baseline) in
        let expected_block=first_rec(fun r->if group="forged_index"
          then {r with A.num_indices=0} else {r with A.num_motives=1}) original_block in
        let expected=List.rev(expected_block::List.tl(List.rev baseline)) in
        ensure "forgery changes only one recursor count" (mutant=expected && mutant<>baseline);
        let code,message,result=Hol_check.check_file_with_certificate path in
        Printf.printf "forgery frontend: %s\n%!" message;
        ensure "forged recursor count declines" (code=2);
        ensure "forged recursor count has no certificate" (result=None);
        let transported=Hol_input.read_file path in
        let claims=match List.hd transported with _,Hol_input.Inductive cs->cs
          | _->failwith "first block not an inductive" in
        let candidate=Hol_check.indexed_mutual claims in
        ensure "native generated metadata rejects count by proof failure"
          (match A.admit_indexed_mutual A.empty candidate with
           | Error {H.kind=H.Proof_failure;_}->true | _->false)
    | _ -> failwith "unknown history group");
    ensure "native rule count 29" (List.length(compose_conjuncts l4_edef_RULES)=29);
    ensure "admission rule count 11"
      (List.length(compose_conjuncts(compose_spec(parse_term "[]:l4_entry list")l4_evalid_RULES))=11);
    ensure "no new HOL axioms" (axioms()=compose_history_axioms_before);
    Printf.printf "HOL_COMPOSE_HISTORY_%s_PASSED %d\n%!" (String.uppercase_ascii group) !count
end;;
