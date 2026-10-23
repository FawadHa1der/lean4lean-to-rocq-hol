(* Same driver linked separately with the actual frozen extraction/frontend and
   the combined candidate. Every result field is emitted, never an expected verdict. *)
module C = Lean_arena
module A = Rocq_adapter
module D = Dag_adapter
let wn s = Wire.Str(Wire.Anonymous,s)
let cn s = A.name (A.create ()) (wn s)
let nat = A.nat
let list xs = A.list (fun x -> x) xs
let assumed n ty = {C.decl_hints = C.HintOpaque; decl_name =n;decl_params=C.Nil;decl_type=ty;decl_value=C.None;decl_kind_of=C.DAssumption}
let pn = cn "P" and hn = cn "proof" and out = wn "out"
let prop = C.ESort C.LZero and typ = C.ESort(C.LSucc C.LZero)
let p = C.EConst(pn,C.Nil)
let wp = Wire.Const(wn "P",[]) and wh = Wire.Const(wn "proof",[])
let header name params typ : Wire.constant = {name;params;typ}
let definition h v = Wire.Definition {header=h;value=v;safety=Wire.Safe;hints=Wire.Abbrev;all=[h.Wire.name]}
let metadata_tail () =
  let ty = C.ELet(C.NameAnon,typ,prop,C.EBVar C.O,C.True) in
  let ind = {C.ind_num_params=nat 2;ind_num_indices=nat 3;ind_all=list[pn;hn];
    ind_ctors=list[hn];ind_num_nested=nat 4;ind_is_rec=C.True;ind_is_reflexive=C.True;ind_is_unsafe=C.False} in
  let ctor = {C.ctor_induct=pn;ctor_index=nat 5;ctor_num_params=nat 6;ctor_num_fields=nat 7;ctor_is_unsafe=C.True} in
  let recd = {C.rec_all=list[pn];rec_num_params=nat 1;rec_num_indices=nat 2;rec_num_motives=nat 3;
    rec_num_minors=nat 4;rec_rules=list[{C.rule_ctor=hn;rule_nfields=nat 2;rule_rhs=ty}];rec_k=C.True;rec_is_unsafe=C.False} in
  List.mapi (fun i kind -> {(assumed (cn ("meta" ^ string_of_int i)) ty) with C.decl_kind_of=kind;
    decl_params=list[pn;hn];decl_value=C.Some (C.ELit(C.LitString(A.string "\000\255payload")))})
    [C.DInductive ind;C.DConstructor ctor;C.DRecursor recd;C.DPrimitive C.PNatMul;
     C.DQuotient C.QInd;C.DUnsafe C.DOpaque;C.DPartial;C.DUnsupported;C.DTheorem;C.DDefinition]
let env size variant =
  let base = [assumed hn p;assumed pn prop] @ metadata_tail () in
  let base = match variant with
    | 1 -> {(assumed hn p) with C.decl_kind_of=C.DUnsafe C.DAssumption} :: base
    | 2 -> assumed hn typ :: base
    | 3 -> {(assumed hn p) with C.decl_kind_of=C.DUnsupported} :: base
    | _ -> base in
  list (base @ List.init (max 0 (size-List.length base)) (fun i ->
    assumed (C.NameStr(C.NameNum(C.NameAnon,A.binary(Z.of_int i)),A.string "same")) prop))
let cases =
  let h = header out [] wp in
  [Wire.Theorem(h,wh,[]);Wire.Opaque(h,wh,false,[]);definition h wh;
   Wire.Theorem(h,Wire.Sort Wire.Zero,[]);
   Wire.Theorem(header out [wn "u";wn "u"] wp,wh,[]);
   Wire.Theorem(header (wn "proof") [] wp,wh,[]);
   Wire.Theorem(header (wn "Nat") [] wp,wh,[]);
   Wire.Opaque(h,Wire.NatLit Z.one,false,[]);
   Wire.Opaque(h,Wire.BVar Z.zero,false,[]);
   Wire.Opaque(h,Wire.MData wh,false,[]);
   Wire.Theorem(header out [] (Wire.Pi(Wire.Anonymous,wp,wp,Wire.Implicit)),
      Wire.Lam(Wire.Anonymous,wp,Wire.BVar Z.zero,Wire.Implicit),[]);
   definition (header out [] (Wire.Sort(Wire.Succ Wire.Zero))) (Wire.Sort Wire.Zero)]
let () =
  let count = ref 0 and accepts = ref 0 in
  List.iter (fun size -> List.iter (fun variant -> List.iter (fun fuel ->
    List.iter (fun input ->
      let e = env size variant in
      let dag = D.admit (nat fuel) e (A.create ()) input in
      let ordinary = A.admit (nat fuel) e (A.create ()) input in
      if dag <> ordinary then failwith "snapshot driver disagrees with ordinary admit full result";
      (match dag with C.Accept _ -> incr accepts | _ -> ());
      print_endline (Yojson.Safe.to_string (`List [`Int !count;Full_result.result dag]));
      incr count) cases) [0;1;16]) [0;1;2;3]) [16;63;64;80];
  if !accepts = 0 then failwith "vacuous snapshot differentials";
  Printf.eprintf "%d full results emitted; %d accepts; all equal ordinary admission\n" !count !accepts
