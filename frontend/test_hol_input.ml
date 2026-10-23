let checks=ref 0
let check label condition =
  incr checks;
  if not condition then failwith ("HOL transport: "^label)
let n s=Wire.dotted_name [s]
let ty=Wire.Sort(Wire.Succ Wire.Zero)
let header s={Wire.name=n s;params=[];typ=ty}
let definition ?(safety=Wire.Safe) ?(all=[]) s value =
  Wire.Definition {Wire.header=header s;value;safety;hints=Wire.Abbrev;
    all=if all=[] then [n s] else List.map n all}
let export rows={Wire.metadata={Wire.format_version="3.1.0";lean_version="test";lean_hash="test"};
  declarations=rows;name_count=0;level_count=0;expr_count=0}
let translate rows=Hol_input.translate_export (export rows)
let malformed rows=try ignore(translate rows);false with Wire.Error e->e.Wire.kind=Wire.Malformed
let () =
  let base=definition "base" (Wire.Sort Wire.Zero) in
  let use=definition "use" (Wire.Const(n "base",[])) in
  check "empty input" (translate []=[]);
  check "forward dependency reordered" (List.map fst (translate [10,use;20,base])=[20;10]);
  check "original line preserved" (List.map fst (translate [20,base;10,use])=[20;10]);
  check "all records retained" (List.length(translate [10,use;20,base])=2);
  check "unchanged reference" (match translate [10,use;20,base] with
    | [_;_,Hol_input.Definition(_,Hol_input.Const(Hol_input.Str(Hol_input.Anonymous,"base"),[]))] -> true
    | _ -> false);
  check "duplicate name malformed" (malformed [10,base;20,base]);
  check "safe cycle malformed" (malformed [10,use;20,definition "base" (Wire.Const(n "use",[]))]);
  check "unknown reference reaches checker" (match translate [10,use] with
    | [10,Hol_input.Definition _] -> true | _ -> false);
  check "safe source all metadata is not a group" (match translate
    [10,definition ~all:["base";"notExported"] "base" (Wire.Sort Wire.Zero)] with
    | [10,Hol_input.Definition _] -> true | _ -> false);
  let mutual s v=definition ~safety:Wire.Unsafe ~all:["a";"b"] s v in
  check "mutual block explicitly declined" (match translate
    [10,mutual "a" (Wire.Const(n "b",[]));20,base;
     30,mutual "b" (Wire.Const(n "base",[]))] with
    | [20,Hol_input.Definition _;10,Hol_input.Unsupported _] -> true | _ -> false);
  check "missing mutual member malformed" (malformed [10,mutual "a" (Wire.Const(n "b",[]))]);
  check "partial singleton explicitly declined" (match translate
    [10,definition ~safety:Wire.Partial "p" (Wire.Const(n "p",[]))] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  let large="12345678901234567890123456789012345678901234567890" in
  check "large literal remains exact" (match translate
    [10,definition "big" (Wire.NatLit(Z.of_string large))] with
    | [10,Hol_input.Definition(_,Hol_input.Natlit n)] -> n=large | _ -> false);
  check "zero literal preserved" (match translate
    [10,definition "zero" (Wire.NatLit Z.zero)] with
    | [10,Hol_input.Definition(_,Hol_input.Natlit "0")] -> true | _ -> false);
  let primitive ?(safety=Wire.Safe) path =
    let name=Wire.dotted_name path in
    Wire.Definition {Wire.header={Wire.name=name;params=[];typ=ty};
      value=Wire.Sort Wire.Zero;safety;hints=Wire.Abbrev;all=[name]} in
  List.iter (fun op ->
    check ("primitive candidate "^op) (match translate [10,primitive ["Nat";op]] with
      | [10,Hol_input.Primitive_definition(h,Hol_input.Sort Hol_input.Zero)] ->
        h.Hol_input.name=Hol_input.Str(Hol_input.Str(Hol_input.Anonymous,"Nat"),op)
      | _ -> false)) ["add";"pred";"sub";"mul";"beq";"ble";"pow";"shiftLeft"];
  check "unimplemented primitive remains unsupported" (match translate [10,primitive ["Nat";"gcd"]] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "Nat cannot use ordinary definition path" (match translate [10,primitive ["Nat"]] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "dotted text is not a primitive name" (match translate [10,primitive ["Nat.add"]] with
    | [10,Hol_input.Definition _] -> true | _ -> false);
  check "unsafe primitive is not a candidate" (match translate [10,primitive ~safety:Wire.Unsafe ["Nat";"add"]] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "partial primitive is not a candidate" (match translate [10,primitive ~safety:Wire.Partial ["Nat";"add"]] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  List.iter (fun safety -> check "shiftLeft retains original safety gate"
    (match translate [10,primitive ~safety ["Nat";"shiftLeft"]] with
     | [10,Hol_input.Unsupported _] -> true | _ -> false)) [Wire.Unsafe;Wire.Partial];
  let shift_header={Wire.name=Wire.dotted_name ["Nat";"shiftLeft"];params=[];typ=ty} in
  List.iter (fun declaration -> check "shiftLeft requires definition kind"
    (match translate [10,declaration] with
     | [10,Hol_input.Unsupported _] -> true | _ -> false))
    [Wire.Axiom(shift_header,false);Wire.Theorem(shift_header,Wire.Sort Wire.Zero,[]);
     Wire.Opaque(shift_header,Wire.Sort Wire.Zero,false,[])];
  let ph={Wire.name=Wire.dotted_name ["Nat";"add"];params=[];typ=ty} in
  check "primitive axiom remains unsupported" (match translate [10,Wire.Axiom(ph,false)] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "primitive opaque remains unsupported" (match translate [10,Wire.Opaque(ph,Wire.Sort Wire.Zero,false,[])] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "primitive theorem remains unsupported" (match translate [10,Wire.Theorem(ph,Wire.Sort Wire.Zero,[])] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  let owner=Wire.dotted_name ["Test";"Pair"] in
  let qowner=Hol_input.Str(Hol_input.Str(Hol_input.Anonymous,"Test"),"Pair") in
  let proj i e=Wire.Proj(owner,i,e) in
  check "projection preserves structured owner and index" (match translate
    [10,definition "field" (proj Z.one (Wire.Const(n "base",[])))] with
    | [10,Hol_input.Definition(_,Hol_input.Proj(o,1,Hol_input.Const(_,[])))] -> o=qowner
    | _ -> false);
  check "nested projections retained" (match translate
    [10,definition "field" (proj Z.zero (proj Z.one (Wire.Const(n "base",[]))))] with
    | [10,Hol_input.Definition(_,Hol_input.Proj(_,0,Hol_input.Proj(_,1,_)))] -> true
    | _ -> false);
  check "projection retains major dependencies" (List.map fst (translate
    [10,definition "field" (proj Z.zero (Wire.Const(n "base",[])));20,base])=[20;10]);
  check "oversized projection index explicitly declined" (match translate
    [10,definition "field" (proj (Z.shift_left Z.one 200) (Wire.Const(n "base",[])))] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "negative direct projection index explicitly declined" (match translate
    [10,definition "field" (proj Z.minus_one (Wire.Const(n "base",[])))] with
    | [10,Hol_input.Unsupported _] -> true | _ -> false);
  check "projection retains literal major" (match translate
    [10,definition "field" (proj Z.zero (Wire.StringLit "text"))] with
    | [10,Hol_input.Definition(_,Hol_input.Proj(_,0,Hol_input.Strlit "text"))] -> true | _ -> false);
  List.iter(fun path ->
    let ph={Wire.name=Wire.dotted_name path;params=[];typ=ty} in
    check "text primitive retains raw candidate" (match translate[10,primitive path] with
      |[10,Hol_input.Text_primitive_definition(h,Hol_input.Sort Hol_input.Zero)] ->
        h.Hol_input.name=Hol_input.name ph.Wire.name|_->false);
    List.iter(fun safety->check "text safety preserved before erasure"
      (match translate[10,primitive ~safety path] with
        |[10,Hol_input.Unsupported _]->true|_->false)) [Wire.Unsafe;Wire.Partial];
    List.iter(fun declaration -> check "text primitive wrong declaration kind declined"
      (match translate[10,declaration] with |[10,Hol_input.Unsupported _]->true|_->false))
      [Wire.Axiom(ph,false);Wire.Opaque(ph,Wire.Sort Wire.Zero,false,[]);
       Wire.Theorem(ph,Wire.Sort Wire.Zero,[])];
    check "dotted text name is ordinary" (match translate[10,primitive[String.concat "." path]] with
      |[10,Hol_input.Definition _]->true|_->false)) [["Char";"ofNat"];["String";"ofList"]];
  List.iter(fun s->check "literal bytes preserved without host interpretation"
    (match translate[10,definition "literal"(Wire.StringLit s)] with
      |[10,Hol_input.Definition(_,Hol_input.Strlit t)]->s=t|_->false))
    ["";"\000";"a\000b";"\195\169";"e\204\129";"\240\159\152\128";"\192\128"];
  List.iter (fun (source,target) ->
    check "quotient kind and raw header preserved" (match translate
      [10,Wire.Quotient({Wire.name=Wire.dotted_name ["Untrusted";"Quot"];
        params=[n "u"];typ=ty},source)] with
      | [10,Hol_input.Quotient(h,k)] -> k=target &&
        h.Hol_input.name=Hol_input.Str(Hol_input.Str(Hol_input.Anonymous,"Untrusted"),"Quot") &&
        h.Hol_input.params=[Hol_input.Str(Hol_input.Anonymous,"u")] &&
        h.Hol_input.typ=Hol_input.Sort(Hol_input.Succ Hol_input.Zero)
      | _ -> false))
    [Wire.QuotType,Hol_input.Qtype;Wire.QuotCtor,Hol_input.Qctor;
     Wire.QuotLift,Hol_input.Qlift;Wire.QuotInd,Hol_input.Qind];
  check "quotient requires its implicit equality dependency first"
    (List.map fst (translate [10,Wire.Quotient(header "Quot",Wire.QuotType);
      20,definition "Eq" (Wire.Sort Wire.Zero)])=[20;10]);
  Printf.printf "PASS: %d HOL transport checks\n" !checks
