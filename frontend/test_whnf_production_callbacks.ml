(* SPDX-License-Identifier: Apache-2.0
   Direct production WHNF boundaries on explicit small environments. Malformed
   fixtures test error priority, not successful declaration admission. *)
module C = Whnf_production_native
let rec nat = function 0 -> C.O | n -> C.S (nat (n-1))
let bool b = if b then C.True else C.False
let ascii ch =
  let k = Char.code ch in let bit i = bool (k land (1 lsl i) <> 0) in
  C.Ascii (bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let string s =
  let v = ref C.EmptyString in
  for i=String.length s-1 downto 0 do v := C.String(ascii s.[i],!v) done; !v
let list xs = List.fold_right (fun x tail -> C.Cons(x,tail)) xs C.Nil
let name s = C.NameStr(C.NameAnon,string s)
let cn s = C.EConst(name s,C.Nil)
let sort = C.ESort C.LZero
let ty = C.ESort(C.LSucc C.LZero)
let declaration label kind value =
  {C.decl_name=name label;decl_params=C.Nil;decl_type=ty;
   decl_kind_of=kind;decl_value=value;decl_hints=C.HintAbbrev}
let definition label body = declaration label C.DDefinition (C.Some body)
let env = list [
  definition "a" (cn "b"); definition "b" sort;
  declaration "opaque" C.DAssumption C.None;
  declaration "unsupported" C.DUnsupported C.None;
  declaration "unsafe" (C.DUnsafe C.DDefinition) (C.Some sort);
  declaration "partial" C.DPartial (C.Some sort);
  declaration "noValue" C.DDefinition C.None;
  definition "badBody" (cn "missing");
  definition "metadataBody" (C.EMData sort);
  {(definition "poly" sort) with C.decl_params=list[name "u"]}]
let assertions = ref 0
let equal label actual expected =
  incr assertions;
  if actual <> expected then failwith label
let out = C.Decline C.OutOfFuel
let direct = [
  "sort",sort,C.Accept sort;
  "two-alias chain",cn "a",C.Accept sort;
  "opaque",cn "opaque",C.Accept(cn "opaque");
  "unknown constant",cn "missing",C.Reject C.UnknownConstant;
  "loose bound",C.EBVar C.O,C.Reject C.LooseBoundVariable;
  "unknown free",C.EFVar(name "x"),C.Reject C.UnknownFreeVariable;
  "expression meta",C.EMVar(name "m"),C.Reject C.MetaVariable;
  "universe meta",C.ESort(C.LMVar(name "m")),C.Reject C.MetaVariable;
  "unknown universe",C.ESort(C.LParam(name "u")),C.Reject C.UnknownUniverse;
  "arity before unknown universe",C.EConst(name "a",list[C.LParam(name "missing")]),C.Reject C.UniverseArity;
  "unsupported declaration",cn "unsupported",C.Decline C.UnsupportedDeclaration;
  "unsafe before arity",C.EConst(name "unsafe",list[C.LZero]),C.Reject C.MalformedDeclaration;
  "partial",cn "partial",C.Reject C.MalformedDeclaration;
  "missing definition value",cn "noValue",C.Reject C.MalformedDeclaration;
  "unfolded unknown constant",cn "badBody",C.Reject C.UnknownConstant;
  "unknown supplied universe",C.EConst(name "poly",list[C.LParam(name "missing")]),C.Reject C.UnknownUniverse]
let let_body body = C.ELet(C.NameAnon,ty,sort,body,C.False)
let nonbeta = C.EApp(cn "opaque",sort)
let recursive = [
  "metadata",C.EMData sort,C.Accept sort;
  "metadata over aliases",C.EMData(cn "a"),C.Accept sort;
  "let",let_body sort,C.Accept sort;
  "application head",nonbeta,C.Accept nonbeta;
  "beta head and result",C.EApp(C.ELam(C.NameAnon,C.BDefault,ty,C.EBVar C.O),sort),C.Accept sort;
  "metadata error after callback",C.EMData(cn "missing"),C.Reject C.UnknownConstant;
  "let error after callback",let_body(cn "missing"),C.Reject C.UnknownConstant;
  "unfolded metadata callback",cn "metadataBody",C.Accept sort]
let bound value = C.push_binding C.empty_context ty value
let free value = {C.empty_context with C.free_context=list[
  C.Pair(name "x",{C.binding_type=ty;binding_value=value})]}
let locals = [
  "bound without value",bound C.None,C.EBVar C.O,C.EBVar C.O,1;
  "bound with value",bound(C.Some sort),C.EBVar C.O,sort,2;
  "free without value",free C.None,C.EFVar(name "x"),C.EFVar(name "x"),1;
  "free with value",free(C.Some sort),C.EFVar(name "x"),sort,2]
let builders = [
  "ordinary delayed",C.checker_mode;
  "ordinary eager-record",C.checker_eager_mode;
  "accessor delayed",C.Accessor.checker_mode C.find_decl;
  "accessor eager-record",C.Accessor.checker_eager_mode C.find_decl]
let () =
  List.iter (fun (label,build) -> List.iter (fun mode ->
    let mode_label = match mode with C.NormalReduction -> "normal" | C.EagerReduction -> "eager" in
    let prefix = label ^ "/" ^ mode_label ^ "/" in
    for depth=0 to 2 do
      let methods = build mode (nat depth) env C.Nil in
      let run = methods.C.whnf_method in
      equal (prefix ^ "inherited mode") methods.C.method_mode mode;
      List.iter (fun (name,term,result) ->
        equal (prefix ^ name ^ "/" ^ string_of_int depth)
          (run C.empty_context term) (if depth=0 then out else result)) direct;
      List.iter (fun (name,term,result) ->
        equal (prefix ^ name ^ "/" ^ string_of_int depth)
          (run C.empty_context term) (if depth<2 then out else result)) recursive;
      List.iter (fun (name,context,term,result,minimum) ->
        equal (prefix ^ name ^ "/" ^ string_of_int depth)
          (run context term) (if depth<minimum then out else C.Accept result)) locals
    done;
    for depth=1 to 3 do
      let methods = build mode (nat depth) env C.Nil in
      equal (prefix ^ "nested metadata remains recursive/" ^ string_of_int depth)
        (methods.C.whnf_method C.empty_context (C.EMData(C.EMData sort)))
        (if depth<3 then out else C.Accept sort)
    done;
    Printf.printf "PASS %s%s\n%!" label ("/" ^ mode_label))
    [C.NormalReduction;C.EagerReduction]) builders;
  Printf.printf "WHNF_PRODUCTION_CALLBACKS_PASS implementations=2 builders=2 modes=2 assertions=%d\n%!" !assertions
