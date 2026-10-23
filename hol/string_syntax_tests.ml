let string_syntax_axioms_before = axioms();;
needs "hol/core.ml";;
needs "hol/string_syntax.ml";;
needs "hol/nested_names.ml";;
needs "hol/indexed_syntax.ml";;
needs "hol/projection_syntax.ml";;

let string_syntax_tests () =
  let open Lean4hol in
  let count=ref 0 in
  let test label p = if not p then failwith("string syntax: "^label) else incr count in
  let bytes ns = String.init(List.length ns)(fun i -> Char.chr(List.nth ns i)) in
  let utf8 n = if n<128 then bytes[n]
    else if n<2048 then bytes[192+n/64;128+n mod 64]
    else if n<65536 then bytes[224+n/4096;128+(n/64)mod 64;128+n mod 64]
    else bytes[240+n/262144;128+(n/4096)mod 64;128+(n/64)mod 64;128+n mod 64] in
  let decode s = try Some(string_scalars s) with Stop {kind=Invalid_input;_}->None in
  for n=0 to 1114111 do
    if n<55296 || n>=57344 then
      test "every Unicode scalar roundtrip" (decode(utf8 n)=Some[n])
  done;
  for a=0 to 255 do for b=0 to 255 do
    let expected = if a<128 && b<128 then Some[a;b]
      else if a>=194 && a<=223 && b>=128 && b<=191 then Some[(a-192)*64+b-128]
      else None in
    test "every two-byte input classification" (decode(bytes[a;b])=expected)
  done done;
  for n=55296 to 57343 do
    test "surrogate encoding forbidden" (decode(utf8 n)=None)
  done;
  for n=128 to 255 do test "non-ASCII single byte forbidden" (decode(bytes[n])=None) done;
  List.iter(fun bs -> test "invalid UTF-8 boundary" (decode(bytes bs)=None))
    [[192;128];[193;191];[224;128;128];[224;159;191];[237;160;128];
     [240;128;128;128];[240;143;191;191];[244;144;128;128];[244;191;191;191];
     [245;128;128;128];[248;128;128;128;128];[255];[194];[224;160];
     [240;144;128];[194;65];[225;128;65];[241;128;128;65]];
  let samples=[[];[0];[65;66;67];[128];[2047;2048];[55295;57344];
    [65535;65536;1114111];[97;769;128512]] in
  let equations=[l4_lift;l4_subst;l4_expr_lsubst;l4_params_expr;l4_anon;
    l4_uses_bound;l4_without_const;l4_no_nested_aux;l4_pi_parts] in
  List.iter(fun ns ->
    let s=String.concat "" (List.map utf8 ns) in
    let e=Strlit s in
    let q=node "L4StrLit"[mk_list(List.map number ns,`:num`)] in
    test "exact scalar quotation" (aconv(quote_expr e)q);
    test "ML lift" (lift {remaining=1000} 7 3 e=e);
    test "ML substitution" (subst {remaining=1000} 2 (Sort Zero) e=e);
    test "ML universe substitution" (instantiate_levels {remaining=1000} [Anonymous] [Zero] e=e);
    let checks=[
      node "l4_lift"[q;`7`;`3`],q;
      node "l4_subst"[q;`2`;quote_expr(Sort Zero)],q;
      node "l4_expr_lsubst"[q;`[]:l4_name list`;`[]:l4_level list`],q;
      node "l4_anon"[q],q;
      node "l4_params_expr"[q;`[]:l4_name list`],`T`;
      node "l4_uses_bound"[q;`0`],`F`;
      node "l4_without_const"[`L4Anonymous`;q],`T`;
      node "l4_no_nested_aux"[q],`T`] in
    List.iter(fun(a,b)->let h=prove(mk_eq(a,b),REWRITE_TAC equations) in
      test "exact closed HOL traversal equality"
        (hyp h=[] && frees(concl h)=[] && aconv(concl h)(mk_eq(a,b)))) checks;
    let h=prove(mk_comb(mk_comb(mk_const("ALL",[`:num`,`:A`]),`l4_unicode_scalar`),
      mk_list(List.map number ns,`:num`)),REWRITE_TAC[ALL;l4_unicode_scalar] THEN CONV_TAC NUM_REDUCE_CONV) in
    test "quoted characters have proved scalar validity" (hyp h=[] && frees(concl h)=[])) samples;
  test "pure engine cannot invent String environment" (match infer [] (Strlit "abc") with
    | Error {kind=Unsupported;_}->true|_->false);
  test "invalid literal classification" (match infer [] (Strlit(bytes[192;128])) with
    | Error {kind=Invalid_input;_}->true|_->false);
  test "zero fuel preserved" (match infer ~fuel:0 [] (Strlit "") with
    | Error {kind=Resource;_}->true|_->false);
  test "empty versus NUL are distinct" (not(aconv(quote_expr(Strlit ""))(quote_expr(Strlit "\000"))));
  test "normalization forms not conflated" (string_scalars(utf8 233)<>string_scalars("e"^utf8 769));
  test "no added HOL axioms" (axioms()=string_syntax_axioms_before);
  Printf.printf "HOL_STRING_SYNTAX_TESTS_PASSED %d\n%!" !count;;
string_syntax_tests();;
