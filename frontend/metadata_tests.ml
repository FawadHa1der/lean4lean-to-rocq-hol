module C = Metadata_native
module M = C.Metadata
module T = C.MetadataCases
let rec nat = function 0 -> C.O | n -> C.S (nat (n-1))
let rec elements = function C.Nil -> [] | C.Cons (x,xs) -> x :: elements xs
let string s =
  let b = Buffer.create 32 in
  let rec go = function C.EmptyString -> () | C.String (C.Ascii(a,b0,c,d,e,f,g,h),xs) ->
    let bits = [a;b0;c;d;e;f;g;h] in
    let n = List.fold_left (fun (sum,power) bit ->
      sum + (if bit=C.True then power else 0),power*2) (0,1) bits |> fst in
    Buffer.add_char b (Char.chr n); go xs in go s; Buffer.contents b
let rejection = function
  | C.UnknownConstant -> "UnknownConstant" | C.UnknownFreeVariable -> "UnknownFreeVariable"
  | C.LooseBoundVariable -> "LooseBoundVariable" | C.UnknownUniverse -> "UnknownUniverse"
  | C.UniverseArity -> "UniverseArity" | C.ExpectedSort -> "ExpectedSort"
  | C.ExpectedPi -> "ExpectedPi" | C.TypeMismatch -> "TypeMismatch"
  | C.NotDefinitionallyEqual -> "NotDefinitionallyEqual" | C.DuplicateDeclaration -> "DuplicateDeclaration"
  | C.DuplicateUniverse -> "DuplicateUniverse" | C.MalformedDeclaration -> "MalformedDeclaration"
  | C.MetaVariable -> "MetaVariable"
let decline = function C.OutOfFuel -> "OutOfFuel" | C.UnsupportedExpression -> "UnsupportedExpression"
  | C.UnsupportedDeclaration -> "UnsupportedDeclaration"
let outcome = function C.Accept _ -> "accept" | C.Reject r -> "Reject " ^ rejection r
  | C.Decline d -> "Decline " ^ decline d
let get label = function C.Accept x -> x | r -> failwith (label ^ ": " ^ outcome r)
let tests = ref 0
let full_comparisons = ref 0 and positive_gates = ref 0 and negative_gates = ref 0
let eq label a b = incr tests; if a<>b then failwith label
let full_eq label a b = incr full_comparisons; eq label a b
let check label b = incr tests; if not b then failwith label
let () =
  List.iter (fun (s,r) -> let env = get s r in
    Printf.printf "checked setup %s: %d declarations\n%!" s (List.length(elements env)))
    ["padding",M.padded_env;"Nat",M.nat_env;"Eq",M.eq_env;"structures",M.structure_env;
     "quotients",M.base_env;"Nat.add",M.with_add];
  eq "genuine indexed recursor and dependent fields" M.fixture_shape_checks (C.Accept C.True);
  List.iter (fun c -> let label = string c.T.case_label in
    let env = get (label ^ " environment") c.T.case_env in
    eq "index gate" (C.use_index M.fuel env) C.True;
    eq "decode exactly" (T.check_decoded c) (C.Accept C.Tt);
    let original = T.ordinary env c in
    Printf.printf "%s: %s\n%!" label (outcome original);
    if c.T.case_positive=C.True then begin
      incr positive_gates; eq (label ^ " expected installation") original (T.expected env c)
    end else begin
      incr negative_gates; check (label ^ " negative") (match original with C.Accept _ -> false | _ -> true)
    end;
    List.iter (fun budget ->
      let frozen = T.linear_cache_new (nat budget) env c in
      full_eq (label ^ " linear-cache/new-Checker vs new ordinary") frozen original;
      full_eq (label ^ " forced collision") (T.forced (nat budget) env c) frozen;
      full_eq (label ^ " guarded") (T.guarded (nat budget) env c) frozen) [0;1;128])
    (elements T.cases);
  let env = get "base" M.base_env in
  List.iter (fun (C.Pair(C.Pair(label,term),expected)) ->
    let s = string label in
    eq (s ^ " original reduction") (C.whnf M.fuel env C.Nil C.empty_context term) (C.Accept expected);
    List.iter (fun hash -> let lookup = C.prepare_lookup hash env in
      eq (s ^ " indexed reduction")
        (C.prepared_whnf lookup M.fuel env C.Nil C.empty_context term) (C.Accept expected))
      [C.suffix_bitfold8;(fun _ -> C.N0)]) (elements T.reductions);
  List.iter (fun (label,r) -> eq label r (C.Reject C.MalformedDeclaration))
    ["forged constructor metadata",M.rejected_ctor_metadata;
     "forged recursor metadata",M.rejected_rec_metadata;
     "forged quotient signature",M.rejected_quot_signature];
  eq "missing Eq prerequisite" M.missing_eq_quot (C.Reject C.UnknownConstant);
  let env = get "add env" M.with_add in
  eq "authenticated tag" (C.primitive_authenticated M.fuel env C.PNatAdd) (C.Accept C.Tt);
  let expected = C.Accept (C.ELit(C.LitNat(C.Npos(C.XO C.XH)))) in
  eq "authenticated add original reduction" (C.whnf M.fuel env C.Nil C.empty_context M.add_value) expected;
  List.iter (fun hash -> eq "authenticated add indexed reduction"
    (C.prepared_whnf (C.prepare_lookup hash env) M.fuel env C.Nil C.empty_context M.add_value) expected)
    [C.suffix_bitfold8;(fun _ -> C.N0)];
  Printf.printf "positive_admission_gates=%d negative_admission_controls=%d direct_reduction_gates=%d full_result_comparisons=%d total_assertions=%d\n%!"
    !positive_gates !negative_gates (List.length(elements T.reductions)+1) !full_comparisons !tests
