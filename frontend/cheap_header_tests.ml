(* Test-only preparation spies. No expected result enters an admission call. *)
module C = Cheap_header_native
module T = C.MetadataCases
let rec nat = function 0 -> C.O | n -> C.S (nat (n - 1))
let rec pos n = if n = 1 then C.XH else if n land 1 = 0 then C.XO (pos (n / 2)) else C.XI (pos (n / 2))
let binary n = if n = 0 then C.N0 else C.Npos (pos n)
let name n = C.NameNum (C.NameAnon, binary n)
let rec list = function [] -> C.Nil | x :: xs -> C.Cons (x, list xs)
let rec elements = function C.Nil -> [] | C.Cons (x, xs) -> x :: elements xs
let p_name = name 1 and h_name = name 2 and fresh = name 3
let prop = C.ESort C.LZero
let p = C.EConst (p_name, C.Nil) and h = C.EConst (h_name, C.Nil)
let loose = C.EBVar C.O
let unknown = C.EConst (name 4, C.Nil)
let assumed n ty = {C.decl_hints = C.HintOpaque; decl_name =n; decl_params=C.Nil; decl_type=ty;
  decl_value=C.None; decl_kind_of=C.DAssumption}
let pad size prefix = list (prefix @ List.init (size - List.length prefix)
  (fun i -> assumed (name (100 + i)) prop))
let hashes = ["bitfold8", C.suffix_bitfold8; "all-collide", (fun _ -> C.N0)]
let kinds = [(C.DagDefinition C.HintOpaque); C.DagTheorem; C.DagOpaque]
let tests = ref 0 and comparisons = ref 0 and zero_preparations = ref 0
let one_preparation = ref 0 and positives = ref 0
let eq label a b = incr tests; if a <> b then failwith label
let full label a b = incr comparisons; eq label a b
let quote ty body = match T.quote_pair ty body with C.Pair (C.Pair (tr,br),rows) -> rows,tr,br
let is_reserved_kind = function C.DagDefinition _ -> false | C.DagTheorem | C.DagOpaque -> true
type probe = {
  label : string; n : C.name; ps : C.name C.list; ty : C.expr; body : C.expr;
  calls : C.dag_admission_kind -> int; reason : C.dag_admission_kind -> C.reject_reason option;
}
let probe label ?(n=fresh) ?(ps=C.Nil) ?(ty=p) ?(body=h) ?(calls=(fun _ -> 1))
    ?(reason=(fun _ -> None)) () = {label;n;ps;ty;body;calls;reason}
let cheap reason = (fun _ -> 0), (fun _ -> Some reason)
let fixed reason _ = Some reason
let probes () =
  let du_calls,du_reason = cheap C.DuplicateUniverse in
  let bad_calls,bad_reason = cheap C.MalformedDeclaration in
  let dd_calls,dd_reason = cheap C.DuplicateDeclaration in
  let du = list [C.NameAnon; C.NameAnon] in
  [probe "accepting-baseline" ();
   probe "duplicate-universes" ~ps:du ~calls:du_calls ~reason:du_reason ();
   probe "unscoped-type" ~ty:loose ~calls:bad_calls ~reason:bad_reason ();
   probe "universe-before-scope" ~ps:du ~ty:loose ~calls:du_calls ~reason:du_reason ();
   probe "duplicate-before-universe" ~n:h_name ~ps:du ~calls:dd_calls ~reason:dd_reason ();
   probe "duplicate-before-scope" ~n:h_name ~ty:loose ~calls:dd_calls ~reason:dd_reason ();
   probe "duplicate-only-retains-index" ~n:h_name ~reason:(fixed C.DuplicateDeclaration) ();
   probe "reserved" ~n:C.core_nat_name
     ~calls:(fun k -> if is_reserved_kind k then 0 else 1)
     ~reason:(fun k -> if is_reserved_kind k then Some C.MalformedDeclaration else None) ();
   probe "reserved-before-universe" ~n:C.core_nat_name ~ps:du ~ty:loose ~calls:(fun _ -> 0)
     ~reason:(fun k -> Some (if is_reserved_kind k then C.MalformedDeclaration else C.DuplicateUniverse)) ();
   probe "late-body-scope" ~body:loose ();
   probe "type-inference-before-body-scope" ~ty:unknown ~body:loose ();
   probe "type-inference-before-body-metavariable" ~ty:unknown ~body:(C.EMVar C.NameAnon) ()]

let spied hash kind budget fuel env n ps rows tr br =
  let calls = ref 0 in
  let prepare C.Tt = incr calls; C.prepare_lookup hash env in
  let result = C.admit_with_preparation prepare kind budget fuel env n ps rows tr br in
  result,!calls

let check_case label hash kind budget fuel env n ps rows tr br expected_calls expected_reason =
  let old = C.before_header_indexed_admit hash kind (nat budget) (nat fuel) env n ps rows tr br in
  let result,calls = spied hash kind (nat budget) (nat fuel) env n ps rows tr br in
  eq (label ^ ": preparation calls") calls expected_calls;
  if calls = 0 then incr zero_preparations else if calls = 1 then incr one_preparation
  else failwith "more than one preparation";
  full (label ^ ": before-change full result") result old;
  full (label ^ ": real forced entry") result
    (C.indexed_admit hash kind (nat budget) (nat fuel) env n ps rows tr br);
  full (label ^ ": linear-cache/new-Checker") result
    (C.linear_cache_new_admit kind (nat budget) (nat fuel) env n ps rows tr br);
  full (label ^ ": new ordinary admission") result
    (C.new_ordinary_decode_admit kind (nat fuel) env n ps rows tr br);
  full (label ^ ": guarded before/after")
    (C.indexed_dag_admit kind (nat budget) (nat fuel) env n ps rows tr br)
    (C.before_header_guarded kind (nat budget) (nat fuel) env n ps rows tr br);
  let guarded_calls = ref 0 in
  let prepare C.Tt = incr guarded_calls; C.prepare_lookup C.suffix_bitfold8 env in
  let guarded = if C.use_index (nat fuel) env = C.True then
      C.admit_with_preparation prepare kind (nat budget) (nat fuel) env n ps rows tr br
    else C.linear_env_admit kind (nat budget) (nat fuel) env n ps rows tr br in
  full (label ^ ": guarded spy result") guarded
    (C.indexed_dag_admit kind (nat budget) (nat fuel) env n ps rows tr br);
  eq (label ^ ": guarded spy count") !guarded_calls
    (if C.use_index (nat fuel) env = C.True then expected_calls else 0);
  Option.iter (fun reason -> eq (label ^ ": exact reason") result (C.Reject reason)) expected_reason;
  result

let matrix () =
  List.iter (fun size ->
    let env = pad size [assumed h_name p; assumed p_name prop] in
    List.iter (fun kind -> List.iter (fun fuel ->
      eq "unchanged 0-fuel/63-64 guard" (C.use_index (nat fuel) env)
        (if fuel > 0 && size >= 64 then C.True else C.False);
      List.iter (fun budget -> List.iter (fun (_,hash) ->
        List.iter (fun c ->
          let rows,tr,br = quote c.ty c.body in
          let result = check_case c.label hash kind budget fuel env c.n c.ps rows tr br
              (c.calls kind) (c.reason kind) in
          if c.label = "accepting-baseline" && fuel = 32 then begin
            incr positives;
            let dk = match kind with C.DagDefinition _ -> C.DDefinition | C.DagTheorem -> C.DTheorem | C.DagOpaque -> C.DOpaque in
            let installed = {C.decl_hints = C.HintOpaque; decl_name =fresh;decl_params=C.Nil;decl_type=p;decl_value=C.Some h;decl_kind_of=dk} in
            eq "baseline exact installation" result (C.Accept (C.Cons (installed,env)))
          end;
          if c.label = "late-body-scope" then begin
            if fuel = 0 then eq "header fuel before body scope" result (C.Decline C.OutOfFuel);
            if fuel = 32 then eq "late body scope rejection" result (C.Reject C.MalformedDeclaration)
          end;
          if c.label = "type-inference-before-body-scope" && fuel = 32 then
            eq "unknown type before malformed body" result (C.Reject C.UnknownConstant)
        ) (probes ());
        (* Cheap duplicate-universe errors must not overtake decoder/root errors. *)
        let rows,tr,br = quote p h in
        let duplicate_rows = list [C.Pair(pos 1,C.DSort C.LZero);C.Pair(pos 1,C.DSort C.LZero)] in
        let malformed = ["missing-type",rows,pos 999,br,C.MalformedDeclaration;
                         "missing-body",rows,tr,pos 999,C.MalformedDeclaration;
                         "empty-rows",C.Nil,tr,br,C.MalformedDeclaration;
                         "self-reference",list [C.Pair(pos 1,C.DMData(pos 1))],pos 1,pos 1,C.MalformedDeclaration;
                         "duplicate-row",duplicate_rows,pos 1,pos 1,C.DuplicateDeclaration] in
        List.iter (fun (label,rs,rt,rb,reason) ->
          ignore (check_case label hash kind budget fuel env fresh (list [C.NameAnon;C.NameAnon])
            rs rt rb 0 (Some reason))) malformed;
        ignore (check_case "duplicate-row-before-reserved-name" hash kind budget fuel env C.core_nat_name C.Nil
          duplicate_rows (pos 1) (pos 1) 0 (Some C.DuplicateDeclaration))
      ) hashes) [0;1;32]) [0;1;2;32]) kinds
  ) [63;64;96]

let shadows () =
  let du = list [C.NameAnon;C.NameAnon] in
  let rows,tr,br = quote loose h in
  List.iter (fun marker ->
    let shadow = {(assumed fresh prop) with C.decl_kind_of=marker} in
    let env = pad 64 [shadow; assumed fresh unknown; assumed h_name p; assumed p_name prop] in
    List.iter (fun kind -> List.iter (fun (_,hash) ->
      ignore (check_case "newest-first arbitrary metadata shadow" hash kind 1 0 env fresh du rows tr br
        0 (Some C.DuplicateDeclaration))) hashes) kinds
  ) [C.DAssumption;C.DUnsafe C.DAssumption;C.DPartial;C.DUnsupported];
  let env = pad 64 [assumed C.core_nat_name prop;assumed h_name p;assumed p_name prop] in
  List.iter (fun kind -> List.iter (fun (_,hash) ->
    ignore (check_case "reserved-before-duplicate" hash kind 1 0 env C.core_nat_name du rows tr br 0
      (Some (if is_reserved_kind kind then C.MalformedDeclaration else C.DuplicateDeclaration)))) hashes) kinds

let metadata () =
  List.iter (fun c ->
    let env = match c.T.case_env with C.Accept env -> env | _ -> failwith "metadata setup must accept" in
    let rows,tr,br = quote c.T.case_type c.T.case_body in
    List.iter (fun budget -> List.iter (fun (_,hash) ->
      let result = check_case "checked metadata" hash c.T.case_kind budget 256 env c.T.case_name C.Nil rows tr br 1 None in
      if c.T.case_positive = C.True then begin
        incr positives; eq "metadata positive exact installation" result (T.expected env c)
      end
    ) hashes) [0;1;128]
  ) (elements T.cases)

let () =
  matrix (); shadows (); metadata ();
  if !positives = 0 || !zero_preparations = 0 || !one_preparation = 0 then failwith "vacuous test coverage";
  Printf.printf "full_result_comparisons=%d assertions=%d zero_preparation_probes=%d one_preparation_probes=%d explicit_positive_installations=%d\n%!"
    !comparisons !tests !zero_preparations !one_preparation !positives
