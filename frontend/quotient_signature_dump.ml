(* Emit data quotations from validated wire syntax, not checker verdicts. *)
let wrap tag xs = "(" ^ tag ^ " " ^ String.concat " " xs ^ ")"
let seq f xs = "[" ^ String.concat ";" (List.map f xs) ^ "]"
let rec name = function
  | Wire.Anonymous -> "L4Anonymous"
  | Wire.Str(n,s) -> wrap "L4String" [name n;
      seq string_of_int (List.init (String.length s) (fun i -> Char.code s.[i]))]
  | Wire.Num(n,k) -> wrap "L4Numeric" [name n;Z.to_string k]
let rec level = function
  | Wire.Zero -> "L4Zero"
  | Wire.Succ u -> wrap "L4Succ" [level u]
  | Wire.Max(u,v) -> wrap "L4Max" [level u;level v]
  | Wire.IMax(u,v) -> wrap "L4IMax" [level u;level v]
  | Wire.Param n -> wrap "L4Param" [name n]
let rec expr = function
  | Wire.BVar i -> wrap "L4BVar" [Z.to_string i]
  | Wire.Sort u -> wrap "L4Sort" [level u]
  | Wire.Const(n,us) -> wrap "L4Const" [name n;seq level us]
  | Wire.App(f,a) -> wrap "L4App" [expr f;expr a]
  | Wire.Lam(_,a,b,_) -> wrap "L4Lam" ["L4Anonymous";expr a;expr b]
  | Wire.Pi(_,a,b,_) -> wrap "L4Pi" ["L4Anonymous";expr a;expr b]
  | Wire.Let(_,a,v,b,_) -> wrap "L4Let" ["L4Anonymous";expr a;expr v;expr b]
  | Wire.MData e -> expr e
  | Wire.Proj(n,i,e) -> wrap "L4Proj" [name n;Z.to_string i;expr e]
  | Wire.NatLit i -> wrap "L4NatLit" [Z.to_string i]
  | Wire.StringLit _ -> failwith "string is not supported by the signature quotation"
let kind = function
  | Wire.QuotType -> "L4QuotType" | Wire.QuotCtor -> "L4QuotCtor"
  | Wire.QuotLift -> "L4QuotLift" | Wire.QuotInd -> "L4QuotInd"
let quote s = "`" ^ s ^ "`"
let () =
  if Array.length Sys.argv<>2 then failwith "expected one NDJSON path";
  let data=Wire.read_file Sys.argv.(1) in
  let claims=List.filter_map (function
    | _,Wire.Quotient(h,k) ->
      let us=List.map (fun n -> Wire.Param n) h.Wire.params in
      let u,v=match us with [u]->u,Wire.Zero | [u;v]->u,v
        | _ -> failwith "unexpected source quotient universe count" in
      Some("(" ^ String.concat "," [quote(kind k);quote(name h.Wire.name);
        quote(expr h.Wire.typ);quote(level u);quote(level v);
        string_of_int(List.length us)] ^ ")")
    | _ -> None) data.Wire.declarations in
  if List.length claims<>4 then failwith "fixture must contain four quotient declarations";
  Printf.printf "let l4_quotient_signature_inputs = [%s];;\n" (String.concat ";\n" claims);
  let eq_name=Wire.dotted_name ["Eq"] in
  let eqs=List.concat_map (function
    | _,Wire.Inductive(types,ctors,_) ->
      List.filter_map (fun (i:Wire.inductive) ->
        if not(Wire.equal_name i.ind_header.name eq_name) then None else
        let u=match i.ind_header.params with [u]->Wire.Param u
          | _ -> failwith "unexpected Eq universe count" in
        let ctor=match List.filter (fun (c:Wire.constructor) -> Wire.equal_name c.induct eq_name) ctors with
          | [c] -> c | _ -> failwith "unexpected Eq constructor count" in
        Some("(" ^ String.concat "," [quote(level u);quote(expr i.ind_header.typ);
          quote(expr ctor.ctor_header.typ)] ^ ")")) types
    | _ -> []) data.Wire.declarations in
  if List.length eqs<>1 then failwith "fixture must contain one Eq family";
  Printf.printf "let l4_quotient_eq_inputs = [%s];;\n" (String.concat ";" eqs)
