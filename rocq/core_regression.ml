(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Test driver only. Logical decisions are computed by extracted Gallina. *)
module C = Lean_core

let rec nat n =
  if n < 0 then invalid_arg "negative test natural"
  else if n = 0 then C.O else C.S (nat (n - 1))

let rec check_extracted index = function
  | C.Nil -> index
  | C.Cons (C.True, rest) -> check_extracted (index + 1) rest
  | C.Cons (C.False, _) -> failwith (Printf.sprintf "extracted regression %d failed" index)

let fuel = nat 256
let x = C.NameNum (C.NameAnon, C.N0)
let y = C.NameNum (C.NameAnon, C.Npos C.XH)
let rho a b n =
  match C.name_eqb n x, C.name_eqb n y with
  | C.True, _ -> nat a
  | _, C.True -> nat b
  | _ -> C.O

let valuations =
  List.concat_map (fun a -> List.map (fun b -> rho a b) [0; 1; 2; 4; 9]) [0; 1; 2; 4; 9]

let normalization_samples = ref 0
let check_normalization u =
  match C.normalize_level fuel u with
  | C.Accept atoms ->
      List.iter (fun rho ->
        if C.level_eval rho u <> C.sublevels_eval rho atoms then
          failwith "guarded universe normalization disagrees with semantic evaluator";
        incr normalization_samples) valuations
  | _ -> failwith "normalization unexpectedly failed at sufficient fuel"

let equality_checks = ref 0
let check_equation a b =
  incr equality_checks;
  match C.level_equiv fuel a b with
  | C.Accept C.True ->
      List.iter (fun rho ->
        if C.level_eval rho a <> C.level_eval rho b then
          failwith "accepted universe equality disagrees with semantic evaluator") valuations
  | _ -> failwith "expected universe identity was not accepted"

let random = Random.State.make [|8223; 20260929|]
let rec generated depth =
  if depth = 0 then
    match Random.State.int random 3 with
    | 0 -> C.LZero | 1 -> C.LParam x | _ -> C.LParam y
  else
    match Random.State.int random 5 with
    | 0 -> C.LZero
    | 1 -> C.LParam (if Random.State.bool random then x else y)
    | 2 -> C.LSucc (generated (depth - 1))
    | 3 -> C.LMax (generated (depth - 1), generated (depth - 1))
    | _ -> C.LIMax (generated (depth - 1), generated (depth - 1))

let rec extracted_list = function
  | [] -> C.Nil | x :: xs -> C.Cons (x, extracted_list xs)

let rec generated_expr size depth =
  let child () = generated_expr (size - 1) depth in
  if size = 0 then C.EBVar (nat (Random.State.int random depth)) else
  match Random.State.int random 9 with
  | 0 -> C.EBVar (nat (Random.State.int random depth))
  | 1 -> C.ESort C.LZero
  | 2 -> C.EConst (x, C.Nil)
  | 3 -> C.EApp (child (), child ())
  | 4 -> C.ELam (x, C.BDefault, child (), generated_expr (size - 1) (depth + 1))
  | 5 -> C.EPi (x, C.BImplicit, child (), generated_expr (size - 1) (depth + 1))
  | 6 -> C.ELet (x, child (), child (), generated_expr (size - 1) (depth + 1), C.False)
  | 7 -> C.EProj (x, C.O, child ())
  | _ -> C.EMData (child ())

let check_substitution () =
  for _ = 1 to 4096 do
    let depth = 1 + Random.State.int random 4 in
    let cutoff = Random.State.int random 4 in
    let count = Random.State.int random 5 in
    let values = List.init count (fun _ -> generated_expr 3 depth) in
    let body = generated_expr 4 (cutoff + count + depth) in
    let expected, _ = List.fold_left (fun (e, index) value ->
      C.subst (nat index) value e, index - 1)
      (body, cutoff + count - 1) (List.rev values) in
    let actual = C.subst_many (nat cutoff) (extracted_list values) body in
    if actual <> expected then failwith "batched substitution disagrees with sequential substitution";
    if C.scoped (nat (cutoff + depth)) actual <> C.True then
      failwith "batched substitution escaped its output scope"
  done

let () =
  let direct = check_extracted 0 (C.regression_checks C.Tt) +
    check_extracted 0 (C.extension_checks C.Tt) +
    check_extracted 0 (C.performance_checks C.Tt) in
  for _ = 1 to 256 do
    let a = generated 5 and b = generated 5 and c = generated 5 in
    List.iter check_normalization [a; b; c];
    check_equation (C.LMax (a,b)) (C.LMax (b,a));
    check_equation (C.LIMax (a,C.LZero)) C.LZero;
    check_equation (C.LIMax (a,a)) a;
    check_equation (C.LSucc (C.LMax (a,b))) (C.LMax (C.LSucc a,C.LSucc b));
    check_equation (C.LIMax (a,C.LMax (b,c)))
      (C.LMax (C.LIMax (a,b),C.LIMax (a,c)));
    check_equation (C.LIMax (a,C.LIMax (b,c)))
      (C.LMax (C.LIMax (a,c),C.LIMax (b,c)))
  done;
  check_substitution ();
  Printf.printf "%d extracted core checks; %d normalization valuation checks; %d universe identities; 4096 substitution comparisons passed\n"
    direct !normalization_samples !equality_checks
