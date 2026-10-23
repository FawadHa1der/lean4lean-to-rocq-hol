(* Tests only; no checker verdict is delegated or supplied by this driver. *)
module C = String_parity
let rec unpack = function C.Nil -> [] | C.Cons (x,xs) -> x :: unpack xs
let tag = function
  | C.Accept C.Tt -> "accept"
  | C.Reject C.NotDefinitionallyEqual -> "not-defeq"
  | C.Reject C.TypeMismatch -> "type-mismatch"
  | C.Reject _ -> "unexpected-reject"
  | C.Decline _ -> "decline"
let () =
  let mode = Sys.argv.(1) in
  let gates = unpack (C.sp_gate_results C.Tt) in
  if List.length gates <> 14 || not (List.for_all ((=) C.True) gates) then
    failwith "positive environment/typing gate failed; observations are not covered";
  let initial = match mode with
    | "base" -> List.init 14 (fun _ -> "accept")
    | "candidate" -> List.init 6 (fun _ -> "not-defeq") @ List.init 8 (fun _ -> "accept")
    | _ -> invalid_arg "expected base or candidate" in
  let expected = initial @ List.init 4 (fun _ -> "not-defeq") @
    [if mode="base" then "accept" else "type-mismatch";
     "accept"; "type-mismatch"; "type-mismatch"] in
  let actual = List.map tag (unpack (C.sp_observations C.Tt)) in
  List.iteri (fun i value -> Printf.printf "%02d %s\n" i value) actual;
  if actual <> expected then failwith "native String parity observation mismatch";
  Printf.printf "PASS %s: %d positive gates; %d observations\n" mode (List.length gates) (List.length actual)
