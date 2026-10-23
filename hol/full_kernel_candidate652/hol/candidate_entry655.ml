(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD SOURCE ONLY / UNCOMPILED. Load after authenticated stock bootstrap,
   BEFORE project sources. This records no grant and runs no selected case. *)
unset_jrh_lexer;;

module Candidate_entry655 : sig
  type payload = Theorems of thm list | Native_checks of string list
  exception State_changed of string
  exception Failure_with_state_change of exn * exn
  val check_state : unit -> unit
  val run : (string * (unit -> payload)) list -> string -> payload
end = struct
  type payload = Theorems of thm list | Native_checks of string list
  exception State_changed of string
  exception Failure_with_state_change of exn * exn

  let candidate_root = Sys.getcwd ()
  let baseline_axioms = axioms ()
  let selected = ref false
  let prefix p s = String.length s >= String.length p &&
    String.sub s 0 (String.length p) = p
  let project_name s =
    s = "FLAT" || prefix "l4_" s || prefix "L4" s || prefix "fixture_" s

  let check_state () =
    if Sys.getcwd () <> candidate_root || !load_path <> [candidate_root] then
      raise (State_changed "655: candidate cwd/load_path changed");
    if not !use_file_raise_failure then
      raise (State_changed "655: loader must raise on included-file failure");
    if axioms () <> baseline_axioms then
      raise (State_changed "655: HOL axiom list changed")

  let () =
    check_state ();
    if List.exists (fun (n,_) -> project_name n) (constants ()) ||
       List.exists (fun (n,_) -> project_name n) (types ()) then
      raise (State_changed "655: preloaded project/fixture/FLAT namespace")

  let run cases name =
    check_state ();
    if !selected then failwith "655: selected entry already invoked; fresh process required";
    let action =
      match List.filter (fun (label,_) -> label = name) cases with
      | [_,f] -> f
      | [] -> failwith ("655: unknown case: " ^ name)
      | _ -> failwith ("655: duplicate case: " ^ name) in
    selected := true;
    try
      let payload = action () in
      (match payload with
       | Theorems [] | Native_checks [] -> failwith "655: empty evidence payload"
       | Theorems ths -> List.iter (fun th ->
           if hyp th <> [] || frees (concl th) <> [] then
             failwith "655: theorem has hypotheses or free term variables") ths
       | Native_checks _ -> ());
      check_state ();
      payload
    with original ->
      (try check_state () with changed ->
         raise (Failure_with_state_change (original,changed)));
      raise original
end;;

set_jrh_lexer;;
