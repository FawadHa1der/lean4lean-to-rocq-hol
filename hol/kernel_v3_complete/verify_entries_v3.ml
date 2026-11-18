(* Fresh-session driver for the eight held "655" entry modules of
   kernel_v3_complete (candidate_entry655.ml and entry_*655.ml).
   Run through verify_all_v3.sh, from this directory, by feeding this file to
   hol.sh on stdin. candidate_entry655.ml refuses to load unless
     - it is loaded BEFORE any project (l4_*/L4*/fixture_*/FLAT) source,
     - load_path is exactly [candidate cwd],
     - use_file_raise_failure is true,
   so these modules cannot be loaded by verify_all_v3.ml (which has already
   loaded the project sources); this driver establishes exactly those
   preconditions.
   After each entry module loads, every one of its held cases is executed in
   this same session through v3_case, which repeats the payload validation of
   Candidate_entry655.run (non-empty payload; theorems closed and without
   hypotheses; check_state before and after). Candidate_entry655.run itself is
   one-shot per process ("fresh process required"), so it is not called; the
   per-file case thunks are reproduced verbatim where the file only exposes
   run_entry655. No axioms, no unsound escapes. *)

let v3_frontend_dir =
  try Sys.getenv "LEAN4LEAN_V3_FRONTEND_DIR"
  with Not_found -> failwith "LEAN4LEAN_V3_FRONTEND_DIR is not set";;
Topdirs.dir_directory (Findlib.package_directory "zarith");;
Topfind.load_deeply ["yojson"];;
Topdirs.dir_directory v3_frontend_dir;;
Topdirs.dir_load Format.std_formatter (Filename.concat v3_frontend_dir "wire.cmo");;
Topdirs.dir_load Format.std_formatter (Filename.concat v3_frontend_dir "replay.cmo");;

load_path := [Sys.getcwd ()];;
use_file_raise_failure := true;;
let v3_ok = ref ([]:string list);;
let v3_fail = ref ([]:(string*string) list);;
let v3_try f =
  let t0 = Sys.time () in
  try
    needs f;
    v3_ok := f :: !v3_ok;
    Printf.printf "\nV3_MODULE_OK %s cpu=%.1fs\n%!" f (Sys.time () -. t0)
  with e ->
    let m = Printexc.to_string e in
    v3_fail := (f,m) :: !v3_fail;
    Printf.printf "\nV3_MODULE_FAIL %s : %s\n%!" f m;;
let v3_loaded f = List.mem f !v3_ok;;

v3_try "hol/candidate_entry655.ml";;
set_jrh_lexer;;

let v3_case_ok = ref 0;;
let v3_case_fail = ref ([]:(string*string*string) list);;
let v3_case file label (action:unit -> Candidate_entry655.payload) =
  let t0 = Sys.time () in
  try
    Candidate_entry655.check_state ();
    let payload = action () in
    (match payload with
     | Candidate_entry655.Theorems [] | Candidate_entry655.Native_checks [] ->
         failwith "655: empty evidence payload"
     | Candidate_entry655.Theorems ths -> List.iter (fun th ->
         if hyp th <> [] || frees (concl th) <> [] then
           failwith "655: theorem has hypotheses or free term variables") ths
     | Candidate_entry655.Native_checks _ -> ());
    Candidate_entry655.check_state ();
    incr v3_case_ok;
    Printf.printf "\nV3_CASE_OK %s %s cpu=%.1fs\n%!" file label (Sys.time () -. t0)
  with e ->
    let m = Printexc.to_string e in
    v3_case_fail := (file,label,m) :: !v3_case_fail;
    Printf.printf "\nV3_CASE_FAIL %s %s : %s\n%!" file label m;;

v3_try "hol/entry_flatten650655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_flatten650655.ml" then
  List.iter (fun (l,a) -> v3_case "entry_flatten650655" l a) entry_cases655;;

v3_try "hol/entry_file642655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_file642655.ml" then
  List.iter (fun (l,a) -> v3_case "entry_file642655" l a) entry_cases655;;

v3_try "hol/entry_quotation610655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_quotation610655.ml" then
  List.iter (fun (l,a) -> v3_case "entry_quotation610655" l a) entry_cases655;;

v3_try "hol/entry_reader641643655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_reader641643655.ml" then
  List.iter (fun (l,a) -> v3_case "entry_reader641643655" l a) entry_cases655;;

(* Thunk body copied from entry_closed644655.ml run_entry655. *)
v3_try "hol/entry_closed644655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_closed644655.ml" then
  List.iter (fun label -> v3_case "entry_closed644655" label (fun () ->
    let state = Kernel_compute646.create
      ~conversions:l4_kernel_conversions647
      (l4_kernel_equations647 @ l4_fixture_equations644) in
    Candidate_entry655.Theorems [l4_fixture_prove644 state label]))
    entry_case_names655;;

(* Thunk body copied from entry_controls646655.ml run_entry655. *)
v3_try "hol/entry_controls646655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_controls646655.ml" then
  List.iter (fun label -> v3_case "entry_controls646655" label (fun () ->
    let built = l4_proposed_cases648 () in
    if List.map fst built <> entry_case_names655 then
      failwith "655: controls648 catalogue differs";
    let action = List.assoc label built in
    action ();
    Candidate_entry655.Native_checks
      ["controls646/" ^ label ^ ": original648 native assertions returned; no theorem payload"]))
    entry_case_names655;;

(* Thunk body copied from entry_serialized649655.ml run_entry655. *)
v3_try "hol/entry_serialized649655.ml";;
set_jrh_lexer;;
if v3_loaded "hol/entry_serialized649655.ml" then
  List.iter (fun label -> v3_case "entry_serialized649655" label (fun () ->
    let state = File_certificate649.create () in
    match File_fixtures649.run_case state label with
    | Some theorem -> Candidate_entry655.Theorems [theorem]
    | None -> Candidate_entry655.Native_checks
        ["serialized649/" ^ label ^
         ": original expected Wire-error kind/line/message checks returned; no certificate"]))
    entry_case_names655;;

begin
  Printf.printf "\nV3E_SUMMARY loaded=%d failed=%d total=%d\n%!"
    (List.length !v3_ok) (List.length !v3_fail)
    (List.length !v3_ok + List.length !v3_fail);
  List.iter (fun (f,m) -> Printf.printf "V3E_FAILED %s : %s\n%!" f m) (List.rev !v3_fail);
  Printf.printf "V3E_CASES ok=%d failed=%d\n%!" !v3_case_ok (List.length !v3_case_fail);
  List.iter (fun (f,l,m) -> Printf.printf "V3E_CASE_FAILED %s %s : %s\n%!" f l m)
    (List.rev !v3_case_fail);
  Printf.printf "AXIOMS=%d\n%!" (List.length (axioms ()));
  List.iter (fun th -> Printf.printf "AXIOM %s\n%!" (string_of_thm th)) (axioms ());
  (try check_axioms (); Printf.printf "V3_CHECK_AXIOMS_OK\n%!"
   with Failure m -> Printf.printf "V3_CHECK_AXIOMS_FAILED %s\n%!" m);
  Printf.printf "V3_LOAD_DONE\n%!";
  exit 0
end;;
