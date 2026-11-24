(* Fresh-session driver for the three end-to-end executable soundness modules
   of kernel_v3_complete (verify_expr973.ml, verify_typechecker974.ml,
   verify_environment975.ml), porting Lean4Lean/Verify/ and
   rocq/Verify{Expr,TypeChecker,Environment}.v to HOL Light.
   Run through verify_all_v3.sh, from this directory, by feeding this file to
   hol.sh on stdin. Each module is loaded with use_file_raise_failure := true
   so any failure is reported as V3_MODULE_FAIL and never silently absorbed.
   Zero new axioms, zero unsound escapes. *)

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

v3_try "hol/verify_expr973.ml";;
set_jrh_lexer;;
v3_try "hol/verify_typechecker974.ml";;
set_jrh_lexer;;
v3_try "hol/verify_environment975.ml";;
set_jrh_lexer;;

begin
  Printf.printf "\nV3S_SUMMARY loaded=%d failed=%d total=%d\n%!"
    (List.length !v3_ok) (List.length !v3_fail)
    (List.length !v3_ok + List.length !v3_fail);
  List.iter (fun (f,m) -> Printf.printf "V3S_FAILED %s : %s\n%!" f m) (List.rev !v3_fail);
  Printf.printf "AXIOMS=%d\n%!" (List.length (axioms ()));
  List.iter (fun th -> Printf.printf "AXIOM %s\n%!" (string_of_thm th)) (axioms ());
  (try check_axioms (); Printf.printf "V3_CHECK_AXIOMS_OK\n%!"
   with Failure m -> Printf.printf "V3_CHECK_AXIOMS_FAILED %s\n%!" m);
  Printf.printf "V3_LOAD_DONE\n%!";
  exit 0
end;;
