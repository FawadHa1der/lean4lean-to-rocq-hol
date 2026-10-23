(* Private native frontend bootstrap. *)
let private_axioms = axioms();;
Topdirs.dir_directory (Filename.concat (Sys.getenv "OPAMROOT") "lean4lean/lib/zarith");;
Topdirs.dir_directory (Filename.concat (Sys.getenv "OPAMROOT") "lean4lean/lib/yojson");;
Topdirs.dir_directory "build/frontend";;
#load "zarith.cma";;
#load "yojson.cma";;
#load "unix.cma";;
#load "wire.cmo";;
#load "replay.cmo";;
#load "hol_input.cmo";;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
needs "hol/environment.ml";;
needs "hol/primitive_validation.ml";;
needs "hol/text_validation.ml";;
let private_native_rule_count = List.length(CONJUNCTS l4_edef_RULES);;
let private_admission_rule_count = List.length(CONJUNCTS(SPEC `[]:l4_entry list` l4_evalid_RULES));;
needs "hol/raw_indexed_admission.ml";;
