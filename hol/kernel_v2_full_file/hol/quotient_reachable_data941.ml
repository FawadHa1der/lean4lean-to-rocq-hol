(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED / UNRUN. Post934 test data, not checker rules.
   Eq seed adapted from rocq/MetadataFixtures.v (Metadata.eq_spec).
   File envelope follows full_file_data644.ml. See ../HANDOFF941.txt.
   Generated metadata is input DATA, never a directly installed environment. *)
needs "hol/file_driver642.ml";;
needs "hol/quotient_dependencies839.ml";;

let l4_q941_u = new_definition
 `l4_q941_u = L4String L4Anonymous [117]`;;
let l4_q941_refl = new_definition
 `l4_q941_refl = L4String l4_q_eq_name608 [114;101;102;108]`;;
let l4_q941_eq_spec = new_definition
 `l4_q941_eq_spec = L4KIndSpec493
   (L4KDeclaration493 l4_q_eq_name608 [l4_q941_u]
     (l4_quotient_eq_type608 (L4KParam447 l4_q941_u)) NONE
     (L4KDInductive493 (L4KInductiveData493 2 0 [l4_q_eq_name608]
       [l4_q941_refl] 0 F F F)) L4KHintOpaque493)
   [L4KDeclaration493 l4_q941_refl [l4_q941_u]
     (l4_quotient_eq_refl_type608 (L4KParam447 l4_q941_u)) NONE
     (L4KDConstructor493 (L4KConstructorData493 l4_q_eq_name608 0 2 0 F))
     L4KHintOpaque493]`;;

(* The zero-index seed is not claimed to be valid exported Eq metadata.
   Actual631 derives indices/recursor metadata. Failure stays a result, never [].
   256 is the existing Metadata fixture fuel, not a measured sufficient bound. *)
let l4_q941_eq_export = new_definition
 `l4_q941_eq_export =
   l4_derive_inductive631 256 [] [l4_q941_u] 2 [l4_q941_eq_spec]`;;
let l4_q941_eq_row = new_definition
 `l4_q941_eq_row generated941 = L4FileInductive642
   (FILTER (\declaration941. match l4_kdecl_kind493 declaration941 with
     | L4KDInductive493 info941 -> T | _ -> F) generated941)
   (FILTER (\declaration941. match l4_kdecl_kind493 declaration941 with
     | L4KDConstructor493 info941 -> T | _ -> F) generated941)
   (FILTER (\declaration941. match l4_kdecl_kind493 declaration941 with
     | L4KDRecursor493 info941 -> T | _ -> F) generated941)`;;
let l4_q941_input = new_definition
 `l4_q941_input rows941 =
   L4FileInput642 [51;46;49;46;48] [102;105;120;116;117;114;101;57;52;49]
     [] 0 0 0 rows941`;;
let l4_q941_prefix = new_definition
 `l4_q941_prefix generated941 = l4_q941_input [(1,l4_q941_eq_row generated941)]`;;
let l4_q941_quot_row = new_definition
 `l4_q941_quot_row kind941 =
   let canonical941 = l4_canonical_quotient608 kind941 in
   L4FileQuotient642 (l4_kdecl_name493 canonical941)
     (l4_kdecl_params493 canonical941) (l4_kdecl_type493 canonical941) kind941`;;
let l4_q941_type_input = new_definition
 `l4_q941_type_input generated941 = l4_q941_input
   [(1,l4_q941_eq_row generated941);(2,l4_q941_quot_row L4KQType493)]`;;
let l4_q941_ctor_input = new_definition
 `l4_q941_ctor_input generated941 = l4_q941_input
   [(1,l4_q941_eq_row generated941);(2,l4_q941_quot_row L4KQType493);
    (3,l4_q941_quot_row L4KQCtor493)]`;;

let l4_q941_impostor_row = new_definition
 `l4_q941_impostor_row =
   let canonical941 = l4_canonical_quotient608 L4KQType493 in
   L4FileOrdinary642
     (L4InputAxiom607 (l4_kdecl_name493 canonical941)
       (l4_kdecl_params493 canonical941) (l4_kdecl_type493 canonical941) F) []`;;
(* Expected inserted record, used only on assertion RHSs, not as an environment
   supplied to admission. This object-language input axiom is not a HOL axiom. *)
let l4_q941_impostor_record = new_definition
 `l4_q941_impostor_record =
   let canonical941 = l4_canonical_quotient608 L4KQType493 in
   L4KDeclaration493 (l4_kdecl_name493 canonical941)
     (l4_kdecl_params493 canonical941) (l4_kdecl_type493 canonical941)
     NONE L4KDAssumption493 L4KHintOpaque493`;;
let l4_q941_impostor_prefix = new_definition
 `l4_q941_impostor_prefix generated941 = l4_q941_input
   [(1,l4_q941_eq_row generated941);(2,l4_q941_impostor_row)]`;;
let l4_q941_impostor_file = new_definition
 `l4_q941_impostor_file generated941 = l4_q941_input
   [(1,l4_q941_eq_row generated941);(2,l4_q941_impostor_row);
    (3,l4_q941_quot_row L4KQCtor493)]`;;

(* Assertions only. No observation below supplies a verdict to the checker. *)
let l4_q941_eq_environment = new_definition
 `l4_q941_eq_environment generated941 env941 <=>
   env941 = generated941 /\
   MAP l4_kdecl_name493 env941 =
     [l4_nested_rec_name437 l4_q_eq_name608;l4_q941_refl;l4_q_eq_name608] /\
   l4_quotient_check_eq608 env941 = L4KAccept491 one /\
   (match l4_kfind_decl493 env941 l4_q_eq_name608 with
    | SOME declaration941 ->
        (match l4_kdecl_kind493 declaration941 with
         | L4KDInductive493 info941 ->
             l4_kind_num_params493 info941 = 2 /\ l4_kind_num_indices493 info941 = 1
         | _ -> F)
    | NONE -> F)`;;
let l4_q941_file_gates = new_definition
 `l4_q941_file_gates input941 batches941 <=>
   l4_names_unique437 (l4_kflatten516
     (MAP (\row941. l4_file_decl_names642 (SND row941)) (l4_file_rows642 input941))) /\
   l4_file_coverage642 (LENGTH (l4_file_rows642 input941)) batches941`;;

let l4_q941_equations =
 [l4_q941_u;l4_q941_refl;l4_q941_eq_spec;l4_q941_eq_export;l4_q941_eq_row;
  l4_q941_input;l4_q941_prefix;l4_q941_quot_row;l4_q941_type_input;
  l4_q941_ctor_input;l4_q941_impostor_row;l4_q941_impostor_record;
  l4_q941_impostor_prefix;l4_q941_impostor_file;l4_q941_eq_environment;
  l4_q941_file_gates];;
