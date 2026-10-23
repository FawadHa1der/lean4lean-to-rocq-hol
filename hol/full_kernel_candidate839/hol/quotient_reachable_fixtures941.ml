(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED / UNRUN. Five held reachable-integration attempts.
   No case executes at load. No case theorem/expected truth enters the compset.
   Requires genuine post934 production equations; see ../HANDOFF941.txt. *)
needs "hol/quotient_reachable_data941.ml";;
needs "hol/kernel_compute646.ml";;
needs "hol/kernel_equations647.ml";;

let l4_quotient_reachable_cases941 =
 ["eq_prefix941",
   `match l4_q941_eq_export with
    | L4KAccept491 generated941 ->
        (match l4_check_file642 256 (l4_q941_prefix generated941) [L4FileSingle642 0] with
         | L4KAccept491 env941 -> l4_q941_eq_environment generated941 env941
         | _ -> F)
    | _ -> F`;
  "canonical_type941",
   `match l4_q941_eq_export with
    | L4KAccept491 generated941 ->
        (match l4_check_file642 256 (l4_q941_prefix generated941) [L4FileSingle642 0] with
         | L4KAccept491 env941 ->
             l4_q941_eq_environment generated941 env941 /\
             l4_file_admit_single642 256 env941 (l4_q941_quot_row L4KQType493) =
               L4KAccept491 (CONS (l4_canonical_quotient608 L4KQType493) env941) /\
             l4_check_file642 256 (l4_q941_type_input generated941)
               [L4FileSingle642 0;L4FileSingle642 1] =
               L4KAccept491 (CONS (l4_canonical_quotient608 L4KQType493) env941)
         | _ -> F)
    | _ -> F`;
  "canonical_type_ctor941",
   `match l4_q941_eq_export with
    | L4KAccept491 generated941 ->
        (match l4_check_file642 256 (l4_q941_prefix generated941) [L4FileSingle642 0] with
         | L4KAccept491 eq_env941 ->
             l4_q941_eq_environment generated941 eq_env941 /\
             (match l4_check_file642 256 (l4_q941_type_input generated941)
               [L4FileSingle642 0;L4FileSingle642 1] with
              | L4KAccept491 type_env941 ->
                  type_env941 = CONS (l4_canonical_quotient608 L4KQType493) eq_env941 /\
                  l4_quotient_dependencies839 type_env941 L4KQCtor493 /\
                  l4_file_admit_single642 256 type_env941 (l4_q941_quot_row L4KQCtor493) =
                    L4KAccept491 (CONS (l4_canonical_quotient608 L4KQCtor493) type_env941) /\
                  l4_check_file642 256 (l4_q941_ctor_input generated941)
                    [L4FileSingle642 0;L4FileSingle642 1;L4FileSingle642 2] =
                    L4KAccept491 (CONS (l4_canonical_quotient608 L4KQCtor493) type_env941)
              | _ -> F)
         | _ -> F)
    | _ -> F`;
  "axiom_impostor_prefix941",
   `match l4_q941_eq_export with
    | L4KAccept491 generated941 ->
        (match l4_check_file642 256 (l4_q941_prefix generated941) [L4FileSingle642 0] with
         | L4KAccept491 eq_env941 ->
             l4_q941_eq_environment generated941 eq_env941 /\
             (match l4_check_file642 256 (l4_q941_impostor_prefix generated941)
               [L4FileSingle642 0;L4FileSingle642 1] with
              | L4KAccept491 bad_env941 ->
                  bad_env941 = CONS l4_q941_impostor_record eq_env941 /\
                  l4_file_admit_single642 256 eq_env941 l4_q941_impostor_row =
                    L4KAccept491 bad_env941 /\
                  l4_kfind_decl493 bad_env941 l4_q_name608 = SOME l4_q941_impostor_record /\
                  l4_kdecl_kind493 l4_q941_impostor_record = L4KDAssumption493 /\
                  l4_kfind_decl493 bad_env941 l4_q_mk_name608 = NONE /\
                  ~l4_quotient_dependencies839 bad_env941 L4KQCtor493
              | _ -> F)
         | _ -> F)
    | _ -> F`;
  "axiom_impostor_ctor_reject941",
   `match l4_q941_eq_export with
    | L4KAccept491 generated941 ->
        (match l4_check_file642 256 (l4_q941_prefix generated941) [L4FileSingle642 0] with
         | L4KAccept491 eq_env941 ->
             l4_q941_eq_environment generated941 eq_env941 /\
             (match l4_check_file642 256 (l4_q941_impostor_prefix generated941)
               [L4FileSingle642 0;L4FileSingle642 1] with
              | L4KAccept491 bad_env941 ->
                  let ctor941 = l4_canonical_quotient608 L4KQCtor493 in
                  bad_env941 = CONS l4_q941_impostor_record eq_env941 /\
                  l4_kfind_decl493 bad_env941 l4_q_name608 = SOME l4_q941_impostor_record /\
                  l4_kfind_decl493 bad_env941 l4_q_mk_name608 = NONE /\
                  l4_quotient_check_eq608 bad_env941 = L4KAccept491 one /\
                  l4_check_header607 256 bad_env941 (l4_kdecl_name493 ctor941)
                    (l4_kdecl_params493 ctor941) (l4_kdecl_type493 ctor941) = L4KAccept491 one /\
                  l4_kdecl_name493 ctor941 = l4_q_mk_name608 /\
                  LENGTH (l4_kdecl_params493 ctor941) = 1 /\
                  l4_kexpr_eqb480
                    (l4_ksubst_levels488 (l4_kdecl_params493 ctor941)
                      (MAP L4KParam447 (l4_kdecl_params493 ctor941)) (l4_kdecl_type493 ctor941))
                    (l4_kdecl_type493 ctor941) /\
                  ~l4_quotient_dependencies839 bad_env941 L4KQCtor493 /\
                  l4_admit_quotient608 256 bad_env941 (l4_kdecl_name493 ctor941)
                    (l4_kdecl_params493 ctor941) (l4_kdecl_type493 ctor941) L4KQCtor493 =
                    L4KReject491 L4KMalformedDeclaration491 /\
                  l4_file_admit_single642 256 bad_env941 (l4_q941_quot_row L4KQCtor493) =
                    L4KReject491 L4KMalformedDeclaration491 /\
                  l4_q941_file_gates (l4_q941_impostor_file generated941)
                    [L4FileSingle642 0;L4FileSingle642 1;L4FileSingle642 2] /\
                  l4_check_file642 256 (l4_q941_impostor_file generated941)
                    [L4FileSingle642 0;L4FileSingle642 1;L4FileSingle642 2] =
                    L4KReject491 L4KMalformedDeclaration491
              | _ -> F)
         | _ -> F)
    | _ -> F`];;

(* Same theorem-producing engine and canonical conversions as839/644.
   Callback only performs the parent's bounded check; it cannot supply a verdict.
   Undefined/stuck computation, Reject/Decline in a positive prefix, or any false
   assertion is a failure, never a skipped case or an expected rejection. *)
let l4_quotient_reachable_fixtures941 check =
  check ();
  let state = Kernel_compute646.create ~conversions:l4_kernel_conversions647
    (l4_q941_equations @ l4_kernel_equations647) in
  check ();
  List.map (fun (label941,query941) -> label941,(fun () ->
    check ();
    let actual941,theorem941 = Kernel_compute646.boolean state query941 in
    if not actual941 || hyp theorem941 <> [] || frees (concl theorem941) <> [] ||
       not (is_eq (concl theorem941)) then
      failwith ("941: false, open or nonequational result: " ^ label941);
    let left941,right941 = dest_eq (concl theorem941) in
    if not (aconv left941 query941) || not (aconv right941 `T`) then
      failwith ("941: wrong query or non-true literal: " ^ label941);
    check ();
    theorem941)) l4_quotient_reachable_cases941;;
