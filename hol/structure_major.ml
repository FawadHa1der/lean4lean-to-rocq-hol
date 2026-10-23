(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Pinned Lean4Lean Inductive/Reduce.lean:toCtorWhenStruct. No new object rule. *)
needs "hol/environment_rules.ml";;

let l4_struct_major = new_definition
 `!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
  l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u <=>
    MEM rec env /\ MEM ind env /\ MEM ctor env /\
    l4_entry_tag rec = L4Generated
      (L4RecursorRole [owner] (LENGTH pars) 0 1 nm rs isk F) /\
    LENGTH (l4_entry_params rec) = LENGTH (rus:l4_level list) /\
    LENGTH (prefix:l4_expr list) = LENGTH pars + SUC nm /\
    MEM (L4RecRule (l4_entry_name ctor) nf body) rs /\
    l4_eta_meta ind ctor owner us pars nf /\
    l4_edef env g (l4_apps (L4Const owner us) pars)
      (l4_apps (L4Const owner us) pars) (L4Sort u) /\
    l4_level_nonzero u /\
    l4_edef env g major (l4_eta_expansion (l4_entry_name ctor) owner us pars nf major)
      (l4_apps (L4Const owner us) pars)`;;

let l4_struct_major_equality = prove
 (`!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
    l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u ==>
    l4_edef env g major (l4_eta_expansion (l4_entry_name ctor) owner us pars nf major)
      (l4_apps (L4Const owner us) pars)`,
  SIMP_TAC [l4_struct_major]);;
let l4_struct_major_nonzero = prove
 (`!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
    l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u ==>
    l4_level_nonzero u`,
  SIMP_TAC [l4_struct_major]);;
let l4_struct_major_structure = prove
 (`!env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u.
    l4_struct_major env g rec ind ctor owner rus us pars prefix nf nm rs isk body major u ==>
    l4_eta_meta ind ctor owner us pars nf`,
  SIMP_TAC [l4_struct_major]);;
