(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment_rules.ml";;
let l4_mindex_checked = new_definition
 `!policy env ps pars u bs large claims.
    l4_mindex_checked policy env ps pars u bs large claims <=>
    l4_evalid policy env /\ l4_mindex_ok env ps pars u bs large claims /\
    l4_evalid policy (APPEND (l4_mindex_generated ps pars u bs large) env)`;;
let l4_mindex_checked_metadata = prove
 (`!policy env ps pars u bs large claims.
    l4_mindex_checked policy env ps pars u bs large claims ==>
    l4_metadata_matches claims (l4_mindex_generated ps pars u bs large)`,
  SIMP_TAC [l4_mindex_checked;l4_mindex_ok]);;
let l4_mindex_checked_fields = prove
 (`!policy env ps pars u bs large claims.
    l4_mindex_checked policy env ps pars u bs large claims ==>
    ALL (\c. l4_mindex_fields_valid (APPEND (l4_mindex_headers ps pars u bs) env)
      bs ps (LENGTH pars) u (REVERSE (MAP SND pars)) 0
      (l4_mindex_fields (SND c))) (l4_mindex_flat bs 0)`,
  SIMP_TAC [l4_mindex_checked;l4_mindex_ok]);;
let l4_mindex_fields_positive = prove
 (`!env bs ps p u. !g j fs.
    l4_mindex_fields_valid env bs ps p u g j fs ==> ALL (l4_mindex_positive bs) fs`,
  REPLICATE_TAC 5 GEN_TAC THEN MATCH_MP_TAC (SPECL
    [`env:l4_entry list`;`bs:l4_mindex_family list`;`ps:l4_name list`;`p:num`;`u:l4_level`]
    l4_mindex_fields_valid_INDUCT) THEN SIMP_TAC [ALL]);;
