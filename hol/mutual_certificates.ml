(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment_rules.ml";;
let l4_mutual_checked = new_definition
 `!policy env ps pars u bs large claims.
    l4_mutual_checked policy env ps pars u bs large claims <=>
    l4_evalid policy env /\ l4_mutual_ok env ps pars u bs large claims /\
    l4_evalid policy (APPEND (l4_mutual_generated ps pars u bs large) env)`;;
let l4_mutual_checked_metadata = prove
 (`!policy env ps pars u bs large claims.
    l4_mutual_checked policy env ps pars u bs large claims ==>
    l4_metadata_matches claims (l4_mutual_generated ps pars u bs large)`,
  SIMP_TAC [l4_mutual_checked;l4_mutual_ok]);;
let l4_mutual_checked_fields = prove
 (`!policy env ps pars u bs large claims.
    l4_mutual_checked policy env ps pars u bs large claims ==>
    ALL (\c. l4_mutual_fields_valid (APPEND (l4_mutual_headers ps pars u bs) env)
      (MAP l4_mutual_name bs) ps (LENGTH pars) u (REVERSE (MAP SND pars)) 0
      (l4_mutual_fields (SND c))) (l4_mutual_flat bs 0)`,
  SIMP_TAC [l4_mutual_checked;l4_mutual_ok]);;
let l4_mutual_fields_positive = prove
 (`!env ns ps p u. !g j fs.
    l4_mutual_fields_valid env ns ps p u g j fs ==>
    ALL (l4_mutual_positive ns) fs`,
  REPLICATE_TAC 5 GEN_TAC THEN MATCH_MP_TAC (SPECL
    [`env:l4_entry list`;`ns:l4_name list`;`ps:l4_name list`;`p:num`;`u:l4_level`]
    l4_mutual_fields_valid_INDUCT) THEN SIMP_TAC [ALL]);;
let l4_mutual_recursive_positive = prove
 (`!ns i ds. l4_mutual_positive ns (L4MutualRec i ds) ==>
    MEM i ns /\ ALL (l4_mutual_without ns) ds`,
  SIMP_TAC [l4_mutual_positive]);;
