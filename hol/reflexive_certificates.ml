(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
needs "hol/environment_rules.ml";;

let l4_index_fields_positive = prove
 (`!env i ps p ni u. !g j fs vs.
    l4_index_fields_valid env i ps p ni u g j fs vs ==>
    ALL (l4_index_positive i ni) fs`,
  REPLICATE_TAC 6 GEN_TAC THEN
  MATCH_MP_TAC (SPECL [`env:l4_entry list`;`i:l4_name`;`ps:l4_name list`;
    `p:num`;`ni:num`;`u:l4_level`] l4_index_fields_valid_INDUCT) THEN
  SIMP_TAC [ALL]);;

let l4_index_function_positive = prove
 (`!i ni ds xs. l4_index_positive i ni (L4IndexFunction ds xs) ==>
    ALL (l4_without_const i) ds /\ LENGTH xs = ni /\ ALL (l4_without_const i) xs`,
  SIMP_TAC [l4_index_positive]);;

let l4_index_checked_fields = prove
 (`!policy env i ps pars inds u cs vss large k claims.
    l4_index_checked policy env i ps pars inds u cs vss large k claims ==>
    ALL2 (\c vs. l4_index_fields_valid (CONS (l4_index_header i ps pars inds u cs) env)
      i ps (LENGTH pars) (LENGTH inds) u (REVERSE (MAP SND pars)) 0
      (l4_index_fields c) vs) cs vss`,
  SIMP_TAC [l4_index_checked;l4_index_ok]);;

let l4_eta_recursive_excluded = prove
 (`!p j ns cs k x u n ps ty value ctor owner us pars nf.
    ~l4_eta_meta (L4Entry (L4Generated (L4InductiveRole p j ns cs k T x u))
      n ps ty value) ctor owner us pars nf`,
  REWRITE_TAC [l4_eta_meta;l4_entry_tag;injectivity "l4_entry_kind"] THEN
  MESON_TAC [l4_eta_ind_meta]);;
