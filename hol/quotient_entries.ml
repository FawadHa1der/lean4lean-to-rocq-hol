(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Loaded after the environment entry datatype and quotient syntax. *)
let l4_quot_eq_meta = new_definition
 `l4_quot_eq_meta ind ctor u v <=>
    l4_entry_name ind = l4_quot_eq /\
    l4_entry_params ind = [u] /\ l4_entry_params ctor = [v] /\
    (?np ni ns nn rec refl. l4_entry_tag ind =
      L4Generated (L4InductiveRole np ni ns [l4_entry_name ctor] nn rec refl F)) /\
    (?idx np nf. l4_entry_tag ctor =
      L4Generated (L4ConstructorRole l4_quot_eq idx np nf F)) /\
    l4_anon (l4_entry_type ind) = l4_quot_eq_type (L4Param u) /\
    l4_anon (l4_entry_type ctor) = l4_quot_refl_type (L4Param v)`;;

let l4_quot_header = new_definition
 `l4_quot_header d k <=>
    l4_entry_tag d = L4QuotientKind k /\
    l4_entry_name d = l4_quot_name k /\
    LENGTH (l4_entry_params d) = l4_quot_arity k /\
    l4_names_distinct (l4_entry_params d) /\
    l4_entry_body d = L4Sort L4Zero /\
    l4_anon (l4_entry_type d) = l4_quot_signature k
      (L4Param (HD (l4_entry_params d)))
      (if k = L4QuotLift then L4Param (HD (TL (l4_entry_params d))) else L4Zero)`;;

let l4_quot_dependencies = new_definition
 `l4_quot_dependencies env k <=>
    (k = L4QuotType \/
      (?d. MEM d env /\ l4_quot_header d L4QuotType)) /\
    (k = L4QuotInd ==>
      (?d. MEM d env /\ l4_quot_header d L4QuotCtor))`;;

let l4_quot_header_not_axiom = prove
 (`!d k. l4_quot_header d k ==> ~(l4_entry_tag d = L4AxiomKind)`,
  SIMP_TAC [l4_quot_header;distinctness "l4_entry_kind"]);;

let l4_quot_lift_redex = new_definition
 `l4_quot_lift_redex u v a r b f h x =
    l4_apps (L4Const (l4_quot_name L4QuotLift) [u;v])
      [a;r;b;f;h;l4_quot_app L4QuotCtor u [a;r;x]]`;;
let l4_quot_ind_redex = new_definition
 `l4_quot_ind_redex u a r b f x =
    l4_apps (L4Const (l4_quot_name L4QuotInd) [u])
      [a;r;b;f;l4_quot_app L4QuotCtor u [a;r;x]]`;;
