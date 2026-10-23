(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE. *)
let l4_projection_meta = new_definition
 `l4_projection_meta ind ctor owner idx us pars indices <=>
    l4_entry_name ind = owner /\
    (?r. l4_entry_tag ind = L4Generated r /\
      l4_proj_ind_meta r (l4_entry_name ctor) (LENGTH (pars:l4_expr list)) (LENGTH (indices:l4_expr list))) /\
    (?r. l4_entry_tag ctor = L4Generated r /\ l4_proj_ctor_meta r owner (LENGTH pars) idx) /\
    l4_entry_params ctor = l4_entry_params ind /\
    LENGTH (l4_entry_params ind) = LENGTH (us:l4_level list)`;;

let l4_eta_meta = new_definition
 `l4_eta_meta ind ctor owner us pars nf <=>
    l4_entry_name ind = owner /\
    (?r. l4_entry_tag ind = L4Generated r /\
      l4_eta_ind_meta r (l4_entry_name ctor) (LENGTH (pars:l4_expr list))) /\
    (?r. l4_entry_tag ctor = L4Generated r /\
      l4_eta_ctor_meta r owner (LENGTH pars) nf) /\
    l4_entry_params ctor = l4_entry_params ind /\
    LENGTH (l4_entry_params ind) = LENGTH (us:l4_level list)`;;
