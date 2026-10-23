(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Operational projection checks follow pinned TypeChecker.lean:inferProj.
   These definitions do not establish correspondence to recursor expansion. *)
needs "hol/inductive_syntax.ml";;

let l4_uses_bound = new_recursive_definition l4_expr_RECURSION
 `(l4_uses_bound (L4BVar j) k <=> j = k) /\
  (l4_uses_bound (L4Sort u) k <=> F) /\
  (l4_uses_bound (L4Const n us) k <=> F) /\
  (l4_uses_bound (L4App f a) k <=> l4_uses_bound f k \/ l4_uses_bound a k) /\
  (l4_uses_bound (L4Lam n a b) k <=> l4_uses_bound a k \/ l4_uses_bound b (SUC k)) /\
  (l4_uses_bound (L4Pi n a b) k <=> l4_uses_bound a k \/ l4_uses_bound b (SUC k)) /\
  (l4_uses_bound (L4Let n a v b) k <=>
    l4_uses_bound a k \/ l4_uses_bound v k \/ l4_uses_bound b (SUC k)) /\
  (l4_uses_bound (L4NatLit lit) k <=> F) /\
  (l4_uses_bound (L4StrLit chars) k <=> F) /\
  (l4_uses_bound (L4Proj owner idx major) k <=> l4_uses_bound major k)`;;
let l4_pi_parts = new_recursive_definition l4_expr_RECURSION
 `(l4_pi_parts (L4BVar j) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4Sort u) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4Const n us) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4App f a) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4Lam n a b) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4Pi n a b) = (T,a,b)) /\
  (l4_pi_parts (L4Let n a v b) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4NatLit lit) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4StrLit chars) = (F,L4Sort L4Zero,L4Sort L4Zero)) /\
  (l4_pi_parts (L4Proj owner idx major) = (F,L4Sort L4Zero,L4Sort L4Zero))`;;
let l4_is_pi = new_definition `l4_is_pi e <=> FST (l4_pi_parts e)`;;
let l4_pi_domain = new_definition `l4_pi_domain e = FST (SND (l4_pi_parts e))`;;
let l4_pi_body = new_definition `l4_pi_body e = SND (SND (l4_pi_parts e))`;;
let l4_proj_drop = new_recursive_definition list_RECURSION
 `(l4_proj_drop [] r = r) /\
  (l4_proj_drop (CONS a args) r = l4_proj_drop args (l4_inst a (l4_pi_body r)))`;;
let l4_proj_drop_ok = new_recursive_definition list_RECURSION
 `(l4_proj_drop_ok [] r <=> T) /\
  (l4_proj_drop_ok (CONS a args) r <=> l4_is_pi r /\
    l4_proj_drop_ok args (l4_inst a (l4_pi_body r)))`;;
let l4_proj_scan = new_recursive_definition num_RECURSION
 `(l4_proj_scan 0 owner major j r = [(r,T)]) /\
  (l4_proj_scan (SUC k) owner major j r =
    CONS (r,l4_uses_bound (l4_pi_body r) 0)
      (l4_proj_scan k owner major (SUC j)
        (l4_inst (L4Proj owner j major) (l4_pi_body r))))`;;
let l4_proj_selected = new_definition
 `l4_proj_selected scan = l4_pi_domain (FST (HD (REVERSE scan)))`;;
let l4_proj_ind_meta = new_recursive_definition l4_role_RECURSION
 `(l4_proj_ind_meta (L4InductiveRole p j ns cs k r x u) c np ni <=>
    cs = [c] /\ p = np /\ j = ni) /\
  (l4_proj_ind_meta (L4ConstructorRole i j p f u) c np ni <=> F) /\
  (l4_proj_ind_meta (L4RecursorRole ns p j m k rs x u) c np ni <=> F)`;;
let l4_proj_ctor_meta = new_recursive_definition l4_role_RECURSION
 `(l4_proj_ctor_meta (L4InductiveRole p j ns cs k r x u) owner np idx <=> F) /\
  (l4_proj_ctor_meta (L4ConstructorRole i j p f u) owner np idx <=>
    i = owner /\ p = np /\ idx < f) /\
  (l4_proj_ctor_meta (L4RecursorRole ns p j m k rs x u) owner np idx <=> F)`;;
let l4_proj_ctor_args = new_recursive_definition l4_role_RECURSION
 `(l4_proj_ctor_args (L4InductiveRole p j ns cs k r x u) owner idx pars fields <=> F) /\
  (l4_proj_ctor_args (L4ConstructorRole i j p f u) owner idx pars fields <=>
    i = owner /\ p = LENGTH (pars:l4_expr list) /\
    f = LENGTH (fields:l4_expr list) /\ idx < f) /\
  (l4_proj_ctor_args (L4RecursorRole ns p j m k rs x u) owner idx pars fields <=> F)`;;

(* TypeChecker.tryEtaStructCore / isDefEqUnitLike use this precise header
   guard; indexed or recursive single-constructor types are not structures. *)
let l4_eta_ind_meta = new_recursive_definition l4_role_RECURSION
 `(l4_eta_ind_meta (L4InductiveRole p j ns cs k r x u) c np <=>
    cs = [c] /\ p = np /\ j = 0 /\ ~r) /\
  (l4_eta_ind_meta (L4ConstructorRole i j p f u) c np <=> F) /\
  (l4_eta_ind_meta (L4RecursorRole ns p j m k rs x u) c np <=> F)`;;
let l4_eta_ctor_meta = new_recursive_definition l4_role_RECURSION
 `(l4_eta_ctor_meta (L4InductiveRole p j ns cs k r x u) owner np nf <=> F) /\
  (l4_eta_ctor_meta (L4ConstructorRole i j p f u) owner np nf <=>
    i = owner /\ p = np /\ f = nf) /\
  (l4_eta_ctor_meta (L4RecursorRole ns p j m k rs x u) owner np nf <=> F)`;;
let l4_eta_fields = new_recursive_definition num_RECURSION
 `(l4_eta_fields 0 owner major = []) /\
  (l4_eta_fields (SUC n) owner major =
    APPEND (l4_eta_fields n owner major) [L4Proj owner n major])`;;
let l4_eta_expansion = new_definition
 `l4_eta_expansion ctor owner us pars nf major =
    l4_apps (L4Const ctor us) (APPEND pars (l4_eta_fields nf owner major))`;;
