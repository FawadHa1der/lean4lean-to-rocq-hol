(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Admission annotations/history only: the existing typing rules are unchanged. *)
needs "hol/raw_ctor_admission.ml";;
needs "hol/closed_syntax.ml";;

let l4_safety_INDUCT,l4_safety_RECURSION = define_type
 "l4_safety = L4Safe | L4Partial | L4Unsafe";;
let l4_hint_INDUCT,l4_hint_RECURSION = define_type
 "l4_hint = L4NoHint | L4OpaqueHint | L4AbbrevHint | L4RegularHint num";;
let l4_mark_INDUCT,l4_mark_RECURSION = define_type
 "l4_mark = L4Mark l4_safety l4_entry l4_hint (l4_name list)";;
let l4_operation_INDUCT,l4_operation_RECURSION = define_type
 "l4_operation = L4SafeStep | L4UnsafeSingle | L4PartialSingle | L4RestrictedMutual";;
let l4_mark_safety = new_recursive_definition l4_mark_RECURSION
 `l4_mark_safety (L4Mark s d h ns) = s`;;
let l4_mark_entry = new_recursive_definition l4_mark_RECURSION
 `l4_mark_entry (L4Mark s d h ns) = d`;;
let l4_mark_hint = new_recursive_definition l4_mark_RECURSION
 `l4_mark_hint (L4Mark s d h ns) = h`;;
let l4_mark_all = new_recursive_definition l4_mark_RECURSION
 `l4_mark_all (L4Mark s d h ns) = ns`;;
let l4_mark_name = new_definition
 `!r. l4_mark_name r = l4_entry_name (l4_mark_entry r)`;;
let l4_safety_visible = new_definition
 `!m r. l4_safety_visible m r <=>
    m = L4Unsafe \/ l4_mark_safety r = L4Safe \/
    (m = L4Partial /\ l4_mark_safety r = L4Partial)`;;
let l4_safety_view = new_definition
 `!m registry. l4_safety_view m registry =
    MAP l4_mark_entry (FILTER (l4_safety_visible m) registry)`;;
let l4_safety_blocked = new_definition
 `!m registry. l4_safety_blocked m registry =
    MAP l4_mark_name (FILTER (\r. ~l4_safety_visible m r) registry)`;;
let l4_safety_safe_entries = new_definition
 `!ds. l4_safety_safe_entries ds = MAP (\d. L4Mark L4Safe d L4NoHint []) ds`;;
let l4_safety_refs = new_recursive_definition l4_expr_RECURSION
 `(l4_safety_refs (L4BVar i) = []) /\
  (l4_safety_refs (L4Sort u) = []) /\
  (l4_safety_refs (L4Const n us) = [n]) /\
  (l4_safety_refs (L4App f a) = APPEND (l4_safety_refs f) (l4_safety_refs a)) /\
  (l4_safety_refs (L4Lam n a b) = APPEND (l4_safety_refs a) (l4_safety_refs b)) /\
  (l4_safety_refs (L4Pi n a b) = APPEND (l4_safety_refs a) (l4_safety_refs b)) /\
  (l4_safety_refs (L4Let n a v b) = APPEND (l4_safety_refs a)
    (APPEND (l4_safety_refs v) (l4_safety_refs b))) /\
  (l4_safety_refs (L4NatLit numeral) = []) /\
  (l4_safety_refs (L4StrLit s) = []) /\
  (l4_safety_refs (L4Proj owner index e) = l4_safety_refs e)`;;
let l4_safety_rule_refs = new_recursive_definition l4_recrule_RECURSION
 `l4_safety_rule_refs (L4RecRule n k rhs) = l4_safety_refs rhs`;;
let l4_safety_role_refs = new_recursive_definition l4_role_RECURSION
 `(l4_safety_role_refs (L4InductiveRole p x ns cs nested r f u) = []) /\
  (l4_safety_role_refs (L4ConstructorRole n j p nf u) = []) /\
  (l4_safety_role_refs (L4RecursorRole ns p x m k rs b u) =
    ITLIST APPEND (MAP l4_safety_rule_refs rs) ([]:l4_name list))`;;
let l4_safety_kind_refs = new_recursive_definition l4_entry_kind_RECURSION
 `(l4_safety_kind_refs L4DefKind = []) /\
  (l4_safety_kind_refs L4ThmKind = []) /\
  (l4_safety_kind_refs L4OpaqueKind = []) /\
  (l4_safety_kind_refs L4AxiomKind = []) /\
  (l4_safety_kind_refs (L4Generated r) = l4_safety_role_refs r) /\
  (l4_safety_kind_refs (L4QuotientKind k) = [])`;;
let l4_safety_entry_refs = new_definition
 `!d. l4_safety_entry_refs d = APPEND (l4_safety_refs (l4_entry_type d))
    (APPEND (l4_safety_refs (l4_entry_body d)) (l4_safety_kind_refs (l4_entry_tag d)))`;;
let l4_safety_references = new_definition
 `!m registry raw. l4_safety_references m registry raw <=>
    ALL (\r. ALL (\n. ~MEM n (l4_safety_blocked m registry))
      (l4_safety_entry_refs (l4_mark_entry r))) raw`;;
let l4_safety_fresh = new_definition
 `!registry raw. l4_safety_fresh registry raw <=>
    l4_names_distinct (APPEND (MAP l4_mark_name raw) (MAP l4_mark_name registry))`;;
let l4_safety_mode = new_definition
 `!op raw. l4_safety_mode op raw =
    if op = L4SafeStep \/ op = L4PartialSingle then L4Safe
    else l4_mark_safety (HD raw)`;;
let l4_safety_placeholder = new_definition
 `!r. l4_safety_placeholder r = L4Entry L4AxiomKind (l4_mark_name r)
    (l4_entry_params (l4_mark_entry r)) (l4_entry_type (l4_mark_entry r)) (L4Sort L4Zero)`;;
let l4_safety_fragment = new_definition
 `!op registry raw. l4_safety_fragment op registry raw =
    if op = L4PartialSingle then l4_safety_view L4Safe registry
    else APPEND (MAP l4_safety_placeholder raw)
      (l4_safety_view (l4_safety_mode op raw) registry)`;;
let l4_safety_definition = new_definition
 `!r. l4_safety_definition r <=>
    l4_entry_tag (l4_mark_entry r) = L4DefKind /\
    ~(l4_mark_hint r = L4NoHint) /\
    ~l4_protected_name (l4_mark_name r) /\
    l4_names_distinct (l4_entry_params (l4_mark_entry r)) /\
    l4_params_expr (l4_entry_type (l4_mark_entry r)) (l4_entry_params (l4_mark_entry r)) /\
    l4_params_expr (l4_entry_body (l4_mark_entry r)) (l4_entry_params (l4_mark_entry r)) /\
    l4_scoped (l4_entry_type (l4_mark_entry r)) 0 /\
    l4_scoped (l4_entry_body (l4_mark_entry r)) 0`;;
let l4_safety_shape = new_definition
 `!op raw. l4_safety_shape op raw <=> ~(raw = []) /\
    ALL l4_safety_definition raw /\
    ((op = L4UnsafeSingle /\ LENGTH raw = 1 /\
       ALL (\r. l4_mark_safety r = L4Unsafe) raw) \/
     (op = L4PartialSingle /\ LENGTH raw = 1 /\
       ALL (\r. l4_mark_safety r = L4Partial) raw) \/
     (op = L4RestrictedMutual /\ ~(l4_mark_safety (HD raw) = L4Safe) /\
       ALL (\r. l4_mark_safety r = l4_mark_safety (HD raw) /\
         l4_entry_params (l4_mark_entry r) = l4_entry_params (l4_mark_entry (HD raw)) /\
         l4_name_inventory (l4_mark_all r) (MAP l4_mark_name raw)) raw))`;;
let l4_safety_header = new_definition
 `!view r. l4_safety_header view r <=>
    ?u. l4_raw_sort view [] (l4_entry_type (l4_mark_entry r)) u`;;
let l4_safety_body = new_definition
 `!fragment r. l4_safety_body fragment r <=> l4_econtext fragment [] /\
    l4_edef fragment [] (l4_entry_body (l4_mark_entry r))
      (l4_entry_body (l4_mark_entry r)) (l4_entry_type (l4_mark_entry r))`;;
let l4_safety_restricted = new_definition
 `!op registry raw. l4_safety_restricted op registry raw <=>
    l4_safety_shape op raw /\ l4_safety_fresh registry raw /\
    l4_safety_references (l4_safety_mode op raw) registry raw /\
    ALL (l4_safety_header (l4_safety_view (l4_safety_mode op raw) registry)) raw /\
    ALL (l4_safety_body (l4_safety_fragment op registry raw)) raw`;;

(* Each history node retains exact raw fields and its actual prior state.
   Canonical safe entries are separate from raw input, as in old input history. *)
let l4_safety_step_INDUCT,l4_safety_step_RECURSION = define_type
 "l4_safety_step = L4SafetyStep l4_operation (l4_mark list) (l4_mark list)
    (l4_entry list) (l4_entry list)";;
let l4_safety_step_op = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_step_op (L4SafetyStep op raw registry env ds) = op`;;
let l4_safety_step_raw = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_step_raw (L4SafetyStep op raw registry env ds) = raw`;;
let l4_safety_step_registry = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_step_registry (L4SafetyStep op raw registry env ds) = registry`;;
let l4_safety_step_env = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_step_env (L4SafetyStep op raw registry env ds) = env`;;
let l4_safety_next_registry = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_next_registry (L4SafetyStep op raw registry env ds) =
    APPEND (if op = L4SafeStep then l4_safety_safe_entries ds else raw) registry`;;
let l4_safety_next_env = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_next_env (L4SafetyStep op raw registry env ds) =
    if op = L4SafeStep then APPEND ds env else env`;;
let l4_safety_step_valid = new_recursive_definition l4_safety_step_RECURSION
 `l4_safety_step_valid policy (L4SafetyStep op raw registry env ds) <=>
    l4_evalid policy env /\ l4_safety_view L4Safe registry = env /\
    (if op = L4SafeStep then
      ALL (\r. l4_mark_safety r = L4Safe) raw /\
      l4_safety_fresh registry raw /\ l4_safety_references L4Safe registry raw /\
      l4_safety_fresh registry (l4_safety_safe_entries ds) /\
      l4_evalid policy (APPEND ds env) /\
      (l4_metadata_matches (MAP l4_mark_entry raw) ds \/
       l4_raw_generated_admitted policy env (MAP l4_mark_entry raw) ds (APPEND ds env))
    else ds = [] /\ l4_safety_restricted op registry raw)`;;
let l4_safety_trace = new_recursive_definition list_RECURSION
 `(l4_safety_trace policy registry env [] <=> registry = [] /\ env = []) /\
  (l4_safety_trace policy registry env (CONS step history) <=>
    registry = l4_safety_next_registry step /\ env = l4_safety_next_env step /\
    l4_safety_trace policy (l4_safety_step_registry step) (l4_safety_step_env step) history /\
    l4_safety_step_valid policy step)`;;
let l4_safety_raw_history = new_recursive_definition list_RECURSION
 `(l4_safety_raw_history [] = ([]:l4_mark list)) /\
  (l4_safety_raw_history (CONS step history) =
    APPEND (l4_safety_step_raw step) (l4_safety_raw_history history))`;;
let l4_safety_safe_history = new_recursive_definition list_RECURSION
 `(l4_safety_safe_history [] = ([]:(l4_entry list)list)) /\
  (l4_safety_safe_history (CONS step history) =
    if l4_safety_step_op step = L4SafeStep then
      CONS (MAP l4_mark_entry (l4_safety_step_raw step)) (l4_safety_safe_history history)
    else l4_safety_safe_history history)`;;
let l4_safety_input_blocks = new_recursive_definition list_RECURSION
 `(l4_safety_input_blocks [] = ([]:(l4_entry list)list)) /\
  (l4_safety_input_blocks (CONS step history) =
    CONS (MAP l4_mark_entry (l4_safety_step_raw step)) (l4_safety_input_blocks history))`;;
let l4_safety_safe_history_all = prove
 (`!h. ALL (\s. l4_safety_step_op s = L4SafeStep) h ==>
    l4_safety_safe_history h = l4_safety_input_blocks h`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [l4_safety_safe_history;l4_safety_input_blocks;ALL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC []);;
let l4_safety_full = new_definition
 `!policy registry env history. l4_safety_full policy registry env history <=>
    l4_safety_trace policy registry env history /\
    l4_safety_view L4Safe registry = env /\
    l4_input_valid policy env (l4_safety_safe_history history) /\
    l4_name_inventory (MAP l4_mark_name (l4_safety_raw_history history)) (MAP l4_mark_name registry) /\
    ALL (\r. l4_entry_tag (l4_mark_entry r) = L4AxiomKind ==>
      l4_mark_safety r = L4Safe /\ MEM (l4_mark_entry r) policy)
      (l4_safety_raw_history history)`;;
let l4_safety_full_environment = prove
 (`!p r e h. l4_safety_full p r e h ==> l4_evalid p e`,
  MESON_TAC [l4_safety_full;l4_input_valid_environment]);;
let l4_safety_full_projection = prove
 (`!p r e h. l4_safety_full p r e h ==>
    l4_input_valid p e (l4_safety_safe_history h) /\ l4_safety_view L4Safe r = e`,
  SIMP_TAC [l4_safety_full]);;
let l4_safety_full_inventory = prove
 (`!p r e h. l4_safety_full p r e h ==>
    l4_name_inventory (MAP l4_mark_name (l4_safety_raw_history h)) (MAP l4_mark_name r)`,
  SIMP_TAC [l4_safety_full]);;
let l4_safety_restricted_preserves_env = prove
 (`!op raw registry env. ~(op = L4SafeStep) ==>
    l4_safety_next_env (L4SafetyStep op raw registry env []) = env`,
  SIMP_TAC [l4_safety_next_env]);;
let l4_safety_full_safe_only = prove
 (`!p r e h raw. l4_safety_full p r e h /\ l4_safety_safe_history h = raw ==>
    l4_input_valid p e raw`,
  MESON_TAC [l4_safety_full_projection]);;
let l4_safety_full_old_safe = prove
 (`!p r e h. l4_safety_full p r e h /\
    ALL (\s. l4_safety_step_op s = L4SafeStep) h ==>
    l4_input_valid p e (l4_safety_input_blocks h)`,
  MESON_TAC [l4_safety_full_projection;l4_safety_safe_history_all]);;
let l4_safety_visible_safe = prove
 (`!r. l4_safety_visible L4Safe r <=> l4_mark_safety r = L4Safe`,
  REWRITE_TAC [l4_safety_visible;distinctness "l4_safety"]);;
let l4_safety_visible_partial = prove
 (`!r. l4_safety_visible L4Partial r <=>
    l4_mark_safety r = L4Safe \/ l4_mark_safety r = L4Partial`,
  REWRITE_TAC [l4_safety_visible;distinctness "l4_safety"]);;
let l4_safety_visible_unsafe = prove
 (`!r. l4_safety_visible L4Unsafe r`,REWRITE_TAC [l4_safety_visible]);;
