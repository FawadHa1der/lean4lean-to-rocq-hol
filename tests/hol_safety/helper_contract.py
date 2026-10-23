"""Source-only contract for the new helper, not its surrounding environment."""

DECLARATION = (
    '  val fragment_check : ?fuel:int -> declaration list -> Lean4hol.expr list ->\n'
    '    Lean4hol.expr -> Lean4hol.expr -> (thm,Lean4hol.error) result\n')
IMPLEMENTATION = '''  (* A fragment judgment is not an authenticated environment or l4_checked. *)
  let fragment_check ?(fuel=100000) entries g e a = run fuel [] (g@[e;a]) (fun st ->
    List.iter (fun d -> validate st [] (validation_terms d)) entries;
    let module Native = Native(struct let entries = entries end) in
    let ctx=Native.context st g in
    ignore(Native.infer_sort st g a);
    let h=Native.check_i st g e a in
    let qe=quote_entries entries and qg=quote_context g in
    guarded (mk_conj(node "l4_econtext" [qe;qg],
      node "l4_edef" [qe;qg;quote_expr e;quote_expr e;quote_expr a])) (CONJ ctx h))

'''


def require_helper(source):
    if source.count(DECLARATION) != 1 or source.count(IMPLEMENTATION) != 1:
        raise AssertionError('fragment_check signature or checked implementation changed')
    if source.count('  val fragment_check ') != 1 or source.count('  let fragment_check ') != 1:
        raise AssertionError('fragment_check duplicated or shadowed')
