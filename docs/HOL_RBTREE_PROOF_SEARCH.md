# RBTree Private Proof-Search Fix

## Result

Confirmed the shared certificate failure in `071_rbTreeRef` and
`082_RBTree.id_spec`, and produced a minimal **proof-search-only** patch in a
private pre-K checkpoint copy. The shared RBTree declaration now accepts with a
closed environment certificate. Both complete files still hit a 30-second
worker limit on this old image; full-file acceptance is **not** claimed.

No production files, object predicates, inference rules, generated terms,
frontend/client code, or later K/cache/primitive-EValid/projection work were
changed. The private baseline was the reviewed indexed checkpoint plus the
previously validated P2 rewrite-list fix.

## Confirmed Obligation

Non-discharging instrumentation appended `ALL_TAC` after the existing proof
tactics and printed any remaining goal. Both inputs stopped at:

```text
RB_PHASE indexed.field.3.premise.1
RB_UNSOLVED indexed.field.3.premise.1
l4_params_expr
  (l4_apps (L4Const RBTree [L4Param u]) (l4_vars 1 3))
  [u]
```

The display above abbreviates the structural encodings of `RBTree` and `u`;
the [full transcript](../tests/hol_indexed_audit/rb_fix/evidence/rb-probe2.log)
preserves the exact goal. This is the fourth field's universe-parameter scope
premise in `l4_index_fields_valid`, before indexed flag or metadata checks.
The failure is not another missing elimination fact.

## Converter Mechanism

The old `vars_unfold` accepts a recognized constant with *any* nonempty argument
list. `DEPTH_CONV` reaches the curried partial application `l4_vars 1` before the
complete application `l4_vars 1 3`. It changes the numeral to `SUC 0`, but the
recursive equation cannot fire without the second argument. The complete call
then fails `is_numeral` because its first argument is now `SUC 0`.
`NUM_REDUCE_CONV` normalizes it back to `1`, undoing the only progress.

An isolated probe using the original converter and the proposed guard recorded:

```text
RB_CONVERSION_EARLY l4_vars (SUC 0) 3
RB_CONVERSION_REVERTED l4_vars 1 3
RB_CONVERSION_FIXED [L4BVar 3]
RB_CONVERSION_CLOSED_EXACT_NO_AXIOMS
```

The probe checks that the fixed conversion returns exactly the closed HOL
theorem `l4_vars 1 3 = [L4BVar 3]` and that `axioms()` is unchanged. It does not
assume the desired equality. Its [source](../tests/hol_indexed_audit/rb_fix/evidence/conversion_probe.ml)
and diagnostic instrumentation patches are archived separately from the fix.

## Exact Patch

Require each recognized function's full arity before converting its numeric
first argument. All subsequent conversions remain unchanged.

[converter.patch](../tests/hol_indexed_audit/rb_fix/converter.patch):

```diff
     | n::_ when is_const h &&
-        mem (fst(dest_const h)) ["l4_vars";"l4_decimal_aux";"l4_fresh_univ_aux"] &&
+        mem (fst(dest_const h),List.length args)
+          ["l4_vars",2;"l4_decimal_aux",2;"l4_fresh_univ_aux",3] &&
         is_numeral n && n<>`0` ->
```

This prevents a conversion from firing too early; it does not add an object
rule, weaken a premise, or change the represented computation. The three
arities come from the existing HOL recursive definitions.

## Frozen Identity

- Original review manifest: `7677c7e691c7a42884b0ff7e97577960615396e6d8bfeddb62fba5988c2003fa`.
- Pre-converter environment, including P2: `6eb71198bbbe0bbda583aa5bfc9830e6fda1de95e1ea195c0f1f08e6444d22a8`.
- Fixed environment: `91fa4b30e5a385dd4fb6ead82dc7c0cabaa9bac66341fa5b8bf90d623f87a3da`.
- Incremental converter patch: `99eae49565cb5c0cee74218fdd27428630febbc9145d77c20b16972f8046e231`.
- New private READY provenance: `35cc318f9a50e66d2a7d7e058f040f9671fd2412e53cb697e9d69ec95141d3dd`.

Private fixed tree: `/private/tmp/hol-indexed-p2.BLzUH9/rb-fixed`.
The sidecar verifies every file in the 39-input review snapshot, allowing only
the exact P2 and converter edits to `hol/environment.ml`. The new server's
27-input closure and bootstrap are checked against the reviewed startup,
substituting only that environment hash. See its
[fresh provenance](../tests/hol_indexed_audit/rb_fix/startup-provenance.json).

Each direct diagnostic/native run also records its own before/after project
snapshot, bootstrap hash, bounded transcript hash, and additional loaded test
source identity. These records identify filesystem inputs, not external
toolchains, executed runtime state, or semantic equivalence to Lean.

## Bounded Results

[report.json](../tests/hol_indexed_audit/rb_fix/report.json), finished
`2026-09-29T21:09:49.073689+00:00`, SHA256
`92c794efbacaf90e9931b70f68b7b85771c1a92e9cf8794e6439095d708ece1c`:

| Check | Result |
| --- | --- |
| Original 7 positive baseline gates | All code 0 |
| Shared RBTree admission prefix | Code 0, line 294, checked 3; 16.453 s |
| Both P2 Prop-only positives | Code 0; 3.471 s and 3.739 s |
| Both P2 forged-large variants | Code 2; declines, not refutations |
| Complete 071_rbTreeRef | Code 2; 30-second worker timeout; child killed/reaped |
| Complete 082_RBTree.id_spec | Code 2; 30-second worker timeout; child killed/reaped |
| Frozen native indexed regressions | All 87 assertions pass; 104.575 s including initialization |
| Existing offline fixture tests | All 8 pass |

The shared admission fixture is the byte-identical first 294 lines of the two
SHA-pinned exports, ending immediately after the complete RBTree block. Only
later definitions/theorems are omitted. Its acceptance directly demonstrates
that the original shared certificate blockage has been cleared, without
claiming those later declarations are covered.

The native run uses the unchanged reviewed `hol/indexed_tests.ml`, checks every
assertion numbered 1 through 87, and includes exact/closed certificates,
recursive indexed iota, dependent indices, metadata/permission/uniqueness
checks, and no new HOL axioms. Its negative assertions check decline behavior,
not formal refutation. The complete [native transcript](../tests/hol_indexed_audit/rb_fix/evidence/rb-native.log)
is retained; it ran within a 180-second whole-process limit.

No wrong verdicts, faults, integrity changes, or outer-harness timeouts occurred.
The two full-file worker timeouts are explicit coverage gaps. The sidecar exits
2 because its paired negative declines remain uncovered, and the full-file
observations have no expected-verdict/pass-fail labels. `077` was not rerun.
No checker or expected-outcome file was used as an oracle.

## Handoff And Cleanup

**Production integration remains with the parent.** Merge only the saturated
arity guard into the current `vars_unfold`; do not replace `environment.ml`
with this private pre-K copy. Preserve P2 and all later native changes. The
current production image may have different performance, but acceptance there
requires a fresh build/run and is not implied by this report.

All requests ended. Private supervisor **72446** and HOL process **72468** were
stopped/reaped and confirmed absent; the socket was removed. The
[evidence summary](../tests/hol_indexed_audit/rb_fix/evidence/summary.json) records
cleanup and all three direct-run identities. Private copies remain for review.

Offline identity recheck, without starting or contacting HOL:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_indexed_audit/rb_fix/run.py \
  --private-root /private/tmp/hol-indexed-p2.BLzUH9/rb-fixed
```
