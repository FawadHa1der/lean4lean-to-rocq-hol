# Indexed P2 Private Fix

## Outcome

Confirmed and fixed the two positive Prop-only declines **in a private copy of
the reviewed indexed checkpoint only**. Production HOL, frontend, native, and
client files were not edited. The private copy excludes the parent's later K,
member-cache, primitive-EValid-append, and projection changes.

All seven original positive gates and both previously declining positives now
accept. Both corresponding forged-large variants still return **2 (decline)**,
not refutation. The frozen native indexed regression file completes all **87
assertions**, including exact/closed certificate checks and no new HOL axioms.

## Confirmed Failure

The diagnostic copy changed only the local indexed `flags` function. It printed
the remaining goal after the existing tactics and then used `ALL_TAC`, which
does not discharge that goal. The original failures were reproduced:

```text
P2_FLAG_BEGIN 8
P2_FLAG_CLOSED 8
P2_FLAG_BEGIN 7
P2_UNSOLVED_FLAG 7 ~(L4BVar 1 = L4BVar 0)
P2_VERDICT hidden-data-prop-only 2 ... TAC_PROOF: Unsolved goals
```

The nested-index case also stopped in **flags 7**, with:

```text
~(L4BVar 1 = L4BVar 0 \/
  L4BVar 1 = L4App (L4Lam ... (L4BVar 0)) (L4BVar 1))
```

Thus the failure was the **large-elimination equivalence**, not K metadata,
constructor typing, or a guessed downstream failure. `generator_calc` unfolded
`MEM` after the earlier flag rewrite pass, leaving expression-constructor
equalities without the necessary injectivity/disjointness simplification.

The complete [probe transcript](../tests/hol_indexed_audit/p2_fix/evidence/probe.log)
and separate [diagnostic-only patch](../tests/hol_indexed_audit/p2_fix/evidence/diagnostic-flags.patch)
are preserved. Diagnostic instrumentation is not part of the proposed fix.

## Exact Change

Only three existing rewrite facts are added to indexed `flags`:
`MEM`, `distinctness "l4_expr"`, and `injectivity "l4_expr"`. Membership unfolds
in the same pass as constructor equality simplification, before the existing
numeric/generator conversion. No predicate, inference rule, generated term,
elimination criterion, ML flag selection, or error classification changes.

[flags.patch](../tests/hol_indexed_audit/p2_fix/flags.patch):

```diff
       let flags j=prove(List.nth conditions j,
-        REWRITE_TAC ([l4_index_large;l4_index_large_fields;l4_index_k;ALL;ALL2;LENGTH;
-          l4_index_fields;l4_index_result;distinctness "list";injectivity "list";hn] @ zeros) THEN
+        REWRITE_TAC ([l4_index_large;l4_index_large_fields;l4_index_k;ALL;ALL2;LENGTH;MEM;
+          l4_index_fields;l4_index_result;distinctness "l4_expr";injectivity "l4_expr";
+          distinctness "list";injectivity "list";hn] @ zeros) THEN
         CONV_TAC generator_calc) in
```

These are HOL datatype theorems and the existing membership definition. Closed
admission certificates are still required; no oracle, axiom, unchecked term, or
new logical rule is introduced.

## Identity

- Base review manifest: `7677c7e691c7a42884b0ff7e97577960615396e6d8bfeddb62fba5988c2003fa`.
- Original `hol/environment.ml`: `879d3d999ef2b3eb5fe9976e4f8b30fe5998d9ed23fa8f3d5ba575a48e496f58`.
- Diagnostic instrumented environment: `a60ada7bd5f75ed229daf37beb9873f4df3673df824407045dc5be3a74d42dd3`.
- Fixed environment: `6eb71198bbbe0bbda583aa5bfc9830e6fda1de95e1ea195c0f1f08e6444d22a8`.
- Exact fix patch: `8b3f87a0d36dc5bf3c9ffd11fc78b2f2424207c852317a7498592940e6801484`.
- Private READY provenance: `06d22525e8d7440ca455b21d1d4a246d68c052d3a4865533d39cd2a66f961d93`.

Private fixed tree: `/private/tmp/hol-indexed-p2.BLzUH9/fixed`.
The runner verifies every file in the original 39-input review snapshot against
that private tree, allowing only the exact text replacement above. Its 27-input
READY closure matches the original startup closure except for this environment
file; the bootstrap hash is unchanged. See the preserved
[private READY manifest](../tests/hol_indexed_audit/p2_fix/fixed-startup-provenance.json).
This remains project-input provenance, not toolchain/runtime/semantic attestation.

`environment_rules.ml` remains
`bc91e7a6067ba40d08c88b50057d69a6c389559c2e1240cb5322ee7a942fe497`;
`indexed_syntax.ml` remains
`f57f23028e8918533e092cb1254be3a763af2b601ca9f1df670a224b1adb5d2c`.
The elimination predicate and admission premises therefore match the reviewed
source byte for byte.

## Targeted Replay

[targeted-report.json](../tests/hol_indexed_audit/p2_fix/targeted-report.json),
completed `2026-09-29T20:50:56.782363+00:00`, SHA256
`4f526fd4da608ca71a29d14fd92dd5600a212c410496e944792859fd40f07d69`:

| Input | Code | Seconds |
| --- | --- | --- |
| All 7 baseline gates | 0 each | 1.20-6.02 |
| hidden-data-prop-only | 0 | 3.990 |
| nested-index-prop-only | 0 | 4.616 |
| hidden-data-forged-large | 2 | 2.621 |
| nested-index-forged-large | 2 | 2.488 |

No false verdicts, faults, timeouts, or integrity changes occurred in this
targeted replay. The runner exits **2** because the two negative declines remain
coverage gaps. No expected outcomes were passed to the checker, and no other
checker was used as an oracle. These are unchanged, hash-pinned copies of the
original seven gates and four mutations, not fixtures adjusted after observing
the fix.

## Native Regressions

The unchanged reviewed `hol/indexed_tests.ml` has SHA256
`f9eb2af8ac20a1d3512458c4c69cff8903b0473679c38c1534754505efb11fe8`.
It was loaded against the fixed private environment under a 180-second bound;
initialization plus tests took 131.865 seconds, exited 0, and emitted
`HOL_INDEXED_TESTS_PASSED 87`. Every numbered assertion from 1 through 87 was
checked in the preserved [transcript](../tests/hol_indexed_audit/p2_fix/evidence/native.log).

This includes direct indexed recursion, dependent index telescopes, Eq and
dependent-pair iota, permuted claims, elimination/metadata certificates,
permission/uniqueness invariants, and no new HOL axioms. Existing negative
assertions test decline behavior; they are not formal refutations. The frozen
test explicitly expects neutral-K reduction to remain unsupported, so this is
not a test of the later K implementation or the entire 717-assertion checkpoint.

## Optional Diagnostics

The three requested inputs were separately SHA-pinned from the Arena manifest
and run as **observations only**, without expected verdicts or pass/fail labels.
[Diagnostic report](../tests/hol_indexed_audit/p2_fix/diagnostics/report.json),
SHA256 `21fbf24e77f37cf664d77aeed96d18364383cc89968661b49683ce50b375d410`:

| Input | Observation On Private Pre-K Copy |
| --- | --- |
| 071_rbTreeRef | Code 2; line 294, checked 2, unsolved HOL goals; 3.093 s |
| 077_sortElimProp2Rec | Code 2; 10-second worker timeout, child killed/reaped; 10.093 s |
| 082_RBTree.id_spec | Code 2; line 294, checked 2, unsolved HOL goals; 3.593 s |

The flags patch does not resolve 071 or 082 here. The 077 timeout does not
establish which later obligation failed or that it would accept with more time.
These observations cannot be substituted for testing the parent's newer K
image. No broader logical-rule work was attempted.

## Handoff And Cleanup

**Parent integration is pending.** Apply only the three rewrite-list additions
to the current indexed `flags` implementation; do not replace the current
`environment.ml` with the private checkpoint file. In particular, preserve all
later K/member-cache/primitive-EValid/projection work. This task did not apply
anything to production or rerun the parent's current full suite.

All private requests and native runs ended. Private supervisor **64420** and HOL
process **64442** were stopped/reaped and confirmed absent; their socket was
removed. See [cleanup and evidence summary](../tests/hol_indexed_audit/p2_fix/evidence/summary.json).
The private source trees and bounded logs are retained for inspection.

To revalidate the persisted fixture and patch identities without starting HOL:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_indexed_audit/p2_fix/run_targeted.py \
  --private-root /private/tmp/hol-indexed-p2.BLzUH9/fixed
```
