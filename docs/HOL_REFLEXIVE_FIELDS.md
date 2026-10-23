# Higher-Order Recursive Fields

The integrated HOL checker supports safe single-family strictly-positive
function-valued recursive fields. The new candidate constructor is
`Index_function (domains, indices)` and its HOL counterpart is
`L4IndexFunction`. This implements the relevant positivity and recursive-field
generation paths from pinned Lean4Lean `Inductive/Add.lean`.

The domain list is an outer-to-inner dependent Pi telescope. A domain can depend
on family parameters, prior constructor fields and prior function arguments;
result indices can depend on all those variables. The native generator builds
the induction hypothesis `Pi xs, motive indices (field xs)` and the recursive
rule argument `lambda xs, recursor ... indices (field xs)`.

The HOL definitions independently reconstruct those terms and require exact
agreement with the candidate and original exported metadata. The checks retain
strict positivity, uniform parameters and universe arguments, field typing in
a header-only environment, universe bounds, elimination/K restrictions,
freshness and complete declaration formation. Recursive family occurrences in
function domains or indices are prohibited. Empty function telescopes behave
as direct recursion; nonempty ones set the derived reflexive flag.

This is general field processing, not recognition of RTree, Acc or filenames.
Mutual/nested families and raw/reducible constructor telescopes remain outside
this extension. Recursive families do not acquire structure eta.

## Formal Boundary

There are still 27 native judgment clauses and nine environment-admission
clauses. The existing indexed clause's premise language is extended, so unchanged
clause counts are not a semantic-conservativity proof. No HOL axiom or unchecked
cast was introduced. Certificates prove the encoded judgments, not a universal
correspondence theorem with Lean. Exact environment/policy binding and closed
certificate guards remain.

`hol/reflexive_certificates.ml` proves positivity facts, extraction of field
validity from admission, and exclusion of recursive headers from structure eta.
The generator helper `index_positions` now returns triples
`(position, domains, indices)`; callers of that helper must use the new shape.

## Verification

The exact combined private sources subsequently integrated pass:

- All 19 native suite markers, 1,181,788 assertions, in 547.717s. No HOL errors,
  source changes or missing markers; the child was reaped. Most assertions are
  the existing 1,179,904 syntax/UTF-8 checks, not separate proof files.
- 60 focused recursive-field checks, including dependent telescopes/indices,
  multiple fields, malicious IH/RHS/metadata, negative occurrences and Acc eta.
  These are included in the full native count, not additional to it.
- 14 selected Arena files: 11 accepts (075, 121-124 and 126-131), three declines
  (119, 120 and 125), and 206 explicitly unselected inventory entries. The
  declines are proof-search failures, not logical refutations or timeouts.
- All three shiftLeft frontend controls, with the wrong-result decline occurring
  without timeout. The rebuilt integrated transport passes 67 checks.

Reports are `build/reports/hol-reflexive-native.{json,log}`,
`hol-reflexive-selected-arena.json`, `hol-reflexive-selected-runtime.json` and
`hol-reflexive-shift-left-exports.json`. The combined source was tested in
`/private/tmp/hol-integrated-reflexive-20260929`; integrated HOL source files were
compared byte-for-byte afterward.

The subsequent full run attempts all 216 available files in the 220-case
manifest: 88 correct accepts, six correct rejects, two allowed-either outcomes,
120 declines and four missing downloads. There are no wrong verdicts,
operational faults or integrity failures. Relative to the prior full run,
only 121 and 123 change classification, from decline to acceptance. The
ten-second worker cap still times out on 122 and 124; their selected longer
run above is separate evidence, not a replacement for these outcomes.

Of the 120 declines, 39 are expected-valid (29 internal timeouts, ten other
declines), 65 are expected-invalid (13 timeouts, 52 other declines), and 16
allow either (five timeouts, eleven other declines). These are not refutations
or passing cases. Internal worker timeouts exit 2, hence are included in the
decline column rather than the harness's outer-timeout column.

Full-run evidence is `build/reports/hol-reflexive-full-arena-10s.json` with
`hol-reflexive-full-runtime.json`. The loaded snapshot is
`a7a608a4c123f2f0e42757e562c8ea7fa58c16d592d85903612984f1fe6af47b`;
its manifest hash is
`502f85cc115f7555c6efc2ec5e74e1d81d165499a73e776827e63c3f77a08b8b`.
The private server and harness have completed and been reaped.

Run `python3 tests/hol_strings/run_native.py reflexive` for the focused suite,
or `full` for all 19 configured suites. Agent development failures and its
earlier 411-assertion checkpoint remain documented in
`/private/tmp/hol-reflexive-fields-20260929.cTWHmx/REPORT.md`.
