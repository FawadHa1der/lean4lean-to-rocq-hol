# Mutual Inductives And Original Input History

This implementation combines two independently developed slices: nonindexed
mutual inductives and raw constructor-type checking. It is actual HOL proof
construction over defined judgments, not a wrapper around Lean or another
checker's verdict. It is still a partial port, not a verified complete Lean kernel.

## Mutual Slice

`hol/mutual_syntax.ml`, `mutual_entries.ml`, `mutual_admission.ml` and
`mutual_certificates.ml` implement safe, nonnested, nonindexed blocks with two
or more families sharing universe parameters, a dependent parameter telescope
and a result sort. Fields may depend on earlier fields. Strictly positive
recursion can cross family boundaries directly or under function binders.

The checker regenerates joint motives, global minor premises, induction
hypotheses and each recursor's right-hand sides, including calls to the correct
sibling recursor. It checks universe arities, ownership, flags, field counts,
motives, minors, rule order and all original claims. Field positivity excludes
every member of the mutual block from negative/function-domain positions.
Constructor formation is checked with all family headers but without constructor
or recursor signatures that could justify circular formation.

The result adds one mutual-iota clause and one environment-admission clause,
giving 28 native and 10 admission clauses. The preceding ordered 27/9 prefixes
are retained and compared against a frozen reference by a native regression.
The environment uniqueness and explicit object-axiom-policy invariants are
reproved for the extended judgment. No HOL axiom is added.

This slice does not implement indexed mutual, nested or unsafe blocks. Those
are not accepted merely because the single-family checker supports related
features. Existing universe-polymorphic/single-family indexed paths remain
separate. Prop mutual blocks retain small elimination and do not acquire K.

## Raw Constructor Slice

Some valid exports use reducible aliases in constructor binder types. Accepting
a normalized replacement alone would lose evidence about the supplied input.
The syntax candidate in `frontend/reducible_candidate.ml` therefore has no
authority to admit a declaration. It proposes a canonical family which must
pass ordinary admission; the separate raw layer checks the original claims.

`hol/raw_ctor_syntax.ml` defines directed head reduction and telescope/positivity
obligations. `reducible_bridge.ml` checks typed conversions of annotations and
recursor bodies while preserving metadata, computational shape and names.
`raw_ctor_admission.ml` combines these with prior-environment/header-only
formation and the admitted canonical family certificate.

Current fallback scope is one safe, nonnested, nonindexed Type-0 family with
direct recursive fields. General polymorphic, function-valued and indexed raw
telescopes remain unsupported. In particular, this integration does not claim
to accept Arena 119/120 or the polymorphic HAdd/outParam prefix.

A retained counterexample demonstrates why a conversion bridge alone was not
enough: a beta-convertible but syntactically nonuniform recursive parameter can
satisfy the old bridge. The directed raw-positivity obligations decline it.
The authentic Arena 055 fixture passes with a closed certificate about its
original decoded claims; opaque aliases and forged metadata do not bypass the
raw checker.

## Certificate Meaning

`Hol_check.check_file_with_certificate` returns, on success, the canonical
environment, the exact decoded declaration history and a closed theorem:

```text
l4_input_valid policy canonical_environment original_decoded_history
```

History is newest block first, preserving entries within each block as supplied
by the decoder. The inductive input trace has exactly three clauses: empty
history, exact metadata-matched admission, and checked raw-family admission.
Every successful declaration must extend that trace before the frontend commits
the new state. Failures return no final input certificate.

The final predicate requires the trace, a duplicate-free matching name inventory,
and explicit permission for every raw input axiom. Closed derived theorems
establish canonical environment validity, uniqueness of raw names and policy
permissions in both representations. An object-level policy is data in the
theorem, not a newly postulated HOL axiom.

This does **not** establish `l4_evalid policy (flatten original_history)` for
the unnormalized representation, conservation of arbitrary raw inductives,
overall Lean typing soundness, or parser/compiler correctness. The raw predicate
states the checked translation obligations explicitly instead of concealing
those distinctions behind a canonical-only success message.

## Ordering Bug Found During Composition

The original final guard required identical name-list order in raw history and
the canonical environment. An authentic mutual export supplied recursors as
`ZB.rec, ZA.rec`; canonical regeneration produced `ZA.rec, ZB.rec`. All six
declarations admitted, but final proof assembly declined. This was a genuine
integration bug, not an invalid input.

`l4_name_inventory` now requires distinct names on both sides and membership
in both directions. It permits only the declaration-table permutation already
allowed by full metadata matching. No history is sorted or discarded, and no
constructor-list, family-list or reduction-rule order is relaxed. General HOL
lemmas prove reflexivity, member equivalence, and that the previous ordered
guard remains sufficient. Seven direct proved controls cover reordering, empty
lists, duplicates on either side, omission, addition and renaming.

Tampered histories must fail the exact theorem-conclusion guard, not merely
exhaust the proof-search budget. The portable mutual and file regressions
explicitly check that failure category. A forged mutual motive count declines
without a certificate; that is fail-closed evidence, not a proof of invalidity.

## Reproduction And Evidence

See `tests/hol_composition/README.md` for the source-pinned bounded runner,
49 selectable groups, original fixture sources/licenses, and fifteen runner
tests. Its reports distinguish selected/unselected groups, failed attempts,
source hashes, closed-certificate checks and process cleanup. The checker never
reads the fixture expectations, manifests or test results.

Private integration evidence is retained in:

- `/private/tmp/hol-mutual-parent-20260930-v2`: seven mutual groups, three export
  groups, and the 20-suite preserved native matrix.
- `/private/tmp/hol-raw-mutual-parent-20260930-v3`: history-inventory proofs and
  raw/mutual/String/primitive/quotient/structure/reflexive composition gates.
- `/private/tmp/hol-packaged-stage-20260930`: current-scheduler portable-suite
  checks and the combined preserved native matrix.

The subsequent actual-project snapshot
`build/reports/hol-composition-20260930T151809Z-73293` passes all eleven selected
groups: history inventory, empty/recursive/forged mutual traces, raw head
conversion, quotient files, mutual positive/higher-order, and all three String
control groups. Each finishes below its 180-second cap. The independent final
audit in `build/reports/hol-main-composition-final-audit-20260930.json` verifies
all 191 origin and snapshot pins, input/log hashes and absence of every recorded
process group. The other eighteen selectable groups were not executed in this
particular matrix; earlier private evidence remains separately identified.

Earlier decoder/proof/order failures remain in their original v2 directories;
they are not counted as passes. The current runtime's separate all-216-available
Arena run is complete: 87 correct accepts, 6 correct rejects, 2 acceptable-either,
121 declines and 4 unavailable files. There are no wrong verdicts, faults,
outer-harness timeouts or skips. The 121 declines include 55 worker timeouts
at the unchanged 10-second cap and 66 other checker-declared declines.

`tutorial/112_structEta` is the sole lost acceptance: the historical run took
8.762630 seconds; the current worker times out in 10.055794 seconds. Seven other
cases remain declined but now hit the worker deadline: six performance cases
previously stopped at the input-nesting limit, and tutorial 055 previously
failed proof construction. The longer focused 055 acceptance is not a pass
under this corpus budget. No previous timeout became decided.

Reports are `build/reports/hol-shipped-raw-mutual-arena.json` and its matching
summary; complete before/after changes and provenance are retained at
`/private/tmp/hol-shipped-arena-validation-20260930-v3`. All 4,416 private input
and runtime pins held, thirty infrastructure tests passed, and all owned
process groups were reaped. Earlier missing-thread-metadata and wrong-GMP-path
startup attempts submitted zero cases and remain separate failed evidence.
This is not a published-budget library run or a complete Lean-compatible port.
