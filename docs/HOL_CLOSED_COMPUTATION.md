# Closed Object Computations

The main HOL engine now tries proved closed-term identities before its existing
object computation conversion. This changes proof construction, not the native
typing or admission rules.

For a structurally closed expression, the helper first proves exactly
`l4_scoped e 0` in HOL. It then instantiates the existing `l4_lift_closed`,
`l4_subst_closed`, or `l4_inst_closed` theorem. Scope recognition alone never
produces a theorem. Every returned conversion must be hypothesis-free and have
the exact original input and expected output. Open, unknown, oversized or
unproved cases fall back to the unchanged ordinary conversion.

Scopedness is not well-typedness. Symbolic HOL universe fields can appear in
hypothesis-free scope theorems; public closed declaration certificates have not
been relaxed.

## Retention Bounds

The new cache retains at most 64 entries and 65,536 weighted units in total,
with at most 8,192 units per entry, depth 128 and labels of 256 bytes. Accounting
includes expression keys, retained theorem conclusions, types and list cells.
Traversal is iterative; bounded entries are compared structurally, not by hash
alone. Both positive and negative entries are charged, and eviction is FIFO.

These are local retained-data bounds, not byte-accurate allocation, transient
proof-search, existing-cache or whole-process memory guarantees.

## Validation

The fresh main replay passes 6,154 assertions across differential, guard and
component-benchmark groups, at unchanged 180-second limits. All source/log
hashes and process cleanup checks pass. Evidence is under
`build/reports/hol-composition-20261001T021755Z-83629/audit.json`.
Pure accounting tests separately pass 83,391 assertions. All preceding 94
composition jobs remain exactly unchanged in the current 97-job registry.

```sh
python3 -B tests/hol_closed_computation/run_budget.py
python3 -B tests/hol_composition/run.py closed-computation-differential closed-computation-guards closed-computation-benchmark
```

The component measurement is not a full-file speedup claim. The earlier HOL
Arena counts belong to the preceding runtime; no newer Arena result is inferred
from these focused tests. Full Lean correspondence remains unproved.
