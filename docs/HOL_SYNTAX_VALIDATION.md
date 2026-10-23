# Iterative Syntax Validation

The HOL port's local syntax validator uses an explicit work stack instead of
recursive traversal with a fixed 512-level cutoff. It retains canonical natural
numerals, UTF-8 scalar checks, nonnegative indices and traversal order for syntax
errors. This is not a new typing rule or a shortcut to acceptance.

Per-traversal physical-identity tables distinguish active ancestors from fully
validated immutable syntax. Repeated completed nodes may reuse syntax validation;
active ancestors identify cycles, which are rejected. No typing verdict or HOL
theorem is cached here, no table survives the traversal, and a hash collision
does not identify distinct nodes. A finite work budget still applies to visits
and string bytes. Other recursive checker/proof-construction operations can
still exhaust stack, memory, fuel or wall time and return a decline.

## Verification

The exact integrated HOL directory is byte-identical to the tested private
`/private/tmp/hol-iterative-validation-20260930/hol` snapshot. Its full run passes
all 20 configured native markers and 1,185,958 assertions in 567.437 seconds, with no HOL
errors, unchanged source hashes and a reaped child. Most assertions are the
existing UTF-8 boundary sweep, not independent proof files.

The new 4,170-check suite compares the previous validator on finite shallow
inputs, including first-error ordering and malformed leaves in every expression
position. It also checks 20,000-level expressions/names/universes, a 10,000-level
shared DAG, deep malformed input, cyclic native values, finite budgets and
ordinary positive/negative typing controls. Syntax-only deep positives are not
claimed as accepted Lean proofs. The existing 18 runner/provenance tests pass.

```sh
python3 tests/hol_strings/run_native.py validation
python3 tests/hol_strings/run_native.py full
```

Reports: `build/reports/hol-iterative-validation-native.{json,log}` and
`hol-iterative-validation-selected-arena.json`, with the latter's loaded-source
manifest at `hol-iterative-validation-runtime.json`.

The selected Arena attempt covers six formerly depth-limited valid inputs,
plus one valid and one invalid control. All six now hit the 30-second worker
timeout; the valid control accepts and the invalid control declines. There are
212 explicitly unselected entries, no wrong verdict and no integrity failure.
Removing the depth cutoff therefore has not yet produced new Arena passes.
The worker and harness are stopped and reaped. A preceding attempt could not
connect to the local socket under the filesystem sandbox; its eight operational
faults are preserved separately in `hol-validation-initial-socket-denial.json`
and are not treated as checker verdicts.
