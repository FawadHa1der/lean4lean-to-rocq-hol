# Text and String Regression Tests

These tests execute the HOL theorem-producing checker. Expected fixture labels
are used only by the test harness, never to establish a checker verdict.

```sh
python3 tests/hol_strings/run_native.py syntax
python3 tests/hol_strings/run_native.py interfaces
python3 tests/hol_strings/run_native.py literals
python3 tests/hol_strings/run_native.py quotients
python3 tests/hol_strings/run_native.py full
sh scripts/build-hol-frontend.sh
python3 -m unittest discover -s tests/hol_runner -v
```

The small native suites default to 180 seconds; the combined suite defaults to
900 seconds. Each command prints a retained output directory containing the full
HOL log and JSON report. It requires all expected completion markers, rejects
HOL error diagnostics, checks source hashes, and kills/reaps its process group
on timeout. The full suite includes the existing core/family/projection/quotient
tests and a focused Nat.pow factory phase; it is not every primitive test phase
or a full Lean kernel soundness proof.

For file-path checks, start the project worker with `sh scripts/hol-server.sh`
and pass its returned private socket to:

```sh
python3 tests/hol_strings/test_exports.py --socket /private/tmp/hol-run-EXAMPLE/s
```

That command preserves generated NDJSON and its report in a fresh output
directory. The fixture uses the pinned Arena canonical Nat block and typed text
interfaces. It accepts the complete interface gate before attempting negatives.
Source and fixture hashes must remain unchanged. The worker has a 45-second
case request cap and the client process a 55-second outer cap. A failed gate,
decline where acceptance is expected, timeout, or operational fault fails the
suite. Negative conversion/unsupported cases require explicit decline, not a
fabricated proof of disequality. The loaded worker provenance is separate from
the fixture-generator hash inventory and must be retained with any published
result.

The million-plus syntax count is chiefly an exhaustive host UTF-8 boundary
exercise, not a million Arena cases or a verified parser theorem. Byte decoding,
AST translation, the encoded judgment's correspondence to Lean, and runtime
resource behavior remain distinct verification boundaries.

The quotient suite admits a custom `String := Quot Nat (Eq Nat)` environment
and checks its literal-typing and explicit-constructor gates before requiring
ordinary quotient WHNF to leave literal, delta, beta and zeta majors neutral.
This distinguishes quotient normalization from inductive/projection string
expansion; unsuccessful conversion is a decline, not a proof of disequality.
