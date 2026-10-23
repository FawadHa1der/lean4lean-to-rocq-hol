# ShiftLeft Regressions

Run from the project root:

```sh
python3 -B -m unittest discover -s tests/hol_shift_left -p test_offline.py -v
python3 -B tests/hol_shift_left/run.py --prepare-only
python3 -B tests/hol_shift_left/run.py
```

This separate runner has ten sequential groups at 180 seconds each. It stops
at the first failure and reports later selected groups as unexecuted. It does
not change the shared 124-group composition registry or default proof-file
dispatch. Group names are in `PHASES` in `run.py`; pass names to select a subset.
Prepare-only captures source provenance and generates test instrumentation
without launching HOL.

Native tests cover the general typed theorem, empty/Nat/dependent contexts,
large values and budget refusals, arithmetic allocation order, full contract
guards, primitive imports, exact authentication, and beta/let/named wrappers.
The test-only numeral observer checks that a zero multiplier is simplified
before exponentiation and that resource refusals precede numeric conversion.
It cannot manufacture a theorem. Every native result must have exact completion
markers, clean error scans, stable source pins, and reaped/absent child groups.

The integrated offline suite has ten tests. A private historical-source freeze
test was intentionally removed for portability; fresh snapshot hashes replace
the dependency on that private tree, not the removed test's assertion count.
`budget_tests.ml` separately exercises the pure resource preflight and is not
part of the native HOL assertion count.

The fresh frozen-main native matrix passes all ten groups / 357 assertions.
The separate pure-budget suite passes 64,233 assertions. Exact source/runtime
pins and cleanup evidence are retained in
`build/reports/shift-left-main-audit-20261001T032945Z-8917/main-matrix-audit.json`.
This does not claim a current Arena result or default-dispatch integration.
